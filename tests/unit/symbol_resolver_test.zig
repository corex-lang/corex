//! Unit Tests for Module & Lexical Scope Name Resolution (`tests/unit/symbol_resolver_test.zig`)
//!
//! Exercises `ScopeArena`, `SymbolTable`, module-level item collection (`resolveModuleSignatures`),
//! `mod` and `use` import resolution (path, alias, group, glob), `pub` visibility hygiene (`E0409`),
//! disjoint `Type` / `Value` / `Const` namespaces, duplicate definitions (`E0408`), explicit
//! `@overload` sets (`DR-02`), unused binding warnings (`W0402`), and bounded Damerau-Levenshtein /
//! Jaro-Winkler "did you mean?" typo suggestions (`E0403`).

const std = @import("std");
const corex = @import("corex");

const symbol_resolver = corex.symbol_resolver;
const type_system = corex.type_system;
const FileId = corex.FileId;
const Span = corex.Span;
const ScopeId = corex.ScopeId;
const TypeId = corex.TypeId;
const StringInterner = corex.StringInterner;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const AstArena = corex.AstArena;
const DiagnosticSink = corex.DiagnosticSink;
const DiagnosticCode = corex.DiagnosticCode;
const ScopeKind = symbol_resolver.ScopeKind;
const Namespace = symbol_resolver.Namespace;
const NamespaceMask = symbol_resolver.NamespaceMask;
const Visibility = symbol_resolver.Visibility;
const SymbolKind = symbol_resolver.SymbolKind;
const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolTable = symbol_resolver.SymbolTable;
const InternPool = type_system.InternPool;

// -------------------------------------- INTERNALS --------------------------------------

/// Helper that runs `typecheckSource` on `source` and returns its `TypecheckResult`.
fn runResolveAndTypecheck(
    allocator: std.mem.Allocator,
    source: []const u8,
) !type_system.TypecheckResult {
    return type_system.typecheckSource(allocator, FileId.fromInt(1), source);
}

/// Returns `true` if `sink` contains at least one diagnostic with `expected_code`.
fn hasDiagnosticCode(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag| {
        if (diag.code == expected_code) return true;
    }
    return false;
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------- ScopeArena & Namespace Primitives --------------

test "test_symbol_resolver_scope_arena_and_namespace_mask_invariants" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var sym_table = try SymbolTable.init(std.testing.allocator, &interner);
    defer sym_table.deinit();

    // [1] `NamespaceMask` membership checks:
    try std.testing.expect(NamespaceMask.TYPE_ONLY.contains(.type_ns));
    try std.testing.expect(!NamespaceMask.TYPE_ONLY.contains(.value_ns));
    try std.testing.expect(NamespaceMask.VALUE_OR_CONST.contains(.value_ns));
    try std.testing.expect(NamespaceMask.VALUE_OR_CONST.contains(.const_ns));
    try std.testing.expect(!NamespaceMask.VALUE_OR_CONST.contains(.type_ns));
    try std.testing.expect(NamespaceMask.ALL.contains(.type_ns));
    try std.testing.expect(NamespaceMask.ALL.contains(.value_ns));
    try std.testing.expect(NamespaceMask.ALL.contains(.const_ns));

    // [2] `ScopeArena` hierarchical allocation and parent chain:
    const mod_scope = try sym_table.scope_arena.allocScope(
        .module_scope,
        .none,
        .NONE,
        FileId.fromInt(1),
        .{},
    );
    const fn_scope = try sym_table.scope_arena.allocScope(
        .fn_scope,
        mod_scope,
        .NONE,
        FileId.fromInt(1),
        .{ .is_inside_fallible_fn = true },
    );
    const loop_scope = try sym_table.scope_arena.allocScope(
        .loop_scope,
        fn_scope,
        .NONE,
        FileId.fromInt(1),
        .{ .is_inside_loop = true },
    );

    try std.testing.expectEqual(@as(usize, 4), sym_table.scope_arena.countScopes());
    try std.testing.expectEqual(ScopeKind.module_scope, sym_table.scope_arena.getScope(mod_scope).kind);
    try std.testing.expectEqual(mod_scope, sym_table.scope_arena.getScope(fn_scope).parent);
    try std.testing.expectEqual(fn_scope, sym_table.scope_arena.getScope(loop_scope).parent);
    try std.testing.expect(sym_table.scope_arena.getScope(loop_scope).flags.is_inside_loop);
    try std.testing.expect(sym_table.scope_arena.isWithinModule(loop_scope, mod_scope));

    try sym_table.reset(&interner);
    try std.testing.expectEqual(@as(usize, 1), sym_table.scope_arena.countScopes());
}

// -------- Disjoint Namespaces, E0408 & @overload Sets ---------

test "test_symbol_resolver_disjoint_namespaces_duplicate_e0408_and_overload_sets" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var sym_table = try SymbolTable.init(std.testing.allocator, &interner);
    defer sym_table.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    const root_scope = try sym_table.scope_arena.allocScope(
        .module_scope,
        .none,
        .NONE,
        FileId.fromInt(1),
        .{},
    );

    const widget_name = try interner.intern("Widget");
    const span_a = Span.init(FileId.fromInt(1), 0, 6);
    const span_b = Span.init(FileId.fromInt(1), 10, 16);

    // [1] Defining `Widget` in `.type_ns` and `.value_ns` succeeds without conflict:
    const type_idx = try sym_table.defineSymbol(.{
        .name = widget_name,
        .name_text = interner.get(widget_name),
        .kind = .struct_sym,
        .namespace = .type_ns,
        .visibility = .public,
        .flags = .{},
        .scope_id = root_scope,
        .decl_span = span_a,
    }, &sink);
    const val_idx = try sym_table.defineSymbol(.{
        .name = widget_name,
        .name_text = interner.get(widget_name),
        .kind = .fn_sym,
        .namespace = .value_ns,
        .visibility = .public,
        .flags = .{},
        .scope_id = root_scope,
        .decl_span = span_b,
    }, &sink);

    try std.testing.expect(!type_idx.isNone());
    try std.testing.expect(!val_idx.isNone());
    try std.testing.expect(type_idx != val_idx);
    try std.testing.expect(!sink.hasErrors());

    try std.testing.expectEqual(
        type_idx,
        sym_table.lookupInScopeDirect(root_scope, widget_name, NamespaceMask.TYPE_ONLY),
    );
    try std.testing.expectEqual(
        val_idx,
        sym_table.lookupInScopeDirect(root_scope, widget_name, NamespaceMask.VALUE_ONLY),
    );

    // [2] Duplicate definition in `.type_ns` emits `E0408`:
    _ = try sym_table.defineSymbol(.{
        .name = widget_name,
        .name_text = interner.get(widget_name),
        .kind = .enum_sym,
        .namespace = .type_ns,
        .visibility = .public,
        .flags = .{},
        .scope_id = root_scope,
        .decl_span = Span.init(FileId.fromInt(1), 20, 26),
    }, &sink);
    try std.testing.expect(hasDiagnosticCode(&sink, .e0408_duplicate_definition));

    // [3] `@overload` functions with the same name group cleanly into an `OverloadSet`:
    var ov_sink = DiagnosticSink.init(std.testing.allocator);
    defer ov_sink.deinit();
    const hash_name = try interner.intern("hash_val");
    const ov_first = try sym_table.defineSymbol(.{
        .name = hash_name,
        .name_text = interner.get(hash_name),
        .kind = .fn_sym,
        .namespace = .value_ns,
        .visibility = .public,
        .flags = .{ .is_overload = true },
        .scope_id = root_scope,
        .decl_span = Span.init(FileId.fromInt(1), 30, 38),
    }, &ov_sink);
    const ov_second = try sym_table.defineSymbol(.{
        .name = hash_name,
        .name_text = interner.get(hash_name),
        .kind = .fn_sym,
        .namespace = .value_ns,
        .visibility = .public,
        .flags = .{ .is_overload = true },
        .scope_id = root_scope,
        .decl_span = Span.init(FileId.fromInt(1), 50, 58),
    }, &ov_sink);
    try std.testing.expect(!ov_sink.hasErrors());
    try std.testing.expect(ov_first != ov_second);

    const ov_set = sym_table.getOverloadSet(root_scope, hash_name).?;
    try std.testing.expectEqual(@as(usize, 2), ov_set.members.items.len);
}

// ------------ Mod, Use Imports & Visibility E0409 -------------

test "test_symbol_resolver_mod_use_imports_and_private_visibility_e0409" {
    // [1] Valid `mod`, `use` path, `use` alias, `use` group, and `use` glob resolution:
    {
        const valid_src =
            "mod math {\n" ++
            "    pub const BASE_OFFSET: i32 = 10;\n" ++
            "    pub fn double_val(input_val: i32) -> i32 {\n" ++
            "        return input_val + BASE_OFFSET;\n" ++
            "    }\n" ++
            "    pub fn triple_val(input_val: i32) -> i32 {\n" ++
            "        return input_val * 3;\n" ++
            "    }\n" ++
            "}\n" ++
            "mod extra {\n" ++
            "    pub const BONUS: i32 = 5;\n" ++
            "}\n" ++
            "use math::{double_val, triple_val as mul3};\n" ++
            "use extra::*;\n" ++
            "pub fn entry(seed: i32) -> i32 {\n" ++
            "    return double_val(seed) + mul3(seed) + BONUS;\n" ++
            "}\n";

        var res = try runResolveAndTypecheck(std.testing.allocator, valid_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
        try std.testing.expectEqual(@as(u32, 0), res.diagnostics.warning_count);
    }

    // [2] Accessing a private function across a module boundary emits `E0409`:
    {
        const private_src =
            "mod internal_mod {\n" ++
            "    fn secret_helper(val: i32) -> i32 {\n" ++
            "        return val + 1;\n" ++
            "    }\n" ++
            "}\n" ++
            "use internal_mod::secret_helper;\n" ++
            "pub fn caller(val: i32) -> i32 {\n" ++
            "    return secret_helper(val);\n" ++
            "}\n";

        var res = try runResolveAndTypecheck(std.testing.allocator, private_src);
        defer res.deinit();
        try std.testing.expect(hasDiagnosticCode(&res.diagnostics, .e0409_private_symbol_access));
    }

    // [3] Accessing a private struct field from outside its defining module emits `E0409`:
    {
        const private_field_src =
            "mod vault {\n" ++
            "    pub struct Account {\n" ++
            "        pub id: u32,\n" ++
            "        balance: i64,\n" ++
            "    }\n" ++
            "}\n" ++
            "pub fn inspect_balance(acc: vault::Account) -> i64 {\n" ++
            "    return acc.balance;\n" ++
            "}\n";

        var res = try runResolveAndTypecheck(std.testing.allocator, private_field_src);
        defer res.deinit();
        try std.testing.expect(hasDiagnosticCode(&res.diagnostics, .e0409_private_symbol_access));
    }
}

// ------- Unused Bindings W0402 & Typo Suggestions E0403 -------

test "test_symbol_resolver_unused_binding_w0402_and_typo_suggestion_e0403" {
    // [1] Unresolved identifier with close lexical match emits `E0403` with `did you mean` label & suggestion:
    {
        const typo_src =
            "pub fn calculate(packet_length: i32) -> i32 {\n" ++
            "    return packet_lenght + 1;\n" ++
            "}\n";

        var res = try runResolveAndTypecheck(std.testing.allocator, typo_src);
        defer res.deinit();
        try std.testing.expect(hasDiagnosticCode(&res.diagnostics, .e0403_unresolved_symbol));
        var has_found_suggestion = false;
        for (res.diagnostics.diagnostics.items) |diag| {
            if (diag.code == .e0403_unresolved_symbol) {
                for (diag.labels) |lbl| {
                    if (std.mem.indexOf(u8, lbl.label, "packet_length") != null) {
                        has_found_suggestion = true;
                    }
                }
                for (diag.suggestions) |sug| {
                    if (std.mem.indexOf(u8, sug.message, "packet_length") != null) {
                        has_found_suggestion = true;
                    }
                }
                for (diag.notes) |note| {
                    if (std.mem.indexOf(u8, note, "packet_length") != null) {
                        has_found_suggestion = true;
                    }
                }
            }
        }
        try std.testing.expect(has_found_suggestion);
    }

    // [3] Unused local variable emits `W0402`, whereas `_`-prefixed local is silent:
    {
        const unused_src =
            "pub fn process(used_param: i32, _ignored_param: i32) -> i32 {\n" ++
            "    let unused_local: i32 = 42;\n" ++
            "    let _intentionally_unused: i32 = 99;\n" ++
            "    return used_param;\n" ++
            "}\n";

        var res = try runResolveAndTypecheck(std.testing.allocator, unused_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
        try std.testing.expectEqual(@as(u32, 1), res.diagnostics.warning_count);
        try std.testing.expect(hasDiagnosticCode(&res.diagnostics, .w0402_unused_binding));
    }
}
