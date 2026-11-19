//! Phase 9 Package Manager, Global CAS Cache & Supply-Chain Sandbox Unit Suite
//!
//! Exhaustively verifies lossless TOML v1.0 CST & `TransactionalPatcher` surgery, single-form
//! `target` `@cfg` & `"unsafe_op"` validation (`E0013`), `.cx` `#!` + `---` script frontmatter &
//! `corex fmt` idempotency, content-addressable `BLAKE3` / Bao / Ed25519 / RFC 6962 / `vendor/`
//! verification (`E0015`), `Bounded-MVS` + `PubGrub` CDCL proof trees (`E0010`), native `links`
//! (`E0011`), `--locked`/`--frozen`/`--offline` (`E0014`/`E0016`), cross-major `E0012`, `.cxi`
//! digests, and `DR-17` supply-chain sandboxing (`E0324`, `E0325`, `E0326`, `E0327`, `E0435`, `W0330`).
//!
//! All filesystem tests run inside isolated `.zig-cache/tmp/phase9_unit_*` scratch directories
//! with hermetic `COREX_HOME` and `COREX_REGISTRY_DIR` environment maps and leak-checked allocators.

const std = @import("std");
const builtin = @import("builtin");
const corex = @import("corex");

const pkg_manifest = corex.pkg_manifest;
const pkg_cache = corex.pkg_cache;
const pkg_resolver = corex.pkg_resolver;
const pkg_conflict_seam = corex.pkg_conflict_seam;
const pkg_cxi_seam = corex.pkg_cxi_seam;
const vfs_sourcemap = corex.vfs_sourcemap;
const router = corex.router;
const style = corex.style;
const mir_sast = corex.mir_sast;
const BumpArena = corex.BumpArena;
const StringInterner = corex.StringInterner;
const FileId = corex.FileId;
const PackageId = corex.PackageId;
const Span = corex.Span;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticSink = corex.DiagnosticSink;
const DiagnosticRenderer = corex.DiagnosticRenderer;
const StyleConfig = corex.StyleConfig;
const SuggestedFix = corex.SuggestedFix;
const CompilerDb = corex.CompilerDb;
const TargetSpec = corex.TargetSpec;

// ---------------------------------------- TYPES ----------------------------------------

/// Captured stdout, stderr, and exit status from an in-process `router.runCli` invocation.
const CliRunCapture = struct {
    /// Exit status returned by `router.runCli` (`0` on success).
    exit_code: u8,
    /// Heap-allocated stdout text captured during execution.
    stdout: []u8,
    /// Heap-allocated stderr text captured during execution.
    stderr: []u8,

    /// Releases captured `stdout` and `stderr` buffers.
    fn deinit(self: *CliRunCapture, allocator: std.mem.Allocator) void {
        allocator.free(self.stdout);
        allocator.free(self.stderr);
        self.* = undefined;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Monotonic atomic counter ensuring unique scratch directories across parallel test threads.
var next_temp_dir_seq: std.atomic.Value(u32) = .init(1);

// -------------------------------------- INTERNALS --------------------------------------

// --------------- Scratch & CLI Helper Routines ----------------

/// Allocates and creates a fresh `.zig-cache/tmp/phase9_unit_<label>_<seq>` directory.
fn createIsolatedTempDir(allocator: std.mem.Allocator, io: std.Io, label: []const u8) ![]u8 {
    const seq_num = next_temp_dir_seq.fetchAdd(1, .monotonic);
    const dir_path = try std.fmt.allocPrint(
        allocator,
        ".zig-cache/tmp/phase9_unit_{s}_{d}",
        .{ label, seq_num },
    );
    errdefer allocator.free(dir_path);
    std.Io.Dir.cwd().deleteTree(io, dir_path) catch {};
    try std.Io.Dir.cwd().createDirPath(io, dir_path);
    return dir_path;
}

/// Writes `content` to `<base_dir>/<rel_path>`, creating parent directories automatically.
fn writeFixtureFile(
    allocator: std.mem.Allocator,
    io: std.Io,
    base_dir: []const u8,
    rel_path: []const u8,
    content: []const u8,
) ![]u8 {
    const full_path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ base_dir, rel_path });
    errdefer allocator.free(full_path);
    if (std.fs.path.dirname(full_path)) |parent_dir| {
        try std.Io.Dir.cwd().createDirPath(io, parent_dir);
    }
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = full_path, .data = content });
    return full_path;
}

/// Builds a hermetic `Environ.Map` with `COREX_HOME`, optional `COREX_REGISTRY_DIR`, and `PATH`.
fn buildHermeticEnvMap(
    allocator: std.mem.Allocator,
    corex_home: []const u8,
    registry_dir_opt: ?[]const u8,
    is_hermetic_env: bool,
) !std.process.Environ.Map {
    var env_map = std.process.Environ.Map.init(allocator);
    errdefer env_map.deinit();
    try env_map.put("COREX_HOME", corex_home);
    try env_map.put("HOME", corex_home);
    try env_map.put("ZIG_GLOBAL_CACHE_DIR", ".zig-cache/zig_global_cache");
    try env_map.put("PATH", "/usr/local/bin:/usr/bin:/bin");
    if (registry_dir_opt) |reg_dir| {
        try env_map.put("COREX_REGISTRY_DIR", reg_dir);
    }
    if (is_hermetic_env) {
        try env_map.put("COREX_HERMETIC", "1");
    }
    return env_map;
}

/// Invokes `router.runCli` with `env_map` and captures `stdout`, `stderr`, and `exit_code`.
fn runCliCaptured(
    allocator: std.mem.Allocator,
    io: std.Io,
    env_map: *const std.process.Environ.Map,
    raw_args: []const []const u8,
) !CliRunCapture {
    var out_alloc: std.Io.Writer.Allocating = .init(allocator);
    defer out_alloc.deinit();
    var err_alloc: std.Io.Writer.Allocating = .init(allocator);
    defer err_alloc.deinit();

    const exit_code = try router.runCli(
        allocator,
        io,
        env_map,
        raw_args,
        &out_alloc.writer,
        &err_alloc.writer,
    );
    const owned_out = try allocator.dupe(u8, out_alloc.written());
    errdefer allocator.free(owned_out);
    const owned_err = try allocator.dupe(u8, err_alloc.written());
    return .{
        .exit_code = exit_code,
        .stdout = owned_out,
        .stderr = owned_err,
    };
}

/// Returns `true` when `sink` contains at least one diagnostic matching `expected_code`.
fn hasSinkDiagnosticCode(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == expected_code) return true;
    }
    return false;
}

/// Concatenates every syntactic token and trivia piece in `doc` to verify lossless CST coverage.
fn reconstructTomlFromTokensAlloc(
    allocator: std.mem.Allocator,
    doc: *const pkg_manifest.TomlDocumentView,
) ![]u8 {
    const SpanPiece = struct {
        /// Starting byte offset relative to `doc.toml_slice`.
        offset: u32,
        /// Byte length of this token or trivia piece.
        length: u32,
    };

    var pieces: std.ArrayListUnmanaged(SpanPiece) = .empty;
    defer pieces.deinit(allocator);

    for (doc.tokens.tokens.items(.byte_offset), doc.tokens.tokens.items(.byte_len)) |tok_off, tok_len| {
        if (tok_len > 0) {
            try pieces.append(allocator, .{ .offset = tok_off, .length = tok_len });
        }
    }
    for (doc.tokens.trivia.items) |triv_item| {
        if (triv_item.byte_len > 0) {
            try pieces.append(allocator, .{ .offset = triv_item.byte_offset, .length = triv_item.byte_len });
        }
    }

    std.mem.sort(SpanPiece, pieces.items, {}, struct {
        /// Sorts token and trivia pieces in ascending byte-offset order.
        fn lessThan(_: void, lhs: SpanPiece, rhs: SpanPiece) bool {
            return lhs.offset < rhs.offset;
        }
    }.lessThan);

    var out_builder = try std.ArrayList(u8).initCapacity(allocator, doc.toml_slice.len);
    errdefer out_builder.deinit(allocator);

    var expected_cursor: u32 = 0;
    for (pieces.items) |piece| {
        try std.testing.expect(piece.offset >= expected_cursor);
        for (doc.toml_slice[expected_cursor..piece.offset]) |gap_byte| {
            try std.testing.expect(
                gap_byte == ' ' or gap_byte == '\t' or gap_byte == '\r' or gap_byte == '\n',
            );
        }
        out_builder.appendSliceAssumeCapacity(doc.toml_slice[expected_cursor..piece.offset]);
        const end_pos = piece.offset + piece.length;
        try std.testing.expect(end_pos <= doc.toml_slice.len);
        out_builder.appendSliceAssumeCapacity(doc.toml_slice[piece.offset..end_pos]);
        expected_cursor = end_pos;
    }
    for (doc.toml_slice[expected_cursor..]) |tail_byte| {
        try std.testing.expect(
            tail_byte == ' ' or tail_byte == '\t' or tail_byte == '\r' or tail_byte == '\n',
        );
    }
    out_builder.appendSliceAssumeCapacity(doc.toml_slice[expected_cursor..]);
    return out_builder.toOwnedSlice(allocator);
}

// ---------------------------------------- MAIN -----------------------------------------

// ----- Pillar 1: Lossless TOML CST & Manifest Validation ------

test "test_phase9_toml_cst_patcher_naming_target_cfg_and_unsafe_op" {
    const allocator = std.testing.allocator;
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    const linux_cfg = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.X86_64_LINUX_GNU, false);
    const macos_cfg = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.AARCH64_APPLE_DARWIN, false);

    // [1] Lossless `TomlToken` (`8B`) + `TomlCstNode` (`16B`) round-trip trivia/comment preservation & `# CVE-` flag:
    {
        try std.testing.expectEqual(@as(usize, 8), @sizeOf(pkg_manifest.TomlToken));
        try std.testing.expectEqual(@as(usize, 16), @sizeOf(pkg_manifest.TomlCstNode));

        const rich_toml =
            "# Header comment preserved verbatim\r\n" ++
            "[package]\r\n" ++
            "name    = \"demo-app\" # inline pkg comment\r\n" ++
            "version = \"0.2.0\"\r\n" ++
            "edition = \"2026\"\r\n" ++
            "\r\n" ++
            "[security]\r\n" ++
            "default_allow_caps = [\"net\", \"unsafe_op\"]\r\n" ++
            "\r\n" ++
            "[dependencies]\r\n" ++
            "http-core   = '1.4.0' # single-quoted\r\n" ++
            "linux-sys   = { version = \"0.3.1\", target = \"target.os == .Linux and target.arch == .X86_64\", allow_caps = [\"unsafe_op\"] }\r\n" ++
            "\r\n" ++
            "[resolution]\r\n" ++
            "exclude = [\r\n" ++
            "    \"http-core@< 1.2.0\", # CVE-2026-4242 advisory ban\r\n" ++
            "]\r\n";

        var arena = BumpArena.init(allocator);
        defer arena.deinit();
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();

        var parsed = try pkg_manifest.parseManifest(
            allocator,
            &arena,
            &interner,
            FileId.fromInt(1),
            rich_toml,
            &linux_cfg,
            &sink,
        );
        defer parsed.doc.deinit(allocator);
        try std.testing.expect(!sink.hasErrors());
        try std.testing.expect(parsed.doc.cst.nodes.len > 0);
        try std.testing.expectEqual(@as(usize, 1), parsed.manifest.excludes.len);
        try std.testing.expect(parsed.manifest.excludes[0].has_cve_advisory);

        const reconstructed = try reconstructTomlFromTokensAlloc(allocator, &parsed.doc);
        defer allocator.free(reconstructed);
        try std.testing.expectEqualStrings(rich_toml, reconstructed);

        // Surgical `buildAutoAppendDependencyEdit` & `buildScalarReplaceEdit` preserve comments, quotes, CRLF, and `=` alignment:
        const append_edit = try pkg_manifest.buildAutoAppendDependencyEdit(
            allocator,
            &parsed.doc,
            &interner,
            "serde-json",
            "\"1.0.5\"",
        );
        const replace_edit = try pkg_manifest.buildScalarReplaceEdit(
            &parsed.doc,
            &interner,
            parsed.doc.cst.anchors.items[parsed.manifest.dependencies[0].anchor_id],
            "1.5.0",
        );
        const fixes = [_]SuggestedFix{
            .{ .message = "bump http-core", .edits = (&replace_edit)[0..1] },
            .{ .message = "append serde-json", .edits = (&append_edit)[0..1] },
        };
        const patched_toml = try pkg_manifest.applyManifestFixesTransactionally(
            allocator,
            &parsed.doc,
            &fixes,
            &interner,
        );
        defer allocator.free(patched_toml);

        try std.testing.expect(std.mem.indexOf(u8, patched_toml, "# Header comment preserved verbatim\r\n") != null);
        try std.testing.expect(std.mem.indexOf(u8, patched_toml, "http-core   = '1.5.0' # single-quoted\r\n") != null);
        try std.testing.expect(std.mem.indexOf(u8, patched_toml, "serde-json  = \"1.0.5\"\r\n") != null);

        // Also verify `buildInsertAliasLineEdit` inserts an aligned alias row cleanly:
        var reparsed_doc = try pkg_manifest.parseTomlDocument(
            allocator,
            FileId.fromInt(1),
            patched_toml,
            patched_toml,
            0,
            0,
            false,
            .e0013_invalid_manifest_or_pkg_name,
            null,
        );
        defer reparsed_doc.deinit(allocator);
        const alias_edit = try pkg_manifest.buildInsertAliasLineEdit(
            &reparsed_doc,
            &interner,
            reparsed_doc.cst.anchors.items[parsed.manifest.dependencies[0].anchor_id],
            "http-v2",
            "http-core",
            "2.0.0",
        );
        const alias_fix = SuggestedFix{ .message = "add v2 alias", .edits = (&alias_edit)[0..1] };
        const with_alias = try pkg_manifest.applyManifestFixesTransactionally(
            allocator,
            &reparsed_doc,
            (&alias_fix)[0..1],
            &interner,
        );
        defer allocator.free(with_alias);
        try std.testing.expect(
            std.mem.indexOf(u8, with_alias, "http-v2     = { package = \"http-core\", version = \"2.0.0\" }\r\n") != null,
        );

        // Verify `computeNormalizedManifestBlake3` ignores comments and whitespace formatting:
        const compact_equivalent =
            "[package]\nname=\"demo-app\"\nversion=\"0.2.0\"\nedition=\"2026\"\n" ++
            "[security]\ndefault_allow_caps=[\"net\",\"unsafe_op\"]\n" ++
            "[dependencies]\nhttp-core=\"1.4.0\"\n" ++
            "linux-sys={version=\"0.3.1\",target=\"target.os == .Linux and target.arch == .X86_64\",allow_caps=[\"unsafe_op\"]}\n" ++
            "[resolution]\nexclude=[\"http-core@< 1.2.0\"]\n";
        var compact_arena = BumpArena.init(allocator);
        defer compact_arena.deinit();
        var parsed_compact = try pkg_manifest.parseManifest(
            allocator,
            &compact_arena,
            &interner,
            FileId.fromInt(2),
            compact_equivalent,
            &linux_cfg,
            null,
        );
        defer parsed_compact.doc.deinit(allocator);
        try std.testing.expectEqualSlices(
            u8,
            &parsed.manifest.root_manifest_blake3,
            &parsed_compact.manifest.root_manifest_blake3,
        );
    }

    // [2] Resource caps (`MAX_TOML_BYTES`, `MAX_TOML_TOKENS`, `MAX_TOML_DEPTH`) emit `E0013` without crashing:
    {
        var cap_arena = BumpArena.init(allocator);
        defer cap_arena.deinit();

        const oversized_toml = try allocator.alloc(u8, pkg_manifest.MAX_TOML_BYTES + 16);
        defer allocator.free(oversized_toml);
        @memset(oversized_toml, ' ');
        var bytes_sink = DiagnosticSink.init(allocator);
        defer bytes_sink.deinit();
        _ = try pkg_manifest.parseLockfile(
            allocator,
            &cap_arena,
            &interner,
            FileId.fromInt(3),
            oversized_toml,
            null,
            &bytes_sink,
        );
        try std.testing.expect(hasSinkDiagnosticCode(&bytes_sink, .e0014_lockfile_drift_or_corrupt));

        var deep_buf: std.ArrayList(u8) = .empty;
        defer deep_buf.deinit(allocator);
        try deep_buf.appendSlice(allocator, "nested = ");
        for (0..pkg_manifest.MAX_TOML_DEPTH + 3) |_| try deep_buf.append(allocator, '[');
        try deep_buf.append(allocator, '1');
        for (0..pkg_manifest.MAX_TOML_DEPTH + 3) |_| try deep_buf.append(allocator, ']');
        try deep_buf.append(allocator, '\n');

        var depth_sink = DiagnosticSink.init(allocator);
        defer depth_sink.deinit();
        _ = try pkg_manifest.parseLockfile(
            allocator,
            &cap_arena,
            &interner,
            FileId.fromInt(4),
            deep_buf.items,
            null,
            &depth_sink,
        );
        try std.testing.expect(hasSinkDiagnosticCode(&depth_sink, .e0014_lockfile_drift_or_corrupt));

        // Build `< 1 MiB` TOML exceeding `MAX_TOML_TOKENS` (`65,536` tokens via `22,000` `k=1\n` lines = `66,000` tokens):
        var tok_buf = try std.ArrayList(u8).initCapacity(allocator, 220_000);
        defer tok_buf.deinit(allocator);
        for (0..22_000) |line_i| {
            var row_tmp: [24]u8 = undefined;
            const row_str = try std.fmt.bufPrint(&row_tmp, "k{d}=1\n", .{line_i});
            try tok_buf.appendSlice(allocator, row_str);
        }
        try std.testing.expect(tok_buf.items.len < pkg_manifest.MAX_TOML_BYTES);
        var tok_sink = DiagnosticSink.init(allocator);
        defer tok_sink.deinit();
        _ = try pkg_manifest.parseLockfile(
            allocator,
            &cap_arena,
            &interner,
            FileId.fromInt(5),
            tok_buf.items,
            null,
            &tok_sink,
        );
        try std.testing.expect(hasSinkDiagnosticCode(&tok_sink, .e0014_lockfile_drift_or_corrupt));
    }

    // [3] Bijective `kebab-case` <-> `snake_case` naming (`_` rejected with `E0013` + `SuggestedFix`, reserved names rejected):
    {
        const snake_pkg = try pkg_resolver.canonicalPkgNameToSnakeAlloc(allocator, "corex-http-v2");
        defer if (snake_pkg) |buf| allocator.free(buf);
        try std.testing.expectEqualStrings("corex_http_v2", snake_pkg.?);
        try std.testing.expect((try pkg_resolver.canonicalPkgNameToSnakeAlloc(allocator, "serde_json")) == null);

        const bad_underscore_toml =
            "[package]\nname = \"my-app\"\nversion = \"0.1.0\"\n[dependencies]\nserde_json = \"1.0.0\"\n";
        var us_arena = BumpArena.init(allocator);
        defer us_arena.deinit();
        var us_sink = DiagnosticSink.init(allocator);
        defer us_sink.deinit();
        var us_parsed = try pkg_manifest.parseManifest(
            allocator,
            &us_arena,
            &interner,
            FileId.fromInt(6),
            bad_underscore_toml,
            &linux_cfg,
            &us_sink,
        );
        defer us_parsed.doc.deinit(allocator);
        try std.testing.expect(hasSinkDiagnosticCode(&us_sink, .e0013_invalid_manifest_or_pkg_name));
        var has_rename_fix = false;
        for (us_sink.diagnostics.items) |diag_entry| {
            if (diag_entry.code == .e0013_invalid_manifest_or_pkg_name and diag_entry.suggestions.len > 0) {
                has_rename_fix = true;
            }
        }
        try std.testing.expect(has_rename_fix);

        const reserved_names = [_][]const u8{ "cx", "core", "std", "pkg", "self", "super" };
        for (reserved_names) |res_name| {
            try std.testing.expect((try pkg_resolver.canonicalPkgNameToSnakeAlloc(allocator, res_name)) == null);
            const res_toml = try std.fmt.allocPrint(
                allocator,
                "[package]\nname = \"{s}\"\nversion = \"0.1.0\"\n",
                .{res_name},
            );
            defer allocator.free(res_toml);
            var res_arena = BumpArena.init(allocator);
            defer res_arena.deinit();
            var res_sink = DiagnosticSink.init(allocator);
            defer res_sink.deinit();
            var res_parsed = try pkg_manifest.parseManifest(
                allocator,
                &res_arena,
                &interner,
                FileId.fromInt(7),
                res_toml,
                &linux_cfg,
                &res_sink,
            );
            defer res_parsed.doc.deinit(allocator);
            try std.testing.expect(hasSinkDiagnosticCode(&res_sink, .e0013_invalid_manifest_or_pkg_name));
        }
    }

    // [4] Single-form `target` `@cfg` evaluation vs Rust `cfg(…)` & `[target.'…'.dependencies]` rejection (`E0013`):
    {
        var eval_arena = BumpArena.init(allocator);
        defer eval_arena.deinit();
        const eval_linux = try pkg_manifest.validateAndEvalManifestTargetCfg(
            &eval_arena,
            &interner,
            null,
            "target.os == .Linux and target.arch == .X86_64",
            &linux_cfg,
            Span.init(FileId.fromInt(8), 0, 10),
            null,
            null,
        );
        const eval_macos = try pkg_manifest.validateAndEvalManifestTargetCfg(
            &eval_arena,
            &interner,
            null,
            "target.os == .Linux and target.arch == .X86_64",
            &macos_cfg,
            Span.init(FileId.fromInt(8), 0, 10),
            null,
            null,
        );
        try std.testing.expectEqual(@as(?bool, true), eval_linux);
        try std.testing.expectEqual(@as(?bool, false), eval_macos);

        const bad_target_manifests = [_][]const u8{
            "[package]\nname = \"app\"\nversion = \"0.1.0\"\n[dependencies]\nlibc-sys = { version = \"1.0.0\", target = \"cfg(unix)\" }\n",
            "[package]\nname = \"app\"\nversion = \"0.1.0\"\n[target.'cfg(unix)'.dependencies]\nlibc-sys = \"1.0.0\"\n",
        };
        for (bad_target_manifests) |bad_toml| {
            var bad_arena = BumpArena.init(allocator);
            defer bad_arena.deinit();
            var bad_sink = DiagnosticSink.init(allocator);
            defer bad_sink.deinit();
            var bad_parsed = try pkg_manifest.parseManifest(
                allocator,
                &bad_arena,
                &interner,
                FileId.fromInt(9),
                bad_toml,
                &macos_cfg,
                &bad_sink,
            );
            defer bad_parsed.doc.deinit(allocator);
            try std.testing.expect(hasSinkDiagnosticCode(&bad_sink, .e0013_invalid_manifest_or_pkg_name));
        }
    }

    // [5] Single-form `"unsafe_op"` capability accepted; bare `"unsafe"` rejected in `corex.toml` (`E0013`) & `corex.lock` (`E0014`):
    {
        const bad_cap_toml =
            "[package]\nname = \"app\"\nversion = \"0.1.0\"\n[security]\ndefault_allow_caps = [\"unsafe\"]\n";
        var cap_arena = BumpArena.init(allocator);
        defer cap_arena.deinit();
        var cap_sink = DiagnosticSink.init(allocator);
        defer cap_sink.deinit();
        var cap_parsed = try pkg_manifest.parseManifest(
            allocator,
            &cap_arena,
            &interner,
            FileId.fromInt(10),
            bad_cap_toml,
            &linux_cfg,
            &cap_sink,
        );
        defer cap_parsed.doc.deinit(allocator);
        try std.testing.expect(hasSinkDiagnosticCode(&cap_sink, .e0013_invalid_manifest_or_pkg_name));

        const zero_hex = "0000000000000000000000000000000000000000000000000000000000000000";
        const valid_lock_toml =
            "version = 1\n" ++
            "root_manifest_blake3 = \"b3:" ++ zero_hex ++ "\"\n\n" ++
            "[[package]]\n" ++
            "name = \"sys-bind\"\n" ++
            "version = \"1.0.0\"\n" ++
            "source = \"registry+https://index.corexlang.dev\"\n" ++
            "tree_hash = \"b3:" ++ zero_hex ++ "\"\n" ++
            "max_caps = [\"ffi\", \"unsafe_op\"]\n" ++
            "cxi_blake3 = \"b3:" ++ zero_hex ++ "\"\n" ++
            "features = []\n" ++
            "dependencies = []\n";

        var lock_arena = BumpArena.init(allocator);
        defer lock_arena.deinit();
        var ok_lock_sink = DiagnosticSink.init(allocator);
        defer ok_lock_sink.deinit();
        const parsed_lock = (try pkg_manifest.parseLockfile(
            allocator,
            &lock_arena,
            &interner,
            FileId.fromInt(11),
            valid_lock_toml,
            null,
            &ok_lock_sink,
        )).?;
        try std.testing.expect(!ok_lock_sink.hasErrors());
        try std.testing.expectEqual(@as(usize, 1), parsed_lock.packages.len);
        const serialized_lock = try pkg_manifest.serializeLockfile(allocator, &parsed_lock, &interner);
        defer allocator.free(serialized_lock);
        try std.testing.expect(std.mem.indexOf(u8, serialized_lock, "max_caps = [\"ffi\", \"unsafe_op\"]") != null);

        const bad_lock_toml =
            "version = 1\n" ++
            "root_manifest_blake3 = \"b3:" ++ zero_hex ++ "\"\n\n" ++
            "[[package]]\n" ++
            "name = \"sys-bind\"\n" ++
            "version = \"1.0.0\"\n" ++
            "source = \"registry+https://index.corexlang.dev\"\n" ++
            "tree_hash = \"b3:" ++ zero_hex ++ "\"\n" ++
            "max_caps = [\"unsafe\"]\n" ++
            "cxi_blake3 = \"b3:" ++ zero_hex ++ "\"\n" ++
            "features = []\n" ++
            "dependencies = []\n";
        var bad_lock_sink = DiagnosticSink.init(allocator);
        defer bad_lock_sink.deinit();
        const rejected_lock = try pkg_manifest.parseLockfile(
            allocator,
            &lock_arena,
            &interner,
            FileId.fromInt(12),
            bad_lock_toml,
            null,
            &bad_lock_sink,
        );
        try std.testing.expect(rejected_lock == null);
        try std.testing.expect(hasSinkDiagnosticCode(&bad_lock_sink, .e0014_lockfile_drift_or_corrupt));
    }
}

// ----- Pillar 2: Script Frontmatter, `fmt` & Inline `use` -----

test "test_phase9_script_frontmatter_fmt_idempotency_and_inline_use" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    const temp_dir = try createIsolatedTempDir(allocator, io, "script_fmt");
    defer allocator.free(temp_dir);
    defer std.Io.Dir.cwd().deleteTree(io, temp_dir) catch {};

    const corex_home = try std.fmt.allocPrint(allocator, "{s}/corex_home", .{temp_dir});
    defer allocator.free(corex_home);
    try std.Io.Dir.cwd().createDirPath(io, corex_home);

    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    const host_cfg = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.host(), false);

    // [1] `#!` + `---` frontmatter blanking preserves exact `.cx` byte offsets, line numbers, and `CRLF`:
    {
        const crlf_script =
            "#!/usr/bin/env -S corex run\r\n" ++
            "---\r\n" ++
            "[dependencies]\r\n" ++
            "math-helper = { path = \"./math_helper\" }\r\n" ++
            "---\r\n" ++
            "use math_helper.add_ten;\r\n" ++
            "fn main() -> i32 {\r\n" ++
            "    return add_ten(32) - 42;\r\n" ++
            "}\r\n";

        var fm_arena = BumpArena.init(allocator);
        defer fm_arena.deinit();
        var fm_sink = DiagnosticSink.init(allocator);
        defer fm_sink.deinit();
        const extracted = (try pkg_manifest.extractScriptFrontmatter(
            &fm_arena,
            FileId.fromInt(20),
            crlf_script,
            &fm_sink,
        )).?;
        try std.testing.expect(!fm_sink.hasErrors());
        try std.testing.expect(extracted.has_frontmatter);
        try std.testing.expectEqual(crlf_script.len, extracted.blanked_cx_source.len);

        for (crlf_script, 0..) |orig_byte, byte_i| {
            const blanked_byte = extracted.blanked_cx_source[byte_i];
            if (byte_i < extracted.prefix_end_byte) {
                if (orig_byte == '\r' or orig_byte == '\n') {
                    try std.testing.expectEqual(orig_byte, blanked_byte);
                } else {
                    try std.testing.expectEqual(@as(u8, ' '), blanked_byte);
                }
            } else {
                try std.testing.expectEqual(orig_byte, blanked_byte);
            }
        }

        // Forbidden `[workspace]`, `[lib]`, and `[[bin]]` sections in `.cx` scripts emit `E0013`:
        const forbidden_sections = [_][]const u8{
            "---\n[workspace]\nmembers = [\"a\"]\n---\nfn main() -> i32 { return 0; }\n",
            "---\n[lib]\npath = \"src/lib.cx\"\n---\nfn main() -> i32 { return 0; }\n",
            "---\n[[bin]]\nname = \"tool\"\npath = \"src/main.cx\"\n---\nfn main() -> i32 { return 0; }\n",
        };
        for (forbidden_sections) |bad_script| {
            var bad_arena = BumpArena.init(allocator);
            defer bad_arena.deinit();
            var bad_sink = DiagnosticSink.init(allocator);
            defer bad_sink.deinit();
            const bad_fm = (try pkg_manifest.extractScriptFrontmatter(
                &bad_arena,
                FileId.fromInt(21),
                bad_script,
                &bad_sink,
            )).?;
            var parsed_bad = try pkg_manifest.parseScriptFrontmatterManifest(
                allocator,
                &bad_arena,
                &interner,
                FileId.fromInt(21),
                bad_script,
                bad_fm,
                &host_cfg,
                &bad_sink,
            );
            defer parsed_bad.doc.deinit(allocator);
            try std.testing.expect(hasSinkDiagnosticCode(&bad_sink, .e0013_invalid_manifest_or_pkg_name));
        }
    }

    // [2] `corex fmt` & `corex fmt --check` idempotency on `#!` + `---` scripts AND inline `use "<spec>" as <alias>;`:
    const helper_toml = try writeFixtureFile(
        allocator,
        io,
        temp_dir,
        "math_helper/corex.toml",
        "[package]\nname = \"math-helper\"\nversion = \"0.1.0\"\n",
    );
    defer allocator.free(helper_toml);
    const helper_src = try writeFixtureFile(
        allocator,
        io,
        temp_dir,
        "math_helper/src/root.cx",
        "pub fn add_ten(val: i32) -> i32 {\n    return val + 10;\n}\n",
    );
    defer allocator.free(helper_src);

    const messy_script_src =
        "#!/usr/bin/env -S corex run\n" ++
        "---\n" ++
        "# Preserved frontmatter comment\n" ++
        "[dependencies]\n" ++
        "math-helper = { path = \"./math_helper\" }\n" ++
        "---\n" ++
        "use math_helper.add_ten;\n" ++
        "\n" ++
        "fn main( ) -> i32 {\n" ++
        "    return add_ten( 32 ) - 42;\n" ++
        "}\n";
    const script_file_path = try writeFixtureFile(allocator, io, temp_dir, "run_script.cx", messy_script_src);
    defer allocator.free(script_file_path);

    const messy_inline_src =
        "use \"https://github.com/org/pkg@v1.2.0\"   as   pkg_alias;\n" ++
        "use \"serde-json@1.4.0\"   as   serde_json;\n" ++
        "\n" ++
        "pub fn demo_inline( val: i32 ) -> i32 {\n" ++
        "    return val + 1;\n" ++
        "}\n";
    const inline_file_path = try writeFixtureFile(allocator, io, temp_dir, "inline_demo.cx", messy_inline_src);
    defer allocator.free(inline_file_path);

    var env_map = try buildHermeticEnvMap(allocator, corex_home, null, false);
    defer env_map.deinit();

    {
        var check_before = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "fmt", "--check", script_file_path, inline_file_path },
        );
        defer check_before.deinit(allocator);
        try std.testing.expect(check_before.exit_code != 0);

        var fmt_apply = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "fmt", script_file_path, inline_file_path },
        );
        defer fmt_apply.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 0), fmt_apply.exit_code);

        var check_after = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "fmt", "--check", script_file_path, inline_file_path },
        );
        defer check_after.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 0), check_after.exit_code);

        const formatted_script = try std.Io.Dir.cwd().readFileAlloc(
            io,
            script_file_path,
            allocator,
            .limited(64 * 1024),
        );
        defer allocator.free(formatted_script);
        try std.testing.expect(std.mem.startsWith(u8, formatted_script, "#!/usr/bin/env -S corex run\n---\n# Preserved frontmatter comment\n"));
        try std.testing.expect(std.mem.indexOf(u8, formatted_script, "return add_ten(32) - 42;") != null);

        const formatted_inline = try std.Io.Dir.cwd().readFileAlloc(
            io,
            inline_file_path,
            allocator,
            .limited(64 * 1024),
        );
        defer allocator.free(formatted_inline);
        try std.testing.expect(
            std.mem.indexOf(u8, formatted_inline, "use \"https://github.com/org/pkg@v1.2.0\" as pkg_alias;") != null,
        );
        try std.testing.expect(
            std.mem.indexOf(u8, formatted_inline, "use \"serde-json@1.4.0\" as serde_json;") != null,
        );

        var inline_arena = BumpArena.init(allocator);
        defer inline_arena.deinit();
        var inline_sink = DiagnosticSink.init(allocator);
        defer inline_sink.deinit();
        const parsed_gh = (try pkg_manifest.parseInlineUseSpec(
            &inline_arena,
            &interner,
            "github.com/org/http-kit@v1.2.0",
            "http_alias",
            Span.init(FileId.fromInt(22), 0, 10),
            Span.init(FileId.fromInt(22), 14, 24),
            &inline_sink,
        )).?;
        try std.testing.expect(!inline_sink.hasErrors());
        try std.testing.expectEqualStrings("http-kit", interner.get(parsed_gh.package_kebab));

        // Reserved URL tail `"pkg"` falls back cleanly to `alias_kebab` (`"pkg-alias"`):
        const parsed_reserved_tail = (try pkg_manifest.parseInlineUseSpec(
            &inline_arena,
            &interner,
            "github.com/org/pkg@v1.2.0",
            "pkg_alias",
            Span.init(FileId.fromInt(22), 0, 10),
            Span.init(FileId.fromInt(22), 14, 23),
            &inline_sink,
        )).?;
        try std.testing.expectEqualStrings("pkg-alias", interner.get(parsed_reserved_tail.package_kebab));
    }

    // [3] `<COREX_HOME>/target/scripts/<64-hex>/corex.lock` determinism & end-to-end `corex run <script.cx>`:
    {
        const lock_path_a = try pkg_manifest.computeScriptLockfilePath(io, allocator, corex_home, script_file_path);
        defer allocator.free(lock_path_a);
        const lock_path_b = try pkg_manifest.computeScriptLockfilePath(io, allocator, corex_home, script_file_path);
        defer allocator.free(lock_path_b);
        try std.testing.expectEqualStrings(lock_path_a, lock_path_b);
        try std.testing.expect(std.mem.indexOf(u8, lock_path_a, "/target/scripts/") != null);

        var script_run = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "run", script_file_path },
        );
        defer script_run.deinit(allocator);
        if (script_run.exit_code != 0) {
            std.debug.print("script_run stderr:\n{s}\n", .{script_run.stderr});
        }
        try std.testing.expectEqual(@as(u8, 0), script_run.exit_code);

        const script_lock_bytes = try std.Io.Dir.cwd().readFileAlloc(
            io,
            lock_path_a,
            allocator,
            .limited(64 * 1024),
        );
        defer allocator.free(script_lock_bytes);
        try std.testing.expect(std.mem.indexOf(u8, script_lock_bytes, "name = \"math-helper\"") != null);

        const sibling_lock = try std.fmt.allocPrint(allocator, "{s}/corex.lock", .{temp_dir});
        defer allocator.free(sibling_lock);
        try std.testing.expectError(
            error.FileNotFound,
            std.Io.Dir.cwd().openFile(io, sibling_lock, .{ .mode = .read_only }),
        );
    }
}

// ------ Pillar 3: CAS, Bao, Ed25519, Tlog, LRU & Vendor -------

test "test_phase9_cas_bao_ed25519_rfc6962_lru_vfs_and_vendor" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    const temp_dir = try createIsolatedTempDir(allocator, io, "cas_crypto");
    defer allocator.free(temp_dir);
    defer std.Io.Dir.cwd().deleteTree(io, temp_dir) catch {};

    const corex_home = try std.fmt.allocPrint(allocator, "{s}/corex_home", .{temp_dir});
    defer allocator.free(corex_home);
    const vendor_dir = try std.fmt.allocPrint(allocator, "{s}/vendor_out", .{temp_dir});
    defer allocator.free(vendor_dir);

    var cache = try pkg_cache.PkgCache.init(allocator, corex_home, 64, 4 * 1024 * 1024);
    defer cache.deinit();

    // [1] `gc.lock` shared/exclusive locking & `CRLF`->`LF` source normalization vs raw binary assets:
    {
        var shared_lock_a = try cache.acquireGcLock(io, .shared, true);
        var shared_lock_b = try cache.acquireGcLock(io, .shared, true);
        shared_lock_b.release(io);
        shared_lock_a.release(io);

        var excl_lock = try cache.acquireGcLock(io, .exclusive, true);
        excl_lock.release(io);

        var norm_arena = BumpArena.init(allocator);
        defer norm_arena.deinit();
        const crlf_cx = "pub fn greet() -> i32 {\r\n    return 7;\r\n}\r\n";
        const norm_src = try pkg_cache.normalizeSourceForBlobIngest(&norm_arena, "src/root.cx", crlf_cx);
        try std.testing.expect(norm_src.is_crlf_normalized);
        try std.testing.expectEqualStrings("pub fn greet() -> i32 {\n    return 7;\n}\n", norm_src.bytes);

        const raw_binary = "\x89PNG\r\n\x1a\n\x00\x01\x02\r\n\xff";
        const norm_bin = try pkg_cache.normalizeSourceForBlobIngest(&norm_arena, "assets/logo.png", raw_binary);
        try std.testing.expect(!norm_bin.is_crlf_normalized);
        try std.testing.expectEqualSlices(u8, raw_binary, norm_bin.bytes);
    }

    // [2] Bao `.obao` verified streaming (`0B`, `1B`, `1024B`, `1025B`, `70 KiB` multi-chunk) + byte-tamper `E0015`:
    {
        const test_sizes = [_]usize{ 0, 1, 1024, 1025, 70 * 1024 };
        for (test_sizes) |blob_len| {
            const data_buf = try allocator.alloc(u8, blob_len);
            defer allocator.free(data_buf);
            for (data_buf, 0..) |*byte_slot, idx| {
                byte_slot.* = @truncate((idx *% 131) ^ 0x5A);
            }
            var root_b3: [32]u8 = undefined;
            std.crypto.hash.Blake3.hash(data_buf, &root_b3, .{});

            const obao = try pkg_cache.encodeBaoOutboard(allocator, data_buf);
            defer allocator.free(obao);

            var ok_sink = DiagnosticSink.init(allocator);
            defer ok_sink.deinit();
            try pkg_cache.verifyBaoOutboard(root_b3, obao, data_buf, &ok_sink, Span.init(FileId.fromInt(30), 0, 1));
            try std.testing.expect(!ok_sink.hasErrors());

            if (blob_len >= 4096) {
                // Verify interior 2-chunk slice `[1024 .. 3072)`:
                try pkg_cache.verifyBaoSlice(
                    root_b3,
                    obao,
                    1024,
                    2048,
                    data_buf[1024..3072],
                    &ok_sink,
                    Span.init(FileId.fromInt(30), 0, 1),
                );
                try std.testing.expect(!ok_sink.hasErrors());
            }

            if (blob_len > 0) {
                data_buf[blob_len / 2] ^= 0x01;
                var tamper_sink = DiagnosticSink.init(allocator);
                defer tamper_sink.deinit();
                try std.testing.expectError(
                    error.CacheIntegrityMismatch,
                    pkg_cache.verifyBaoOutboard(
                        root_b3,
                        obao,
                        data_buf,
                        &tamper_sink,
                        Span.init(FileId.fromInt(30), 0, 1),
                    ),
                );
                try std.testing.expect(hasSinkDiagnosticCode(&tamper_sink, .e0015_cache_integrity_mismatch));
            }
        }
    }

    // [3] Ed25519 publisher signature pass vs tampered payload and non-canonical public key (`E0015`):
    {
        const seed: [32]u8 = @splat(0x42);
        const kp = try std.crypto.sign.Ed25519.KeyPair.generateDeterministic(seed);
        const tree_digest: [32]u8 = @splat(0xAB);
        const tree_hex = std.fmt.bytesToHex(tree_digest, .lower);
        const msg = try std.fmt.allocPrint(
            allocator,
            "corex-publish-v1\ndemo-pkg\n1.2.3\n{s}",
            .{&tree_hex},
        );
        defer allocator.free(msg);
        const valid_sig = try kp.sign(msg, null);

        var sig_ok_sink = DiagnosticSink.init(allocator);
        defer sig_ok_sink.deinit();
        try pkg_cache.verifyPublisherSignature(
            allocator,
            "demo-pkg",
            "1.2.3",
            tree_digest,
            kp.public_key.toBytes(),
            valid_sig.toBytes(),
            &sig_ok_sink,
            Span.init(FileId.fromInt(31), 0, 1),
        );
        try std.testing.expect(!sig_ok_sink.hasErrors());

        var bad_sig_sink = DiagnosticSink.init(allocator);
        defer bad_sig_sink.deinit();
        var forged_tree = tree_digest;
        forged_tree[0] ^= 0xFF;
        try std.testing.expectError(
            error.CacheIntegrityMismatch,
            pkg_cache.verifyPublisherSignature(
                allocator,
                "demo-pkg",
                "1.2.3",
                forged_tree,
                kp.public_key.toBytes(),
                valid_sig.toBytes(),
                &bad_sig_sink,
                Span.init(FileId.fromInt(31), 0, 1),
            ),
        );
        try std.testing.expect(hasSinkDiagnosticCode(&bad_sig_sink, .e0015_cache_integrity_mismatch));

        var bad_pk_sink = DiagnosticSink.init(allocator);
        defer bad_pk_sink.deinit();
        const non_canonical_pk: [32]u8 = @splat(0xFF);
        try std.testing.expectError(
            error.CacheIntegrityMismatch,
            pkg_cache.verifyEd25519Signature(
                non_canonical_pk,
                msg,
                valid_sig.toBytes(),
                &bad_pk_sink,
                Span.init(FileId.fromInt(31), 0, 1),
            ),
        );
        try std.testing.expect(hasSinkDiagnosticCode(&bad_pk_sink, .e0015_cache_integrity_mismatch));
    }

    // [4] RFC 6962 Merkle inclusion & consistency proof pass vs forged proof rejection (`E0015`):
    {
        const leaf_0 = pkg_cache.computeRfc6962LeafHash("leaf-0");
        const leaf_1 = pkg_cache.computeRfc6962LeafHash("leaf-1");
        const leaf_2 = pkg_cache.computeRfc6962LeafHash("leaf-2");
        const leaf_3 = pkg_cache.computeRfc6962LeafHash("leaf-3");
        const node_01 = pkg_cache.computeRfc6962NodeHash(leaf_0, leaf_1);
        const node_23 = pkg_cache.computeRfc6962NodeHash(leaf_2, leaf_3);
        const root_4 = pkg_cache.computeRfc6962NodeHash(node_01, node_23);

        var tlog_ok_sink = DiagnosticSink.init(allocator);
        defer tlog_ok_sink.deinit();
        const inc_proof_leaf2 = [_][32]u8{ leaf_3, node_01 };
        try pkg_cache.verifyMerkleInclusionProof(
            2,
            4,
            "leaf-2",
            &inc_proof_leaf2,
            root_4,
            &tlog_ok_sink,
            Span.init(FileId.fromInt(32), 0, 1),
        );
        const cons_proof_2_to_4 = [_][32]u8{node_23};
        try pkg_cache.verifyMerkleConsistencyProof(
            2,
            4,
            &cons_proof_2_to_4,
            node_01,
            root_4,
            &tlog_ok_sink,
            Span.init(FileId.fromInt(32), 0, 1),
        );
        try std.testing.expect(!tlog_ok_sink.hasErrors());

        var forged_inc = inc_proof_leaf2;
        forged_inc[0][0] ^= 0x01;
        var tlog_bad_sink = DiagnosticSink.init(allocator);
        defer tlog_bad_sink.deinit();
        try std.testing.expectError(
            error.CacheIntegrityMismatch,
            pkg_cache.verifyMerkleInclusionProof(
                2,
                4,
                "leaf-2",
                &forged_inc,
                root_4,
                &tlog_bad_sink,
                Span.init(FileId.fromInt(32), 0, 1),
            ),
        );
        try std.testing.expect(hasSinkDiagnosticCode(&tlog_bad_sink, .e0015_cache_integrity_mismatch));

        var split_sink = DiagnosticSink.init(allocator);
        defer split_sink.deinit();
        var forged_cons = cons_proof_2_to_4;
        forged_cons[0][0] ^= 0x80;
        try std.testing.expectError(
            error.CacheIntegrityMismatch,
            pkg_cache.verifyMerkleConsistencyProof(
                2,
                4,
                &forged_cons,
                node_01,
                root_4,
                &split_sink,
                Span.init(FileId.fromInt(32), 0, 1),
            ),
        );
        try std.testing.expect(hasSinkDiagnosticCode(&split_sink, .e0015_cache_integrity_mismatch));
    }

    // [5] `BoundedMetadataLru` eviction by BOTH `max_entries` AND `max_bytes`:
    {
        var lru = pkg_cache.BoundedMetadataLru.init(allocator, 3, 100);
        defer lru.deinit();

        const makeKey = struct {
            /// Creates a distinct `LruCacheKey` tagged with `tag_byte`.
            fn run(tag_byte: u8) pkg_cache.LruCacheKey {
                return .{ .digest = @splat(tag_byte), .domain = .cxtree };
            }
        }.run;

        const payload_30: [30]u8 = @splat('a');
        try lru.put(makeKey(1), &payload_30);
        try lru.put(makeKey(2), &payload_30);
        try lru.put(makeKey(3), &payload_30);
        try std.testing.expectEqual(@as(u32, 3), lru.live_entries);
        // Touch key `1` so key `2` becomes LRU tail; inserting key `4` evicts key `2` via `max_entries == 3`:
        try std.testing.expect(lru.get(makeKey(1)) != null);
        try lru.put(makeKey(4), &payload_30);
        try std.testing.expectEqual(@as(u32, 3), lru.live_entries);
        try std.testing.expect(lru.get(makeKey(1)) != null);
        try std.testing.expect(lru.get(makeKey(2)) == null);

        // Insert a `60`-byte entry: `90 + 60 > 100` (`max_bytes`), forcing byte-cap eviction of multiple entries:
        const payload_60: [60]u8 = @splat('b');
        try lru.put(makeKey(5), &payload_60);
        try std.testing.expect(lru.live_bytes <= 100);
        try std.testing.expectEqual(@as(u32, 2), lru.live_entries);
        try std.testing.expect(lru.eviction_count >= 3);
    }

    // [6] Atomic CAS publish, `VfsSourceMap.mountCxTreePackage` virtual `/cx/` paths (ZERO host path leakage!),
    //     POSIX `\` separator normalization, and `materializeVendorDir`:
    {
        const root_cx_src = "pub fn pkg_answer() -> i32 {\n    return 42;\n}\n";
        var root_cx_b3: [32]u8 = undefined;
        std.crypto.hash.Blake3.hash(root_cx_src, &root_cx_b3, .{});
        const asset_bin = "\x00\x01COREX_ASSET\r\n";
        var asset_b3: [32]u8 = undefined;
        std.crypto.hash.Blake3.hash(asset_bin, &asset_b3, .{});

        var pub_sink = DiagnosticSink.init(allocator);
        defer pub_sink.deinit();
        const dummy_span = Span.init(FileId.fromInt(33), 0, 1);

        try cache.publishBlob(io, root_cx_src, root_cx_b3, &pub_sink, dummy_span);
        try cache.publishBlob(io, asset_bin, asset_b3, &pub_sink, dummy_span);

        const entries_in = [_]pkg_cache.CxTreeInputEntry{
            .{ .rel_path = "src/root.cx", .file_mode = 0x01, .file_size = root_cx_src.len, .file_blake3 = root_cx_b3 },
            .{ .rel_path = "assets/blob.bin", .file_mode = 0x01, .file_size = asset_bin.len, .file_blake3 = asset_b3 },
        };
        const built_tree = try pkg_cache.buildCxTreeBytes(allocator, "demo-pkg", &entries_in, &pub_sink, dummy_span);
        defer allocator.free(built_tree.bytes);
        try cache.publishCxTree(io, built_tree.bytes, built_tree.tree_blake3, &pub_sink, dummy_span);

        const cxi_bytes = try pkg_cxi_seam.serializeCxiSummary(allocator, 0, 0, &.{}, &.{});
        defer allocator.free(cxi_bytes);
        const cxi_digest = pkg_cxi_seam.computeCxiBlake3(0, 0, &.{});
        try cache.publishCxiSummary(io, cxi_bytes, cxi_digest, &pub_sink, dummy_span);
        try std.testing.expect(!pub_sink.hasErrors());

        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &interner);
        defer vfs.deinit(io);

        const ext_pkg_id = PackageId.fromInt(2);
        const mounted_fids = try vfs.mountCxTreePackage(
            io,
            ext_pkg_id,
            "demo-pkg",
            "1.0.0",
            built_tree.bytes,
            cache.blobs_dir,
        );
        defer allocator.free(mounted_fids);
        try std.testing.expectEqual(@as(usize, 2), mounted_fids.len);

        for (mounted_fids) |fid| {
            const entry = vfs.entries.items[fid.asInt()];
            const virt_str = interner.get(entry.virtual_path);
            const os_str = interner.get(entry.resolved_os_path);
            try std.testing.expectEqualStrings(virt_str, os_str);
            try std.testing.expect(std.mem.startsWith(u8, virt_str, "/cx/demo-pkg@1.0.0/"));
            try std.testing.expect(std.mem.indexOf(u8, os_str, corex_home) == null);
            try std.testing.expect(std.mem.indexOf(u8, os_str, "cache/blake3") == null);
        }

        // Verify POSIX `\` separator normalization in `lookupCxTreeAsset`:
        const asset_loaded = (try vfs.lookupCxTreeAsset("/cx/demo-pkg@1.0.0\\assets\\blob.bin")).?;
        try std.testing.expectEqualSlices(u8, asset_bin, asset_loaded);
        const src_loaded = (try vfs.lookupCxTreeAsset("/cx/demo-pkg@1.0.0/src/root.cx")).?;
        try std.testing.expectEqualStrings(root_cx_src, src_loaded);

        // Render a diagnostic on `mounted_fids[1]` and verify ZERO host path leakage in diagnostic text:
        var diag_sink = DiagnosticSink.init(allocator);
        defer diag_sink.deinit();
        try diag_sink.emit(.{
            .code = .e0401_type_mismatch,
            .severity = .err,
            .primary_span = Span.init(mounted_fids[1], 4, 14),
            .message = "synthetic diagnostic inside mounted `.cxtree` file",
        });
        var rendered_diag: std.Io.Writer.Allocating = .init(allocator);
        defer rendered_diag.deinit();
        try DiagnosticRenderer.init(&vfs, &interner, StyleConfig.MONOCHROME).renderAll(
            &rendered_diag.writer,
            &diag_sink,
        );
        try std.testing.expect(std.mem.indexOf(u8, rendered_diag.written(), "/cx/demo-pkg@1.0.0/src/root.cx") != null);
        try std.testing.expect(std.mem.indexOf(u8, rendered_diag.written(), corex_home) == null);

        // Verify `materializeVendorDir` writes `vendor/modules.toml` + deduplicated blobs/trees:
        const vendor_pkgs = [_]pkg_cache.VendorPackageRecord{
            .{
                .name = "demo-pkg",
                .version = "1.0.0",
                .source = "registry+https://index.corexlang.dev",
                .tree_blake3 = built_tree.tree_blake3,
            },
        };
        const vendor_stats = try pkg_cache.materializeVendorDir(
            &cache,
            io,
            vendor_dir,
            &vendor_pkgs,
            &pub_sink,
            dummy_span,
        );
        try std.testing.expect(
            vendor_stats.reflink_count + vendor_stats.hardlink_count + vendor_stats.copy_count >= 3,
        );
        const modules_toml_path = try std.fmt.allocPrint(allocator, "{s}/modules.toml", .{vendor_dir});
        defer allocator.free(modules_toml_path);
        const modules_toml = try std.Io.Dir.cwd().readFileAlloc(io, modules_toml_path, allocator, .limited(16 * 1024));
        defer allocator.free(modules_toml);
        try std.testing.expect(std.mem.indexOf(u8, modules_toml, "name = \"demo-pkg\"") != null);
    }
}

// -------- Pillar 4: MVS, PubGrub, Links & Hermetic CLI --------

test "test_phase9_mvs_pubgrub_conflicts_links_registry_git_and_hermetic_cli" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    const temp_dir = try createIsolatedTempDir(allocator, io, "solver_cli");
    defer allocator.free(temp_dir);
    defer std.Io.Dir.cwd().deleteTree(io, temp_dir) catch {};

    const corex_home = try std.fmt.allocPrint(allocator, "{s}/corex_home", .{temp_dir});
    defer allocator.free(corex_home);
    const reg_dir = try std.fmt.allocPrint(allocator, "{s}/mock_registry", .{temp_dir});
    defer allocator.free(reg_dir);
    try std.Io.Dir.cwd().createDirPath(io, corex_home);
    try std.Io.Dir.cwd().createDirPath(io, reg_dir);

    // [1] Diamond MVS + `P2-1` monotone feature re-enqueue (`v_next == v_cur`) + weak `foo?/feat` + `SeriesKey` coexistence:
    {
        // Populate mock registry packages:
        // - `leaf-opt@1.0.0` with feature `extra = []`
        // - `shared-core@1.0.0` & `shared-core@1.2.0` where `tls = ["dep:leaf-opt"]` and `boost = ["leaf-opt?/extra"]`
        // - `mid-left@1.0.0` -> `shared-core = { version = "1.2.0", features = ["boost"] }`
        // - `mid-right@1.0.0` -> `shared-core = { version = "1.0.0", features = ["tls"] }`
        //   (`v_next == 1.2.0 == v_cur`, must re-enqueue `shared-core` AND activate `leaf-opt` + `leaf-opt/extra`!)
        // - `corex-http@1.8.0` & `corex-http@2.1.0` (`SeriesKey` coexistence!)
        // - `alpha-pre@0.1.2` & `alpha-pre@0.2.1` (`0.x` `SeriesKey` coexistence):
        const p1 = try writeFixtureFile(allocator, io, reg_dir, "packages/leaf-opt-1.0.0/src/root.cx", "pub fn opt_fn() -> i32 = 1;\n");
        defer allocator.free(p1);
        const p2 = try writeFixtureFile(allocator, io, reg_dir, "packages/shared-core-1.0.0/src/root.cx", "pub fn sc() -> i32 = 10;\n");
        defer allocator.free(p2);
        const p3 = try writeFixtureFile(allocator, io, reg_dir, "packages/shared-core-1.2.0/src/root.cx", "pub fn sc() -> i32 = 12;\n");
        defer allocator.free(p3);
        const p4 = try writeFixtureFile(allocator, io, reg_dir, "packages/mid-left-1.0.0/src/root.cx", "pub fn ml() -> i32 = 2;\n");
        defer allocator.free(p4);
        const p5 = try writeFixtureFile(allocator, io, reg_dir, "packages/mid-right-1.0.0/src/root.cx", "pub fn mr() -> i32 = 3;\n");
        defer allocator.free(p5);
        const p6 = try writeFixtureFile(allocator, io, reg_dir, "packages/corex-http-1.8.0/src/root.cx", "pub struct Resp { pub code: i32 }\n");
        defer allocator.free(p6);
        const p7 = try writeFixtureFile(allocator, io, reg_dir, "packages/corex-http-2.1.0/src/root.cx", "pub struct Resp { pub code: i32 }\n");
        defer allocator.free(p7);
        const p8 = try writeFixtureFile(allocator, io, reg_dir, "packages/alpha-pre-0.1.2/src/root.cx", "pub fn v01() -> i32 = 1;\n");
        defer allocator.free(p8);
        const p9 = try writeFixtureFile(allocator, io, reg_dir, "packages/alpha-pre-0.2.1/src/root.cx", "pub fn v02() -> i32 = 2;\n");
        defer allocator.free(p9);

        const idx_leaf = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/le/af/leaf-opt",
            "{\"name\":\"leaf-opt\",\"vers\":\"1.0.0\",\"deps\":[],\"features\":{\"extra\":[]}}\n",
        );
        defer allocator.free(idx_leaf);
        const idx_shared = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/sh/ar/shared-core",
            "{\"name\":\"shared-core\",\"vers\":\"1.0.0\",\"deps\":[" ++
                "{\"name\":\"leaf-opt\",\"req\":\"1.0.0\",\"optional\":true}]," ++
                "\"features\":{\"tls\":[\"dep:leaf-opt\"],\"boost\":[\"leaf-opt?/extra\"]}}\n" ++
                "{\"name\":\"shared-core\",\"vers\":\"1.2.0\",\"deps\":[" ++
                "{\"name\":\"leaf-opt\",\"req\":\"1.0.0\",\"optional\":true}]," ++
                "\"features\":{\"tls\":[\"dep:leaf-opt\"],\"boost\":[\"leaf-opt?/extra\"]}}\n",
        );
        defer allocator.free(idx_shared);
        const idx_ml = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/mi/d-/mid-left",
            "{\"name\":\"mid-left\",\"vers\":\"1.0.0\",\"deps\":[{\"name\":\"shared-core\",\"req\":\"1.2.0\",\"features\":[\"boost\"]}]}\n",
        );
        defer allocator.free(idx_ml);
        const idx_mr = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/mi/d-/mid-right",
            "{\"name\":\"mid-right\",\"vers\":\"1.0.0\",\"deps\":[{\"name\":\"shared-core\",\"req\":\"1.0.0\",\"features\":[\"tls\"]}]}\n",
        );
        defer allocator.free(idx_mr);
        const idx_http = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/co/re/corex-http",
            "{\"name\":\"corex-http\",\"vers\":\"1.8.0\",\"deps\":[]}\n" ++
                "{\"name\":\"corex-http\",\"vers\":\"2.1.0\",\"deps\":[]}\n",
        );
        defer allocator.free(idx_http);
        const idx_alpha = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/al/ph/alpha-pre",
            "{\"name\":\"alpha-pre\",\"vers\":\"0.1.2\",\"deps\":[]}\n" ++
                "{\"name\":\"alpha-pre\",\"vers\":\"0.2.1\",\"deps\":[]}\n",
        );
        defer allocator.free(idx_alpha);

        const ws_dir = try std.fmt.allocPrint(allocator, "{s}/diamond_ws", .{temp_dir});
        defer allocator.free(ws_dir);
        const ws_toml_text =
            "[package]\nname = \"diamond-app\"\nversion = \"0.1.0\"\n" ++
            "[dependencies]\n" ++
            "mid-left = \"1.0.0\"\n" ++
            "mid-right = \"1.0.0\"\n" ++
            "http-v1 = { package = \"corex-http\", version = \"1.8.0\" }\n" ++
            "http-v2 = { package = \"corex-http\", version = \"2.1.0\" }\n" ++
            "alpha-one = { package = \"alpha-pre\", version = \"0.1.0\" }\n" ++
            "alpha-two = { package = \"alpha-pre\", version = \"0.2.0\" }\n";
        const ws_toml_path = try writeFixtureFile(allocator, io, ws_dir, "corex.toml", ws_toml_text);
        defer allocator.free(ws_toml_path);
        const ws_main_path = try writeFixtureFile(allocator, io, ws_dir, "src/main.cx", "fn main() -> i32 = 0;\n");
        defer allocator.free(ws_main_path);

        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &interner);
        defer vfs.deinit(io);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const cfg_env = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.host(), false);

        const toml_fid = try vfs.resolveOrCreatePath(io, ws_toml_path, .root);
        var bundle = try pkg_manifest.loadWorkspaceManifestBundle(
            io,
            allocator,
            &interner,
            ws_toml_path,
            toml_fid,
            &cfg_env,
            &sink,
        );
        defer bundle.deinit();
        try std.testing.expect(!sink.hasErrors());

        var graph = (try pkg_resolver.resolveProjectGraph(
            allocator,
            &interner,
            &vfs,
            &bundle,
            null,
            .{
                .io = io,
                .corex_home_dir = corex_home,
                .local_registry_dir = reg_dir,
            },
            &sink,
        )).?;
        defer graph.deinit(allocator);
        try std.testing.expect(!sink.hasErrors());
        try std.testing.expect(graph.has_used_mvs_fast_path);

        // Verify `shared-core@1.2.0` AND `leaf-opt@1.0.0` (with `"extra"` via weak `leaf-opt?/extra`!) AND coexisting series:
        var has_shared_120 = false;
        var has_leaf_extra = false;
        var http_series_count: usize = 0;
        var alpha_series_count: usize = 0;
        for (graph.packages) |pkg_node| {
            if (std.mem.eql(u8, pkg_node.canonical_name, "shared-core")) {
                try std.testing.expectEqual(@as(u32, 1), pkg_node.version.major);
                try std.testing.expectEqual(@as(u32, 2), pkg_node.version.minor);
                has_shared_120 = true;
            } else if (std.mem.eql(u8, pkg_node.canonical_name, "leaf-opt")) {
                for (pkg_node.enabled_features) |feat_name| {
                    if (std.mem.eql(u8, feat_name, "extra")) has_leaf_extra = true;
                }
            } else if (std.mem.eql(u8, pkg_node.canonical_name, "corex-http")) {
                http_series_count += 1;
            } else if (std.mem.eql(u8, pkg_node.canonical_name, "alpha-pre")) {
                alpha_series_count += 1;
            }
        }
        try std.testing.expect(has_shared_120);
        try std.testing.expect(has_leaf_extra);
        try std.testing.expectEqual(@as(usize, 2), http_series_count);
        try std.testing.expectEqual(@as(usize, 2), alpha_series_count);
    }

    // [2] Unsatisfiable diamond & `[resolution].exclude` conflicts emit `E0010` monochrome proof tree + `ConflictDagExport`:
    {
        const conf_p1 = try writeFixtureFile(allocator, io, reg_dir, "packages/conf-lib-1.0.0/src/root.cx", "pub fn c() -> i32 = 1;\n");
        defer allocator.free(conf_p1);
        const conf_p2 = try writeFixtureFile(allocator, io, reg_dir, "packages/conf-lib-1.5.0/src/root.cx", "pub fn c() -> i32 = 2;\n");
        defer allocator.free(conf_p2);
        const idx_conf = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/co/nf/conf-lib",
            "{\"name\":\"conf-lib\",\"vers\":\"1.0.0\",\"deps\":[]}\n" ++
                "{\"name\":\"conf-lib\",\"vers\":\"1.5.0\",\"deps\":[]}\n",
        );
        defer allocator.free(idx_conf);

        const bad_ws_dir = try std.fmt.allocPrint(allocator, "{s}/conflict_ws", .{temp_dir});
        defer allocator.free(bad_ws_dir);
        const bad_ws_toml =
            "[package]\nname = \"conflict-app\"\nversion = \"0.1.0\"\n" ++
            "[dependencies]\nconf-lib = \">= 1.0.0, < 2.0.0\"\n" ++
            "[resolution]\nexclude = [\n    \"conf-lib@>= 1.0.0\", # CVE-2026-9999\n]\n";
        const bad_toml_path = try writeFixtureFile(allocator, io, bad_ws_dir, "corex.toml", bad_ws_toml);
        defer allocator.free(bad_toml_path);

        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &interner);
        defer vfs.deinit(io);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const cfg_env = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.host(), false);

        const toml_fid = try vfs.resolveOrCreatePath(io, bad_toml_path, .root);
        var bundle = try pkg_manifest.loadWorkspaceManifestBundle(
            io,
            allocator,
            &interner,
            bad_toml_path,
            toml_fid,
            &cfg_env,
            &sink,
        );
        defer bundle.deinit();

        var failed_graph = try pkg_resolver.resolveProjectGraph(
            allocator,
            &interner,
            &vfs,
            &bundle,
            null,
            .{ .io = io, .corex_home_dir = corex_home, .local_registry_dir = reg_dir },
            &sink,
        );
        defer if (failed_graph) |*fg| fg.deinit(allocator);
        try std.testing.expect(failed_graph == null);
        try std.testing.expect(hasSinkDiagnosticCode(&sink, .e0010_unsatisfiable_dependency_graph));

        var rendered_err: std.Io.Writer.Allocating = .init(allocator);
        defer rendered_err.deinit();
        try DiagnosticRenderer.init(&vfs, &interner, StyleConfig.MONOCHROME).renderAll(&rendered_err.writer, &sink);
        const err_txt = rendered_err.written();
        try std.testing.expect(!style.hasBannedEmoji(err_txt));
        try std.testing.expect(std.mem.indexOf(u8, err_txt, "╭─ PubGrub Conflict Proof Tree") != null);
        try std.testing.expect(std.mem.indexOf(u8, err_txt, "╰─") != null);

        // Also directly verify `pkg_conflict_seam.exportLevelZeroConflictDag` layout invariants:
        var seam_arena = BumpArena.init(allocator);
        defer seam_arena.deinit();
        const sample_terms = [_]pkg_conflict_seam.IncompatTerm{.{ .series_id = 0, .ver_min = 0, .ver_max = 0 }};
        const sample_nodes = [_]pkg_conflict_seam.IncompatNode{.{ .term_start = 0, .term_len = 1, .kind = .root_pin }};
        const exported_dag = try pkg_conflict_seam.exportLevelZeroConflictDag(
            &seam_arena,
            0,
            &sample_nodes,
            &sample_terms,
            bundle.root_manifest.anchors,
        );
        try std.testing.expectEqual(@as(usize, 1), exported_dag.nodes.len);
        try std.testing.expectEqual(@as(usize, 1), exported_dag.terms.len);
    }

    // [3] Native `links = "z"` collision across two resolved packages emits `E0011`:
    {
        const za = try writeFixtureFile(allocator, io, reg_dir, "packages/zlib-one-1.0.0/src/root.cx", "pub fn z1() -> i32 = 1;\n");
        defer allocator.free(za);
        const zb = try writeFixtureFile(allocator, io, reg_dir, "packages/zlib-two-1.0.0/src/root.cx", "pub fn z2() -> i32 = 2;\n");
        defer allocator.free(zb);
        const idx_za = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/zl/ib/zlib-one",
            "{\"name\":\"zlib-one\",\"vers\":\"1.0.0\",\"links\":\"z\",\"deps\":[]}\n",
        );
        defer allocator.free(idx_za);
        const idx_zb = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/zl/ib/zlib-two",
            "{\"name\":\"zlib-two\",\"vers\":\"1.0.0\",\"links\":\"z\",\"deps\":[]}\n",
        );
        defer allocator.free(idx_zb);

        const links_ws = try std.fmt.allocPrint(allocator, "{s}/links_ws", .{temp_dir});
        defer allocator.free(links_ws);
        const links_toml_path = try writeFixtureFile(
            allocator,
            io,
            links_ws,
            "corex.toml",
            "[package]\nname = \"links-app\"\nversion = \"0.1.0\"\n[dependencies]\nzlib-one = \"1.0.0\"\nzlib-two = \"1.0.0\"\n",
        );
        defer allocator.free(links_toml_path);

        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &interner);
        defer vfs.deinit(io);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const cfg_env = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.host(), false);
        const toml_fid = try vfs.resolveOrCreatePath(io, links_toml_path, .root);
        var bundle = try pkg_manifest.loadWorkspaceManifestBundle(
            io,
            allocator,
            &interner,
            links_toml_path,
            toml_fid,
            &cfg_env,
            &sink,
        );
        defer bundle.deinit();

        const links_res = try pkg_resolver.resolveProjectGraph(
            allocator,
            &interner,
            &vfs,
            &bundle,
            null,
            .{ .io = io, .corex_home_dir = corex_home, .local_registry_dir = reg_dir },
            &sink,
        );
        try std.testing.expect(links_res == null);
        try std.testing.expect(hasSinkDiagnosticCode(&sink, .e0011_native_links_collision));
    }

    // [4] Mock registry (signed + Tlog!) + local Git repo + `path` dep + unlocked auto-sync +
    //     `--locked`/`--frozen` (`E0014`) + `--offline` (`E0016`) + `--verify-checksums` (`E0015`) + reproducible `--frozen`:
    {
        // Create signed + RFC 6962 Tlog-verified registry package `auto-lib@1.0.0`:
        const auto_src = "pub fn auto_val() -> i32 {\n    return 21;\n}\n";
        const auto_src_path = try writeFixtureFile(allocator, io, reg_dir, "packages/auto-lib-1.0.0/src/root.cx", auto_src);
        defer allocator.free(auto_src_path);
        var auto_src_b3: [32]u8 = undefined;
        std.crypto.hash.Blake3.hash(auto_src, &auto_src_b3, .{});
        const auto_entries = [_]pkg_cache.CxTreeInputEntry{
            .{ .rel_path = "src/root.cx", .file_mode = 0x01, .file_size = auto_src.len, .file_blake3 = auto_src_b3 },
        };
        const auto_tree = try pkg_cache.buildCxTreeBytes(allocator, "auto-lib", &auto_entries, null, Span.init(.none, 0, 0));
        defer allocator.free(auto_tree.bytes);
        const auto_tree_hex = std.fmt.bytesToHex(auto_tree.tree_blake3, .lower);

        const kp = try std.crypto.sign.Ed25519.KeyPair.generateDeterministic(@splat(0x77));
        const sig_payload = try std.fmt.allocPrint(allocator, "corex-publish-v1\nauto-lib\n1.0.0\n{s}", .{&auto_tree_hex});
        defer allocator.free(sig_payload);
        const sig = try kp.sign(sig_payload, null);
        const pk_hex = std.fmt.bytesToHex(kp.public_key.toBytes(), .lower);
        const sig_hex = std.fmt.bytesToHex(sig.toBytes(), .lower);
        const tlog_root_hex = std.fmt.bytesToHex(pkg_cache.computeRfc6962LeafHash(sig_payload), .lower);

        const idx_auto_line = try std.fmt.allocPrint(
            allocator,
            "{{\"name\":\"auto-lib\",\"vers\":\"1.0.0\",\"deps\":[],\"tree_hash\":\"b3:{s}\"," ++
                "\"pub_key\":\"{s}\",\"sig\":\"{s}\",\"tlog_index\":0,\"tlog_tree_size\":1," ++
                "\"tlog_root\":\"b3:{s}\",\"tlog_proof\":[]}}\n",
            .{ &auto_tree_hex, &pk_hex, &sig_hex, &tlog_root_hex },
        );
        defer allocator.free(idx_auto_line);
        const idx_auto_path = try writeFixtureFile(allocator, io, reg_dir, "index/au/to/auto-lib", idx_auto_line);
        defer allocator.free(idx_auto_path);

        // Create local Git fixture repository `git_dep` with `.git/HEAD` + `refs/tags/v1.0.0`:
        const git_oid = "0123456789abcdef0123456789abcdef01234567";
        const git_repo_dir = try std.fmt.allocPrint(allocator, "{s}/git_dep", .{temp_dir});
        defer allocator.free(git_repo_dir);
        const git_head = try writeFixtureFile(allocator, io, git_repo_dir, ".git/HEAD", "ref: refs/heads/main\n");
        defer allocator.free(git_head);
        const git_tag = try writeFixtureFile(allocator, io, git_repo_dir, ".git/refs/tags/v1.0.0", git_oid ++ "\n");
        defer allocator.free(git_tag);
        const git_toml = try writeFixtureFile(
            allocator,
            io,
            git_repo_dir,
            "corex.toml",
            "[package]\nname = \"git-dep\"\nversion = \"1.0.0\"\n",
        );
        defer allocator.free(git_toml);
        const git_src = try writeFixtureFile(
            allocator,
            io,
            git_repo_dir,
            "src/root.cx",
            "pub fn git_val() -> i32 {\n    return 11;\n}\n",
        );
        defer allocator.free(git_src);

        // Create local `path` dependency `local_dep`:
        const local_dep_dir = try std.fmt.allocPrint(allocator, "{s}/local_dep", .{temp_dir});
        defer allocator.free(local_dep_dir);
        const local_toml = try writeFixtureFile(
            allocator,
            io,
            local_dep_dir,
            "corex.toml",
            "[package]\nname = \"local-dep\"\nversion = \"0.1.0\"\n",
        );
        defer allocator.free(local_toml);
        const local_src = try writeFixtureFile(
            allocator,
            io,
            local_dep_dir,
            "src/root.cx",
            "pub fn local_val() -> i32 {\n    return 10;\n}\n",
        );
        defer allocator.free(local_src);

        // Create workspace `full_app` with `git-dep` & `local-dep`, plus bare `use auto_lib;` to trigger unlocked auto-sync:
        const app_dir = try std.fmt.allocPrint(allocator, "{s}/full_app", .{temp_dir});
        defer allocator.free(app_dir);
        const app_toml_initial =
            "# App manifest comment\n" ++
            "[package]\nname = \"full-app\"\nversion = \"0.1.0\"\n" ++
            "[dependencies]\n" ++
            "local-dep = { path = \"../local_dep\" }\n" ++
            "git-dep   = { git = \"../git_dep\", tag = \"v1.0.0\" }\n";
        const app_toml_path = try writeFixtureFile(allocator, io, app_dir, "corex.toml", app_toml_initial);
        defer allocator.free(app_toml_path);
        const app_main_src =
            "use auto_lib.auto_val;\n" ++
            "use git_dep.git_val;\n" ++
            "use local_dep.local_val;\n" ++
            "fn main() -> i32 {\n" ++
            "    return (auto_val() + git_val() + local_val()) - 42;\n" ++
            "}\n";
        const app_main_path = try writeFixtureFile(allocator, io, app_dir, "src/main.cx", app_main_src);
        defer allocator.free(app_main_path);

        var env_map = try buildHermeticEnvMap(allocator, corex_home, reg_dir, false);
        defer env_map.deinit();

        // `--locked` before `corex.lock` exists MUST fail with `E0014`:
        var missing_lock_res = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "check", "--locked", "--manifest-path", app_toml_path },
        );
        defer missing_lock_res.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 1), missing_lock_res.exit_code);
        try std.testing.expect(std.mem.indexOf(u8, missing_lock_res.stderr, "E0014") != null);

        // `--offline` on a cold empty cache MUST fail with `E0016` (`e0016_offline_or_fetch_failed`):
        const cold_home = try std.fmt.allocPrint(allocator, "{s}/cold_empty_home", .{temp_dir});
        defer allocator.free(cold_home);
        const offline_ws = try std.fmt.allocPrint(allocator, "{s}/offline_ws", .{temp_dir});
        defer allocator.free(offline_ws);
        const offline_toml = try writeFixtureFile(
            allocator,
            io,
            offline_ws,
            "corex.toml",
            "[package]\nname = \"offline-app\"\nversion = \"0.1.0\"\n[dependencies]\nauto-lib = \"1.0.0\"\n",
        );
        defer allocator.free(offline_toml);
        const offline_main = try writeFixtureFile(allocator, io, offline_ws, "src/main.cx", "fn main() -> i32 = 0;\n");
        defer allocator.free(offline_main);
        {
            var interner = try StringInterner.init(allocator);
            defer interner.deinit();
            var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &interner);
            defer vfs.deinit(io);
            var off_sink = DiagnosticSink.init(allocator);
            defer off_sink.deinit();
            const cfg_env = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.host(), false);
            const off_fid = try vfs.resolveOrCreatePath(io, offline_toml, .root);
            var off_bundle = try pkg_manifest.loadWorkspaceManifestBundle(
                io,
                allocator,
                &interner,
                offline_toml,
                off_fid,
                &cfg_env,
                &off_sink,
            );
            defer off_bundle.deinit();
            const off_graph = try pkg_resolver.resolveProjectGraph(
                allocator,
                &interner,
                &vfs,
                &off_bundle,
                null,
                .{ .io = io, .corex_home_dir = cold_home, .local_registry_dir = reg_dir, .is_offline = true },
                &off_sink,
            );
            try std.testing.expect(off_graph == null);
            try std.testing.expect(hasSinkDiagnosticCode(&off_sink, .e0016_offline_or_fetch_failed));
        }

        // Unlocked `corex build` auto-syncs `auto-lib = "1.0.0"` into `corex.toml` and writes `corex.lock`:
        const out_bin_1 = try std.fmt.allocPrint(allocator, "{s}/bin_1", .{temp_dir});
        defer allocator.free(out_bin_1);
        var build_1 = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "build", "--manifest-path", app_toml_path, "-o", out_bin_1 },
        );
        defer build_1.deinit(allocator);
        if (build_1.exit_code != 0) {
            std.debug.print("build_1 stderr:\n{s}\n", .{build_1.stderr});
        }
        try std.testing.expectEqual(@as(u8, 0), build_1.exit_code);

        const synced_toml = try std.Io.Dir.cwd().readFileAlloc(io, app_toml_path, allocator, .limited(16 * 1024));
        defer allocator.free(synced_toml);
        try std.testing.expect(std.mem.indexOf(u8, synced_toml, "# App manifest comment\n") != null);
        try std.testing.expect(std.mem.indexOf(u8, synced_toml, "auto-lib") != null);

        // Bit-for-bit reproducible `--frozen` build (with registry deleted to prove 100% offline cache resolution!):
        const out_bin_a = try std.fmt.allocPrint(allocator, "{s}/frozen_bin_a", .{temp_dir});
        defer allocator.free(out_bin_a);
        const out_bin_b = try std.fmt.allocPrint(allocator, "{s}/frozen_bin_b", .{temp_dir});
        defer allocator.free(out_bin_b);
        var hermetic_env = try buildHermeticEnvMap(allocator, corex_home, null, true);
        defer hermetic_env.deinit();

        var frozen_a = try runCliCaptured(
            allocator,
            io,
            &hermetic_env,
            &.{ "--color=never", "build", "--frozen", "--manifest-path", app_toml_path, "-o", out_bin_a },
        );
        defer frozen_a.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 0), frozen_a.exit_code);

        var frozen_b = try runCliCaptured(
            allocator,
            io,
            &hermetic_env,
            &.{ "--color=never", "build", "--frozen", "--manifest-path", app_toml_path, "-o", out_bin_b },
        );
        defer frozen_b.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 0), frozen_b.exit_code);

        const bytes_a = try std.Io.Dir.cwd().readFileAlloc(io, out_bin_a, allocator, .limited(16 * 1024 * 1024));
        defer allocator.free(bytes_a);
        const bytes_b = try std.Io.Dir.cwd().readFileAlloc(io, out_bin_b, allocator, .limited(16 * 1024 * 1024));
        defer allocator.free(bytes_b);
        try std.testing.expectEqualSlices(u8, bytes_a, bytes_b);

        // Mutating `corex.toml` under `--frozen` MUST fail with `E0014`:
        const drifted_toml = try std.fmt.allocPrint(allocator, "{s}\n[features]\nextra_mode = []\n", .{synced_toml});
        defer allocator.free(drifted_toml);
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = app_toml_path, .data = drifted_toml });
        var drift_res = try runCliCaptured(
            allocator,
            io,
            &hermetic_env,
            &.{ "--color=never", "check", "--frozen", "--manifest-path", app_toml_path },
        );
        defer drift_res.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 1), drift_res.exit_code);
        try std.testing.expect(std.mem.indexOf(u8, drift_res.stderr, "E0014") != null);

        // Restore `synced_toml`, tamper with cached blob on disk, and verify `--verify-checksums` emits `E0015`:
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = app_toml_path, .data = synced_toml });
        const blob_hex = std.fmt.bytesToHex(auto_src_b3, .lower);
        const cached_blob_path = try std.fmt.allocPrint(
            allocator,
            "{s}/cache/blake3/blobs/{s}/{s}",
            .{ corex_home, blob_hex[0..2], blob_hex[2..64] },
        );
        defer allocator.free(cached_blob_path);
        if (std.Io.Dir.cwd().openFile(io, cached_blob_path, .{ .mode = .read_only })) |ro_file| {
            const st = try ro_file.stat(io);
            ro_file.setPermissions(io, st.permissions.setReadOnly(false)) catch {};
            ro_file.close(io);
        } else |_| {}
        std.Io.Dir.cwd().deleteFile(io, cached_blob_path) catch {};
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = cached_blob_path, .data = "pub fn auto_val() -> i32 = 999;\n" });

        var tamper_check = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "check", "--locked", "--verify-checksums", "--manifest-path", app_toml_path },
        );
        defer tamper_check.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 1), tamper_check.exit_code);
        try std.testing.expect(std.mem.indexOf(u8, tamper_check.stderr, "E0015") != null);
    }
}

// ------ Pillar 5: Multi-Pkg DB, E0012, `.cxi` & Sandbox -------

test "test_phase9_multipkg_db_cross_major_e0012_cxi_sandbox_and_entrypoint" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    const temp_dir = try createIsolatedTempDir(allocator, io, "db_sandbox");
    defer allocator.free(temp_dir);
    defer std.Io.Dir.cwd().deleteTree(io, temp_dir) catch {};

    const corex_home = try std.fmt.allocPrint(allocator, "{s}/corex_home", .{temp_dir});
    defer allocator.free(corex_home);
    const reg_dir = try std.fmt.allocPrint(allocator, "{s}/mock_reg", .{temp_dir});
    defer allocator.free(reg_dir);
    try std.Io.Dir.cwd().createDirPath(io, corex_home);
    try std.Io.Dir.cwd().createDirPath(io, reg_dir);

    // [1] Submodule `use pkg.RootType;`, undeclared transitive dep rejection, `Durability.high` external stdlib
    //     firewall (`E0218` on `use core.mem;`, `E0327` on `@trusted`/`@std_cap_boundary` even inside inactive `@cfg`!),
    //     and `@cfg(cfg.feature.undeclared)` emitting `E0435`:
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.X86_64_LINUX_GNU);
        db.setPackageGraphMounted(true);

        const pkg_trans = PackageId.fromInt(2);
        const pkg_ext = PackageId.fromInt(3);
        const fid_trans = FileId.fromInt(10);
        const fid_ext_root = FileId.fromInt(11);
        const fid_ext_sub = FileId.fromInt(12);
        const fid_app = FileId.fromInt(13);

        _ = try db.setInput(fid_trans, "pub struct HiddenTrans { pub val: i32 }\n", .high);
        _ = try db.setInput(
            fid_ext_root,
            "pub mod sub;\npub struct RootType { pub code: i32 }\n",
            .high,
        );
        _ = try db.setInput(
            fid_ext_sub,
            "use pkg.RootType;\npub fn make_root(val: i32) -> RootType {\n    return RootType { code: val };\n}\n",
            .high,
        );
        try db.bindExternalModule(fid_ext_root, "sub", fid_ext_sub);
        try db.registerPackageRootFile(pkg_trans, fid_trans);
        try db.registerPackageRootFile(pkg_ext, fid_ext_root);
        try db.bindPackageDepFile(pkg_ext, try db.interner.intern("trans_pkg"), fid_trans);

        const declared_feats = [_][]const u8{"tls"};
        try db.setPackageCfgFeatures(pkg_ext, &declared_feats, &declared_feats);
        try db.setPackageCfgFeatures(.root, &.{}, &.{});

        // Root binds ONLY `ext_pkg` (NOT `trans_pkg`), verifying `use pkg.RootType;` succeeds while `use trans_pkg` fails:
        _ = try db.setInput(
            fid_app,
            "use ext_pkg.sub.make_root;\npub fn run_ok() -> i32 {\n    return make_root(9).code;\n}\n",
            .low,
        );
        try db.registerPackageRootFile(.root, fid_app);
        try db.bindPackageDepFile(.root, try db.interner.intern("ext_pkg"), fid_ext_root);

        try std.testing.expectEqual(@as(u32, 0), (try db.resolveSignatures(fid_ext_sub)).error_count);
        const app_tree = try db.extractItemTree(fid_app);
        try std.testing.expectEqual(@as(u32, 0), (try db.typecheckBody(app_tree.entries[1].def_id)).error_count);

        // Undeclared transitive `use trans_pkg.HiddenTrans;` from `.root` MUST be rejected:
        const fid_undecl = FileId.fromInt(14);
        _ = try db.setInput(fid_undecl, "use trans_pkg.HiddenTrans;\npub fn bad() -> i32 = 0;\n", .low);
        db.symbol_table.setFilePackageId(fid_undecl, .root) catch unreachable;
        try std.testing.expect((try db.resolveSignatures(fid_undecl)).error_count >= 1);

        // `Durability.high` external package (`PackageId >= 2`) stdlib firewall:
        // - `use core.mem;` -> `E0218` (`e0218_direct_core_import_forbidden`)
        // - `@trusted` / `@std_cap_boundary` inside inactive `@cfg(target.os == .Windows)` -> `E0327`
        // - `@cfg(cfg.feature.undeclared_feat)` -> `E0435` (`e0435_unknown_cfg_feature` / `e0435_invalid_cfg_predicate`):
        const fid_firewall = FileId.fromInt(15);
        const firewall_src =
            "use core.mem;\n" ++
            "@cfg(target.os == .Windows)\n" ++
            "@trusted\n" ++
            "pub fn sneaky_inactive_bypass() -> i32 = 1;\n" ++
            "@cfg(cfg.feature.undeclared_feat)\n" ++
            "pub fn bad_feat_gate() -> i32 = 2;\n";
        _ = try db.setInput(fid_firewall, firewall_src, .high);
        db.symbol_table.setFilePackageId(fid_firewall, pkg_ext) catch unreachable;
        _ = try db.resolveSignatures(fid_firewall);
        const fw_diags = db.getSignatureDiagnostics(fid_firewall).?;
        try std.testing.expect(hasSinkDiagnosticCode(fw_diags, .e0218_direct_core_import_forbidden));
        try std.testing.expect(hasSinkDiagnosticCode(fw_diags, .e0327_forbidden_sandbox_bypass_attribute));
        try std.testing.expect(hasSinkDiagnosticCode(fw_diags, .e0435_invalid_cfg_predicate));
    }

    // [2] Cross-major `E0012` (`e0012_cross_major_cxi_type_mismatch`) on direct nominal, `Result` (`T!E`), and trait bound:
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setPackageGraphMounted(true);

        const pkg_v1 = PackageId.fromInt(2);
        const pkg_v2 = PackageId.fromInt(3);
        const fid_v1 = FileId.fromInt(20);
        const fid_v2 = FileId.fromInt(21);
        const fid_caller = FileId.fromInt(22);

        const http_pkg_src =
            "pub struct Resp {\n    pub status: i32,\n}\n" ++
            "pub trait Handler {\n    fn code(self: &Self) -> i32;\n}\n" ++
            "pub struct ImplV1 {\n    pub tag: i32,\n}\n" ++
            "impl Handler for ImplV1 {\n    fn code(self: &Self) -> i32 { return self.tag; }\n}\n";
        _ = try db.setInput(fid_v1, http_pkg_src, .high);
        _ = try db.setInput(fid_v2, http_pkg_src, .high);

        try db.registerPackageRootFile(pkg_v1, fid_v1);
        try db.registerPackageRootFile(pkg_v2, fid_v2);
        try db.symbol_table.setPackageIdentityMeta(&db.interner, pkg_v1, "corex-http", "1.8.0", "http_v1", fid_v1);
        try db.symbol_table.setPackageIdentityMeta(&db.interner, pkg_v2, "corex-http", "2.1.0", "http_v2", fid_v2);

        const caller_src =
            "use http_v1;\n" ++
            "use http_v2;\n" ++
            "fn take_v2_resp(resp: http_v2.Resp) -> i32 { return resp.status; }\n" ++
            "fn take_v2_result(res: http_v2.Resp!i32) -> i32 {\n" ++
            "    match res {\n" ++
            "        .Ok(val) => return val.status,\n" ++
            "        .Err(err_code) => return err_code,\n" ++
            "    }\n" ++
            "}\n" ++
            "fn take_v2_handler[T: http_v2.Handler](item: T) -> i32 { return item.code(); }\n" ++
            "pub fn trigger_direct() -> i32 {\n" ++
            "    let r1 = http_v1.Resp { status: 200 };\n" ++
            "    return take_v2_resp(r1);\n" ++
            "}\n" ++
            "pub fn trigger_generic_result() -> i32 {\n" ++
            "    let r1: http_v1.Resp!i32 = .Ok(http_v1.Resp { status: 201 });\n" ++
            "    return take_v2_result(r1);\n" ++
            "}\n" ++
            "pub fn trigger_trait_bound() -> i32 {\n" ++
            "    let h1 = http_v1.ImplV1 { tag: 7 };\n" ++
            "    return take_v2_handler(h1);\n" ++
            "}\n";
        _ = try db.setInput(fid_caller, caller_src, .low);
        try db.registerPackageRootFile(.root, fid_caller);
        try db.bindPackageDepFile(.root, try db.interner.intern("http_v1"), fid_v1);
        try db.bindPackageDepFile(.root, try db.interner.intern("http_v2"), fid_v2);

        const caller_tree = try db.extractItemTree(fid_caller);
        var e0012_fn_count: usize = 0;
        for (caller_tree.entries) |entry| {
            if (std.mem.startsWith(u8, entry.name_text, "trigger_")) {
                _ = try db.typecheckBody(entry.def_id);
                const body_diags = db.getBodyDiagnostics(entry.def_id).?;
                try std.testing.expect(hasSinkDiagnosticCode(body_diags, .e0012_cross_major_cxi_type_mismatch));
                e0012_fn_count += 1;
            }
        }
        try std.testing.expectEqual(@as(usize, 3), e0012_fn_count);
    }

    // [3] `.cxi` `pkg_cxi_seam` digest stability across private body/comment/`pub(pkg)` edits vs change on signature or `surface_caps`:
    {
        const computeIsolatedCxi = struct {
            /// Compiles `source_text` inside a clean multi-package `CompilerDb` and returns its `PackageCxiArtifact`.
            fn run(alloc: std.mem.Allocator, source_text: []const u8) !corex.query_db.PackageCxiArtifact {
                var iso_db = try CompilerDb.init(alloc);
                defer iso_db.deinit();
                iso_db.setPackageGraphMounted(true);
                const pkg_lib = PackageId.fromInt(2);
                const fid_lib = FileId.fromInt(30);
                _ = try iso_db.setInput(fid_lib, source_text, .high);
                try iso_db.registerPackageRootFile(pkg_lib, fid_lib);
                return iso_db.computePackageCxiSummary(alloc, pkg_lib, &.{fid_lib});
            }
        }.run;

        const src_v1 =
            "// Initial doc comment\n" ++
            "fn private_helper(seed: i32) -> i32 { return seed +% 1; }\n" ++
            "pub(pkg) fn internal_pkg_only(val: i32) -> i32 { return val +% 5; }\n" ++
            "pub fn exported_calc(val: i32) -> i32 { return private_helper(val); }\n";
        var cxi_1 = try computeIsolatedCxi(allocator, src_v1);
        defer cxi_1.deinit(allocator);

        // Private body, `pub(pkg)`, & comment edit MUST preserve `cxi_blake3` bit-for-bit:
        const src_v2_private_edit =
            "// Updated comment and private/pub(pkg) implementation\n" ++
            "fn private_helper(seed: i32) -> i32 { return seed +% 77; }\n" ++
            "pub(pkg) fn internal_pkg_only(val: i32) -> i32 { return val *% 9; }\n" ++
            "pub fn exported_calc(val: i32) -> i32 { return private_helper(val); }\n";
        var cxi_2 = try computeIsolatedCxi(allocator, src_v2_private_edit);
        defer cxi_2.deinit(allocator);
        try std.testing.expectEqualSlices(u8, &cxi_1.cxi_blake3, &cxi_2.cxi_blake3);

        // Public signature change MUST alter `cxi_blake3`:
        const src_v3_sig_change =
            "pub fn exported_calc(val: i64) -> i64 { return val +% 1; }\n";
        var cxi_3 = try computeIsolatedCxi(allocator, src_v3_sig_change);
        defer cxi_3.deinit(allocator);
        try std.testing.expect(!std.mem.eql(u8, &cxi_1.cxi_blake3, &cxi_3.cxi_blake3));

        // Adding `surface_caps` (`ffi` + `unsafe_op` while keeping `pub fn exported_calc(val: i32) -> i32`) MUST alter `cxi_blake3`:
        const src_v4_cap_change =
            "extern \"C\" fn sneaky_c_call() -> i32;\n" ++
            "pub fn exported_calc(val: i32) -> i32 { return val +% unsafe { sneaky_c_call() }; }\n";
        var cxi_4 = try computeIsolatedCxi(allocator, src_v4_cap_change);
        defer cxi_4.deinit(allocator);
        try std.testing.expect(!std.mem.eql(u8, &cxi_1.cxi_blake3, &cxi_4.cxi_blake3));
    }

    // [4] Supply-chain sandboxing: transitive capability laundering (`E0324` with witness!), default-arg & `pub subscript`
    //     & inactive `@cfg(target.os == .Windows)` capability detection, dead high-risk `W0330`, comptime `E0325`,
    //     and `.cxtree` / symlink `@embed_bytes` & `@c_import` escape rejection (`E0326`):
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(TargetSpec.X86_64_LINUX_GNU);
        db.setPackageGraphMounted(true);

        const pkg_a = PackageId.fromInt(2);
        const pkg_b = PackageId.fromInt(3);
        const fid_root = FileId.fromInt(40);
        const fid_a = FileId.fromInt(41);
        const fid_b = FileId.fromInt(42);

        // `pkg_b` uses `cx.net` inside inactive `@cfg(target.os == .Windows)`, `ffi` in a default arg & `pub subscript`,
        // plus an unreachable dead `process` function (`W0330`):
        const src_b =
            "extern \"C\" fn c_ffi_default() -> i32;\n" ++
            "pub struct SubBox {\n" ++
            "    pub val: i32,\n" ++
            "    pub subscript(idx: usize) -> i32 {\n" ++
            "        yield unsafe { c_ffi_default() } + @int_cast(i32, idx);\n" ++
            "    }\n" ++
            "}\n" ++
            "@cfg(target.os == .Windows)\n" ++
            "pub fn win_only_net() -> i32 {\n" ++
            "    return cx.net.connect();\n" ++
            "}\n" ++
            "pub fn leaf_action(seed: i32 = unsafe { c_ffi_default() }) -> i32 {\n" ++
            "    return seed + 1;\n" ++
            "}\n" ++
            "fn dead_unreachable_proc() -> i32 {\n" ++
            "    return unsafe { c_ffi_default() };\n" ++
            "}\n";
        const src_a =
            "use pkg_b.leaf_action;\n" ++
            "pub fn bridge_action() -> i32 {\n" ++
            "    return leaf_action(10);\n" ++
            "}\n";
        const src_root =
            "use pkg_a.bridge_action;\n" ++
            "pub fn app_entry() -> i32 {\n" ++
            "    return bridge_action();\n" ++
            "}\n";

        _ = try db.setInput(fid_b, src_b, .high);
        _ = try db.setInput(fid_a, src_a, .high);
        _ = try db.setInput(fid_root, src_root, .low);

        try db.registerPackageRootFile(pkg_b, fid_b);
        try db.registerPackageRootFile(pkg_a, fid_a);
        try db.registerPackageRootFile(.root, fid_root);
        try db.bindPackageDepFile(pkg_a, try db.interner.intern("pkg_b"), fid_b);
        try db.bindPackageDepFile(.root, try db.interner.intern("pkg_a"), fid_a);

        // Typecheck bodies so cross-package call witnesses are recorded:
        for ([_]FileId{ fid_b, fid_a, fid_root }) |check_fid| {
            const tree = try db.extractItemTree(check_fid);
            for (tree.entries) |ent| {
                if (ent.kind == .fn_decl) _ = try db.typecheckBody(ent.def_id);
            }
        }

        // Configure laundering attempt: `.root` allows `net | ffi | unsafe_op` on `pkg_a`,
        // but `pkg_a -> pkg_b` edge denies `net` (`allow_caps = EMPTY`):
        const non_os_bits: u16 = 0x0FFF & ~mir_sast.EffectCapabilityMask.LOCKFILE_CAP_BITS;
        try db.setPackageCapPolicy(.root, .{
            .package_name = "root",
            .allowed_caps = mir_sast.EffectCapabilityMask.fromBits(0x0FFF),
            .is_third_party_dependency = false,
        });
        try db.setPackageCapPolicy(pkg_a, .{
            .package_name = "pkg-a@1.0.0",
            .policy_span = Span.init(fid_a, 0, 10),
            .allowed_caps = mir_sast.EffectCapabilityMask.fromBits(0x0FFF),
            .is_third_party_dependency = true,
        });
        try db.setPackageCapPolicy(pkg_b, .{
            .package_name = "pkg-b@1.0.0",
            .policy_span = Span.init(fid_b, 0, 10),
            .allowed_caps = mir_sast.EffectCapabilityMask.fromBits(non_os_bits),
            .is_third_party_dependency = true,
            .is_warning_ambient_dead_caps = true,
        });

        var pkg_files_map: std.AutoHashMapUnmanaged(PackageId, []const FileId) = .empty;
        defer pkg_files_map.deinit(allocator);
        try pkg_files_map.put(allocator, pkg_b, &.{fid_b});
        try pkg_files_map.put(allocator, pkg_a, &.{fid_a});
        try pkg_files_map.put(allocator, .root, &.{fid_root});

        const cap_edges = [_]mir_sast.WorkspacePackageEdge{
            .{
                .caller_pkg = .root,
                .callee_pkg = pkg_a,
                .edge_label = "pkg_a",
                .edge_span = Span.init(fid_root, 0, 10),
                .allow_caps = mir_sast.EffectCapabilityMask.fromBits(0x0FFF),
            },
            .{
                .caller_pkg = pkg_a,
                .callee_pkg = pkg_b,
                .edge_label = "pkg_b",
                .edge_span = Span.init(fid_a, 0, 10),
                .allow_caps = mir_sast.EffectCapabilityMask.fromBits(non_os_bits),
            },
        };
        const pkg_order = [_]PackageId{ pkg_b, pkg_a, .root };

        var cap_sink = DiagnosticSink.init(allocator);
        defer cap_sink.deinit();
        const reports = try db.verifyWorkspaceCapabilitySandbox(
            allocator,
            &pkg_order,
            &pkg_files_map,
            &cap_edges,
            &cap_sink,
        );
        defer allocator.free(reports);

        try std.testing.expect(hasSinkDiagnosticCode(&cap_sink, .e0324_package_capability_violation));
        // Also verify `W0330` dead high-risk capability warning when `pkg-dead` has ONLY unreachable `extern`/`unsafe`:
        const pkg_dead = PackageId.fromInt(4);
        const fid_dead = FileId.fromInt(43);
        const dead_src =
            "extern \"C\" fn unused_foreign() -> i32;\n" ++
            "pub fn safe_exported(val: i32) -> i32 { return val + 1; }\n" ++
            "fn unreachable_foreign_caller() -> i32 { return unsafe { unused_foreign() }; }\n";
        _ = try db.setInput(fid_dead, dead_src, .high);
        try db.registerPackageRootFile(pkg_dead, fid_dead);
        try db.setPackageCapPolicy(pkg_dead, .{
            .package_name = "dead-cap-pkg@1.0.0",
            .policy_span = Span.init(fid_dead, 0, 10),
            .allowed_caps = mir_sast.EffectCapabilityMask.fromBits(non_os_bits),
            .is_third_party_dependency = true,
            .is_warning_ambient_dead_caps = true,
        });
        try pkg_files_map.put(allocator, pkg_dead, &.{fid_dead});
        var dead_sink = DiagnosticSink.init(allocator);
        defer dead_sink.deinit();
        const dead_reports = try db.verifyWorkspaceCapabilitySandbox(
            allocator,
            &.{pkg_dead},
            &pkg_files_map,
            &.{},
            &dead_sink,
        );
        defer allocator.free(dead_reports);
        try std.testing.expect(hasSinkDiagnosticCode(&dead_sink, .w0330_ambient_dead_capability_in_dep));

        // Comptime sandbox violation (`E0325`):
        const fid_ct = FileId.fromInt(44);
        _ = try db.setInput(
            fid_ct,
            "extern \"C\" fn host_env() -> i32;\nfn bridge() -> i32 { return unsafe { host_env() }; }\npub const BAD: i32 = bridge();\n",
            .low,
        );
        const ct_tree = try db.extractItemTree(fid_ct);
        const ct_art = try db.evalComptimeDef(ct_tree.entries[2].def_id);
        try std.testing.expect(ct_art.has_errors);
        try std.testing.expect(
            hasSinkDiagnosticCode(db.getComptimeDiagnostics(ct_tree.entries[2].def_id).?, .e0325_comptime_sandbox_violation),
        );

        // `.cxtree` and host symlink `@embed_bytes` & `@c_import` escape rejection (`E0326`):
        const jail_dir = try std.fmt.allocPrint(allocator, "{s}/embed_jail", .{temp_dir});
        defer allocator.free(jail_dir);
        const outside_secret = try writeFixtureFile(allocator, io, temp_dir, "outside_secret.txt", "TOP_SECRET");
        defer allocator.free(outside_secret);
        const outside_hdr = try writeFixtureFile(allocator, io, temp_dir, "outside_hdr.h", "int leak(void);\n");
        defer allocator.free(outside_hdr);
        try std.Io.Dir.cwd().createDirPath(io, jail_dir);

        // Create symlinks inside `jail_dir` pointing outside `jail_dir` (on POSIX) and verify `E0326` on symlink escape:
        if (builtin.os.tag != .windows) {
            const sym_hdr_path = try std.fmt.allocPrint(allocator, "{s}/escape_link.h", .{jail_dir});
            defer allocator.free(sym_hdr_path);
            std.Io.Dir.cwd().symLink(io, "../outside_hdr.h", sym_hdr_path, .{}) catch {};

            db.embed_io = io;
            const pkg_host_jailed = PackageId.fromInt(6);
            try db.setPackageEmbedJail(pkg_host_jailed, .{ .host_dir_jailed = jail_dir });
            const fid_sym_escape = FileId.fromInt(47);
            _ = try db.setInput(
                fid_sym_escape,
                "const sym_c = @c_import(\"escape_link.h\");\npub fn g() -> i32 = 0;\n",
                .high,
            );
            db.symbol_table.setFilePackageId(fid_sym_escape, pkg_host_jailed) catch unreachable;
            _ = try db.resolveSignatures(fid_sym_escape);
            try std.testing.expect(
                hasSinkDiagnosticCode(db.getSignatureDiagnostics(fid_sym_escape).?, .e0326_embed_path_escape),
            );
        }

        const pkg_jailed = PackageId.fromInt(5);
        try db.setPackageEmbedJail(pkg_jailed, .{
            .cxtree_only = .{ .pkg_id = pkg_jailed, .virtual_root_prefix = "/cx/jailed-pkg@1.0.0" },
        });

        const fid_escape_embed = FileId.fromInt(45);
        _ = try db.setInput(
            fid_escape_embed,
            "pub const ESC: &[u8] = @embed_bytes(\"../outside_secret.txt\");\n",
            .high,
        );
        db.symbol_table.setFilePackageId(fid_escape_embed, pkg_jailed) catch unreachable;
        const esc_tree = try db.extractItemTree(fid_escape_embed);
        const esc_eval = try db.evalComptimeDef(esc_tree.entries[0].def_id);
        try std.testing.expect(esc_eval.has_errors);
        const esc_ct_diags = db.getComptimeDiagnostics(esc_tree.entries[0].def_id).?;
        try std.testing.expect(hasSinkDiagnosticCode(esc_ct_diags, .e0326_embed_path_escape));

        const fid_escape_c = FileId.fromInt(46);
        _ = try db.setInput(
            fid_escape_c,
            "const bad_c = @c_import(\"../outside_hdr.h\");\npub fn f() -> i32 = 0;\n",
            .high,
        );
        db.symbol_table.setFilePackageId(fid_escape_c, pkg_jailed) catch unreachable;
        _ = try db.resolveSignatures(fid_escape_c);
        try std.testing.expect(
            hasSinkDiagnosticCode(db.getSignatureDiagnostics(fid_escape_c).?, .e0326_embed_path_escape),
        );
    }

    // [5] Dependency `pub fn main() -> i32 { return 99; }` does NOT hijack `PackageId.root`'s `fn main() -> i32 { return 0; }`
    //     in BOTH C99 (`--ofmt=c`) and LLVM (`--ofmt=llvm`) codegen + POSIX executable `+x` permission check:
    {
        const dep_main_src = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "packages/dep-with-main-1.0.0/src/root.cx",
            "pub fn helper_seven() -> i32 { return 7; }\npub fn main() -> i32 { return 99; }\n",
        );
        defer allocator.free(dep_main_src);
        const idx_dep_main = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/de/p-/dep-with-main",
            "{\"name\":\"dep-with-main\",\"vers\":\"1.0.0\",\"deps\":[]}\n",
        );
        defer allocator.free(idx_dep_main);

        const entry_ws = try std.fmt.allocPrint(allocator, "{s}/entry_ws", .{temp_dir});
        defer allocator.free(entry_ws);
        const entry_toml = try writeFixtureFile(
            allocator,
            io,
            entry_ws,
            "corex.toml",
            "[package]\nname = \"entry-app\"\nversion = \"0.1.0\"\n[dependencies]\ndep-with-main = \"1.0.0\"\n",
        );
        defer allocator.free(entry_toml);
        const entry_main = try writeFixtureFile(
            allocator,
            io,
            entry_ws,
            "src/main.cx",
            "use dep_with_main.helper_seven;\nfn main() -> i32 {\n    return helper_seven() - 7;\n}\n",
        );
        defer allocator.free(entry_main);

        var env_map = try buildHermeticEnvMap(allocator, corex_home, reg_dir, false);
        defer env_map.deinit();

        for ([_][]const u8{ "c", "llvm" }) |backend_name| {
            const out_exe = try std.fmt.allocPrint(allocator, "{s}/entry_{s}_exe", .{ temp_dir, backend_name });
            defer allocator.free(out_exe);
            const ofmt_arg = try std.fmt.allocPrint(allocator, "--ofmt={s}", .{backend_name});
            defer allocator.free(ofmt_arg);

            var build_res = try runCliCaptured(
                allocator,
                io,
                &env_map,
                &.{ "--color=never", "build", ofmt_arg, "--manifest-path", entry_toml, "-o", out_exe },
            );
            defer build_res.deinit(allocator);
            if (build_res.exit_code != 0) {
                std.debug.print("entry build ({s}) stderr:\n{s}\n", .{ backend_name, build_res.stderr });
            }
            try std.testing.expectEqual(@as(u8, 0), build_res.exit_code);

            // Verify POSIX `+x` executable permission bit and direct execution returning `0` (NOT `99`!):
            if (builtin.os.tag != .windows) {
                const exe_file = try std.Io.Dir.cwd().openFile(io, out_exe, .{ .mode = .read_only });
                defer exe_file.close(io);
                const exe_stat = try exe_file.stat(io);
                try std.testing.expect((@backingInt(exe_stat.permissions) & 0o111) != 0);
            }
            const child_run = try std.process.run(allocator, io, .{
                .argv = &.{out_exe},
                .environ_map = &env_map,
            });
            defer allocator.free(child_run.stdout);
            defer allocator.free(child_run.stderr);
            try std.testing.expectEqual(std.process.Child.Term{ .exited = 0 }, child_run.term);
        }
    }
}

// ------ Pillar 6: Red-Team & Verifier Remediation Suite -------

test "test_phase9_redteam_and_verifier_remediation_regressions" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    const temp_dir = try createIsolatedTempDir(allocator, io, "remediation");
    defer allocator.free(temp_dir);
    defer std.Io.Dir.cwd().deleteTree(io, temp_dir) catch {};

    const corex_home = try std.fmt.allocPrint(allocator, "{s}/corex_home", .{temp_dir});
    defer allocator.free(corex_home);
    const reg_dir = try std.fmt.allocPrint(allocator, "{s}/mock_reg", .{temp_dir});
    defer allocator.free(reg_dir);
    try std.Io.Dir.cwd().createDirPath(io, corex_home);
    try std.Io.Dir.cwd().createDirPath(io, reg_dir);

    var env_map = try buildHermeticEnvMap(allocator, corex_home, reg_dir, false);
    defer env_map.deinit();

    // [1] `[CRITICAL-01]` & `[HIGH-03]`: External dependency with `@std_cap_boundary` (`E0327`), `use core.mem;` (`E0218`),
    //     or inactive `@cfg(target.os == .Windows) pub fn f() { core.mem.zero(); }` fails `corex check` and writes NO `corex.lock`:
    {
        const bad_dep_specs = [_]struct {
            pkg_name: []const u8,
            sparse_rel: []const u8,
            root_cx: []const u8,
            expected_diag: []const u8,
        }{
            .{
                .pkg_name = "bad-cap-attr",
                .sparse_rel = "index/ba/d-/bad-cap-attr",
                .root_cx = "@std_cap_boundary(clears: [unsafe_op])\npub fn leak() -> i32 { return 1; }\n",
                .expected_diag = "E0327",
            },
            .{
                .pkg_name = "bad-core-use",
                .sparse_rel = "index/ba/d-/bad-core-use",
                .root_cx = "use core.mem;\npub fn leak() -> i32 { return 1; }\n",
                .expected_diag = "E0218",
            },
            .{
                .pkg_name = "bad-inact-core",
                .sparse_rel = "index/ba/d-/bad-inact-core",
                .root_cx = "@cfg(target.os == .Windows)\npub fn f() {\n    core.mem.zero();\n}\npub fn ok() -> i32 { return 1; }\n",
                .expected_diag = "E0218",
            },
        };

        for (bad_dep_specs, 0..) |spec, case_i| {
            const pkg_rel = try std.fmt.allocPrint(allocator, "packages/{s}-1.0.0/src/root.cx", .{spec.pkg_name});
            defer allocator.free(pkg_rel);
            const p_src = try writeFixtureFile(allocator, io, reg_dir, pkg_rel, spec.root_cx);
            defer allocator.free(p_src);

            const idx_line = try std.fmt.allocPrint(
                allocator,
                "{{\"name\":\"{s}\",\"vers\":\"1.0.0\",\"deps\":[]}}\n",
                .{spec.pkg_name},
            );
            defer allocator.free(idx_line);
            const p_idx = try writeFixtureFile(allocator, io, reg_dir, spec.sparse_rel, idx_line);
            defer allocator.free(p_idx);

            const case_ws = try std.fmt.allocPrint(allocator, "{s}/crit01_ws_{d}", .{ temp_dir, case_i });
            defer allocator.free(case_ws);
            const ws_toml_txt = try std.fmt.allocPrint(
                allocator,
                "[package]\nname = \"crit01-app\"\nversion = \"0.1.0\"\n[dependencies]\n{s} = \"1.0.0\"\n",
                .{spec.pkg_name},
            );
            defer allocator.free(ws_toml_txt);
            const ws_toml = try writeFixtureFile(allocator, io, case_ws, "corex.toml", ws_toml_txt);
            defer allocator.free(ws_toml);
            const snake_dep = (try pkg_resolver.canonicalPkgNameToSnakeAlloc(allocator, spec.pkg_name)).?;
            defer allocator.free(snake_dep);
            const ws_main_txt = try std.fmt.allocPrint(
                allocator,
                "use {s};\nfn main() -> i32 {{ return 0; }}\n",
                .{snake_dep},
            );
            defer allocator.free(ws_main_txt);
            const ws_main = try writeFixtureFile(allocator, io, case_ws, "src/main.cx", ws_main_txt);
            defer allocator.free(ws_main);

            var check_res = try runCliCaptured(
                allocator,
                io,
                &env_map,
                &.{ "--color=never", "check", "--manifest-path", ws_toml },
            );
            defer check_res.deinit(allocator);
            try std.testing.expect(check_res.exit_code != 0);
            try std.testing.expect(std.mem.indexOf(u8, check_res.stderr, spec.expected_diag) != null);

            const lock_candidate = try std.fmt.allocPrint(allocator, "{s}/corex.lock", .{case_ws});
            defer allocator.free(lock_candidate);
            try std.testing.expectError(
                error.FileNotFound,
                std.Io.Dir.cwd().openFile(io, lock_candidate, .{ .mode = .read_only }),
            );
        }
    }

    // [2] `[CRITICAL-02]`: `impl Drop for Guard` and `impl PublicTrait for Guard` (with `allow_caps = []`,
    //     `enforcement_scope = "surface"`) propagate capabilities into `surface_caps` and emit `E0324`:
    {
        const drop_trait_cases = [_][]const u8{
            "extern \"C\" fn raw_ping() -> i32;\n" ++
                "pub struct Guard {\n    pub v: i32,\n}\n" ++
                "impl Drop for Guard {\n" ++
                "    fn drop(&mut self) {\n" ++
                "        let _ = unsafe { raw_ping() };\n" ++
                "    }\n" ++
                "}\n",
            "extern \"C\" fn raw_env() -> i32;\n" ++
                "pub trait PublicTrait {\n    fn act(&self) -> i32;\n}\n" ++
                "pub struct Guard {\n    pub v: i32,\n}\n" ++
                "impl PublicTrait for Guard {\n" ++
                "    fn act(&self) -> i32 {\n" ++
                "        return unsafe { raw_env() };\n" ++
                "    }\n" ++
                "}\n",
        };

        for (drop_trait_cases, 0..) |dep_cx, case_idx| {
            var db = try CompilerDb.init(allocator);
            defer db.deinit();
            db.setTargetSpec(TargetSpec.X86_64_LINUX_GNU);
            db.setPackageGraphMounted(true);

            const pkg_dep = PackageId.fromInt(2);
            const fid_dep = FileId.fromInt(@intCast(60 + case_idx));
            _ = try db.setInput(fid_dep, dep_cx, .high);
            try db.registerPackageRootFile(pkg_dep, fid_dep);

            const non_os_bits: u16 = 0x0FFF & ~mir_sast.EffectCapabilityMask.LOCKFILE_CAP_BITS;
            try db.setPackageCapPolicy(pkg_dep, .{
                .package_name = "drop-guard-pkg@1.0.0",
                .policy_span = Span.init(fid_dep, 0, 10),
                .allowed_caps = mir_sast.EffectCapabilityMask.fromBits(non_os_bits),
                .is_third_party_dependency = true,
                .enforcement_scope = .surface,
            });

            var cxi_art = try db.computePackageCxiSummary(allocator, pkg_dep, &.{fid_dep});
            defer cxi_art.deinit(allocator);
            try std.testing.expect(cxi_art.caps.surface_caps.ffi);
            try std.testing.expect(cxi_art.caps.surface_caps.unsafe_op);

            var files_map: std.AutoHashMapUnmanaged(PackageId, []const FileId) = .empty;
            defer files_map.deinit(allocator);
            try files_map.put(allocator, pkg_dep, &.{fid_dep});

            var cap_sink = DiagnosticSink.init(allocator);
            defer cap_sink.deinit();
            const cap_reports = try db.verifyWorkspaceCapabilitySandbox(
                allocator,
                &.{pkg_dep},
                &files_map,
                &.{},
                &cap_sink,
            );
            defer allocator.free(cap_reports);
            try std.testing.expect(hasSinkDiagnosticCode(&cap_sink, .e0324_package_capability_violation));
        }
    }

    // [3] `[CRITICAL-03]` & `[HIGH-06]`: `allow_caps = ["comptime_io"]` sets `has_comptime_io_cap == true` with
    //     `mask == 0` (granting zero runtime OS capabilities), while `corex.lock` rejects `max_caps = ["comptime_io"]`
    //     and `checksum = ""` with `E0014`:
    {
        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        const host_cfg = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.host(), false);
        var m_arena = BumpArena.init(allocator);
        defer m_arena.deinit();
        var m_sink = DiagnosticSink.init(allocator);
        defer m_sink.deinit();

        const ct_io_toml =
            "[package]\nname = \"ct-app\"\nversion = \"0.1.0\"\n" ++
            "[dependencies]\nct-gen = { version = \"1.0.0\", allow_caps = [\"comptime_io\"] }\n";
        var parsed_ct = try pkg_manifest.parseManifest(
            allocator,
            &m_arena,
            &interner,
            FileId.fromInt(70),
            ct_io_toml,
            &host_cfg,
            &m_sink,
        );
        defer parsed_ct.doc.deinit(allocator);
        try std.testing.expect(!m_sink.hasErrors());
        try std.testing.expectEqual(@as(usize, 1), parsed_ct.manifest.dependencies.len);
        try std.testing.expect(parsed_ct.manifest.dependencies[0].has_comptime_io_cap);
        try std.testing.expectEqual(@as(u16, 0), parsed_ct.manifest.dependencies[0].allow_caps.?.asBits());

        const zero_hex = "0000000000000000000000000000000000000000000000000000000000000000";
        const bad_lock_cases = [_][]const u8{
            "version = 1\nroot_manifest_blake3 = \"b3:" ++ zero_hex ++ "\"\n\n" ++
                "[[package]]\nname = \"ct-gen\"\nversion = \"1.0.0\"\n" ++
                "source = \"registry+https://index.corexlang.dev\"\n" ++
                "tree_hash = \"b3:" ++ zero_hex ++ "\"\n" ++
                "max_caps = [\"comptime_io\"]\n" ++
                "cxi_blake3 = \"b3:" ++ zero_hex ++ "\"\nfeatures = []\ndependencies = []\n",
            "version = 1\nroot_manifest_blake3 = \"b3:" ++ zero_hex ++ "\"\n\n" ++
                "[[package]]\nname = \"ct-gen\"\nversion = \"1.0.0\"\n" ++
                "source = \"registry+https://index.corexlang.dev\"\n" ++
                "checksum = \"\"\n" ++
                "tree_hash = \"b3:" ++ zero_hex ++ "\"\n" ++
                "max_caps = []\n" ++
                "cxi_blake3 = \"b3:" ++ zero_hex ++ "\"\nfeatures = []\ndependencies = []\n",
        };
        for (bad_lock_cases) |bad_lock| {
            var lock_sink = DiagnosticSink.init(allocator);
            defer lock_sink.deinit();
            const res_lock = try pkg_manifest.parseLockfile(
                allocator,
                &m_arena,
                &interner,
                FileId.fromInt(71),
                bad_lock,
                null,
                &lock_sink,
            );
            try std.testing.expect(res_lock == null);
            try std.testing.expect(hasSinkDiagnosticCode(&lock_sink, .e0014_lockfile_drift_or_corrupt));
        }
    }

    // [4] `[CRITICAL-04]`: Under `[security] default_dep_policy = "zero_trust"`, an untrusted dependency's own
    //     `corex.toml` declaring `leaf-sneak = { version = "1.0.0", allow_caps = ["ffi", "unsafe_op", "net"] }`
    //     does NOT grant capabilities to `leaf-sneak` (`E0324`):
    {
        const leaf_toml = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "packages/leaf-sneak-1.0.0/corex.toml",
            "[package]\nname = \"leaf-sneak\"\nversion = \"1.0.0\"\n",
        );
        defer allocator.free(leaf_toml);
        const leaf_src = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "packages/leaf-sneak-1.0.0/src/root.cx",
            "extern \"C\" fn raw_sock() -> i32;\npub fn open_sock() -> i32 { return unsafe { raw_sock() }; }\n",
        );
        defer allocator.free(leaf_src);

        const mid_toml = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "packages/mid-untrusted-1.0.0/corex.toml",
            "[package]\nname = \"mid-untrusted\"\nversion = \"1.0.0\"\n" ++
                "[dependencies]\nleaf-sneak = { version = \"1.0.0\", allow_caps = [\"ffi\", \"net\", \"unsafe_op\"] }\n",
        );
        defer allocator.free(mid_toml);
        const mid_src = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "packages/mid-untrusted-1.0.0/src/root.cx",
            "use leaf_sneak.open_sock;\npub fn relay() -> i32 { return open_sock(); }\n",
        );
        defer allocator.free(mid_src);

        const zt_ws = try std.fmt.allocPrint(allocator, "{s}/zero_trust_ws", .{temp_dir});
        defer allocator.free(zt_ws);
        const zt_toml = try writeFixtureFile(
            allocator,
            io,
            zt_ws,
            "corex.toml",
            "[package]\nname = \"zt-app\"\nversion = \"0.1.0\"\n" ++
                "[security]\ndefault_dep_policy = \"zero_trust\"\n" ++
                "[dependencies]\nmid-untrusted = \"1.0.0\"\n",
        );
        defer allocator.free(zt_toml);
        const zt_main = try writeFixtureFile(
            allocator,
            io,
            zt_ws,
            "src/main.cx",
            "use mid_untrusted.relay;\nfn main() -> i32 { return relay(); }\n",
        );
        defer allocator.free(zt_main);

        var zt_check = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "check", "--manifest-path", zt_toml },
        );
        defer zt_check.deinit(allocator);
        try std.testing.expect(zt_check.exit_code != 0);
        try std.testing.expect(std.mem.indexOf(u8, zt_check.stderr, "E0324") != null);
    }

    // [5] `[CRITICAL-05]`: Nested C `#include` inside `.host_dir_jailed` & `.cxtree_only` (`/* comment */ #include "../../escape.h"`
    //     or symlinked nested `#include`) is rejected with `E0326`:
    {
        const outside_esc_hdr = try writeFixtureFile(allocator, io, temp_dir, "escape_outside.h", "int pwn(void);\n");
        defer allocator.free(outside_esc_hdr);
        const nested_jail = try std.fmt.allocPrint(allocator, "{s}/nested_c_jail/sub", .{temp_dir});
        defer allocator.free(nested_jail);
        try std.Io.Dir.cwd().createDirPath(io, nested_jail);

        const host_jail_root = try std.fmt.allocPrint(allocator, "{s}/nested_c_jail", .{temp_dir});
        defer allocator.free(host_jail_root);
        const top_hdr = try writeFixtureFile(
            allocator,
            io,
            host_jail_root,
            "top_comment_esc.h",
            "/* sneaky leading block comment */ #include \"../../escape_outside.h\"\nint safe_decl(void);\n",
        );
        defer allocator.free(top_hdr);

        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.embed_io = io;
        db.setPackageGraphMounted(true);

        const pkg_host_j = PackageId.fromInt(2);
        try db.setPackageEmbedJail(pkg_host_j, .{ .host_dir_jailed = host_jail_root });
        const fid_nested_host = FileId.fromInt(80);
        _ = try db.setInput(
            fid_nested_host,
            "const c_api = @c_import(\"top_comment_esc.h\");\npub fn call_it() -> i32 = 0;\n",
            .high,
        );
        db.symbol_table.setFilePackageId(fid_nested_host, pkg_host_j) catch unreachable;
        _ = try db.resolveSignatures(fid_nested_host);
        try std.testing.expect(
            hasSinkDiagnosticCode(db.getSignatureDiagnostics(fid_nested_host).?, .e0326_embed_path_escape),
        );

        if (builtin.os.tag != .windows) {
            const sym_leaf = try std.fmt.allocPrint(allocator, "{s}/sym_target.h", .{host_jail_root});
            defer allocator.free(sym_leaf);
            std.Io.Dir.cwd().symLink(io, "../escape_outside.h", sym_leaf, .{}) catch {};
            const top_sym_hdr = try writeFixtureFile(
                allocator,
                io,
                host_jail_root,
                "top_via_sym.h",
                "#include \"sym_target.h\"\nint wrapper_decl(void);\n",
            );
            defer allocator.free(top_sym_hdr);

            const fid_nested_sym = FileId.fromInt(81);
            _ = try db.setInput(
                fid_nested_sym,
                "const c_sym = @c_import(\"top_via_sym.h\");\npub fn call_sym() -> i32 = 0;\n",
                .high,
            );
            db.symbol_table.setFilePackageId(fid_nested_sym, pkg_host_j) catch unreachable;
            _ = try db.resolveSignatures(fid_nested_sym);
            try std.testing.expect(
                hasSinkDiagnosticCode(db.getSignatureDiagnostics(fid_nested_sym).?, .e0326_embed_path_escape),
            );
        }

        // Also verify `.cxtree_only` nested `/* comment */ #include "../../escape_outside.h"` rejection (`E0326`):
        var vfs_interner = try StringInterner.init(allocator);
        defer vfs_interner.deinit();
        var vfs_map = vfs_sourcemap.VfsSourceMap.init(allocator, &vfs_interner);
        defer vfs_map.deinit(io);
        const pkg_cx_j = PackageId.fromInt(3);
        _ = try vfs_map.setOverlay(
            "/cx/cx-cimport@1.0.0/include/top.h",
            "/* comment */ #include \"../../escape_outside.h\"\nint x(void);\n",
            pkg_cx_j,
        );
        const fid_cx_caller = try vfs_map.setOverlay(
            "/cx/cx-cimport@1.0.0/src/root.cx",
            "const c_top = @c_import(\"include/top.h\");\npub fn f() -> i32 = 0;\n",
            pkg_cx_j,
        );
        db.vfs_source_map = &vfs_map;
        try db.setPackageEmbedJail(pkg_cx_j, .{
            .cxtree_only = .{ .pkg_id = pkg_cx_j, .virtual_root_prefix = "/cx/cx-cimport@1.0.0" },
        });
        _ = try db.setInput(
            fid_cx_caller,
            "const c_top = @c_import(\"include/top.h\");\npub fn f() -> i32 = 0;\n",
            .high,
        );
        db.symbol_table.setFilePackageId(fid_cx_caller, pkg_cx_j) catch unreachable;
        _ = try db.resolveSignatures(fid_cx_caller);
        try std.testing.expect(
            hasSinkDiagnosticCode(db.getSignatureDiagnostics(fid_cx_caller).?, .e0326_embed_path_escape),
        );
    }

    // [6] `[CRITICAL-06]`: Tampering 1 byte of an existing same-size read-only `.cxtree` or `.cxi` in CAS
    //     causes `publishCxTree` / `publishCxiSummary` to reject with `E0015`:
    {
        const cas_home = try std.fmt.allocPrint(allocator, "{s}/crit06_home", .{temp_dir});
        defer allocator.free(cas_home);
        var cache = try pkg_cache.PkgCache.init(allocator, cas_home, 32, 1024 * 1024);
        defer cache.deinit();

        const blob_data = "pub fn v() -> i32 = 1;\n";
        var blob_b3: [32]u8 = undefined;
        std.crypto.hash.Blake3.hash(blob_data, &blob_b3, .{});
        const entries = [_]pkg_cache.CxTreeInputEntry{
            .{ .rel_path = "src/root.cx", .file_mode = 0x01, .file_size = blob_data.len, .file_blake3 = blob_b3 },
        };
        const built_tree = try pkg_cache.buildCxTreeBytes(allocator, "tamper-pkg", &entries, null, Span.init(.none, 0, 0));
        defer allocator.free(built_tree.bytes);
        try cache.publishCxTree(io, built_tree.bytes, built_tree.tree_blake3, null, Span.init(.none, 0, 0));

        const cxi_bytes = try pkg_cxi_seam.serializeCxiSummary(allocator, 0x0002, 0, &.{}, &.{});
        defer allocator.free(cxi_bytes);
        const cxi_digest = pkg_cxi_seam.computeCxiBlake3(0x0002, 0, &.{});
        try cache.publishCxiSummary(io, cxi_bytes, cxi_digest, null, Span.init(.none, 0, 0));

        const flipSingleByteOnDisk = struct {
            /// Flips 1 byte inside an immutable CAS file while keeping its exact byte size and read-only mode.
            fn run(alloc: std.mem.Allocator, io_h: std.Io, path: []const u8) !void {
                if (std.Io.Dir.cwd().openFile(io_h, path, .{ .mode = .read_only })) |ro_f| {
                    const st = try ro_f.stat(io_h);
                    ro_f.setPermissions(io_h, st.permissions.setReadOnly(false)) catch {};
                    ro_f.close(io_h);
                } else |_| {}
                const orig = try std.Io.Dir.cwd().readFileAlloc(io_h, path, alloc, .limited(64 * 1024));
                defer alloc.free(orig);
                orig[orig.len - 1] ^= 0x01;
                std.Io.Dir.cwd().deleteFile(io_h, path) catch {};
                const rw_f = try std.Io.Dir.cwd().createFile(io_h, path, .{ .truncate = true });
                try rw_f.writeStreamingAll(io_h, orig);
                const st_after = try rw_f.stat(io_h);
                rw_f.setPermissions(io_h, st_after.permissions.setReadOnly(true)) catch {};
                rw_f.close(io_h);
            }
        }.run;

        const tree_hex = std.fmt.bytesToHex(built_tree.tree_blake3, .lower);
        const tree_disk_path = try std.fmt.allocPrint(
            allocator,
            "{s}/trees/{s}/{s}.cxtree",
            .{ cache.cas_root, tree_hex[0..2], tree_hex[2..64] },
        );
        defer allocator.free(tree_disk_path);
        try flipSingleByteOnDisk(allocator, io, tree_disk_path);

        var tree_sink = DiagnosticSink.init(allocator);
        defer tree_sink.deinit();
        try std.testing.expectError(
            error.CacheIntegrityMismatch,
            cache.publishCxTree(io, built_tree.bytes, built_tree.tree_blake3, &tree_sink, Span.init(.none, 0, 0)),
        );
        try std.testing.expect(hasSinkDiagnosticCode(&tree_sink, .e0015_cache_integrity_mismatch));

        const cxi_hex = std.fmt.bytesToHex(cxi_digest, .lower);
        const cxi_disk_path = try std.fmt.allocPrint(
            allocator,
            "{s}/cxi/{s}/{s}.cxi",
            .{ cache.cas_root, cxi_hex[0..2], cxi_hex[2..64] },
        );
        defer allocator.free(cxi_disk_path);
        try flipSingleByteOnDisk(allocator, io, cxi_disk_path);

        var cxi_sink = DiagnosticSink.init(allocator);
        defer cxi_sink.deinit();
        try std.testing.expectError(
            error.CacheIntegrityMismatch,
            cache.publishCxiSummary(io, cxi_bytes, cxi_digest, &cxi_sink, Span.init(.none, 0, 0)),
        );
        try std.testing.expect(hasSinkDiagnosticCode(&cxi_sink, .e0015_cache_integrity_mismatch));
    }

    // [7] `[CRITICAL-07]` & `[HIGH-04]` & `[HIGH-05]`: `[security.package.*]` drift (`E0014`), `corex.lock`
    //     `features`/`source` tampering under `--frozen` (`E0014`), and `>= 64 KiB` `.obao` 1-byte tamper
    //     under `--verify-checksums` (`E0015`):
    {
        // Build a `>= 64 KiB` valid `.cx` source file (`68 KiB` via padded doc comment) so CAS emits a `.obao` file:
        var big_cx_buf = try std.ArrayList(u8).initCapacity(allocator, 70 * 1024);
        defer big_cx_buf.deinit(allocator);
        for (0..1100) |_| {
            try big_cx_buf.appendSlice(
                allocator,
                "// Padding comment line ensuring package source blob exceeds 64 KiB Bao threshold.\n",
            );
        }
        try big_cx_buf.appendSlice(allocator, "pub fn big_dep_val() -> i32 { return 55; }\n");
        try std.testing.expect(big_cx_buf.items.len >= pkg_cache.BAO_OUTBOARD_MIN_BYTES);

        var big_blob_b3: [32]u8 = undefined;
        std.crypto.hash.Blake3.hash(big_cx_buf.items, &big_blob_b3, .{});

        const big_src_path = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "packages/big-dep-1.0.0/src/root.cx",
            big_cx_buf.items,
        );
        defer allocator.free(big_src_path);
        const big_idx_ndjson =
            "{\"name\":\"big-dep\",\"vers\":\"1.0.0\",\"deps\":[],\"features\":{\"default\":[],\"extra\":[]}}\n";
        const big_idx_path = try writeFixtureFile(
            allocator,
            io,
            reg_dir,
            "index/bi/g-/big-dep",
            big_idx_ndjson,
        );
        defer allocator.free(big_idx_path);

        const sec_ws = try std.fmt.allocPrint(allocator, "{s}/crit07_ws", .{temp_dir});
        defer allocator.free(sec_ws);
        const orig_sec_toml =
            "[package]\nname = \"sec-app\"\nversion = \"0.1.0\"\n" ++
            "[security.package.big-dep]\nallow_caps = [\"net\"]\n" ++
            "[dependencies]\nbig-dep = \"1.0.0\"\n";
        const sec_toml_path = try writeFixtureFile(allocator, io, sec_ws, "corex.toml", orig_sec_toml);
        defer allocator.free(sec_toml_path);
        const sec_main_path = try writeFixtureFile(
            allocator,
            io,
            sec_ws,
            "src/main.cx",
            "use big_dep.big_dep_val;\nfn main() -> i32 { return big_dep_val() - 55; }\n",
        );
        defer allocator.free(sec_main_path);

        var init_check = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "check", "--manifest-path", sec_toml_path },
        );
        defer init_check.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 0), init_check.exit_code);

        const cached_big_idx_path = try writeFixtureFile(
            allocator,
            io,
            corex_home,
            "cache/blake3/index/default/bi/g-/big-dep",
            big_idx_ndjson,
        );
        defer allocator.free(cached_big_idx_path);

        const sec_lock_path = try std.fmt.allocPrint(allocator, "{s}/corex.lock", .{sec_ws});
        defer allocator.free(sec_lock_path);
        const clean_lock_bytes = try std.Io.Dir.cwd().readFileAlloc(io, sec_lock_path, allocator, .limited(64 * 1024));
        defer allocator.free(clean_lock_bytes);

        // `[CRITICAL-07]`: Editing `[security.package.big-dep]` in `corex.toml` under `--frozen` -> `E0014`:
        const edited_sec_toml =
            "[package]\nname = \"sec-app\"\nversion = \"0.1.0\"\n" ++
            "[security.package.big-dep]\nallow_caps = []\n" ++
            "[dependencies]\nbig-dep = \"1.0.0\"\n";
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = sec_toml_path, .data = edited_sec_toml });
        var sec_drift = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "check", "--frozen", "--manifest-path", sec_toml_path },
        );
        defer sec_drift.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 1), sec_drift.exit_code);
        try std.testing.expect(std.mem.indexOf(u8, sec_drift.stderr, "E0014") != null);
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = sec_toml_path, .data = orig_sec_toml });

        // `[HIGH-04]`: Tampering `features` or `source` inside `corex.lock` under `--frozen` -> `E0014`:
        const tampered_feats_lock = try std.mem.replaceOwned(
            u8,
            allocator,
            clean_lock_bytes,
            "features = [\"default\"]",
            "features = [\"default\", \"extra\"]",
        );
        defer allocator.free(tampered_feats_lock);
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = sec_lock_path, .data = tampered_feats_lock });
        var feat_drift = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "check", "--frozen", "--manifest-path", sec_toml_path },
        );
        defer feat_drift.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 1), feat_drift.exit_code);
        try std.testing.expect(std.mem.indexOf(u8, feat_drift.stderr, "E0014") != null);

        const tampered_src_lock = try std.mem.replaceOwned(
            u8,
            allocator,
            clean_lock_bytes,
            pkg_resolver.DEFAULT_REGISTRY_URI,
            "registry+https://evil.mirror.example/",
        );
        defer allocator.free(tampered_src_lock);
        try std.testing.expect(!std.mem.eql(u8, clean_lock_bytes, tampered_src_lock));
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = sec_lock_path, .data = tampered_src_lock });
        var src_drift = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "check", "--frozen", "--manifest-path", sec_toml_path },
        );
        defer src_drift.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 1), src_drift.exit_code);
        try std.testing.expect(std.mem.indexOf(u8, src_drift.stderr, "E0014") != null);
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = sec_lock_path, .data = clean_lock_bytes });

        // `[HIGH-05]`: Tampering 1 byte in `blobs/<2>/<62>.obao` under `--verify-checksums` -> `E0015`:
        const big_hex = std.fmt.bytesToHex(big_blob_b3, .lower);
        const obao_disk_path = try std.fmt.allocPrint(
            allocator,
            "{s}/cache/blake3/blobs/{s}/{s}.obao",
            .{ corex_home, big_hex[0..2], big_hex[2..64] },
        );
        defer allocator.free(obao_disk_path);
        if (std.Io.Dir.cwd().openFile(io, obao_disk_path, .{ .mode = .read_only })) |ro_ob| {
            const st = try ro_ob.stat(io);
            ro_ob.setPermissions(io, st.permissions.setReadOnly(false)) catch {};
            ro_ob.close(io);
        } else |_| {}
        const orig_obao = try std.Io.Dir.cwd().readFileAlloc(io, obao_disk_path, allocator, .limited(64 * 1024));
        defer allocator.free(orig_obao);
        try std.testing.expect(orig_obao.len >= 72);
        orig_obao[16] ^= 0x40;
        std.Io.Dir.cwd().deleteFile(io, obao_disk_path) catch {};
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = obao_disk_path, .data = orig_obao });

        var obao_check = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "check", "--locked", "--verify-checksums", "--manifest-path", sec_toml_path },
        );
        defer obao_check.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 1), obao_check.exit_code);
        try std.testing.expect(std.mem.indexOf(u8, obao_check.stderr, "E0015") != null);
    }

    // [8] `[CRITICAL-08]`, `[MEDIUM-05]`, `[VERIFIER-02]`, `[VERIFIER-04]`, & `[HIGH-07..09]`:
    //     - Direct `pkg_resolver.evaluateManifestTargetCfg`
    //     - `corex fmt` on `use "github.com/org/pkg@v1.2.0" as pkg_alias;` & `use "registry:serde-json@1.4.2" as serde_json;`
    //     - Truncated/unclosed/oversized inputs to `parseTomlDocument` / `parseManifest` / `parseScriptFrontmatterManifest`
    //     - Incremental `db.setInput` private-body edit preserving `cxi_blake3` (`pub_fn_count == 1`)
    //     - Tier-1 `Bounded-MVS` weak `foo?/feat`, `default`-feature activation on version upgrade, & Tier-2 `-F pkg/feat`:
    {
        // Direct `pkg_resolver.evaluateManifestTargetCfg`:
        const eval_ok_linux = try pkg_resolver.evaluateManifestTargetCfg(
            allocator,
            "target.os == .Linux and target.arch == .X86_64",
            TargetSpec.X86_64_LINUX_GNU,
            Span.init(FileId.fromInt(90), 0, 10),
            null,
        );
        const eval_ok_darwin = try pkg_resolver.evaluateManifestTargetCfg(
            allocator,
            "target.os == .Linux and target.arch == .X86_64",
            TargetSpec.AARCH64_APPLE_DARWIN,
            Span.init(FileId.fromInt(90), 0, 10),
            null,
        );
        try std.testing.expectEqual(@as(?bool, true), eval_ok_linux);
        try std.testing.expectEqual(@as(?bool, false), eval_ok_darwin);

        // `parser` + `corex fmt` shorthand inline `use` (`github.com/…` & `registry:…`):
        const shorthand_cx =
            "use \"github.com/org/pkg@v1.2.0\"   as   pkg_alias;\n" ++
            "use \"registry:serde-json@1.4.2\"   as   serde_json;\n\n" ++
            "pub fn f( val: i32 ) -> i32 {\n    return val + 1;\n}\n";
        const shorthand_path = try writeFixtureFile(allocator, io, temp_dir, "shorthand_inline.cx", shorthand_cx);
        defer allocator.free(shorthand_path);
        var fmt_shorthand = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "fmt", shorthand_path },
        );
        defer fmt_shorthand.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 0), fmt_shorthand.exit_code);
        var fmt_shorthand_check = try runCliCaptured(
            allocator,
            io,
            &env_map,
            &.{ "--color=never", "fmt", "--check", shorthand_path },
        );
        defer fmt_shorthand_check.deinit(allocator);
        try std.testing.expectEqual(@as(u8, 0), fmt_shorthand_check.exit_code);

        // Truncated/unclosed/invalid-UTF8/oversized TOML never panics in `parseTomlDocument` / `parseManifest` / `parseScriptFrontmatterManifest`:
        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        const host_cfg = corex.symbol_resolver.CfgEnv.fromTargetSpec(TargetSpec.host(), false);
        const oversized_slice = try allocator.alloc(u8, pkg_manifest.MAX_TOML_BYTES + 32);
        defer allocator.free(oversized_slice);
        @memset(oversized_slice, 'a');

        const malformed_inputs = [_][]const u8{
            "",
            "[package]\nname = \"unclosed",
            "[package]\n\xff\xfe",
            oversized_slice,
        };
        for (malformed_inputs) |bad_in| {
            var arena = BumpArena.init(allocator);
            defer arena.deinit();
            var sink_a = DiagnosticSink.init(allocator);
            defer sink_a.deinit();
            var doc_a = try pkg_manifest.parseTomlDocument(
                allocator,
                FileId.fromInt(91),
                bad_in,
                bad_in,
                0,
                0,
                false,
                .e0013_invalid_manifest_or_pkg_name,
                &sink_a,
            );
            doc_a.deinit(allocator);

            var sink_b = DiagnosticSink.init(allocator);
            defer sink_b.deinit();
            var pm_b = try pkg_manifest.parseManifest(
                allocator,
                &arena,
                &interner,
                FileId.fromInt(92),
                bad_in,
                &host_cfg,
                &sink_b,
            );
            pm_b.doc.deinit(allocator);

            if (bad_in.len <= 256) {
                const script_wrap = try std.fmt.allocPrint(
                    allocator,
                    "---\n{s}\n---\nfn main() -> i32 {{ return 0; }}\n",
                    .{bad_in},
                );
                defer allocator.free(script_wrap);
                var sink_c = DiagnosticSink.init(allocator);
                defer sink_c.deinit();
                if (try pkg_manifest.extractScriptFrontmatter(&arena, FileId.fromInt(93), script_wrap, &sink_c)) |fm| {
                    var pm_c = try pkg_manifest.parseScriptFrontmatterManifest(
                        allocator,
                        &arena,
                        &interner,
                        FileId.fromInt(93),
                        script_wrap,
                        fm,
                        &host_cfg,
                        &sink_c,
                    );
                    pm_c.doc.deinit(allocator);
                }
            }
        }

        // Incremental `db.setInput` private-body edit on the SAME `CompilerDb` preserves identical `cxi_blake3` & `pub_fn_count`:
        {
            var inc_db = try CompilerDb.init(allocator);
            defer inc_db.deinit();
            inc_db.setPackageGraphMounted(true);
            const pkg_inc = PackageId.fromInt(2);
            const fid_inc = FileId.fromInt(94);
            _ = try inc_db.setInput(
                fid_inc,
                "fn priv(v: i32) -> i32 { return v +% 1; }\npub fn api(v: i32) -> i32 { return priv(v); }\n",
                .high,
            );
            try inc_db.registerPackageRootFile(pkg_inc, fid_inc);
            var inc_cxi_1 = try inc_db.computePackageCxiSummary(allocator, pkg_inc, &.{fid_inc});
            defer inc_cxi_1.deinit(allocator);

            _ = try inc_db.setInput(
                fid_inc,
                "// Added comment\nfn priv(v: i32) -> i32 { return v +% 99; }\npub fn api(v: i32) -> i32 { return priv(v); }\n",
                .high,
            );
            var inc_cxi_2 = try inc_db.computePackageCxiSummary(allocator, pkg_inc, &.{fid_inc});
            defer inc_cxi_2.deinit(allocator);

            const hdr_1 = std.mem.bytesAsValue(pkg_cxi_seam.CxiHeader, inc_cxi_1.bytes[0..64]);
            const hdr_2 = std.mem.bytesAsValue(pkg_cxi_seam.CxiHeader, inc_cxi_2.bytes[0..64]);
            try std.testing.expectEqual(@as(u32, 1), hdr_1.pub_fn_count);
            try std.testing.expectEqual(@as(u32, 1), hdr_2.pub_fn_count);
            try std.testing.expectEqualSlices(u8, &inc_cxi_1.cxi_blake3, &inc_cxi_2.cxi_blake3);
        }

        // Solver `[HIGH-07..09]`: Tier-1 weak `foo?/feat` (inactive optional dep stays unpulled),
        // `default` feature activation after `1.0.0 -> 1.1.0` upgrade, and Tier-2 `-F sub-pkg/extra`:
        {
            const s_opt = try writeFixtureFile(allocator, io, reg_dir, "packages/weak-opt-1.0.0/src/root.cx", "pub fn w() -> i32 = 1;\n");
            defer allocator.free(s_opt);
            const s_upg0 = try writeFixtureFile(allocator, io, reg_dir, "packages/upg-def-1.0.0/src/root.cx", "pub fn u() -> i32 = 1;\n");
            defer allocator.free(s_upg0);
            const s_upg1 = try writeFixtureFile(allocator, io, reg_dir, "packages/upg-def-1.1.0/src/root.cx", "pub fn u() -> i32 = 2;\n");
            defer allocator.free(s_upg1);
            const s_left = try writeFixtureFile(allocator, io, reg_dir, "packages/upg-left-1.0.0/src/root.cx", "pub fn l() -> i32 = 1;\n");
            defer allocator.free(s_left);
            const s_right = try writeFixtureFile(allocator, io, reg_dir, "packages/upg-right-1.0.0/src/root.cx", "pub fn r() -> i32 = 1;\n");
            defer allocator.free(s_right);

            const idx_w = try writeFixtureFile(
                allocator,
                io,
                reg_dir,
                "index/we/ak/weak-opt",
                "{\"name\":\"weak-opt\",\"vers\":\"1.0.0\",\"deps\":[],\"features\":{\"extra\":[]}}\n",
            );
            defer allocator.free(idx_w);
            // `upg-def@1.0.0` has NO `default` feature; `upg-def@1.1.0` introduces `default = ["fast"]`:
            const idx_u = try writeFixtureFile(
                allocator,
                io,
                reg_dir,
                "index/up/g-/upg-def",
                "{\"name\":\"upg-def\",\"vers\":\"1.0.0\",\"deps\":[],\"features\":{\"fast\":[]}}\n" ++
                    "{\"name\":\"upg-def\",\"vers\":\"1.1.0\",\"deps\":[],\"features\":{\"default\":[\"fast\"],\"fast\":[]}}\n",
            );
            defer allocator.free(idx_u);
            const idx_ul = try writeFixtureFile(
                allocator,
                io,
                reg_dir,
                "index/up/g-/upg-left",
                "{\"name\":\"upg-left\",\"vers\":\"1.0.0\",\"deps\":[{\"name\":\"upg-def\",\"req\":\"1.0.0\",\"default_features\":true}]}\n",
            );
            defer allocator.free(idx_ul);
            const idx_ur = try writeFixtureFile(
                allocator,
                io,
                reg_dir,
                "index/up/g-/upg-right",
                "{\"name\":\"upg-right\",\"vers\":\"1.0.0\",\"deps\":[{\"name\":\"upg-def\",\"req\":\"1.1.0\",\"default_features\":false}]}\n",
            );
            defer allocator.free(idx_ur);

            const mvs_ws = try std.fmt.allocPrint(allocator, "{s}/high07_ws", .{temp_dir});
            defer allocator.free(mvs_ws);
            const mvs_toml_txt =
                "[package]\nname = \"mvs-edge-app\"\nversion = \"0.1.0\"\n" ++
                "[features]\ndefault = [\"try_weak\"]\ntry_weak = [\"weak-opt?/extra\"]\n" ++
                "[dependencies]\n" ++
                "weak-opt = { version = \"1.0.0\", optional = true }\n" ++
                "upg-left = \"1.0.0\"\n" ++
                "upg-right = \"1.0.0\"\n";
            const mvs_toml = try writeFixtureFile(allocator, io, mvs_ws, "corex.toml", mvs_toml_txt);
            defer allocator.free(mvs_toml);

            var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &interner);
            defer vfs.deinit(io);
            var sink = DiagnosticSink.init(allocator);
            defer sink.deinit();
            const mvs_fid = try vfs.resolveOrCreatePath(io, mvs_toml, .root);
            var mvs_bundle = try pkg_manifest.loadWorkspaceManifestBundle(
                io,
                allocator,
                &interner,
                mvs_toml,
                mvs_fid,
                &host_cfg,
                &sink,
            );
            defer mvs_bundle.deinit();

            var mvs_graph = (try pkg_resolver.resolveProjectGraph(
                allocator,
                &interner,
                &vfs,
                &mvs_bundle,
                null,
                .{ .io = io, .corex_home_dir = corex_home, .local_registry_dir = reg_dir },
                &sink,
            )).?;
            defer mvs_graph.deinit(allocator);
            try std.testing.expect(mvs_graph.has_used_mvs_fast_path);

            var has_pulled_weak_opt = false;
            var has_upg_fast = false;
            for (mvs_graph.packages) |pkg_n| {
                if (std.mem.eql(u8, pkg_n.canonical_name, "weak-opt")) has_pulled_weak_opt = true;
                if (std.mem.eql(u8, pkg_n.canonical_name, "upg-def")) {
                    try std.testing.expectEqual(@as(u32, 1), pkg_n.version.minor);
                    for (pkg_n.enabled_features) |feat_s| {
                        if (std.mem.eql(u8, feat_s, "fast")) has_upg_fast = true;
                    }
                }
            }
            try std.testing.expect(!has_pulled_weak_opt);
            try std.testing.expect(has_upg_fast);

            // Tier-2 PubGrub CDCL (forced via `[resolution].exclude` on `1.0.0`) with CLI `-F upg-def/fast`:
            const cdcl_ws = try std.fmt.allocPrint(allocator, "{s}/high09_ws", .{temp_dir});
            defer allocator.free(cdcl_ws);
            const cdcl_toml_txt =
                "[package]\nname = \"cdcl-feat-app\"\nversion = \"0.1.0\"\n" ++
                "[dependencies]\nupg-def = { version = \"1.0.0\", default-features = false }\n" ++
                "[resolution]\nexclude = [\"upg-def@=1.0.0\"]\n";
            const cdcl_toml = try writeFixtureFile(allocator, io, cdcl_ws, "corex.toml", cdcl_toml_txt);
            defer allocator.free(cdcl_toml);

            const cdcl_fid = try vfs.resolveOrCreatePath(io, cdcl_toml, .root);
            var cdcl_bundle = try pkg_manifest.loadWorkspaceManifestBundle(
                io,
                allocator,
                &interner,
                cdcl_toml,
                cdcl_fid,
                &host_cfg,
                &sink,
            );
            defer cdcl_bundle.deinit();

            var cdcl_graph = (try pkg_resolver.resolveProjectGraph(
                allocator,
                &interner,
                &vfs,
                &cdcl_bundle,
                null,
                .{
                    .io = io,
                    .corex_home_dir = corex_home,
                    .local_registry_dir = reg_dir,
                    .cli_features = &.{"upg-def/fast"},
                },
                &sink,
            )).?;
            defer cdcl_graph.deinit(allocator);
            try std.testing.expect(!cdcl_graph.has_used_mvs_fast_path);

            var has_cdcl_fast = false;
            for (cdcl_graph.packages) |pkg_n| {
                if (std.mem.eql(u8, pkg_n.canonical_name, "upg-def")) {
                    try std.testing.expectEqual(@as(u32, 1), pkg_n.version.minor);
                    for (pkg_n.enabled_features) |feat_s| {
                        if (std.mem.eql(u8, feat_s, "fast")) has_cdcl_fast = true;
                    }
                }
            }
            try std.testing.expect(has_cdcl_fast);
        }
    }
}
