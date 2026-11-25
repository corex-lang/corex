//! Phase 11.1c (`DR-25` §2.2 & §4.4) Exhaustive 44-Rule Matrix, Auto-Fix Convergence & Cross-Platform Suite
//!
//! Exercises every built-in lint rule (`RuleId` `0..43`, `ALL_RULES_MASK = (1 << 44) - 1`) across negative
//! triggers (`Severity.warning` only, `[W0xxx/slug]` rendered headers), adjacent false-positive guards (`0`
//! warnings), and `<= 2`-pass `applyCheckFixesOnDb` convergence (`26` `Auto` + `7` `Unsafe` rules).
//!
//! Also verifies cascading `W0002` stale-`@expect` cleanup, `CRLF` (`\r\n`) four-scope suppression and
//! docstring hoisting, cross-platform `CompiledGlob64` (`\` vs. `/`), and multi-target `W0413` word-width gates.

const std = @import("std");
const corex = @import("corex");

const BumpArena = corex.BumpArena;
const CompilerDb = corex.CompilerDb;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticRenderer = corex.DiagnosticRenderer;
const DiagnosticSink = corex.DiagnosticSink;
const FileId = corex.FileId;
const PackageId = corex.PackageId;
const RuleId = corex.RuleId;
const RuleMask64 = corex.RuleMask64;
const Severity = corex.Severity;
const Span = corex.Span;
const StringInterner = corex.StringInterner;
const StyleConfig = corex.StyleConfig;
const TargetSpec = corex.TargetSpec;
const VfsSourceMap = corex.VfsSourceMap;
const check_audit = corex.check_audit;
const codegen_abi = corex.codegen_abi;
const diagnostic = corex.diagnostic;
const mir_sast = corex.mir_sast;
const pkg_manifest = corex.pkg_manifest;
const type_system = corex.type_system;

// ---------------------------------------- TYPES ----------------------------------------

/// Pipeline harness mode used to evaluate a `RuleVerificationCase`.
const HarnessMode = enum(u8) {
    /// Standard single-file `CompilerDb.projectFileDiagnostics` + `applyCheckFixesOnDb` pipeline.
    single_file_db = 0,
    /// Multi-package workspace capability sandbox check (`W0330` `ambient-dead-capability`).
    workspace_dep_caps = 1,
    /// Deterministic simulation SAST check (`W0332` `nondeterministic-sim-source`, `is_sim_mode = true`).
    sim_mode_sast = 2,
};

/// Complete verification specification for a single `DR-25` built-in lint rule (`RuleId` `0..43`).
const RuleVerificationCase = struct {
    /// Dense `0..43` rule identifier under test.
    rule_id: RuleId,
    /// Expected `DiagnosticCode` (`W0xxx`).
    expected_code: DiagnosticCode,
    /// Expected canonical `kebab-case` rule slug.
    expected_slug: []const u8,
    /// Expected default fix applicability (`.machine_applicable`, `.maybe_incorrect`, or `.unspecified`).
    expected_applicability: diagnostic.FixApplicability,
    /// Pipeline execution mode for this rule.
    mode: HarnessMode = .single_file_db,
    /// Invalid or non-idiomatic `.cx` source expected to trigger `expected_code` with `0` errors.
    negative_src: []const u8,
    /// Adjacent valid `.cx` source expected to emit `0` errors and `0` warnings.
    positive_src: []const u8,
};

// --------------------------------------- CONSTS ----------------------------------------

// -------------------- 44-Rule Matrix Specs --------------------

/// Exhaustive 44-entry table covering `RuleId` `0..43` in exact dense ordinal order.
const ALL_44_RULE_CASES = [RuleId.COUNT]RuleVerificationCase{
    // [0] W0002 / unused-suppression (Auto):
    .{
        .rule_id = .unused_suppression,
        .expected_code = .w0002_unused_suppression,
        .expected_slug = "unused-suppression",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\@expect(W0123, reason: "stale hex expectation")
        \\pub fn mask_val() -> u32 {
        \\    0xDEAD_BEEF_u32
        \\}
        ++ "\n",
        .positive_src =
        \\@expect(W0123, reason: "legacy wire constant")
        \\pub fn mask_val() -> u32 {
        \\    0xdead_beef_u32
        \\}
        ++ "\n",
    },
    // [1] W0003 / missing-suppression-reason (Diag):
    .{
        .rule_id = .missing_suppression_reason,
        .expected_code = .w0003_missing_suppression_reason,
        .expected_slug = "missing-suppression-reason",
        .expected_applicability = .unspecified,
        .negative_src =
        \\@expect(W0123)
        \\pub fn mask_val() -> u32 {
        \\    0xdead_beef_u32
        \\}
        ++ "\n",
        .positive_src =
        \\@expect(W0123, reason: "documented hex fixture")
        \\pub fn mask_val() -> u32 {
        \\    0xdead_beef_u32
        \\}
        ++ "\n",
    },
    // [2] W0004 / prefer-expect-over-allow (Auto):
    .{
        .rule_id = .prefer_expect_over_allow,
        .expected_code = .w0004_prefer_expect_over_allow,
        .expected_slug = "prefer-expect-over-allow",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\@allow(W0203, reason: "short math parameter")
        \\pub fn step_coord(c: i32) -> i32 {
        \\    c + 1
        \\}
        ++ "\n",
        .positive_src =
        \\// corex check: file-allow(W0203) -- module math conventions
        \\
        \\@cfg(target.ptr_width == 64)
        \\@allow(W0123, reason: "target-gated mask")
        \\pub fn step_coord(c: u32) -> u32 {
        \\    c ^ 0xdead_beef_u32
        \\}
        ++ "\n",
    },
    // [3] W0101 / redundant-escape-sequence (Auto):
    .{
        .rule_id = .redundant_escape_sequence,
        .expected_code = .w0101_redundant_escape_sequence,
        .expected_slug = "redundant-escape-sequence",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn delimiter_text() -> str {
        \\    "key\:val"
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn delimiter_text() -> str {
        \\    "line1\nline2\t\"quoted\"\\\x20\u{0041}"
        \\}
        ++ "\n",
    },
    // [4] W0102 / unicode-trojan-control (Auto):
    .{
        .rule_id = .unicode_trojan_control,
        .expected_code = .w0102_unicode_trojan_control,
        .expected_slug = "unicode-trojan-control",
        .expected_applicability = .machine_applicable,
        .negative_src = "pub fn bidi_sample() -> str {\n    \"ab\u{202E}cd\"\n}\n",
        .positive_src = "\xEF\xBB\xBFpub fn clean_bom() -> str {\n    \"plain_ascii\"\n}\n",
    },
    // [5] W0103 / confusable-ident (Diag):
    .{
        .rule_id = .confusable_ident,
        .expected_code = .w0103_confusable_ident,
        .expected_slug = "confusable-ident",
        .expected_applicability = .unspecified,
        .negative_src = "pub fn verify_ident() -> i32 {\n    let p\u{0430}ypal = 7;\n    p\u{0430}ypal + 1\n}\n",
        .positive_src = "pub fn step_physics(Δt: f64, μs: f64) -> f64 {\n    Δt + μs\n}\n",
    },
    // [6] W0104 / ambiguous-unicode-text (Unsafe):
    .{
        .rule_id = .ambiguous_unicode_text,
        .expected_code = .w0104_ambiguous_unicode_text,
        .expected_slug = "ambiguous-unicode-text",
        .expected_applicability = .maybe_incorrect,
        .negative_src = "// Header \u{2014} summary\npub fn cache_tag() -> str {\n    \"\u{0421}ache\"\n}\n",
        .positive_src = "// Привет мир – чистый комментарий…\n" ++
            "pub fn banner_text() -> str {\n    \"Привет – ok…\"\n}\n",
    },
    // [7] W0119 / useless-format-string (Auto):
    .{
        .rule_id = .useless_format_string,
        .expected_code = .w0119_useless_format_string,
        .expected_slug = "useless-format-string",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn static_banner() -> str {
        \\    f"no_interpolation_holes"
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn dynamic_banner(port: u16) -> str {
        \\    _ = f"port={port}";
        \\    "ok"
        \\}
        ++ "\n",
    },
    // [8] W0120 / uninterpolated-fmt-braces (Unsafe):
    .{
        .rule_id = .uninterpolated_fmt_braces,
        .expected_code = .w0120_uninterpolated_fmt_placeholder,
        .expected_slug = "uninterpolated-fmt-braces",
        .expected_applicability = .maybe_incorrect,
        .negative_src =
        \\fn sink_fmt(args: FmtArgs) {
        \\    _ = args;
        \\}
        \\
        \\pub fn report_count(count: i32) -> i32 {
        \\    sink_fmt("count={count}");
        \\    count + 1
        \\}
        ++ "\n",
        .positive_src =
        \\fn keep_raw(text: str) -> str {
        \\    text
        \\}
        \\
        \\pub fn literal_template(count: i32) -> str {
        \\    _ = count;
        \\    keep_raw("count={count}")
        \\}
        ++ "\n",
    },
    // [9] W0121 / needless-raw-string-hashes (Auto):
    .{
        .rule_id = .needless_raw_string_hashes,
        .expected_code = .w0121_needless_raw_string_hashes,
        .expected_slug = "needless-raw-string-hashes",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn plain_raw() -> str {
        \\    r#"alpha_beta"#
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn regex_raw() -> str {
        \\    r"a\b"
        \\}
        ++ "\n",
    },
    // [10] W0122 / ungrouped-numeric-literal (Auto):
    .{
        .rule_id = .ungrouped_numeric_literal,
        .expected_code = .w0122_ungrouped_numeric_literal,
        .expected_slug = "ungrouped-numeric-literal",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn million_val() -> u32 {
        \\    1000000_u32
        \\}
        ++ "\n",
        .positive_src =
        \\pub const PI_VAL: f64 = 3.1415926535_f64;
        \\pub const HTTP_PORT: u32 = 8080;
        \\
        \\pub fn port_sum() -> u32 {
        \\    _ = PI_VAL;
        \\    HTTP_PORT + 0xFFFF_u32
        \\}
        ++ "\n",
    },
    // [11] W0123 / non-upper-hex-literal (Auto):
    .{
        .rule_id = .non_upper_hex_literal,
        .expected_code = .w0123_non_upper_hex_literal,
        .expected_slug = "non-upper-hex-literal",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn magic_word() -> u32 {
        \\    0xdead_beef_u32
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn magic_word() -> u32 {
        \\    0xDEAD_BEEF_u32
        \\}
        ++ "\n",
    },
    // [12] W0201 / non-canonical-case (Auto):
    .{
        .rule_id = .non_canonical_case,
        .expected_code = .w0201_non_canonical_identifier_case,
        .expected_slug = "non-canonical-case",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn computeTotal(userId: i32) -> i32 {
        \\    userId + 1
        \\}
        ++ "\n",
        .positive_src =
        \\extern "C" fn ForeignInit(handle: *mut opaque);
        \\
        \\pub fn compute_total(user_id: i32, handle: *mut opaque) -> i32 {
        \\    unsafe { ForeignInit(handle); }
        \\    user_id + 1
        \\}
        ++ "\n",
    },
    // [13] W0202 / non-idiomatic-syntax (Auto):
    .{
        .rule_id = .non_idiomatic_syntax,
        .expected_code = .w0202_non_idiomatic_construct,
        .expected_slug = "non-idiomatic-syntax",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub struct Point {
        \\    pub x: i32,
        \\    pub y: i32,
        \\}
        \\
        \\pub fn build_point(x: i32, y: i32) -> Point {
        \\    ;
        \\    Point { x: x, y }
        \\}
        ++ "\n",
        .positive_src =
        \\pub type HookFn = fn() -> unit;
        \\
        \\pub struct Point {
        \\    pub x: i32,
        \\    pub y: i32,
        \\}
        \\
        \\pub fn build_point(x: i32, y: i32) -> Point {
        \\    Point { x, y }
        \\}
        ++ "\n",
    },
    // [14] W0203 / single-char-ident (Diag):
    .{
        .rule_id = .single_char_ident,
        .expected_code = .w0203_single_char_ident,
        .expected_slug = "single-char-ident",
        .expected_applicability = .unspecified,
        .negative_src =
        \\pub fn bad_local(seed: i32) -> i32 {
        \\    let c = seed + 1;
        \\    c * 2
        \\}
        ++ "\n",
        .positive_src =
        \\pub struct Entry {
        \\    pub id: i32,
        \\}
        \\
        \\pub fn closure_and_coords(entry: Entry, x: i32, n: i32) -> i32 {
        \\    let proj = |v: Entry| v.id;
        \\    proj(entry) + x + n
        \\}
        ++ "\n",
    },
    // [15] W0204 / shadowed-binding (Diag):
    .{
        .rule_id = .shadowed_binding,
        .expected_code = .w0204_shadowed_binding,
        .expected_slug = "shadowed-binding",
        .expected_applicability = .unspecified,
        .negative_src =
        \\pub fn shadow_live(flag: bool) -> i32 {
        \\    let total = 10;
        \\    if flag {
        \\        let total = 20;
        \\        _ = total;
        \\    }
        \\    total
        \\}
        ++ "\n",
        .positive_src =
        \\@derive(Copy, Clone)
        \\pub enum ParseErr {
        \\    Invalid,
        \\}
        \\
        \\fn parse(raw_x: str) -> i32!ParseErr {
        \\    if raw_x.len() > 0 => .Ok(1) else .Err(.Invalid)
        \\}
        \\
        \\pub fn rebind_dead(x: str) -> i32!ParseErr {
        \\    let x = parse(x)?;
        \\    .Ok(x + 1)
        \\}
        ++ "\n",
    },
    // [16] W0205 / bool-predicate-naming (Diag):
    .{
        .rule_id = .bool_predicate_naming,
        .expected_code = .w0205_bool_predicate_naming,
        .expected_slug = "bool-predicate-naming",
        .expected_applicability = .unspecified,
        .negative_src =
        \\pub fn validate_header(len_val: usize) -> bool {
        \\    len_val > 0
        \\}
        ++ "\n",
        .positive_src =
        \\pub struct Config {
        \\    pub readonly: bool,
        \\}
        \\
        \\pub fn is_valid_header(cfg: Config) -> bool {
        \\    cfg.readonly
        \\}
        ++ "\n",
    },
    // [17] W0206 / getter-prefix-noise (Unsafe):
    .{
        .rule_id = .getter_prefix_noise,
        .expected_code = .w0206_getter_prefix_noise,
        .expected_slug = "getter-prefix-noise",
        .expected_applicability = .maybe_incorrect,
        .negative_src =
        \\pub struct Header {
        \\    pub length_val: u32,
        \\}
        \\
        \\impl Header {
        \\    pub fn get_length(&self) -> u32 {
        \\        self.length_val
        \\    }
        \\}
        ++ "\n",
        .positive_src =
        \\pub struct Header {
        \\    pub length_val: u32,
        \\}
        \\
        \\impl Header {
        \\    pub fn length(&self) -> u32 {
        \\        self.length_val
        \\    }
        \\
        \\    pub fn get(&self, idx: usize) -> u32? {
        \\        if idx == 0 => .Some(self.length_val) else .None
        \\    }
        \\}
        ++ "\n",
    },
    // [18] W0207 / conversion-prefix-mismatch (Unsafe):
    .{
        .rule_id = .conversion_prefix_mismatch,
        .expected_code = .w0207_conversion_prefix_mismatch,
        .expected_slug = "conversion-prefix-mismatch",
        .expected_applicability = .maybe_incorrect,
        .negative_src =
        \\@derive(Copy, Clone)
        \\pub struct SliceMeta {
        \\    pub count: u32,
        \\}
        \\
        \\impl SliceMeta {
        \\    pub fn to_meta_ref(&self) -> &SliceMeta {
        \\        self
        \\    }
        \\}
        ++ "\n",
        .positive_src =
        \\@derive(Copy, Clone)
        \\pub struct FloatScalar {
        \\    pub raw: f32,
        \\}
        \\
        \\impl FloatScalar {
        \\    pub fn to_bits(self) -> u32 {
        \\        if self.raw > 0.0_f32 => 1_u32 else 0_u32
        \\    }
        \\
        \\    pub fn as_raw(&self) -> &f32 {
        \\        &self.raw
        \\    }
        \\}
        ++ "\n",
    },
    // [19] W0208 / redundant-literal-type (Auto):
    .{
        .rule_id = .redundant_literal_type,
        .expected_code = .w0208_redundant_literal_type,
        .expected_slug = "redundant-literal-type",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn add_explicit(seed: u32) -> u32 {
        \\    let offset: u32 = 27_u32;
        \\    seed + offset
        \\}
        ++ "\n",
        .positive_src =
        \\pub const BASE_LIMIT: u32 = 27;
        \\
        \\pub fn keep_unsuffixed() -> u32 {
        \\    let x: u32 = 27;
        \\    x + BASE_LIMIT
        \\}
        ++ "\n",
    },
    // [20] W0209 / needless-trailing-return (Auto):
    .{
        .rule_id = .needless_trailing_return,
        .expected_code = .w0209_needless_trailing_return,
        .expected_slug = "needless-trailing-return",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn inc_val(val: i32) -> i32 {
        \\    return val + 1;
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn clamp_non_neg(val: i32) -> i32 {
        \\    if val < 0 {
        \\        return 0;
        \\    }
        \\    val
        \\}
        ++ "\n",
    },
    // [21] W0210 / manual-assign-or-swap (Auto):
    .{
        .rule_id = .manual_assign_or_swap,
        .expected_code = .w0210_manual_assign_or_swap,
        .expected_slug = "manual-assign-or-swap",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn swap_pair(delta: i32) -> i32 {
        \\    var lhs = 1;
        \\    var rhs = 2;
        \\    let tmp = lhs;
        \\    lhs = rhs;
        \\    rhs = tmp;
        \\    lhs = lhs + delta;
        \\    lhs + rhs
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn swap_slice_elems(arr: &mut [i32], i: usize, j: usize) {
        \\    if i < arr.len() and j < arr.len() {
        \\        let tmp_elem = arr[i];
        \\        arr[i] = arr[j];
        \\        arr[j] = tmp_elem;
        \\    }
        \\}
        ++ "\n",
    },
    // [22] W0308 / unused-region-alloc (Diag):
    .{
        .rule_id = .unused_region_alloc,
        .expected_code = .w0308_unused_region_allocation,
        .expected_slug = "unused-region-alloc",
        .expected_applicability = .unspecified,
        .negative_src =
        \\pub struct BumpArena {
        \\    pub cursor: usize,
        \\}
        \\
        \\impl BumpArena {
        \\    pub fn reset(&mut self) {
        \\        self.cursor = 0;
        \\    }
        \\
        \\    pub fn deinit(own self) {
        \\        let BumpArena { cursor: _cursor } = self;
        \\    }
        \\}
        \\
        \\pub fn idle_region() {
        \\    var region = BumpArena { cursor: 0 };
        \\    region.reset();
        \\    region.deinit();
        \\}
        ++ "\n",
        .positive_src =
        \\pub struct BumpArena {
        \\    pub cursor: usize,
        \\}
        \\
        \\impl BumpArena {
        \\    pub fn alloc_bytes(&mut self, count: usize) -> usize {
        \\        self.cursor = self.cursor +% count;
        \\        self.cursor
        \\    }
        \\
        \\    pub fn deinit(own self) {
        \\        let BumpArena { cursor: _cursor } = self;
        \\    }
        \\}
        \\
        \\pub fn active_region() -> usize {
        \\    var region = BumpArena { cursor: 0 };
        \\    let out_bytes = region.alloc_bytes(64);
        \\    region.deinit();
        \\    out_bytes
        \\}
        ++ "\n",
    },
    // [23] W0329 / vacated-projection-abort (Diag):
    .{
        .rule_id = .vacated_projection_abort,
        .expected_code = .w0329_vacated_projection_panic_abort,
        .expected_slug = "vacated-projection-abort",
        .expected_applicability = .unspecified,
        .negative_src =
        \\pub struct Vec[T] {
        \\    pub len_val: usize,
        \\}
        \\
        \\pub struct NonCopySlot {
        \\    pub buf: Vec[i64],
        \\}
        \\
        \\pub struct SlotPair {
        \\    pub items: [NonCopySlot; 2],
        \\}
        \\
        \\impl SlotPair {
        \\    pub subscript(idx: usize) -> NonCopySlot {
        \\        inout {
        \\            yield &mut self.items[idx];
        \\        }
        \\    }
        \\}
        \\
        \\pub fn overwrite_vacated(lookup_idx: usize) -> usize {
        \\    var slots = SlotPair {
        \\        items: [
        \\            NonCopySlot { buf: Vec { len_val: 1 } },
        \\            NonCopySlot { buf: Vec { len_val: 2 } },
        \\        ],
        \\    };
        \\    let table: [usize; 2] = [10, 20];
        \\    slots[0] = NonCopySlot { buf: Vec { len_val: table[lookup_idx] } };
        \\    slots.items[0].buf.len_val
        \\}
        ++ "\n",
        .positive_src =
        \\pub struct Vec[T] {
        \\    pub len_val: usize,
        \\}
        \\
        \\pub struct NonCopySlot {
        \\    pub buf: Vec[i64],
        \\}
        \\
        \\pub struct SlotPair {
        \\    pub items: [NonCopySlot; 2],
        \\}
        \\
        \\impl SlotPair {
        \\    pub subscript(idx: usize) -> NonCopySlot {
        \\        inout {
        \\            yield &mut self.items[idx];
        \\        }
        \\    }
        \\}
        \\
        \\pub fn overwrite_total_safe() -> usize {
        \\    var slots = SlotPair {
        \\        items: [
        \\            NonCopySlot { buf: Vec { len_val: 1 } },
        \\            NonCopySlot { buf: Vec { len_val: 2 } },
        \\        ],
        \\    };
        \\    slots[0] = NonCopySlot { buf: Vec { len_val: 99 } };
        \\    slots.items[0].buf.len_val
        \\}
        ++ "\n",
    },
    // [24] W0330 / ambient-dead-capability (Diag, workspace third-party dependency):
    .{
        .rule_id = .ambient_dead_capability,
        .expected_code = .w0330_ambient_dead_capability_in_dep,
        .expected_slug = "ambient-dead-capability",
        .expected_applicability = .unspecified,
        .mode = .workspace_dep_caps,
        .negative_src =
        \\extern "C" fn raw_backdoor_ffi(code: i32) -> i32;
        \\
        \\pub fn pure_sum(lhs: i32, rhs: i32) -> i32 {
        \\    lhs + rhs
        \\}
        \\
        \\fn unreachable_ffi_helper(code: i32) -> i32 {
        \\    unsafe { raw_backdoor_ffi(code) }
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn pure_sum(lhs: i32, rhs: i32) -> i32 {
        \\    lhs + rhs
        \\}
        ++ "\n",
    },
    // [25] W0332 / nondeterministic-sim-source (Diag, `--sim` mode):
    .{
        .rule_id = .nondeterministic_sim_source,
        .expected_code = .w0332_nondeterministic_sim_source,
        .expected_slug = "nondeterministic-sim-source",
        .expected_applicability = .unspecified,
        .mode = .sim_mode_sast,
        .negative_src =
        \\extern "C" fn clock_gettime(clk_id: i32, tp: *mut u8) -> i32;
        \\
        \\pub fn read_host_clock(tp: *mut u8) -> i32 {
        \\    unsafe { clock_gettime(0, tp) }
        \\}
        \\
        \\test "sim_clock_bypass" {
        \\    let null_tp = 0 as *mut u8;
        \\    _ = read_host_clock(null_tp);
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn step_virtual_rng(seed: u64) -> u64 {
        \\    seed ^ 0x9E37_79B9_7F4A_7C15_u64
        \\}
        \\
        \\test "sim_deterministic_rng" {
        \\    _ = step_virtual_rng(7_u64);
        \\}
        ++ "\n",
    },
    // [26] W0333 / redundant-private-contract (Auto):
    .{
        .rule_id = .redundant_private_contract,
        .expected_code = .w0333_redundant_private_contract,
        .expected_slug = "redundant-private-contract",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\@no_alloc
        \\fn helper_step(val: i32) -> i32 {
        \\    val + 1
        \\}
        \\
        \\pub fn run_step(val: i32) -> i32 {
        \\    helper_step(val)
        \\}
        ++ "\n",
        .positive_src =
        \\@no_alloc
        \\pub fn exported_step(val: i32) -> i32 {
        \\    val + 1
        \\}
        ++ "\n",
    },
    // [27] W0334 / redundant-move-clone (Auto):
    .{
        .rule_id = .redundant_move_clone,
        .expected_code = .w0334_redundant_move_clone,
        .expected_slug = "redundant-move-clone",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub struct OwnedPacket {
        \\    pub tag: i32,
        \\}
        \\
        \\impl Drop for OwnedPacket {
        \\    fn drop(&mut self) {
        \\        self.tag = 0;
        \\    }
        \\}
        \\
        \\impl OwnedPacket {
        \\    pub fn clone(&self) -> OwnedPacket {
        \\        OwnedPacket { tag: self.tag }
        \\    }
        \\}
        \\
        \\fn consume_packet(pkt: own OwnedPacket) -> i32 {
        \\    pkt.tag
        \\}
        \\
        \\pub fn send_once() -> i32 {
        \\    let pkt = OwnedPacket { tag: 9 };
        \\    consume_packet(pkt.clone())
        \\}
        ++ "\n",
        .positive_src =
        \\pub struct OwnedPacket {
        \\    pub tag: i32,
        \\}
        \\
        \\impl Drop for OwnedPacket {
        \\    fn drop(&mut self) {
        \\        self.tag = 0;
        \\    }
        \\}
        \\
        \\impl OwnedPacket {
        \\    pub fn clone(&self) -> OwnedPacket {
        \\        OwnedPacket { tag: self.tag }
        \\    }
        \\}
        \\
        \\fn consume_packet(pkt: own OwnedPacket) -> i32 {
        \\    pkt.tag
        \\}
        \\
        \\pub fn clone_from_borrow(borrowed: &OwnedPacket) -> i32 {
        \\    consume_packet(borrowed.clone())
        \\}
        ++ "\n",
    },
    // [28] W0335 / string-concat-in-loop (Diag):
    .{
        .rule_id = .string_concat_in_loop,
        .expected_code = .w0335_string_concat_in_loop,
        .expected_slug = "string-concat-in-loop",
        .expected_applicability = .unspecified,
        .negative_src =
        \\pub struct String {
        \\    pub len_val: usize,
        \\}
        \\
        \\impl String {
        \\    pub fn new() -> String {
        \\        String { len_val: 0 }
        \\    }
        \\
        \\    pub fn push_str(&mut self, chunk: str) {
        \\        self.len_val += chunk.len();
        \\    }
        \\}
        \\
        \\pub fn join_unreserved(chunks: &[str]) -> usize {
        \\    var out = String.new();
        \\    for piece in chunks {
        \\        out.push_str(piece);
        \\    }
        \\    out.len_val
        \\}
        ++ "\n",
        .positive_src =
        \\pub struct String {
        \\    pub len_val: usize,
        \\}
        \\
        \\impl String {
        \\    pub fn with_capacity(cap: usize) -> String {
        \\        String { len_val: cap }
        \\    }
        \\
        \\    pub fn push_str(&mut self, chunk: str) {
        \\        self.len_val += chunk.len();
        \\    }
        \\}
        \\
        \\pub fn join_preallocated(chunks: &[str]) -> usize {
        \\    var out = String.with_capacity(128);
        \\    for piece in chunks {
        \\        out.push_str(piece);
        \\    }
        \\    out.len_val
        \\}
        ++ "\n",
    },
    // [29] W0401 / unreachable-pattern (Unsafe):
    .{
        .rule_id = .unreachable_pattern,
        .expected_code = .w0401_unreachable_pattern_arm,
        .expected_slug = "unreachable-pattern",
        .expected_applicability = .maybe_incorrect,
        .negative_src =
        \\pub enum Level {
        \\    Low,
        \\    Mid,
        \\    High,
        \\}
        \\
        \\pub fn score_level(lvl: Level) -> i32 {
        \\    match lvl {
        \\        .Low => 1,
        \\        .Low => 2,
        \\        .Mid => 3,
        \\        .High => 4,
        \\    }
        \\}
        ++ "\n",
        .positive_src =
        \\pub enum Level {
        \\    Low,
        \\    Mid,
        \\    High,
        \\}
        \\
        \\pub fn score_level(lvl: Level) -> i32 {
        \\    match lvl {
        \\        .Low => 1,
        \\        .Mid => 3,
        \\        .High => 4,
        \\    }
        \\}
        ++ "\n",
    },
    // [30] W0402 / unused-binding (Unsafe):
    .{
        .rule_id = .unused_binding,
        .expected_code = .w0402_unused_binding,
        .expected_slug = "unused-binding",
        .expected_applicability = .maybe_incorrect,
        .negative_src =
        \\pub fn pick_first(first_val: i32, extra_val: i32) -> i32 {
        \\    first_val + 1
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn pick_first(first_val: i32, _extra_val: i32) -> i32 {
        \\    first_val + 1
        \\}
        ++ "\n",
    },
    // [31] W0403 / deprecated-use (Auto):
    .{
        .rule_id = .deprecated_use,
        .expected_code = .w0403_deprecated_symbol,
        .expected_slug = "deprecated-use",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\@deprecated(reason: "use modern_calc", upgrade: "modern_calc($0)")
        \\pub fn legacy_calc(val: i32) -> i32 {
        \\    modern_calc(val)
        \\}
        \\
        \\pub fn modern_calc(val: i32) -> i32 {
        \\    val + 2
        \\}
        \\
        \\pub fn execute_calc(val: i32) -> i32 {
        \\    legacy_calc(val)
        \\}
        ++ "\n",
        .positive_src =
        \\@deprecated(reason: "use modern_calc", upgrade: "modern_calc($0)")
        \\pub fn legacy_calc(val: i32) -> i32 {
        \\    modern_calc(val)
        \\}
        \\
        \\pub fn modern_calc(val: i32) -> i32 {
        \\    val + 2
        \\}
        \\
        \\pub fn execute_calc(val: i32) -> i32 {
        \\    modern_calc(val)
        \\}
        ++ "\n",
    },
    // [32] W0404 / unused-import (Auto):
    .{
        .rule_id = .unused_import,
        .expected_code = .w0404_unused_import,
        .expected_slug = "unused-import",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub mod math_ops {
        \\    pub fn double_val(val: i32) -> i32 {
        \\        val * 2
        \\    }
        \\
        \\    pub fn triple_val(val: i32) -> i32 {
        \\        val * 3
        \\    }
        \\}
        \\
        \\use math_ops.{double_val, triple_val};
        \\
        \\pub fn compute_val(val: i32) -> i32 {
        \\    double_val(val)
        \\}
        ++ "\n",
        .positive_src =
        \\pub mod math_ops {
        \\    pub fn double_val(val: i32) -> i32 {
        \\        val * 2
        \\    }
        \\}
        \\
        \\use math_ops.double_val;
        \\
        \\pub fn compute_val(val: i32) -> i32 {
        \\    double_val(val)
        \\}
        ++ "\n",
    },
    // [33] W0405 / unused-mut-binding (Auto):
    .{
        .rule_id = .unused_mut_binding,
        .expected_code = .w0405_unused_mut_binding,
        .expected_slug = "unused-mut-binding",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn sum_immutable(seed: i32) -> i32 {
        \\    var factor = seed + 3;
        \\    factor * 2
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn sum_mutated(seed: i32) -> i32 {
        \\    var factor = seed;
        \\    factor += 3;
        \\    factor
        \\}
        ++ "\n",
    },
    // [34] W0406 / unused-pkg-visibility (Auto):
    .{
        .rule_id = .unused_pkg_visibility,
        .expected_code = .w0406_unused_pkg_visibility,
        .expected_slug = "unused-pkg-visibility",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub(pkg) fn local_helper(val: i32) -> i32 {
        \\    val + 4
        \\}
        \\
        \\pub fn public_entry(val: i32) -> i32 {
        \\    local_helper(val)
        \\}
        ++ "\n",
        .positive_src =
        \\fn local_helper(val: i32) -> i32 {
        \\    val + 4
        \\}
        \\
        \\pub fn public_entry(val: i32) -> i32 {
        \\    local_helper(val)
        \\}
        ++ "\n",
    },
    // [35] W0407 / needless-bool-branch (Auto):
    .{
        .rule_id = .needless_bool_branch,
        .expected_code = .w0407_needless_bool_branch,
        .expected_slug = "needless-bool-branch",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn is_nonzero(val: i32) -> bool {
        \\    if val != 0 => true else false
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn is_unordered_float(lhs: f64, rhs: f64) -> bool {
        \\    not (lhs == rhs)
        \\}
        ++ "\n",
    },
    // [36] W0408 / collapsible-if (Auto):
    .{
        .rule_id = .collapsible_if,
        .expected_code = .w0408_collapsible_if,
        .expected_slug = "collapsible-if",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn maybe_bump(cond_a: bool, cond_b: bool, out: &mut i32) {
        \\    if cond_a {
        \\        if cond_b {
        \\            out.* += 1;
        \\        }
        \\    }
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn keep_documented_inner(cond_a: bool, cond_b: bool, out: &mut i32) {
        \\    if cond_a {
        \\        // Preserve distinct inner branch commentary:
        \\        if cond_b {
        \\            out.* += 1;
        \\        }
        \\    }
        \\}
        ++ "\n",
    },
    // [37] W0409 / simplifiable-match (Auto):
    .{
        .rule_id = .simplifiable_match,
        .expected_code = .w0409_simplifiable_match,
        .expected_slug = "simplifiable-match",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub enum Signal {
        \\    Delta(i32),
        \\    Ping,
        \\    Quit,
        \\}
        \\
        \\pub fn apply_signal(sig: Signal, acc: &mut i32) {
        \\    match sig {
        \\        .Delta(step) => {
        \\            acc.* += step;
        \\        }
        \\        _ => {}
        \\    }
        \\}
        ++ "\n",
        .positive_src =
        \\pub enum Signal {
        \\    Delta(i32),
        \\    Ping,
        \\    Quit,
        \\}
        \\
        \\pub fn apply_signal(sig: Signal, acc: &mut i32) {
        \\    match sig {
        \\        .Delta(step) => {
        \\            acc.* += step;
        \\        }
        \\        .Ping => {
        \\            acc.* += 1;
        \\        }
        \\        .Quit => {}
        \\    }
        \\}
        ++ "\n",
    },
    // [38] W0410 / manual-orelse-or-try (Auto):
    .{
        .rule_id = .manual_orelse_or_try,
        .expected_code = .w0410_manual_orelse_or_try,
        .expected_slug = "manual-orelse-or-try",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\pub fn unwrap_default(maybe_val: i32?) -> i32 {
        \\    match maybe_val {
        \\        .Some(inner) => inner,
        \\        .None => 0,
        \\    }
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn map_increment(maybe_val: i32?) -> i32 {
        \\    match maybe_val {
        \\        .Some(inner) => inner + 1,
        \\        .None => 0,
        \\    }
        \\}
        ++ "\n",
    },
    // [39] W0411 / single-use-temp (Auto):
    .{
        .rule_id = .single_use_temp,
        .expected_code = .w0411_single_use_temp,
        .expected_slug = "single-use-temp",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\fn scale_val(val: i32) -> i32 {
        \\    val * 4 + 1
        \\}
        \\
        \\pub fn compute_scaled(val: i32) -> i32 {
        \\    let scaled_out = scale_val(val);
        \\    scaled_out
        \\}
        ++ "\n",
        .positive_src =
        \\fn bump_after_read(slot: &mut i32) {
        \\    slot.* += 1;
        \\}
        \\
        \\pub fn snapshot_before_defer(slot: &mut i32) -> i32 {
        \\    let saved = slot.*;
        \\    defer bump_after_read(slot);
        \\    saved
        \\}
        ++ "\n",
    },
    // [40] W0412 / clone-on-copy (Auto):
    .{
        .rule_id = .clone_on_copy,
        .expected_code = .w0412_clone_on_copy,
        .expected_slug = "clone-on-copy",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\@derive(Copy, Clone)
        \\pub struct TokenTag {
        \\    pub lo: u64,
        \\    pub hi: u64,
        \\}
        \\
        \\pub fn sum_tags(owned_tag: TokenTag, ref_tag: &TokenTag) -> u64 {
        \\    let first_tag = owned_tag.clone();
        \\    let second_tag = ref_tag.clone();
        \\    first_tag.lo + second_tag.hi
        \\}
        ++ "\n",
        .positive_src =
        \\pub struct HeavyBuf {
        \\    pub tag: u32,
        \\}
        \\
        \\impl Drop for HeavyBuf {
        \\    fn drop(&mut self) {
        \\        self.tag = 0;
        \\    }
        \\}
        \\
        \\impl HeavyBuf {
        \\    pub fn clone(&self) -> HeavyBuf {
        \\        HeavyBuf { tag: self.tag }
        \\    }
        \\}
        \\
        \\pub fn duplicate_borrowed(borrowed: &HeavyBuf) -> HeavyBuf {
        \\    borrowed.clone()
        \\}
        ++ "\n",
    },
    // [41] W0413 / trivially-copy-pass-by-ref (Auto on non-`pub` fn):
    .{
        .rule_id = .trivially_copy_pass_by_ref,
        .expected_code = .w0413_trivially_copy_pass_by_ref,
        .expected_slug = "trivially-copy-pass-by-ref",
        .expected_applicability = .machine_applicable,
        .negative_src =
        \\@derive(Copy, Clone)
        \\pub struct Pair8 {
        \\    pub lo: u32,
        \\    pub hi: u32,
        \\}
        \\
        \\fn pair_sum(pair: &Pair8) -> u32 {
        \\    pair.lo + pair.hi
        \\}
        \\
        \\pub fn eval_pair(pair: Pair8) -> u32 {
        \\    pair_sum(&pair)
        \\}
        ++ "\n",
        .positive_src =
        \\pub fn slice_len(bytes: &[u8]) -> usize {
        \\    bytes.len()
        \\}
        \\
        \\pub fn first_byte_ref(block: &[u8; 4]) -> &u8 {
        \\    &block[0]
        \\}
        ++ "\n",
    },
    // [42] W0414 / identical-operands (Unsafe):
    .{
        .rule_id = .identical_operands,
        .expected_code = .w0414_identical_operands,
        .expected_slug = "identical-operands",
        .expected_applicability = .maybe_incorrect,
        .negative_src =
        \\pub fn is_redundant_both(flag: bool) -> bool {
        \\    flag and flag
        \\}
        ++ "\n",
        .positive_src =
        \\fn next_step(counter: &mut i32) -> i32 {
        \\    counter.* += 1;
        \\    counter.*
        \\}
        \\
        \\pub fn is_equal_ticks(counter: &mut i32) -> bool {
        \\    next_step(counter) == next_step(counter)
        \\}
        ++ "\n",
    },
    // [43] W0501 / inlining-budget-exceeded (Diag):
    .{
        .rule_id = .inlining_budget_exceeded,
        .expected_code = .w0501_inlining_budget_exceeded,
        .expected_slug = "inlining-budget-exceeded",
        .expected_applicability = .unspecified,
        .negative_src =
        \\@inline(always)
        \\pub fn recursive_sum(n: i32) -> i32 {
        \\    if n <= 0 => 0 else recursive_sum(n - 1) + 1
        \\}
        ++ "\n",
        .positive_src =
        \\@inline(always)
        \\pub fn leaf_inc(n: i32) -> i32 {
        \\    n + 1
        \\}
        ++ "\n",
    },
};

// -------------------------------------- INTERNALS --------------------------------------

// -------------------- Verification Helpers --------------------

/// Initializes a single-file `CompilerDb` + `VfsSourceMap` fixture on `X86_64_LINUX_GNU` (`64`-bit).
fn initSingleFileHarness(
    allocator: std.mem.Allocator,
    source: []const u8,
    virtual_path: []const u8,
    target_spec: TargetSpec,
    out_interner: *StringInterner,
    out_vfs: *VfsSourceMap,
    out_db: *CompilerDb,
) !FileId {
    out_interner.* = try StringInterner.init(allocator);
    errdefer out_interner.deinit();
    out_vfs.* = VfsSourceMap.init(allocator, out_interner);
    errdefer out_vfs.deinit(std.testing.io);
    out_db.* = try CompilerDb.init(allocator);
    errdefer out_db.deinit();

    out_db.setTargetSpec(target_spec);
    const fid = try out_vfs.setOverlay(virtual_path, source, .root);
    try out_db.setFilePackageId(fid, .root);
    try out_db.setFilePath(fid, virtual_path);
    _ = try out_db.setInput(fid, source, .low);
    try out_db.setPackageLintSemanticSettings(.root, .{}, null);
    try out_db.setPackageLintFilterConfig(.root, "D:/ws", .{}, null);
    return fid;
}

/// Asserts that `diag_item` renders with `[W0xxx/slug]` and strictly `Severity.warning`.
fn assertRenderedLintHeader(
    allocator: std.mem.Allocator,
    vfs_map: *VfsSourceMap,
    interner: *const StringInterner,
    diag_item: corex.Diagnostic,
    expected_code: DiagnosticCode,
    expected_slug: []const u8,
) !void {
    try std.testing.expectEqual(Severity.warning, diag_item.severity);
    try std.testing.expect(diag_item.severity != .err);

    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();
    const diag_renderer = DiagnosticRenderer.init(vfs_map, interner, StyleConfig.MONOCHROME);
    try diag_renderer.renderDiagnostic(&out_alloc.writer, diag_item);

    const expected_tag = try std.fmt.allocPrint(
        allocator,
        "warning[{s}/{s}]:",
        .{ expected_code.asCodeStr(), expected_slug },
    );
    defer allocator.free(expected_tag);
    try std.testing.expect(std.mem.indexOf(u8, out_alloc.written(), expected_tag) != null);
}

/// Runs `verifyWorkspaceCapabilitySandbox` on a `.root` + third-party `dep` (`PackageId = 2`) pair for `W0330`.
fn runWorkspaceDepCapsCheck(
    allocator: std.mem.Allocator,
    dep_source: []const u8,
    out_sink: *DiagnosticSink,
) !void {
    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_GNU);

    const root_fid = FileId.fromInt(901);
    const dep_fid = FileId.fromInt(902);
    const dep_pkg = PackageId.fromInt(2);
    const root_src =
        \\use dep.pure_sum;
        \\
        \\pub fn main_entry() -> i32 {
        \\    pure_sum(3, 4)
        \\}
    ++ "\n";

    try db.setFilePackageId(root_fid, .root);
    try db.setFilePath(root_fid, "D:/ws/src/main.cx");
    _ = try db.setInput(root_fid, root_src, .low);
    try db.registerPackageRootFile(.root, root_fid);

    try db.setFilePackageId(dep_fid, dep_pkg);
    try db.setFilePath(dep_fid, "D:/ws/vendor/dep/lib.cx");
    _ = try db.setInput(dep_fid, dep_source, .low);
    try db.registerRootModule("dep", dep_fid);
    try db.registerPackageRootFile(dep_pkg, dep_fid);
    const dep_name_sym = try db.interner.intern("dep");
    try db.symbol_table.package_metas.put(allocator, dep_pkg, .{
        .pkg_id = dep_pkg,
        .canonical_name_sym = dep_name_sym,
        .canonical_name = "dep",
        .version_text = "1.0.0",
        .root_file_id = dep_fid,
    });
    try db.setPackageCapPolicy(dep_pkg, .{
        .package_name = "dep",
        .allowed_caps = mir_sast.EffectCapabilityMask.EMPTY,
        .is_third_party_dependency = true,
        .is_warning_ambient_dead_caps = true,
        .policy_span = Span.init(root_fid, 0, 16),
    });

    _ = try db.projectFileDiagnostics(dep_fid);
    _ = try db.projectFileDiagnostics(root_fid);

    var pkg_files_map: std.AutoHashMapUnmanaged(PackageId, []const FileId) = .empty;
    defer pkg_files_map.deinit(allocator);
    const root_slice = [_]FileId{root_fid};
    const dep_slice = [_]FileId{dep_fid};
    try pkg_files_map.put(allocator, .root, &root_slice);
    try pkg_files_map.put(allocator, dep_pkg, &dep_slice);

    const pkg_order = [_]PackageId{ .root, dep_pkg };
    const edges = [_]mir_sast.WorkspacePackageEdge{
        .{ .caller_pkg = .root, .callee_pkg = dep_pkg },
    };
    const reports = try db.verifyWorkspaceCapabilitySandbox(
        allocator,
        &pkg_order,
        &pkg_files_map,
        &edges,
        out_sink,
    );
    defer allocator.free(reports);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_dr25_exhaustive_all_44_rules_negative_positive_and_2pass_fix_convergence" {
    const allocator = std.testing.allocator;
    var verified_rules_mask: RuleMask64 = 0;
    var verified_auto_count: usize = 0;
    var verified_unsafe_count: usize = 0;
    var verified_diag_count: usize = 0;

    for (ALL_44_RULE_CASES, 0..) |spec, expected_ordinal| {
        try std.testing.expectEqual(expected_ordinal, @as(usize, spec.rule_id.asInt()));
        const meta = spec.rule_id.asMeta();
        try std.testing.expectEqual(spec.expected_code, meta.diag_code);
        try std.testing.expectEqualStrings(spec.expected_slug, meta.slug);
        try std.testing.expectEqual(spec.expected_applicability, meta.default_applicability);
        try std.testing.expectEqual(Severity.warning, spec.expected_code.defaultSeverity());

        // [1] Workspace third-party dead capability (`W0330`) & `--sim` SAST (`W0332`) modes:
        if (spec.mode == .workspace_dep_caps) {
            var neg_sink = DiagnosticSink.init(allocator);
            defer neg_sink.deinit();
            try runWorkspaceDepCapsCheck(allocator, spec.negative_src, &neg_sink);
            try std.testing.expectEqual(@as(u32, 0), neg_sink.error_count);

            var matched_neg = false;
            var interner = try StringInterner.init(allocator);
            defer interner.deinit();
            var vfs_map = VfsSourceMap.init(allocator, &interner);
            defer vfs_map.deinit(std.testing.io);
            for (neg_sink.asSlice()) |diag_item| {
                try std.testing.expectEqual(Severity.warning, diag_item.severity);
                if (diag_item.code == spec.expected_code) {
                    try assertRenderedLintHeader(
                        allocator,
                        &vfs_map,
                        &interner,
                        diag_item,
                        spec.expected_code,
                        spec.expected_slug,
                    );
                    matched_neg = true;
                }
            }
            try std.testing.expect(matched_neg);

            var pos_sink = DiagnosticSink.init(allocator);
            defer pos_sink.deinit();
            try runWorkspaceDepCapsCheck(allocator, spec.positive_src, &pos_sink);
            try std.testing.expectEqual(@as(usize, 0), pos_sink.countDiagnostics());

            verified_diag_count += 1;
            verified_rules_mask |= spec.rule_id.bit();
            continue;
        }

        if (spec.mode == .sim_mode_sast) {
            var neg_bundle = try mir_sast.lowerAndVerifySourceMirSast(
                allocator,
                FileId.fromInt(910),
                spec.negative_src,
                type_system.TargetLayout.NATIVE_64,
                .{ .is_sim_mode = true },
            );
            defer neg_bundle.deinit();
            try std.testing.expectEqual(@as(u32, 0), neg_bundle.diagnostics.error_count);

            var matched_sim = false;
            var vfs_map = VfsSourceMap.init(allocator, &neg_bundle.interner);
            defer vfs_map.deinit(std.testing.io);
            for (neg_bundle.diagnostics.asSlice()) |diag_item| {
                try std.testing.expectEqual(Severity.warning, diag_item.severity);
                if (diag_item.code == spec.expected_code) {
                    try assertRenderedLintHeader(
                        allocator,
                        &vfs_map,
                        &neg_bundle.interner,
                        diag_item,
                        spec.expected_code,
                        spec.expected_slug,
                    );
                    matched_sim = true;
                }
            }
            try std.testing.expect(matched_sim);

            var pos_bundle = try mir_sast.lowerAndVerifySourceMirSast(
                allocator,
                FileId.fromInt(911),
                spec.positive_src,
                type_system.TargetLayout.NATIVE_64,
                .{ .is_sim_mode = true },
            );
            defer pos_bundle.deinit();
            try std.testing.expectEqual(@as(usize, 0), pos_bundle.diagnostics.countDiagnostics());

            verified_diag_count += 1;
            verified_rules_mask |= spec.rule_id.bit();
            continue;
        }

        // [2] Positive false-positive guard (`0` errors and `0` warnings):
        {
            var pos_interner: StringInterner = undefined;
            var pos_vfs: VfsSourceMap = undefined;
            var pos_db: CompilerDb = undefined;
            const pos_fid = try initSingleFileHarness(
                allocator,
                spec.positive_src,
                "D:/ws/src/positive_guard.cx",
                TargetSpec.X86_64_LINUX_GNU,
                &pos_interner,
                &pos_vfs,
                &pos_db,
            );
            defer {
                pos_db.deinit();
                pos_vfs.deinit(std.testing.io);
                pos_interner.deinit();
            }
            const pos_sink = try pos_db.projectFileDiagnostics(pos_fid);
            if (pos_sink.countDiagnostics() != 0) {
                for (pos_sink.asSlice()) |unexpected_diag| {
                    std.debug.print(
                        "Unexpected positive-guard diagnostic for `{s}`: [{s}] {s}\n",
                        .{ spec.expected_slug, unexpected_diag.code.asCodeStr(), unexpected_diag.message },
                    );
                }
            }
            try std.testing.expectEqual(@as(u32, 0), pos_sink.error_count);
            try std.testing.expectEqual(@as(usize, 0), pos_sink.countDiagnostics());
        }

        // [3] Negative trigger + `[W0xxx/slug]` rendered header + `<= 2`-pass auto-fix convergence:
        {
            var neg_interner: StringInterner = undefined;
            var neg_vfs: VfsSourceMap = undefined;
            var neg_db: CompilerDb = undefined;
            const neg_fid = try initSingleFileHarness(
                allocator,
                spec.negative_src,
                "D:/ws/src/negative_case.cx",
                TargetSpec.X86_64_LINUX_GNU,
                &neg_interner,
                &neg_vfs,
                &neg_db,
            );
            defer {
                neg_db.deinit();
                neg_vfs.deinit(std.testing.io);
                neg_interner.deinit();
            }

            const neg_sink = try neg_db.projectFileDiagnostics(neg_fid);
            try std.testing.expectEqual(@as(u32, 0), neg_sink.error_count);

            var hit_expected_rule = false;
            for (neg_sink.asSlice()) |diag_item| {
                try std.testing.expectEqual(Severity.warning, diag_item.severity);
                if (diag_item.code == spec.expected_code) {
                    try assertRenderedLintHeader(
                        allocator,
                        &neg_vfs,
                        &neg_db.interner,
                        diag_item,
                        spec.expected_code,
                        spec.expected_slug,
                    );
                    hit_expected_rule = true;
                }
            }
            if (!hit_expected_rule) {
                std.debug.print("Missing negative trigger for `{s}` (`{s}`)\n", .{
                    spec.expected_code.asCodeStr(),
                    spec.expected_slug,
                });
            }
            try std.testing.expect(hit_expected_rule);

            switch (spec.expected_applicability) {
                .machine_applicable => {
                    const report = try check_audit.applyCheckFixesOnDb(allocator, &neg_db, .{
                        .vfs = &neg_vfs,
                        .candidate_files = &.{neg_fid},
                        .allow_unsafe_fixes = false,
                    });
                    try std.testing.expect(!report.is_rolled_back);
                    try std.testing.expect(report.applied_fix_count >= 1);
                    try std.testing.expect(report.pass_count <= 2);

                    const post_sink = try neg_db.projectFileDiagnostics(neg_fid);
                    if (post_sink.countDiagnostics() != 0) {
                        for (post_sink.asSlice()) |rem_diag| {
                            std.debug.print(
                                "Post-`--fix` residual diagnostic for `{s}`: [{s}] {s}\n",
                                .{ spec.expected_slug, rem_diag.code.asCodeStr(), rem_diag.message },
                            );
                        }
                    }
                    try std.testing.expectEqual(@as(u32, 0), post_sink.error_count);
                    try std.testing.expectEqual(@as(u32, 0), post_sink.warning_count);
                    verified_auto_count += 1;
                },
                .maybe_incorrect => {
                    // Must NOT apply under safe `--fix` (`allow_unsafe_fixes = false`):
                    const safe_report = try check_audit.applyCheckFixesOnDb(allocator, &neg_db, .{
                        .vfs = &neg_vfs,
                        .candidate_files = &.{neg_fid},
                        .allow_unsafe_fixes = false,
                    });
                    try std.testing.expect(!safe_report.is_rolled_back);
                    try std.testing.expectEqual(@as(u32, 0), safe_report.applied_fix_count);
                    try std.testing.expect(safe_report.pass_count <= 2);

                    const still_dirty = try neg_db.projectFileDiagnostics(neg_fid);
                    try std.testing.expect(still_dirty.warning_count >= 1);

                    // Must apply cleanly in `<= 2` passes under `--fix-unsafe` (`allow_unsafe_fixes = true`):
                    const unsafe_report = try check_audit.applyCheckFixesOnDb(allocator, &neg_db, .{
                        .vfs = &neg_vfs,
                        .candidate_files = &.{neg_fid},
                        .allow_unsafe_fixes = true,
                    });
                    try std.testing.expect(!unsafe_report.is_rolled_back);
                    try std.testing.expect(unsafe_report.applied_fix_count >= 1);
                    try std.testing.expect(unsafe_report.pass_count <= 2);

                    const post_sink = try neg_db.projectFileDiagnostics(neg_fid);
                    if (post_sink.countDiagnostics() != 0) {
                        for (post_sink.asSlice()) |rem_diag| {
                            std.debug.print(
                                "Post-`--fix-unsafe` residual diagnostic for `{s}`: [{s}] {s}\n",
                                .{ spec.expected_slug, rem_diag.code.asCodeStr(), rem_diag.message },
                            );
                        }
                    }
                    try std.testing.expectEqual(@as(u32, 0), post_sink.error_count);
                    try std.testing.expectEqual(@as(u32, 0), post_sink.warning_count);
                    verified_unsafe_count += 1;
                },
                .unspecified, .has_placeholders => {
                    const diag_report = try check_audit.applyCheckFixesOnDb(allocator, &neg_db, .{
                        .vfs = &neg_vfs,
                        .candidate_files = &.{neg_fid},
                        .allow_unsafe_fixes = true,
                    });
                    try std.testing.expect(!diag_report.is_rolled_back);
                    try std.testing.expectEqual(@as(u32, 0), diag_report.applied_fix_count);
                    verified_diag_count += 1;
                },
            }
        }

        verified_rules_mask |= spec.rule_id.bit();
    }

    try std.testing.expectEqual(@as(usize, 26), verified_auto_count);
    try std.testing.expectEqual(@as(usize, 7), verified_unsafe_count);
    try std.testing.expectEqual(@as(usize, 11), verified_diag_count);
    try std.testing.expectEqual(corex.ALL_RULES_MASK, verified_rules_mask);
}

test "test_dr25_cascading_stale_expect_cleanup_after_pass1_warning_fix" {
    const allocator = std.testing.allocator;

    // Pass 1 fixes `W0410` (`match res { .Ok(num) => num, .Err(e) => return .Err(e) }` -> `res?`),
    // eliminating the `e` binding that previously fulfilled `@expect(single-char-ident, ...)`.
    // Pass 2 detects that `@expect(single-char-ident, ...)` is now stale (`W0002`) and prunes it!
    const cascade_src =
        \\@derive(Copy, Clone)
        \\pub enum StepErr {
        \\    BadDigit,
        \\}
        \\
        \\@expect(single-char-ident, reason: "error binding inside manual match")
        \\pub fn propagate_step(res: i32!StepErr) -> i32!StepErr {
        \\    let unwrapped = match res {
        \\        .Ok(num) => num,
        \\        .Err(e) => return .Err(e),
        \\    };
        \\    .Ok(unwrapped + 1)
        \\}
    ++ "\n";

    var interner: StringInterner = undefined;
    var vfs_map: VfsSourceMap = undefined;
    var db: CompilerDb = undefined;
    const fid = try initSingleFileHarness(
        allocator,
        cascade_src,
        "D:/ws/src/cascade_expect.cx",
        TargetSpec.X86_64_LINUX_GNU,
        &interner,
        &vfs_map,
        &db,
    );
    defer {
        db.deinit();
        vfs_map.deinit(std.testing.io);
        interner.deinit();
    }

    const pre_sink = try db.projectFileDiagnostics(fid);
    try std.testing.expectEqual(@as(u32, 0), pre_sink.error_count);
    try std.testing.expectEqual(@as(u32, 1), pre_sink.warning_count);
    try std.testing.expectEqual(DiagnosticCode.w0410_manual_orelse_or_try, pre_sink.asSlice()[0].code);

    const report = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
        .vfs = &vfs_map,
        .candidate_files = &.{fid},
        .allow_unsafe_fixes = false,
    });
    try std.testing.expect(!report.is_rolled_back);
    try std.testing.expectEqual(@as(u32, 2), report.applied_fix_count);

    const fixed_src = try db.getSourceText(fid);
    try std.testing.expect(std.mem.indexOf(u8, fixed_src, "@expect") == null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_src, "res?") != null);

    const post_sink = try db.projectFileDiagnostics(fid);
    try std.testing.expectEqual(@as(u32, 0), post_sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), post_sink.warning_count);

    // Idempotent second `--fix` invocation applies `0` edits in `1` check pass:
    const idemp_report = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
        .vfs = &vfs_map,
        .candidate_files = &.{fid},
        .allow_unsafe_fixes = false,
    });
    try std.testing.expect(!idemp_report.is_rolled_back);
    try std.testing.expectEqual(@as(u32, 0), idemp_report.applied_fix_count);
    try std.testing.expect(idemp_report.pass_count <= 2);
}

test "test_dr25_crlf_four_scope_suppression_deletion_and_docstring_hoisting" {
    const allocator = std.testing.allocator;

    // [1] CRLF (`\r\n`) Scope-2 `file-expect` partial pruning + Scope-3 `@expect` standalone-line deletion
    //     + Scope-4 trailing `// corex check: expect(...)` pruning:
    {
        const crlf_scopes_src =
            "// corex check: file-expect(W0123, W0122) -- crlf file preamble\r\n\r\n" ++
            "/| Computes masked header word.\r\n" ++
            "@expect(W0101, reason: \"crlf stale standalone attr\")\r\n" ++
            "pub fn mask_header(seed: u32) -> u32 {\r\n" ++
            "    let base = 0xdead_beef_u32;\r\n" ++
            "    let clean = seed ^ base; // corex check: expect(W0208) -- crlf stale trailing\r\n" ++
            "    clean ^ 1_u32\r\n" ++
            "}\r\n";
        try std.testing.expect(std.mem.indexOf(u8, crlf_scopes_src, "\r\n") != null);

        var interner: StringInterner = undefined;
        var vfs_map: VfsSourceMap = undefined;
        var db: CompilerDb = undefined;
        const fid = try initSingleFileHarness(
            allocator,
            crlf_scopes_src,
            "D:/ws/src/crlf_scopes.cx",
            TargetSpec.X86_64_WINDOWS_MSVC,
            &interner,
            &vfs_map,
            &db,
        );
        defer {
            db.deinit();
            vfs_map.deinit(std.testing.io);
            interner.deinit();
        }

        const pre_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(u32, 0), pre_sink.error_count);
        // Exactly 3 stale expectations (`W0122` in Scope 2, `W0101` in Scope 3, `W0208` in Scope 4):
        try std.testing.expectEqual(@as(u32, 3), pre_sink.warning_count);
        for (pre_sink.asSlice()) |diag_item| {
            try std.testing.expectEqual(DiagnosticCode.w0002_unused_suppression, diag_item.code);
        }

        const report = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .vfs = &vfs_map,
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        try std.testing.expect(!report.is_rolled_back);
        try std.testing.expect(report.pass_count <= 2);

        const patched = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, patched, "file-expect(W0123) -- crlf file preamble") != null);
        try std.testing.expect(std.mem.indexOf(u8, patched, "W0101") == null);
        try std.testing.expect(std.mem.indexOf(u8, patched, "W0208") == null);
        try std.testing.expect(std.mem.indexOf(u8, patched, "/| Computes masked header word.\n") != null);

        const post_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(u32, 0), post_sink.error_count);
        try std.testing.expectEqual(@as(u32, 0), post_sink.warning_count);
    }

    // [2] CRLF (`\r\n`) above-line `// corex check: expect(...)` hoisting below multi-line `/|` docstrings (`W0202`):
    {
        const crlf_hoist_src =
            "// corex check: expect(single-char-ident) -- crlf hoist below docstrings\r\n" ++
            "/| Evaluates single-step offset.\r\n" ++
            "/| Preserves docstring ordering under CRLF.\r\n" ++
            "pub fn eval_offset(c: i32) -> i32 {\r\n" ++
            "    c + 1\r\n" ++
            "}\r\n";

        var interner: StringInterner = undefined;
        var vfs_map: VfsSourceMap = undefined;
        var db: CompilerDb = undefined;
        const fid = try initSingleFileHarness(
            allocator,
            crlf_hoist_src,
            "D:/ws/src/crlf_hoist.cx",
            TargetSpec.X86_64_WINDOWS_MSVC,
            &interner,
            &vfs_map,
            &db,
        );
        defer {
            db.deinit();
            vfs_map.deinit(std.testing.io);
            interner.deinit();
        }

        const pre_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(u32, 0), pre_sink.error_count);
        try std.testing.expectEqual(@as(u32, 1), pre_sink.warning_count);
        try std.testing.expectEqual(DiagnosticCode.w0202_non_idiomatic_construct, pre_sink.asSlice()[0].code);

        const report = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .vfs = &vfs_map,
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        try std.testing.expect(!report.is_rolled_back);
        try std.testing.expect(report.pass_count <= 2);

        const hoisted = try db.getSourceText(fid);
        const doc_pos = std.mem.indexOf(u8, hoisted, "/| Preserves docstring ordering under CRLF.").?;
        const attr_pos = std.mem.indexOf(
            u8,
            hoisted,
            "@expect(single-char-ident, reason: \"crlf hoist below docstrings\")",
        ).?;
        const fn_pos = std.mem.indexOf(u8, hoisted, "pub fn eval_offset(c: i32) -> i32").?;
        try std.testing.expect(doc_pos < attr_pos);
        try std.testing.expect(attr_pos < fn_pos);

        const post_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(u32, 0), post_sink.error_count);
        try std.testing.expectEqual(@as(u32, 0), post_sink.warning_count);
    }
}

test "test_dr25_cross_platform_compiled_glob64_paths_and_multi_target_w0413" {
    const allocator = std.testing.allocator;

    // [1] `CompiledGlob64` Windows `\` vs. POSIX `/` path matching & `[[lint.overrides]]` resolution:
    {
        var arena = BumpArena.init(allocator);
        defer arena.deinit();
        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();

        const glob_tests = (try pkg_manifest.compileGlob64(
            &arena,
            &interner,
            "tests/**/*.{cx,cxi}",
            Span.ZERO,
            &sink,
        )).?;
        const glob_strict = (try pkg_manifest.compileGlob64(
            &arena,
            &interner,
            "tests/security_strict/**/*.cx",
            Span.ZERO,
            &sink,
        )).?;
        try std.testing.expectEqual(@as(usize, 0), sink.countDiagnostics());

        try std.testing.expect(glob_tests.matchesPath("tests/unit/net_test.cx"));
        try std.testing.expect(glob_tests.matchesPath("tests\\unit\\net_test.cx"));
        try std.testing.expect(glob_tests.matchesPath(".\\tests\\fuzz\\seed_01.cxi"));
        try std.testing.expect(glob_tests.matchesPath("./tests/nested/deep/check.cx"));
        try std.testing.expect(!glob_tests.matchesPath("src\\tests_helper\\mod.cx"));

        const overrides = [_]pkg_manifest.LintOverride{
            .{
                .files = &.{glob_tests},
                .exclude_files = &.{glob_strict},
                .disable_mask = RuleId.single_char_ident.bit() | RuleId.unused_pkg_visibility.bit(),
            },
        };
        const lint_cfg: pkg_manifest.LintConfig = .{
            .overrides = &overrides,
        };

        const win_relaxed = lint_cfg.resolveFileDisabledMask(".\\tests\\unit\\win_path_test.cx", .{});
        const posix_relaxed = lint_cfg.resolveFileDisabledMask("tests/unit/win_path_test.cx", .{});
        try std.testing.expectEqual(posix_relaxed, win_relaxed);
        try std.testing.expect((win_relaxed & RuleId.single_char_ident.bit()) != 0);

        const win_strict = lint_cfg.resolveFileDisabledMask("tests\\security_strict\\auth\\verify.cx", .{});
        const posix_strict = lint_cfg.resolveFileDisabledMask("tests/security_strict/auth/verify.cx", .{});
        try std.testing.expectEqual(@as(RuleMask64, 0), win_strict);
        try std.testing.expectEqual(@as(RuleMask64, 0), posix_strict);
    }

    // [2] `W0413` (`trivially-copy-pass-by-ref`) across Windows MSVC, Linux GNU, Apple ARM64, and `wasm32-wasi`:
    const targets = [_]struct {
        spec: TargetSpec,
        expects_8b_warning: bool,
    }{
        .{ .spec = TargetSpec.X86_64_WINDOWS_MSVC, .expects_8b_warning = true },
        .{ .spec = TargetSpec.X86_64_LINUX_GNU, .expects_8b_warning = true },
        .{ .spec = TargetSpec.AARCH64_APPLE_DARWIN, .expects_8b_warning = true },
        .{ .spec = TargetSpec.WASM32_UNKNOWN_WASI, .expects_8b_warning = false },
    };

    const abi_probe_src =
        \\@derive(Copy, Clone)
        \\pub struct Small4 {
        \\    pub raw: u32,
        \\}
        \\
        \\@derive(Copy, Clone)
        \\pub struct Medium8 {
        \\    pub lo: u32,
        \\    pub hi: u32,
        \\}
        \\
        \\@derive(Copy, Clone)
        \\pub struct Large16 {
        \\    pub first_word: u64,
        \\    pub second_word: u64,
        \\}
        \\
        \\fn read_small(item: &Small4) -> u32 {
        \\    item.raw
        \\}
        \\
        \\fn read_medium(item: &Medium8) -> u32 {
        \\    item.lo + item.hi
        \\}
        \\
        \\pub fn probe_all(s_val: Small4, m_val: Medium8, l_ref: &Large16, bytes: &[u8]) -> u64 {
        \\    let sum32 = read_small(&s_val) + read_medium(&m_val);
        \\    (sum32 as u64) + l_ref.first_word + l_ref.second_word + (bytes.len() as u64)
        \\}
    ++ "\n";

    for (targets) |target_case| {
        var interner: StringInterner = undefined;
        var vfs_map: VfsSourceMap = undefined;
        var db: CompilerDb = undefined;
        const fid = try initSingleFileHarness(
            allocator,
            abi_probe_src,
            "D:/ws/src/abi_probe.cx",
            target_case.spec,
            &interner,
            &vfs_map,
            &db,
        );
        defer {
            db.deinit();
            vfs_map.deinit(std.testing.io);
            interner.deinit();
        }

        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(u32, 0), sink.error_count);

        var w0413_count: usize = 0;
        for (sink.asSlice()) |diag_item| {
            if (diag_item.code == .w0413_trivially_copy_pass_by_ref) {
                w0413_count += 1;
            }
        }
        // `Small4` (`4 B`) triggers on all 4 targets; `Medium8` (`8 B`) triggers only on 64-bit targets;
        // `Large16` (`16 B`) and `&[u8]` never trigger on any target!
        const expected_count: usize = if (target_case.expects_8b_warning) 2 else 1;
        try std.testing.expectEqual(expected_count, w0413_count);

        const fix_report = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .vfs = &vfs_map,
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        try std.testing.expect(!fix_report.is_rolled_back);
        try std.testing.expect(fix_report.pass_count <= 2);

        const post_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(u32, 0), post_sink.error_count);
        try std.testing.expectEqual(@as(u32, 0), post_sink.warning_count);
    }
}
