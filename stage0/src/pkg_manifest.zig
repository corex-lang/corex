//! Lossless TOML v1.0 CST, `corex.toml` Manifest, Script Frontmatter & `corex.lock` Engine
//!
//! Implements the non-backtracking DFA TOML v1.0 lexer (`8B` `TomlToken`, `8B` `TomlTriviaPiece`),
//! flat SoA `TomlCstArena` (`16B` `TomlCstNode`, `24B` `TomlSpanAnchor`), SemVer 2.0.0 & Bounded-MVS
//! `VersionReq` algebra, bijective `kebab-case` <-> `snake_case` package validation (`E0013`), CoreX
//! `@cfg` `target` evaluation, `"unsafe_op"` capability validation, `.cx` `#!` + `---` blank-in-place
//! script frontmatter, surgical `TransactionalPatcher` manifest edits, and canonical `corex.lock` v1.
//!
//! Enforces strict deterministic resource caps (`MAX_TOML_BYTES = 1 MiB`, `MAX_TOML_TOKENS = 65,536`,
//! `MAX_TOML_DEPTH = 16`) and canonical `(name_ascii ASC, SemVer.compare ASC, source_ascii ASC)`
//! lockfile ordering (`E0014` on corruption, version drift, or invalid `"b3:<64-hex>"` digests).

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const mir_sast = @import("mir_sast.zig");
const mir_vm = @import("mir_vm.zig");
const diagnostic = @import("diag/diagnostic.zig");
const lint_filter = @import("lint_filter.zig");
const pkg_conflict_seam = @import("pkg_conflict_seam.zig");

const FileId = mem_foundation.FileId;
const StringId = mem_foundation.StringId;
const Span = mem_foundation.Span;
const BumpArena = mem_foundation.BumpArena;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const TokenKind = syntax_arenas.TokenKind;
const TokenBuffer = syntax_arenas.TokenBuffer;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstArena = syntax_arenas.AstArena;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const SuggestedFix = diagnostic.SuggestedFix;
const TextEdit = diagnostic.TextEdit;

// ---------------------------------------- TYPES ----------------------------------------

// --------------- SemVer & Version Requirements ----------------

/// Re-exported 24-byte lossless TOML key/value span anchor (`pkg_conflict_seam.TomlSpanAnchor`).
pub const TomlSpanAnchor = pkg_conflict_seam.TomlSpanAnchor;
/// Re-exported conflict-free interval scheduler (`diagnostic.TransactionalPatcher`).
pub const TransactionalPatcher = diagnostic.TransactionalPatcher;
/// Re-exported 16-bit capability/effect bitmask (`mir_sast.EffectCapabilityMask`).
pub const EffectCapabilityMask = mir_sast.EffectCapabilityMask;
/// Re-exported `@cfg` evaluation environment (`symbol_resolver.CfgEnv`).
pub const CfgEnv = symbol_resolver.CfgEnv;
/// Re-exported dense `0..43` lint rule identifier (`diagnostic.RuleId`).
pub const RuleId = diagnostic.RuleId;
/// Re-exported 64-bit lint rule bitmask (`diagnostic.RuleMask64`).
pub const RuleMask64 = diagnostic.RuleMask64;
/// Re-exported semantic `[lint.settings]` configuration (`lint_filter.LintSettings`).
pub const LintSettings = lint_filter.LintSettings;
/// Re-exported 128-bit `[lint.settings]` content digest (`lint_filter.SemanticSettingsDigest`).
pub const SemanticSettingsDigest = lint_filter.SemanticSettingsDigest;
/// Re-exported CLI `--only` / `--disable` filter (`lint_filter.CliLintFilter`).
pub const CliLintFilter = lint_filter.CliLintFilter;

/// Compatibility-series tier used by Bounded-MVS (`DR-11` §3.1).
pub const SeriesTier = enum(u8) {
    /// Major release series `N.x.y` with `N >= 1` (`1.x` and `2.x` coexist as distinct series).
    major_ge_1 = 0,
    /// Pre-1.0 minor series `0.M.z` with `M >= 1` (`0.1.x` and `0.2.x` coexist as distinct series).
    minor_0_x = 1,
    /// Initial patch series `0.0.Z` (`0.0.1` and `0.0.2` coexist as distinct series).
    patch_0_0_z = 2,
};

/// Exact 12-byte (`96`-bit, `0` padding) SemVer numeric core `(major, minor, patch)`.
pub const SemVerCore = extern struct {
    /// Major version component (`X` in `X.Y.Z`).
    major: u32 = 0,
    /// Minor version component (`Y` in `X.Y.Z`).
    minor: u32 = 0,
    /// Patch version component (`Z` in `X.Y.Z`).
    patch: u32 = 0,

    /// Compares two `SemVerCore` tuples in `(major, minor, patch)` lexicographic order.
    pub fn compare(lhs: SemVerCore, rhs: SemVerCore) std.math.Order {
        if (lhs.major != rhs.major) return std.math.order(lhs.major, rhs.major);
        if (lhs.minor != rhs.minor) return std.math.order(lhs.minor, rhs.minor);
        return std.math.order(lhs.patch, rhs.patch);
    }
};

/// Exact 20-byte (`160`-bit, `0` padding) SemVer 2.0.0 record using interned `StringId` suffixes.
pub const SemVer = extern struct {
    /// Major version number (`0..maxInt(u32)`).
    major: u32 = 0,
    /// Minor version number (`0..maxInt(u32)`).
    minor: u32 = 0,
    /// Patch version number (`0..maxInt(u32)`).
    patch: u32 = 0,
    /// Dot-separated pre-release suffix (`StringId.empty` for normal releases; e.g., `"alpha.1"`).
    pre: StringId = .empty,
    /// Build metadata suffix (`StringId.empty` when omitted; ignored in `compare`).
    build: StringId = .empty,

    /// Extracts the 12-byte numeric `SemVerCore` projection of `self`.
    pub inline fn asCore(self: SemVer) SemVerCore {
        return .{ .major = self.major, .minor = self.minor, .patch = self.patch };
    }

    /// Classifies `self` into its `DR-11` §3.1 Bounded-MVS compatibility series `(tier, number)`.
    pub inline fn classifySeriesSlot(self: SemVer) struct { tier: SeriesTier, number: u32 } {
        if (self.major >= 1) return .{ .tier = .major_ge_1, .number = self.major };
        if (self.minor >= 1) return .{ .tier = .minor_0_x, .number = self.minor };
        return .{ .tier = .patch_0_0_z, .number = self.patch };
    }

    /// Parses strict SemVer 2.0.0 (`X.Y.Z[-pre][+build]`), returning `null` on invalid syntax.
    pub fn parse(interner: *StringInterner, raw_text: []const u8) !?SemVer {
        return parseSemVerImpl(interner, raw_text);
    }

    /// Compares `lhs` and `rhs` per SemVer 2.0.0 §11 precedence (`build` metadata ignored).
    pub fn compare(lhs: SemVer, rhs: SemVer, interner: *const StringInterner) std.math.Order {
        const core_ord = SemVerCore.compare(lhs.asCore(), rhs.asCore());
        if (core_ord != .eq) return core_ord;
        const lhs_pre = interner.get(lhs.pre);
        const rhs_pre = interner.get(rhs.pre);
        return compareSemVerPreSlices(lhs_pre, rhs_pre);
    }

    /// Total order extending `compare` with ASCII `build` metadata tie-breaking for `corex.lock`.
    pub fn compareTotal(lhs: SemVer, rhs: SemVer, interner: *const StringInterner) std.math.Order {
        const prec_ord = compare(lhs, rhs, interner);
        if (prec_ord != .eq) return prec_ord;
        return std.mem.order(u8, interner.get(lhs.build), interner.get(rhs.build));
    }

    /// Returns `true` when `lhs` and `rhs` have equal SemVer 2.0.0 precedence.
    pub inline fn eql(lhs: SemVer, rhs: SemVer, interner: *const StringInterner) bool {
        return compare(lhs, rhs, interner) == .eq;
    }

    /// Appends canonical `"X.Y.Z[-pre][+build]"` text of `self` onto `builder`.
    pub fn appendFormatted(
        self: SemVer,
        builder: *std.ArrayList(u8),
        allocator: std.mem.Allocator,
        interner: *const StringInterner,
    ) !void {
        var core_buf: [40]u8 = undefined;
        const core_str = try std.fmt.bufPrint(&core_buf, "{d}.{d}.{d}", .{ self.major, self.minor, self.patch });
        try builder.appendSlice(allocator, core_str);
        const pre_str = interner.get(self.pre);
        if (pre_str.len > 0) {
            try builder.append(allocator, '-');
            try builder.appendSlice(allocator, pre_str);
        }
        const build_str = interner.get(self.build);
        if (build_str.len > 0) {
            try builder.append(allocator, '+');
            try builder.appendSlice(allocator, build_str);
        }
    }

    /// Formats `self` into a newly allocated canonical SemVer string.
    pub fn formatAlloc(
        self: SemVer,
        allocator: std.mem.Allocator,
        interner: *const StringInterner,
    ) ![]u8 {
        var builder: std.ArrayList(u8) = .empty;
        errdefer builder.deinit(allocator);
        try self.appendFormatted(&builder, allocator, interner);
        return builder.toOwnedSlice(allocator);
    }
};

/// Atomic version comparator operator inside a `VersionReq` conjunction.
pub const ComparatorOp = enum(u8) {
    /// Exact version equality (`=1.2.3`).
    exact = 0,
    /// Inclusive lower bound (`>=1.2.0`).
    greater_eq = 1,
    /// Strict lower bound (`>1.2.0`).
    greater = 2,
    /// Inclusive upper bound (`<=1.5.0`).
    less_eq = 3,
    /// Exclusive upper bound (`<2.0.0`).
    less = 4,
    /// Unrestricted wildcard (`*`).
    wildcard_any = 5,
};

/// Single normalized version comparator atom `(op, ver)`.
pub const VersionComparator = struct {
    /// Relational operator of this comparator.
    op: ComparatorOp = .wildcard_any,
    /// Target `SemVer` operand.
    ver: SemVer = .{},
};

/// Conjunction of up to `MAX_VERSION_COMPARATORS` (`8`) atomic SemVer comparators.
pub const VersionReq = struct {
    /// Fixed inline array of atomic comparators (`0 .. len`).
    comparators: [MAX_VERSION_COMPARATORS]VersionComparator = @splat(.{}),
    /// Number of active comparators in `comparators` (`1..8`).
    len: u8 = 0,
    /// Highest lower-bound floor implied by `comparators` (used for $O(1)$ MVS candidate seeding).
    min_floor: SemVer = .{},
    /// `true` when an upper bound tighter than the natural `SeriesKey` ceiling is present.
    has_intra_series_upper_bound: bool = false,

    /// Parses bare MVS `"1.4.2"`, caret `"^1.2"`, tilde `"~0.4.1"`, wildcard `"1.*"`, or `">=1.0, <1.5"`.
    pub fn parse(interner: *StringInterner, raw_req: []const u8) !?VersionReq {
        return parseVersionReqImpl(interner, raw_req);
    }

    /// Evaluates whether `candidate` satisfies all comparators in `self` (including pre-release rules).
    pub fn isMatchedBy(self: *const VersionReq, candidate: SemVer, interner: *const StringInterner) bool {
        return isVersionReqMatchingImpl(self, candidate, interner);
    }
};

// -------------- Lossless TOML Token & CST Arenas --------------

/// Contiguous 1-byte TOML v1.0 syntactic token kind (`0..19`).
pub const TomlTokenKind = enum(u8) {
    /// Unquoted key identifier (`[A-Za-z0-9_-]+`).
    bare_key = 0,
    /// Double-quoted single-line string (`"…"`).
    basic_string = 1,
    /// Triple-double-quoted multiline string (`"""…"""`).
    multiline_basic_string = 2,
    /// Single-quoted literal string (`'…'`).
    literal_string = 3,
    /// Triple-single-quoted multiline literal string (`'''…'''`).
    multiline_literal_string = 4,
    /// Decimal, hexadecimal (`0x`), octal (`0o`), or binary (`0b`) integer literal.
    int_lit = 5,
    /// Floating-point literal (`1.0`, `1e-5`, `inf`, `nan`).
    float_lit = 6,
    /// Boolean literal (`true` or `false`).
    bool_lit = 7,
    /// RFC 3339 / ISO-8601 date, time, or offset/local datetime literal.
    datetime_lit = 8,
    /// Single opening bracket (`[`).
    lbracket = 9,
    /// Double opening bracket (`[[` at table-header position).
    double_lbracket = 10,
    /// Single closing bracket (`]`).
    rbracket = 11,
    /// Double closing bracket (`]]` closing an array-of-tables header).
    double_rbracket = 12,
    /// Inline-table opening brace (`{`).
    lbrace = 13,
    /// Inline-table closing brace (`}`).
    rbrace = 14,
    /// Key-value assignment equals (`=`).
    eq = 15,
    /// Dotted-key path separator (`.`).
    dot = 16,
    /// Array or inline-table element comma (`,`).
    comma = 17,
    /// Malformed lexical sequence preserved losslessly for error recovery.
    invalid_token = 18,
    /// End-of-document sentinel token.
    eof = 19,
};

/// 1-byte bit-packed lexical flags attached to each `TomlToken`.
pub const TomlTokenFlags = packed struct(u8) {
    /// `true` if at least one `\n` preceded this token since the previous token.
    has_leading_newline: bool = false,
    /// `true` if at least one `#` comment preceded this token since the previous token.
    has_leading_comment: bool = false,
    /// `true` if a same-line `#` comment trails this token before `\n`.
    has_trailing_comment: bool = false,
    /// `true` if an adjacent `#` comment mentions `CVE-`, `GHSA-`, or `CXSEC-`.
    has_cve_comment: bool = false,
    /// `true` if string contains `\` escapes or token length saturated `0xFFFF`.
    has_escape_or_long_len: bool = false,
    /// `true` if a lexical violation occurred while scanning this token.
    has_lexer_error: bool = false,
    /// Reserved zero bits (`0`).
    reserved: u2 = 0,
};

/// Exact 8-byte (`64`-bit, `0` padding) TOML token record stored in SoA `TomlTokenBuffer`.
pub const TomlToken = extern struct {
    /// Byte offset relative to `TomlDocumentView.toml_slice`.
    byte_offset: u32 = 0,
    /// Clamped byte length (`0xFFFF` when `>= 65,535`).
    byte_len: u16 = 0,
    /// Syntactic classification of this token.
    kind: TomlTokenKind = .eof,
    /// Packed trivia/escape/error flags.
    flags: TomlTokenFlags = .{},
};

/// Trivia kind stored inside `TomlTriviaMeta`.
pub const TomlTriviaKind = enum(u2) {
    /// Horizontal whitespace (`' '` or `'\t'`).
    spaces_or_tabs = 0,
    /// Unix line feed (`\n`).
    newline_lf = 1,
    /// Windows carriage-return + line-feed (`\r\n`).
    newline_crlf = 2,
    /// Hash comment (`# …` up to line break).
    hash_comment = 3,
};

/// 1-byte packed metadata on each `TomlTriviaPiece`.
pub const TomlTriviaMeta = packed struct(u8) {
    /// Trivia classification.
    kind: TomlTriviaKind = .spaces_or_tabs,
    /// `true` when attached on the same line after a syntactic token.
    is_trailing: bool = false,
    /// `true` when `#` comment slice contains `CVE-`, `GHSA-`, or `CXSEC-`.
    has_cve_advisory: bool = false,
    /// Clamped count of blank lines immediately preceding this comment (`0..3`).
    blank_lines_before: u2 = 0,
    /// `true` when followed immediately by `\n` or `\r\n`.
    has_newline_after: bool = false,
    /// Reserved zero bit (`0`).
    reserved: u1 = 0,
};

/// Exact 8-byte (`64`-bit, `0` padding) whitespace/comment trivia record.
pub const TomlTriviaPiece = extern struct {
    /// Byte offset relative to `TomlDocumentView.toml_slice`.
    byte_offset: u32 = 0,
    /// Clamped byte length (`<= 65,535`).
    byte_len: u16 = 0,
    /// Packed trivia metadata flags.
    meta: TomlTriviaMeta = .{},
    /// Clamped leading column indentation (`0..255`).
    indent_cols: u8 = 0,
};

/// Flat Structure-of-Arrays (`SoA`) TOML token and `#` comment trivia buffer.
pub const TomlTokenBuffer = struct {
    /// Parallel SoA token columns (`<= MAX_TOML_TOKENS`).
    tokens: std.MultiArrayList(TomlToken) = .empty,
    /// Contiguous `#` comment and newline trivia pieces.
    trivia: std.ArrayListUnmanaged(TomlTriviaPiece) = .empty,

    /// Releases `tokens` and `trivia` backing storage.
    pub fn deinit(self: *TomlTokenBuffer, allocator: std.mem.Allocator) void {
        self.tokens.deinit(allocator);
        self.trivia.deinit(allocator);
        self.* = .{};
    }
};

/// Contiguous 1-byte TOML CST node kind (`0..8`).
pub const TomlCstKind = enum(u8) {
    /// Root TOML document node (`0`).
    document = 0,
    /// Standard `[table.path]` header (`1`).
    table_header = 1,
    /// Array-of-tables `[[array.path]]` header (`2`).
    array_table_header = 2,
    /// `key = value` assignment entry (`3`).
    key_value = 3,
    /// Multi-segment `a.b.c` dotted key (`4`).
    dotted_key = 4,
    /// Single-line `{ k = v, … }` inline table (`5`).
    inline_table = 5,
    /// `[ elem, … ]` array literal (`6`).
    array = 6,
    /// String, integer, float, boolean, or datetime scalar (`7`).
    scalar = 7,
    /// Malformed subtree recovered at newline/delimiter (`8`).
    invalid_subtree = 8,
};

/// 1-byte packed flags on each `TomlCstNode`.
pub const TomlCstFlags = packed struct(u8) {
    /// `true` if a syntax error occurred inside this subtree.
    has_error: bool = false,
    /// `true` if an array literal ended with a trailing `,` before `]`.
    has_trailing_comma: bool = false,
    /// `true` if an adjacent `#` comment carries a `CVE-`/`GHSA-`/`CXSEC-` marker.
    has_cve_advisory: bool = false,
    /// `true` when `key_value` resides inside `{ … }` inline braces.
    is_inline_table_entry: bool = false,
    /// Reserved zero bits (`0`).
    reserved: u4 = 0,
};

/// Exact 16-byte (`128`-bit, `0` padding) pre-order TOML CST node stored in SoA `TomlCstArena`.
pub const TomlCstNode = extern struct {
    /// CST construct discriminant.
    kind: TomlCstKind = .document,
    /// Packed node flags.
    flags: TomlCstFlags = .{},
    /// 0-based UTF-8 column of `=` on `key_value` rows (`0` on non-`key_value` nodes).
    eq_align_col: u16 = 0,
    /// Inclusive starting token index inside `TomlTokenBuffer.tokens`.
    first_token: u32 = 0,
    /// Inclusive ending token index inside `TomlTokenBuffer.tokens`.
    last_token: u32 = 0,
    /// Total node count in this pre-order CST subtree (`>= 1`).
    subtree_size: u32 = 1,
};

/// Flat Structure-of-Arrays (`SoA`) lossless TOML CST arena and `TomlSpanAnchor` table.
pub const TomlCstArena = struct {
    /// Pre-order SoA CST nodes.
    nodes: std.MultiArrayList(TomlCstNode) = .empty,
    /// Absolute-offset `24B` `TomlSpanAnchor` records indexed by `anchor_id`.
    anchors: std.ArrayListUnmanaged(TomlSpanAnchor) = .empty,

    /// Releases `nodes` and `anchors` storage.
    pub fn deinit(self: *TomlCstArena, allocator: std.mem.Allocator) void {
        self.nodes.deinit(allocator);
        self.anchors.deinit(allocator);
        self.* = .{};
    }
};

/// Lossless parsed view over `corex.toml`, `corex.lock`, or `.cx` `---` script frontmatter.
pub const TomlDocumentView = struct {
    /// Source file handle in `VfsSourceMap`.
    file_id: FileId,
    /// Full underlying file buffer (`corex.toml` or complete `.cx` script).
    full_file_bytes: []const u8,
    /// Interior TOML slice (`full_file_bytes[base_byte_offset .. fm_end]` for scripts).
    toml_slice: []const u8,
    /// Byte offset of `toml_slice[0]` inside `full_file_bytes` (`0` for standalone `.toml`/`.lock`).
    base_byte_offset: u32 = 0,
    /// 0-based line offset of `toml_slice[0]` inside `full_file_bytes`.
    base_line_offset: u32 = 0,
    /// `true` when parsed from a `.cx` `---` script frontmatter block.
    is_script_frontmatter: bool = false,
    /// `true` if any lexical or syntactic error occurred while parsing `toml_slice`.
    has_syntax_errors: bool = false,
    /// Byte offset inside `full_file_bytes` immediately past the last entry of `[dependencies]` (`0` when absent).
    deps_section_insert_byte: u32 = 0,
    /// Dominant `=` alignment column inside `[dependencies]` (`0` when absent).
    deps_section_eq_col: u16 = 0,
    /// SoA token and `#` trivia buffer.
    tokens: TomlTokenBuffer = .{},
    /// SoA CST node and `TomlSpanAnchor` arena.
    cst: TomlCstArena = .{},

    /// Releases `tokens` and `cst` buffers owned by `self`.
    pub fn deinit(self: *TomlDocumentView, allocator: std.mem.Allocator) void {
        self.tokens.deinit(allocator);
        self.cst.deinit(allocator);
        self.* = undefined;
    }
};

// ------------ Manifest, Workspace & Lockfile Types ------------

/// Dependency table category inside `corex.toml`.
pub const DepKind = enum(u8) {
    /// Standard `[dependencies]` propagated transitively (`0`).
    normal = 0,
    /// Test/benchmark-only `[dev-dependencies]` (`1`).
    dev = 1,
    /// Pre-build codegen `[build-dependencies]` (`2`).
    build = 2,
};

/// Git reference selector for `git = "…"` dependencies.
pub const GitRevKind = enum(u8) {
    /// Default remote `HEAD` branch (`0`).
    default_head = 0,
    /// Explicit Git tag (`tag = "v1.2.0"`, `1`).
    tag = 1,
    /// Explicit Git branch (`branch = "main"`, `2`).
    branch = 2,
    /// Exact commit SHA (`rev = "<hex>"`, `3`).
    rev = 3,
};

/// Source origin specification for a manifest dependency or `[patch]` entry.
pub const DepSourceSpec = union(enum) {
    /// Sparse HTTP registry dependency constrained by `VersionReq`.
    registry: VersionReq,
    /// Direct Git / GitHub repository dependency.
    git: struct {
        /// Repository URL (`https://…`, `git+https://…`, `git+file://…`).
        url: StringId,
        /// Selector kind (`default_head`, `tag`, `branch`, or `rev`).
        rev_kind: GitRevKind = .default_head,
        /// Tag, branch, or commit SHA value (`.empty` when `.default_head`).
        rev_value: StringId = .empty,
    },
    /// Workspace-relative or local filesystem path dependency.
    path: struct {
        /// Normalized relative POSIX path (`../proto`).
        rel_path: StringId,
        /// Optional SemVer requirement for publish verification.
        version_req: ?VersionReq = null,
    },
    /// Inherited from `[workspace.dependencies]` (`workspace = true`).
    workspace_inherit: struct {
        /// `true` when member inherits base spec from `[workspace.dependencies]`.
        is_inherited: bool = true,
    },
};

/// Normalized dependency edge parsed from `[dependencies]`, `[dev-dependencies]`, or `[build-dependencies]`.
pub const DependencySpec = struct {
    /// Local manifest key in strict `kebab-case` (e.g., `"http-v1"` or `"serde-json"`).
    alias_kebab: StringId,
    /// Bijective `.cx` root module identifier in `snake_case` (e.g., `"http_v1"` or `"serde_json"`).
    module_snake: StringId,
    /// Upstream canonical `kebab-case` package name (`package = "…"`, defaults to `alias_kebab`).
    package_kebab: StringId,
    /// Table section (`normal`, `dev`, or `build`).
    kind: DepKind = .normal,
    /// Backing registry, Git, path, or workspace-inherited source.
    source: DepSourceSpec,
    /// `true` unless `default-features = false` was specified.
    has_default_features: bool = true,
    /// `true` when `optional = true` was specified.
    is_optional: bool = false,
    /// Sorted deduplicated additive feature names.
    features: []const StringId = &.{},
    /// Validated CoreX `@cfg` target expression (`.empty` when unconditional).
    target_cfg: StringId = .empty,
    /// Explicit per-dependency `allow_caps` capability ceiling (`null` inherits `[security]`).
    allow_caps: ?EffectCapabilityMask = null,
    /// Explicit per-dependency `deny_caps` capability blockmask.
    deny_caps: EffectCapabilityMask = .EMPTY,
    /// `true` if `"comptime_io"` was explicitly listed in `allow_caps`.
    has_comptime_io_cap: bool = false,
    /// Index into `Manifest.anchors` (`0xFFFF_FFFF` when synthetic).
    anchor_id: u32 = std.math.maxInt(u32),
    /// Source byte span of this dependency declaration for `E0011`/`E0012`/`E0324` diagnostics.
    decl_span: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 },
};

/// Version exclusion rule inside `[resolution].exclude` (`DR-11` §1.3, `DR-16` §1.3).
pub const ExcludeRule = struct {
    /// Excluded `kebab-case` package name.
    package_kebab: StringId,
    /// Version interval or exact pin banned from resolution.
    req: VersionReq,
    /// `true` when an adjacent `#` comment cites `CVE-`, `GHSA-`, or `CXSEC-`.
    has_cve_advisory: bool = false,
    /// Index into `Manifest.anchors` (`form = 4`).
    anchor_id: u32 = std.math.maxInt(u32),
    /// Source span of the string element inside `exclude = […]`.
    span: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 },
};

/// Transitive dependency source override inside `[patch.<scope>]`.
pub const PatchSpec = struct {
    /// Patch scope key (`"default"`, `"registry"`, `"crates-io"`, or custom URL).
    scope: StringId,
    /// Target `kebab-case` package name being overridden.
    package_kebab: StringId,
    /// Replacement `.path` or `.git` source (`E0013` on bare registry versions).
    replacement: DepSourceSpec,
    /// Index into `Manifest.anchors`.
    anchor_id: u32 = std.math.maxInt(u32),
    /// Source span of the patch entry.
    span: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 },
};

/// Default first-lock dependency policy under `[security].default_dep_policy`.
pub const DefaultDepPolicy = enum(u8) {
    /// Trust capabilities on initial lock and block silent escalations on upgrade (`0`).
    trust_on_first_lock = 0,
    /// Require explicit `allow_caps` for any non-pure capability (`1`).
    zero_trust = 1,
    /// Permit all `LOCKFILE_CAP_BITS` unless blocked by `deny_caps` (`2`).
    allow_all = 2,
};

/// Capability enforcement granularity under `[security].enforcement_scope`.
pub const EnforcementScope = enum(u8) {
    /// Audit all exported `pub` APIs plus inactive `@cfg` branches (`0`, default).
    surface = 0,
    /// Audit functions reachable from active binary/test entrypoints (`1`).
    reachable = 1,
};

/// Per-package capability override declared in `[security.package.<name>]`.
pub const PackageSecurityOverride = struct {
    /// Target `kebab-case` package name.
    package_kebab: StringId,
    /// Explicit capability allowlist (`null` when unspecified).
    allow_caps: ?EffectCapabilityMask = null,
    /// Explicit capability denylist.
    deny_caps: EffectCapabilityMask = .EMPTY,
};

/// Declarative supply-chain capability policy parsed from `[security]` (`DR-17` §4.2).
pub const SecurityPolicy = struct {
    /// High-level policy preset (`trust_on_first_lock`, `zero_trust`, or `allow_all`).
    default_dep_policy: DefaultDepPolicy = .trust_on_first_lock,
    /// Default capability ceiling for dependencies lacking explicit `allow_caps`.
    default_allow_caps: ?EffectCapabilityMask = null,
    /// Workspace-wide forbidden capability bits across third-party dependencies.
    deny_caps: EffectCapabilityMask = .EMPTY,
    /// Whether `E0324` inspects `surface` exports or `reachable` call graphs.
    enforcement_scope: EnforcementScope = .surface,
    /// Whether `W0330` warns on unexported dead `ffi` / `unsafe_op` capabilities (`warn_ambient_dead_caps`).
    is_warn_ambient_dead_caps: bool = true,
    /// Optional `[security.dev]` `default_allow_caps` override for `[dev-dependencies]`.
    dev_default_allow_caps: ?EffectCapabilityMask = null,
    /// Optional `[security.dev]` `deny_caps` mask.
    dev_deny_caps: EffectCapabilityMask = .EMPTY,
    /// Sorted per-package overrides from `[security.package.<name>]`.
    package_overrides: []const PackageSecurityOverride = &.{},
};

/// Publishing restriction parsed from `[package].publish`.
pub const PublishPolicy = union(enum) {
    /// Boolean allow/forbid (`publish = true` / `publish = false`).
    is_allowed: bool,
    /// Explicit allowlist of registry names (`publish = ["internal-reg"]`).
    registries: []const StringId,
};

/// `[package]` metadata table inside `corex.toml`.
pub const PackageMeta = struct {
    /// Canonical `kebab-case` package name.
    name_kebab: StringId,
    /// Bijective `snake_case` `.cx` module identifier.
    module_snake: StringId,
    /// Package SemVer 2.0.0 version.
    version: SemVer,
    /// Minimum CoreX toolchain version requirement (`corex = "1.0"`, `.empty` when omitted).
    corex_req: StringId = .empty,
    /// Language edition (`"2026"` by default).
    edition: StringId,
    /// Human-readable package summary.
    description: StringId = .empty,
    /// SPDX license expression.
    license: StringId = .empty,
    /// Upstream source repository URL.
    repository: StringId = .empty,
    /// Registry publication policy (`publish = true` default).
    publish: PublishPolicy = .{ .is_allowed = true },
    /// Explicit root `.cx` source path override (`root_module = "src/lib.cx"`).
    root_module: StringId = .empty,
    /// Exclusive native C library linkage key (`links = "z"` -> `E0011` on collision).
    links: StringId = .empty,
};

/// Explicit `[lib]` target configuration.
pub const LibTarget = struct {
    /// Library module identifier in `snake_case`.
    name_snake: StringId,
    /// Relative POSIX path to library root `.cx` file (`"src/root.cx"` / `"src/lib.cx"`).
    path: StringId,
};

/// Explicit `[[bin]]` executable target configuration.
pub const BinTarget = struct {
    /// Executable binary name in `kebab-case`.
    name_kebab: StringId,
    /// Relative POSIX path to binary entry `.cx` file (`"src/main.cx"`).
    path: StringId,
};

/// Single additive feature entry under `[features]`.
pub const FeatureDecl = struct {
    /// Feature identifier (`"default"`, `"tls"`, etc.).
    name: StringId,
    /// Sorted deduplicated activations (`"dep:foo"`, `"foo/feat"`, `"foo?/feat"`, or local feature).
    activations: []const StringId = &.{},
};

/// Shared `[workspace.package]` metadata inheritable by workspace members via `{ workspace = true }`.
pub const WorkspacePackageMeta = struct {
    /// Optional shared SemVer 2.0.0 version.
    version: ?SemVer = null,
    /// Optional shared minimum CoreX toolchain version requirement (`corex = "…"`).
    corex_req: ?StringId = null,
    /// Optional shared language edition (`"2026"`).
    edition: ?StringId = null,
    /// Optional shared human-readable description.
    description: ?StringId = null,
    /// Optional shared SPDX license expression.
    license: ?StringId = null,
    /// Optional shared source repository URL.
    repository: ?StringId = null,
    /// Optional shared registry publication policy.
    publish: ?PublishPolicy = null,
};

/// Single non-backtracking 64-state bit-parallel Thompson NFA compiled from one brace-expanded glob branch.
pub const SubNfa64 = struct {
    /// Number of byte-consuming states (`0 .. num_states - 1`; accept state is `num_states <= 63`).
    num_states: u8 = 0,
    /// Bitmask `(1 << num_states) - 1` of byte-consuming state indices.
    valid_state_mask: u64 = 0,
    /// Precomputed epsilon closure of state `0`.
    initial_mask: u64 = 0,
    /// Single-bit mask `1 << num_states` representing the accepting state.
    accept_bit: u64 = 0,
    /// States `s` that stay in `s` on a matching byte (`*` and `**`).
    self_loop_mask: u64 = 0,
    /// States `s` that advance to `s + 1` on a matching byte (literals, `?`, `[…]`, `/` in `**/`).
    advance_mask: u64 = 0,
    /// Per-state 256-bit ASCII/UTF-8 byte class (`len == num_states`).
    char_classes: []const [4]u64 = &.{},
    /// Precomputed transitive epsilon closure for every state `0 .. num_states` (`len == num_states + 1`).
    eps_closure: []const u64 = &.{},

    /// Returns `true` if `state_idx` accepts `byte` in $O(1)$ time.
    pub inline fn stateMatchesByte(self: SubNfa64, state_idx: u6, byte: u8) bool {
        const word = self.char_classes[state_idx][byte >> 6];
        return (word & (@as(u64, 1) << @intCast(byte & 63))) != 0;
    }

    /// Evaluates whether `rel_path` matches this NFA in $O(|\text{path}|)$ time with zero allocations.
    pub fn matchesNormalizedPath(self: SubNfa64, rel_path: []const u8) bool {
        var active = self.initial_mask;
        for (rel_path) |raw_byte| {
            if (active == 0) return false;
            const norm_byte: u8 = if (raw_byte == '\\') '/' else raw_byte;
            var matched: u64 = 0;
            var iter_active = active & self.valid_state_mask;
            while (iter_active != 0) {
                const state_idx: u6 = @intCast(@ctz(iter_active));
                iter_active &= iter_active - 1;
                if (self.stateMatchesByte(state_idx, norm_byte)) {
                    matched |= (@as(u64, 1) << state_idx);
                }
            }
            const raw_next = (matched & self.self_loop_mask) | ((matched & self.advance_mask) << 1);
            var next_active: u64 = 0;
            var iter_next = raw_next;
            while (iter_next != 0) {
                const next_idx: u6 = @intCast(@ctz(iter_next));
                iter_next &= iter_next - 1;
                next_active |= self.eps_closure[next_idx];
            }
            active = next_active;
        }
        return (active & self.accept_bit) != 0;
    }
};

/// Deterministic non-backtracking path-glob matcher supporting up to 16 `{a,b}` 64-state Thompson NFAs.
pub const CompiledGlob64 = struct {
    /// Original interned glob pattern text for deterministic matrix fingerprinting.
    pattern_id: StringId = .empty,
    /// Compiled brace-expanded sub-automata (`1..=16`).
    sub_nfas: []const SubNfa64 = &.{},

    /// Returns `true` if `raw_rel_path` matches any brace-expanded NFA in $O(|\text{path}|)$ time (`0` allocs).
    pub fn matchesPath(self: CompiledGlob64, raw_rel_path: []const u8) bool {
        var path_view = raw_rel_path;
        while (std.mem.startsWith(u8, path_view, "./") or std.mem.startsWith(u8, path_view, ".\\")) {
            path_view = path_view[2..];
        }
        for (self.sub_nfas) |sub| {
            if (sub.matchesNormalizedPath(path_view)) return true;
        }
        return false;
    }
};

/// Per-glob lint disable override parsed from `[[lint.overrides]]` or `[[workspace.lint.overrides]]`.
pub const LintOverride = struct {
    /// Non-empty inclusion globs matched against workspace/package-relative POSIX paths.
    files: []const CompiledGlob64 = &.{},
    /// Optional exclusion globs carving paths out of `files`.
    exclude_files: []const CompiledGlob64 = &.{},
    /// Additional lint rules disabled on matching files.
    disable_mask: RuleMask64 = 0,
};

/// Validated `[lint]` or `[workspace.lint]` configuration (`DR-25` §3.1, `ADR-25B`).
pub const LintConfig = struct {
    /// When `true` (default), workspace members inherit `[workspace.lint]` before applying local overrides.
    inherit: bool = true,
    /// `true` if `inherit` was explicitly written in TOML.
    has_explicit_inherit: bool = false,
    /// Package-wide disabled rule bitmask (`0` = all 44 rules enabled).
    disable_mask: RuleMask64 = 0,
    /// Paths excluded from lint emission completely.
    exclude: []const CompiledGlob64 = &.{},
    /// Bounded semantic thresholds hashed separately at `QueryStage.lint_semantic_settings`.
    settings: LintSettings = .{},
    /// Bitmask of `[lint.settings]` keys explicitly set in this table (`bits 0..5`).
    explicit_settings_mask: u8 = 0,
    /// Ordered `[[lint.overrides]]` blocks accumulating path-scoped `disable_mask` bits.
    overrides: []const LintOverride = &.{},

    /// Returns `true` if `rel_path` matches any pattern in `self.exclude`.
    pub fn isFileExcluded(self: LintConfig, rel_path: []const u8) bool {
        for (self.exclude) |glob_item| {
            if (glob_item.matchesPath(rel_path)) return true;
        }
        return false;
    }

    /// Resolves the effective `RuleMask64` of disabled rules for `rel_path` + `cli_filter` (`DR-25` §3.1).
    pub fn resolveFileDisabledMask(
        self: LintConfig,
        rel_path: []const u8,
        cli_filter: CliLintFilter,
    ) RuleMask64 {
        if (self.isFileExcluded(rel_path)) return diagnostic.ALL_RULES_MASK;
        var disabled = self.disable_mask;
        for (self.overrides) |override_entry| {
            var is_included = false;
            for (override_entry.files) |inc_glob| {
                if (inc_glob.matchesPath(rel_path)) {
                    is_included = true;
                    break;
                }
            }
            if (!is_included) continue;
            var is_excluded = false;
            for (override_entry.exclude_files) |exc_glob| {
                if (exc_glob.matchesPath(rel_path)) {
                    is_excluded = true;
                    break;
                }
            }
            if (!is_excluded) {
                disabled |= override_entry.disable_mask;
            }
        }
        return cli_filter.applyToDisabledMask(disabled);
    }

    /// Computes a 64-bit `Wyhash` digest over `disable_mask`, `exclude`, and `overrides` (excluding `settings`).
    pub fn computeDisabledMatrixFingerprint(
        self: LintConfig,
        interner: *const StringInterner,
    ) u64 {
        var hasher = std.hash.Wyhash.init(0xA5A5_5A5A_C3C3_3C3C);
        const mask_le = std.mem.nativeToLittle(u64, self.disable_mask);
        hasher.update(std.mem.asBytes(&mask_le));

        const excl_len_le = std.mem.nativeToLittle(u32, @intCast(self.exclude.len));
        hasher.update(std.mem.asBytes(&excl_len_le));
        for (self.exclude) |glob_item| {
            const pat_str = interner.get(glob_item.pattern_id);
            const pat_len_le = std.mem.nativeToLittle(u32, @intCast(pat_str.len));
            hasher.update(std.mem.asBytes(&pat_len_le));
            hasher.update(pat_str);
        }

        const ov_len_le = std.mem.nativeToLittle(u32, @intCast(self.overrides.len));
        hasher.update(std.mem.asBytes(&ov_len_le));
        for (self.overrides) |ov_item| {
            const ov_mask_le = std.mem.nativeToLittle(u64, ov_item.disable_mask);
            hasher.update(std.mem.asBytes(&ov_mask_le));
            const files_len_le = std.mem.nativeToLittle(u32, @intCast(ov_item.files.len));
            hasher.update(std.mem.asBytes(&files_len_le));
            for (ov_item.files) |inc_glob| {
                const pat_str = interner.get(inc_glob.pattern_id);
                const pat_len_le = std.mem.nativeToLittle(u32, @intCast(pat_str.len));
                hasher.update(std.mem.asBytes(&pat_len_le));
                hasher.update(pat_str);
            }
            const ex_files_len_le = std.mem.nativeToLittle(u32, @intCast(ov_item.exclude_files.len));
            hasher.update(std.mem.asBytes(&ex_files_len_le));
            for (ov_item.exclude_files) |exc_glob| {
                const pat_str = interner.get(exc_glob.pattern_id);
                const pat_len_le = std.mem.nativeToLittle(u32, @intCast(pat_str.len));
                hasher.update(std.mem.asBytes(&pat_len_le));
                hasher.update(pat_str);
            }
        }
        return hasher.final();
    }
};

/// Validated `[fmt]` or `[workspace.fmt]` guardrails (`DR-25` §3.1; style knobs rejected with `E0018`).
pub const FmtConfig = struct {
    /// When `true` (default), workspace members inherit `[workspace.fmt]`.
    inherit: bool = true,
    /// `true` if `inherit` was explicitly written in TOML.
    has_explicit_inherit: bool = false,
    /// Paths skipped by `corex fmt` directory traversal.
    exclude: []const CompiledGlob64 = &.{},
    /// When `false` (default), `@generated` / `DO NOT EDIT` files are skipped by `corex fmt`.
    check_generated: bool = false,
    /// `true` if `check-generated` was explicitly written in TOML.
    has_explicit_check_generated: bool = false,

    /// Returns `true` if `rel_path` matches any pattern in `self.exclude`.
    pub fn isFileExcluded(self: FmtConfig, rel_path: []const u8) bool {
        for (self.exclude) |glob_item| {
            if (glob_item.matchesPath(rel_path)) return true;
        }
        return false;
    }
};

/// Parameter-name inlay hint verbosity mode in `[lsp].inlay-hints-parameter-names` (`DR-25` §3.1).
pub const LspParamHintsMode = enum(u8) {
    /// Disable parameter-name inlay hints (`"none"`).
    none = 0,
    /// Show parameter-name inlay hints unless the argument identifier matches (`"non-matching"`, default).
    non_matching = 1,
    /// Show parameter-name inlay hints on every positional argument (`"all"`).
    all = 2,
};

/// Effect/capability inlay hint verbosity mode in `[lsp].inlay-hints-effects` (`DR-25` §3.1).
pub const LspEffectsHintsMode = enum(u8) {
    /// Disable effect/capability inlay hints (`"none"`).
    none = 0,
    /// Show effect hints only on contract boundaries (`"contracts-only"`, default).
    contracts_only = 1,
    /// Show inferred effect hints on all functions (`"all"`).
    all = 2,
};

/// Validated `[lsp]` or `[workspace.lsp]` presentation settings (`DR-25` §3.1, Ruling 2).
pub const LspConfig = struct {
    /// When `true` (default), workspace members inherit `[workspace.lsp]`.
    inherit: bool = true,
    /// `true` if `inherit` was explicitly written in TOML.
    has_explicit_inherit: bool = false,
    /// Enables inferred `: Type` inlay hints on `let` / `var` bindings (`inlay-hints-types`).
    inlay_hints_types: bool = true,
    /// Parameter-name inlay hint verbosity (`inlay-hints-parameter-names`).
    inlay_hints_parameter_names: LspParamHintsMode = .non_matching,
    /// Enables implicit MVS projection inlay hints (`inlay-hints-mvs-modes`).
    inlay_hints_mvs_modes: bool = true,
    /// Effect/capability inlay hint verbosity (`inlay-hints-effects`).
    inlay_hints_effects: LspEffectsHintsMode = .contracts_only,
    /// Enables `▸ Run test` / `▸ Run bench` CodeLens items (`code-lens-test-bench`).
    code_lens_test_bench: bool = true,
    /// Maximum completion candidates returned per `textDocument/completion` response (`16..=256`, default `64`).
    max_completion_items: u16 = 64,
    /// Bitmask of `[lsp]` keys explicitly set in this table (`bits 0..5`).
    explicit_fields_mask: u8 = 0,
};

/// Monorepo `[workspace]` configuration parsed from a root `corex.toml`.
pub const WorkspaceConfig = struct {
    /// Member directory patterns (`members = ["crates/*", "tools/cli"]`).
    members: []const StringId = &.{},
    /// Default build target member patterns (`default-members`).
    default_members: []const StringId = &.{},
    /// Excluded directory paths (`exclude = ["vendor"]`).
    exclude: []const StringId = &.{},
    /// Optional `[workspace.package]` metadata inheritable via `{ workspace = true }`.
    package: ?WorkspacePackageMeta = null,
    /// Shared `[workspace.dependencies]` inheritable via `workspace = true`.
    dependencies: []const DependencySpec = &.{},
    /// Optional `[workspace.security]` policy inherited when root `[security]` is absent.
    security: ?SecurityPolicy = null,
    /// Optional `[workspace.resolution]` `exclude` rules.
    excludes: []const ExcludeRule = &.{},
    /// Optional `[workspace.patch.*]` overrides.
    patches: []const PatchSpec = &.{},
    /// Shared `[workspace.lint]` policy inherited when member `lint.inherit == true`.
    lint: LintConfig = .{},
    /// Shared `[workspace.fmt]` policy inherited when member `fmt.inherit == true`.
    fmt: FmtConfig = .{},
    /// Shared `[workspace.lsp]` policy inherited when member `lsp.inherit == true`.
    lsp: LspConfig = .{},
};

/// Complete validated representation of a `corex.toml` manifest or `.cx` script frontmatter.
pub const Manifest = struct {
    /// Source `FileId` of this manifest.
    file_id: FileId,
    /// `true` when parsed from a single-file `.cx` script frontmatter block.
    is_script: bool = false,
    /// `[package]` metadata (`null` for virtual `[workspace]` manifests or bare script frontmatter).
    package: ?PackageMeta = null,
    /// Optional `[lib]` target descriptor.
    lib_target: ?LibTarget = null,
    /// Optional `[[bin]]` target descriptors.
    bin_targets: []const BinTarget = &.{},
    /// Canonically sorted `[features]` declarations.
    features: []const FeatureDecl = &.{},
    /// Canonically sorted `[dependencies]`, `[dev-dependencies]`, and `[build-dependencies]`.
    dependencies: []const DependencySpec = &.{},
    /// Canonically sorted `[resolution].exclude` bans.
    excludes: []const ExcludeRule = &.{},
    /// Canonically sorted `[patch.*]` overrides.
    patches: []const PatchSpec = &.{},
    /// Effective `[security]` capability policy.
    security: SecurityPolicy = .{},
    /// Effective `[lint]` configuration (excluded from `root_manifest_blake3` per `DR-25` §3.1).
    lint: LintConfig = .{},
    /// Effective `[fmt]` configuration (excluded from `root_manifest_blake3` per `DR-25` §3.1).
    fmt: FmtConfig = .{},
    /// Effective `[lsp]` configuration (excluded from `root_manifest_blake3` per `DR-25` §3.1).
    lsp: LspConfig = .{},
    /// Optional `[workspace]` table.
    workspace: ?WorkspaceConfig = null,
    /// Cloned `24B` `TomlSpanAnchor` array indexed by `anchor_id`.
    anchors: []const TomlSpanAnchor = &.{},
    /// Whitespace- and comment-invariant 256-bit `BLAKE3` digest of this manifest.
    root_manifest_blake3: [32]u8 = @splat(0),
};

/// Candidate workspace member directory discovered directly or via `/*` glob expansion.
const MemberDirCandidate = struct {
    /// Normalized workspace-relative directory path.
    rel_dir: []const u8,
    /// `true` when listed explicitly in `[workspace].members` rather than expanded from `/*`.
    is_explicit: bool,
};

/// Resolved member package inside a `WorkspaceManifestBundle`.
pub const WorkspaceMember = struct {
    /// Relative POSIX directory path from `workspace_root_dir` (`"."` for root package).
    rel_dir: []const u8,
    /// Normalized host directory path containing `corex.toml`.
    abs_dir: []const u8,
    /// Normalized path to `<abs_dir>/corex.toml` (or `.cx` script path).
    manifest_path: []const u8,
    /// Validated `Manifest` (with `workspace = true` inheritance resolved).
    manifest: Manifest,
    /// `true` when selected by default workspace builds (`default_members`).
    is_default_member: bool = true,
};

/// Unified workspace or single-package manifest bundle consumed by `pkg_resolver.resolveProjectGraph`.
pub const WorkspaceManifestBundle = struct {
    /// Arena owning all strings, slices, anchors, and member `Manifest` structures.
    arena: BumpArena,
    /// Root directory of the workspace (or parent directory of a `.cx` script).
    workspace_root_dir: []const u8,
    /// Path to the root `corex.toml` (or `.cx` script).
    root_manifest_path: []const u8,
    /// Parsed root `Manifest`.
    root_manifest: Manifest,
    /// Sorted array of resolved `WorkspaceMember` packages (`rel_dir` ASCII ascending).
    members: []const WorkspaceMember = &.{},
    /// Active target member index when invoked inside a member subdirectory (`null` for virtual root).
    primary_member_index: ?u32 = null,
    /// `true` when backed by a single-file `.cx` script rather than `corex.toml`.
    is_script: bool = false,
    /// Combined normalized 256-bit `BLAKE3` digest written to `corex.lock` `root_manifest_blake3`.
    root_manifest_blake3: [32]u8 = @splat(0),

    /// Releases `arena` memory owned by this bundle.
    pub fn deinit(self: *WorkspaceManifestBundle) void {
        self.arena.deinit();
        self.* = undefined;
    }
};

/// Paired validated `Manifest` and lossless `TomlDocumentView` returned by manifest parsers.
pub const ParsedManifestResult = struct {
    /// Lowered and validated manifest configuration.
    manifest: Manifest,
    /// Lossless CST/token view backing span anchors and surgical TOML edits.
    doc: TomlDocumentView,
};

/// Parsed inline `use "<spec>" as <snake_alias>;` specifier (`DR-11` §1.2).
pub const InlineUseSpec = struct {
    /// Validated `snake_case` module alias bound in `.cx` source.
    alias_snake: StringId,
    /// Bijective `kebab-case` alias key for auto-hoisting into `corex.toml`.
    alias_kebab: StringId,
    /// Upstream `kebab-case` package name derived from `<spec>` (or `alias_kebab` for paths).
    package_kebab: StringId,
    /// Parsed registry, Git/GitHub, or relative path dependency source.
    source: DepSourceSpec,
};

/// Result of blank-in-place `.cx` `#!` + `---` script frontmatter extraction (`DR-11` §1.2).
pub const ScriptFrontmatterExtract = struct {
    /// `true` if a top-of-file `--- … ---` TOML frontmatter block was present.
    has_frontmatter: bool,
    /// NUL-terminated `.cx` source of identical length with prefix non-`\r`/`\n` bytes set to `' '` (`0x20`).
    blanked_cx_source: [:0]u8,
    /// Interior TOML slice `raw_source[fm_start_byte .. fm_end_byte]` (`""` when `!has_frontmatter`).
    toml_slice: []const u8,
    /// Exact byte offset where `toml_slice` starts in `raw_source` (for `TomlSpanAnchor` rebasing).
    fm_start_byte: u32,
    /// 0-based line index where `toml_slice` starts in `raw_source`.
    fm_start_line: u32,
    /// Exclusive byte offset immediately past the closing `---` fence line (`0` when no `#!` / `---`).
    prefix_end_byte: u32,
};

/// Single resolved `[[package]]` record in canonical `corex.lock` v1 (`DR-11` §1.3, `DR-17` §4.2).
pub const LockPackage = struct {
    /// Strict `kebab-case` package name.
    name: StringId,
    /// Exact resolved `SemVer` 2.0.0 version.
    version: SemVer,
    /// Canonical source URI (`"registry+…"`, `"git+…"`, `"path+file://…"`, or `"root"`).
    source: StringId,
    /// Optional `"b3:<64-hex>"` archive digest (`null` for `path+file://` / local packages).
    checksum: ?[32]u8 = null,
    /// Mandatory `"b3:<64-hex>"` `.cxtree` directory Merkle digest.
    tree_hash: [32]u8,
    /// Optional `"ed25519:<128-hex>"` 64-byte publisher signature (`null` for local/unverified sources).
    signature: ?[64]u8 = null,
    /// Optional RFC 6962 transparency-log leaf index (`0` is valid leaf `0`; `null` omits key).
    tlog_index: ?u64 = null,
    /// Authorized/surface `LOCKFILE_CAP_BITS` serialized as sorted `"unsafe_op"`-canonical strings.
    max_caps: EffectCapabilityMask = .EMPTY,
    /// Unconditional ambient capabilities (omitted in `corex.lock` when `.isEmpty()`).
    ambient_caps: EffectCapabilityMask = .EMPTY,
    /// Mandatory `"b3:<64-hex>"` `.cxi` public-interface summary digest.
    cxi_blake3: [32]u8,
    /// Optional exclusive native C library linkage key (omitted when `.empty`).
    links: StringId = .empty,
    /// Sorted ASCII deduplicated enabled feature names.
    features: []const StringId = &.{},
    /// Sorted ASCII deduplicated dependency references (`"<name> <version> (<source>)"`).
    dependencies: []const StringId = &.{},
};

/// Validated `corex.lock` v1 document (`DR-11` §1.3, `DR-17` §4.2).
pub const Lockfile = struct {
    /// Schema version (`1`).
    version: u32 = LOCKFILE_VERSION,
    /// Normalized 256-bit `BLAKE3` digest of the workspace/root manifest (`"b3:<64-hex>"`).
    root_manifest_blake3: [32]u8,
    /// Strictly sorted `(name_ascii ASC, SemVer.compare ASC, source_ascii ASC)` package array.
    packages: []const LockPackage = &.{},
};

// --------------------------------------- CONSTS ----------------------------------------

/// Hard upper bound on `corex.toml`, `.cx` frontmatter, or `corex.lock` input size (`1 MiB`).
pub const MAX_TOML_BYTES: usize = 1024 * 1024;
/// Hard upper bound on TOML syntactic tokens per document (`65,536`).
pub const MAX_TOML_TOKENS: u32 = 65_536;
/// Hard upper bound on nested `[…]` arrays and `{…}` inline tables (`16`).
pub const MAX_TOML_DEPTH: u8 = 16;
/// Maximum byte length of a canonical `kebab-case` package name (`64`).
pub const MAX_PKG_NAME_BYTES: usize = 64;
/// Maximum atomic comparators inside a single comma-separated `VersionReq` (`8`).
pub const MAX_VERSION_COMPARATORS: usize = 8;
/// Canonical `corex.lock` schema version (`1`).
pub const LOCKFILE_VERSION: u32 = 1;
/// Default CoreX language edition when `[package].edition` is omitted.
pub const DEFAULT_COREX_EDITION = "2026";
/// Maximum `{a,b}` brace expansion branches permitted in a single glob string (`E0019`).
pub const MAX_GLOB_BRACE_EXPANSIONS: usize = 16;
/// Maximum total NFA states (`0..63`) permitted in a single `SubNfa64` glob branch (`E0019`).
pub const MAX_GLOB_STATES: usize = 64;
/// Inclusive lower bound for `[lsp].max-completion-items` (`E0020`).
pub const LSP_MAX_COMPLETION_ITEMS_MIN: u16 = 16;
/// Inclusive upper bound for `[lsp].max-completion-items` (`E0020`).
pub const LSP_MAX_COMPLETION_ITEMS_MAX: u16 = 256;

/// CoreX-specific standalone tool configuration dotfiles rejected with `E0017` (`DR-25` §3.1, Ruling 2).
pub const FORBIDDEN_STRAY_TOOL_DOTFILES = [_][]const u8{
    ".corex-fmt.toml",
    ".corex-lint.toml",
    ".corex-lsp.toml",
    ".corexfmt.toml",
    ".corexlint.toml",
    "corex-fmt.toml",
    "corex-lint.toml",
    "corex-lsp.toml",
    "corexfmt.toml",
    "corexlint.toml",
};

/// Domain header hashed at the front of `computeNormalizedManifestBlake3`.
const MANIFEST_NORM_DOMAIN = "corex-manifest-norm-v1\x00";

/// $O(1)$ static set of reserved module/namespace names forbidden as `corex.toml` package names (`E0013`).
pub const RESERVED_PKG_NAME_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "Self", {} },
    .{ "core", {} },
    .{ "cx", {} },
    .{ "pkg", {} },
    .{ "self", {} },
    .{ "std", {} },
    .{ "super", {} },
});

/// $O(1)$ static map from canonical manifest capability names to `EffectCapabilityMask` bits (`comptime_io` -> `0`).
pub const MANIFEST_CAPABILITY_MAP = std.StaticStringMap(u16).initComptime(.{
    .{ "alloc", EffectCapabilityMask.ALLOC_BIT },
    .{ "blocking_sync", 1 << 10 },
    .{ "clock", 1 << 8 },
    .{ "comptime_io", 0 },
    .{ "entropy", 1 << 9 },
    .{ "env", 1 << 2 },
    .{ "ffi", 1 << 4 },
    .{ "fs", 1 << 0 },
    .{ "indirect_opaque", EffectCapabilityMask.INDIRECT_OPAQUE_BIT },
    .{ "may_panic", EffectCapabilityMask.MAY_PANIC_BIT },
    .{ "net", 1 << 1 },
    .{ "process", 1 << 3 },
    .{ "unsafe_op", 1 << 5 },
});

/// $O(1)$ static map of runtime capability strings valid inside `corex.lock` `max_caps` / `ambient_caps` (`0x033F`).
const LOCKFILE_CAPABILITY_MAP = std.StaticStringMap(u16).initComptime(.{
    .{ "clock", 1 << 8 },
    .{ "entropy", 1 << 9 },
    .{ "env", 1 << 2 },
    .{ "ffi", 1 << 4 },
    .{ "fs", 1 << 0 },
    .{ "net", 1 << 1 },
    .{ "process", 1 << 3 },
    .{ "unsafe_op", 1 << 5 },
});

/// Canonical ASCII-sorted `LOCKFILE_CAP_BITS` entries serialized into `corex.lock` `max_caps` / `ambient_caps`.
const CANONICAL_LOCKFILE_CAPS = [_]struct {
    /// Canonical capability string (`"unsafe_op"` exclusively for bit 5).
    name: []const u8,
    /// Single bit inside `EffectCapabilityMask`.
    bit: u16,
}{
    .{ .name = "clock", .bit = 1 << 8 },
    .{ .name = "entropy", .bit = 1 << 9 },
    .{ .name = "env", .bit = 1 << 2 },
    .{ .name = "ffi", .bit = 1 << 4 },
    .{ .name = "fs", .bit = 1 << 0 },
    .{ .name = "net", .bit = 1 << 1 },
    .{ .name = "process", .bit = 1 << 3 },
    .{ .name = "unsafe_op", .bit = 1 << 5 },
};

// -------------------------------------- INTERNALS --------------------------------------

// --------------- SemVer & Version Requirements ----------------

/// Parses a non-negative `u32` decimal slice rejecting empty strings and leading zeros (`"01"` -> `null`).
fn parseStrictSemVerUint(digits: []const u8) ?u32 {
    if (digits.len == 0) return null;
    if (digits.len > 1 and digits[0] == '0') return null;
    var accum: u64 = 0;
    for (digits) |ch_byte| {
        if (!std.ascii.isDigit(ch_byte)) return null;
        accum = accum * 10 + (ch_byte - '0');
        if (accum > std.math.maxInt(u32)) return null;
    }
    return @intCast(accum);
}

/// Validates a dot-separated SemVer 2.0.0 pre-release or build suffix.
fn isValidSemVerSuffix(suffix: []const u8, is_prerelease: bool) bool {
    if (suffix.len == 0) return false;
    var part_iter = std.mem.splitScalar(u8, suffix, '.');
    while (part_iter.next()) |ident| {
        if (ident.len == 0) return false;
        var is_all_digits = true;
        for (ident) |ch_byte| {
            if (std.ascii.isDigit(ch_byte)) continue;
            if (std.ascii.isAlphabetic(ch_byte) or ch_byte == '-') {
                is_all_digits = false;
                continue;
            }
            return false;
        }
        if (is_prerelease and is_all_digits and ident.len > 1 and ident[0] == '0') {
            return false;
        }
    }
    return true;
}

/// Parses strict SemVer 2.0.0 (`major.minor.patch[-pre][+build]`).
fn parseSemVerImpl(interner: *StringInterner, raw_text: []const u8) !?SemVer {
    const trimmed = std.mem.trim(u8, raw_text, " \t");
    if (trimmed.len == 0 or trimmed.len != raw_text.len) return null;

    var core_and_pre = trimmed;
    var build_slice: []const u8 = "";
    if (std.mem.indexOfScalar(u8, trimmed, '+')) |plus_idx| {
        core_and_pre = trimmed[0..plus_idx];
        build_slice = trimmed[plus_idx + 1 ..];
        if (!isValidSemVerSuffix(build_slice, false)) return null;
    }

    var core_slice = core_and_pre;
    var pre_slice: []const u8 = "";
    if (std.mem.indexOfScalar(u8, core_and_pre, '-')) |dash_idx| {
        core_slice = core_and_pre[0..dash_idx];
        pre_slice = core_and_pre[dash_idx + 1 ..];
        if (!isValidSemVerSuffix(pre_slice, true)) return null;
    }

    const first_dot = std.mem.indexOfScalar(u8, core_slice, '.') orelse return null;
    const after_first = core_slice[first_dot + 1 ..];
    const second_dot = std.mem.indexOfScalar(u8, after_first, '.') orelse return null;
    if (std.mem.indexOfScalar(u8, after_first[second_dot + 1 ..], '.') != null) return null;

    const major_val = parseStrictSemVerUint(core_slice[0..first_dot]) orelse return null;
    const minor_val = parseStrictSemVerUint(after_first[0..second_dot]) orelse return null;
    const patch_val = parseStrictSemVerUint(after_first[second_dot + 1 ..]) orelse return null;

    return .{
        .major = major_val,
        .minor = minor_val,
        .patch = patch_val,
        .pre = if (pre_slice.len > 0) try interner.intern(pre_slice) else .empty,
        .build = if (build_slice.len > 0) try interner.intern(build_slice) else .empty,
    };
}

/// Returns `true` if every byte in `ident` is an ASCII decimal digit.
fn isAllAsciiDigits(ident: []const u8) bool {
    if (ident.len == 0) return false;
    for (ident) |ch_byte| {
        if (!std.ascii.isDigit(ch_byte)) return false;
    }
    return true;
}

/// Compares two SemVer 2.0.0 pre-release slices (`""` > non-empty; numeric id < alphanumeric id).
fn compareSemVerPreSlices(lhs_pre: []const u8, rhs_pre: []const u8) std.math.Order {
    if (lhs_pre.len == 0 and rhs_pre.len == 0) return .eq;
    if (lhs_pre.len == 0) return .gt;
    if (rhs_pre.len == 0) return .lt;

    var lhs_iter = std.mem.splitScalar(u8, lhs_pre, '.');
    var rhs_iter = std.mem.splitScalar(u8, rhs_pre, '.');
    while (true) {
        const lhs_opt = lhs_iter.next();
        const rhs_opt = rhs_iter.next();
        if (lhs_opt == null and rhs_opt == null) return .eq;
        if (lhs_opt == null) return .lt;
        if (rhs_opt == null) return .gt;

        const lhs_id = lhs_opt.?;
        const rhs_id = rhs_opt.?;
        const is_lhs_num = isAllAsciiDigits(lhs_id);
        const is_rhs_num = isAllAsciiDigits(rhs_id);
        if (is_lhs_num and is_rhs_num) {
            if (lhs_id.len != rhs_id.len) return std.math.order(lhs_id.len, rhs_id.len);
            const num_ord = std.mem.order(u8, lhs_id, rhs_id);
            if (num_ord != .eq) return num_ord;
        } else if (is_lhs_num != is_rhs_num) {
            return if (is_lhs_num) .lt else .gt;
        } else {
            const str_ord = std.mem.order(u8, lhs_id, rhs_id);
            if (str_ord != .eq) return str_ord;
        }
    }
}

/// Decoded partial version tuple (`1`, `1.2`, `1.*`, or full `1.2.3-alpha`) used inside `VersionReq.parse`.
const PartialSemVer = struct {
    /// Major component (`null` only for `"*"`).
    major: ?u32 = null,
    /// Minor component (`null` when omitted or wildcard).
    minor: ?u32 = null,
    /// Patch component (`null` when omitted or wildcard).
    patch: ?u32 = null,
    /// Optional pre-release string handle.
    pre: StringId = .empty,
    /// `true` if `*`, `x`, or `X` appeared in any component.
    has_wildcard: bool = false,
};

/// Parses a partial or wildcard version operand inside a `VersionReq` atom.
fn parsePartialSemVer(interner: *StringInterner, raw_part: []const u8) !?PartialSemVer {
    const trimmed = std.mem.trim(u8, raw_part, " \t");
    if (trimmed.len == 0) return null;
    if (std.mem.eql(u8, trimmed, "*") or std.mem.eql(u8, trimmed, "x") or std.mem.eql(u8, trimmed, "X")) {
        return .{ .has_wildcard = true };
    }

    var base_slice = trimmed;
    if (std.mem.indexOfScalar(u8, base_slice, '+')) |plus_idx| {
        if (!isValidSemVerSuffix(base_slice[plus_idx + 1 ..], false)) return null;
        base_slice = base_slice[0..plus_idx];
    }

    var pre_id: StringId = .empty;
    if (std.mem.indexOfScalar(u8, base_slice, '-')) |dash_idx| {
        const pre_str = base_slice[dash_idx + 1 ..];
        if (!isValidSemVerSuffix(pre_str, true)) return null;
        pre_id = try interner.intern(pre_str);
        base_slice = base_slice[0..dash_idx];
    }

    var seg_iter = std.mem.splitScalar(u8, base_slice, '.');
    const seg0 = seg_iter.next() orelse return null;
    const major_val = parseStrictSemVerUint(seg0) orelse return null;

    var result = PartialSemVer{ .major = major_val, .pre = pre_id };
    if (seg_iter.next()) |seg1| {
        if (std.mem.eql(u8, seg1, "*") or std.mem.eql(u8, seg1, "x") or std.mem.eql(u8, seg1, "X")) {
            if (pre_id != .empty) return null;
            if (seg_iter.next()) |seg2| {
                if (!std.mem.eql(u8, seg2, "*") and !std.mem.eql(u8, seg2, "x") and !std.mem.eql(u8, seg2, "X")) {
                    return null;
                }
                if (seg_iter.next() != null) return null;
            }
            result.has_wildcard = true;
            return result;
        }
        result.minor = parseStrictSemVerUint(seg1) orelse return null;
        if (seg_iter.next()) |seg2| {
            if (seg_iter.next() != null) return null;
            if (std.mem.eql(u8, seg2, "*") or std.mem.eql(u8, seg2, "x") or std.mem.eql(u8, seg2, "X")) {
                if (pre_id != .empty) return null;
                result.has_wildcard = true;
                return result;
            }
            result.patch = parseStrictSemVerUint(seg2) orelse return null;
        } else if (pre_id != .empty) {
            return null;
        }
    } else if (pre_id != .empty) {
        return null;
    }
    return result;
}

/// Appends one `VersionComparator` onto `req`, returning `false` on overflow past `MAX_VERSION_COMPARATORS`.
fn pushComparator(req: *VersionReq, op: ComparatorOp, ver: SemVer, interner: *const StringInterner) bool {
    if (req.len >= MAX_VERSION_COMPARATORS) return false;
    req.comparators[req.len] = .{ .op = op, .ver = ver };
    req.len += 1;
    if (op == .exact or op == .greater_eq or op == .greater) {
        if (SemVer.compare(ver, req.min_floor, interner) == .gt) {
            req.min_floor = ver;
        }
    }
    return true;
}

/// Computes the natural `SeriesKey` exclusive ceiling `< ceiling` for `floor_ver` (`1.x -> 2.0.0`, `0.2.x -> 0.3.0`).
fn computeNaturalSeriesCeiling(floor_ver: SemVer) ?SemVer {
    if (floor_ver.major >= 1) {
        const next_maj = std.math.add(u32, floor_ver.major, 1) catch return null;
        return .{ .major = next_maj, .minor = 0, .patch = 0 };
    }
    if (floor_ver.minor >= 1) {
        const next_min = std.math.add(u32, floor_ver.minor, 1) catch return null;
        return .{ .major = 0, .minor = next_min, .patch = 0 };
    }
    const next_pat = std.math.add(u32, floor_ver.patch, 1) catch return null;
    return .{ .major = 0, .minor = 0, .patch = next_pat };
}

/// Parses comma-separated SemVer requirement atoms into a normalized `VersionReq`.
fn parseVersionReqImpl(interner: *StringInterner, raw_req: []const u8) !?VersionReq {
    const trimmed_all = std.mem.trim(u8, raw_req, " \t");
    if (trimmed_all.len == 0) return null;

    var req = VersionReq{};
    var clause_iter = std.mem.splitScalar(u8, trimmed_all, ',');
    while (clause_iter.next()) |raw_clause| {
        const clause = std.mem.trim(u8, raw_clause, " \t");
        if (clause.len == 0) return null;

        if (std.mem.startsWith(u8, clause, ">=")) {
            const part = (try parsePartialSemVer(interner, clause[2..])) orelse return null;
            if (part.has_wildcard or part.major == null) return null;
            const floor_v = SemVer{
                .major = part.major.?,
                .minor = part.minor orelse 0,
                .patch = part.patch orelse 0,
                .pre = part.pre,
            };
            if (!pushComparator(&req, .greater_eq, floor_v, interner)) return null;
        } else if (std.mem.startsWith(u8, clause, "<=")) {
            const part = (try parsePartialSemVer(interner, clause[2..])) orelse return null;
            if (part.has_wildcard or part.major == null) return null;
            const ceil_v = SemVer{
                .major = part.major.?,
                .minor = part.minor orelse std.math.maxInt(u32),
                .patch = part.patch orelse std.math.maxInt(u32),
                .pre = part.pre,
            };
            req.has_intra_series_upper_bound = true;
            if (!pushComparator(&req, .less_eq, ceil_v, interner)) return null;
        } else if (std.mem.startsWith(u8, clause, ">")) {
            const part = (try parsePartialSemVer(interner, clause[1..])) orelse return null;
            if (part.has_wildcard or part.major == null) return null;
            if (part.minor == null) {
                const next_maj = std.math.add(u32, part.major.?, 1) catch return null;
                if (!pushComparator(&req, .greater_eq, .{ .major = next_maj }, interner)) return null;
            } else if (part.patch == null) {
                const next_min = std.math.add(u32, part.minor.?, 1) catch return null;
                if (!pushComparator(&req, .greater_eq, .{ .major = part.major.?, .minor = next_min }, interner)) {
                    return null;
                }
            } else {
                const ver = SemVer{
                    .major = part.major.?,
                    .minor = part.minor.?,
                    .patch = part.patch.?,
                    .pre = part.pre,
                };
                if (!pushComparator(&req, .greater, ver, interner)) return null;
            }
        } else if (std.mem.startsWith(u8, clause, "<")) {
            const part = (try parsePartialSemVer(interner, clause[1..])) orelse return null;
            if (part.has_wildcard or part.major == null) return null;
            const ceil_v = SemVer{
                .major = part.major.?,
                .minor = part.minor orelse 0,
                .patch = part.patch orelse 0,
                .pre = part.pre,
            };
            req.has_intra_series_upper_bound = true;
            if (!pushComparator(&req, .less, ceil_v, interner)) return null;
        } else if (std.mem.startsWith(u8, clause, "=")) {
            const part = (try parsePartialSemVer(interner, clause[1..])) orelse return null;
            if (part.has_wildcard or part.major == null or part.minor == null or part.patch == null) {
                return null;
            }
            const exact_v = SemVer{
                .major = part.major.?,
                .minor = part.minor.?,
                .patch = part.patch.?,
                .pre = part.pre,
            };
            req.has_intra_series_upper_bound = true;
            if (!pushComparator(&req, .exact, exact_v, interner)) return null;
        } else if (std.mem.startsWith(u8, clause, "~")) {
            const part = (try parsePartialSemVer(interner, clause[1..])) orelse return null;
            if (part.has_wildcard or part.major == null) return null;
            const floor_v = SemVer{
                .major = part.major.?,
                .minor = part.minor orelse 0,
                .patch = part.patch orelse 0,
                .pre = part.pre,
            };
            if (!pushComparator(&req, .greater_eq, floor_v, interner)) return null;
            const ceil_v: SemVer = if (part.minor) |min_val|
                .{ .major = part.major.?, .minor = std.math.add(u32, min_val, 1) catch return null }
            else
                .{ .major = std.math.add(u32, part.major.?, 1) catch return null };
            if (part.major.? >= 1 and part.minor != null) {
                req.has_intra_series_upper_bound = true;
            }
            if (!pushComparator(&req, .less, ceil_v, interner)) return null;
        } else {
            const body = if (std.mem.startsWith(u8, clause, "^")) clause[1..] else clause;
            const is_caret = std.mem.startsWith(u8, clause, "^");
            const part = (try parsePartialSemVer(interner, body)) orelse return null;
            if (part.major == null) {
                if (is_caret) return null;
                if (!pushComparator(&req, .wildcard_any, .{}, interner)) return null;
                continue;
            }
            if (part.has_wildcard) {
                if (is_caret) return null;
                const floor_v = SemVer{ .major = part.major.?, .minor = part.minor orelse 0, .patch = 0 };
                if (!pushComparator(&req, .greater_eq, floor_v, interner)) return null;
                const ceil_v: SemVer = if (part.minor) |min_val|
                    .{ .major = part.major.?, .minor = std.math.add(u32, min_val, 1) catch return null }
                else
                    .{ .major = std.math.add(u32, part.major.?, 1) catch return null };
                if (part.major.? >= 1 and part.minor != null) {
                    req.has_intra_series_upper_bound = true;
                }
                if (!pushComparator(&req, .less, ceil_v, interner)) return null;
                continue;
            }

            // Bare MVS lower bound (`"1.4.2"`) or `^` compatibility range:
            const floor_v = SemVer{
                .major = part.major.?,
                .minor = part.minor orelse 0,
                .patch = part.patch orelse 0,
                .pre = part.pre,
            };
            if (!pushComparator(&req, .greater_eq, floor_v, interner)) return null;
            const ceil_v: SemVer = if (part.major.? >= 1)
                .{ .major = std.math.add(u32, part.major.?, 1) catch return null }
            else if (part.minor) |min_val| blk: {
                if (min_val >= 1) {
                    break :blk .{ .major = 0, .minor = std.math.add(u32, min_val, 1) catch return null };
                }
                if (part.patch) |pat_val| {
                    break :blk .{ .major = 0, .minor = 0, .patch = std.math.add(u32, pat_val, 1) catch return null };
                }
                break :blk .{ .major = 0, .minor = 1, .patch = 0 };
            } else .{ .major = 1, .minor = 0, .patch = 0 };

            if (computeNaturalSeriesCeiling(floor_v)) |nat_ceil| {
                if (SemVer.compare(ceil_v, nat_ceil, interner) == .lt) {
                    req.has_intra_series_upper_bound = true;
                }
            }
            if (!pushComparator(&req, .less, ceil_v, interner)) return null;
        }
    }
    return if (req.len > 0) req else null;
}

/// Evaluates `candidate` against all comparators in `req` per Cargo / SemVer pre-release semantics.
fn isVersionReqMatchingImpl(req: *const VersionReq, candidate: SemVer, interner: *const StringInterner) bool {
    const active = req.comparators[0..req.len];
    for (active) |comp| {
        const ord = SemVer.compare(candidate, comp.ver, interner);
        const is_ok = switch (comp.op) {
            .wildcard_any => candidate.pre == .empty,
            .exact => ord == .eq,
            .greater_eq => ord == .gt or ord == .eq,
            .greater => ord == .gt,
            .less_eq => ord == .lt or ord == .eq,
            .less => blk: {
                if (candidate.pre != .empty and comp.ver.pre == .empty and
                    SemVerCore.compare(candidate.asCore(), comp.ver.asCore()) == .eq)
                {
                    break :blk false;
                }
                break :blk ord == .lt;
            },
        };
        if (!is_ok) return false;
    }

    if (candidate.pre != .empty) {
        var has_matching_pre_tuple = false;
        for (active) |comp| {
            if (comp.op != .wildcard_any and comp.ver.pre != .empty and
                SemVerCore.compare(candidate.asCore(), comp.ver.asCore()) == .eq)
            {
                has_matching_pre_tuple = true;
                break;
            }
        }
        if (!has_matching_pre_tuple) return false;
    }
    return true;
}

// ------------ TOML v1.0 Non-Backtracking DFA Lexer ------------

/// Deterministic container/context state driving context-sensitive TOML key vs. value lexing.
const TomlLexMode = enum(u8) {
    /// Start of document or line (keys or `[table]` / `[[array_table]]` headers).
    doc_line_start = 0,
    /// Expecting a bare/quoted key segment after `.` at top level.
    key_segment = 1,
    /// Immediately after a top-level key segment (`.` or `=`).
    after_key = 2,
    /// Expecting a scalar, `[` array, or `{` inline-table value after `=`.
    val_start = 3,
    /// Inside `[ … ]` array literal.
    array_elem = 4,
    /// Expecting key or `}` inside `{ … }` inline table.
    inline_table_key = 5,
    /// After key segment inside `{ … }` inline table (`.` or `=`).
    inline_table_after_key = 6,
    /// Expecting value after `=` inside `{ … }` inline table.
    inline_table_val = 7,
    /// After value inside `{ … }` inline table (`,` or `}`).
    inline_table_after_val = 8,
    /// Inside `[table]` header.
    table_hdr = 9,
    /// Inside `[[array_table]]` header.
    array_table_hdr = 10,
};

/// Returns `true` if `ch_byte` is a TOML v1.0 bare-key byte (`[A-Za-z0-9_-]`).
inline fn isTomlBareKeyByte(ch_byte: u8) bool {
    return std.ascii.isAlphanumeric(ch_byte) or ch_byte == '_' or ch_byte == '-';
}

/// Returns `true` if `comment_slice` mentions `CVE-`, `GHSA-`, or `CXSEC-`.
fn hasSecurityAdvisoryMarker(comment_slice: []const u8) bool {
    return std.mem.indexOf(u8, comment_slice, "CVE-") != null or
        std.mem.indexOf(u8, comment_slice, "GHSA-") != null or
        std.mem.indexOf(u8, comment_slice, "CXSEC-") != null;
}

/// Returns `true` if `ch_byte` is a disallowed control byte inside TOML comments/strings.
inline fn isDisallowedTomlControl(ch_byte: u8) bool {
    return (ch_byte <= 0x08) or (ch_byte >= 0x0A and ch_byte <= 0x1F and ch_byte != '\n' and ch_byte != '\r') or ch_byte == 0x7F;
}

/// Emits a manifest (`E0013`) or lockfile (`E0014`) diagnostic at rebased byte span `[rel_lo .. rel_hi)`.
fn emitTomlDiag(
    sink: ?*DiagnosticSink,
    code: DiagnosticCode,
    file_id: FileId,
    base_byte_offset: u32,
    rel_lo: usize,
    rel_hi: usize,
    message: []const u8,
) !void {
    if (sink) |diag_sink| {
        const start_b: u32 = base_byte_offset +| @as(u32, @intCast(@min(rel_lo, std.math.maxInt(u32))));
        const end_b: u32 = base_byte_offset +| @as(u32, @intCast(@min(@max(rel_hi, rel_lo), std.math.maxInt(u32))));
        try diag_sink.emit(.{
            .code = code,
            .severity = .err,
            .primary_span = Span.init(file_id, start_b, end_b),
            .message = message,
        });
    }
}

/// Scans `doc.toml_slice` in a single non-backtracking $O(N)$ pass into `doc.tokens`.
fn lexTomlSlice(
    allocator: std.mem.Allocator,
    doc: *TomlDocumentView,
    diag_code: DiagnosticCode,
    sink: ?*DiagnosticSink,
) !void {
    const src = doc.toml_slice;
    if (src.len > MAX_TOML_BYTES) {
        doc.has_syntax_errors = true;
        try emitTomlDiag(
            sink,
            diag_code,
            doc.file_id,
            doc.base_byte_offset,
            0,
            @min(src.len, 1),
            "TOML document exceeds maximum 1 MiB size limit (`MAX_TOML_BYTES`)",
        );
        return;
    }
    if (!std.unicode.utf8ValidateSlice(src)) {
        doc.has_syntax_errors = true;
        try emitTomlDiag(
            sink,
            diag_code,
            doc.file_id,
            doc.base_byte_offset,
            0,
            @min(src.len, 1),
            "TOML document contains invalid UTF-8 byte sequences",
        );
        return;
    }

    var mode_stack: [MAX_TOML_DEPTH + 4]TomlLexMode = @splat(.doc_line_start);
    var stack_top: usize = 0;

    var cursor: usize = 0;
    var has_pending_newline = false;
    var has_pending_comment = false;
    var has_pending_cve = false;
    var blank_run: u8 = 0;
    var col_indent: u8 = 0;
    var is_at_line_head = true;

    while (cursor < src.len) {
        const ch_byte = src[cursor];

        // [1] Horizontal whitespace (`' '` or `'\t'`):
        if (ch_byte == ' ' or ch_byte == '\t') {
            if (is_at_line_head) col_indent +|= 1;
            cursor += 1;
            continue;
        }

        // [2] Line breaks (`\n` or `\r\n`; bare `\r` rejected per TOML v1.0):
        if (ch_byte == '\r' or ch_byte == '\n') {
            if (ch_byte == '\r' and (cursor + 1 >= src.len or src[cursor + 1] != '\n')) {
                doc.has_syntax_errors = true;
                try emitTomlDiag(
                    sink,
                    diag_code,
                    doc.file_id,
                    doc.base_byte_offset,
                    cursor,
                    cursor + 1,
                    "bare carriage return (`\\r`) is invalid in TOML v1.0; use `\\n` or `\\r\\n`",
                );
                cursor += 1;
                continue;
            }
            const nl_len: usize = if (ch_byte == '\r') 2 else 1;
            const cur_mode = mode_stack[stack_top];
            if (cur_mode == .inline_table_key or cur_mode == .inline_table_after_key or
                cur_mode == .inline_table_val or cur_mode == .inline_table_after_val)
            {
                doc.has_syntax_errors = true;
                try emitTomlDiag(
                    sink,
                    diag_code,
                    doc.file_id,
                    doc.base_byte_offset,
                    cursor,
                    cursor + nl_len,
                    "TOML v1.0 inline tables (`{ … }`) cannot contain unescaped line breaks",
                );
            } else if (stack_top == 0) {
                if (cur_mode != .doc_line_start) {
                    doc.has_syntax_errors = true;
                    try emitTomlDiag(
                        sink,
                        diag_code,
                        doc.file_id,
                        doc.base_byte_offset,
                        cursor,
                        cursor + nl_len,
                        "incomplete TOML key-value assignment or unclosed table header before newline",
                    );
                    mode_stack[0] = .doc_line_start;
                }
            }
            if (is_at_line_head) blank_run +|= 1;
            has_pending_newline = true;
            is_at_line_head = true;
            col_indent = 0;
            cursor += nl_len;
            continue;
        }

        // [3] `#` hash comments up to `\r\n`, `\n`, or EOF:
        if (ch_byte == '#') {
            const cmt_start = cursor;
            cursor += 1;
            var has_ctrl_err = false;
            while (cursor < src.len and src[cursor] != '\n' and src[cursor] != '\r') : (cursor += 1) {
                if (isDisallowedTomlControl(src[cursor])) {
                    has_ctrl_err = true;
                }
            }
            if (has_ctrl_err) {
                doc.has_syntax_errors = true;
                try emitTomlDiag(
                    sink,
                    diag_code,
                    doc.file_id,
                    doc.base_byte_offset,
                    cmt_start,
                    cursor,
                    "control character is forbidden inside TOML `#` comment",
                );
            }
            const cmt_slice = src[cmt_start..cursor];
            const is_cve = hasSecurityAdvisoryMarker(cmt_slice);
            const is_trailing = !is_at_line_head and doc.tokens.tokens.len > 0;
            if (is_trailing) {
                const last_idx = doc.tokens.tokens.len - 1;
                var prev_flags = doc.tokens.tokens.items(.flags)[last_idx];
                prev_flags.has_trailing_comment = true;
                if (is_cve) prev_flags.has_cve_comment = true;
                doc.tokens.tokens.items(.flags)[last_idx] = prev_flags;
            } else {
                has_pending_comment = true;
                if (is_cve) has_pending_cve = true;
            }
            try doc.tokens.trivia.append(allocator, .{
                .byte_offset = @intCast(cmt_start),
                .byte_len = @intCast(@min(cmt_slice.len, std.math.maxInt(u16))),
                .meta = .{
                    .kind = .hash_comment,
                    .is_trailing = is_trailing,
                    .has_cve_advisory = is_cve,
                    .blank_lines_before = @intCast(@min(blank_run, 3)),
                    .has_newline_after = cursor < src.len,
                },
                .indent_cols = col_indent,
            });
            blank_run = 0;
            continue;
        }

        // Enforce `MAX_TOML_TOKENS` cap before emitting syntactic token:
        if (doc.tokens.tokens.len + 1 >= MAX_TOML_TOKENS) {
            doc.has_syntax_errors = true;
            try emitTomlDiag(
                sink,
                diag_code,
                doc.file_id,
                doc.base_byte_offset,
                cursor,
                cursor + 1,
                "TOML document exceeds `MAX_TOML_TOKENS` (`65,536`) limit",
            );
            break;
        }

        is_at_line_head = false;
        blank_run = 0;

        var tok_flags = TomlTokenFlags{
            .has_leading_newline = has_pending_newline,
            .has_leading_comment = has_pending_comment,
            .has_cve_comment = has_pending_cve,
        };
        has_pending_newline = false;
        has_pending_comment = false;
        has_pending_cve = false;

        const tok_start = cursor;
        const cur_mode = mode_stack[stack_top];

        // [4] Punctuation & structural delimiters:
        if (ch_byte == '[') {
            if (stack_top == 0 and cur_mode == .doc_line_start) {
                if (cursor + 1 < src.len and src[cursor + 1] == '[') {
                    cursor += 2;
                    mode_stack[0] = .array_table_hdr;
                    try doc.tokens.tokens.append(allocator, .{
                        .byte_offset = @intCast(tok_start),
                        .byte_len = 2,
                        .kind = .double_lbracket,
                        .flags = tok_flags,
                    });
                } else {
                    cursor += 1;
                    mode_stack[0] = .table_hdr;
                    try doc.tokens.tokens.append(allocator, .{
                        .byte_offset = @intCast(tok_start),
                        .byte_len = 1,
                        .kind = .lbracket,
                        .flags = tok_flags,
                    });
                }
                continue;
            }
            cursor += 1;
            if (cur_mode == .val_start) {
                mode_stack[stack_top] = .doc_line_start;
            } else if (cur_mode == .inline_table_val) {
                mode_stack[stack_top] = .inline_table_after_val;
            }
            if (stack_top + 1 > MAX_TOML_DEPTH) {
                doc.has_syntax_errors = true;
                try emitTomlDiag(
                    sink,
                    diag_code,
                    doc.file_id,
                    doc.base_byte_offset,
                    tok_start,
                    cursor,
                    "TOML nesting depth exceeds `MAX_TOML_DEPTH` (`16`)",
                );
                break;
            }
            stack_top += 1;
            mode_stack[stack_top] = .array_elem;
            try doc.tokens.tokens.append(allocator, .{
                .byte_offset = @intCast(tok_start),
                .byte_len = 1,
                .kind = .lbracket,
                .flags = tok_flags,
            });
            continue;
        }

        if (ch_byte == ']') {
            if (stack_top == 0 and cur_mode == .array_table_hdr and cursor + 1 < src.len and src[cursor + 1] == ']') {
                cursor += 2;
                mode_stack[0] = .doc_line_start;
                try doc.tokens.tokens.append(allocator, .{
                    .byte_offset = @intCast(tok_start),
                    .byte_len = 2,
                    .kind = .double_rbracket,
                    .flags = tok_flags,
                });
                continue;
            }
            cursor += 1;
            if (stack_top == 0 and cur_mode == .table_hdr) {
                mode_stack[0] = .doc_line_start;
            } else if (stack_top > 0 and cur_mode == .array_elem) {
                stack_top -= 1;
            } else {
                doc.has_syntax_errors = true;
                tok_flags.has_lexer_error = true;
            }
            try doc.tokens.tokens.append(allocator, .{
                .byte_offset = @intCast(tok_start),
                .byte_len = 1,
                .kind = .rbracket,
                .flags = tok_flags,
            });
            continue;
        }

        if (ch_byte == '{') {
            cursor += 1;
            if (cur_mode == .val_start) {
                mode_stack[stack_top] = .doc_line_start;
            } else if (cur_mode == .inline_table_val) {
                mode_stack[stack_top] = .inline_table_after_val;
            }
            if (stack_top + 1 > MAX_TOML_DEPTH) {
                doc.has_syntax_errors = true;
                try emitTomlDiag(
                    sink,
                    diag_code,
                    doc.file_id,
                    doc.base_byte_offset,
                    tok_start,
                    cursor,
                    "TOML inline-table nesting exceeds `MAX_TOML_DEPTH` (`16`)",
                );
                break;
            }
            stack_top += 1;
            mode_stack[stack_top] = .inline_table_key;
            try doc.tokens.tokens.append(allocator, .{
                .byte_offset = @intCast(tok_start),
                .byte_len = 1,
                .kind = .lbrace,
                .flags = tok_flags,
            });
            continue;
        }

        if (ch_byte == '}') {
            cursor += 1;
            if (stack_top > 0 and (cur_mode == .inline_table_key or cur_mode == .inline_table_after_val)) {
                stack_top -= 1;
            } else {
                doc.has_syntax_errors = true;
                tok_flags.has_lexer_error = true;
            }
            try doc.tokens.tokens.append(allocator, .{
                .byte_offset = @intCast(tok_start),
                .byte_len = 1,
                .kind = .rbrace,
                .flags = tok_flags,
            });
            continue;
        }

        if (ch_byte == '=') {
            cursor += 1;
            if (cur_mode == .after_key) {
                mode_stack[stack_top] = .val_start;
            } else if (cur_mode == .inline_table_after_key) {
                mode_stack[stack_top] = .inline_table_val;
            } else {
                doc.has_syntax_errors = true;
                tok_flags.has_lexer_error = true;
            }
            try doc.tokens.tokens.append(allocator, .{
                .byte_offset = @intCast(tok_start),
                .byte_len = 1,
                .kind = .eq,
                .flags = tok_flags,
            });
            continue;
        }

        if (ch_byte == '.') {
            cursor += 1;
            if (cur_mode == .after_key) {
                mode_stack[stack_top] = .key_segment;
            } else if (cur_mode == .inline_table_after_key) {
                mode_stack[stack_top] = .inline_table_key;
            }
            try doc.tokens.tokens.append(allocator, .{
                .byte_offset = @intCast(tok_start),
                .byte_len = 1,
                .kind = .dot,
                .flags = tok_flags,
            });
            continue;
        }

        if (ch_byte == ',') {
            cursor += 1;
            if (cur_mode == .inline_table_after_val) {
                var peek = cursor;
                while (peek < src.len and (src[peek] == ' ' or src[peek] == '\t')) : (peek += 1) {}
                if (peek < src.len and src[peek] == '}') {
                    doc.has_syntax_errors = true;
                    tok_flags.has_lexer_error = true;
                    try emitTomlDiag(
                        sink,
                        diag_code,
                        doc.file_id,
                        doc.base_byte_offset,
                        tok_start,
                        cursor,
                        "TOML v1.0 forbids trailing comma inside inline table `{ … }`",
                    );
                }
                mode_stack[stack_top] = .inline_table_key;
            } else if (cur_mode != .array_elem) {
                doc.has_syntax_errors = true;
                tok_flags.has_lexer_error = true;
            }
            try doc.tokens.tokens.append(allocator, .{
                .byte_offset = @intCast(tok_start),
                .byte_len = 1,
                .kind = .comma,
                .flags = tok_flags,
            });
            continue;
        }

        // [5] Basic & literal strings (`"…"`, `"""…"""`, `'…'`, `'''…'''`):
        if (ch_byte == '"' or ch_byte == '\'') {
            const is_double = ch_byte == '"';
            const is_multi = cursor + 2 < src.len and src[cursor + 1] == ch_byte and src[cursor + 2] == ch_byte;
            cursor += if (is_multi) 3 else 1;
            var has_closed = false;
            var has_escape = false;
            var has_str_err = false;

            while (cursor < src.len) {
                const str_ch = src[cursor];
                if (is_double and str_ch == '\\') {
                    has_escape = true;
                    cursor += 1;
                    if (cursor >= src.len) {
                        has_str_err = true;
                        break;
                    }
                    const esc_ch = src[cursor];
                    if (is_multi and (esc_ch == '\n' or esc_ch == '\r' or esc_ch == ' ' or esc_ch == '\t')) {
                        while (cursor < src.len and (src[cursor] == ' ' or src[cursor] == '\t' or
                            src[cursor] == '\r' or src[cursor] == '\n')) : (cursor += 1)
                        {}
                        continue;
                    }
                    cursor += 1;
                    continue;
                }
                if (!is_multi and (str_ch == '\n' or str_ch == '\r')) {
                    has_str_err = true;
                    break;
                }
                if (is_multi and str_ch == '\r' and (cursor + 1 >= src.len or src[cursor + 1] != '\n')) {
                    has_str_err = true;
                }
                if (isDisallowedTomlControl(str_ch) and str_ch != '\t') {
                    has_str_err = true;
                }
                if (str_ch == ch_byte) {
                    if (is_multi) {
                        if (cursor + 2 < src.len and src[cursor + 1] == ch_byte and src[cursor + 2] == ch_byte) {
                            cursor += 3;
                            var extra_quotes: u8 = 0;
                            while (cursor < src.len and src[cursor] == ch_byte and extra_quotes < 2) : (extra_quotes += 1) {
                                cursor += 1;
                            }
                            has_closed = true;
                            break;
                        }
                    } else {
                        cursor += 1;
                        has_closed = true;
                        break;
                    }
                }
                cursor += 1;
            }

            if (!has_closed or has_str_err) {
                doc.has_syntax_errors = true;
                tok_flags.has_lexer_error = true;
                try emitTomlDiag(
                    sink,
                    diag_code,
                    doc.file_id,
                    doc.base_byte_offset,
                    tok_start,
                    cursor,
                    "unterminated or invalid TOML string literal",
                );
            }
            const span_len = cursor - tok_start;
            if (has_escape or span_len >= 0xFFFF) tok_flags.has_escape_or_long_len = true;

            const str_kind: TomlTokenKind = if (is_double)
                (if (is_multi) .multiline_basic_string else .basic_string)
            else
                (if (is_multi) .multiline_literal_string else .literal_string);

            advanceModeAfterAtom(mode_stack[0..], stack_top);
            try doc.tokens.tokens.append(allocator, .{
                .byte_offset = @intCast(tok_start),
                .byte_len = @intCast(@min(span_len, 0xFFFF)),
                .kind = str_kind,
                .flags = tok_flags,
            });
            continue;
        }

        // [6] Context-aware bare keys vs. scalar literals (`bool_lit`, `int_lit`, `float_lit`, `datetime_lit`):
        const is_key_ctx = (cur_mode == .doc_line_start or cur_mode == .key_segment or
            cur_mode == .inline_table_key or cur_mode == .table_hdr or cur_mode == .array_table_hdr);
        if (is_key_ctx) {
            if (isTomlBareKeyByte(ch_byte)) {
                while (cursor < src.len and isTomlBareKeyByte(src[cursor])) : (cursor += 1) {}
                advanceModeAfterAtom(mode_stack[0..], stack_top);
                try doc.tokens.tokens.append(allocator, .{
                    .byte_offset = @intCast(tok_start),
                    .byte_len = @intCast(@min(cursor - tok_start, 0xFFFF)),
                    .kind = .bare_key,
                    .flags = tok_flags,
                });
                continue;
            }
        } else {
            while (cursor < src.len) : (cursor += 1) {
                const b_cur = src[cursor];
                if (b_cur == ' ' or b_cur == '\t' or b_cur == '\r' or b_cur == '\n' or
                    b_cur == '#' or b_cur == ',' or b_cur == ']' or b_cur == '}')
                {
                    break;
                }
                if (b_cur == ':' and cursor + 2 < src.len and
                    std.ascii.isDigit(src[cursor + 1]) and std.ascii.isDigit(src[cursor + 2]))
                {
                    continue;
                }
            }
            if (cursor > tok_start) {
                var val_end = cursor;
                const head = src[tok_start..val_end];
                if (head.len >= 10 and head[4] == '-' and head[7] == '-' and
                    cursor < src.len and src[cursor] == ' ' and
                    cursor + 2 < src.len and std.ascii.isDigit(src[cursor + 1]))
                {
                    cursor += 1;
                    while (cursor < src.len and src[cursor] != ' ' and src[cursor] != '\t' and
                        src[cursor] != '\r' and src[cursor] != '\n' and src[cursor] != '#' and
                        src[cursor] != ',' and src[cursor] != ']' and src[cursor] != '}') : (cursor += 1)
                    {}
                    val_end = cursor;
                }
                const atom = src[tok_start..val_end];
                const scalar_kind = classifyTomlValueScalar(atom);
                if (scalar_kind == .invalid_token) {
                    doc.has_syntax_errors = true;
                    tok_flags.has_lexer_error = true;
                    try emitTomlDiag(
                        sink,
                        diag_code,
                        doc.file_id,
                        doc.base_byte_offset,
                        tok_start,
                        val_end,
                        "invalid TOML value literal",
                    );
                }
                advanceModeAfterAtom(mode_stack[0..], stack_top);
                try doc.tokens.tokens.append(allocator, .{
                    .byte_offset = @intCast(tok_start),
                    .byte_len = @intCast(@min(val_end - tok_start, 0xFFFF)),
                    .kind = scalar_kind,
                    .flags = tok_flags,
                });
                continue;
            }
        }

        // [7] Unexpected byte recovery:
        cursor += 1;
        doc.has_syntax_errors = true;
        tok_flags.has_lexer_error = true;
        try emitTomlDiag(
            sink,
            diag_code,
            doc.file_id,
            doc.base_byte_offset,
            tok_start,
            cursor,
            "unexpected character in TOML document",
        );
        try doc.tokens.tokens.append(allocator, .{
            .byte_offset = @intCast(tok_start),
            .byte_len = 1,
            .kind = .invalid_token,
            .flags = tok_flags,
        });
    }

    if (stack_top != 0 or (mode_stack[0] != .doc_line_start)) {
        doc.has_syntax_errors = true;
        try emitTomlDiag(
            sink,
            diag_code,
            doc.file_id,
            doc.base_byte_offset,
            src.len,
            src.len,
            "unexpected end of TOML document (unclosed `[…]`/`{…}` or incomplete assignment)",
        );
    }

    try doc.tokens.tokens.append(allocator, .{
        .byte_offset = @intCast(src.len),
        .byte_len = 0,
        .kind = .eof,
        .flags = .{
            .has_leading_newline = has_pending_newline,
            .has_leading_comment = has_pending_comment,
            .has_cve_comment = has_pending_cve,
        },
    });
}

/// Transitions the top `TomlLexMode` after scanning a key segment or scalar value.
fn advanceModeAfterAtom(mode_stack: []TomlLexMode, stack_top: usize) void {
    switch (mode_stack[stack_top]) {
        .doc_line_start, .key_segment => mode_stack[stack_top] = .after_key,
        .inline_table_key => mode_stack[stack_top] = .inline_table_after_key,
        .val_start => mode_stack[stack_top] = .doc_line_start,
        .inline_table_val => mode_stack[stack_top] = .inline_table_after_val,
        .table_hdr, .array_table_hdr, .array_elem, .after_key, .inline_table_after_key, .inline_table_after_val => {},
    }
}

/// Classifies a non-string TOML scalar slice into `.bool_lit`, `.datetime_lit`, `.int_lit`, `.float_lit`, or `.invalid_token`.
fn classifyTomlValueScalar(atom: []const u8) TomlTokenKind {
    if (std.mem.eql(u8, atom, "true") or std.mem.eql(u8, atom, "false")) return .bool_lit;
    if (std.mem.eql(u8, atom, "inf") or std.mem.eql(u8, atom, "+inf") or std.mem.eql(u8, atom, "-inf") or
        std.mem.eql(u8, atom, "nan") or std.mem.eql(u8, atom, "+nan") or std.mem.eql(u8, atom, "-nan"))
    {
        return .float_lit;
    }
    if ((atom.len >= 10 and atom[4] == '-' and atom[7] == '-') or
        (atom.len >= 8 and atom[2] == ':' and atom[5] == ':'))
    {
        return .datetime_lit;
    }

    var body = atom;
    var has_sign = false;
    if (body.len > 0 and (body[0] == '+' or body[0] == '-')) {
        has_sign = true;
        body = body[1..];
    }
    if (body.len == 0) return .invalid_token;

    if (!has_sign and body.len > 2 and body[0] == '0' and
        (body[1] == 'x' or body[1] == 'o' or body[1] == 'b'))
    {
        const radix_char = body[1];
        const digits = body[2..];
        if (digits.len == 0 or digits[0] == '_' or digits[digits.len - 1] == '_') return .invalid_token;
        var has_prev_us = false;
        for (digits) |ch_b| {
            if (ch_b == '_') {
                if (has_prev_us) return .invalid_token;
                has_prev_us = true;
                continue;
            }
            has_prev_us = false;
            const is_valid_digit = switch (radix_char) {
                'x' => std.ascii.isHex(ch_b),
                'o' => ch_b >= '0' and ch_b <= '7',
                'b' => ch_b == '0' or ch_b == '1',
                else => false,
            };
            if (!is_valid_digit) return .invalid_token;
        }
        return .int_lit;
    }

    if (body[0] == '_' or body[body.len - 1] == '_') return .invalid_token;
    var has_dot = false;
    var has_exp = false;
    var has_prev_underscore = false;
    for (body, 0..) |ch_b, i| {
        if (ch_b == '_') {
            if (has_prev_underscore or i == 0 or !std.ascii.isDigit(body[i - 1]) or
                i + 1 >= body.len or !std.ascii.isDigit(body[i + 1]))
            {
                return .invalid_token;
            }
            has_prev_underscore = true;
        } else if (ch_b == '.') {
            if (has_dot or has_exp or i == 0 or i + 1 >= body.len or
                !std.ascii.isDigit(body[i - 1]) or !std.ascii.isDigit(body[i + 1]))
            {
                return .invalid_token;
            }
            has_dot = true;
            has_prev_underscore = false;
        } else if (ch_b == 'e' or ch_b == 'E') {
            if (has_exp or i == 0 or i + 1 >= body.len) return .invalid_token;
            has_exp = true;
            has_prev_underscore = false;
        } else if (ch_b == '+' or ch_b == '-') {
            if (i == 0 or (body[i - 1] != 'e' and body[i - 1] != 'E') or
                i + 1 >= body.len or !std.ascii.isDigit(body[i + 1]))
            {
                return .invalid_token;
            }
            has_prev_underscore = false;
        } else if (std.ascii.isDigit(ch_b)) {
            has_prev_underscore = false;
        } else {
            return .invalid_token;
        }
    }
    const int_head_end = std.mem.indexOfAny(u8, body, ".eE") orelse body.len;
    const int_head = body[0..int_head_end];
    if (int_head.len > 1 and int_head[0] == '0') return .invalid_token;
    return if (has_dot or has_exp) .float_lit else .int_lit;
}

// ------------- TOML CST & Semantic Table Builder --------------

/// Typed arena-allocated TOML value node constructed alongside `TomlCstArena`.
const TomlDomValue = union(enum) {
    /// Decoded UTF-8 string value.
    str_val: []const u8,
    /// Decoded 64-bit signed integer value.
    int_val: i64,
    /// Decoded 64-bit unsigned integer value (for `tlog_index: u64` >= `2^63`).
    uint_val: u64,
    /// Decoded 64-bit floating-point value.
    float_val: f64,
    /// Decoded boolean value.
    bool_val: bool,
    /// Raw ISO-8601 datetime text.
    datetime_val: []const u8,
    /// Ordered array of elements.
    array_val: []const TomlDomElem,
    /// Key-ordered TOML table.
    table_val: *TomlDomTable,
};

/// Array element pairing a `TomlDomValue` with its source span and `TomlSpanAnchor` index.
const TomlDomElem = struct {
    /// Decoded element value.
    val: TomlDomValue,
    /// Rebased source `Span` of the element.
    span: Span,
    /// Index into `doc.cst.anchors` (`0xFFFF_FFFF` for compound sub-elements).
    anchor_id: u32 = std.math.maxInt(u32),
    /// `true` if adjacent `#` trivia cited `CVE-`/`GHSA-`/`CXSEC-`.
    has_cve_advisory: bool = false,
};

/// Single key-value entry inside a `TomlDomTable`.
const TomlDomEntry = struct {
    /// Unquoted UTF-8 key name.
    key: []const u8,
    /// Rebased `Span` of the key token.
    key_span: Span,
    /// Rebased `Span` of the value expression.
    val_span: Span,
    /// Decoded value.
    val: TomlDomValue,
    /// Geometric backing buffer for `[[array_table]]` elements ($O(N)$ amortized growth).
    array_table_buf: std.ArrayListUnmanaged(TomlDomElem) = .empty,
    /// Index into `doc.cst.anchors`.
    anchor_id: u32 = std.math.maxInt(u32),
    /// `true` when defined via `[subtable]` header rather than inline/dotted key.
    is_explicit_header: bool = false,
};

/// Arena-backed TOML table preserving insertion order and TOML v1.0 redefinition invariants.
const TomlDomTable = struct {
    /// Ordered list of entries in this table.
    entries: std.ArrayListUnmanaged(TomlDomEntry) = .empty,
    /// $O(1)$ lookup index mapping entry keys to `entries.items` indices.
    key_index: std.StringHashMapUnmanaged(u32) = .empty,
    /// `true` if sealed as an inline `{ … }` table or scalar-assigned dotted parent.
    is_inline_sealed: bool = false,
    /// `true` if already opened via an explicit `[table]` header.
    is_explicitly_defined: bool = false,
    /// `true` if implicitly created as a super-table of `[a.b]` (may still be opened once as `[a]`).
    is_super_table: bool = false,
    /// Header span for diagnostics.
    header_span: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 },

    /// Appends `entry` onto `self.entries` and indexes `entry.key` in $O(1)$ amortized time.
    fn appendEntry(self: *TomlDomTable, allocator: std.mem.Allocator, entry: TomlDomEntry) !void {
        const idx: u32 = @intCast(self.entries.items.len);
        try self.entries.append(allocator, entry);
        try self.key_index.put(allocator, entry.key, idx);
    }

    /// Looks up `key` inside `self.entries` in $O(1)$ time via `self.key_index`.
    fn findEntry(self: *const TomlDomTable, key: []const u8) ?*TomlDomEntry {
        const idx = self.key_index.get(key) orelse return null;
        return &self.entries.items[idx];
    }
};

/// Returns the safe relative byte offset of token `tok_idx` inside `doc.toml_slice`.
inline fn getTokenByteOffset(doc: *const TomlDocumentView, tok_idx: u32) u32 {
    if (tok_idx >= doc.tokens.tokens.len) {
        return @intCast(@min(doc.toml_slice.len, std.math.maxInt(u32)));
    }
    return doc.tokens.tokens.items(.byte_offset)[tok_idx];
}

/// Returns the exact slice of token `tok_idx` in `doc.toml_slice` (handling `>= 65,535` long strings).
fn getTomlTokenSlice(doc: *const TomlDocumentView, tok_idx: u32) []const u8 {
    if (tok_idx >= doc.tokens.tokens.len) return "";
    const offsets = doc.tokens.tokens.items(.byte_offset);
    const lens = doc.tokens.tokens.items(.byte_len);
    const kinds = doc.tokens.tokens.items(.kind);
    const start: usize = @min(@as(usize, offsets[tok_idx]), doc.toml_slice.len);
    var len: usize = lens[tok_idx];
    if (len == 0xFFFF and kinds[tok_idx] != .eof and tok_idx + 1 < doc.tokens.tokens.len) {
        const next_off: usize = @max(start, @min(@as(usize, offsets[tok_idx + 1]), doc.toml_slice.len));
        const sub = doc.toml_slice[start..next_off];
        len = std.mem.trimEnd(u8, sub, " \t\r\n").len;
    }
    return doc.toml_slice[start..@min(start + len, doc.toml_slice.len)];
}

/// Computes the rebased `Span` of token range `[first_tok .. last_tok]` in `doc.file_id`.
fn getTomlTokenRangeSpan(doc: *const TomlDocumentView, first_tok: u32, last_tok: u32) Span {
    if (doc.tokens.tokens.len == 0) {
        return Span.init(doc.file_id, doc.base_byte_offset, doc.base_byte_offset);
    }
    const max_idx: u32 = @intCast(doc.tokens.tokens.len - 1);
    const clamped_first = @min(first_tok, max_idx);
    const clamped_last = @max(clamped_first, @min(last_tok, max_idx));
    const offsets = doc.tokens.tokens.items(.byte_offset);
    const start_rel = offsets[clamped_first];
    const last_slice = getTomlTokenSlice(doc, clamped_last);
    const end_rel: u32 = offsets[clamped_last] +| @as(u32, @intCast(last_slice.len));
    return Span.init(doc.file_id, doc.base_byte_offset +| start_rel, doc.base_byte_offset +| end_rel);
}

/// Computes the 0-based UTF-8 column of `rel_byte` on its enclosing line in `doc.toml_slice`.
fn computeUtf8Column(toml_slice: []const u8, rel_byte: u32) u16 {
    const pos: usize = @min(@as(usize, rel_byte), toml_slice.len);
    var line_start = pos;
    while (line_start > 0 and toml_slice[line_start - 1] != '\n') : (line_start -= 1) {}
    const count = std.unicode.utf8CountCodepoints(toml_slice[line_start..pos]) catch (pos - line_start);
    return @intCast(@min(count, std.math.maxInt(u16)));
}

/// Computes the absolute `full_file_bytes` offset immediately past the newline ending `rel_byte`'s line.
fn computeRowEndByte(doc: *const TomlDocumentView, rel_byte: u32) u32 {
    var cursor: usize = @min(@as(usize, rel_byte), doc.toml_slice.len);
    while (cursor < doc.toml_slice.len and doc.toml_slice[cursor] != '\n') : (cursor += 1) {}
    if (cursor < doc.toml_slice.len and doc.toml_slice[cursor] == '\n') cursor += 1;
    return doc.base_byte_offset +| @as(u32, @intCast(cursor));
}

/// Unquotes and unescapes a TOML basic/literal/multiline string or bare key into `arena`.
fn decodeTomlStringOrKey(
    arena: *BumpArena,
    doc: *TomlDocumentView,
    tok_idx: u32,
    is_key: bool,
    diag_code: DiagnosticCode,
    sink: ?*DiagnosticSink,
) ![]const u8 {
    if (tok_idx >= doc.tokens.tokens.len) return "";
    const kind = doc.tokens.tokens.items(.kind)[tok_idx];
    const raw = getTomlTokenSlice(doc, tok_idx);
    if (kind == .bare_key) return raw;

    if (is_key and (kind == .multiline_basic_string or kind == .multiline_literal_string)) {
        doc.has_syntax_errors = true;
        const off = getTokenByteOffset(doc, tok_idx);
        try emitTomlDiag(
            sink,
            diag_code,
            doc.file_id,
            doc.base_byte_offset,
            off,
            off + raw.len,
            "TOML v1.0 forbids multiline strings (`\"\"\"` / `'''`) as table or entry keys",
        );
    }

    if (kind == .literal_string) {
        return if (raw.len >= 2) raw[1 .. raw.len - 1] else "";
    }
    if (kind == .multiline_literal_string) {
        if (raw.len < 6) return "";
        var inner = raw[3 .. raw.len - 3];
        if (std.mem.startsWith(u8, inner, "\r\n")) {
            inner = inner[2..];
        } else if (std.mem.startsWith(u8, inner, "\n")) {
            inner = inner[1..];
        }
        if (std.mem.indexOf(u8, inner, "\r\n") == null) return inner;

        var norm_out: std.ArrayList(u8) = .empty;
        defer norm_out.deinit(arena.backing_allocator);
        try norm_out.ensureTotalCapacity(arena.backing_allocator, inner.len);
        var scan_i: usize = 0;
        while (scan_i < inner.len) {
            if (inner[scan_i] == '\r' and scan_i + 1 < inner.len and inner[scan_i + 1] == '\n') {
                norm_out.appendAssumeCapacity('\n');
                scan_i += 2;
            } else {
                norm_out.appendAssumeCapacity(inner[scan_i]);
                scan_i += 1;
            }
        }
        return arena.dupe(u8, norm_out.items);
    }

    const is_multi = kind == .multiline_basic_string;
    const delim_len: usize = if (is_multi) 3 else 1;
    if (raw.len < delim_len * 2) return "";
    var inner = raw[delim_len .. raw.len - delim_len];
    if (is_multi) {
        if (std.mem.startsWith(u8, inner, "\r\n")) {
            inner = inner[2..];
        } else if (std.mem.startsWith(u8, inner, "\n")) {
            inner = inner[1..];
        }
    }
    if (std.mem.indexOfScalar(u8, inner, '\\') == null and std.mem.indexOf(u8, inner, "\r\n") == null) {
        return inner;
    }

    var out: std.ArrayList(u8) = .empty;
    defer out.deinit(arena.backing_allocator);
    var i: usize = 0;
    while (i < inner.len) {
        if (is_multi and inner[i] == '\r' and i + 1 < inner.len and inner[i + 1] == '\n') {
            try out.append(arena.backing_allocator, '\n');
            i += 2;
            continue;
        }
        if (inner[i] != '\\') {
            try out.append(arena.backing_allocator, inner[i]);
            i += 1;
            continue;
        }
        i += 1;
        if (i >= inner.len) break;
        const esc = inner[i];
        if (is_multi and (esc == ' ' or esc == '\t' or esc == '\r' or esc == '\n')) {
            var has_nl = false;
            while (i < inner.len and (inner[i] == ' ' or inner[i] == '\t' or inner[i] == '\r' or inner[i] == '\n')) : (i += 1) {
                if (inner[i] == '\n') has_nl = true;
            }
            if (!has_nl) {
                doc.has_syntax_errors = true;
                const off = doc.tokens.tokens.items(.byte_offset)[tok_idx];
                try emitTomlDiag(
                    sink,
                    diag_code,
                    doc.file_id,
                    doc.base_byte_offset,
                    off,
                    off + raw.len,
                    "invalid line-ending backslash escape in multiline TOML string",
                );
            }
            continue;
        }
        switch (esc) {
            'b' => {
                try out.append(arena.backing_allocator, 0x08);
                i += 1;
            },
            't' => {
                try out.append(arena.backing_allocator, '\t');
                i += 1;
            },
            'n' => {
                try out.append(arena.backing_allocator, '\n');
                i += 1;
            },
            'f' => {
                try out.append(arena.backing_allocator, 0x0C);
                i += 1;
            },
            'r' => {
                try out.append(arena.backing_allocator, '\r');
                i += 1;
            },
            '"' => {
                try out.append(arena.backing_allocator, '"');
                i += 1;
            },
            '\\' => {
                try out.append(arena.backing_allocator, '\\');
                i += 1;
            },
            'u', 'U' => {
                const hex_digits: usize = if (esc == 'u') 4 else 8;
                i += 1;
                if (i + hex_digits <= inner.len) {
                    if (std.fmt.parseInt(u21, inner[i .. i + hex_digits], 16)) |cp_val| {
                        if (std.unicode.utf8ValidCodepoint(cp_val)) {
                            var utf8_buf: [4]u8 = undefined;
                            const enc_len = std.unicode.utf8Encode(cp_val, &utf8_buf) catch 0;
                            try out.appendSlice(arena.backing_allocator, utf8_buf[0..enc_len]);
                            i += hex_digits;
                            continue;
                        }
                    } else |_| {}
                }
                doc.has_syntax_errors = true;
                const off = doc.tokens.tokens.items(.byte_offset)[tok_idx];
                try emitTomlDiag(
                    sink,
                    diag_code,
                    doc.file_id,
                    doc.base_byte_offset,
                    off,
                    off + raw.len,
                    "invalid `\\uXXXX` / `\\UXXXXXXXX` Unicode scalar escape in TOML string",
                );
            },
            else => {
                doc.has_syntax_errors = true;
                const off = doc.tokens.tokens.items(.byte_offset)[tok_idx];
                try emitTomlDiag(
                    sink,
                    diag_code,
                    doc.file_id,
                    doc.base_byte_offset,
                    off,
                    off + raw.len,
                    "unknown escape sequence in TOML basic string",
                );
                i += 1;
            },
        }
    }
    return arena.dupe(u8, out.items);
}

/// Parses a TOML integer token (`0x`, `0o`, `0b`, or `_`-separated decimal) into `int_val` or `uint_val`.
fn decodeTomlInteger(raw_atom: []const u8) ?TomlDomValue {
    var clean_buf: [128]u8 = undefined;
    var clean_len: usize = 0;
    for (raw_atom) |ch_b| {
        if (ch_b == '_') continue;
        if (clean_len >= clean_buf.len) return null;
        clean_buf[clean_len] = ch_b;
        clean_len += 1;
    }
    const clean = clean_buf[0..clean_len];
    if (std.mem.startsWith(u8, clean, "0x")) {
        return .{ .uint_val = std.fmt.parseInt(u64, clean[2..], 16) catch return null };
    }
    if (std.mem.startsWith(u8, clean, "0o")) {
        return .{ .uint_val = std.fmt.parseInt(u64, clean[2..], 8) catch return null };
    }
    if (std.mem.startsWith(u8, clean, "0b")) {
        return .{ .uint_val = std.fmt.parseInt(u64, clean[2..], 2) catch return null };
    }
    if (clean.len > 0 and clean[0] == '-') {
        return .{ .int_val = std.fmt.parseInt(i64, clean, 10) catch return null };
    }
    const digits = if (clean.len > 0 and clean[0] == '+') clean[1..] else clean;
    if (std.fmt.parseInt(u64, digits, 10)) |unsigned_val| {
        if (unsigned_val <= std.math.maxInt(i64)) {
            return .{ .int_val = @intCast(unsigned_val) };
        }
        return .{ .uint_val = unsigned_val };
    } else |_| {
        return null;
    }
}

/// Stateful recursive-descent CST & `TomlDomTable` builder bounded by `MAX_TOML_DEPTH`.
const TomlParser = struct {
    /// Backing allocator for SoA CST arrays.
    allocator: std.mem.Allocator,
    /// Arena owning `TomlDomTable` / `TomlDomValue` nodes and decoded strings.
    dom_arena: *BumpArena,
    /// Target `TomlDocumentView` being populated.
    doc: *TomlDocumentView,
    /// Diagnostic code (`E0013` or `E0014`) emitted on errors.
    diag_code: DiagnosticCode,
    /// Optional diagnostic sink.
    sink: ?*DiagnosticSink,
    /// Current index in `doc.tokens.tokens`.
    pos: u32 = 0,

    /// Peeks the `TomlTokenKind` at `self.pos`, returning `.eof` when `self.pos >= tokens.len`.
    inline fn peekKind(self: *const TomlParser) TomlTokenKind {
        if (self.pos >= self.doc.tokens.tokens.len) return .eof;
        return self.doc.tokens.tokens.items(.kind)[self.pos];
    }

    /// Peeks the `TomlTokenFlags` at `self.pos`, returning default flags when `self.pos >= tokens.len`.
    inline fn peekFlags(self: *const TomlParser) TomlTokenFlags {
        if (self.pos >= self.doc.tokens.tokens.len) return .{};
        return self.doc.tokens.tokens.items(.flags)[self.pos];
    }

    /// Returns the `TomlTokenFlags` at `tok_idx` safely when `tok_idx < tokens.len`.
    inline fn getTokenFlagsAt(self: *const TomlParser, tok_idx: u32) TomlTokenFlags {
        if (tok_idx >= self.doc.tokens.tokens.len) return .{};
        return self.doc.tokens.tokens.items(.flags)[tok_idx];
    }

    /// Returns `true` if `kind` is a valid TOML key token.
    inline fn isKeyToken(kind: TomlTokenKind) bool {
        return kind == .bare_key or kind == .basic_string or kind == .literal_string or
            kind == .multiline_basic_string or kind == .multiline_literal_string;
    }

    /// Appends a pre-order `TomlCstNode` placeholder and returns its index.
    fn beginCstNode(self: *TomlParser, kind: TomlCstKind, first_tok: u32) !u32 {
        const idx: u32 = @intCast(self.doc.cst.nodes.len);
        try self.doc.cst.nodes.append(self.allocator, .{
            .kind = kind,
            .first_token = first_tok,
            .last_token = first_tok,
            .subtree_size = 1,
        });
        return idx;
    }

    /// Finalizes `node_idx`'s `last_token`, `subtree_size`, `eq_align_col`, and `flags`.
    fn finishCstNode(
        self: *TomlParser,
        node_idx: u32,
        last_tok: u32,
        eq_col: u16,
        flags: TomlCstFlags,
    ) void {
        const total_now: u32 = @intCast(self.doc.cst.nodes.len);
        self.doc.cst.nodes.items(.last_token)[node_idx] = last_tok;
        self.doc.cst.nodes.items(.subtree_size)[node_idx] = total_now - node_idx;
        self.doc.cst.nodes.items(.eq_align_col)[node_idx] = eq_col;
        self.doc.cst.nodes.items(.flags)[node_idx] = flags;
    }

    /// Parses a dotted or simple key path (`1..32` segments) into `out_keys`.
    fn parseKeyPath(
        self: *TomlParser,
        out_keys: *[32][]const u8,
        out_spans: *[32]Span,
    ) !struct { len: usize, first_tok: u32, last_tok: u32, cst_idx: u32 } {
        const first_tok = self.pos;
        const cst_idx = try self.beginCstNode(.dotted_key, first_tok);
        var count: usize = 0;

        while (count < out_keys.len and isKeyToken(self.peekKind())) {
            const key_tok = self.pos;
            self.pos += 1;
            out_keys[count] = try decodeTomlStringOrKey(
                self.dom_arena,
                self.doc,
                key_tok,
                true,
                self.diag_code,
                self.sink,
            );
            out_spans[count] = getTomlTokenRangeSpan(self.doc, key_tok, key_tok);
            count += 1;
            if (self.peekKind() == .dot) {
                self.pos += 1;
                if (!isKeyToken(self.peekKind())) {
                    self.doc.has_syntax_errors = true;
                    break;
                }
            } else {
                break;
            }
        }

        const last_tok = if (self.pos > first_tok) self.pos - 1 else first_tok;
        self.finishCstNode(cst_idx, last_tok, 0, .{});
        return .{ .len = count, .first_tok = first_tok, .last_tok = last_tok, .cst_idx = cst_idx };
    }

    /// Records a `24B` `TomlSpanAnchor` in `doc.cst.anchors` and returns its `u32` index.
    fn recordAnchor(
        self: *TomlParser,
        key_first_tok: u32,
        val_first_tok: u32,
        val_last_tok: u32,
        eq_col: u16,
        form: u8,
        has_cve: bool,
        is_trailing_comma: bool,
    ) !u32 {
        const kinds = self.doc.tokens.tokens.items(.kind);
        const key_rel = getTokenByteOffset(self.doc, key_first_tok);
        const val_first_rel = getTokenByteOffset(self.doc, val_first_tok);
        const val_last_rel = getTokenByteOffset(self.doc, val_last_tok);
        const key_lo = self.doc.base_byte_offset +| key_rel;
        const val_lo = self.doc.base_byte_offset +| val_first_rel;
        const last_slice = getTomlTokenSlice(self.doc, val_last_tok);
        const val_hi = self.doc.base_byte_offset +| val_last_rel +| @as(u32, @intCast(last_slice.len));
        const row_end = computeRowEndByte(self.doc, val_last_rel);

        var anchor_flags: u8 = 0;
        if (has_cve) anchor_flags |= 0x01;
        if (val_first_tok < kinds.len and
            (kinds[val_first_tok] == .literal_string or kinds[val_first_tok] == .multiline_literal_string))
        {
            anchor_flags |= 0x02;
        }
        if (self.doc.is_script_frontmatter) anchor_flags |= 0x08;
        if (is_trailing_comma) anchor_flags |= 0x10;

        const id: u32 = @intCast(self.doc.cst.anchors.items.len);
        try self.doc.cst.anchors.append(self.allocator, .{
            .file_id = self.doc.file_id,
            .key_lo = key_lo,
            .val_lo = val_lo,
            .val_hi = val_hi,
            .row_end = row_end,
            .eq_col = eq_col,
            .form = form,
            .flags = anchor_flags,
        });
        return id;
    }

    /// Parses any TOML value (`scalar`, `[…]` array, or `{…}` inline table) bounded by `depth <= MAX_TOML_DEPTH`.
    fn parseValue(self: *TomlParser, depth: u8) anyerror!struct {
        val: TomlDomValue,
        first_tok: u32,
        last_tok: u32,
        has_cve: bool,
    } {
        if (depth > MAX_TOML_DEPTH) {
            self.doc.has_syntax_errors = true;
            return .{ .val = .{ .bool_val = false }, .first_tok = self.pos, .last_tok = self.pos, .has_cve = false };
        }

        const start_tok = self.pos;
        const kind = self.peekKind();
        if (kind == .eof) {
            self.doc.has_syntax_errors = true;
            return .{ .val = .{ .str_val = "" }, .first_tok = start_tok, .last_tok = start_tok, .has_cve = false };
        }
        const tok_flags = self.getTokenFlagsAt(start_tok);

        // [1] Array `[ elem, … ]`:
        if (kind == .lbracket) {
            const arr_cst = try self.beginCstNode(.array, start_tok);
            self.pos += 1;
            var elems: std.ArrayList(TomlDomElem) = .empty;
            defer elems.deinit(self.dom_arena.backing_allocator);
            var has_trailing_comma = false;
            var has_any_cve = tok_flags.has_cve_comment;

            while (self.peekKind() != .rbracket and self.peekKind() != .eof) {
                has_trailing_comma = false;
                const parsed_elem = try self.parseValue(depth + 1);
                var has_elem_cve = parsed_elem.has_cve;
                var has_seen_comma = false;
                if (self.peekKind() == .comma) {
                    const comma_flags = self.peekFlags();
                    if (comma_flags.has_cve_comment) has_elem_cve = true;
                    has_seen_comma = true;
                    self.pos += 1;
                    if (self.peekKind() == .rbracket) has_trailing_comma = true;
                }
                if (has_elem_cve) has_any_cve = true;
                const elem_anchor = try self.recordAnchor(
                    parsed_elem.first_tok,
                    parsed_elem.first_tok,
                    parsed_elem.last_tok,
                    0,
                    4,
                    has_elem_cve,
                    has_seen_comma,
                );
                try elems.append(self.dom_arena.backing_allocator, .{
                    .val = parsed_elem.val,
                    .span = getTomlTokenRangeSpan(self.doc, parsed_elem.first_tok, parsed_elem.last_tok),
                    .anchor_id = elem_anchor,
                    .has_cve_advisory = has_elem_cve,
                });
                if (!has_seen_comma and self.peekKind() != .rbracket) {
                    self.doc.has_syntax_errors = true;
                    break;
                }
            }
            const end_tok = self.pos;
            if (self.peekKind() == .rbracket) self.pos += 1 else self.doc.has_syntax_errors = true;
            self.finishCstNode(arr_cst, end_tok, 0, .{
                .has_trailing_comma = has_trailing_comma,
                .has_cve_advisory = has_any_cve,
            });
            return .{
                .val = .{ .array_val = try self.dom_arena.dupe(TomlDomElem, elems.items) },
                .first_tok = start_tok,
                .last_tok = end_tok,
                .has_cve = has_any_cve,
            };
        }

        // [2] Inline table `{ key = val, … }`:
        if (kind == .lbrace) {
            const tbl_cst = try self.beginCstNode(.inline_table, start_tok);
            self.pos += 1;
            const inline_tbl = try self.dom_arena.create(TomlDomTable);
            inline_tbl.* = .{
                .is_inline_sealed = false,
                .header_span = getTomlTokenRangeSpan(self.doc, start_tok, start_tok),
            };
            var has_any_cve = tok_flags.has_cve_comment;

            while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
                const kv_start = self.pos;
                const kv_cst = try self.beginCstNode(.key_value, kv_start);
                var keys: [32][]const u8 = undefined;
                var key_spans: [32]Span = undefined;
                const key_res = try self.parseKeyPath(&keys, &key_spans);
                if (key_res.len == 0 or self.peekKind() != .eq) {
                    self.doc.has_syntax_errors = true;
                    break;
                }
                const eq_tok = self.pos;
                const eq_col = computeUtf8Column(
                    self.doc.toml_slice,
                    getTokenByteOffset(self.doc, eq_tok),
                );
                self.pos += 1;

                const rhs = try self.parseValue(depth + 1);
                if (rhs.has_cve) has_any_cve = true;
                const inner_anchor = try self.recordAnchor(
                    key_res.first_tok,
                    rhs.first_tok,
                    rhs.last_tok,
                    eq_col,
                    1,
                    rhs.has_cve,
                    false,
                );
                self.finishCstNode(kv_cst, rhs.last_tok, eq_col, .{
                    .is_inline_table_entry = true,
                    .has_cve_advisory = rhs.has_cve,
                });
                try self.insertDottedKeyValue(
                    inline_tbl,
                    keys[0..key_res.len],
                    key_spans[0..key_res.len],
                    getTomlTokenRangeSpan(self.doc, rhs.first_tok, rhs.last_tok),
                    rhs.val,
                    inner_anchor,
                );

                if (self.peekKind() == .comma) {
                    self.pos += 1;
                } else if (self.peekKind() != .rbrace) {
                    self.doc.has_syntax_errors = true;
                    break;
                }
            }
            inline_tbl.is_inline_sealed = true;
            const end_tok = self.pos;
            if (self.peekKind() == .rbrace) self.pos += 1 else self.doc.has_syntax_errors = true;
            self.finishCstNode(tbl_cst, end_tok, 0, .{ .has_cve_advisory = has_any_cve });
            return .{
                .val = .{ .table_val = inline_tbl },
                .first_tok = start_tok,
                .last_tok = end_tok,
                .has_cve = has_any_cve,
            };
        }

        // [3] Scalar token:
        const scalar_cst = try self.beginCstNode(.scalar, start_tok);
        const raw = getTomlTokenSlice(self.doc, start_tok);
        self.pos += 1;
        self.finishCstNode(scalar_cst, start_tok, 0, .{ .has_cve_advisory = tok_flags.has_cve_comment });

        const decoded: TomlDomValue = switch (kind) {
            .basic_string, .multiline_basic_string, .literal_string, .multiline_literal_string => .{
                .str_val = try decodeTomlStringOrKey(
                    self.dom_arena,
                    self.doc,
                    start_tok,
                    false,
                    self.diag_code,
                    self.sink,
                ),
            },
            .bool_lit => .{ .bool_val = std.mem.eql(u8, raw, "true") },
            .int_lit => decodeTomlInteger(raw) orelse blk: {
                self.doc.has_syntax_errors = true;
                const off = getTokenByteOffset(self.doc, start_tok);
                try emitTomlDiag(
                    self.sink,
                    self.diag_code,
                    self.doc.file_id,
                    self.doc.base_byte_offset,
                    off,
                    off + raw.len,
                    "TOML integer literal overflows 64-bit integer range",
                );
                break :blk .{ .int_val = 0 };
            },
            .float_lit => blk: {
                var clean_buf: [128]u8 = undefined;
                var clean_len: usize = 0;
                for (raw) |ch_b| {
                    if (ch_b != '_' and clean_len < clean_buf.len) {
                        clean_buf[clean_len] = ch_b;
                        clean_len += 1;
                    }
                }
                break :blk .{ .float_val = std.fmt.parseFloat(f64, clean_buf[0..clean_len]) catch 0.0 };
            },
            .datetime_lit => .{ .datetime_val = raw },
            else => blk: {
                self.doc.has_syntax_errors = true;
                break :blk .{ .str_val = "" };
            },
        };
        return .{
            .val = decoded,
            .first_tok = start_tok,
            .last_tok = start_tok,
            .has_cve = tok_flags.has_cve_comment,
        };
    }

    /// Inserts a `keys` assignment into `base_table`, rejecting duplicate keys and sealed-table mutations.
    fn insertDottedKeyValue(
        self: *TomlParser,
        base_table: *TomlDomTable,
        keys: []const []const u8,
        key_spans: []const Span,
        val_span: Span,
        val: TomlDomValue,
        anchor_id: u32,
    ) !void {
        var cur_tbl = base_table;
        var seg_idx: usize = 0;
        while (seg_idx + 1 < keys.len) : (seg_idx += 1) {
            const seg = keys[seg_idx];
            if (cur_tbl.findEntry(seg)) |existing| {
                switch (existing.val) {
                    .table_val => |sub_tbl| {
                        if (sub_tbl.is_inline_sealed or sub_tbl.is_explicitly_defined) {
                            self.doc.has_syntax_errors = true;
                            try self.emitSpanErr(key_spans[seg_idx], "cannot extend inline or explicitly defined TOML table via dotted key");
                            return;
                        }
                        cur_tbl = sub_tbl;
                    },
                    else => {
                        self.doc.has_syntax_errors = true;
                        try self.emitSpanErr(key_spans[seg_idx], "TOML dotted key conflicts with existing scalar/array key");
                        return;
                    },
                }
            } else {
                const sub_tbl = try self.dom_arena.create(TomlDomTable);
                sub_tbl.* = .{ .header_span = key_spans[seg_idx] };
                try cur_tbl.appendEntry(self.dom_arena.asAllocator(), .{
                    .key = seg,
                    .key_span = key_spans[seg_idx],
                    .val_span = key_spans[seg_idx],
                    .val = .{ .table_val = sub_tbl },
                });
                cur_tbl = sub_tbl;
            }
        }

        const leaf_key = keys[keys.len - 1];
        const leaf_span = key_spans[keys.len - 1];
        if (cur_tbl.findEntry(leaf_key) != null) {
            self.doc.has_syntax_errors = true;
            try self.emitSpanErr(leaf_span, "duplicate TOML key in table");
            return;
        }
        try cur_tbl.appendEntry(self.dom_arena.asAllocator(), .{
            .key = leaf_key,
            .key_span = leaf_span,
            .val_span = val_span,
            .val = val,
            .anchor_id = anchor_id,
        });
    }

    /// Resolves `[path]` or `[[path]]` table headers against `root_tbl` per TOML v1.0 table rules.
    fn resolveTableHeader(
        self: *TomlParser,
        root_tbl: *TomlDomTable,
        keys: []const []const u8,
        key_spans: []const Span,
        is_array_table: bool,
        hdr_span: Span,
    ) !*TomlDomTable {
        var cur_tbl = root_tbl;
        var i: usize = 0;
        while (i + 1 < keys.len) : (i += 1) {
            const seg = keys[i];
            if (cur_tbl.findEntry(seg)) |existing| {
                switch (existing.val) {
                    .table_val => |sub_tbl| {
                        if (sub_tbl.is_inline_sealed) {
                            self.doc.has_syntax_errors = true;
                            try self.emitSpanErr(key_spans[i], "cannot reopen inline `{ … }` TOML table with `[…]` header");
                            return cur_tbl;
                        }
                        cur_tbl = sub_tbl;
                    },
                    .array_val => |arr_elems| {
                        if (arr_elems.len == 0 or arr_elems[arr_elems.len - 1].val != .table_val) {
                            self.doc.has_syntax_errors = true;
                            try self.emitSpanErr(key_spans[i], "cannot append subtable onto static TOML array");
                            return cur_tbl;
                        }
                        cur_tbl = arr_elems[arr_elems.len - 1].val.table_val;
                    },
                    else => {
                        self.doc.has_syntax_errors = true;
                        try self.emitSpanErr(key_spans[i], "TOML `[table]` header conflicts with scalar key");
                        return cur_tbl;
                    },
                }
            } else {
                const sub_tbl = try self.dom_arena.create(TomlDomTable);
                sub_tbl.* = .{ .is_super_table = true, .header_span = key_spans[i] };
                try cur_tbl.appendEntry(self.dom_arena.asAllocator(), .{
                    .key = seg,
                    .key_span = key_spans[i],
                    .val_span = hdr_span,
                    .val = .{ .table_val = sub_tbl },
                    .is_explicit_header = true,
                });
                cur_tbl = sub_tbl;
            }
        }

        const leaf = keys[keys.len - 1];
        const leaf_span = key_spans[keys.len - 1];
        if (is_array_table) {
            const elem_tbl = try self.dom_arena.create(TomlDomTable);
            elem_tbl.* = .{ .is_explicitly_defined = true, .header_span = hdr_span };
            if (cur_tbl.findEntry(leaf)) |existing| {
                if (!existing.is_explicit_header or existing.val != .array_val) {
                    self.doc.has_syntax_errors = true;
                    try self.emitSpanErr(leaf_span, "`[[array_table]]` conflicts with existing key or table");
                    return elem_tbl;
                }
                try existing.array_table_buf.append(
                    self.dom_arena.asAllocator(),
                    .{ .val = .{ .table_val = elem_tbl }, .span = hdr_span },
                );
                existing.val = .{ .array_val = existing.array_table_buf.items };
            } else {
                var arr_buf: std.ArrayListUnmanaged(TomlDomElem) = .empty;
                try arr_buf.append(
                    self.dom_arena.asAllocator(),
                    .{ .val = .{ .table_val = elem_tbl }, .span = hdr_span },
                );
                try cur_tbl.appendEntry(self.dom_arena.asAllocator(), .{
                    .key = leaf,
                    .key_span = leaf_span,
                    .val_span = hdr_span,
                    .val = .{ .array_val = arr_buf.items },
                    .array_table_buf = arr_buf,
                    .is_explicit_header = true,
                });
            }
            return elem_tbl;
        }

        if (cur_tbl.findEntry(leaf)) |existing| {
            if (existing.val == .table_val) {
                const sub_tbl = existing.val.table_val;
                if (sub_tbl.is_super_table and !sub_tbl.is_explicitly_defined and !sub_tbl.is_inline_sealed) {
                    sub_tbl.is_explicitly_defined = true;
                    sub_tbl.header_span = hdr_span;
                    return sub_tbl;
                }
            }
            self.doc.has_syntax_errors = true;
            try self.emitSpanErr(leaf_span, "duplicate or conflicting `[table]` header in TOML document");
            const dummy_tbl = try self.dom_arena.create(TomlDomTable);
            dummy_tbl.* = .{ .header_span = hdr_span };
            return dummy_tbl;
        }

        const new_tbl = try self.dom_arena.create(TomlDomTable);
        new_tbl.* = .{ .is_explicitly_defined = true, .header_span = hdr_span };
        try cur_tbl.appendEntry(self.dom_arena.asAllocator(), .{
            .key = leaf,
            .key_span = leaf_span,
            .val_span = hdr_span,
            .val = .{ .table_val = new_tbl },
            .is_explicit_header = true,
        });
        return new_tbl;
    }

    /// Emits `self.diag_code` at `span`.
    fn emitSpanErr(self: *TomlParser, span: Span, msg: []const u8) !void {
        if (self.sink) |diag_sink| {
            try diag_sink.emit(.{
                .code = self.diag_code,
                .severity = .err,
                .primary_span = span,
                .message = msg,
            });
        }
    }

    /// Parses the entire token stream into `doc.cst` and returns the root `*TomlDomTable`.
    fn parseDocument(self: *TomlParser) !*TomlDomTable {
        const root_tbl = try self.dom_arena.create(TomlDomTable);
        root_tbl.* = .{ .header_span = Span.init(self.doc.file_id, self.doc.base_byte_offset, self.doc.base_byte_offset) };
        if (self.doc.tokens.tokens.len == 0) return root_tbl;

        const root_cst = try self.beginCstNode(.document, 0);
        var active_tbl = root_tbl;
        var is_in_direct_deps_section = false;

        while (self.peekKind() != .eof) {
            const start_tok = self.pos;
            const kind = self.peekKind();

            if (kind == .lbracket or kind == .double_lbracket) {
                const is_arr = kind == .double_lbracket;
                const hdr_cst = try self.beginCstNode(if (is_arr) .array_table_header else .table_header, start_tok);
                self.pos += 1;
                var keys: [32][]const u8 = undefined;
                var key_spans: [32]Span = undefined;
                const key_res = try self.parseKeyPath(&keys, &key_spans);
                const close_kind: TomlTokenKind = if (is_arr) .double_rbracket else .rbracket;
                const end_tok = self.pos;
                if (self.peekKind() == close_kind) {
                    self.pos += 1;
                } else {
                    self.doc.has_syntax_errors = true;
                }
                if (self.peekKind() != .eof and !self.peekFlags().has_leading_newline) {
                    self.doc.has_syntax_errors = true;
                    try self.emitSpanErr(
                        getTomlTokenRangeSpan(self.doc, self.pos, self.pos),
                        "unexpected token after TOML `[table]` header on the same line",
                    );
                }
                self.finishCstNode(hdr_cst, end_tok, 0, .{});
                const hdr_span = getTomlTokenRangeSpan(self.doc, start_tok, end_tok);
                if (key_res.len > 0) {
                    active_tbl = try self.resolveTableHeader(
                        root_tbl,
                        keys[0..key_res.len],
                        key_spans[0..key_res.len],
                        is_arr,
                        hdr_span,
                    );
                    is_in_direct_deps_section = (!is_arr and key_res.len == 1 and
                        std.mem.eql(u8, keys[0], "dependencies"));
                    if (is_in_direct_deps_section) {
                        self.doc.deps_section_insert_byte = computeRowEndByte(
                            self.doc,
                            getTokenByteOffset(self.doc, end_tok),
                        );
                    }
                }
                continue;
            }

            if (isKeyToken(kind)) {
                const kv_cst = try self.beginCstNode(.key_value, start_tok);
                var keys: [32][]const u8 = undefined;
                var key_spans: [32]Span = undefined;
                const key_res = try self.parseKeyPath(&keys, &key_spans);
                if (key_res.len == 0 or self.peekKind() != .eq) {
                    self.doc.has_syntax_errors = true;
                    if (self.peekKind() != .eof) self.pos += 1;
                    self.finishCstNode(kv_cst, start_tok, 0, .{ .has_error = true });
                    continue;
                }
                const eq_tok = self.pos;
                const eq_col = computeUtf8Column(
                    self.doc.toml_slice,
                    getTokenByteOffset(self.doc, eq_tok),
                );
                self.pos += 1;

                const rhs = try self.parseValue(0);
                if (self.peekKind() != .eof and !self.peekFlags().has_leading_newline) {
                    self.doc.has_syntax_errors = true;
                    try self.emitSpanErr(
                        getTomlTokenRangeSpan(self.doc, self.pos, self.pos),
                        "unexpected trailing token after TOML value on the same line",
                    );
                }
                const has_lead_cve = self.getTokenFlagsAt(start_tok).has_cve_comment;
                const form_code: u8 = if (rhs.val == .table_val)
                    1
                else if (key_res.len > 1)
                    2
                else if (active_tbl != root_tbl)
                    3
                else
                    0;

                const anchor_id = try self.recordAnchor(
                    key_res.first_tok,
                    rhs.first_tok,
                    rhs.last_tok,
                    eq_col,
                    form_code,
                    has_lead_cve or rhs.has_cve,
                    false,
                );
                self.finishCstNode(kv_cst, rhs.last_tok, eq_col, .{
                    .has_cve_advisory = has_lead_cve or rhs.has_cve,
                });
                try self.insertDottedKeyValue(
                    active_tbl,
                    keys[0..key_res.len],
                    key_spans[0..key_res.len],
                    getTomlTokenRangeSpan(self.doc, rhs.first_tok, rhs.last_tok),
                    rhs.val,
                    anchor_id,
                );
                if (is_in_direct_deps_section) {
                    self.doc.deps_section_insert_byte = computeRowEndByte(
                        self.doc,
                        getTokenByteOffset(self.doc, rhs.last_tok),
                    );
                    if (self.doc.deps_section_eq_col == 0) {
                        self.doc.deps_section_eq_col = eq_col;
                    }
                }
                continue;
            }

            // Skip invalid/unexpected token to prevent infinite loops:
            self.doc.has_syntax_errors = true;
            self.pos += 1;
        }

        const final_tok: u32 = @intCast(self.doc.tokens.tokens.len - 1);
        self.finishCstNode(root_cst, final_tok, 0, .{ .has_error = self.doc.has_syntax_errors });
        return root_tbl;
    }
};

// ------------- Target `@cfg` & Capability Helpers -------------

/// Translates common Rust-style `cfg(target_os = "linux")` predicates into CoreX `@cfg` syntax for autofixes.
fn suggestCorexTargetCfgFromRust(arena: *BumpArena, raw_pred: []const u8) !?[]const u8 {
    var inner = std.mem.trim(u8, raw_pred, " \t");
    if (std.mem.startsWith(u8, inner, "cfg(") and std.mem.endsWith(u8, inner, ")")) {
        inner = std.mem.trim(u8, inner[4 .. inner.len - 1], " \t");
    }
    if (std.mem.eql(u8, inner, "unix")) {
        return try arena.dupe(u8, "target.os is (.Linux | .Macos)");
    }
    if (std.mem.eql(u8, inner, "windows")) {
        return try arena.dupe(u8, "target.os == .Windows");
    }
    const eq_pos = std.mem.indexOfScalar(u8, inner, '=') orelse return null;
    if (eq_pos + 1 < inner.len and inner[eq_pos + 1] == '=') return null;
    const lhs = std.mem.trim(u8, inner[0..eq_pos], " \t");
    const rhs_quoted = std.mem.trim(u8, inner[eq_pos + 1 ..], " \t");
    if (rhs_quoted.len < 2 or (rhs_quoted[0] != '\'' and rhs_quoted[0] != '"') or
        rhs_quoted[rhs_quoted.len - 1] != rhs_quoted[0])
    {
        return null;
    }
    const rhs_val = rhs_quoted[1 .. rhs_quoted.len - 1];
    if (std.mem.eql(u8, lhs, "target_os")) {
        const variant = if (std.mem.eql(u8, rhs_val, "linux"))
            ".Linux"
        else if (std.mem.eql(u8, rhs_val, "macos"))
            ".Macos"
        else if (std.mem.eql(u8, rhs_val, "windows"))
            ".Windows"
        else if (std.mem.eql(u8, rhs_val, "wasi"))
            ".Wasi"
        else if (std.mem.eql(u8, rhs_val, "none") or std.mem.eql(u8, rhs_val, "freestanding"))
            ".Freestanding"
        else
            return null;
        return try std.fmt.allocPrint(arena.asAllocator(), "target.os == {s}", .{variant});
    }
    if (std.mem.eql(u8, lhs, "target_arch")) {
        const variant = if (std.mem.eql(u8, rhs_val, "x86_64"))
            ".X86_64"
        else if (std.mem.eql(u8, rhs_val, "aarch64"))
            ".Aarch64"
        else if (std.mem.eql(u8, rhs_val, "wasm32"))
            ".Wasm32"
        else
            return null;
        return try std.fmt.allocPrint(arena.asAllocator(), "target.arch == {s}", .{variant});
    }
    return null;
}

/// Validates and normalizes a manifest-relative `.cx` source path (`E0013` on `..`, `\`, `:`, or absolute paths).
fn normalizeAndValidateManifestRelPath(raw_path: []const u8) ?[]const u8 {
    if (raw_path.len == 0 or std.mem.indexOfAny(u8, raw_path, "\\*?") != null) return null;
    const stripped = if (std.mem.startsWith(u8, raw_path, "./")) raw_path[2..] else raw_path;
    if (!mir_vm.isValidSandboxedEmbedPath(stripped)) return null;
    return stripped;
}

/// Validates a `[workspace]` relative directory or `/*` glob pattern (`E0013` on `..`, `\`, `:`, or absolute paths).
fn isValidWorkspaceRelPattern(raw_pat: []const u8, is_glob_allowed: bool) bool {
    if (raw_pat.len == 0 or std.mem.indexOfScalar(u8, raw_pat, '\\') != null) return false;
    if (std.mem.eql(u8, raw_pat, ".")) return true;
    if (is_glob_allowed and std.mem.endsWith(u8, raw_pat, "/*")) {
        const prefix = raw_pat[0 .. raw_pat.len - 2];
        return std.mem.indexOfAny(u8, prefix, "*?") == null and mir_vm.isValidSandboxedEmbedPath(prefix);
    }
    return std.mem.indexOfAny(u8, raw_pat, "*?") == null and mir_vm.isValidSandboxedEmbedPath(raw_pat);
}

/// Parses a TOML string array of canonical capabilities (`"unsafe_op"`, rejecting `"unsafe"` / unknown).
fn parseCapabilityElemArray(
    elems: []const TomlDomElem,
    doc: ?*const TomlDocumentView,
    interner: *StringInterner,
    diag_code: DiagnosticCode,
    is_sorted_unique_req: bool,
    out_has_comptime_io: ?*bool,
    sink: ?*DiagnosticSink,
) !?EffectCapabilityMask {
    var mask: u16 = 0;
    var prev_cap: ?[]const u8 = null;

    for (elems) |elem| {
        if (elem.val != .str_val) {
            if (sink) |diag_sink| {
                try diag_sink.emit(.{
                    .code = diag_code,
                    .severity = .err,
                    .primary_span = elem.span,
                    .message = "capability array element must be a string literal",
                });
            }
            return null;
        }
        const cap_name = elem.val.str_val;
        if (std.mem.eql(u8, cap_name, "unsafe")) {
            if (sink) |diag_sink| {
                var fix_slice: [1]SuggestedFix = undefined;
                var fix_count: usize = 0;
                if (diag_code == .e0013_invalid_manifest_or_pkg_name) {
                    if (doc) |doc_view| {
                        if (elem.anchor_id < doc_view.cst.anchors.items.len) {
                            const edit = try buildScalarReplaceEdit(
                                doc_view,
                                interner,
                                doc_view.cst.anchors.items[elem.anchor_id],
                                "unsafe_op",
                            );
                            const edit_arr = try diag_sink.arena.dupe(TextEdit, &.{edit});
                            fix_slice[0] = .{
                                .message = "replace `\"unsafe\"` with canonical `\"unsafe_op\"`",
                                .applicability = .machine_applicable,
                                .priority = .syntax_canonicalization,
                                .edits = edit_arr,
                            };
                            fix_count = 1;
                        }
                    }
                }
                try diag_sink.emit(.{
                    .code = diag_code,
                    .severity = .err,
                    .primary_span = elem.span,
                    .message = "capability `\"unsafe\"` is not valid; write `\"unsafe_op\"` for 1:1 `@std_cap_boundary` parity",
                    .suggestions = fix_slice[0..fix_count],
                });
            }
            return null;
        }

        const is_lockfile_caps = (diag_code == .e0014_lockfile_drift_or_corrupt);
        const cap_bits = (if (is_lockfile_caps)
            LOCKFILE_CAPABILITY_MAP.get(cap_name)
        else
            MANIFEST_CAPABILITY_MAP.get(cap_name)) orelse {
            if (sink) |diag_sink| {
                try diag_sink.emit(.{
                    .code = diag_code,
                    .severity = .err,
                    .primary_span = elem.span,
                    .message = if (is_lockfile_caps)
                        "unknown or non-runtime capability name in `corex.lock` capability list"
                    else
                        "unknown capability name in capability list",
                });
            }
            return null;
        };

        if (prev_cap) |prior| {
            const ord = std.mem.order(u8, prior, cap_name);
            if (ord == .eq or (is_sorted_unique_req and ord == .gt)) {
                if (sink) |diag_sink| {
                    try diag_sink.emit(.{
                        .code = diag_code,
                        .severity = .err,
                        .primary_span = elem.span,
                        .message = "duplicate or non-canonically ordered capability entry",
                    });
                }
                return null;
            }
        }
        prev_cap = cap_name;
        if (std.mem.eql(u8, cap_name, "comptime_io")) {
            if (out_has_comptime_io) |flag_ptr| {
                if (flag_ptr.*) {
                    if (sink) |diag_sink| {
                        try diag_sink.emit(.{
                            .code = diag_code,
                            .severity = .err,
                            .primary_span = elem.span,
                            .message = "duplicate `\"comptime_io\"` capability in capability list",
                        });
                    }
                    return null;
                }
                flag_ptr.* = true;
                continue;
            }
            if (sink) |diag_sink| {
                try diag_sink.emit(.{
                    .code = diag_code,
                    .severity = .err,
                    .primary_span = elem.span,
                    .message = "`\"comptime_io\"` capability is only valid inside dependency `allow_caps`",
                });
            }
            return null;
        }
        if ((mask & cap_bits) != 0) {
            if (sink) |diag_sink| {
                try diag_sink.emit(.{
                    .code = diag_code,
                    .severity = .err,
                    .primary_span = elem.span,
                    .message = "duplicate capability bit in capability list",
                });
            }
            return null;
        }
        mask |= cap_bits;
    }
    return EffectCapabilityMask.fromBits(mask);
}

/// Updates `hasher` with length-prefixed (`u32` LE) UTF-8 bytes.
fn hashLenPrefixedBytes(hasher: *std.crypto.hash.Blake3, bytes: []const u8) void {
    const len_le = std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(@min(bytes.len, std.math.maxInt(u32)))));
    hasher.update(&len_le);
    hasher.update(bytes);
}

/// Updates `hasher` with canonical `SemVer` fields.
fn hashSemVerValue(
    hasher: *std.crypto.hash.Blake3,
    ver: SemVer,
    interner: *const StringInterner,
) void {
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, ver.major)));
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, ver.minor)));
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, ver.patch)));
    hashLenPrefixedBytes(hasher, interner.get(ver.pre));
}

/// Updates `hasher` with canonical `PublishPolicy` encoding.
fn hashPublishPolicy(
    hasher: *std.crypto.hash.Blake3,
    policy: PublishPolicy,
    interner: *const StringInterner,
) void {
    switch (policy) {
        .is_allowed => |is_ok| hasher.update(&[2]u8{ 0, @intFromBool(is_ok) }),
        .registries => |regs| {
            hasher.update(&[1]u8{1});
            hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(regs.len))));
            for (regs) |reg_id| hashLenPrefixedBytes(hasher, interner.get(reg_id));
        },
    }
}

/// Updates `hasher` with canonical `DepSourceSpec` encoding.
fn hashDepSourceSpec(
    hasher: *std.crypto.hash.Blake3,
    source: DepSourceSpec,
    interner: *const StringInterner,
) void {
    switch (source) {
        .registry => |req| {
            hasher.update(&[1]u8{0});
            hasher.update(&[1]u8{req.len});
            for (req.comparators[0..req.len]) |comp| {
                hasher.update(&[1]u8{@backingInt(comp.op)});
                hashSemVerValue(hasher, comp.ver, interner);
            }
        },
        .git => |git_spec| {
            hasher.update(&[1]u8{1});
            hashLenPrefixedBytes(hasher, interner.get(git_spec.url));
            hasher.update(&[1]u8{@backingInt(git_spec.rev_kind)});
            hashLenPrefixedBytes(hasher, interner.get(git_spec.rev_value));
        },
        .path => |path_spec| {
            hasher.update(&[1]u8{2});
            hashLenPrefixedBytes(hasher, interner.get(path_spec.rel_path));
            if (path_spec.version_req) |req| {
                hashDepSourceSpec(hasher, .{ .registry = req }, interner);
            } else {
                hasher.update(&[1]u8{0xFF});
            }
        },
        .workspace_inherit => {
            hasher.update(&[1]u8{3});
        },
    }
}

/// Updates `hasher` with a canonically sorted `DependencySpec` slice (including `has_comptime_io_cap`).
fn hashDependencySlice(
    hasher: *std.crypto.hash.Blake3,
    deps: []const DependencySpec,
    interner: *const StringInterner,
) void {
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(deps.len))));
    for (deps) |dep| {
        hasher.update(&[4]u8{
            @backingInt(dep.kind),
            @intFromBool(dep.has_default_features),
            @intFromBool(dep.is_optional),
            @intFromBool(dep.has_comptime_io_cap),
        });
        hashLenPrefixedBytes(hasher, interner.get(dep.alias_kebab));
        hashLenPrefixedBytes(hasher, interner.get(dep.package_kebab));
        hashDepSourceSpec(hasher, dep.source, interner);
        hashLenPrefixedBytes(hasher, interner.get(dep.target_cfg));
        const allow_bits: u16 = if (dep.allow_caps) |allow_mask| allow_mask.asBits() else 0xFFFF;
        hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u16, allow_bits)));
        hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u16, dep.deny_caps.asBits())));
        hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(dep.features.len))));
        for (dep.features) |feat_id| hashLenPrefixedBytes(hasher, interner.get(feat_id));
    }
}

/// Updates `hasher` with a canonically sorted `ExcludeRule` slice.
fn hashExcludeSlice(
    hasher: *std.crypto.hash.Blake3,
    excludes: []const ExcludeRule,
    interner: *const StringInterner,
) void {
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(excludes.len))));
    for (excludes) |ex_rule| {
        hashLenPrefixedBytes(hasher, interner.get(ex_rule.package_kebab));
        hashDepSourceSpec(hasher, .{ .registry = ex_rule.req }, interner);
    }
}

/// Updates `hasher` with a canonically sorted `PatchSpec` slice.
fn hashPatchSlice(
    hasher: *std.crypto.hash.Blake3,
    patches: []const PatchSpec,
    interner: *const StringInterner,
) void {
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(patches.len))));
    for (patches) |patch_spec| {
        hashLenPrefixedBytes(hasher, interner.get(patch_spec.scope));
        hashLenPrefixedBytes(hasher, interner.get(patch_spec.package_kebab));
        hashDepSourceSpec(hasher, patch_spec.replacement, interner);
    }
}

/// Updates `hasher` with the complete `SecurityPolicy` (including `[security.dev]` and `[security.package.*]`).
fn hashSecurityPolicy(
    hasher: *std.crypto.hash.Blake3,
    sec: SecurityPolicy,
    interner: *const StringInterner,
) void {
    const sec_allow: u16 = if (sec.default_allow_caps) |allow_mask| allow_mask.asBits() else 0xFFFF;
    const dev_allow: u16 = if (sec.dev_default_allow_caps) |dev_mask| dev_mask.asBits() else 0xFFFF;
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u16, sec_allow)));
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u16, sec.deny_caps.asBits())));
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u16, dev_allow)));
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u16, sec.dev_deny_caps.asBits())));
    hasher.update(&[3]u8{
        @backingInt(sec.default_dep_policy),
        @backingInt(sec.enforcement_scope),
        @intFromBool(sec.is_warn_ambient_dead_caps),
    });
    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(sec.package_overrides.len))));
    for (sec.package_overrides) |pkg_ov| {
        hashLenPrefixedBytes(hasher, interner.get(pkg_ov.package_kebab));
        const ov_allow: u16 = if (pkg_ov.allow_caps) |allow_mask| allow_mask.asBits() else 0xFFFF;
        hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u16, ov_allow)));
        hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u16, pkg_ov.deny_caps.asBits())));
    }
}

/// Sorts and deduplicates `StringId` slices in ascending ASCII order of interned text.
fn sortAndDedupStringIds(
    arena: *BumpArena,
    interner: *const StringInterner,
    raw_ids: []const StringId,
) ![]const StringId {
    if (raw_ids.len == 0) return &.{};
    const buf = try arena.dupe(StringId, raw_ids);
    std.mem.sort(StringId, buf, interner, struct {
        /// Orders `StringId`s by ASCII byte order of their interned strings.
        fn lessThan(int_ptr: *const StringInterner, lhs: StringId, rhs: StringId) bool {
            return std.mem.order(u8, int_ptr.get(lhs), int_ptr.get(rhs)) == .lt;
        }
    }.lessThan);
    var out_len: usize = 1;
    var i: usize = 1;
    while (i < buf.len) : (i += 1) {
        if (buf[i] != buf[out_len - 1]) {
            buf[out_len] = buf[i];
            out_len += 1;
        }
    }
    return buf[0..out_len];
}

/// Parses `"b3:<64-lowercase-or-hex>"` into a 32-byte digest (`null` on invalid prefix/hex).
fn parsePrefixedBlake3Hex(raw_str: []const u8) ?[32]u8 {
    if (!std.mem.startsWith(u8, raw_str, "b3:") or raw_str.len != 67) return null;
    var out: [32]u8 = undefined;
    _ = std.fmt.hexToBytes(&out, raw_str[3..]) catch return null;
    return out;
}

/// Parses `"ed25519:<128-hex>"` into a 64-byte signature (`null` on invalid prefix/hex).
fn parsePrefixedEd25519Hex(raw_str: []const u8) ?[64]u8 {
    if (!std.mem.startsWith(u8, raw_str, "ed25519:") or raw_str.len != 136) return null;
    var out: [64]u8 = undefined;
    _ = std.fmt.hexToBytes(&out, raw_str[8..]) catch return null;
    return out;
}

/// Parses a shorthand `"github.com/<org>/<repo>@<ref>"` or `"https://…"` string into `DepSourceSpec`.
fn parseShorthandGitOrReq(
    arena: *BumpArena,
    interner: *StringInterner,
    raw_spec: []const u8,
) !?DepSourceSpec {
    if (std.mem.startsWith(u8, raw_spec, "github.com/") or
        std.mem.startsWith(u8, raw_spec, "gitlab.com/") or
        std.mem.startsWith(u8, raw_spec, "https://") or
        std.mem.startsWith(u8, raw_spec, "git+https://") or
        std.mem.startsWith(u8, raw_spec, "git+ssh://") or
        std.mem.startsWith(u8, raw_spec, "git+file://"))
    {
        var base_url = raw_spec;
        var rev_kind: GitRevKind = .default_head;
        var rev_val: StringId = .empty;

        if (std.mem.lastIndexOfAny(u8, raw_spec, "@#")) |sep_idx| {
            const scheme_end = if (std.mem.indexOf(u8, raw_spec, "://")) |sc_i| sc_i + 3 else 0;
            const is_ssh_at = std.mem.startsWith(u8, raw_spec, "git+ssh://git@") and sep_idx < 16;
            if (!is_ssh_at and sep_idx > scheme_end) {
                const ref_str = raw_spec[sep_idx + 1 ..];
                if (ref_str.len == 0) return null;
                base_url = raw_spec[0..sep_idx];
                if (ref_str.len == 40 and isAllHexAscii(ref_str)) {
                    rev_kind = .rev;
                } else {
                    rev_kind = .tag;
                }
                rev_val = try interner.intern(ref_str);
            }
        }

        const normalized_url = if (std.mem.startsWith(u8, base_url, "github.com/") or
            std.mem.startsWith(u8, base_url, "gitlab.com/"))
            try std.fmt.allocPrint(arena.asAllocator(), "https://{s}", .{base_url})
        else if (std.mem.startsWith(u8, base_url, "git+"))
            base_url[4..]
        else
            base_url;

        return .{
            .git = .{
                .url = try interner.intern(normalized_url),
                .rev_kind = rev_kind,
                .rev_value = rev_val,
            },
        };
    }

    const req = (try VersionReq.parse(interner, raw_spec)) orelse return null;
    return .{ .registry = req };
}

/// Returns `true` if every byte in `slice` is a hexadecimal digit.
fn isAllHexAscii(slice: []const u8) bool {
    if (slice.len == 0) return false;
    for (slice) |ch_b| {
        if (!std.ascii.isHex(ch_b)) return false;
    }
    return true;
}

/// Extracts dependency entries from `[dependencies]`, `[dev-dependencies]`, `[build-dependencies]`, or `[workspace.dependencies]`.
fn parseDependencySection(
    arena: *BumpArena,
    interner: *StringInterner,
    doc: *const TomlDocumentView,
    tbl: *const TomlDomTable,
    dep_kind: DepKind,
    default_cfg: *const CfgEnv,
    out_list: *std.ArrayList(DependencySpec),
    sink: ?*DiagnosticSink,
) !void {
    for (tbl.entries.items) |entry| {
        if (!try validatePackageNameKebab(arena, interner, doc.full_file_bytes, entry.key, entry.key_span, sink)) {
            continue;
        }
        const alias_kebab_id = try interner.intern(entry.key);
        const alias_snake_str = try kebabToSnakeModule(arena, entry.key);
        const module_snake_id = try interner.intern(alias_snake_str);

        if (entry.val == .str_val) {
            const src_spec = (try parseShorthandGitOrReq(arena, interner, entry.val.str_val)) orelse {
                if (sink) |diag_sink| {
                    try diag_sink.emit(.{
                        .code = .e0013_invalid_manifest_or_pkg_name,
                        .severity = .err,
                        .primary_span = entry.val_span,
                        .message = "invalid SemVer requirement or URL shorthand in dependency specification",
                    });
                }
                continue;
            };
            try out_list.append(arena.asAllocator(), .{
                .alias_kebab = alias_kebab_id,
                .module_snake = module_snake_id,
                .package_kebab = alias_kebab_id,
                .kind = dep_kind,
                .source = src_spec,
                .anchor_id = entry.anchor_id,
                .decl_span = entry.val_span,
            });
            continue;
        }

        if (entry.val != .table_val) {
            if (sink) |diag_sink| {
                try diag_sink.emit(.{
                    .code = .e0013_invalid_manifest_or_pkg_name,
                    .severity = .err,
                    .primary_span = entry.val_span,
                    .message = "dependency entry must be a version string or `{ … }` / `[dependencies.<pkg>]` table",
                });
            }
            continue;
        }

        const sub = entry.val.table_val;
        var pkg_kebab_id = alias_kebab_id;
        var ver_req_opt: ?VersionReq = null;
        var git_url_opt: ?StringId = null;
        var git_rev_kind: GitRevKind = .default_head;
        var git_rev_val: StringId = .empty;
        var path_rel_opt: ?StringId = null;
        var is_ws_inherit = false;
        var has_default_feats = true;
        var is_opt = false;
        var feats_slice: []const StringId = &.{};
        var target_cfg_id: StringId = .empty;
        var allow_caps_opt: ?EffectCapabilityMask = null;
        var deny_caps_mask: EffectCapabilityMask = .EMPTY;
        var has_comptime_io = false;
        var detail_anchor = entry.anchor_id;
        var has_entry_err = false;

        for (sub.entries.items) |sub_kv| {
            const sub_k = sub_kv.key;
            if (std.mem.eql(u8, sub_k, "version")) {
                if (sub_kv.val != .str_val) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`version` must be a SemVer requirement string");
                    continue;
                }
                ver_req_opt = (try VersionReq.parse(interner, sub_kv.val.str_val)) orelse blk: {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "invalid SemVer version requirement in `version`");
                    break :blk null;
                };
                if (sub_kv.anchor_id != std.math.maxInt(u32)) detail_anchor = sub_kv.anchor_id;
            } else if (std.mem.eql(u8, sub_k, "package")) {
                if (sub_kv.val != .str_val) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`package` must be a `kebab-case` package name string");
                    continue;
                }
                if (!try validatePackageNameKebab(
                    arena,
                    interner,
                    doc.full_file_bytes,
                    sub_kv.val.str_val,
                    sub_kv.val_span,
                    sink,
                )) {
                    has_entry_err = true;
                    continue;
                }
                pkg_kebab_id = try interner.intern(sub_kv.val.str_val);
            } else if (std.mem.eql(u8, sub_k, "git")) {
                if (sub_kv.val != .str_val or sub_kv.val.str_val.len == 0) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`git` must be a non-empty repository URL string");
                    continue;
                }
                git_url_opt = try interner.intern(sub_kv.val.str_val);
            } else if (std.mem.eql(u8, sub_k, "tag") or std.mem.eql(u8, sub_k, "branch") or std.mem.eql(u8, sub_k, "rev")) {
                if (sub_kv.val != .str_val or sub_kv.val.str_val.len == 0 or git_rev_kind != .default_head) {
                    has_entry_err = true;
                    try emitManifestFieldErr(
                        sink,
                        sub_kv.val_span,
                        "specify at most one non-empty `tag`, `branch`, or `rev` selector on a `git` dependency",
                    );
                    continue;
                }
                git_rev_kind = if (std.mem.eql(u8, sub_k, "tag"))
                    .tag
                else if (std.mem.eql(u8, sub_k, "branch"))
                    .branch
                else
                    .rev;
                git_rev_val = try interner.intern(sub_kv.val.str_val);
            } else if (std.mem.eql(u8, sub_k, "path")) {
                if (sub_kv.val != .str_val or sub_kv.val.str_val.len == 0) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`path` must be a non-empty relative directory string");
                    continue;
                }
                path_rel_opt = try interner.intern(sub_kv.val.str_val);
            } else if (std.mem.eql(u8, sub_k, "workspace")) {
                if (sub_kv.val != .bool_val or !sub_kv.val.bool_val) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`workspace` inheritance key only accepts `workspace = true`");
                    continue;
                }
                is_ws_inherit = true;
            } else if (std.mem.eql(u8, sub_k, "default-features")) {
                if (sub_kv.val != .bool_val) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`default-features` must be a boolean");
                    continue;
                }
                has_default_feats = sub_kv.val.bool_val;
            } else if (std.mem.eql(u8, sub_k, "optional")) {
                if (sub_kv.val != .bool_val) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`optional` must be a boolean");
                    continue;
                }
                is_opt = sub_kv.val.bool_val;
            } else if (std.mem.eql(u8, sub_k, "features")) {
                if (sub_kv.val != .array_val) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`features` must be an array of feature name strings");
                    continue;
                }
                var raw_f: std.ArrayList(StringId) = .empty;
                defer raw_f.deinit(arena.backing_allocator);
                for (sub_kv.val.array_val) |felem| {
                    if (felem.val != .str_val or felem.val.str_val.len == 0) {
                        has_entry_err = true;
                        try emitManifestFieldErr(sink, felem.span, "feature name must be a non-empty string");
                        break;
                    }
                    try raw_f.append(arena.backing_allocator, try interner.intern(felem.val.str_val));
                }
                feats_slice = try sortAndDedupStringIds(arena, interner, raw_f.items);
            } else if (std.mem.eql(u8, sub_k, "target")) {
                if (sub_kv.val != .str_val) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`target` must be a CoreX `@cfg` predicate string");
                    continue;
                }
                const anchor_opt: ?TomlSpanAnchor = if (sub_kv.anchor_id < doc.cst.anchors.items.len)
                    doc.cst.anchors.items[sub_kv.anchor_id]
                else
                    null;
                if ((try validateAndEvalManifestTargetCfg(
                    arena,
                    interner,
                    doc,
                    sub_kv.val.str_val,
                    default_cfg,
                    sub_kv.val_span,
                    anchor_opt,
                    sink,
                )) == null) {
                    has_entry_err = true;
                    continue;
                }
                target_cfg_id = try interner.intern(std.mem.trim(u8, sub_kv.val.str_val, " \t"));
            } else if (std.mem.eql(u8, sub_k, "allow_caps")) {
                if (sub_kv.val != .array_val) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`allow_caps` must be an array of capability strings");
                    continue;
                }
                allow_caps_opt = (try parseCapabilityElemArray(
                    sub_kv.val.array_val,
                    doc,
                    interner,
                    .e0013_invalid_manifest_or_pkg_name,
                    false,
                    &has_comptime_io,
                    sink,
                )) orelse {
                    has_entry_err = true;
                    continue;
                };
            } else if (std.mem.eql(u8, sub_k, "deny_caps")) {
                if (sub_kv.val != .array_val) {
                    has_entry_err = true;
                    try emitManifestFieldErr(sink, sub_kv.val_span, "`deny_caps` must be an array of capability strings");
                    continue;
                }
                deny_caps_mask = (try parseCapabilityElemArray(
                    sub_kv.val.array_val,
                    doc,
                    interner,
                    .e0013_invalid_manifest_or_pkg_name,
                    false,
                    null,
                    sink,
                )) orelse {
                    has_entry_err = true;
                    continue;
                };
            } else {
                has_entry_err = true;
                try emitManifestFieldErr(sink, sub_kv.key_span, "unknown key inside dependency specification table");
            }
        }

        if (has_entry_err) continue;

        const dep_source: DepSourceSpec = if (is_ws_inherit) blk: {
            if (git_url_opt != null or path_rel_opt != null or ver_req_opt != null) {
                try emitManifestFieldErr(
                    sink,
                    entry.val_span,
                    "`workspace = true` dependency cannot simultaneously redeclare `version`, `git`, or `path`",
                );
                continue;
            }
            break :blk .{ .workspace_inherit = .{} };
        } else if (git_url_opt) |g_url| blk: {
            if (path_rel_opt != null) {
                try emitManifestFieldErr(sink, entry.val_span, "dependency cannot specify both `git` and `path`");
                continue;
            }
            break :blk .{ .git = .{ .url = g_url, .rev_kind = git_rev_kind, .rev_value = git_rev_val } };
        } else if (path_rel_opt) |p_rel|
            .{ .path = .{ .rel_path = p_rel, .version_req = ver_req_opt } }
        else if (ver_req_opt) |v_req|
            .{ .registry = v_req }
        else {
            try emitManifestFieldErr(
                sink,
                entry.val_span,
                "dependency table must declare `version`, `git`, `path`, or `workspace = true`",
            );
            continue;
        };

        if (detail_anchor < doc.cst.anchors.items.len and is_opt) {
            doc.cst.anchors.items[detail_anchor].flags |= 0x04;
        }
        try out_list.append(arena.asAllocator(), .{
            .alias_kebab = alias_kebab_id,
            .module_snake = module_snake_id,
            .package_kebab = pkg_kebab_id,
            .kind = dep_kind,
            .source = dep_source,
            .has_default_features = has_default_feats,
            .is_optional = is_opt,
            .features = feats_slice,
            .target_cfg = target_cfg_id,
            .allow_caps = allow_caps_opt,
            .deny_caps = deny_caps_mask,
            .has_comptime_io_cap = has_comptime_io,
            .anchor_id = detail_anchor,
            .decl_span = entry.val_span,
        });
    }
}

/// Emits `E0013` at `span` with `message`.
fn emitManifestFieldErr(sink: ?*DiagnosticSink, span: Span, message: []const u8) !void {
    if (sink) |diag_sink| {
        try diag_sink.emit(.{
            .code = .e0013_invalid_manifest_or_pkg_name,
            .severity = .err,
            .primary_span = span,
            .message = message,
        });
    }
}

// --------------- Tooling Configuration & Globs ----------------

/// Emits a manifest tooling diagnostic (`E0017`–`E0020`) with an optional `help:` footer note.
fn emitToolConfigDiag(
    sink: ?*DiagnosticSink,
    code: DiagnosticCode,
    span: Span,
    message: []const u8,
    help_note_opt: ?[]const u8,
) !void {
    if (sink) |diag_sink| {
        if (help_note_opt) |help_note| {
            const notes = try diag_sink.arena.dupe([]const u8, &.{help_note});
            try diag_sink.emit(.{
                .code = code,
                .severity = .err,
                .primary_span = span,
                .message = message,
                .notes = notes,
            });
        } else {
            try diag_sink.emit(.{
                .code = code,
                .severity = .err,
                .primary_span = span,
                .message = message,
            });
        }
    }
}

/// Sets or clears `byte` inside a 256-bit `[4]u64` character-class bitset.
inline fn setByteClassBit(bits: *[4]u64, byte: u8, is_set: bool) void {
    const word_idx = byte >> 6;
    const mask = @as(u64, 1) << @intCast(byte & 63);
    if (is_set) {
        bits[word_idx] |= mask;
    } else {
        bits[word_idx] &= ~mask;
    }
}

/// Expands `{a,b}` alternations up to `MAX_GLOB_BRACE_EXPANSIONS` (`16`), returning `null` on syntax/cap error.
fn expandGlobBraceBranches(
    arena: *BumpArena,
    raw_pattern: []const u8,
    err_reason_out: *[]const u8,
) !?[]const []const u8 {
    var queue_buf: [MAX_GLOB_BRACE_EXPANSIONS][]const u8 = undefined;
    queue_buf[0] = raw_pattern;
    var queue_len: usize = 1;

    outer: while (true) {
        var target_idx: ?usize = null;
        var open_pos: usize = 0;
        var close_pos: usize = 0;

        for (queue_buf[0..queue_len], 0..) |candidate, q_idx| {
            var scan_i: usize = 0;
            var in_brackets = false;
            var found_open: ?usize = null;
            var brace_depth: u32 = 0;
            var comma_at_top = false;

            while (scan_i < candidate.len) : (scan_i += 1) {
                const ch_byte = candidate[scan_i];
                if (in_brackets) {
                    if (ch_byte == ']') in_brackets = false;
                    continue;
                }
                if (ch_byte == '[') {
                    in_brackets = true;
                    if (scan_i + 1 < candidate.len and
                        (candidate[scan_i + 1] == '!' or candidate[scan_i + 1] == '^'))
                    {
                        scan_i += 1;
                    }
                    if (scan_i + 1 < candidate.len and candidate[scan_i + 1] == ']') {
                        scan_i += 1;
                    }
                    continue;
                }
                if (ch_byte == '{') {
                    if (brace_depth == 0) found_open = scan_i;
                    brace_depth += 1;
                } else if (ch_byte == '}') {
                    if (brace_depth == 0) {
                        err_reason_out.* = "unmatched closing `}` in path glob pattern";
                        return null;
                    }
                    brace_depth -= 1;
                    if (brace_depth == 0 and target_idx == null) {
                        if (!comma_at_top) {
                            err_reason_out.* = "brace alternation `{…}` in path glob requires at least two comma-separated branches";
                            return null;
                        }
                        target_idx = q_idx;
                        open_pos = found_open.?;
                        close_pos = scan_i;
                        break;
                    }
                } else if (ch_byte == ',' and brace_depth == 1) {
                    comma_at_top = true;
                }
            }

            if (in_brackets) {
                err_reason_out.* = "unclosed `[…]` character class in path glob pattern";
                return null;
            }
            if (brace_depth != 0) {
                err_reason_out.* = "unclosed `{…}` brace alternation in path glob pattern";
                return null;
            }
            if (target_idx != null) break;
        }

        const expand_q_idx = target_idx orelse break :outer;
        const source_pat = queue_buf[expand_q_idx];
        const prefix = source_pat[0..open_pos];
        const inner = source_pat[open_pos + 1 .. close_pos];
        const suffix = source_pat[close_pos + 1 ..];

        var parts_buf: [MAX_GLOB_BRACE_EXPANSIONS][]const u8 = undefined;
        var parts_len: usize = 0;
        var part_start: usize = 0;
        var inner_depth: u32 = 0;
        var inner_brackets = false;
        var inner_i: usize = 0;
        while (inner_i <= inner.len) : (inner_i += 1) {
            if (inner_i == inner.len or (inner[inner_i] == ',' and inner_depth == 0 and !inner_brackets)) {
                const branch_part = inner[part_start..inner_i];
                if (branch_part.len == 0) {
                    err_reason_out.* = "empty alternative inside `{…}` path glob pattern is forbidden";
                    return null;
                }
                if (parts_len >= MAX_GLOB_BRACE_EXPANSIONS) {
                    err_reason_out.* = "path glob `{…}` alternation exceeds maximum `16` expansions";
                    return null;
                }
                parts_buf[parts_len] = branch_part;
                parts_len += 1;
                part_start = inner_i + 1;
                continue;
            }
            const inner_ch = inner[inner_i];
            if (inner_brackets) {
                if (inner_ch == ']') inner_brackets = false;
            } else if (inner_ch == '[') {
                inner_brackets = true;
            } else if (inner_ch == '{') {
                inner_depth += 1;
            } else if (inner_ch == '}') {
                inner_depth -|= 1;
            }
        }

        if ((queue_len - 1) + parts_len > MAX_GLOB_BRACE_EXPANSIONS) {
            err_reason_out.* = "path glob `{…}` alternation exceeds maximum `16` expansions";
            return null;
        }

        var next_queue: [MAX_GLOB_BRACE_EXPANSIONS][]const u8 = undefined;
        var next_len: usize = 0;
        for (queue_buf[0..expand_q_idx]) |prior| {
            next_queue[next_len] = prior;
            next_len += 1;
        }
        for (parts_buf[0..parts_len]) |branch_mid| {
            next_queue[next_len] = try std.fmt.allocPrint(
                arena.asAllocator(),
                "{s}{s}{s}",
                .{ prefix, branch_mid, suffix },
            );
            next_len += 1;
        }
        for (queue_buf[expand_q_idx + 1 .. queue_len]) |rest_item| {
            next_queue[next_len] = rest_item;
            next_len += 1;
        }
        queue_buf = next_queue;
        queue_len = next_len;
    }

    return try arena.dupe([]const u8, queue_buf[0..queue_len]);
}

/// Compiles one brace-expanded glob `branch` into a 64-state `SubNfa64` (`null` on invalid syntax or `> 64` states).
fn compileSingleSubNfa64(
    arena: *BumpArena,
    raw_branch: []const u8,
    err_reason_out: *[]const u8,
) !?SubNfa64 {
    var branch = raw_branch;
    while (std.mem.startsWith(u8, branch, "./")) {
        branch = branch[2..];
    }
    if (branch.len == 0) {
        err_reason_out.* = "path glob pattern cannot be empty";
        return null;
    }
    if (branch[0] == '/' or (branch.len >= 2 and std.ascii.isAlphabetic(branch[0]) and branch[1] == ':')) {
        err_reason_out.* = "path glob must be a jailed relative path without leading `/` or drive prefix";
        return null;
    }
    if (std.mem.indexOfScalar(u8, branch, '\\') != null) {
        err_reason_out.* = "path glob must use portable forward-slash `/` separators instead of `\\`";
        return null;
    }
    if (branch[branch.len - 1] == '/' or std.mem.indexOf(u8, branch, "//") != null) {
        err_reason_out.* = "path glob cannot end with `/` or contain empty `//` segments (use `dir/**`)";
        return null;
    }

    var seg_iter = std.mem.splitScalar(u8, branch, '/');
    while (seg_iter.next()) |seg| {
        if (std.mem.eql(u8, seg, "..") or std.mem.eql(u8, seg, ".")) {
            err_reason_out.* = "path traversal segment `..` or `.` is forbidden in `corex.toml` globs";
            return null;
        }
    }

    var classes_buf: [MAX_GLOB_STATES][4]u64 = undefined;
    var direct_eps: [MAX_GLOB_STATES]u64 = @splat(0);
    var self_loop_mask: u64 = 0;
    var advance_mask: u64 = 0;
    var state_count: usize = 0;

    const all_bytes_class: [4]u64 = @splat(std.math.maxInt(u64));
    var non_slash_class: [4]u64 = all_bytes_class;
    setByteClassBit(&non_slash_class, '/', false);
    var slash_only_class: [4]u64 = @splat(0);
    setByteClassBit(&slash_only_class, '/', true);

    var cursor: usize = 0;
    while (cursor < branch.len) {
        // [1] Leading `**/` (`0+` directory prefixes):
        if (cursor == 0 and std.mem.startsWith(u8, branch, "**/")) {
            if (state_count + 2 >= MAX_GLOB_STATES) {
                err_reason_out.* = "path glob exceeds maximum `64`-state NFA complexity cap";
                return null;
            }
            const s_any = state_count;
            const s_slash = state_count + 1;
            classes_buf[s_any] = all_bytes_class;
            self_loop_mask |= (@as(u64, 1) << @intCast(s_any));
            direct_eps[s_any] |= (@as(u64, 1) << @intCast(s_slash)) | (@as(u64, 1) << @intCast(state_count + 2));

            classes_buf[s_slash] = slash_only_class;
            advance_mask |= (@as(u64, 1) << @intCast(s_slash));
            state_count += 2;
            cursor += 3;
            continue;
        }

        // [2] Interior `/**/` (`0+` intermediate directory segments):
        if (std.mem.startsWith(u8, branch[cursor..], "/**/")) {
            if (state_count + 3 >= MAX_GLOB_STATES) {
                err_reason_out.* = "path glob exceeds maximum `64`-state NFA complexity cap";
                return null;
            }
            const s_lead_slash = state_count;
            const s_any = state_count + 1;
            const s_tail_slash = state_count + 2;
            classes_buf[s_lead_slash] = slash_only_class;
            advance_mask |= (@as(u64, 1) << @intCast(s_lead_slash));

            classes_buf[s_any] = all_bytes_class;
            self_loop_mask |= (@as(u64, 1) << @intCast(s_any));
            direct_eps[s_any] |= (@as(u64, 1) << @intCast(s_tail_slash)) | (@as(u64, 1) << @intCast(state_count + 3));

            classes_buf[s_tail_slash] = slash_only_class;
            advance_mask |= (@as(u64, 1) << @intCast(s_tail_slash));
            state_count += 3;
            cursor += 4;
            continue;
        }

        // [3] Trailing `/**` (everything beneath directory):
        if (cursor + 3 == branch.len and std.mem.eql(u8, branch[cursor..], "/**")) {
            if (state_count + 2 >= MAX_GLOB_STATES) {
                err_reason_out.* = "path glob exceeds maximum `64`-state NFA complexity cap";
                return null;
            }
            const s_slash = state_count;
            const s_any = state_count + 1;
            classes_buf[s_slash] = slash_only_class;
            advance_mask |= (@as(u64, 1) << @intCast(s_slash));

            classes_buf[s_any] = all_bytes_class;
            self_loop_mask |= (@as(u64, 1) << @intCast(s_any));
            direct_eps[s_any] |= (@as(u64, 1) << @intCast(state_count + 2));
            state_count += 2;
            cursor += 3;
            continue;
        }

        // [4] Standalone or general `**` vs single `*`:
        if (branch[cursor] == '*') {
            var star_end = cursor + 1;
            while (star_end < branch.len and branch[star_end] == '*') : (star_end += 1) {}
            if (state_count + 1 >= MAX_GLOB_STATES) {
                err_reason_out.* = "path glob exceeds maximum `64`-state NFA complexity cap";
                return null;
            }
            const is_double = (star_end - cursor) >= 2;
            classes_buf[state_count] = if (is_double) all_bytes_class else non_slash_class;
            self_loop_mask |= (@as(u64, 1) << @intCast(state_count));
            direct_eps[state_count] |= (@as(u64, 1) << @intCast(state_count + 1));
            state_count += 1;
            cursor = star_end;
            continue;
        }

        // [5] Single `?` (`1` non-`/` byte):
        if (branch[cursor] == '?') {
            if (state_count + 1 >= MAX_GLOB_STATES) {
                err_reason_out.* = "path glob exceeds maximum `64`-state NFA complexity cap";
                return null;
            }
            classes_buf[state_count] = non_slash_class;
            advance_mask |= (@as(u64, 1) << @intCast(state_count));
            state_count += 1;
            cursor += 1;
            continue;
        }

        // [6] Character class `[abc]` / `[a-z]` / `[!a-z]` / `[^a-z]` (never matches `/`):
        if (branch[cursor] == '[') {
            if (state_count + 1 >= MAX_GLOB_STATES) {
                err_reason_out.* = "path glob exceeds maximum `64`-state NFA complexity cap";
                return null;
            }
            var cls_i = cursor + 1;
            var is_negated = false;
            if (cls_i < branch.len and (branch[cls_i] == '!' or branch[cls_i] == '^')) {
                is_negated = true;
                cls_i += 1;
            }
            var cls_bits: [4]u64 = @splat(0);
            var has_any_cls_item = false;
            while (cls_i < branch.len) {
                if (branch[cls_i] == ']' and has_any_cls_item) break;
                const lo_ch = branch[cls_i];
                has_any_cls_item = true;
                if (cls_i + 2 < branch.len and branch[cls_i + 1] == '-' and branch[cls_i + 2] != ']') {
                    const hi_ch = branch[cls_i + 2];
                    if (lo_ch > hi_ch) {
                        err_reason_out.* = "inverted `[z-a]` character range in path glob pattern";
                        return null;
                    }
                    var range_ch: u16 = lo_ch;
                    while (range_ch <= hi_ch) : (range_ch += 1) {
                        setByteClassBit(&cls_bits, @intCast(range_ch), true);
                    }
                    cls_i += 3;
                } else {
                    setByteClassBit(&cls_bits, lo_ch, true);
                    cls_i += 1;
                }
            }
            if (!has_any_cls_item or cls_i >= branch.len or branch[cls_i] != ']') {
                err_reason_out.* = "unclosed or empty `[…]` character class in path glob pattern";
                return null;
            }
            if (is_negated) {
                for (&cls_bits) |*word| word.* = ~word.*;
            }
            setByteClassBit(&cls_bits, '/', false);
            if ((cls_bits[0] | cls_bits[1] | cls_bits[2] | cls_bits[3]) == 0) {
                err_reason_out.* = "character class `[…]` in path glob matches zero valid non-`/` characters";
                return null;
            }
            classes_buf[state_count] = cls_bits;
            advance_mask |= (@as(u64, 1) << @intCast(state_count));
            state_count += 1;
            cursor = cls_i + 1;
            continue;
        }

        // [7] Exact literal byte:
        if (state_count + 1 >= MAX_GLOB_STATES) {
            err_reason_out.* = "path glob exceeds maximum `64`-state NFA complexity cap";
            return null;
        }
        var lit_bits: [4]u64 = @splat(0);
        setByteClassBit(&lit_bits, branch[cursor], true);
        classes_buf[state_count] = lit_bits;
        advance_mask |= (@as(u64, 1) << @intCast(state_count));
        state_count += 1;
        cursor += 1;
    }

    const total_nfa_states = state_count + 1;
    const eps_closure = try arena.allocSlice(u64, total_nfa_states);
    var s_idx: usize = 0;
    while (s_idx < total_nfa_states) : (s_idx += 1) {
        eps_closure[s_idx] = (@as(u64, 1) << @intCast(s_idx)) | direct_eps[s_idx];
    }

    var changed = true;
    while (changed) {
        changed = false;
        var st_i: usize = 0;
        while (st_i < total_nfa_states) : (st_i += 1) {
            var expanded = eps_closure[st_i];
            var iter_bits = expanded;
            while (iter_bits != 0) {
                const target_bit: u6 = @intCast(@ctz(iter_bits));
                iter_bits &= iter_bits - 1;
                if (target_bit < total_nfa_states) {
                    expanded |= eps_closure[target_bit];
                }
            }
            if (expanded != eps_closure[st_i]) {
                eps_closure[st_i] = expanded;
                changed = true;
            }
        }
    }

    const valid_mask: u64 = if (state_count == 0) 0 else (@as(u64, 1) << @intCast(state_count)) - 1;
    return .{
        .num_states = @intCast(state_count),
        .valid_state_mask = valid_mask,
        .initial_mask = eps_closure[0],
        .accept_bit = @as(u64, 1) << @intCast(state_count),
        .self_loop_mask = self_loop_mask,
        .advance_mask = advance_mask,
        .char_classes = try arena.dupe([4]u64, classes_buf[0..state_count]),
        .eps_closure = eps_closure,
    };
}

/// Compiles `raw_pattern` into a `CompiledGlob64` (`E0019` on malformed globs, `..`, `> 16` braces, or `> 64` states).
fn compileGlob64Impl(
    arena: *BumpArena,
    interner: *StringInterner,
    raw_pattern: []const u8,
    span: Span,
    sink: ?*DiagnosticSink,
) !?CompiledGlob64 {
    if (raw_pattern.len == 0) {
        try emitToolConfigDiag(sink, .e0019_invalid_lint_rule_or_glob, span, "path glob pattern cannot be empty", null);
        return null;
    }
    var err_reason: []const u8 = "invalid path glob pattern";
    const branches = (try expandGlobBraceBranches(arena, raw_pattern, &err_reason)) orelse {
        try emitToolConfigDiag(sink, .e0019_invalid_lint_rule_or_glob, span, err_reason, null);
        return null;
    };

    const sub_nfas = try arena.allocSlice(SubNfa64, branches.len);
    for (branches, 0..) |branch, i| {
        sub_nfas[i] = (try compileSingleSubNfa64(arena, branch, &err_reason)) orelse {
            try emitToolConfigDiag(sink, .e0019_invalid_lint_rule_or_glob, span, err_reason, null);
            return null;
        };
    }

    return .{
        .pattern_id = try interner.intern(raw_pattern),
        .sub_nfas = sub_nfas,
    };
}

/// Parses an array of TOML glob strings into `[]const CompiledGlob64` (`E0013` if non-array; `E0019` on bad glob).
fn parseGlobArray(
    arena: *BumpArena,
    interner: *StringInterner,
    val: TomlDomValue,
    val_span: Span,
    field_label: []const u8,
    require_non_empty: bool,
    sink: ?*DiagnosticSink,
) !?[]const CompiledGlob64 {
    if (val != .array_val) {
        if (sink) |diag_sink| {
            const msg = try std.fmt.allocPrint(
                diag_sink.arena.asAllocator(),
                "`{s}` must be an array of path glob strings",
                .{field_label},
            );
            try emitManifestFieldErr(sink, val_span, msg);
        }
        return null;
    }
    if (require_non_empty and val.array_val.len == 0) {
        if (sink) |diag_sink| {
            const msg = try std.fmt.allocPrint(
                diag_sink.arena.asAllocator(),
                "`{s}` must contain at least one path glob string",
                .{field_label},
            );
            try emitToolConfigDiag(sink, .e0019_invalid_lint_rule_or_glob, val_span, msg, null);
        }
        return null;
    }

    var globs: std.ArrayList(CompiledGlob64) = .empty;
    defer globs.deinit(arena.backing_allocator);
    for (val.array_val) |elem| {
        if (elem.val != .str_val) {
            try emitToolConfigDiag(
                sink,
                .e0019_invalid_lint_rule_or_glob,
                elem.span,
                "path glob element must be a string",
                null,
            );
            continue;
        }
        if (try compileGlob64Impl(arena, interner, elem.val.str_val, elem.span, sink)) |compiled| {
            try globs.append(arena.backing_allocator, compiled);
        }
    }
    return try arena.dupe(CompiledGlob64, globs.items);
}

/// Parses a `disable = ["…"]` rule selector array into `RuleMask64` (`E0019` + Jaro-Winkler help on unknown rules).
fn parseLintDisableMask(
    val: TomlDomValue,
    val_span: Span,
    field_label: []const u8,
    sink: ?*DiagnosticSink,
) !RuleMask64 {
    if (val != .array_val) {
        if (sink) |diag_sink| {
            const msg = try std.fmt.allocPrint(
                diag_sink.arena.asAllocator(),
                "`{s}` must be an array of lint rule slugs or `W0xxx` codes",
                .{field_label},
            );
            try emitManifestFieldErr(sink, val_span, msg);
        }
        return 0;
    }

    var mask: RuleMask64 = 0;
    for (val.array_val) |elem| {
        if (elem.val != .str_val) {
            try emitToolConfigDiag(
                sink,
                .e0019_invalid_lint_rule_or_glob,
                elem.span,
                "lint rule selector in `disable` must be a string",
                null,
            );
            continue;
        }
        const raw_sel = elem.val.str_val;
        switch (diagnostic.lookupLintRuleBySelector(raw_sel)) {
            .rule => |rule_id| {
                mask |= rule_id.bit();
            },
            .forbidden_category_or_wildcard => {
                if (sink) |diag_sink| {
                    const msg = try std.fmt.allocPrint(
                        diag_sink.arena.asAllocator(),
                        "category or wildcard `{s}` cannot be disabled as a group in `corex.toml`; list explicit rule slugs or `W0xxx` codes",
                        .{raw_sel},
                    );
                    try emitToolConfigDiag(sink, .e0019_invalid_lint_rule_or_glob, elem.span, msg, null);
                }
            },
            .non_suppressible_error_code => {
                if (sink) |diag_sink| {
                    const msg = try std.fmt.allocPrint(
                        diag_sink.arena.asAllocator(),
                        "compiler error `{s}` cannot be disabled; `[lint].disable` only accepts `W0xxx` lint rules",
                        .{raw_sel},
                    );
                    try emitToolConfigDiag(sink, .e0019_invalid_lint_rule_or_glob, elem.span, msg, null);
                }
            },
            .non_suppressible_subsystem_warning => {
                if (sink) |diag_sink| {
                    const msg = try std.fmt.allocPrint(
                        diag_sink.arena.asAllocator(),
                        "subsystem warning `{s}` is not a configurable lint rule",
                        .{raw_sel},
                    );
                    try emitToolConfigDiag(sink, .e0019_invalid_lint_rule_or_glob, elem.span, msg, null);
                }
            },
            .unknown => {
                if (sink) |diag_sink| {
                    const msg = try std.fmt.allocPrint(
                        diag_sink.arena.asAllocator(),
                        "unknown lint rule `{s}` in `disable`",
                        .{raw_sel},
                    );
                    const help_note = if (diagnostic.suggestClosestLintRule(raw_sel)) |closest|
                        try std.fmt.allocPrint(diag_sink.arena.asAllocator(), "help: did you mean `{s}`?", .{closest})
                    else
                        null;
                    try emitToolConfigDiag(sink, .e0019_invalid_lint_rule_or_glob, elem.span, msg, help_note);
                }
            },
        }
    }
    return mask;
}

/// Extracts an integer scalar from `TomlDomValue` (`int_val` or `uint_val`), returning `null` if non-integer.
fn extractTomlSignedOrUnsignedInt(val: TomlDomValue) ?i128 {
    return switch (val) {
        .int_val => |iv| iv,
        .uint_val => |uv| @as(i128, uv),
        else => null,
    };
}

/// Validates that `ident` is a valid non-empty ASCII CoreX identifier (`[A-Za-z_][A-Za-z0-9_]*`).
fn isValidAllowedIdentEntry(ident: []const u8) bool {
    if (ident.len == 0 or ident.len > MAX_PKG_NAME_BYTES) return false;
    const first_ch = ident[0];
    if (!std.ascii.isAlphabetic(first_ch) and first_ch != '_') return false;
    for (ident[1..]) |ch_byte| {
        if (!std.ascii.isAlphanumeric(ch_byte) and ch_byte != '_') return false;
    }
    return true;
}

/// Parses and validates `[lint.settings]` or `[workspace.lint.settings]` (`E0020` on out-of-range values).
fn parseLintSettingsSection(
    arena: *BumpArena,
    interner: *StringInterner,
    settings_tbl: *const TomlDomTable,
    explicit_mask_out: *u8,
    sink: ?*DiagnosticSink,
) !LintSettings {
    var settings: LintSettings = .{};
    for (settings_tbl.entries.items) |kv| {
        if (std.mem.eql(u8, kv.key, "min-grouped-int-digits")) {
            explicit_mask_out.* |= (1 << 0);
            const raw_int = extractTomlSignedOrUnsignedInt(kv.val) orelse {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].min-grouped-int-digits` must be an integer in `4..=12`",
                    null,
                );
                continue;
            };
            if (raw_int < lint_filter.MIN_GROUPED_INT_DIGITS_MIN or raw_int > lint_filter.MIN_GROUPED_INT_DIGITS_MAX) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].min-grouped-int-digits` is out of range (expected `4..=12`)",
                    null,
                );
                continue;
            }
            settings.min_grouped_int_digits = @intCast(raw_int);
        } else if (std.mem.eql(u8, kv.key, "min-grouped-hex-digits")) {
            explicit_mask_out.* |= (1 << 1);
            const raw_hex = extractTomlSignedOrUnsignedInt(kv.val) orelse {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].min-grouped-hex-digits` must be an integer in `4..=16`",
                    null,
                );
                continue;
            };
            if (raw_hex < lint_filter.MIN_GROUPED_HEX_DIGITS_MIN or raw_hex > lint_filter.MIN_GROUPED_HEX_DIGITS_MAX) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].min-grouped-hex-digits` is out of range (expected `4..=16`)",
                    null,
                );
                continue;
            }
            settings.min_grouped_hex_digits = @intCast(raw_hex);
        } else if (std.mem.eql(u8, kv.key, "trivial-copy-max-bytes")) {
            explicit_mask_out.* |= (1 << 2);
            const raw_copy = extractTomlSignedOrUnsignedInt(kv.val) orelse {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].trivial-copy-max-bytes` must be an integer in `4..=16`",
                    null,
                );
                continue;
            };
            if (raw_copy < lint_filter.TRIVIAL_COPY_MAX_BYTES_MIN or raw_copy > lint_filter.TRIVIAL_COPY_MAX_BYTES_MAX) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].trivial-copy-max-bytes` is out of range (expected `4..=16`)",
                    null,
                );
                continue;
            }
            settings.trivial_copy_max_bytes = @intCast(raw_copy);
        } else if (std.mem.eql(u8, kv.key, "require-suppression-reason")) {
            explicit_mask_out.* |= (1 << 3);
            if (kv.val != .bool_val) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].require-suppression-reason` must be a boolean (`true` or `false`)",
                    null,
                );
                continue;
            }
            settings.require_suppression_reason = kv.val.bool_val;
        } else if (std.mem.eql(u8, kv.key, "allowed-ident-names")) {
            explicit_mask_out.* |= (1 << 4);
            if (kv.val != .array_val) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].allowed-ident-names` must be an array of `<= 64` identifier strings",
                    null,
                );
                continue;
            }
            if (kv.val.array_val.len > lint_filter.MAX_ALLOWED_IDENT_NAMES) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].allowed-ident-names` exceeds maximum `64` entries",
                    null,
                );
                continue;
            }
            var raw_ids: std.ArrayList(StringId) = .empty;
            defer raw_ids.deinit(arena.backing_allocator);
            for (kv.val.array_val) |elem| {
                if (elem.val != .str_val or !isValidAllowedIdentEntry(elem.val.str_val)) {
                    try emitToolConfigDiag(
                        sink,
                        .e0020_tool_setting_out_of_range,
                        elem.span,
                        "`[lint.settings].allowed-ident-names` entries must be non-empty ASCII identifiers",
                        null,
                    );
                    continue;
                }
                try raw_ids.append(arena.backing_allocator, try interner.intern(elem.val.str_val));
            }
            settings.allowed_ident_names = try sortAndDedupStringIds(arena, interner, raw_ids.items);
        } else if (std.mem.eql(u8, kv.key, "allowed-confusables")) {
            explicit_mask_out.* |= (1 << 5);
            if (kv.val != .array_val) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].allowed-confusables` must be an array of `<= 64` single non-ASCII characters",
                    null,
                );
                continue;
            }
            if (kv.val.array_val.len > lint_filter.MAX_ALLOWED_CONFUSABLES) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lint.settings].allowed-confusables` exceeds maximum `64` entries",
                    null,
                );
                continue;
            }
            var cps: std.ArrayList(u21) = .empty;
            defer cps.deinit(arena.backing_allocator);
            for (kv.val.array_val) |elem| {
                if (elem.val != .str_val) {
                    try emitToolConfigDiag(
                        sink,
                        .e0020_tool_setting_out_of_range,
                        elem.span,
                        "`[lint.settings].allowed-confusables` entry must be a single non-ASCII Unicode character string",
                        null,
                    );
                    continue;
                }
                const str_s = elem.val.str_val;
                var utf8_ok = false;
                var decoded_cp: u21 = 0;
                if (str_s.len >= 2 and std.unicode.utf8ValidateSlice(str_s)) {
                    const cp_len = std.unicode.utf8ByteSequenceLength(str_s[0]) catch 0;
                    if (cp_len == str_s.len) {
                        decoded_cp = std.unicode.utf8Decode(str_s) catch 0;
                        if (decoded_cp >= 0x80) utf8_ok = true;
                    }
                }
                if (!utf8_ok) {
                    try emitToolConfigDiag(
                        sink,
                        .e0020_tool_setting_out_of_range,
                        elem.span,
                        "`[lint.settings].allowed-confusables` entry must be a single non-ASCII scalar (`>= U+0080`)",
                        null,
                    );
                    continue;
                }
                try cps.append(arena.backing_allocator, decoded_cp);
            }
            std.mem.sort(u21, cps.items, {}, std.sort.asc(u21));
            var dedup_len: usize = 0;
            for (cps.items) |cp_val| {
                if (dedup_len == 0 or cps.items[dedup_len - 1] != cp_val) {
                    cps.items[dedup_len] = cp_val;
                    dedup_len += 1;
                }
            }
            settings.allowed_confusables = try arena.dupe(u21, cps.items[0..dedup_len]);
        } else {
            try emitManifestFieldErr(sink, kv.key_span, "unknown key in `[lint.settings]` table");
        }
    }
    return settings;
}

/// Returns `true` if `key` is a forbidden severity-remapping or per-rule toggle key in `[lint]` (`E0018`).
fn isForbiddenLintSeverityOrToggleKey(key: []const u8) bool {
    if (std.mem.eql(u8, key, "rules") or
        std.mem.eql(u8, key, "categories") or
        std.mem.eql(u8, key, "levels") or
        std.mem.eql(u8, key, "enable") or
        std.mem.eql(u8, key, "select") or
        std.mem.eql(u8, key, "extend-select") or
        std.mem.eql(u8, key, "allow") or
        std.mem.eql(u8, key, "warn") or
        std.mem.eql(u8, key, "deny") or
        std.mem.eql(u8, key, "forbid") or
        std.mem.eql(u8, key, "severity") or
        std.mem.eql(u8, key, "level"))
    {
        return true;
    }
    return switch (diagnostic.lookupLintRuleBySelector(key)) {
        .rule, .forbidden_category_or_wildcard => true,
        else => false,
    };
}

/// Parses and validates `[lint]` or `[workspace.lint]` (`E0018`, `E0019`, `E0020`).
fn parseLintSection(
    arena: *BumpArena,
    interner: *StringInterner,
    lint_tbl: *const TomlDomTable,
    is_workspace_table: bool,
    sink: ?*DiagnosticSink,
) !LintConfig {
    var cfg: LintConfig = .{};
    var overrides_list: std.ArrayList(LintOverride) = .empty;
    defer overrides_list.deinit(arena.backing_allocator);

    for (lint_tbl.entries.items) |kv| {
        if (std.mem.eql(u8, kv.key, "inherit")) {
            if (is_workspace_table) {
                try emitManifestFieldErr(sink, kv.key_span, "`inherit` is only valid on package `[lint]`, not `[workspace.lint]`");
                continue;
            }
            if (kv.val != .bool_val) {
                try emitManifestFieldErr(sink, kv.val_span, "`[lint].inherit` must be a boolean");
                continue;
            }
            cfg.inherit = kv.val.bool_val;
            cfg.has_explicit_inherit = true;
        } else if (std.mem.eql(u8, kv.key, "disable")) {
            cfg.disable_mask |= try parseLintDisableMask(kv.val, kv.val_span, "[lint].disable", sink);
        } else if (std.mem.eql(u8, kv.key, "exclude")) {
            if (try parseGlobArray(arena, interner, kv.val, kv.val_span, "[lint].exclude", false, sink)) |globs| {
                cfg.exclude = globs;
            }
        } else if (std.mem.eql(u8, kv.key, "settings")) {
            if (kv.val != .table_val) {
                try emitManifestFieldErr(sink, kv.val_span, "`[lint.settings]` must be a table");
                continue;
            }
            cfg.settings = try parseLintSettingsSection(
                arena,
                interner,
                kv.val.table_val,
                &cfg.explicit_settings_mask,
                sink,
            );
        } else if (std.mem.eql(u8, kv.key, "overrides")) {
            if (kv.val != .array_val) {
                try emitManifestFieldErr(sink, kv.val_span, "`[[lint.overrides]]` must be an array of tables");
                continue;
            }
            for (kv.val.array_val) |ov_elem| {
                if (ov_elem.val != .table_val) {
                    try emitManifestFieldErr(sink, ov_elem.span, "`[[lint.overrides]]` element must be a table");
                    continue;
                }
                var ov_entry: LintOverride = .{};
                var has_files_key = false;
                var has_disable_key = false;
                for (ov_elem.val.table_val.entries.items) |okv| {
                    if (std.mem.eql(u8, okv.key, "files")) {
                        has_files_key = true;
                        if (try parseGlobArray(
                            arena,
                            interner,
                            okv.val,
                            okv.val_span,
                            "[[lint.overrides]].files",
                            true,
                            sink,
                        )) |inc_globs| {
                            ov_entry.files = inc_globs;
                        }
                    } else if (std.mem.eql(u8, okv.key, "exclude_files")) {
                        if (try parseGlobArray(
                            arena,
                            interner,
                            okv.val,
                            okv.val_span,
                            "[[lint.overrides]].exclude_files",
                            false,
                            sink,
                        )) |exc_globs| {
                            ov_entry.exclude_files = exc_globs;
                        }
                    } else if (std.mem.eql(u8, okv.key, "disable")) {
                        has_disable_key = true;
                        ov_entry.disable_mask |= try parseLintDisableMask(
                            okv.val,
                            okv.val_span,
                            "[[lint.overrides]].disable",
                            sink,
                        );
                    } else if (isForbiddenLintSeverityOrToggleKey(okv.key)) {
                        if (sink) |diag_sink| {
                            const msg = try std.fmt.allocPrint(
                                diag_sink.arena.asAllocator(),
                                "`[[lint.overrides]]` uses a strict `disable`-only model; `{s}` is forbidden (`DR-25`)",
                                .{okv.key},
                            );
                            try emitToolConfigDiag(
                                sink,
                                .e0018_forbidden_tool_config_key,
                                okv.key_span,
                                msg,
                                "help: list suppressed rules in `disable = [\"…\"]`",
                            );
                        }
                    } else {
                        try emitManifestFieldErr(sink, okv.key_span, "unknown key in `[[lint.overrides]]` table");
                    }
                }
                if (!has_files_key) {
                    try emitToolConfigDiag(
                        sink,
                        .e0019_invalid_lint_rule_or_glob,
                        ov_elem.span,
                        "`[[lint.overrides]]` entry requires a non-empty `files = [\"…\"]` glob array",
                        null,
                    );
                }
                if (!has_disable_key) {
                    try emitManifestFieldErr(sink, ov_elem.span, "`[[lint.overrides]]` entry requires `disable = […]`");
                }
                if (ov_entry.files.len > 0) {
                    try overrides_list.append(arena.backing_allocator, ov_entry);
                }
            }
        } else if (isForbiddenLintSeverityOrToggleKey(kv.key) or kv.val == .bool_val or kv.val == .str_val) {
            if (sink) |diag_sink| {
                const msg = try std.fmt.allocPrint(
                    diag_sink.arena.asAllocator(),
                    "`[lint]` uses a strict `disable`-only model (`E0xxx` = error, `W0xxx` = warning); `{s}` is forbidden (`DR-25`)",
                    .{kv.key},
                );
                try emitToolConfigDiag(
                    sink,
                    .e0018_forbidden_tool_config_key,
                    kv.key_span,
                    msg,
                    "help: remove per-rule toggles/severities and list suppressed rules in `disable = [\"…\"]`",
                );
            }
        } else {
            try emitManifestFieldErr(sink, kv.key_span, "unknown key in `[lint]` table");
        }
    }

    cfg.overrides = try arena.dupe(LintOverride, overrides_list.items);
    return cfg;
}

/// Parses and validates `[fmt]` or `[workspace.fmt]`, rejecting all style-fragmenting knobs with `E0018`.
fn parseFmtSection(
    arena: *BumpArena,
    interner: *StringInterner,
    fmt_tbl: *const TomlDomTable,
    is_workspace_table: bool,
    sink: ?*DiagnosticSink,
) !FmtConfig {
    var cfg: FmtConfig = .{};
    for (fmt_tbl.entries.items) |kv| {
        if (std.mem.eql(u8, kv.key, "inherit")) {
            if (is_workspace_table) {
                try emitManifestFieldErr(sink, kv.key_span, "`inherit` is only valid on package `[fmt]`, not `[workspace.fmt]`");
                continue;
            }
            if (kv.val != .bool_val) {
                try emitManifestFieldErr(sink, kv.val_span, "`[fmt].inherit` must be a boolean");
                continue;
            }
            cfg.inherit = kv.val.bool_val;
            cfg.has_explicit_inherit = true;
        } else if (std.mem.eql(u8, kv.key, "exclude")) {
            if (try parseGlobArray(arena, interner, kv.val, kv.val_span, "[fmt].exclude", false, sink)) |globs| {
                cfg.exclude = globs;
            }
        } else if (std.mem.eql(u8, kv.key, "check-generated")) {
            if (kv.val != .bool_val) {
                try emitManifestFieldErr(sink, kv.val_span, "`[fmt].check-generated` must be a boolean");
                continue;
            }
            cfg.check_generated = kv.val.bool_val;
            cfg.has_explicit_check_generated = true;
        } else {
            if (sink) |diag_sink| {
                const msg = try std.fmt.allocPrint(
                    diag_sink.arena.asAllocator(),
                    "style-configuration key `[fmt].{s}` is forbidden; `corex fmt` enforces a single zero-knob canonical style (`DR-25`)",
                    .{kv.key},
                );
                try emitToolConfigDiag(
                    sink,
                    .e0018_forbidden_tool_config_key,
                    kv.key_span,
                    msg,
                    "help: `[fmt]` only permits `inherit`, `exclude`, and `check-generated`",
                );
            }
        }
    }
    return cfg;
}

/// Parses and validates `[lsp]` or `[workspace.lsp]` (`E0020` on out-of-range/invalid enum values).
fn parseLspSection(
    lsp_tbl: *const TomlDomTable,
    is_workspace_table: bool,
    sink: ?*DiagnosticSink,
) !LspConfig {
    var cfg: LspConfig = .{};
    for (lsp_tbl.entries.items) |kv| {
        if (std.mem.eql(u8, kv.key, "inherit")) {
            if (is_workspace_table) {
                try emitManifestFieldErr(sink, kv.key_span, "`inherit` is only valid on package `[lsp]`, not `[workspace.lsp]`");
                continue;
            }
            if (kv.val != .bool_val) {
                try emitManifestFieldErr(sink, kv.val_span, "`[lsp].inherit` must be a boolean");
                continue;
            }
            cfg.inherit = kv.val.bool_val;
            cfg.has_explicit_inherit = true;
        } else if (std.mem.eql(u8, kv.key, "inlay-hints-types")) {
            cfg.explicit_fields_mask |= (1 << 0);
            if (kv.val != .bool_val) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lsp].inlay-hints-types` must be a boolean (`true` or `false`)",
                    null,
                );
                continue;
            }
            cfg.inlay_hints_types = kv.val.bool_val;
        } else if (std.mem.eql(u8, kv.key, "inlay-hints-parameter-names")) {
            cfg.explicit_fields_mask |= (1 << 1);
            if (kv.val != .str_val) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lsp].inlay-hints-parameter-names` must be `\"none\"`, `\"non-matching\"`, or `\"all\"`",
                    null,
                );
                continue;
            }
            if (std.mem.eql(u8, kv.val.str_val, "none")) {
                cfg.inlay_hints_parameter_names = .none;
            } else if (std.mem.eql(u8, kv.val.str_val, "non-matching")) {
                cfg.inlay_hints_parameter_names = .non_matching;
            } else if (std.mem.eql(u8, kv.val.str_val, "all")) {
                cfg.inlay_hints_parameter_names = .all;
            } else {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "invalid `[lsp].inlay-hints-parameter-names` mode (expected `\"none\"`, `\"non-matching\"`, or `\"all\"`)",
                    null,
                );
            }
        } else if (std.mem.eql(u8, kv.key, "inlay-hints-mvs-modes")) {
            cfg.explicit_fields_mask |= (1 << 2);
            if (kv.val != .bool_val) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lsp].inlay-hints-mvs-modes` must be a boolean (`true` or `false`)",
                    null,
                );
                continue;
            }
            cfg.inlay_hints_mvs_modes = kv.val.bool_val;
        } else if (std.mem.eql(u8, kv.key, "inlay-hints-effects")) {
            cfg.explicit_fields_mask |= (1 << 3);
            if (kv.val != .str_val) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lsp].inlay-hints-effects` must be `\"none\"`, `\"contracts-only\"`, or `\"all\"`",
                    null,
                );
                continue;
            }
            if (std.mem.eql(u8, kv.val.str_val, "none")) {
                cfg.inlay_hints_effects = .none;
            } else if (std.mem.eql(u8, kv.val.str_val, "contracts-only")) {
                cfg.inlay_hints_effects = .contracts_only;
            } else if (std.mem.eql(u8, kv.val.str_val, "all")) {
                cfg.inlay_hints_effects = .all;
            } else {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "invalid `[lsp].inlay-hints-effects` mode (expected `\"none\"`, `\"contracts-only\"`, or `\"all\"`)",
                    null,
                );
            }
        } else if (std.mem.eql(u8, kv.key, "code-lens-test-bench")) {
            cfg.explicit_fields_mask |= (1 << 4);
            if (kv.val != .bool_val) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lsp].code-lens-test-bench` must be a boolean (`true` or `false`)",
                    null,
                );
                continue;
            }
            cfg.code_lens_test_bench = kv.val.bool_val;
        } else if (std.mem.eql(u8, kv.key, "max-completion-items")) {
            cfg.explicit_fields_mask |= (1 << 5);
            const raw_max = extractTomlSignedOrUnsignedInt(kv.val) orelse {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lsp].max-completion-items` must be an integer in `16..=256`",
                    null,
                );
                continue;
            };
            if (raw_max < LSP_MAX_COMPLETION_ITEMS_MIN or raw_max > LSP_MAX_COMPLETION_ITEMS_MAX) {
                try emitToolConfigDiag(
                    sink,
                    .e0020_tool_setting_out_of_range,
                    kv.val_span,
                    "`[lsp].max-completion-items` is out of range (expected `16..=256`)",
                    null,
                );
                continue;
            }
            cfg.max_completion_items = @intCast(raw_max);
        } else {
            try emitManifestFieldErr(sink, kv.key_span, "unknown key in `[lsp]` table");
        }
    }
    return cfg;
}

/// Merges `member_lint` over `ws_lint` when `member_lint.inherit` is `true` (`DR-25` §3.1).
fn resolveEffectivePackageLintConfigImpl(
    arena: *BumpArena,
    member_lint: LintConfig,
    ws_lint: LintConfig,
) !LintConfig {
    if (!member_lint.inherit) return member_lint;

    var merged_exclude: []const CompiledGlob64 = member_lint.exclude;
    if (ws_lint.exclude.len > 0) {
        if (member_lint.exclude.len == 0) {
            merged_exclude = ws_lint.exclude;
        } else {
            const combined = try arena.allocSlice(CompiledGlob64, ws_lint.exclude.len + member_lint.exclude.len);
            @memcpy(combined[0..ws_lint.exclude.len], ws_lint.exclude);
            @memcpy(combined[ws_lint.exclude.len..], member_lint.exclude);
            merged_exclude = combined;
        }
    }

    var merged_overrides: []const LintOverride = member_lint.overrides;
    if (ws_lint.overrides.len > 0) {
        if (member_lint.overrides.len == 0) {
            merged_overrides = ws_lint.overrides;
        } else {
            const combined_ov = try arena.allocSlice(LintOverride, ws_lint.overrides.len + member_lint.overrides.len);
            @memcpy(combined_ov[0..ws_lint.overrides.len], ws_lint.overrides);
            @memcpy(combined_ov[ws_lint.overrides.len..], member_lint.overrides);
            merged_overrides = combined_ov;
        }
    }

    var eff_settings = ws_lint.settings;
    if ((member_lint.explicit_settings_mask & (1 << 0)) != 0) {
        eff_settings.min_grouped_int_digits = member_lint.settings.min_grouped_int_digits;
    }
    if ((member_lint.explicit_settings_mask & (1 << 1)) != 0) {
        eff_settings.min_grouped_hex_digits = member_lint.settings.min_grouped_hex_digits;
    }
    if ((member_lint.explicit_settings_mask & (1 << 2)) != 0) {
        eff_settings.trivial_copy_max_bytes = member_lint.settings.trivial_copy_max_bytes;
    }
    if ((member_lint.explicit_settings_mask & (1 << 3)) != 0) {
        eff_settings.require_suppression_reason = member_lint.settings.require_suppression_reason;
    }
    if ((member_lint.explicit_settings_mask & (1 << 4)) != 0) {
        eff_settings.allowed_ident_names = member_lint.settings.allowed_ident_names;
    }
    if ((member_lint.explicit_settings_mask & (1 << 5)) != 0) {
        eff_settings.allowed_confusables = member_lint.settings.allowed_confusables;
    }

    return .{
        .inherit = true,
        .has_explicit_inherit = member_lint.has_explicit_inherit,
        .disable_mask = ws_lint.disable_mask | member_lint.disable_mask,
        .exclude = merged_exclude,
        .settings = eff_settings,
        .explicit_settings_mask = ws_lint.explicit_settings_mask | member_lint.explicit_settings_mask,
        .overrides = merged_overrides,
    };
}

/// Merges `member_fmt` over `ws_fmt` when `member_fmt.inherit` is `true` (`DR-25` §3.1).
fn resolveEffectivePackageFmtConfigImpl(
    arena: *BumpArena,
    member_fmt: FmtConfig,
    ws_fmt: FmtConfig,
) !FmtConfig {
    if (!member_fmt.inherit) return member_fmt;

    var merged_exclude: []const CompiledGlob64 = member_fmt.exclude;
    if (ws_fmt.exclude.len > 0) {
        if (member_fmt.exclude.len == 0) {
            merged_exclude = ws_fmt.exclude;
        } else {
            const combined = try arena.allocSlice(CompiledGlob64, ws_fmt.exclude.len + member_fmt.exclude.len);
            @memcpy(combined[0..ws_fmt.exclude.len], ws_fmt.exclude);
            @memcpy(combined[ws_fmt.exclude.len..], member_fmt.exclude);
            merged_exclude = combined;
        }
    }

    return .{
        .inherit = true,
        .has_explicit_inherit = member_fmt.has_explicit_inherit,
        .exclude = merged_exclude,
        .check_generated = if (member_fmt.has_explicit_check_generated)
            member_fmt.check_generated
        else
            ws_fmt.check_generated,
        .has_explicit_check_generated = member_fmt.has_explicit_check_generated or ws_fmt.has_explicit_check_generated,
    };
}

/// Merges `member_lsp` over `ws_lsp` when `member_lsp.inherit` is `true` (`DR-25` §3.1).
fn resolveEffectivePackageLspConfigImpl(member_lsp: LspConfig, ws_lsp: LspConfig) LspConfig {
    if (!member_lsp.inherit) return member_lsp;
    var eff = ws_lsp;
    eff.inherit = true;
    eff.has_explicit_inherit = member_lsp.has_explicit_inherit;
    if ((member_lsp.explicit_fields_mask & (1 << 0)) != 0) eff.inlay_hints_types = member_lsp.inlay_hints_types;
    if ((member_lsp.explicit_fields_mask & (1 << 1)) != 0) {
        eff.inlay_hints_parameter_names = member_lsp.inlay_hints_parameter_names;
    }
    if ((member_lsp.explicit_fields_mask & (1 << 2)) != 0) eff.inlay_hints_mvs_modes = member_lsp.inlay_hints_mvs_modes;
    if ((member_lsp.explicit_fields_mask & (1 << 3)) != 0) eff.inlay_hints_effects = member_lsp.inlay_hints_effects;
    if ((member_lsp.explicit_fields_mask & (1 << 4)) != 0) {
        eff.code_lens_test_bench = member_lsp.code_lens_test_bench;
    }
    if ((member_lsp.explicit_fields_mask & (1 << 5)) != 0) {
        eff.max_completion_items = member_lsp.max_completion_items;
    }
    eff.explicit_fields_mask = ws_lsp.explicit_fields_mask | member_lsp.explicit_fields_mask;
    return eff;
}

/// Probes `dir_path` for forbidden standalone CoreX tool dotfiles, emitting `E0017` when present.
fn checkStrayToolConfigDotfilesImpl(
    io: std.Io,
    dir_path: []const u8,
    fallback_file_id: FileId,
    sink: ?*DiagnosticSink,
) !bool {
    const trimmed_dir = std.mem.trimEnd(u8, dir_path, "/\\");
    var path_buf: [1024]u8 = undefined;
    var found_any = false;

    for (FORBIDDEN_STRAY_TOOL_DOTFILES) |dotfile_name| {
        const probe_path = if (trimmed_dir.len == 0 or std.mem.eql(u8, trimmed_dir, "."))
            dotfile_name
        else
            std.fmt.bufPrint(&path_buf, "{s}/{s}", .{ trimmed_dir, dotfile_name }) catch continue;

        if (std.Io.Dir.cwd().statFile(io, probe_path, .{})) |_| {
            found_any = true;
            if (sink) |diag_sink| {
                const msg = try std.fmt.allocPrint(
                    diag_sink.arena.asAllocator(),
                    "standalone tool configuration file `{s}` is forbidden (`DR-25`); " ++
                        "consolidate `[lint]`, `[fmt]`, and `[lsp]` inside `corex.toml`",
                    .{dotfile_name},
                );
                const help_note = try std.fmt.allocPrint(
                    diag_sink.arena.asAllocator(),
                    "help: move settings into `corex.toml` and delete `{s}`",
                    .{dotfile_name},
                );
                try emitToolConfigDiag(
                    sink,
                    .e0017_stray_tool_config_dotfile,
                    Span.init(fallback_file_id, 0, 0),
                    msg,
                    help_note,
                );
            }
        } else |_| {}
    }
    return found_any;
}

/// Parses `[security]` (including `[security.dev]` and `[security.package.<name>]`).
fn parseSecuritySection(
    arena: *BumpArena,
    interner: *StringInterner,
    doc: *const TomlDocumentView,
    sec_tbl: *const TomlDomTable,
    sink: ?*DiagnosticSink,
) !SecurityPolicy {
    var policy = SecurityPolicy{};
    var overrides: std.ArrayList(PackageSecurityOverride) = .empty;
    defer overrides.deinit(arena.backing_allocator);

    for (sec_tbl.entries.items) |kv| {
        if (std.mem.eql(u8, kv.key, "default_allow_caps")) {
            if (kv.val != .array_val) {
                try emitManifestFieldErr(sink, kv.val_span, "`default_allow_caps` must be an array of capability strings");
                continue;
            }
            policy.default_allow_caps = try parseCapabilityElemArray(
                kv.val.array_val,
                doc,
                interner,
                .e0013_invalid_manifest_or_pkg_name,
                false,
                null,
                sink,
            );
            if (policy.default_allow_caps) |caps| {
                if (caps.isEmpty()) policy.default_dep_policy = .zero_trust;
            }
        } else if (std.mem.eql(u8, kv.key, "default_dep_policy")) {
            if (kv.val != .str_val) {
                try emitManifestFieldErr(sink, kv.val_span, "`default_dep_policy` must be a policy name string");
                continue;
            }
            const pol_s = kv.val.str_val;
            if (std.mem.eql(u8, pol_s, "trust_on_first_lock")) {
                policy.default_dep_policy = .trust_on_first_lock;
            } else if (std.mem.eql(u8, pol_s, "zero_trust")) {
                policy.default_dep_policy = .zero_trust;
                if (policy.default_allow_caps == null) policy.default_allow_caps = .EMPTY;
            } else if (std.mem.eql(u8, pol_s, "allow_all")) {
                policy.default_dep_policy = .allow_all;
                if (policy.default_allow_caps == null) {
                    policy.default_allow_caps = EffectCapabilityMask.fromBits(EffectCapabilityMask.LOCKFILE_CAP_BITS);
                }
            } else {
                try emitManifestFieldErr(
                    sink,
                    kv.val_span,
                    "invalid `default_dep_policy`; expected `\"trust_on_first_lock\"`, `\"zero_trust\"`, or `\"allow_all\"`",
                );
            }
        } else if (std.mem.eql(u8, kv.key, "deny_caps")) {
            if (kv.val != .array_val) {
                try emitManifestFieldErr(sink, kv.val_span, "capability denylist must be an array of capability strings");
                continue;
            }
            if (try parseCapabilityElemArray(
                kv.val.array_val,
                doc,
                interner,
                .e0013_invalid_manifest_or_pkg_name,
                false,
                null,
                sink,
            )) |parsed_deny| {
                policy.deny_caps = policy.deny_caps.unionWith(parsed_deny);
            }
        } else if (std.mem.eql(u8, kv.key, "enforcement_scope")) {
            if (kv.val != .str_val) {
                try emitManifestFieldErr(sink, kv.val_span, "`enforcement_scope` must be `\"surface\"` or `\"reachable\"`");
                continue;
            }
            if (std.mem.eql(u8, kv.val.str_val, "surface")) {
                policy.enforcement_scope = .surface;
            } else if (std.mem.eql(u8, kv.val.str_val, "reachable")) {
                policy.enforcement_scope = .reachable;
            } else {
                try emitManifestFieldErr(sink, kv.val_span, "`enforcement_scope` must be `\"surface\"` or `\"reachable\"`");
            }
        } else if (std.mem.eql(u8, kv.key, "warn_ambient_dead_caps")) {
            if (kv.val != .bool_val) {
                try emitManifestFieldErr(sink, kv.val_span, "`warn_ambient_dead_caps` must be a boolean");
                continue;
            }
            policy.is_warn_ambient_dead_caps = kv.val.bool_val;
        } else if (std.mem.eql(u8, kv.key, "dev") and kv.val == .table_val) {
            for (kv.val.table_val.entries.items) |dev_kv| {
                if (std.mem.eql(u8, dev_kv.key, "default_allow_caps") and dev_kv.val == .array_val) {
                    policy.dev_default_allow_caps = try parseCapabilityElemArray(
                        dev_kv.val.array_val,
                        doc,
                        interner,
                        .e0013_invalid_manifest_or_pkg_name,
                        false,
                        null,
                        sink,
                    );
                } else if (std.mem.eql(u8, dev_kv.key, "deny_caps") and dev_kv.val == .array_val) {
                    if (try parseCapabilityElemArray(
                        dev_kv.val.array_val,
                        doc,
                        interner,
                        .e0013_invalid_manifest_or_pkg_name,
                        false,
                        null,
                        sink,
                    )) |dev_deny| {
                        policy.dev_deny_caps = dev_deny;
                    }
                } else {
                    try emitManifestFieldErr(sink, dev_kv.key_span, "unknown key in `[security.dev]`");
                }
            }
        } else if (std.mem.eql(u8, kv.key, "package") and kv.val == .table_val) {
            for (kv.val.table_val.entries.items) |pkg_ov| {
                if (!try validatePackageNameKebab(
                    arena,
                    interner,
                    doc.full_file_bytes,
                    pkg_ov.key,
                    pkg_ov.key_span,
                    sink,
                )) continue;
                if (pkg_ov.val != .table_val) {
                    try emitManifestFieldErr(sink, pkg_ov.val_span, "`[security.package.<name>]` must be a table");
                    continue;
                }
                var ov_allow: ?EffectCapabilityMask = null;
                var ov_deny: EffectCapabilityMask = .EMPTY;
                for (pkg_ov.val.table_val.entries.items) |ov_kv| {
                    if (std.mem.eql(u8, ov_kv.key, "allow_caps") and ov_kv.val == .array_val) {
                        ov_allow = try parseCapabilityElemArray(
                            ov_kv.val.array_val,
                            doc,
                            interner,
                            .e0013_invalid_manifest_or_pkg_name,
                            false,
                            null,
                            sink,
                        );
                    } else if (std.mem.eql(u8, ov_kv.key, "deny_caps") and ov_kv.val == .array_val) {
                        if (try parseCapabilityElemArray(
                            ov_kv.val.array_val,
                            doc,
                            interner,
                            .e0013_invalid_manifest_or_pkg_name,
                            false,
                            null,
                            sink,
                        )) |d_mask| {
                            ov_deny = d_mask;
                        }
                    } else {
                        try emitManifestFieldErr(sink, ov_kv.key_span, "unknown key in `[security.package.<name>]`");
                    }
                }
                try overrides.append(arena.backing_allocator, .{
                    .package_kebab = try interner.intern(pkg_ov.key),
                    .allow_caps = ov_allow,
                    .deny_caps = ov_deny,
                });
            }
        } else {
            try emitManifestFieldErr(sink, kv.key_span, "unknown key in `[security]` table");
        }
    }

    std.mem.sort(PackageSecurityOverride, overrides.items, interner, struct {
        /// Sorts `PackageSecurityOverride` entries by ASCII `package_kebab`.
        fn lessThan(int_ptr: *const StringInterner, lhs: PackageSecurityOverride, rhs: PackageSecurityOverride) bool {
            return std.mem.order(u8, int_ptr.get(lhs.package_kebab), int_ptr.get(rhs.package_kebab)) == .lt;
        }
    }.lessThan);
    policy.package_overrides = try arena.dupe(PackageSecurityOverride, overrides.items);
    return policy;
}

/// Parses `[resolution]` `exclude = ["pkg@1.2.3", "pkg@<1.4.0"]` entries.
fn parseResolutionSection(
    arena: *BumpArena,
    interner: *StringInterner,
    res_tbl: *const TomlDomTable,
    out_excludes: *std.ArrayList(ExcludeRule),
    sink: ?*DiagnosticSink,
) !void {
    for (res_tbl.entries.items) |kv| {
        if (!std.mem.eql(u8, kv.key, "exclude") or kv.val != .array_val) {
            try emitManifestFieldErr(sink, kv.key_span, "`[resolution]` supports only `exclude = [\"<pkg>@<req>\", …]`");
            continue;
        }
        for (kv.val.array_val) |elem| {
            if (elem.val != .str_val) {
                try emitManifestFieldErr(sink, elem.span, "`[resolution].exclude` element must be a `\"<pkg>@<req>\"` string");
                continue;
            }
            const spec_s = elem.val.str_val;
            const at_idx = std.mem.indexOfScalar(u8, spec_s, '@') orelse {
                try emitManifestFieldErr(sink, elem.span, "`[resolution].exclude` entry must have form `\"<pkg>@<req>\"`");
                continue;
            };
            const pkg_name = spec_s[0..at_idx];
            const req_part = spec_s[at_idx + 1 ..];
            if (!isValidPackageNameKebab(pkg_name)) {
                try emitManifestFieldErr(sink, elem.span, "invalid `kebab-case` package name in `[resolution].exclude`");
                continue;
            }
            const parsed_req = blk: {
                if (try SemVer.parse(interner, req_part)) |exact_sem| {
                    var exact_r = VersionReq{ .len = 1, .min_floor = exact_sem, .has_intra_series_upper_bound = true };
                    exact_r.comparators[0] = .{ .op = .exact, .ver = exact_sem };
                    break :blk exact_r;
                }
                break :blk (try VersionReq.parse(interner, req_part)) orelse {
                    try emitManifestFieldErr(sink, elem.span, "invalid SemVer constraint in `[resolution].exclude`");
                    continue;
                };
            };
            try out_excludes.append(arena.asAllocator(), .{
                .package_kebab = try interner.intern(pkg_name),
                .req = parsed_req,
                .has_cve_advisory = elem.has_cve_advisory,
                .anchor_id = elem.anchor_id,
                .span = elem.span,
            });
        }
    }
}

/// Parses `[patch.<scope>]` tables (`path = "…"` or `git = "…"` only).
fn parsePatchRootSection(
    arena: *BumpArena,
    interner: *StringInterner,
    doc: *const TomlDocumentView,
    patch_root: *const TomlDomTable,
    out_patches: *std.ArrayList(PatchSpec),
    sink: ?*DiagnosticSink,
) !void {
    for (patch_root.entries.items) |scope_entry| {
        if (scope_entry.val != .table_val) {
            try emitManifestFieldErr(sink, scope_entry.val_span, "`[patch]` children must be `[patch.<source>]` subtables");
            continue;
        }
        const scope_id = try interner.intern(scope_entry.key);
        for (scope_entry.val.table_val.entries.items) |pkg_entry| {
            if (!try validatePackageNameKebab(
                arena,
                interner,
                doc.full_file_bytes,
                pkg_entry.key,
                pkg_entry.key_span,
                sink,
            )) continue;
            if (pkg_entry.val != .table_val) {
                try emitManifestFieldErr(sink, pkg_entry.val_span, "`[patch]` override must be a table specifying `path` or `git`");
                continue;
            }
            var git_url: ?StringId = null;
            var git_kind: GitRevKind = .default_head;
            var git_val: StringId = .empty;
            var rel_path: ?StringId = null;
            var has_bad_patch = false;

            for (pkg_entry.val.table_val.entries.items) |pkv| {
                if (std.mem.eql(u8, pkv.key, "path") and pkv.val == .str_val and pkv.val.str_val.len > 0) {
                    rel_path = try interner.intern(pkv.val.str_val);
                } else if (std.mem.eql(u8, pkv.key, "git") and pkv.val == .str_val and pkv.val.str_val.len > 0) {
                    git_url = try interner.intern(pkv.val.str_val);
                } else if ((std.mem.eql(u8, pkv.key, "tag") or std.mem.eql(u8, pkv.key, "branch") or
                    std.mem.eql(u8, pkv.key, "rev")) and pkv.val == .str_val and pkv.val.str_val.len > 0)
                {
                    git_kind = if (std.mem.eql(u8, pkv.key, "tag"))
                        .tag
                    else if (std.mem.eql(u8, pkv.key, "branch"))
                        .branch
                    else
                        .rev;
                    git_val = try interner.intern(pkv.val.str_val);
                } else {
                    has_bad_patch = true;
                    try emitManifestFieldErr(sink, pkv.key_span, "unsupported key in `[patch]` override (use `path` or `git`)");
                }
            }
            if (has_bad_patch) continue;
            const replacement: DepSourceSpec = if (rel_path) |rp| blk: {
                if (git_url != null) {
                    try emitManifestFieldErr(sink, pkg_entry.val_span, "`[patch]` entry cannot specify both `path` and `git`");
                    continue;
                }
                break :blk .{ .path = .{ .rel_path = rp } };
            } else if (git_url) |gu|
                .{ .git = .{ .url = gu, .rev_kind = git_kind, .rev_value = git_val } }
            else {
                try emitManifestFieldErr(sink, pkg_entry.val_span, "`[patch]` entry must specify either `path` or `git`");
                continue;
            };

            try out_patches.append(arena.asAllocator(), .{
                .scope = scope_id,
                .package_kebab = try interner.intern(pkg_entry.key),
                .replacement = replacement,
                .anchor_id = pkg_entry.anchor_id,
                .span = pkg_entry.val_span,
            });
        }
    }
}

/// Validates `{ workspace = true }` inline inheritance tables (`E0013` on `false` or extra keys).
fn isWorkspaceInheritFieldTable(
    val: TomlDomValue,
    val_span: Span,
    sink: ?*DiagnosticSink,
) !bool {
    if (val != .table_val) return false;
    if (val.table_val.findEntry("workspace")) |ws_entry| {
        if (ws_entry.val == .bool_val and ws_entry.val.bool_val and val.table_val.entries.items.len == 1) {
            return true;
        }
    }
    try emitManifestFieldErr(sink, val_span, "field table inheritance only supports `{ workspace = true }`");
    return true;
}

/// Parses `[workspace.package]` shared metadata (`version`, `corex`, `edition`, `license`, `repository`, `description`, `publish`).
fn parseWorkspacePackageSection(
    arena: *BumpArena,
    interner: *StringInterner,
    ws_pkg_tbl: *const TomlDomTable,
    is_emitting_diags: bool,
    sink: ?*DiagnosticSink,
) !WorkspacePackageMeta {
    const eff_sink: ?*DiagnosticSink = if (is_emitting_diags) sink else null;
    var meta = WorkspacePackageMeta{};
    for (ws_pkg_tbl.entries.items) |pkv| {
        if (std.mem.eql(u8, pkv.key, "version")) {
            if (pkv.val != .str_val) {
                try emitManifestFieldErr(eff_sink, pkv.val_span, "`workspace.package.version` must be a SemVer 2.0.0 string");
                continue;
            }
            meta.version = (try SemVer.parse(interner, pkv.val.str_val)) orelse blk: {
                try emitManifestFieldErr(eff_sink, pkv.val_span, "invalid SemVer 2.0.0 version in `workspace.package.version`");
                break :blk null;
            };
        } else if (std.mem.eql(u8, pkv.key, "corex")) {
            if (pkv.val != .str_val or (try VersionReq.parse(interner, pkv.val.str_val)) == null) {
                try emitManifestFieldErr(eff_sink, pkv.val_span, "`workspace.package.corex` must be a valid version requirement string");
                continue;
            }
            meta.corex_req = try interner.intern(pkv.val.str_val);
        } else if (std.mem.eql(u8, pkv.key, "edition")) {
            if (pkv.val != .str_val or !std.mem.eql(u8, pkv.val.str_val, DEFAULT_COREX_EDITION)) {
                try emitManifestFieldErr(eff_sink, pkv.val_span, "unsupported `workspace.package.edition` (only `\"2026\"` is valid)");
                continue;
            }
            meta.edition = try interner.intern(pkv.val.str_val);
        } else if (std.mem.eql(u8, pkv.key, "description")) {
            if (pkv.val != .str_val) {
                try emitManifestFieldErr(eff_sink, pkv.val_span, "`workspace.package.description` must be a string");
                continue;
            }
            meta.description = try interner.intern(pkv.val.str_val);
        } else if (std.mem.eql(u8, pkv.key, "license")) {
            if (pkv.val != .str_val) {
                try emitManifestFieldErr(eff_sink, pkv.val_span, "`workspace.package.license` must be a string");
                continue;
            }
            meta.license = try interner.intern(pkv.val.str_val);
        } else if (std.mem.eql(u8, pkv.key, "repository")) {
            if (pkv.val != .str_val) {
                try emitManifestFieldErr(eff_sink, pkv.val_span, "`workspace.package.repository` must be a string");
                continue;
            }
            meta.repository = try interner.intern(pkv.val.str_val);
        } else if (std.mem.eql(u8, pkv.key, "publish")) {
            if (pkv.val == .bool_val) {
                meta.publish = .{ .is_allowed = pkv.val.bool_val };
            } else if (pkv.val == .array_val) {
                var regs: std.ArrayList(StringId) = .empty;
                defer regs.deinit(arena.backing_allocator);
                for (pkv.val.array_val) |relem| {
                    if (relem.val == .str_val and relem.val.str_val.len > 0) {
                        try regs.append(arena.backing_allocator, try interner.intern(relem.val.str_val));
                    } else {
                        try emitManifestFieldErr(eff_sink, relem.span, "`workspace.package.publish` registry names must be non-empty strings");
                    }
                }
                meta.publish = .{ .registries = try sortAndDedupStringIds(arena, interner, regs.items) };
            } else {
                try emitManifestFieldErr(eff_sink, pkv.val_span, "`workspace.package.publish` must be a boolean or registry array");
            }
        } else {
            try emitManifestFieldErr(eff_sink, pkv.key_span, "unknown or non-inheritable key in `[workspace.package]` table");
        }
    }
    return meta;
}

/// Resolves `dep = { workspace = true }` entries against `ws_deps`, emitting `E0013` on missing workspace entries.
fn resolveWorkspaceInheritedDeps(
    allocator: std.mem.Allocator,
    arena: *BumpArena,
    interner: *StringInterner,
    deps: []const DependencySpec,
    ws_deps: []const DependencySpec,
    sink: ?*DiagnosticSink,
) ![]const DependencySpec {
    var has_any_ws_inherit = false;
    for (deps) |dep_check| {
        if (dep_check.source == .workspace_inherit) {
            has_any_ws_inherit = true;
            break;
        }
    }
    if (!has_any_ws_inherit) return deps;

    const resolved_deps = try arena.dupe(DependencySpec, deps);
    var ws_by_alias: std.AutoHashMapUnmanaged(StringId, usize) = .empty;
    defer ws_by_alias.deinit(allocator);
    var ws_by_pkg: std.AutoHashMapUnmanaged(StringId, usize) = .empty;
    defer ws_by_pkg.deinit(allocator);
    for (ws_deps, 0..) |ws_dep, ws_i| {
        if (ws_dep.source == .workspace_inherit) continue;
        const alias_gop = try ws_by_alias.getOrPut(allocator, ws_dep.alias_kebab);
        if (!alias_gop.found_existing) alias_gop.value_ptr.* = ws_i;
        const pkg_gop = try ws_by_pkg.getOrPut(allocator, ws_dep.package_kebab);
        if (!pkg_gop.found_existing) pkg_gop.value_ptr.* = ws_i;
    }

    for (resolved_deps) |*dep_item| {
        if (dep_item.source != .workspace_inherit) continue;
        const match_idx_opt = ws_by_alias.get(dep_item.alias_kebab) orelse ws_by_pkg.get(dep_item.package_kebab);
        if (match_idx_opt) |ws_idx| {
            const ws_dep = ws_deps[ws_idx];
            dep_item.source = ws_dep.source;
            dep_item.package_kebab = ws_dep.package_kebab;
            dep_item.has_default_features = dep_item.has_default_features and ws_dep.has_default_features;
            if (dep_item.allow_caps == null) dep_item.allow_caps = ws_dep.allow_caps;
            dep_item.deny_caps = dep_item.deny_caps.unionWith(ws_dep.deny_caps);
            dep_item.has_comptime_io_cap = dep_item.has_comptime_io_cap or ws_dep.has_comptime_io_cap;
            if (dep_item.features.len == 0) {
                dep_item.features = ws_dep.features;
            } else if (ws_dep.features.len > 0) {
                var merged: std.ArrayList(StringId) = .empty;
                defer merged.deinit(allocator);
                try merged.appendSlice(allocator, ws_dep.features);
                try merged.appendSlice(allocator, dep_item.features);
                dep_item.features = try sortAndDedupStringIds(arena, interner, merged.items);
            }
        } else {
            try emitManifestFieldErr(
                sink,
                dep_item.decl_span,
                "dependency specifies `workspace = true`, but no matching entry exists in `[workspace.dependencies]`",
            );
        }
    }
    return resolved_deps;
}

/// Lowers a parsed root `TomlDomTable` into a validated `Manifest` (`E0013` on schema/script violations).
fn lowerDomToManifest(
    arena: *BumpArena,
    interner: *StringInterner,
    doc: *const TomlDocumentView,
    root_tbl: *const TomlDomTable,
    is_script: bool,
    cfg_env: *const CfgEnv,
    inherited_ws_pkg: ?WorkspacePackageMeta,
    sink: ?*DiagnosticSink,
) !Manifest {
    var manifest = Manifest{
        .file_id = doc.file_id,
        .is_script = is_script,
        .anchors = try arena.dupe(TomlSpanAnchor, doc.cst.anchors.items),
    };

    // Pre-scan local `[workspace.package]` when `[package]` and `[workspace]` coexist in the same `corex.toml`:
    var effective_ws_pkg = inherited_ws_pkg;
    if (!is_script and effective_ws_pkg == null) {
        if (root_tbl.findEntry("workspace")) |ws_top| {
            if (ws_top.val == .table_val) {
                if (ws_top.val.table_val.findEntry("package")) |ws_pkg_entry| {
                    if (ws_pkg_entry.val == .table_val) {
                        effective_ws_pkg = try parseWorkspacePackageSection(
                            arena,
                            interner,
                            ws_pkg_entry.val.table_val,
                            false,
                            null,
                        );
                    }
                }
            }
        }
    }

    var deps_list: std.ArrayList(DependencySpec) = .empty;
    var excludes_list: std.ArrayList(ExcludeRule) = .empty;
    var patches_list: std.ArrayList(PatchSpec) = .empty;
    var feats_list: std.ArrayList(FeatureDecl) = .empty;
    var bins_list: std.ArrayList(BinTarget) = .empty;
    var has_seen_pkg_section = false;

    for (root_tbl.entries.items) |top_kv| {
        const key = top_kv.key;
        if (std.mem.eql(u8, key, "target")) {
            if (sink) |diag_sink| {
                const help_fix = "move platform dependencies into `[dependencies]` with inline `target = \"target.os == .Linux\"`";
                const notes = try diag_sink.arena.dupe([]const u8, &.{help_fix});
                try diag_sink.emit(.{
                    .code = .e0013_invalid_manifest_or_pkg_name,
                    .severity = .err,
                    .primary_span = top_kv.key_span,
                    .message = "`[target.'…'.dependencies]` tables are forbidden in `corex.toml`; use inline `target = \"<CoreX @cfg>\"`",
                    .notes = notes,
                });
            }
            continue;
        }

        if (std.mem.eql(u8, key, "package")) {
            has_seen_pkg_section = true;
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[package]` must be a table");
                continue;
            }
            const pkg_tbl = top_kv.val.table_val;
            var has_seen_name = false;
            var has_seen_version = false;
            var name_id: ?StringId = null;
            var mod_snake_id: StringId = .empty;
            var ver_opt: ?SemVer = null;
            var corex_req_id: StringId = .empty;
            var edition_id: StringId = try interner.intern(DEFAULT_COREX_EDITION);
            var desc_id: StringId = .empty;
            var lic_id: StringId = .empty;
            var repo_id: StringId = .empty;
            var pub_pol: PublishPolicy = .{ .is_allowed = true };
            var root_mod_id: StringId = .empty;
            var links_id: StringId = .empty;

            for (pkg_tbl.entries.items) |pkv| {
                if (std.mem.eql(u8, pkv.key, "name")) {
                    has_seen_name = true;
                    if (pkv.val != .str_val) {
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.name` must be a `kebab-case` string");
                        continue;
                    }
                    if (try validatePackageNameKebab(
                        arena,
                        interner,
                        doc.full_file_bytes,
                        pkv.val.str_val,
                        pkv.val_span,
                        sink,
                    )) {
                        name_id = try interner.intern(pkv.val.str_val);
                        mod_snake_id = try interner.intern(try kebabToSnakeModule(arena, pkv.val.str_val));
                    }
                } else if (std.mem.eql(u8, pkv.key, "version")) {
                    has_seen_version = true;
                    if (pkv.val == .table_val) {
                        if (pkv.val.table_val.findEntry("workspace")) |ws_e| {
                            if (ws_e.val == .bool_val and ws_e.val.bool_val and pkv.val.table_val.entries.items.len == 1) {
                                if (effective_ws_pkg != null and effective_ws_pkg.?.version != null) {
                                    ver_opt = effective_ws_pkg.?.version;
                                } else {
                                    try emitManifestFieldErr(
                                        sink,
                                        pkv.val_span,
                                        "`package.version = { workspace = true }` requires `[workspace.package].version`",
                                    );
                                }
                                continue;
                            }
                        }
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.version` table only supports `{ workspace = true }`");
                        continue;
                    }
                    if (pkv.val != .str_val) {
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.version` must be a SemVer 2.0.0 string");
                        continue;
                    }
                    ver_opt = (try SemVer.parse(interner, pkv.val.str_val)) orelse blk: {
                        try emitManifestFieldErr(sink, pkv.val_span, "invalid SemVer 2.0.0 version in `package.version`");
                        break :blk null;
                    };
                } else if (std.mem.eql(u8, pkv.key, "corex")) {
                    if (pkv.val == .table_val) {
                        if (pkv.val.table_val.findEntry("workspace")) |ws_e| {
                            if (ws_e.val == .bool_val and ws_e.val.bool_val and pkv.val.table_val.entries.items.len == 1) {
                                if (effective_ws_pkg != null and effective_ws_pkg.?.corex_req != null) {
                                    corex_req_id = effective_ws_pkg.?.corex_req.?;
                                } else {
                                    try emitManifestFieldErr(
                                        sink,
                                        pkv.val_span,
                                        "`package.corex = { workspace = true }` requires `[workspace.package].corex`",
                                    );
                                }
                                continue;
                            }
                        }
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.corex` table only supports `{ workspace = true }`");
                        continue;
                    }
                    if (pkv.val != .str_val or (try VersionReq.parse(interner, pkv.val.str_val)) == null) {
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.corex` must be a valid version requirement string");
                        continue;
                    }
                    corex_req_id = try interner.intern(pkv.val.str_val);
                } else if (std.mem.eql(u8, pkv.key, "edition")) {
                    if (pkv.val == .table_val) {
                        if (pkv.val.table_val.findEntry("workspace")) |ws_e| {
                            if (ws_e.val == .bool_val and ws_e.val.bool_val and pkv.val.table_val.entries.items.len == 1) {
                                if (effective_ws_pkg != null and effective_ws_pkg.?.edition != null) {
                                    edition_id = effective_ws_pkg.?.edition.?;
                                } else {
                                    try emitManifestFieldErr(
                                        sink,
                                        pkv.val_span,
                                        "`package.edition = { workspace = true }` requires `[workspace.package].edition`",
                                    );
                                }
                                continue;
                            }
                        }
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.edition` table only supports `{ workspace = true }`");
                        continue;
                    }
                    if (pkv.val != .str_val or !std.mem.eql(u8, pkv.val.str_val, DEFAULT_COREX_EDITION)) {
                        try emitManifestFieldErr(sink, pkv.val_span, "unsupported `package.edition` (only `\"2026\"` is valid)");
                        continue;
                    }
                    edition_id = try interner.intern(pkv.val.str_val);
                } else if (std.mem.eql(u8, pkv.key, "description")) {
                    if (pkv.val == .table_val) {
                        if (try isWorkspaceInheritFieldTable(pkv.val, pkv.val_span, sink)) {
                            if (pkv.val.table_val.entries.items.len == 1 and
                                pkv.val.table_val.entries.items[0].val == .bool_val and
                                pkv.val.table_val.entries.items[0].val.bool_val)
                            {
                                if (effective_ws_pkg != null and effective_ws_pkg.?.description != null) {
                                    desc_id = effective_ws_pkg.?.description.?;
                                } else {
                                    try emitManifestFieldErr(
                                        sink,
                                        pkv.val_span,
                                        "`package.description = { workspace = true }` requires `[workspace.package].description`",
                                    );
                                }
                            }
                        }
                        continue;
                    }
                    if (pkv.val != .str_val) {
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.description` must be a string");
                        continue;
                    }
                    desc_id = try interner.intern(pkv.val.str_val);
                } else if (std.mem.eql(u8, pkv.key, "license")) {
                    if (pkv.val == .table_val) {
                        if (try isWorkspaceInheritFieldTable(pkv.val, pkv.val_span, sink)) {
                            if (pkv.val.table_val.entries.items.len == 1 and
                                pkv.val.table_val.entries.items[0].val == .bool_val and
                                pkv.val.table_val.entries.items[0].val.bool_val)
                            {
                                if (effective_ws_pkg != null and effective_ws_pkg.?.license != null) {
                                    lic_id = effective_ws_pkg.?.license.?;
                                } else {
                                    try emitManifestFieldErr(
                                        sink,
                                        pkv.val_span,
                                        "`package.license = { workspace = true }` requires `[workspace.package].license`",
                                    );
                                }
                            }
                        }
                        continue;
                    }
                    if (pkv.val != .str_val) {
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.license` must be a string");
                        continue;
                    }
                    lic_id = try interner.intern(pkv.val.str_val);
                } else if (std.mem.eql(u8, pkv.key, "repository")) {
                    if (pkv.val == .table_val) {
                        if (try isWorkspaceInheritFieldTable(pkv.val, pkv.val_span, sink)) {
                            if (pkv.val.table_val.entries.items.len == 1 and
                                pkv.val.table_val.entries.items[0].val == .bool_val and
                                pkv.val.table_val.entries.items[0].val.bool_val)
                            {
                                if (effective_ws_pkg != null and effective_ws_pkg.?.repository != null) {
                                    repo_id = effective_ws_pkg.?.repository.?;
                                } else {
                                    try emitManifestFieldErr(
                                        sink,
                                        pkv.val_span,
                                        "`package.repository = { workspace = true }` requires `[workspace.package].repository`",
                                    );
                                }
                            }
                        }
                        continue;
                    }
                    if (pkv.val != .str_val) {
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.repository` must be a string");
                        continue;
                    }
                    repo_id = try interner.intern(pkv.val.str_val);
                } else if (std.mem.eql(u8, pkv.key, "publish")) {
                    if (is_script) {
                        try emitManifestFieldErr(sink, pkv.key_span, "`package.publish` is forbidden inside `.cx` script frontmatter");
                        continue;
                    }
                    if (pkv.val == .table_val) {
                        if (try isWorkspaceInheritFieldTable(pkv.val, pkv.val_span, sink)) {
                            if (pkv.val.table_val.entries.items.len == 1 and
                                pkv.val.table_val.entries.items[0].val == .bool_val and
                                pkv.val.table_val.entries.items[0].val.bool_val)
                            {
                                if (effective_ws_pkg != null and effective_ws_pkg.?.publish != null) {
                                    pub_pol = effective_ws_pkg.?.publish.?;
                                } else {
                                    try emitManifestFieldErr(
                                        sink,
                                        pkv.val_span,
                                        "`package.publish = { workspace = true }` requires `[workspace.package].publish`",
                                    );
                                }
                            }
                        }
                        continue;
                    }
                    if (pkv.val == .bool_val) {
                        pub_pol = .{ .is_allowed = pkv.val.bool_val };
                    } else if (pkv.val == .array_val) {
                        var regs: std.ArrayList(StringId) = .empty;
                        defer regs.deinit(arena.backing_allocator);
                        for (pkv.val.array_val) |relem| {
                            if (relem.val == .str_val and relem.val.str_val.len > 0) {
                                try regs.append(arena.backing_allocator, try interner.intern(relem.val.str_val));
                            } else {
                                try emitManifestFieldErr(sink, relem.span, "`package.publish` registry names must be non-empty strings");
                            }
                        }
                        pub_pol = .{ .registries = try sortAndDedupStringIds(arena, interner, regs.items) };
                    } else {
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.publish` must be a boolean or registry array");
                    }
                } else if (std.mem.eql(u8, pkv.key, "root_module")) {
                    if (pkv.val != .str_val) {
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.root_module` must be a relative path string");
                        continue;
                    }
                    const norm_root = normalizeAndValidateManifestRelPath(pkv.val.str_val) orelse {
                        try emitManifestFieldErr(
                            sink,
                            pkv.val_span,
                            "`package.root_module` must be a jailed forward-slash relative path without `..` or `\\`",
                        );
                        continue;
                    };
                    root_mod_id = try interner.intern(norm_root);
                } else if (std.mem.eql(u8, pkv.key, "links")) {
                    if (pkv.val != .str_val or pkv.val.str_val.len == 0) {
                        try emitManifestFieldErr(sink, pkv.val_span, "`package.links` must be a non-empty C library identifier");
                        continue;
                    }
                    links_id = try interner.intern(pkv.val.str_val);
                } else {
                    try emitManifestFieldErr(sink, pkv.key_span, "unknown or mistyped key in `[package]` table");
                }
            }

            if (is_script) {
                const fallback_name = name_id orelse try interner.intern("script-pkg");
                const fallback_snake = if (mod_snake_id != .empty) mod_snake_id else try interner.intern("script_pkg");
                manifest.package = .{
                    .name_kebab = fallback_name,
                    .module_snake = fallback_snake,
                    .version = ver_opt orelse .{ .major = 0, .minor = 1, .patch = 0 },
                    .corex_req = corex_req_id,
                    .edition = edition_id,
                    .description = desc_id,
                    .license = lic_id,
                    .repository = repo_id,
                    .publish = .{ .is_allowed = false },
                    .root_module = root_mod_id,
                    .links = links_id,
                };
            } else if (name_id != null and ver_opt != null) {
                manifest.package = .{
                    .name_kebab = name_id.?,
                    .module_snake = mod_snake_id,
                    .version = ver_opt.?,
                    .corex_req = corex_req_id,
                    .edition = edition_id,
                    .description = desc_id,
                    .license = lic_id,
                    .repository = repo_id,
                    .publish = pub_pol,
                    .root_module = root_mod_id,
                    .links = links_id,
                };
            } else if (!has_seen_name or !has_seen_version) {
                try emitManifestFieldErr(sink, pkg_tbl.header_span, "`[package]` requires both `name` and `version`");
            }
            continue;
        }

        if (std.mem.eql(u8, key, "lib")) {
            if (is_script) {
                try emitManifestFieldErr(sink, top_kv.key_span, "`[lib]` is forbidden in single-file `.cx` script frontmatter");
                continue;
            }
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[lib]` must be a table");
                continue;
            }
            var lib_name: StringId = if (manifest.package) |pkg_meta| pkg_meta.module_snake else .empty;
            var lib_path: StringId = try interner.intern("src/root.cx");
            for (top_kv.val.table_val.entries.items) |lkv| {
                if (std.mem.eql(u8, lkv.key, "name") and lkv.val == .str_val) {
                    if (!isValidSnakeAlias(lkv.val.str_val)) {
                        try emitManifestFieldErr(sink, lkv.val_span, "`lib.name` must be a non-reserved `snake_case` identifier");
                    } else {
                        lib_name = try interner.intern(lkv.val.str_val);
                    }
                } else if (std.mem.eql(u8, lkv.key, "path")) {
                    if (lkv.val != .str_val) {
                        try emitManifestFieldErr(sink, lkv.val_span, "`lib.path` must be a relative path string");
                    } else if (normalizeAndValidateManifestRelPath(lkv.val.str_val)) |norm_lib| {
                        lib_path = try interner.intern(norm_lib);
                    } else {
                        try emitManifestFieldErr(
                            sink,
                            lkv.val_span,
                            "`lib.path` must be a jailed forward-slash relative path without `..` or `\\`",
                        );
                    }
                } else {
                    try emitManifestFieldErr(sink, lkv.key_span, "unknown key in `[lib]` table");
                }
            }
            manifest.lib_target = .{ .name_snake = lib_name, .path = lib_path };
            continue;
        }

        if (std.mem.eql(u8, key, "bin")) {
            if (is_script) {
                try emitManifestFieldErr(sink, top_kv.key_span, "`[[bin]]` is forbidden in single-file `.cx` script frontmatter");
                continue;
            }
            if (top_kv.val != .array_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[[bin]]` must be an array of tables");
                continue;
            }
            for (top_kv.val.array_val) |belem| {
                if (belem.val != .table_val) {
                    try emitManifestFieldErr(sink, belem.span, "`[[bin]]` element must be a table");
                    continue;
                }
                var bin_name: ?StringId = null;
                var bin_path: ?StringId = null;
                var has_bad_bin_path = false;
                for (belem.val.table_val.entries.items) |bkv| {
                    if (std.mem.eql(u8, bkv.key, "name") and bkv.val == .str_val) {
                        if (try validatePackageNameKebab(
                            arena,
                            interner,
                            doc.full_file_bytes,
                            bkv.val.str_val,
                            bkv.val_span,
                            sink,
                        )) {
                            bin_name = try interner.intern(bkv.val.str_val);
                        }
                    } else if (std.mem.eql(u8, bkv.key, "path")) {
                        if (bkv.val != .str_val) {
                            has_bad_bin_path = true;
                            try emitManifestFieldErr(sink, bkv.val_span, "`bin.path` must be a relative path string");
                        } else if (normalizeAndValidateManifestRelPath(bkv.val.str_val)) |norm_bin| {
                            bin_path = try interner.intern(norm_bin);
                        } else {
                            has_bad_bin_path = true;
                            try emitManifestFieldErr(
                                sink,
                                bkv.val_span,
                                "`bin.path` must be a jailed forward-slash relative path without `..` or `\\`",
                            );
                        }
                    } else {
                        try emitManifestFieldErr(sink, bkv.key_span, "unknown key in `[[bin]]` target");
                    }
                }
                if (bin_name) |bn| {
                    if (!has_bad_bin_path) {
                        const resolved_path = bin_path orelse try interner.intern("src/main.cx");
                        try bins_list.append(arena.asAllocator(), .{ .name_kebab = bn, .path = resolved_path });
                    }
                } else {
                    try emitManifestFieldErr(sink, belem.span, "`[[bin]]` target requires `name`");
                }
            }
            continue;
        }

        if (std.mem.eql(u8, key, "features")) {
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[features]` must be a table");
                continue;
            }
            for (top_kv.val.table_val.entries.items) |fkv| {
                if (fkv.key.len == 0 or fkv.val != .array_val) {
                    try emitManifestFieldErr(sink, fkv.val_span, "each `[features]` key must map to an array of activation strings");
                    continue;
                }
                var acts: std.ArrayList(StringId) = .empty;
                defer acts.deinit(arena.backing_allocator);
                for (fkv.val.array_val) |aelem| {
                    if (aelem.val != .str_val or aelem.val.str_val.len == 0) {
                        try emitManifestFieldErr(sink, aelem.span, "feature activation must be a non-empty string");
                        continue;
                    }
                    try acts.append(arena.backing_allocator, try interner.intern(aelem.val.str_val));
                }
                try feats_list.append(arena.asAllocator(), .{
                    .name = try interner.intern(fkv.key),
                    .activations = try sortAndDedupStringIds(arena, interner, acts.items),
                });
            }
            continue;
        }

        if (std.mem.eql(u8, key, "dependencies") or
            std.mem.eql(u8, key, "dev-dependencies") or
            std.mem.eql(u8, key, "build-dependencies"))
        {
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "dependency section must be a table");
                continue;
            }
            const d_kind: DepKind = if (std.mem.eql(u8, key, "dependencies"))
                .normal
            else if (std.mem.eql(u8, key, "dev-dependencies"))
                .dev
            else
                .build;
            try parseDependencySection(arena, interner, doc, top_kv.val.table_val, d_kind, cfg_env, &deps_list, sink);
            continue;
        }

        if (std.mem.eql(u8, key, "security")) {
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[security]` must be a table");
                continue;
            }
            manifest.security = try parseSecuritySection(arena, interner, doc, top_kv.val.table_val, sink);
            continue;
        }

        if (std.mem.eql(u8, key, "resolution")) {
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[resolution]` must be a table");
                continue;
            }
            try parseResolutionSection(arena, interner, top_kv.val.table_val, &excludes_list, sink);
            continue;
        }

        if (std.mem.eql(u8, key, "patch")) {
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[patch]` must be a table");
                continue;
            }
            try parsePatchRootSection(arena, interner, doc, top_kv.val.table_val, &patches_list, sink);
            continue;
        }

        if (std.mem.eql(u8, key, "lint")) {
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[lint]` must be a table");
                continue;
            }
            manifest.lint = try parseLintSection(arena, interner, top_kv.val.table_val, false, sink);
            continue;
        }

        if (std.mem.eql(u8, key, "lints")) {
            try emitToolConfigDiag(
                sink,
                .e0018_forbidden_tool_config_key,
                top_kv.key_span,
                "Cargo-style `[lints]` severity table is forbidden in `corex.toml`; use `[lint]` with `disable = [\"…\"]` (`DR-25`)",
                "help: replace `[lints]` with `[lint]`",
            );
            continue;
        }

        if (std.mem.eql(u8, key, "fmt")) {
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[fmt]` must be a table");
                continue;
            }
            manifest.fmt = try parseFmtSection(arena, interner, top_kv.val.table_val, false, sink);
            continue;
        }

        if (std.mem.eql(u8, key, "lsp")) {
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[lsp]` must be a table");
                continue;
            }
            manifest.lsp = try parseLspSection(top_kv.val.table_val, false, sink);
            continue;
        }

        if (std.mem.eql(u8, key, "workspace")) {
            if (is_script) {
                try emitManifestFieldErr(sink, top_kv.key_span, "`[workspace]` is forbidden in single-file `.cx` script frontmatter");
                continue;
            }
            if (top_kv.val != .table_val) {
                try emitManifestFieldErr(sink, top_kv.val_span, "`[workspace]` must be a table");
                continue;
            }
            var ws_cfg = WorkspaceConfig{};
            var ws_deps: std.ArrayList(DependencySpec) = .empty;
            var ws_excl: std.ArrayList(ExcludeRule) = .empty;
            var ws_patch: std.ArrayList(PatchSpec) = .empty;

            for (top_kv.val.table_val.entries.items) |wkv| {
                if (std.mem.eql(u8, wkv.key, "members") and wkv.val == .array_val) {
                    ws_cfg.members = try extractWorkspaceRelArraySorted(arena, interner, wkv.val.array_val, true, sink);
                } else if (std.mem.eql(u8, wkv.key, "default-members") and wkv.val == .array_val) {
                    ws_cfg.default_members = try extractWorkspaceRelArraySorted(arena, interner, wkv.val.array_val, false, sink);
                } else if (std.mem.eql(u8, wkv.key, "exclude") and wkv.val == .array_val) {
                    ws_cfg.exclude = try extractWorkspaceRelArraySorted(arena, interner, wkv.val.array_val, false, sink);
                } else if (std.mem.eql(u8, wkv.key, "dependencies") and wkv.val == .table_val) {
                    try parseDependencySection(arena, interner, doc, wkv.val.table_val, .normal, cfg_env, &ws_deps, sink);
                } else if (std.mem.eql(u8, wkv.key, "security") and wkv.val == .table_val) {
                    ws_cfg.security = try parseSecuritySection(arena, interner, doc, wkv.val.table_val, sink);
                } else if (std.mem.eql(u8, wkv.key, "resolution") and wkv.val == .table_val) {
                    try parseResolutionSection(arena, interner, wkv.val.table_val, &ws_excl, sink);
                } else if (std.mem.eql(u8, wkv.key, "patch") and wkv.val == .table_val) {
                    try parsePatchRootSection(arena, interner, doc, wkv.val.table_val, &ws_patch, sink);
                } else if (std.mem.eql(u8, wkv.key, "package") and wkv.val == .table_val) {
                    ws_cfg.package = try parseWorkspacePackageSection(arena, interner, wkv.val.table_val, true, sink);
                } else if (std.mem.eql(u8, wkv.key, "lint") and wkv.val == .table_val) {
                    ws_cfg.lint = try parseLintSection(arena, interner, wkv.val.table_val, true, sink);
                } else if (std.mem.eql(u8, wkv.key, "lints")) {
                    try emitToolConfigDiag(
                        sink,
                        .e0018_forbidden_tool_config_key,
                        wkv.key_span,
                        "Cargo-style `[workspace.lints]` severity table is forbidden; use `[workspace.lint]` (`DR-25`)",
                        "help: replace `[workspace.lints]` with `[workspace.lint]`",
                    );
                } else if (std.mem.eql(u8, wkv.key, "fmt") and wkv.val == .table_val) {
                    ws_cfg.fmt = try parseFmtSection(arena, interner, wkv.val.table_val, true, sink);
                } else if (std.mem.eql(u8, wkv.key, "lsp") and wkv.val == .table_val) {
                    ws_cfg.lsp = try parseLspSection(wkv.val.table_val, true, sink);
                } else {
                    try emitManifestFieldErr(sink, wkv.key_span, "unknown key in `[workspace]` table");
                }
            }
            for (ws_deps.items) |ws_dep_chk| {
                if (ws_dep_chk.source == .workspace_inherit) {
                    try emitManifestFieldErr(
                        sink,
                        ws_dep_chk.decl_span,
                        "`[workspace.dependencies]` entry cannot specify `workspace = true`",
                    );
                }
            }
            std.mem.sort(DependencySpec, ws_deps.items, interner, struct {
                /// Sorts `[workspace.dependencies]` records by `(kind ASC, alias_kebab ASC)`.
                fn lessThan(int_ptr: *const StringInterner, lhs: DependencySpec, rhs: DependencySpec) bool {
                    if (lhs.kind != rhs.kind) return @backingInt(lhs.kind) < @backingInt(rhs.kind);
                    return std.mem.order(u8, int_ptr.get(lhs.alias_kebab), int_ptr.get(rhs.alias_kebab)) == .lt;
                }
            }.lessThan);
            std.mem.sort(ExcludeRule, ws_excl.items, interner, struct {
                /// Sorts `[workspace.resolution]` exclude records by `(package_kebab ASC, min_floor ASC)`.
                fn lessThan(int_ptr: *const StringInterner, lhs: ExcludeRule, rhs: ExcludeRule) bool {
                    const name_ord = std.mem.order(u8, int_ptr.get(lhs.package_kebab), int_ptr.get(rhs.package_kebab));
                    if (name_ord != .eq) return name_ord == .lt;
                    return SemVer.compare(lhs.req.min_floor, rhs.req.min_floor, int_ptr) == .lt;
                }
            }.lessThan);
            std.mem.sort(PatchSpec, ws_patch.items, interner, struct {
                /// Sorts `[workspace.patch]` records by `(scope ASC, package_kebab ASC)`.
                fn lessThan(int_ptr: *const StringInterner, lhs: PatchSpec, rhs: PatchSpec) bool {
                    const sc_ord = std.mem.order(u8, int_ptr.get(lhs.scope), int_ptr.get(rhs.scope));
                    if (sc_ord != .eq) return sc_ord == .lt;
                    return std.mem.order(u8, int_ptr.get(lhs.package_kebab), int_ptr.get(rhs.package_kebab)) == .lt;
                }
            }.lessThan);
            ws_cfg.dependencies = ws_deps.items;
            ws_cfg.excludes = ws_excl.items;
            ws_cfg.patches = ws_patch.items;
            manifest.workspace = ws_cfg;
            continue;
        }

        try emitManifestFieldErr(sink, top_kv.key_span, "unknown top-level section or key in `corex.toml`");
    }

    if (!is_script and !has_seen_pkg_section and manifest.workspace == null) {
        try emitManifestFieldErr(
            sink,
            Span.init(doc.file_id, doc.base_byte_offset, doc.base_byte_offset),
            "`corex.toml` must declare `[package]` or `[workspace]`",
        );
    }

    // Sort `bin_targets`, `features`, `dependencies`, `excludes`, and `patches` deterministically:
    std.mem.sort(BinTarget, bins_list.items, interner, struct {
        /// Sorts `BinTarget` records by `(name_kebab ASC, path ASC)`.
        fn lessThan(int_ptr: *const StringInterner, lhs: BinTarget, rhs: BinTarget) bool {
            const name_ord = std.mem.order(u8, int_ptr.get(lhs.name_kebab), int_ptr.get(rhs.name_kebab));
            if (name_ord != .eq) return name_ord == .lt;
            return std.mem.order(u8, int_ptr.get(lhs.path), int_ptr.get(rhs.path)) == .lt;
        }
    }.lessThan);
    std.mem.sort(FeatureDecl, feats_list.items, interner, struct {
        /// Sorts `FeatureDecl` records by ASCII `name`.
        fn lessThan(int_ptr: *const StringInterner, lhs: FeatureDecl, rhs: FeatureDecl) bool {
            return std.mem.order(u8, int_ptr.get(lhs.name), int_ptr.get(rhs.name)) == .lt;
        }
    }.lessThan);
    std.mem.sort(DependencySpec, deps_list.items, interner, struct {
        /// Sorts `DependencySpec` records by `(kind ASC, alias_kebab ASC)`.
        fn lessThan(int_ptr: *const StringInterner, lhs: DependencySpec, rhs: DependencySpec) bool {
            if (lhs.kind != rhs.kind) return @backingInt(lhs.kind) < @backingInt(rhs.kind);
            return std.mem.order(u8, int_ptr.get(lhs.alias_kebab), int_ptr.get(rhs.alias_kebab)) == .lt;
        }
    }.lessThan);
    std.mem.sort(ExcludeRule, excludes_list.items, interner, struct {
        /// Sorts `ExcludeRule` records by `(package_kebab ASC, min_floor ASC)`.
        fn lessThan(int_ptr: *const StringInterner, lhs: ExcludeRule, rhs: ExcludeRule) bool {
            const name_ord = std.mem.order(u8, int_ptr.get(lhs.package_kebab), int_ptr.get(rhs.package_kebab));
            if (name_ord != .eq) return name_ord == .lt;
            return SemVer.compare(lhs.req.min_floor, rhs.req.min_floor, int_ptr) == .lt;
        }
    }.lessThan);
    std.mem.sort(PatchSpec, patches_list.items, interner, struct {
        /// Sorts `PatchSpec` records by `(scope ASC, package_kebab ASC)`.
        fn lessThan(int_ptr: *const StringInterner, lhs: PatchSpec, rhs: PatchSpec) bool {
            const sc_ord = std.mem.order(u8, int_ptr.get(lhs.scope), int_ptr.get(rhs.scope));
            if (sc_ord != .eq) return sc_ord == .lt;
            return std.mem.order(u8, int_ptr.get(lhs.package_kebab), int_ptr.get(rhs.package_kebab)) == .lt;
        }
    }.lessThan);

    if (manifest.lib_target) |*lib_tgt| {
        if (lib_tgt.name_snake == .empty) {
            if (manifest.package) |pkg_meta| {
                lib_tgt.name_snake = pkg_meta.module_snake;
            }
        }
    }

    manifest.bin_targets = bins_list.items;
    manifest.features = feats_list.items;
    manifest.dependencies = if (manifest.workspace) |ws_self|
        try resolveWorkspaceInheritedDeps(
            arena.backing_allocator,
            arena,
            interner,
            deps_list.items,
            ws_self.dependencies,
            sink,
        )
    else
        deps_list.items;
    if (root_tbl.findEntry("features")) |feat_entry| {
        if (feat_entry.val == .table_val) {
            try validateManifestFeatureActivations(
                arena.backing_allocator,
                interner,
                feat_entry.val.table_val,
                manifest.features,
                manifest.dependencies,
                sink,
            );
        }
    }
    manifest.excludes = excludes_list.items;
    manifest.patches = patches_list.items;
    if (manifest.package != null) {
        if (manifest.workspace) |ws_self| {
            manifest.lint = try resolveEffectivePackageLintConfig(arena, manifest.lint, ws_self.lint);
            manifest.fmt = try resolveEffectivePackageFmtConfig(arena, manifest.fmt, ws_self.fmt);
            manifest.lsp = resolveEffectivePackageLspConfig(manifest.lsp, ws_self.lsp);
        }
    }
    manifest.root_manifest_blake3 = computeNormalizedManifestBlake3(&manifest, interner);
    return manifest;
}

/// Validates `[features]` activation targets (`dep:<opt>`, `<dep>/<feat>`, `<local_feat>`) in $O(1)$ per entry.
fn validateManifestFeatureActivations(
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    feat_tbl: *const TomlDomTable,
    features: []const FeatureDecl,
    dependencies: []const DependencySpec,
    sink: ?*DiagnosticSink,
) !void {
    if (features.len == 0) return;

    var declared_set: std.AutoHashMapUnmanaged(StringId, void) = .empty;
    defer declared_set.deinit(allocator);
    for (features) |feat_decl| {
        try declared_set.put(allocator, feat_decl.name, {});
    }

    var all_dep_set: std.AutoHashMapUnmanaged(StringId, void) = .empty;
    defer all_dep_set.deinit(allocator);
    var opt_dep_set: std.AutoHashMapUnmanaged(StringId, void) = .empty;
    defer opt_dep_set.deinit(allocator);
    for (dependencies) |dep| {
        try all_dep_set.put(allocator, dep.alias_kebab, {});
        if (dep.is_optional) {
            try opt_dep_set.put(allocator, dep.alias_kebab, {});
        }
    }

    for (feat_tbl.entries.items) |fkv| {
        if (fkv.key.len == 0 or fkv.val != .array_val) continue;
        for (fkv.val.array_val) |aelem| {
            if (aelem.val != .str_val or aelem.val.str_val.len == 0) continue;
            const act_str = aelem.val.str_val;
            if (std.mem.startsWith(u8, act_str, "dep:")) {
                const opt_name = act_str[4..];
                const opt_id = try interner.intern(opt_name);
                if (opt_name.len == 0 or !opt_dep_set.contains(opt_id)) {
                    try emitManifestFieldErr(
                        sink,
                        aelem.span,
                        "`dep:<name>` in `[features]` must reference an `optional = true` dependency",
                    );
                }
            } else if (std.mem.indexOfScalar(u8, act_str, '/')) |slash_pos| {
                const raw_dep = act_str[0..slash_pos];
                const dep_alias = if (std.mem.endsWith(u8, raw_dep, "?"))
                    raw_dep[0 .. raw_dep.len - 1]
                else
                    raw_dep;
                const sub_feat = act_str[slash_pos + 1 ..];
                const dep_id = try interner.intern(dep_alias);
                if (dep_alias.len == 0 or sub_feat.len == 0 or !all_dep_set.contains(dep_id)) {
                    try emitManifestFieldErr(
                        sink,
                        aelem.span,
                        "`<dep>/<feature>` in `[features]` references an undeclared dependency alias",
                    );
                }
            } else {
                const local_id = try interner.intern(act_str);
                if (!declared_set.contains(local_id) and !opt_dep_set.contains(local_id)) {
                    try emitManifestFieldErr(
                        sink,
                        aelem.span,
                        "`[features]` activation references an undeclared local feature or non-optional dependency",
                    );
                }
            }
        }
    }
}

/// Extracts, validates, and sorts `[workspace]` relative directory or `/*` glob patterns into `StringId`s.
fn extractWorkspaceRelArraySorted(
    arena: *BumpArena,
    interner: *StringInterner,
    elems: []const TomlDomElem,
    is_glob_allowed: bool,
    sink: ?*DiagnosticSink,
) ![]const StringId {
    var ids: std.ArrayList(StringId) = .empty;
    defer ids.deinit(arena.backing_allocator);
    for (elems) |el| {
        if (el.val != .str_val or el.val.str_val.len == 0) {
            try emitManifestFieldErr(sink, el.span, "expected non-empty relative path string in `[workspace]` array");
            continue;
        }
        const stripped = if (std.mem.startsWith(u8, el.val.str_val, "./")) el.val.str_val[2..] else el.val.str_val;
        if (!isValidWorkspaceRelPattern(stripped, is_glob_allowed)) {
            try emitManifestFieldErr(
                sink,
                el.span,
                "`[workspace]` path must be a jailed forward-slash relative directory without `..`, `:`, or `\\`",
            );
            continue;
        }
        try ids.append(arena.backing_allocator, try interner.intern(stripped));
    }
    return sortAndDedupStringIds(arena, interner, ids.items);
}

/// Validates a `.cx` `snake_case` module alias (`^[a-z][a-z0-9_]*$`, non-reserved, `1..64` bytes).
fn isValidSnakeAlias(alias: []const u8) bool {
    if (alias.len == 0 or alias.len > MAX_PKG_NAME_BYTES) return false;
    if (RESERVED_PKG_NAME_MAP.has(alias) or lexer.KEYWORD_OR_PRIM_MAP.has(alias)) return false;
    if (alias[0] < 'a' or alias[0] > 'z') return false;
    for (alias[1..]) |ch_b| {
        const is_ok = (ch_b >= 'a' and ch_b <= 'z') or (ch_b >= '0' and ch_b <= '9') or ch_b == '_';
        if (!is_ok) return false;
    }
    return true;
}

// ------------------------------------- PUBLIC API --------------------------------------

// --------------- Tooling Configuration & Globs ----------------

/// Compiles `raw_pattern` into a non-backtracking 64-state `CompiledGlob64` (`E0019` on error).
pub fn compileGlob64(
    arena: *BumpArena,
    interner: *StringInterner,
    raw_pattern: []const u8,
    span: Span,
    sink: ?*DiagnosticSink,
) !?CompiledGlob64 {
    return compileGlob64Impl(arena, interner, raw_pattern, span, sink);
}

/// Merges `member_lint` over `ws_lint` when `member_lint.inherit` is `true` (`DR-25` §3.1).
pub fn resolveEffectivePackageLintConfig(
    arena: *BumpArena,
    member_lint: LintConfig,
    ws_lint: LintConfig,
) !LintConfig {
    return resolveEffectivePackageLintConfigImpl(arena, member_lint, ws_lint);
}

/// Merges `member_fmt` over `ws_fmt` when `member_fmt.inherit` is `true` (`DR-25` §3.1).
pub fn resolveEffectivePackageFmtConfig(
    arena: *BumpArena,
    member_fmt: FmtConfig,
    ws_fmt: FmtConfig,
) !FmtConfig {
    return resolveEffectivePackageFmtConfigImpl(arena, member_fmt, ws_fmt);
}

/// Merges `member_lsp` over `ws_lsp` when `member_lsp.inherit` is `true` (`DR-25` §3.1).
pub fn resolveEffectivePackageLspConfig(member_lsp: LspConfig, ws_lsp: LspConfig) LspConfig {
    return resolveEffectivePackageLspConfigImpl(member_lsp, ws_lsp);
}

/// Probes `dir_path` for forbidden standalone CoreX tool dotfiles, emitting `E0017` when present.
pub fn checkStrayToolConfigDotfiles(
    io: std.Io,
    dir_path: []const u8,
    fallback_file_id: FileId,
    sink: ?*DiagnosticSink,
) !bool {
    return checkStrayToolConfigDotfilesImpl(io, dir_path, fallback_file_id, sink);
}

// --------------- Package Naming & Target `@cfg` ---------------

/// Returns `true` iff `name` is a canonical non-reserved `kebab-case` package identifier (`DR-11` §1.1).
pub fn isValidPackageNameKebab(name: []const u8) bool {
    if (name.len == 0 or name.len > MAX_PKG_NAME_BYTES) return false;
    if (RESERVED_PKG_NAME_MAP.has(name) or lexer.KEYWORD_OR_PRIM_MAP.has(name)) return false;
    if (name[0] < 'a' or name[0] > 'z' or name[name.len - 1] == '-') return false;

    var snake_buf: [MAX_PKG_NAME_BYTES]u8 = undefined;
    var has_prev_dash = false;
    for (name, 0..) |ch_b, i| {
        if (ch_b == '-') {
            if (has_prev_dash) return false;
            has_prev_dash = true;
            snake_buf[i] = '_';
        } else if ((ch_b >= 'a' and ch_b <= 'z') or (ch_b >= '0' and ch_b <= '9')) {
            has_prev_dash = false;
            snake_buf[i] = ch_b;
        } else {
            return false;
        }
    }
    const snake_view = snake_buf[0..name.len];
    return !RESERVED_PKG_NAME_MAP.has(snake_view) and !lexer.KEYWORD_OR_PRIM_MAP.has(snake_view);
}

/// Validates `raw_name` as strict `kebab-case`, emitting `E0013` (with `_`->`-` / lowercase `SuggestedFix`).
pub fn validatePackageNameKebab(
    arena: *BumpArena,
    interner: *StringInterner,
    full_file_bytes: []const u8,
    raw_name: []const u8,
    span: Span,
    sink: ?*DiagnosticSink,
) !bool {
    if (isValidPackageNameKebab(raw_name)) return true;

    if (sink) |diag_sink| {
        var norm_buf: [MAX_PKG_NAME_BYTES]u8 = undefined;
        var fix_arr: [1]SuggestedFix = undefined;
        var fix_len: usize = 0;

        if (raw_name.len > 0 and raw_name.len <= MAX_PKG_NAME_BYTES) {
            for (raw_name, 0..) |ch_b, i| {
                norm_buf[i] = if (ch_b == '_') '-' else std.ascii.toLower(ch_b);
            }
            const candidate = norm_buf[0..raw_name.len];
            if (isValidPackageNameKebab(candidate) and span.end_byte <= full_file_bytes.len) {
                const raw_span_slice = full_file_bytes[span.start_byte..span.end_byte];
                const replacement_str = if (raw_span_slice.len >= 2 and
                    (raw_span_slice[0] == '"' or raw_span_slice[0] == '\''))
                    try std.fmt.allocPrint(
                        arena.asAllocator(),
                        "{c}{s}{c}",
                        .{ raw_span_slice[0], candidate, raw_span_slice[0] },
                    )
                else
                    try arena.dupe(u8, candidate);

                const edit = TextEdit{
                    .file_id = span.file_id,
                    .start_byte = span.start_byte,
                    .end_byte = span.end_byte,
                    .replacement_id = try interner.intern(replacement_str),
                };
                fix_arr[0] = .{
                    .message = "normalize package identifier to canonical `kebab-case`",
                    .applicability = .machine_applicable,
                    .priority = .syntax_canonicalization,
                    .edits = try diag_sink.arena.dupe(TextEdit, &.{edit}),
                };
                fix_len = 1;
            }
        }

        const msg = if (RESERVED_PKG_NAME_MAP.has(raw_name) or lexer.KEYWORD_OR_PRIM_MAP.has(raw_name))
            "reserved language/module identifier cannot be used as a package name"
        else
            "package and dependency names in `corex.toml` must be canonical `kebab-case` (`[a-z][a-z0-9-]*`, no `_` or `--`)";

        try diag_sink.emit(.{
            .code = .e0013_invalid_manifest_or_pkg_name,
            .severity = .err,
            .primary_span = span,
            .message = msg,
            .suggestions = fix_arr[0..fix_len],
        });
    }
    return false;
}

/// Converts a validated `kebab-case` package name into its bijective `snake_case` `.cx` module name in `arena`.
pub fn kebabToSnakeModule(arena: *BumpArena, kebab: []const u8) ![]u8 {
    const out = try arena.allocSlice(u8, kebab.len);
    for (kebab, 0..) |ch_b, i| {
        out[i] = if (ch_b == '-') '_' else ch_b;
    }
    return out;
}

/// Converts a validated `snake_case` `.cx` module name into its bijective `kebab-case` package name in `arena`.
pub fn snakeModuleToKebab(arena: *BumpArena, snake: []const u8) ![]u8 {
    const out = try arena.allocSlice(u8, snake.len);
    for (snake, 0..) |ch_b, i| {
        out[i] = if (ch_b == '_') '-' else ch_b;
    }
    return out;
}

/// Validates `raw_pkg_name` and allocates its bijective `snake_case` `.cx` module name (`null` if invalid).
pub fn canonicalPkgNameToSnakeAlloc(allocator: std.mem.Allocator, raw_pkg_name: []const u8) !?[]u8 {
    if (!isValidPackageNameKebab(raw_pkg_name)) return null;
    const out = try allocator.alloc(u8, raw_pkg_name.len);
    for (raw_pkg_name, 0..) |ch_b, i| {
        out[i] = if (ch_b == '-') '_' else ch_b;
    }
    return out;
}

/// Validates a `corex.toml` `target = "<CoreX @cfg expr>"` string and evaluates it against `cfg_env` (`E0013` on error).
pub fn validateAndEvalManifestTargetCfg(
    arena: *BumpArena,
    interner: *StringInterner,
    doc: ?*const TomlDocumentView,
    raw_predicate: []const u8,
    cfg_env: *const CfgEnv,
    span: Span,
    anchor_opt: ?TomlSpanAnchor,
    sink: ?*DiagnosticSink,
) !?bool {
    const trimmed = std.mem.trim(u8, raw_predicate, " \t\r\n");
    if (trimmed.len == 0) {
        try emitManifestFieldErr(sink, span, "`target` `@cfg` predicate string cannot be empty");
        return null;
    }

    // [1] Reject Rust-style `cfg(…)`, `all(…)`, `any(…)`, `target_os`, `target_arch`, `&&`, `||`, `!` with `E0013`:
    const is_rust_style = std.mem.startsWith(u8, trimmed, "cfg(") or
        std.mem.startsWith(u8, trimmed, "all(") or
        std.mem.startsWith(u8, trimmed, "any(") or
        std.mem.indexOf(u8, trimmed, "target_os") != null or
        std.mem.indexOf(u8, trimmed, "target_arch") != null or
        std.mem.indexOf(u8, trimmed, "target_env") != null or
        std.mem.eql(u8, trimmed, "unix") or
        std.mem.eql(u8, trimmed, "windows");

    if (is_rust_style) {
        if (sink) |diag_sink| {
            var fixes: [1]SuggestedFix = undefined;
            var fix_count: usize = 0;
            if (try suggestCorexTargetCfgFromRust(arena, trimmed)) |rewritten| {
                if (doc) |doc_view| {
                    if (anchor_opt) |anchor| {
                        const edit = try buildScalarReplaceEdit(doc_view, interner, anchor, rewritten);
                        fixes[0] = .{
                            .message = "rewrite Rust `cfg(…)` target filter to canonical CoreX `@cfg` syntax",
                            .applicability = .machine_applicable,
                            .priority = .syntax_canonicalization,
                            .edits = try diag_sink.arena.dupe(TextEdit, &.{edit}),
                        };
                        fix_count = 1;
                    }
                }
            }
            try diag_sink.emit(.{
                .code = .e0013_invalid_manifest_or_pkg_name,
                .severity = .err,
                .primary_span = span,
                .message = "Rust-style `cfg(…)` syntax is invalid in `corex.toml`; write a CoreX `@cfg` expression (e.g., `target.os == .Linux`)",
                .suggestions = fixes[0..fix_count],
            });
        }
        return null;
    }

    // [2] Pre-tokenize `trimmed` to bound token count and reject invalid/escape tokens before `@cfg(…)` parsing:
    const alloc = arena.backing_allocator;
    const nul_src = try arena.dupeZ(trimmed);
    var pre_tok_buf = TokenBuffer.init(alloc);
    defer pre_tok_buf.deinit();
    try lexer.tokenize(nul_src, FileId.fromInt(0), &pre_tok_buf, null, null);

    const pre_count = pre_tok_buf.countTokens();
    if (pre_count > 120) {
        try emitManifestFieldErr(sink, span, "`target` `@cfg` predicate exceeds maximum token complexity (`120` tokens)");
        return null;
    }
    var paren_balance: i32 = 0;
    var check_i: u32 = 0;
    while (check_i < pre_count) : (check_i += 1) {
        const tk = pre_tok_buf.getToken(TokenIndex.fromInt(check_i)).kind;
        if (tk == .invalid_token or tk == .pipepipe or tk == .bang or tk == .amp) {
            try emitManifestFieldErr(
                sink,
                span,
                "invalid operator in `target` `@cfg` predicate; use CoreX `and`, `or`, `not`, `==`, `!=`, or `is`",
            );
            return null;
        }
        if (tk == .semi or tk == .lbrace or tk == .rbrace or tk == .at) {
            try emitManifestFieldErr(sink, span, "malformed CoreX `@cfg` expression in dependency `target` field");
            return null;
        }
        if (tk == .lparen) {
            paren_balance += 1;
        } else if (tk == .rparen) {
            paren_balance -= 1;
            if (paren_balance < 0) {
                try emitManifestFieldErr(sink, span, "unbalanced `)` in dependency `target` `@cfg` predicate");
                return null;
            }
        }
    }
    if (paren_balance != 0) {
        try emitManifestFieldErr(sink, span, "unclosed `(` in dependency `target` `@cfg` predicate");
        return null;
    }

    // [3] Delegate to CoreX's canonical parser + `symbol_resolver.evaluateCstNodeCfgWithEnv` with $O(1)$ feature sets:
    const probe_src = try std.fmt.allocPrintSentinel(arena.asAllocator(), "@cfg({s}) fn cx_cfg_probe() {{}}", .{trimmed}, 0);
    var probe_toks = TokenBuffer.init(alloc);
    defer probe_toks.deinit();
    var probe_cst = LosslessCstArena.init(alloc);
    defer probe_cst.deinit();
    var probe_ast = AstArena.init(alloc);
    defer probe_ast.deinit();
    var probe_sink = DiagnosticSink.init(alloc);
    defer probe_sink.deinit();

    _ = try parser.parseSource(
        probe_src,
        FileId.fromInt(0),
        &probe_toks,
        &probe_cst,
        &probe_ast,
        &probe_sink,
        interner,
    );
    if (probe_cst.has_parse_errors or probe_sink.error_count > 0 or probe_cst.countNodes() < 2) {
        try emitManifestFieldErr(sink, span, "malformed CoreX `@cfg` expression in dependency `target` field");
        return null;
    }

    var eff_env = cfg_env.*;
    var local_sym_table: ?symbol_resolver.SymbolTable = null;
    defer if (local_sym_table) |*st| st.deinit();

    if (eff_env.sym_table_features == null and (eff_env.enabled_features.len > 0 or eff_env.declared_features != null)) {
        var st = try symbol_resolver.SymbolTable.init(alloc, interner);
        errdefer st.deinit();
        if (eff_env.declared_features) |decl_feats| {
            try st.has_package_feature_manifest.put(st.allocator, eff_env.owner_pkg_id, {});
            for (decl_feats) |feat_str| {
                try st.declarePackageFeature(eff_env.owner_pkg_id, try interner.intern(feat_str));
            }
        }
        for (eff_env.enabled_features) |en_str| {
            try st.enablePackageFeature(eff_env.owner_pkg_id, try interner.intern(en_str));
        }
        local_sym_table = st;
        eff_env.enabled_features = &.{};
        eff_env.declared_features = null;
        eff_env.sym_table_features = &local_sym_table.?;
    }

    const eval_ok = try symbol_resolver.evaluateCstNodeCfgWithEnv(
        &eff_env,
        FileId.fromInt(0),
        probe_src,
        &probe_toks,
        &probe_cst,
        CstNodeIndex.fromInt(1),
        &probe_sink,
    );
    if (probe_sink.error_count > 0) {
        const detail = if (probe_sink.diagnostics.items.len > 0)
            try arena.dupe(u8, probe_sink.diagnostics.items[0].message)
        else
            "malformed CoreX `@cfg` expression in dependency `target` field";
        try emitManifestFieldErr(sink, span, detail);
        return null;
    }
    return eval_ok;
}

// ------------- Script Frontmatter & Inline `use` --------------

/// Extracts optional `#!` + `--- … ---` TOML frontmatter and blanks prefix non-`\r`/`\n` bytes to `' '` (`0x20`).
pub fn extractScriptFrontmatter(
    arena: *BumpArena,
    file_id: FileId,
    raw_source: []const u8,
    sink: ?*DiagnosticSink,
) !?ScriptFrontmatterExtract {
    var cursor: usize = 0;
    var cur_line: u32 = 0;

    // [0] Skip optional leading UTF-8 BOM (`0xEF 0xBB 0xBF`), blanking its 3 bytes to `' '` below:
    if (std.mem.startsWith(u8, raw_source, "\xEF\xBB\xBF")) {
        cursor = 3;
    }

    // [1] Advance past optional line-1 `#!…` shebang:
    if (std.mem.startsWith(u8, raw_source[cursor..], "#!")) {
        while (cursor < raw_source.len and raw_source[cursor] != '\n') : (cursor += 1) {}
        if (cursor < raw_source.len and raw_source[cursor] == '\n') {
            cursor += 1;
            cur_line += 1;
        }
    }

    // [2] Check for `---` opening frontmatter fence:
    if (!std.mem.startsWith(u8, raw_source[cursor..], "---")) {
        const blanked = try arena.dupeZ(raw_source);
        var i: usize = 0;
        while (i < cursor) : (i += 1) {
            if (blanked[i] != '\n' and blanked[i] != '\r') blanked[i] = ' ';
        }
        return .{
            .has_frontmatter = false,
            .blanked_cx_source = blanked,
            .toml_slice = "",
            .fm_start_byte = @intCast(cursor),
            .fm_start_line = cur_line,
            .prefix_end_byte = @intCast(cursor),
        };
    }

    var fence_after = cursor + 3;
    while (fence_after < raw_source.len and (raw_source[fence_after] == ' ' or raw_source[fence_after] == '\t')) : (fence_after += 1) {}
    if (fence_after < raw_source.len and raw_source[fence_after] == '\r') fence_after += 1;
    if (fence_after >= raw_source.len or raw_source[fence_after] != '\n') {
        try emitManifestFieldErr(
            sink,
            Span.init(file_id, @intCast(cursor), @intCast(@min(fence_after + 1, raw_source.len))),
            "opening `---` script frontmatter fence must be followed immediately by a newline",
        );
        return null;
    }

    const fm_start = fence_after + 1;
    const fm_line = cur_line + 1;
    var scan = fm_start;
    var found_close_start: ?usize = null;
    var close_end: usize = raw_source.len;

    while (scan < raw_source.len) {
        const line_start = scan;
        while (scan < raw_source.len and raw_source[scan] != '\n') : (scan += 1) {}
        const line_end_no_lf = if (scan > line_start and raw_source[scan - 1] == '\r') scan - 1 else scan;
        const trimmed_line = std.mem.trimEnd(u8, raw_source[line_start..line_end_no_lf], " \t");
        if (scan < raw_source.len and raw_source[scan] == '\n') scan += 1;
        if (std.mem.eql(u8, trimmed_line, "---")) {
            found_close_start = line_start;
            close_end = scan;
            break;
        }
    }

    if (found_close_start == null) {
        try emitManifestFieldErr(
            sink,
            Span.init(file_id, @intCast(cursor), @intCast(cursor + 3)),
            "unclosed `---` TOML frontmatter block in `.cx` script",
        );
        return null;
    }

    if (found_close_start.? - fm_start > MAX_TOML_BYTES) {
        try emitManifestFieldErr(
            sink,
            Span.init(file_id, @intCast(fm_start), @intCast(found_close_start.?)),
            "script TOML frontmatter exceeds `1 MiB` `MAX_TOML_BYTES` limit",
        );
        return null;
    }

    // [3] Blank `[0 .. close_end)` non-`\r`/`\n` bytes to `' '` (`0x20`) preserving 100% of `.cx` offsets:
    const blanked_cx = try arena.dupeZ(raw_source);
    var idx: usize = 0;
    while (idx < close_end) : (idx += 1) {
        if (blanked_cx[idx] != '\n' and blanked_cx[idx] != '\r') {
            blanked_cx[idx] = ' ';
        }
    }
    return .{
        .has_frontmatter = true,
        .blanked_cx_source = blanked_cx,
        .toml_slice = raw_source[fm_start..found_close_start.?],
        .fm_start_byte = @intCast(fm_start),
        .fm_start_line = fm_line,
        .prefix_end_byte = @intCast(close_end),
    };
}

/// Computes `<corex_home>/target/scripts/<64-hex-blake3(canonical_realpath)>/corex.lock` (`DR-11` §1.2).
pub fn computeScriptLockfilePath(
    io: std.Io,
    allocator: std.mem.Allocator,
    corex_home: []const u8,
    script_path: []const u8,
) ![]u8 {
    const resolved_opt = std.Io.Dir.cwd().realPathFileAlloc(io, script_path, allocator) catch null;
    defer if (resolved_opt) |buf| allocator.free(buf);
    const raw_canon = resolved_opt orelse script_path;

    const norm_buf = try allocator.alloc(u8, raw_canon.len);
    defer allocator.free(norm_buf);
    for (raw_canon, 0..) |ch_b, i| {
        norm_buf[i] = if (ch_b == '\\') '/' else ch_b;
    }

    var digest: [32]u8 = undefined;
    std.crypto.hash.Blake3.hash(norm_buf, &digest, .{});
    const hex = std.fmt.bytesToHex(digest, .lower);
    const trimmed_home = std.mem.trimEnd(u8, corex_home, "/\\");
    return std.fmt.allocPrint(allocator, "{s}/target/scripts/{s}/corex.lock", .{ trimmed_home, &hex });
}

/// Parses and validates an inline `use "<spec>" as <snake_alias>;` import (`E0013` on invalid spec/alias).
pub fn parseInlineUseSpec(
    arena: *BumpArena,
    interner: *StringInterner,
    raw_spec: []const u8,
    raw_alias: []const u8,
    spec_span: Span,
    alias_span: Span,
    sink: ?*DiagnosticSink,
) !?InlineUseSpec {
    if (!isValidSnakeAlias(raw_alias)) {
        try emitManifestFieldErr(
            sink,
            alias_span,
            "inline package import alias must be a valid non-reserved `snake_case` identifier",
        );
        return null;
    }
    const alias_snake_id = try interner.intern(raw_alias);
    const alias_kebab_str = try snakeModuleToKebab(arena, raw_alias);
    if (!isValidPackageNameKebab(alias_kebab_str)) {
        try emitManifestFieldErr(sink, alias_span, "inline package import alias cannot contain consecutive `__` or trailing `_`");
        return null;
    }
    const alias_kebab_id = try interner.intern(alias_kebab_str);

    if (raw_spec.len == 0 or raw_spec.len > 512) {
        try emitManifestFieldErr(sink, spec_span, "inline package import specifier must be `1..512` bytes");
        return null;
    }
    for (raw_spec) |ch_b| {
        if (ch_b < 0x20 or ch_b == 0x7F) {
            try emitManifestFieldErr(sink, spec_span, "inline package import specifier cannot contain control bytes");
            return null;
        }
        switch (ch_b) {
            '"', '\'', '\\', '{', '}', '[', ']', '#' => {
                try emitManifestFieldErr(
                    sink,
                    spec_span,
                    "inline package import specifier contains forbidden TOML metacharacter (`\"`, `'`, `\\`, `{`, `}`, `[`, `]`, or `#`)",
                );
                return null;
            },
            else => {},
        }
    }

    // [1] Local relative directory path (`./…` or `../…`):
    if (std.mem.startsWith(u8, raw_spec, "./") or std.mem.startsWith(u8, raw_spec, "../")) {
        if (std.mem.indexOfScalar(u8, raw_spec, ':') != null) {
            try emitManifestFieldErr(sink, spec_span, "local inline `use` path cannot contain `:` or drive letters");
            return null;
        }
        var has_named_seg = false;
        var seg_iter = std.mem.splitScalar(u8, std.mem.trimEnd(u8, raw_spec, "/"), '/');
        while (seg_iter.next()) |seg| {
            if (seg.len == 0) {
                try emitManifestFieldErr(sink, spec_span, "local inline `use` path cannot contain empty `/` segments");
                return null;
            }
            if (!std.mem.eql(u8, seg, ".") and !std.mem.eql(u8, seg, "..")) {
                has_named_seg = true;
            }
        }
        if (!has_named_seg) {
            try emitManifestFieldErr(sink, spec_span, "local inline `use` path must name a target package directory");
            return null;
        }
        return .{
            .alias_snake = alias_snake_id,
            .alias_kebab = alias_kebab_id,
            .package_kebab = alias_kebab_id,
            .source = .{ .path = .{ .rel_path = try interner.intern(raw_spec) } },
        };
    }

    // [2] Git / GitHub / HTTPS URL (`github.com/org/repo@v1.0`, `https://…`, `git+https://…`, `git+file://…`):
    if (std.mem.startsWith(u8, raw_spec, "github.com/") or
        std.mem.startsWith(u8, raw_spec, "gitlab.com/") or
        std.mem.startsWith(u8, raw_spec, "https://") or
        std.mem.startsWith(u8, raw_spec, "git+https://") or
        std.mem.startsWith(u8, raw_spec, "git+ssh://") or
        std.mem.startsWith(u8, raw_spec, "git+file://"))
    {
        const git_src = (try parseShorthandGitOrReq(arena, interner, raw_spec)) orelse {
            try emitManifestFieldErr(sink, spec_span, "invalid Git/URL specifier in inline `use` import");
            return null;
        };
        const url_str = interner.get(git_src.git.url);
        const trimmed_url = if (std.mem.endsWith(u8, url_str, ".git")) url_str[0 .. url_str.len - 4] else url_str;
        const last_seg = if (std.mem.lastIndexOfScalar(u8, trimmed_url, '/')) |sl| trimmed_url[sl + 1 ..] else trimmed_url;
        const derived_pkg = if (isValidPackageNameKebab(last_seg)) try interner.intern(last_seg) else alias_kebab_id;
        return .{
            .alias_snake = alias_snake_id,
            .alias_kebab = alias_kebab_id,
            .package_kebab = derived_pkg,
            .source = git_src,
        };
    }

    // [3] Registry specifier (`registry:<kebab>@<req>` or `<kebab>@<req>`):
    const stripped = if (std.mem.startsWith(u8, raw_spec, "registry:")) raw_spec[9..] else raw_spec;
    const at_pos = std.mem.indexOfScalar(u8, stripped, '@') orelse {
        try emitManifestFieldErr(
            sink,
            spec_span,
            "registry inline `use` specifier requires explicit `@<version_req>` (e.g., `\"serde-json@1.4.2\"`)",
        );
        return null;
    };
    const pkg_name = stripped[0..at_pos];
    const req_str = stripped[at_pos + 1 ..];
    if (!isValidPackageNameKebab(pkg_name)) {
        try emitManifestFieldErr(
            sink,
            spec_span,
            "package name in inline `use` specifier must be canonical `kebab-case`",
        );
        return null;
    }
    const ver_req = (try VersionReq.parse(interner, req_str)) orelse {
        try emitManifestFieldErr(sink, spec_span, "invalid SemVer version requirement in inline `use` specifier");
        return null;
    };
    return .{
        .alias_snake = alias_snake_id,
        .alias_kebab = alias_kebab_id,
        .package_kebab = try interner.intern(pkg_name),
        .source = .{ .registry = ver_req },
    };
}

// ------------ Manifest, Workspace & Patch Surgery -------------

/// Parses a raw TOML slice into a lossless `TomlDocumentView` (`8B` tokens + `16B` CST nodes + `24B` anchors).
pub fn parseTomlDocument(
    allocator: std.mem.Allocator,
    file_id: FileId,
    full_file_bytes: []const u8,
    toml_slice: []const u8,
    base_byte_offset: u32,
    base_line_offset: u32,
    is_script_frontmatter: bool,
    diag_code: DiagnosticCode,
    sink: ?*DiagnosticSink,
) !TomlDocumentView {
    var doc = TomlDocumentView{
        .file_id = file_id,
        .full_file_bytes = full_file_bytes,
        .toml_slice = toml_slice,
        .base_byte_offset = base_byte_offset,
        .base_line_offset = base_line_offset,
        .is_script_frontmatter = is_script_frontmatter,
    };
    errdefer doc.deinit(allocator);

    try lexTomlSlice(allocator, &doc, diag_code, sink);
    if (doc.tokens.tokens.len == 0) return doc;

    var dom_arena = BumpArena.init(allocator);
    defer dom_arena.deinit();
    var parser_inst = TomlParser{
        .allocator = allocator,
        .dom_arena = &dom_arena,
        .doc = &doc,
        .diag_code = diag_code,
        .sink = sink,
    };
    _ = try parser_inst.parseDocument();
    return doc;
}

/// Internal helper parsing `corex.toml` with optional inherited `[workspace.package]` metadata.
fn parseManifestWithInheritedPkg(
    allocator: std.mem.Allocator,
    arena: *BumpArena,
    interner: *StringInterner,
    file_id: FileId,
    source_bytes: []const u8,
    cfg_env: *const CfgEnv,
    inherited_ws_pkg: ?WorkspacePackageMeta,
    sink: ?*DiagnosticSink,
) !ParsedManifestResult {
    var doc = TomlDocumentView{
        .file_id = file_id,
        .full_file_bytes = source_bytes,
        .toml_slice = source_bytes,
    };
    errdefer doc.deinit(allocator);

    try lexTomlSlice(allocator, &doc, .e0013_invalid_manifest_or_pkg_name, sink);
    if (doc.tokens.tokens.len == 0) {
        var empty_manifest = Manifest{ .file_id = file_id, .is_script = false };
        empty_manifest.root_manifest_blake3 = computeNormalizedManifestBlake3(&empty_manifest, interner);
        return .{ .manifest = empty_manifest, .doc = doc };
    }

    var dom_arena = BumpArena.init(allocator);
    defer dom_arena.deinit();
    var parser_inst = TomlParser{
        .allocator = allocator,
        .dom_arena = &dom_arena,
        .doc = &doc,
        .diag_code = .e0013_invalid_manifest_or_pkg_name,
        .sink = sink,
    };
    const root_tbl = try parser_inst.parseDocument();
    const manifest = try lowerDomToManifest(
        arena,
        interner,
        &doc,
        root_tbl,
        false,
        cfg_env,
        inherited_ws_pkg,
        sink,
    );
    return .{ .manifest = manifest, .doc = doc };
}

/// Parses and validates a `corex.toml` buffer into `Manifest` + lossless `TomlDocumentView`.
pub fn parseManifest(
    allocator: std.mem.Allocator,
    arena: *BumpArena,
    interner: *StringInterner,
    file_id: FileId,
    source_bytes: []const u8,
    cfg_env: *const CfgEnv,
    sink: ?*DiagnosticSink,
) !ParsedManifestResult {
    return parseManifestWithInheritedPkg(
        allocator,
        arena,
        interner,
        file_id,
        source_bytes,
        cfg_env,
        null,
        sink,
    );
}

/// Parses a single-file `.cx` script's extracted `ScriptFrontmatterExtract` into a validated `Manifest`.
pub fn parseScriptFrontmatterManifest(
    allocator: std.mem.Allocator,
    arena: *BumpArena,
    interner: *StringInterner,
    file_id: FileId,
    full_script_bytes: []const u8,
    extracted: ScriptFrontmatterExtract,
    cfg_env: *const CfgEnv,
    sink: ?*DiagnosticSink,
) !ParsedManifestResult {
    var doc = TomlDocumentView{
        .file_id = file_id,
        .full_file_bytes = full_script_bytes,
        .toml_slice = extracted.toml_slice,
        .base_byte_offset = extracted.fm_start_byte,
        .base_line_offset = extracted.fm_start_line,
        .is_script_frontmatter = true,
    };
    errdefer doc.deinit(allocator);

    try lexTomlSlice(allocator, &doc, .e0013_invalid_manifest_or_pkg_name, sink);
    if (doc.tokens.tokens.len == 0) {
        var fallback_manifest = Manifest{
            .file_id = file_id,
            .is_script = true,
            .package = .{
                .name_kebab = try interner.intern("script-pkg"),
                .module_snake = try interner.intern("script_pkg"),
                .version = .{ .major = 0, .minor = 1, .patch = 0 },
                .edition = try interner.intern(DEFAULT_COREX_EDITION),
                .publish = .{ .is_allowed = false },
            },
        };
        fallback_manifest.root_manifest_blake3 = computeNormalizedManifestBlake3(&fallback_manifest, interner);
        return .{ .manifest = fallback_manifest, .doc = doc };
    }

    var dom_arena = BumpArena.init(allocator);
    defer dom_arena.deinit();
    var parser_inst = TomlParser{
        .allocator = allocator,
        .dom_arena = &dom_arena,
        .doc = &doc,
        .diag_code = .e0013_invalid_manifest_or_pkg_name,
        .sink = sink,
    };
    const root_tbl = try parser_inst.parseDocument();
    var manifest = try lowerDomToManifest(arena, interner, &doc, root_tbl, true, cfg_env, null, sink);
    if (manifest.package == null) {
        manifest.package = .{
            .name_kebab = try interner.intern("script-pkg"),
            .module_snake = try interner.intern("script_pkg"),
            .version = .{ .major = 0, .minor = 1, .patch = 0 },
            .edition = try interner.intern(DEFAULT_COREX_EDITION),
            .publish = .{ .is_allowed = false },
        };
        manifest.root_manifest_blake3 = computeNormalizedManifestBlake3(&manifest, interner);
    }
    return .{ .manifest = manifest, .doc = doc };
}

/// Computes the comment/whitespace/ordering-invariant 256-bit `BLAKE3` digest of `manifest`.
pub fn computeNormalizedManifestBlake3(
    manifest: *const Manifest,
    interner: *const StringInterner,
) [32]u8 {
    var hasher = std.crypto.hash.Blake3.init(.{});
    hasher.update(MANIFEST_NORM_DOMAIN);
    hasher.update(&[1]u8{@intFromBool(manifest.is_script)});

    if (manifest.package) |pkg| {
        hasher.update(&[1]u8{1});
        hashLenPrefixedBytes(&hasher, interner.get(pkg.name_kebab));
        hashSemVerValue(&hasher, pkg.version, interner);
        hashLenPrefixedBytes(&hasher, interner.get(pkg.corex_req));
        hashLenPrefixedBytes(&hasher, interner.get(pkg.edition));
        hashLenPrefixedBytes(&hasher, interner.get(pkg.root_module));
        hashLenPrefixedBytes(&hasher, interner.get(pkg.links));
        hashPublishPolicy(&hasher, pkg.publish, interner);
    } else {
        hasher.update(&[1]u8{0});
    }

    if (manifest.lib_target) |lib| {
        hasher.update(&[1]u8{1});
        hashLenPrefixedBytes(&hasher, interner.get(lib.name_snake));
        hashLenPrefixedBytes(&hasher, interner.get(lib.path));
    } else {
        hasher.update(&[1]u8{0});
    }

    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(manifest.bin_targets.len))));
    for (manifest.bin_targets) |bin_tgt| {
        hashLenPrefixedBytes(&hasher, interner.get(bin_tgt.name_kebab));
        hashLenPrefixedBytes(&hasher, interner.get(bin_tgt.path));
    }

    hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(manifest.features.len))));
    for (manifest.features) |feat| {
        hashLenPrefixedBytes(&hasher, interner.get(feat.name));
        hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(feat.activations.len))));
        for (feat.activations) |act_id| hashLenPrefixedBytes(&hasher, interner.get(act_id));
    }

    hashDependencySlice(&hasher, manifest.dependencies, interner);
    hashExcludeSlice(&hasher, manifest.excludes, interner);
    hashPatchSlice(&hasher, manifest.patches, interner);
    hashSecurityPolicy(&hasher, manifest.security, interner);

    if (manifest.workspace) |ws| {
        hasher.update(&[1]u8{1});
        hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(ws.members.len))));
        for (ws.members) |mid| hashLenPrefixedBytes(&hasher, interner.get(mid));
        hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(ws.default_members.len))));
        for (ws.default_members) |def_id| hashLenPrefixedBytes(&hasher, interner.get(def_id));
        hasher.update(&std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(ws.exclude.len))));
        for (ws.exclude) |ex_dir_id| hashLenPrefixedBytes(&hasher, interner.get(ex_dir_id));

        if (ws.package) |ws_pkg| {
            hasher.update(&[1]u8{1});
            if (ws_pkg.version) |ws_ver| {
                hasher.update(&[1]u8{1});
                hashSemVerValue(&hasher, ws_ver, interner);
            } else {
                hasher.update(&[1]u8{0});
            }
            hashLenPrefixedBytes(&hasher, if (ws_pkg.corex_req) |cid| interner.get(cid) else "");
            hashLenPrefixedBytes(&hasher, if (ws_pkg.edition) |eid| interner.get(eid) else "");
            hashLenPrefixedBytes(&hasher, if (ws_pkg.description) |did| interner.get(did) else "");
            hashLenPrefixedBytes(&hasher, if (ws_pkg.license) |lid| interner.get(lid) else "");
            hashLenPrefixedBytes(&hasher, if (ws_pkg.repository) |rid| interner.get(rid) else "");
            if (ws_pkg.publish) |ws_pub| {
                hasher.update(&[1]u8{1});
                hashPublishPolicy(&hasher, ws_pub, interner);
            } else {
                hasher.update(&[1]u8{0});
            }
        } else {
            hasher.update(&[1]u8{0});
        }

        hashDependencySlice(&hasher, ws.dependencies, interner);
        hashExcludeSlice(&hasher, ws.excludes, interner);
        hashPatchSlice(&hasher, ws.patches, interner);
        if (ws.security) |ws_sec| {
            hasher.update(&[1]u8{1});
            hashSecurityPolicy(&hasher, ws_sec, interner);
        } else {
            hasher.update(&[1]u8{0});
        }
    } else {
        hasher.update(&[1]u8{0});
    }

    var out: [32]u8 = undefined;
    hasher.final(&out);
    return out;
}

/// Wraps a single parsed `Manifest` into a `WorkspaceManifestBundle` for `pkg_resolver`.
pub fn buildBundleFromSingleManifest(
    allocator: std.mem.Allocator,
    root_dir: []const u8,
    manifest_path: []const u8,
    manifest: Manifest,
    is_script: bool,
) !WorkspaceManifestBundle {
    var arena = BumpArena.init(allocator);
    errdefer arena.deinit();

    const owned_root = try arena.dupe(u8, root_dir);
    const owned_path = try arena.dupe(u8, manifest_path);
    const members = try arena.allocSlice(WorkspaceMember, 1);
    members[0] = .{
        .rel_dir = ".",
        .abs_dir = owned_root,
        .manifest_path = owned_path,
        .manifest = manifest,
        .is_default_member = true,
    };
    return .{
        .arena = arena,
        .workspace_root_dir = owned_root,
        .root_manifest_path = owned_path,
        .root_manifest = manifest,
        .members = members,
        .primary_member_index = 0,
        .is_script = is_script,
        .root_manifest_blake3 = manifest.root_manifest_blake3,
    };
}

/// Loads a root `corex.toml` and expands any `[workspace].members` (including `/*` globs) into `WorkspaceManifestBundle`.
pub fn loadWorkspaceManifestBundle(
    io: std.Io,
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    root_manifest_path: []const u8,
    root_file_id: FileId,
    cfg_env: *const CfgEnv,
    sink: ?*DiagnosticSink,
) !WorkspaceManifestBundle {
    var arena = BumpArena.init(allocator);
    errdefer arena.deinit();

    var has_oversized_root = false;
    const root_bytes = std.Io.Dir.cwd().readFileAlloc(
        io,
        root_manifest_path,
        allocator,
        .limited(MAX_TOML_BYTES + 1),
    ) catch |read_err| blk_root: {
        if (read_err == error.StreamTooLong) {
            has_oversized_root = true;
            try emitManifestFieldErr(
                sink,
                Span.init(root_file_id, 0, 0),
                "TOML document exceeds maximum 1 MiB size limit (`MAX_TOML_BYTES`)",
            );
            break :blk_root try allocator.alloc(u8, 0);
        }
        return read_err;
    };
    defer allocator.free(root_bytes);

    var parsed_root: ParsedManifestResult = if (has_oversized_root) blk_empty: {
        var empty_m = Manifest{ .file_id = root_file_id };
        empty_m.root_manifest_blake3 = computeNormalizedManifestBlake3(&empty_m, interner);
        break :blk_empty .{
            .manifest = empty_m,
            .doc = TomlDocumentView{
                .file_id = root_file_id,
                .full_file_bytes = &.{},
                .toml_slice = &.{},
                .has_syntax_errors = true,
            },
        };
    } else try parseManifest(allocator, &arena, interner, root_file_id, root_bytes, cfg_env, sink);
    defer parsed_root.doc.deinit(allocator);

    if (parsed_root.manifest.workspace == null) {
        parsed_root.manifest.dependencies = try resolveWorkspaceInheritedDeps(
            allocator,
            &arena,
            interner,
            parsed_root.manifest.dependencies,
            &.{},
            sink,
        );
    }

    const root_dir_raw = std.fs.path.dirname(root_manifest_path) orelse ".";
    const owned_root_dir = try arena.dupe(u8, root_dir_raw);
    const owned_root_path = try arena.dupe(u8, root_manifest_path);
    _ = try checkStrayToolConfigDotfiles(io, owned_root_dir, root_file_id, sink);

    var member_list: std.ArrayList(WorkspaceMember) = .empty;
    if (parsed_root.manifest.package != null) {
        try member_list.append(arena.asAllocator(), .{
            .rel_dir = ".",
            .abs_dir = owned_root_dir,
            .manifest_path = owned_root_path,
            .manifest = parsed_root.manifest,
            .is_default_member = true,
        });
    }

    if (parsed_root.manifest.workspace) |ws_cfg| {
        var rel_dirs: std.ArrayList(MemberDirCandidate) = .empty;
        defer rel_dirs.deinit(allocator);

        var exclude_set: std.StringHashMapUnmanaged(void) = .empty;
        defer exclude_set.deinit(allocator);
        for (ws_cfg.exclude) |ex_id| {
            try exclude_set.put(allocator, interner.get(ex_id), {});
        }

        var default_member_set: std.StringHashMapUnmanaged(void) = .empty;
        defer default_member_set.deinit(allocator);
        for (ws_cfg.default_members) |def_id| {
            try default_member_set.put(allocator, interner.get(def_id), {});
        }

        for (ws_cfg.members) |pat_id| {
            const pat = interner.get(pat_id);
            if (std.mem.endsWith(u8, pat, "/*")) {
                const prefix = pat[0 .. pat.len - 2];
                const scan_dir_path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ owned_root_dir, prefix });
                defer allocator.free(scan_dir_path);
                if (std.Io.Dir.cwd().openDir(io, scan_dir_path, .{ .iterate = true })) |opened_sub| {
                    var sub_dir = opened_sub;
                    defer sub_dir.close(io);
                    var iter = sub_dir.iterate();
                    while (try iter.next(io)) |entry| {
                        if (entry.kind != .directory) continue;
                        const cand_rel = try std.fmt.allocPrint(arena.asAllocator(), "{s}/{s}", .{ prefix, entry.name });
                        try rel_dirs.append(allocator, .{ .rel_dir = cand_rel, .is_explicit = false });
                    }
                } else |_| {}
            } else {
                try rel_dirs.append(allocator, .{ .rel_dir = pat, .is_explicit = true });
            }
        }

        std.mem.sort(MemberDirCandidate, rel_dirs.items, {}, struct {
            /// Sorts relative member directories in ASCII ascending order (`is_explicit` wins ties).
            fn lessThan(_: void, lhs: MemberDirCandidate, rhs: MemberDirCandidate) bool {
                const ord = std.mem.order(u8, lhs.rel_dir, rhs.rel_dir);
                if (ord != .eq) return ord == .lt;
                return lhs.is_explicit and !rhs.is_explicit;
            }
        }.lessThan);

        var next_fid = root_file_id.asInt() +| 1;
        var prev_rel_dir: ?[]const u8 = null;
        for (rel_dirs.items) |cand_mem| {
            const rel_d = cand_mem.rel_dir;
            if (prev_rel_dir) |prior_rel| {
                if (std.mem.eql(u8, prior_rel, rel_d)) continue;
            }
            prev_rel_dir = rel_d;
            if (std.mem.eql(u8, rel_d, ".") or exclude_set.contains(rel_d)) continue;

            const mem_dir = try std.fmt.allocPrint(arena.asAllocator(), "{s}/{s}", .{ owned_root_dir, rel_d });
            const mem_toml = try std.fmt.allocPrint(arena.asAllocator(), "{s}/corex.toml", .{mem_dir});
            _ = try checkStrayToolConfigDotfiles(io, mem_dir, FileId.fromInt(next_fid), sink);
            const mem_bytes = std.Io.Dir.cwd().readFileAlloc(
                io,
                mem_toml,
                allocator,
                .limited(MAX_TOML_BYTES + 1),
            ) catch |mem_err| {
                if (cand_mem.is_explicit or mem_err == error.StreamTooLong) {
                    if (sink) |diag_sink| {
                        const msg = try std.fmt.allocPrint(
                            diag_sink.arena.asAllocator(),
                            "failed to load workspace member `{s}` manifest `{s}`",
                            .{ rel_d, mem_toml },
                        );
                        try emitManifestFieldErr(sink, Span.init(root_file_id, 0, 0), msg);
                    }
                }
                continue;
            };
            defer allocator.free(mem_bytes);

            var parsed_mem = try parseManifestWithInheritedPkg(
                allocator,
                &arena,
                interner,
                FileId.fromInt(next_fid),
                mem_bytes,
                cfg_env,
                ws_cfg.package,
                sink,
            );
            defer parsed_mem.doc.deinit(allocator);
            next_fid +|= 1;

            // Inherit `[workspace.security]` when member did not configure `[security]`:
            if (ws_cfg.security) |ws_sec| {
                const mem_sec = parsed_mem.manifest.security;
                const is_mem_default_sec = mem_sec.default_dep_policy == .trust_on_first_lock and
                    mem_sec.default_allow_caps == null and mem_sec.deny_caps.isEmpty() and
                    mem_sec.dev_default_allow_caps == null and mem_sec.dev_deny_caps.isEmpty() and
                    mem_sec.package_overrides.len == 0;
                if (is_mem_default_sec) {
                    parsed_mem.manifest.security = ws_sec;
                }
            }

            // Resolve `workspace = true` dependency inheritance against `ws_cfg.dependencies`:
            parsed_mem.manifest.dependencies = try resolveWorkspaceInheritedDeps(
                allocator,
                &arena,
                interner,
                parsed_mem.manifest.dependencies,
                ws_cfg.dependencies,
                sink,
            );
            parsed_mem.manifest.lint = try resolveEffectivePackageLintConfig(
                &arena,
                parsed_mem.manifest.lint,
                ws_cfg.lint,
            );
            parsed_mem.manifest.fmt = try resolveEffectivePackageFmtConfig(
                &arena,
                parsed_mem.manifest.fmt,
                ws_cfg.fmt,
            );
            parsed_mem.manifest.lsp = resolveEffectivePackageLspConfig(
                parsed_mem.manifest.lsp,
                ws_cfg.lsp,
            );
            parsed_mem.manifest.root_manifest_blake3 = computeNormalizedManifestBlake3(&parsed_mem.manifest, interner);

            const is_default = ws_cfg.default_members.len == 0 or default_member_set.contains(rel_d);
            try member_list.append(arena.asAllocator(), .{
                .rel_dir = rel_d,
                .abs_dir = mem_dir,
                .manifest_path = mem_toml,
                .manifest = parsed_mem.manifest,
                .is_default_member = is_default,
            });
        }
    }

    // Combine root + sorted member manifest digests into bundle `root_manifest_blake3`:
    var bundle_hasher = std.crypto.hash.Blake3.init(.{});
    bundle_hasher.update(&parsed_root.manifest.root_manifest_blake3);
    for (member_list.items) |mem_rec| {
        hashLenPrefixedBytes(&bundle_hasher, mem_rec.rel_dir);
        bundle_hasher.update(&mem_rec.manifest.root_manifest_blake3);
    }
    var bundle_digest: [32]u8 = undefined;
    bundle_hasher.final(&bundle_digest);

    return .{
        .arena = arena,
        .workspace_root_dir = owned_root_dir,
        .root_manifest_path = owned_root_path,
        .root_manifest = parsed_root.manifest,
        .members = member_list.items,
        .primary_member_index = if (parsed_root.manifest.package != null and member_list.items.len > 0) 0 else null,
        .is_script = false,
        .root_manifest_blake3 = if (member_list.items.len <= 1 and parsed_root.manifest.workspace == null)
            parsed_root.manifest.root_manifest_blake3
        else
            bundle_digest,
    };
}

/// Appends a complete TOML v1.0 basic string literal (`"…"`, including surrounding quotes) onto `list`,
/// escaping `\\`, `\"`, `\b`, `\t`, `\n`, `\f`, `\r`, and control bytes `< 0x20` or `0x7F` as `\u00XX`.
pub fn appendEscapedTomlBasicString(
    list: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    raw: []const u8,
) !void {
    try list.ensureUnusedCapacity(allocator, raw.len + 2);
    try list.append(allocator, '"');
    for (raw) |ch_b| {
        switch (ch_b) {
            '\\' => try list.appendSlice(allocator, "\\\\"),
            '"' => try list.appendSlice(allocator, "\\\""),
            0x08 => try list.appendSlice(allocator, "\\b"),
            '\t' => try list.appendSlice(allocator, "\\t"),
            '\n' => try list.appendSlice(allocator, "\\n"),
            0x0C => try list.appendSlice(allocator, "\\f"),
            '\r' => try list.appendSlice(allocator, "\\r"),
            else => {
                if (ch_b < 0x20 or ch_b == 0x7F) {
                    const hex_digits = "0123456789abcdef";
                    const esc_seq = [6]u8{
                        '\\',
                        'u',
                        '0',
                        '0',
                        hex_digits[(ch_b >> 4) & 0x0F],
                        hex_digits[ch_b & 0x0F],
                    };
                    try list.appendSlice(allocator, &esc_seq);
                } else {
                    try list.append(allocator, ch_b);
                }
            },
        }
    }
    try list.append(allocator, '"');
}

/// Builds a quote-preserving `TextEdit` replacing `[anchor.val_lo .. anchor.val_hi)` with `new_unquoted_val`.
pub fn buildScalarReplaceEdit(
    doc: *const TomlDocumentView,
    interner: *StringInterner,
    anchor: TomlSpanAnchor,
    new_unquoted_val: []const u8,
) !TextEdit {
    const is_single_safe = (((anchor.flags & 0x02) != 0) or
        (anchor.val_lo < doc.full_file_bytes.len and doc.full_file_bytes[anchor.val_lo] == '\'')) and
        std.mem.indexOfAny(u8, new_unquoted_val, "'\r\n") == null;
    var out_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer out_buf.deinit(interner.backing_allocator);
    if (is_single_safe) {
        try out_buf.append(interner.backing_allocator, '\'');
        try out_buf.appendSlice(interner.backing_allocator, new_unquoted_val);
        try out_buf.append(interner.backing_allocator, '\'');
    } else {
        try appendEscapedTomlBasicString(&out_buf, interner.backing_allocator, new_unquoted_val);
    }
    return .{
        .file_id = anchor.file_id,
        .start_byte = anchor.val_lo,
        .end_byte = anchor.val_hi,
        .replacement_id = try interner.intern(out_buf.items),
    };
}

/// Builds a zero-width `TextEdit` inserting `<alias> = { package = "<pkg>", version = "<ver>" }` at `anchor.row_end`.
pub fn buildInsertAliasLineEdit(
    doc: *const TomlDocumentView,
    interner: *StringInterner,
    anchor: TomlSpanAnchor,
    alias_kebab: []const u8,
    pkg_kebab: []const u8,
    ver_str: []const u8,
) !TextEdit {
    const has_crlf = anchor.row_end >= 2 and anchor.row_end <= doc.full_file_bytes.len and
        doc.full_file_bytes[anchor.row_end - 2] == '\r' and doc.full_file_bytes[anchor.row_end - 1] == '\n';
    const nl = if (has_crlf) "\r\n" else "\n";
    const target_col: usize = @max(@as(usize, anchor.eq_col), alias_kebab.len + 1);
    const pad_spaces: usize = target_col - alias_kebab.len;

    var line_list: std.ArrayListUnmanaged(u8) = .empty;
    defer line_list.deinit(interner.backing_allocator);
    try line_list.appendSlice(interner.backing_allocator, alias_kebab);
    try line_list.appendNTimes(interner.backing_allocator, ' ', @min(pad_spaces, 64));
    try line_list.appendSlice(interner.backing_allocator, "= { package = ");
    try appendEscapedTomlBasicString(&line_list, interner.backing_allocator, pkg_kebab);
    try line_list.appendSlice(interner.backing_allocator, ", version = ");
    try appendEscapedTomlBasicString(&line_list, interner.backing_allocator, ver_str);
    try line_list.appendSlice(interner.backing_allocator, " }");
    try line_list.appendSlice(interner.backing_allocator, nl);

    return .{
        .file_id = anchor.file_id,
        .start_byte = anchor.row_end,
        .end_byte = anchor.row_end,
        .replacement_id = try interner.intern(line_list.items),
    };
}

/// Builds a comment-preserving `TextEdit` appending or hoisting `<alias_kebab> = <toml_rhs>` into `[dependencies]`.
pub fn buildAutoAppendDependencyEdit(
    allocator: std.mem.Allocator,
    doc: *const TomlDocumentView,
    interner: *StringInterner,
    alias_kebab: []const u8,
    toml_rhs: []const u8,
) !TextEdit {
    const has_crlf = std.mem.indexOf(u8, doc.full_file_bytes, "\r\n") != null;
    const nl = if (has_crlf) "\r\n" else "\n";

    if (doc.deps_section_insert_byte > 0) {
        const target_col: usize = if (doc.deps_section_eq_col > alias_kebab.len)
            doc.deps_section_eq_col
        else
            alias_kebab.len + 1;
        const pad_len = @min(target_col - alias_kebab.len, 64);
        var builder: std.ArrayList(u8) = .empty;
        defer builder.deinit(allocator);
        try builder.appendSlice(allocator, alias_kebab);
        try builder.appendNTimes(allocator, ' ', pad_len);
        try builder.appendSlice(allocator, "= ");
        try builder.appendSlice(allocator, toml_rhs);
        try builder.appendSlice(allocator, nl);
        return .{
            .file_id = doc.file_id,
            .start_byte = doc.deps_section_insert_byte,
            .end_byte = doc.deps_section_insert_byte,
            .replacement_id = try interner.intern(builder.items),
        };
    }

    const insert_at: u32 = doc.base_byte_offset +| @as(u32, @intCast(doc.toml_slice.len));
    const is_needing_lead_nl = doc.toml_slice.len > 0 and doc.toml_slice[doc.toml_slice.len - 1] != '\n';
    const section_text = try std.fmt.allocPrint(
        allocator,
        "{s}{s}[dependencies]{s}{s} = {s}{s}",
        .{ if (is_needing_lead_nl) nl else "", nl, nl, alias_kebab, toml_rhs, nl },
    );
    defer allocator.free(section_text);
    return .{
        .file_id = doc.file_id,
        .start_byte = insert_at,
        .end_byte = insert_at,
        .replacement_id = try interner.intern(section_text),
    };
}

/// Applies `fixes` via `TransactionalPatcher` and verifies that the patched TOML re-parses with zero syntax errors.
pub fn applyManifestFixesTransactionally(
    allocator: std.mem.Allocator,
    doc: *const TomlDocumentView,
    fixes: []const SuggestedFix,
    interner: *const StringInterner,
) ![]u8 {
    const outcome = try TransactionalPatcher.apply(
        allocator,
        doc.full_file_bytes,
        doc.file_id,
        fixes,
        interner,
    );
    errdefer allocator.free(outcome.patched_source);
    if (outcome.skipped_conflict_count > 0) return error.ConflictingManifestEdits;

    var verify_slice = outcome.patched_source;
    var verify_off: u32 = 0;
    if (doc.is_script_frontmatter) {
        var check_arena = BumpArena.init(allocator);
        defer check_arena.deinit();
        const fm = (try extractScriptFrontmatter(&check_arena, doc.file_id, outcome.patched_source, null)) orelse {
            return error.InvalidPatchedToml;
        };
        verify_slice = @constCast(fm.toml_slice);
        verify_off = fm.fm_start_byte;
    }

    var verify_doc = try parseTomlDocument(
        allocator,
        doc.file_id,
        outcome.patched_source,
        verify_slice,
        verify_off,
        0,
        doc.is_script_frontmatter,
        .e0013_invalid_manifest_or_pkg_name,
        null,
    );
    defer verify_doc.deinit(allocator);
    if (verify_doc.has_syntax_errors) return error.InvalidPatchedToml;
    return outcome.patched_source;
}

// --------------- Canonical `corex.lock` v1 I/O ----------------

/// Compares two `LockPackage` entries by `(name_ascii ASC, SemVer.compare ASC, source_ascii ASC)`.
pub fn compareLockPackages(
    interner: *const StringInterner,
    lhs: LockPackage,
    rhs: LockPackage,
) std.math.Order {
    const name_ord = std.mem.order(u8, interner.get(lhs.name), interner.get(rhs.name));
    if (name_ord != .eq) return name_ord;
    const ver_ord = SemVer.compareTotal(lhs.version, rhs.version, interner);
    if (ver_ord != .eq) return ver_ord;
    return std.mem.order(u8, interner.get(lhs.source), interner.get(rhs.source));
}

/// Serializes `lockfile` into deterministic canonical `corex.lock` v1 text (`DR-11` §1.3).
pub fn serializeLockfile(
    allocator: std.mem.Allocator,
    lockfile: *const Lockfile,
    interner: *const StringInterner,
) ![]u8 {
    const sorted_pkgs = try allocator.dupe(LockPackage, lockfile.packages);
    defer allocator.free(sorted_pkgs);
    std.mem.sort(LockPackage, sorted_pkgs, interner, struct {
        /// Orders `LockPackage` items in canonical `corex.lock` order.
        fn lessThan(int_ptr: *const StringInterner, lhs: LockPackage, rhs: LockPackage) bool {
            return compareLockPackages(int_ptr, lhs, rhs) == .lt;
        }
    }.lessThan);

    var out: std.ArrayList(u8) = .empty;
    errdefer out.deinit(allocator);

    const root_hex = std.fmt.bytesToHex(lockfile.root_manifest_blake3, .lower);
    const hdr_line = try std.fmt.allocPrint(
        allocator,
        "# @generated by CoreX. Do not edit manually.\nversion = {d}\nroot_manifest_blake3 = \"b3:{s}\"\n",
        .{ LOCKFILE_VERSION, &root_hex },
    );
    defer allocator.free(hdr_line);
    try out.appendSlice(allocator, hdr_line);

    const appendCapArray = struct {
        /// Appends `key = ["clock", …, "unsafe_op"]\n` onto `buf`.
        fn run(
            buf: *std.ArrayList(u8),
            alloc: std.mem.Allocator,
            key_name: []const u8,
            mask: EffectCapabilityMask,
        ) !void {
            try buf.appendSlice(alloc, key_name);
            try buf.appendSlice(alloc, " = [");
            const bits = mask.asBits();
            var is_first = true;
            for (CANONICAL_LOCKFILE_CAPS) |cap_entry| {
                if ((bits & cap_entry.bit) != 0) {
                    if (!is_first) try buf.appendSlice(alloc, ", ");
                    is_first = false;
                    try appendEscapedTomlBasicString(buf, alloc, cap_entry.name);
                }
            }
            try buf.appendSlice(alloc, "]\n");
        }
    }.run;

    const appendStrIdArray = struct {
        /// Appends sorted `key = ["…"]\n` onto `buf`.
        fn run(
            buf: *std.ArrayList(u8),
            alloc: std.mem.Allocator,
            int_ptr: *const StringInterner,
            key_name: []const u8,
            items: []const StringId,
        ) !void {
            const copy = try alloc.dupe(StringId, items);
            defer alloc.free(copy);
            std.mem.sort(StringId, copy, int_ptr, struct {
                /// Orders `StringId` items by ASCII text.
                fn lessThan(inner_interner: *const StringInterner, lhs: StringId, rhs: StringId) bool {
                    return std.mem.order(u8, inner_interner.get(lhs), inner_interner.get(rhs)) == .lt;
                }
            }.lessThan);
            try buf.appendSlice(alloc, key_name);
            try buf.appendSlice(alloc, " = [");
            for (copy, 0..) |sid, i| {
                if (i > 0) try buf.appendSlice(alloc, ", ");
                try appendEscapedTomlBasicString(buf, alloc, int_ptr.get(sid));
            }
            try buf.appendSlice(alloc, "]\n");
        }
    }.run;

    var ver_scratch: std.ArrayListUnmanaged(u8) = .empty;
    defer ver_scratch.deinit(allocator);

    for (sorted_pkgs) |pkg| {
        try out.appendSlice(allocator, "\n[[package]]\nname = ");
        try appendEscapedTomlBasicString(&out, allocator, interner.get(pkg.name));
        try out.appendSlice(allocator, "\nversion = ");
        ver_scratch.clearRetainingCapacity();
        try pkg.version.appendFormatted(&ver_scratch, allocator, interner);
        try appendEscapedTomlBasicString(&out, allocator, ver_scratch.items);
        try out.appendSlice(allocator, "\nsource = ");
        try appendEscapedTomlBasicString(&out, allocator, interner.get(pkg.source));
        try out.append(allocator, '\n');

        if (pkg.checksum) |cksum| {
            const ck_hex = std.fmt.bytesToHex(cksum, .lower);
            try out.appendSlice(allocator, "checksum = \"b3:");
            try out.appendSlice(allocator, &ck_hex);
            try out.appendSlice(allocator, "\"\n");
        }

        const tree_hex = std.fmt.bytesToHex(pkg.tree_hash, .lower);
        try out.appendSlice(allocator, "tree_hash = \"b3:");
        try out.appendSlice(allocator, &tree_hex);
        try out.appendSlice(allocator, "\"\n");

        if (pkg.signature) |sig| {
            const sig_hex = std.fmt.bytesToHex(sig, .lower);
            try out.appendSlice(allocator, "signature = \"ed25519:");
            try out.appendSlice(allocator, &sig_hex);
            try out.appendSlice(allocator, "\"\n");
        }

        if (pkg.tlog_index) |tlog_idx| {
            var idx_buf: [32]u8 = undefined;
            try out.appendSlice(allocator, try std.fmt.bufPrint(&idx_buf, "tlog_index = {d}\n", .{tlog_idx}));
        }

        try appendCapArray(&out, allocator, "max_caps", pkg.max_caps);
        if (!pkg.ambient_caps.isEmpty()) {
            try appendCapArray(&out, allocator, "ambient_caps", pkg.ambient_caps);
        }

        const cxi_hex = std.fmt.bytesToHex(pkg.cxi_blake3, .lower);
        try out.appendSlice(allocator, "cxi_blake3 = \"b3:");
        try out.appendSlice(allocator, &cxi_hex);
        try out.appendSlice(allocator, "\"\n");

        if (pkg.links != .empty) {
            try out.appendSlice(allocator, "links = ");
            try appendEscapedTomlBasicString(&out, allocator, interner.get(pkg.links));
            try out.append(allocator, '\n');
        }

        try appendStrIdArray(&out, allocator, interner, "features", pkg.features);
        try appendStrIdArray(&out, allocator, interner, "dependencies", pkg.dependencies);
    }

    return out.toOwnedSlice(allocator);
}

/// Parses and validates `corex.lock` v1 (`E0014` on syntax corruption, version mismatch, or manifest drift).
pub fn parseLockfile(
    allocator: std.mem.Allocator,
    arena: *BumpArena,
    interner: *StringInterner,
    file_id: FileId,
    lock_bytes: []const u8,
    expected_manifest_blake3: ?[32]u8,
    sink: ?*DiagnosticSink,
) !?Lockfile {
    var doc = TomlDocumentView{
        .file_id = file_id,
        .full_file_bytes = lock_bytes,
        .toml_slice = lock_bytes,
    };
    defer doc.deinit(allocator);

    try lexTomlSlice(allocator, &doc, .e0014_lockfile_drift_or_corrupt, sink);
    if (doc.has_syntax_errors) return null;

    var dom_arena = BumpArena.init(allocator);
    defer dom_arena.deinit();
    var parser_inst = TomlParser{
        .allocator = allocator,
        .dom_arena = &dom_arena,
        .doc = &doc,
        .diag_code = .e0014_lockfile_drift_or_corrupt,
        .sink = sink,
    };
    const root_tbl = try parser_inst.parseDocument();
    if (doc.has_syntax_errors) return null;

    const emitLockErr = struct {
        /// Emits `E0014` at `span`.
        fn run(s_opt: ?*DiagnosticSink, err_span: Span, msg: []const u8) !void {
            if (s_opt) |ds| {
                try ds.emit(.{
                    .code = .e0014_lockfile_drift_or_corrupt,
                    .severity = .err,
                    .primary_span = err_span,
                    .message = msg,
                });
            }
        }
    }.run;

    var has_version = false;
    var root_b3: ?[32]u8 = null;
    var pkg_elems: []const TomlDomElem = &.{};

    for (root_tbl.entries.items) |kv| {
        if (std.mem.eql(u8, kv.key, "version")) {
            if (kv.val != .int_val or kv.val.int_val != LOCKFILE_VERSION) {
                try emitLockErr(sink, kv.val_span, "unsupported or corrupt `corex.lock` schema `version` (expected `1`)");
                return null;
            }
            has_version = true;
        } else if (std.mem.eql(u8, kv.key, "root_manifest_blake3")) {
            if (kv.val != .str_val) {
                try emitLockErr(sink, kv.val_span, "`root_manifest_blake3` must be a `\"b3:<64-hex>\"` digest string");
                return null;
            }
            root_b3 = parsePrefixedBlake3Hex(kv.val.str_val) orelse {
                try emitLockErr(sink, kv.val_span, "invalid `\"b3:<64-hex>\"` digest in `root_manifest_blake3`");
                return null;
            };
        } else if (std.mem.eql(u8, kv.key, "package")) {
            if (kv.val != .array_val) {
                try emitLockErr(sink, kv.val_span, "`[[package]]` must be an array of tables in `corex.lock`");
                return null;
            }
            pkg_elems = kv.val.array_val;
        } else {
            try emitLockErr(sink, kv.key_span, "unknown top-level key in `corex.lock`");
            return null;
        }
    }

    if (!has_version or root_b3 == null) {
        try emitLockErr(sink, Span.init(file_id, 0, 0), "`corex.lock` is missing required `version = 1` or `root_manifest_blake3`");
        return null;
    }
    if (expected_manifest_blake3) |exp_b3| {
        if (!std.crypto.timing_safe.eql([32]u8, root_b3.?, exp_b3)) {
            try emitLockErr(
                sink,
                Span.init(file_id, 0, 0),
                "`corex.lock` `root_manifest_blake3` is out of sync with `corex.toml` (`--locked` / `--frozen`)",
            );
            return null;
        }
    }

    var parsed_pkgs: std.ArrayList(LockPackage) = .empty;
    for (pkg_elems) |pelem| {
        if (pelem.val != .table_val) {
            try emitLockErr(sink, pelem.span, "corrupt `[[package]]` entry in `corex.lock`");
            return null;
        }
        var name_id: ?StringId = null;
        var ver_opt: ?SemVer = null;
        var src_id: ?StringId = null;
        var cksum_opt: ?[32]u8 = null;
        var tree_opt: ?[32]u8 = null;
        var sig_opt: ?[64]u8 = null;
        var tlog_opt: ?u64 = null;
        var max_caps: ?EffectCapabilityMask = null;
        var amb_caps: EffectCapabilityMask = .EMPTY;
        var cxi_opt: ?[32]u8 = null;
        var links_id: StringId = .empty;
        var feats_ids: ?[]const StringId = null;
        var deps_ids: ?[]const StringId = null;

        for (pelem.val.table_val.entries.items) |pkv| {
            const pk = pkv.key;
            if (std.mem.eql(u8, pk, "name")) {
                if (pkv.val != .str_val or !isValidPackageNameKebab(pkv.val.str_val)) {
                    try emitLockErr(sink, pkv.val_span, "invalid `kebab-case` package `name` in `corex.lock`");
                    return null;
                }
                name_id = try interner.intern(pkv.val.str_val);
            } else if (std.mem.eql(u8, pk, "version")) {
                if (pkv.val != .str_val) {
                    try emitLockErr(sink, pkv.val_span, "invalid `version` in `corex.lock`");
                    return null;
                }
                ver_opt = (try SemVer.parse(interner, pkv.val.str_val)) orelse {
                    try emitLockErr(sink, pkv.val_span, "malformed SemVer 2.0.0 `version` in `corex.lock`");
                    return null;
                };
            } else if (std.mem.eql(u8, pk, "source")) {
                if (pkv.val != .str_val or pkv.val.str_val.len == 0) {
                    try emitLockErr(sink, pkv.val_span, "missing or empty `source` in `corex.lock`");
                    return null;
                }
                src_id = try interner.intern(pkv.val.str_val);
            } else if (std.mem.eql(u8, pk, "checksum")) {
                if (pkv.val != .str_val) {
                    try emitLockErr(sink, pkv.val_span, "`checksum` must be a `\"b3:<64-hex>\"` string");
                    return null;
                }
                cksum_opt = parsePrefixedBlake3Hex(pkv.val.str_val) orelse {
                    try emitLockErr(sink, pkv.val_span, "malformed or empty `\"b3:<64-hex>\"` `checksum` in `corex.lock`");
                    return null;
                };
            } else if (std.mem.eql(u8, pk, "tree_hash")) {
                if (pkv.val != .str_val) {
                    try emitLockErr(sink, pkv.val_span, "`tree_hash` must be a `\"b3:<64-hex>\"` string");
                    return null;
                }
                tree_opt = parsePrefixedBlake3Hex(pkv.val.str_val) orelse {
                    try emitLockErr(sink, pkv.val_span, "malformed `\"b3:<64-hex>\"` `tree_hash` in `corex.lock`");
                    return null;
                };
            } else if (std.mem.eql(u8, pk, "signature")) {
                if (pkv.val != .str_val) {
                    try emitLockErr(sink, pkv.val_span, "`signature` must be an `\"ed25519:<128-hex>\"` string");
                    return null;
                }
                sig_opt = parsePrefixedEd25519Hex(pkv.val.str_val) orelse {
                    try emitLockErr(sink, pkv.val_span, "malformed or empty `\"ed25519:<128-hex>\"` `signature` in `corex.lock`");
                    return null;
                };
            } else if (std.mem.eql(u8, pk, "tlog_index")) {
                if (pkv.val == .int_val) {
                    if (pkv.val.int_val < 0) {
                        try emitLockErr(sink, pkv.val_span, "`tlog_index` in `corex.lock` must be a non-negative `u64`");
                        return null;
                    }
                    tlog_opt = @intCast(pkv.val.int_val);
                } else if (pkv.val == .uint_val) {
                    tlog_opt = pkv.val.uint_val;
                } else {
                    try emitLockErr(sink, pkv.val_span, "`tlog_index` must be an unsigned integer");
                    return null;
                }
            } else if (std.mem.eql(u8, pk, "max_caps")) {
                if (pkv.val != .array_val) {
                    try emitLockErr(sink, pkv.val_span, "`max_caps` must be an array of capability strings");
                    return null;
                }
                max_caps = (try parseCapabilityElemArray(
                    pkv.val.array_val,
                    &doc,
                    interner,
                    .e0014_lockfile_drift_or_corrupt,
                    true,
                    null,
                    sink,
                )) orelse return null;
            } else if (std.mem.eql(u8, pk, "ambient_caps")) {
                if (pkv.val != .array_val) {
                    try emitLockErr(sink, pkv.val_span, "`ambient_caps` must be an array of capability strings");
                    return null;
                }
                amb_caps = (try parseCapabilityElemArray(
                    pkv.val.array_val,
                    &doc,
                    interner,
                    .e0014_lockfile_drift_or_corrupt,
                    true,
                    null,
                    sink,
                )) orelse return null;
            } else if (std.mem.eql(u8, pk, "cxi_blake3")) {
                if (pkv.val != .str_val) {
                    try emitLockErr(sink, pkv.val_span, "`cxi_blake3` must be a `\"b3:<64-hex>\"` string");
                    return null;
                }
                cxi_opt = parsePrefixedBlake3Hex(pkv.val.str_val) orelse {
                    try emitLockErr(sink, pkv.val_span, "malformed `\"b3:<64-hex>\"` `cxi_blake3` in `corex.lock`");
                    return null;
                };
            } else if (std.mem.eql(u8, pk, "links")) {
                if (pkv.val != .str_val or pkv.val.str_val.len == 0) {
                    try emitLockErr(sink, pkv.val_span, "`links` in `corex.lock` must be a non-empty string");
                    return null;
                }
                links_id = try interner.intern(pkv.val.str_val);
            } else if (std.mem.eql(u8, pk, "features") or std.mem.eql(u8, pk, "dependencies")) {
                if (pkv.val != .array_val) {
                    try emitLockErr(sink, pkv.val_span, "expected string array in `corex.lock`");
                    return null;
                }
                var arr_ids = try arena.allocSlice(StringId, pkv.val.array_val.len);
                var prev_s: ?[]const u8 = null;
                for (pkv.val.array_val, 0..) |selem, i| {
                    if (selem.val != .str_val or selem.val.str_val.len == 0) {
                        try emitLockErr(sink, selem.span, "expected non-empty string in `corex.lock` array");
                        return null;
                    }
                    if (prev_s) |prior| {
                        if (std.mem.order(u8, prior, selem.val.str_val) != .lt) {
                            try emitLockErr(sink, selem.span, "unsorted or duplicate array entry in `corex.lock`");
                            return null;
                        }
                    }
                    prev_s = selem.val.str_val;
                    arr_ids[i] = try interner.intern(selem.val.str_val);
                }
                if (std.mem.eql(u8, pk, "features")) feats_ids = arr_ids else deps_ids = arr_ids;
            } else {
                try emitLockErr(sink, pkv.key_span, "unknown key inside `[[package]]` entry of `corex.lock`");
                return null;
            }
        }

        if (name_id == null or ver_opt == null or src_id == null or tree_opt == null or
            max_caps == null or cxi_opt == null or feats_ids == null or deps_ids == null)
        {
            try emitLockErr(
                sink,
                pelem.span,
                "`[[package]]` entry in `corex.lock` is missing required v1 schema fields",
            );
            return null;
        }

        const lock_pkg = LockPackage{
            .name = name_id.?,
            .version = ver_opt.?,
            .source = src_id.?,
            .checksum = cksum_opt,
            .tree_hash = tree_opt.?,
            .signature = sig_opt,
            .tlog_index = tlog_opt,
            .max_caps = max_caps.?,
            .ambient_caps = amb_caps,
            .cxi_blake3 = cxi_opt.?,
            .links = links_id,
            .features = feats_ids.?,
            .dependencies = deps_ids.?,
        };

        if (parsed_pkgs.items.len > 0) {
            const prev_pkg = parsed_pkgs.items[parsed_pkgs.items.len - 1];
            if (compareLockPackages(interner, prev_pkg, lock_pkg) != .lt) {
                try emitLockErr(
                    sink,
                    pelem.span,
                    "`[[package]]` entries in `corex.lock` are out of canonical `(name, version, source)` order or duplicated",
                );
                return null;
            }
        }
        try parsed_pkgs.append(arena.asAllocator(), lock_pkg);
    }

    return .{
        .version = LOCKFILE_VERSION,
        .root_manifest_blake3 = root_b3.?,
        .packages = parsed_pkgs.items,
    };
}

// ---------------------------------------- MAIN -----------------------------------------

comptime {
    std.debug.assert(@sizeOf(SemVerCore) == 12 and @alignOf(SemVerCore) == 4);
    std.debug.assert(@sizeOf(SemVer) == 20 and @alignOf(SemVer) == 4);
    std.debug.assert(@sizeOf(TomlToken) == 8 and @alignOf(TomlToken) == 4);
    std.debug.assert(@sizeOf(TomlTriviaPiece) == 8 and @alignOf(TomlTriviaPiece) == 4);
    std.debug.assert(@sizeOf(TomlCstNode) == 16 and @alignOf(TomlCstNode) == 4);
    std.debug.assert(@sizeOf(TomlSpanAnchor) == 24 and @alignOf(TomlSpanAnchor) == 4);
}

// ---------------------------------------- TESTS ----------------------------------------

test "test_pkg_manifest_dr25_tooling_schema_compiled_glob64_and_lockfile_firewall" {
    const allocator = std.testing.allocator;
    var arena = BumpArena.init(allocator);
    defer arena.deinit();
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    const cfg_env: CfgEnv = .{};

    const bare_toml =
        \\[package]
        \\name = "telemetry-gateway"
        \\version = "1.2.0"
        \\corex = "1.0"
    ;
    var parsed_bare = try parseManifest(allocator, &arena, &interner, FileId.fromInt(1), bare_toml, &cfg_env, &sink);
    defer parsed_bare.doc.deinit(allocator);

    const full_toml =
        \\[package]
        \\name = "telemetry-gateway"
        \\version = "1.2.0"
        \\corex = "1.0"
        \\
        \\[lint]
        \\inherit = true
        \\disable = ["W0501", "needless-trailing-return"]
        \\exclude = ["src/generated/**/*.cx"]
        \\
        \\[lint.settings]
        \\min-grouped-int-digits     = 6
        \\min-grouped-hex-digits     = 8
        \\trivial-copy-max-bytes     = 16
        \\require-suppression-reason = false
        \\allowed-ident-names        = ["id", "db", "io", "rx", "tx"]
        \\allowed-confusables        = ["α", "β"]
        \\
        \\[[lint.overrides]]
        \\files = ["tests/**/*.cx", "**/pb/*.cx", "src/legacy_{v1,v2}/**"]
        \\exclude_files = ["tests/security_strict/**/*.cx"]
        \\disable = ["unused-pkg-visibility", "single-char-ident"]
        \\
        \\[fmt]
        \\exclude = ["tests/fixtures/malformed/**/*.cx"]
        \\check-generated = true
        \\
        \\[lsp]
        \\inlay-hints-types           = false
        \\inlay-hints-parameter-names = "all"
        \\inlay-hints-mvs-modes       = false
        \\inlay-hints-effects         = "none"
        \\code-lens-test-bench        = false
        \\max-completion-items        = 128
    ;
    var parsed_full = try parseManifest(allocator, &arena, &interner, FileId.fromInt(2), full_toml, &cfg_env, &sink);
    defer parsed_full.doc.deinit(allocator);

    try std.testing.expectEqual(@as(usize, 0), sink.countDiagnostics());
    // Lockfile hash firewall: editing `[lint]`, `[fmt]`, or `[lsp]` must NEVER alter `root_manifest_blake3`!
    try std.testing.expectEqualSlices(
        u8,
        &parsed_bare.manifest.root_manifest_blake3,
        &parsed_full.manifest.root_manifest_blake3,
    );

    const lint_cfg = parsed_full.manifest.lint;
    try std.testing.expectEqual(@as(u8, 6), lint_cfg.settings.min_grouped_int_digits);
    try std.testing.expectEqual(@as(u8, 8), lint_cfg.settings.min_grouped_hex_digits);
    try std.testing.expectEqual(@as(?u8, 16), lint_cfg.settings.trivial_copy_max_bytes);
    try std.testing.expect(!lint_cfg.settings.require_suppression_reason);
    try std.testing.expectEqual(@as(usize, 5), lint_cfg.settings.allowed_ident_names.len);
    try std.testing.expectEqual(@as(usize, 2), lint_cfg.settings.allowed_confusables.len);
    try std.testing.expect(lint_cfg.isFileExcluded("src/generated/v1/api.cx"));
    try std.testing.expect(!lint_cfg.isFileExcluded("src/net/http.cx"));

    const mask_src = lint_cfg.resolveFileDisabledMask("src/net/http.cx", .{});
    try std.testing.expect((mask_src & RuleId.inlining_budget_exceeded.bit()) != 0);
    try std.testing.expect((mask_src & RuleId.needless_trailing_return.bit()) != 0);
    try std.testing.expect((mask_src & RuleId.single_char_ident.bit()) == 0);

    const mask_test = lint_cfg.resolveFileDisabledMask("tests/unit/auth_test.cx", .{});
    try std.testing.expect((mask_test & RuleId.single_char_ident.bit()) != 0);
    try std.testing.expect((mask_test & RuleId.unused_pkg_visibility.bit()) != 0);

    const mask_pb = lint_cfg.resolveFileDisabledMask("crates/rpc/pb/wire.cx", .{});
    try std.testing.expect((mask_pb & RuleId.single_char_ident.bit()) != 0);

    const mask_legacy = lint_cfg.resolveFileDisabledMask("src/legacy_v2/old.cx", .{});
    try std.testing.expect((mask_legacy & RuleId.single_char_ident.bit()) != 0);

    const mask_strict = lint_cfg.resolveFileDisabledMask("tests/security_strict/audit.cx", .{});
    try std.testing.expect((mask_strict & RuleId.single_char_ident.bit()) == 0);

    try std.testing.expect(parsed_full.manifest.fmt.check_generated);
    try std.testing.expect(parsed_full.manifest.fmt.isFileExcluded("tests/fixtures/malformed/bad.cx"));
    try std.testing.expect(!parsed_full.manifest.lsp.inlay_hints_types);
    try std.testing.expectEqual(LspParamHintsMode.all, parsed_full.manifest.lsp.inlay_hints_parameter_names);
    try std.testing.expect(!parsed_full.manifest.lsp.inlay_hints_mvs_modes);
    try std.testing.expectEqual(LspEffectsHintsMode.none, parsed_full.manifest.lsp.inlay_hints_effects);
    try std.testing.expect(!parsed_full.manifest.lsp.code_lens_test_bench);
    try std.testing.expectEqual(@as(u16, 128), parsed_full.manifest.lsp.max_completion_items);
}

test "test_pkg_manifest_dr25_script_frontmatter_workspace_inheritance_and_e0018_e0020" {
    const allocator = std.testing.allocator;
    var arena = BumpArena.init(allocator);
    defer arena.deinit();
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    const cfg_env: CfgEnv = .{};

    // [1] Script frontmatter supports `[lint]`, `[fmt]`, and `[lsp]`:
    {
        var script_sink = DiagnosticSink.init(allocator);
        defer script_sink.deinit();
        const script_src =
            \\---
            \\[lint]
            \\disable = ["single-char-ident"]
            \\[fmt]
            \\check-generated = true
            \\[lsp]
            \\max-completion-items = 32
            \\---
            \\pub fn main() {}
        ;
        const extracted = (try extractScriptFrontmatter(&arena, FileId.fromInt(3), script_src, &script_sink)).?;
        var parsed_script = try parseScriptFrontmatterManifest(
            allocator,
            &arena,
            &interner,
            FileId.fromInt(3),
            script_src,
            extracted,
            &cfg_env,
            &script_sink,
        );
        defer parsed_script.doc.deinit(allocator);
        try std.testing.expectEqual(@as(usize, 0), script_sink.countDiagnostics());
        try std.testing.expect((parsed_script.manifest.lint.disable_mask & RuleId.single_char_ident.bit()) != 0);
        try std.testing.expect(parsed_script.manifest.fmt.check_generated);
        try std.testing.expectEqual(@as(u16, 32), parsed_script.manifest.lsp.max_completion_items);
    }

    // [2] Workspace inheritance (`inherit = true` merges vs `inherit = false` isolates):
    {
        var ws_sink = DiagnosticSink.init(allocator);
        defer ws_sink.deinit();
        const ws_toml =
            \\[package]
            \\name = "root-pkg"
            \\version = "0.1.0"
            \\[lint]
            \\disable = ["unused-binding"]
            \\[lint.settings]
            \\min-grouped-int-digits = 7
            \\[workspace]
            \\members = []
            \\[workspace.lint]
            \\disable = ["deprecated-use"]
            \\[workspace.lint.settings]
            \\min-grouped-int-digits = 6
            \\min-grouped-hex-digits = 10
            \\[workspace.lsp]
            \\max-completion-items = 200
        ;
        var parsed_ws = try parseManifest(allocator, &arena, &interner, FileId.fromInt(4), ws_toml, &cfg_env, &ws_sink);
        defer parsed_ws.doc.deinit(allocator);
        try std.testing.expectEqual(@as(usize, 0), ws_sink.countDiagnostics());
        const eff_lint = parsed_ws.manifest.lint;
        try std.testing.expect((eff_lint.disable_mask & RuleId.unused_binding.bit()) != 0);
        try std.testing.expect((eff_lint.disable_mask & RuleId.deprecated_use.bit()) != 0);
        try std.testing.expectEqual(@as(u8, 7), eff_lint.settings.min_grouped_int_digits);
        try std.testing.expectEqual(@as(u8, 10), eff_lint.settings.min_grouped_hex_digits);
        try std.testing.expectEqual(@as(u16, 200), parsed_ws.manifest.lsp.max_completion_items);

        const isolated = try resolveEffectivePackageLintConfig(
            &arena,
            .{ .inherit = false, .disable_mask = RuleId.single_char_ident.bit() },
            parsed_ws.manifest.workspace.?.lint,
        );
        try std.testing.expectEqual(RuleId.single_char_ident.bit(), isolated.disable_mask);
    }

    // [3] E0018, E0019 (Jaro-Winkler suggestion + bad globs), and E0020 out-of-range checks:
    {
        var err_sink = DiagnosticSink.init(allocator);
        defer err_sink.deinit();
        const bad_toml =
            \\[package]
            \\name = "bad-cfg"
            \\version = "0.1.0"
            \\[lint]
            \\disable = ["unused-bindng", "correctness", "E0403"]
            \\exclude = ["../escape/*.cx", "/abs/*.cx", "{a,b"]
            \\allow = ["W0402"]
            \\[lint.settings]
            \\min-grouped-int-digits = 2
            \\trivial-copy-max-bytes = 64
            \\allowed-confusables = ["ab"]
            \\[fmt]
            \\indent-width = 2
            \\[lsp]
            \\max-completion-items = 999
            \\inlay-hints-parameter-names = "verbose"
        ;
        var parsed_bad = try parseManifest(allocator, &arena, &interner, FileId.fromInt(5), bad_toml, &cfg_env, &err_sink);
        defer parsed_bad.doc.deinit(allocator);

        var count_e0018: usize = 0;
        var count_e0019: usize = 0;
        var count_e0020: usize = 0;
        var saw_did_you_mean = false;
        for (err_sink.asSlice()) |diag_item| {
            if (diag_item.code == .e0018_forbidden_tool_config_key) count_e0018 += 1;
            if (diag_item.code == .e0019_invalid_lint_rule_or_glob) {
                count_e0019 += 1;
                for (diag_item.notes) |note_str| {
                    if (std.mem.indexOf(u8, note_str, "unused-binding") != null) saw_did_you_mean = true;
                }
            }
            if (diag_item.code == .e0020_tool_setting_out_of_range) count_e0020 += 1;
        }
        try std.testing.expectEqual(@as(usize, 2), count_e0018);
        try std.testing.expectEqual(@as(usize, 6), count_e0019);
        try std.testing.expectEqual(@as(usize, 5), count_e0020);
        try std.testing.expect(saw_did_you_mean);
    }
}
