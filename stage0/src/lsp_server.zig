//! Built-In Language Server Protocol (`LSP 3.17`) Daemon & In-Process Query Driver
//!
//! Implements the Phase 10 (`PLAN.md` §Phase 10, `DR-12` §3–§5, `DR-17` §4.4) built-in `corex lsp`
//! Language Server Protocol 3.17 server over Zig `0.17.0` `std.Io` streams, backed directly in-process
//! by `VfsSourceMap`, `CompilerDb`, `fmt_engine`, `type_system`, `symbol_resolver`, and `mir_sast`.
//!
//! Enforces strict untrusted-input resource caps (`AGENTS.md` §2), buffered `$/cancelRequest` priority
//! pre-draining and `didChange` coalescing, dual-bounded $O(1)$ `SemanticTokensCache` LRU eviction,
//! cross-platform `file://` URI normalization, and hygiene-verified cross-file `rename`.

const std = @import("std");
const builtin = @import("builtin");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const diagnostic = @import("diag/diagnostic.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const mir_sast = @import("mir_sast.zig");
const fmt_engine = @import("fmt_engine.zig");
const lint_filter = @import("lint_filter.zig");
const query_db = @import("query_db.zig");
const codegen_abi = @import("codegen_abi.zig");
const pkg_manifest = @import("pkg_manifest.zig");
const pkg_cache = @import("pkg_cache.zig");
const pkg_resolver = @import("pkg_resolver.zig");

const FileId = mem_foundation.FileId;
const StringId = mem_foundation.StringId;
const SymbolId = mem_foundation.SymbolId;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const NodeIndex = mem_foundation.NodeIndex;
const ExtraIndex = mem_foundation.ExtraIndex;
const ScopeId = mem_foundation.ScopeId;
const TypeId = mem_foundation.TypeId;
const Span = mem_foundation.Span;
const BumpArena = mem_foundation.BumpArena;
const StringInterner = mem_foundation.StringInterner;

const PackageId = vfs_sourcemap.PackageId;
const PositionEncoding = vfs_sourcemap.PositionEncoding;
const LineIndex = vfs_sourcemap.LineIndex;
const VfsSourceMap = vfs_sourcemap.VfsSourceMap;

const TokenKind = syntax_arenas.TokenKind;
const TriviaKind = syntax_arenas.TriviaKind;
const CstNodeKind = syntax_arenas.CstNodeKind;
const AstTag = syntax_arenas.AstTag;
const TokenBuffer = syntax_arenas.TokenBuffer;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstArena = syntax_arenas.AstArena;

const Severity = diagnostic.Severity;
const FixApplicability = diagnostic.FixApplicability;
const DiagnosticCode = diagnostic.DiagnosticCode;
const Diagnostic = diagnostic.Diagnostic;
const DiagnosticSink = diagnostic.DiagnosticSink;
const SuggestedFix = diagnostic.SuggestedFix;
const LabeledSpan = diagnostic.LabeledSpan;

const Namespace = symbol_resolver.Namespace;
const NamespaceMask = symbol_resolver.NamespaceMask;
const Visibility = symbol_resolver.Visibility;
const SymbolKind = symbol_resolver.SymbolKind;
const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolRecord = symbol_resolver.SymbolRecord;
const SymbolTable = symbol_resolver.SymbolTable;
const FnParamSpec = symbol_resolver.FnParamSpec;

const TypeTag = type_system.TypeTag;
const ParamMode = type_system.ParamMode;
const IncompleteDotTarget = type_system.IncompleteDotTarget;
const BodySemanticSideTables = type_system.BodySemanticSideTables;
const InternPool = type_system.InternPool;

const EffectCapabilityMask = mir_sast.EffectCapabilityMask;
const FnRegionSummary = mir_sast.FnRegionSummary;

const CompilerDb = query_db.CompilerDb;
const Durability = query_db.Durability;
const DefId = query_db.DefId;
const Fingerprint128 = query_db.Fingerprint128;

// ---------------------------------------- TYPES ----------------------------------------

// ------------------- Public Options & State -------------------

/// Configuration options controlling `corex lsp` server execution.
pub const LspServerOptions = struct {
    /// Permits direct `core.*` kernel imports and `workspace/symbol` hits in `std_core` (`--internal-core`).
    is_internal_core: bool = false,
};

/// LSP 3.17 server lifecycle state machine.
const LifecycleState = enum(u8) {
    /// Initial state prior to receiving an `initialize` request (`-32002` on other requests).
    uninitialized = 0,
    /// Active state after `initialize` succeeds.
    initialized = 1,
    /// Draining state after `shutdown` succeeds (`-32600` on non-`exit` requests; `exit` returns `0`).
    shutting_down = 2,
};

/// Client-configured `$/setTrace` verbosity level.
const TraceMode = enum(u8) {
    /// Tracing disabled (`"off"`).
    off = 0,
    /// High-level message tracing (`"messages"`).
    messages = 1,
    /// Detailed payload tracing (`"verbose"`).
    verbose = 2,
};

/// Canonical LSP 3.17 method tags dispatched in $O(1)$ via `LSP_METHOD_MAP`.
const LspMethod = enum(u8) {
    /// `initialize` handshake request.
    initialize,
    /// `initialized` post-handshake notification.
    initialized,
    /// `shutdown` graceful teardown request.
    shutdown,
    /// `exit` process termination notification.
    exit,
    /// `$/setTrace` trace level notification.
    set_trace,
    /// `$/cancelRequest` asynchronous request cancellation notification.
    cancel_request,
    /// `textDocument/didOpen` buffer open notification.
    did_open,
    /// `textDocument/didChange` incremental or full buffer edit notification.
    did_change,
    /// `textDocument/didSave` buffer save notification.
    did_save,
    /// `textDocument/didClose` buffer close notification.
    did_close,
    /// `workspace/didChangeWatchedFiles` disk file watcher notification.
    did_change_watched_files,
    /// `textDocument/diagnostic` pull diagnostics request (`LSP 3.17`).
    document_diagnostic,
    /// `textDocument/semanticTokens/full` full semantic token request.
    semantic_tokens_full,
    /// `textDocument/semanticTokens/full/delta` incremental delta semantic token request.
    semantic_tokens_delta,
    /// `textDocument/semanticTokens/range` viewport range semantic token request.
    semantic_tokens_range,
    /// `textDocument/hover` symbol signature, contracts, and doc-comment hover request.
    hover,
    /// `textDocument/definition` go-to-definition request.
    definition,
    /// `textDocument/typeDefinition` go-to-type-definition request.
    type_definition,
    /// `textDocument/references` visibility-pruned find-references request.
    references,
    /// `textDocument/documentHighlight` intra-file read/write highlight request.
    document_highlight,
    /// `textDocument/documentSymbol` hierarchical outline symbols request.
    document_symbol,
    /// `workspace/symbol` fuzzy workspace symbol search request.
    workspace_symbol,
    /// `textDocument/completion` dot, `@` attribute, and lexical completion request.
    completion,
    /// `textDocument/signatureHelp` call-site parameter and `@overload` signature help request.
    signature_help,
    /// `textDocument/inlayHint` inferred type, parameter label, and contract inlay hints request.
    inlay_hint,
    /// `textDocument/codeAction` `SuggestedFix` quickfix code actions request.
    code_action,
    /// `textDocument/codeLens` runnable `test` / `bench` CodeLens request.
    code_lens,
    /// `textDocument/formatting` lossless CST whole-document formatting request.
    formatting,
    /// `textDocument/rangeFormatting` lossless CST range formatting request.
    range_formatting,
    /// `textDocument/prepareRename` rename target validation and range request.
    prepare_rename,
    /// `textDocument/rename` hygiene-checked cross-file workspace rename request.
    rename,
};

// ---------------- JSON-RPC 2.0 & Framing Types ----------------

/// Strongly typed JSON-RPC 2.0 request/response identifier.
const JsonRpcId = union(enum) {
    /// Absent `id` field (JSON-RPC notification).
    missing: void,
    /// Explicit `null` `id` value.
    null_id: void,
    /// Signed 64-bit integer `id` value.
    int_id: i64,
    /// UTF-8 string `id` value.
    string_id: []const u8,

    /// Returns `true` when `lhs` and `rhs` identify the exact same JSON-RPC request.
    pub fn eql(lhs: JsonRpcId, rhs: JsonRpcId) bool {
        return switch (lhs) {
            .missing => rhs == .missing,
            .null_id => rhs == .null_id,
            .int_id => |lhs_int| rhs == .int_id and lhs_int == rhs.int_id,
            .string_id => |lhs_str| rhs == .string_id and std.mem.eql(u8, lhs_str, rhs.string_id),
        };
    }
};

/// Single key-value member inside an arena-allocated `JsonValue.object_val`.
const JsonObjectField = struct {
    /// Decoded UTF-8 property name.
    key: []const u8,
    /// Parsed property value.
    value: JsonValue,
};

/// Arena-allocated, strictly typed JSON DOM value produced by the non-backtracking JSON scanner.
const JsonValue = union(enum) {
    /// JSON `null`.
    null_val: void,
    /// JSON `true` or `false`.
    bool_val: bool,
    /// Exact 64-bit signed integer literal.
    int_val: i64,
    /// IEEE-754 64-bit floating-point literal.
    float_val: f64,
    /// UTF-8 validated and unescaped string slice.
    string_val: []const u8,
    /// Ordered JSON array slice.
    array_val: []const JsonValue,
    /// Ordered JSON object key-value slice.
    object_val: []const JsonObjectField,

    /// Looks up `field_name` in `self` if `self` is `.object_val`, returning the last matching value.
    pub fn getField(self: JsonValue, field_name: []const u8) ?JsonValue {
        if (self != .object_val) return null;
        var matched_val: ?JsonValue = null;
        for (self.object_val) |entry| {
            if (std.mem.eql(u8, entry.key, field_name)) {
                matched_val = entry.value;
            }
        }
        return matched_val;
    }

    /// Extracts a string field named `field_name` from an object value, or `null` when absent/non-string.
    pub fn getStringField(self: JsonValue, field_name: []const u8) ?[]const u8 {
        const val = self.getField(field_name) orelse return null;
        return if (val == .string_val) val.string_val else null;
    }

    /// Extracts an integer field named `field_name` from an object value, or `null` when absent/non-int.
    pub fn getIntField(self: JsonValue, field_name: []const u8) ?i64 {
        const val = self.getField(field_name) orelse return null;
        return if (val == .int_val) val.int_val else null;
    }

    /// Extracts a boolean field named `field_name` from an object value, or `null` when absent/non-bool.
    pub fn getBoolField(self: JsonValue, field_name: []const u8) ?bool {
        const val = self.getField(field_name) orelse return null;
        return if (val == .bool_val) val.bool_val else null;
    }
};

/// Errors raised by the bounded, non-backtracking JSON-RPC 2.0 parser.
const JsonParseError = error{
    /// Malformed JSON token, lone UTF-16 surrogate, unescaped control byte, or invalid UTF-8 (`-32700`).
    InvalidJsonSyntax,
    /// Nesting exceeded `MAX_LSP_JSON_DEPTH` (`64`, `-32700`).
    MaxDepthExceeded,
    /// Backing arena ran out of memory.
    OutOfMemory,
};

/// Parsed `Content-Length` header classification distinguishing valid lengths, integer overflow, and malformed headers.
const ParsedContentLength = union(enum) {
    /// Valid non-negative byte length fitting in `usize`.
    ok: usize,
    /// Valid ASCII decimal digits that overflowed `usize` (`> usize.max`; maps to `.content_too_large` / `-32600`).
    overflow: void,
    /// Missing, empty, non-digit, or conflicting `Content-Length` header (`-32700`).
    invalid: void,
};

/// Result of reading a single framed LSP message from `*std.Io.Reader`.
const InboundFrame = union(enum) {
    /// Valid frame whose owned `payload` bytes have length `<= MAX_LSP_CONTENT_LENGTH`.
    payload: []u8,
    /// Clean end-of-stream at a message boundary.
    eof: void,
    /// Header block exceeded `MAX_LSP_HEADER_BYTES` (`8 KiB`) or lacked a valid `Content-Length` (`-32700`).
    header_parse_error: void,
    /// Declared `Content-Length` exceeded `MAX_LSP_CONTENT_LENGTH` (`16 MiB`); `true` when stream sync is unrecoverable.
    content_too_large: bool,
};

/// Fixed 256-slot ring buffer storing pre-drained `$/cancelRequest` IDs (`MAX_CANCELED_REQUEST_IDS`).
const CanceledRequestRing = struct {
    /// Inline storage for string request IDs (`<= 120` raw bytes or 67-byte `"b3:<hex>"` BLAKE3 key).
    const Slot = struct {
        /// `true` when this ring slot holds an active unconsumed cancellation ID.
        is_active: bool = false,
        /// `true` when canceling a string ID; `false` when canceling an integer ID.
        is_string: bool = false,
        /// `true` when `str_buf` stores `"b3:" ++ hex(blake3(id_str))` for `id_str.len > 120`.
        is_hashed_string: bool = false,
        /// Integer ID payload when `!is_string`.
        int_val: i64 = 0,
        /// Byte length of `str_buf` when `is_string`.
        str_len: u8 = 0,
        /// Inline string buffer avoiding heap churn inside the cancellation ring.
        str_buf: [120]u8 = @splat(0),
    };

    /// Stack-encoded string cancellation key (raw slice `<= 120` bytes or `"b3:" ++ hex` digest).
    const EncodedStringKey = struct {
        /// Key bytes to store or compare inside `Slot.str_buf`.
        key: []const u8,
        /// `true` when `key` was hashed via `Blake3` because `id_str.len > 120`.
        is_hashed: bool,
    };

    /// Fixed-capacity circular slot array.
    slots: [MAX_CANCELED_REQUEST_IDS]Slot = @splat(.{}),
    /// Next write cursor (`0 .. MAX_CANCELED_REQUEST_IDS - 1`).
    write_cursor: usize = 0,

    /// Formats `id_str` into an inline key (`"b3:" ++ hex` via `Blake3` when `id_str.len > 120`).
    fn formatStringKey(id_str: []const u8, hash_key_buf: *[67]u8) EncodedStringKey {
        if (id_str.len <= 120) {
            return .{ .key = id_str, .is_hashed = false };
        }
        var digest: [32]u8 = undefined;
        std.crypto.hash.Blake3.hash(id_str, &digest, .{});
        const hex_digest = std.fmt.bytesToHex(digest, .lower);
        @memcpy(hash_key_buf[0..3], "b3:");
        @memcpy(hash_key_buf[3..67], &hex_digest);
        return .{ .key = hash_key_buf[0..67], .is_hashed = true };
    }

    /// Records string request ID `id_str` as canceled without heap allocation.
    pub fn recordStringId(self: *CanceledRequestRing, id_str: []const u8) void {
        var hash_key_buf: [67]u8 = undefined;
        const encoded = formatStringKey(id_str, &hash_key_buf);
        var slot = Slot{
            .is_active = true,
            .is_string = true,
            .is_hashed_string = encoded.is_hashed,
            .str_len = @intCast(encoded.key.len),
        };
        @memcpy(slot.str_buf[0..encoded.key.len], encoded.key);
        self.slots[self.write_cursor] = slot;
        self.write_cursor = (self.write_cursor + 1) % MAX_CANCELED_REQUEST_IDS;
    }

    /// Consumes and returns `true` if string request ID `id_str` was previously canceled.
    pub fn takeCanceledString(self: *CanceledRequestRing, id_str: []const u8) bool {
        var hash_key_buf: [67]u8 = undefined;
        const encoded = formatStringKey(id_str, &hash_key_buf);
        for (&self.slots) |*slot| {
            if (slot.is_active and slot.is_string and
                slot.is_hashed_string == encoded.is_hashed and
                slot.str_len == encoded.key.len and
                std.mem.eql(u8, slot.str_buf[0..slot.str_len], encoded.key))
            {
                slot.is_active = false;
                return true;
            }
        }
        return false;
    }

    /// Records `req_id` as canceled in $O(1)$ time, overwriting the oldest slot when full.
    pub fn insert(self: *CanceledRequestRing, req_id: JsonRpcId) void {
        switch (req_id) {
            .int_id => |int_val| {
                self.slots[self.write_cursor] = .{
                    .is_active = true,
                    .is_string = false,
                    .int_val = int_val,
                };
                self.write_cursor = (self.write_cursor + 1) % MAX_CANCELED_REQUEST_IDS;
            },
            .string_id => |str_val| self.recordStringId(str_val),
            .missing, .null_id => {},
        }
    }

    /// Checks whether `req_id` was canceled and consumes the matching slot if present.
    pub fn consumeIfCanceled(self: *CanceledRequestRing, req_id: JsonRpcId) bool {
        switch (req_id) {
            .int_id => |int_val| {
                for (&self.slots) |*slot| {
                    if (slot.is_active and !slot.is_string and slot.int_val == int_val) {
                        slot.is_active = false;
                        return true;
                    }
                }
            },
            .string_id => |str_val| return self.takeCanceledString(str_val),
            .missing, .null_id => {},
        }
        return false;
    }
};

// ------------- Dual-Bounded Semantic Tokens Cache -------------

/// Cached 5-integer-per-token semantic token snapshot inside `SemanticTokensCache`.
const SemanticCacheEntry = struct {
    /// Target `FileId` owning this snapshot (`.none` when slot is unoccupied).
    file_id: FileId = .none,
    /// 16-hex-character monotonic `resultId` string returned to the LSP client.
    result_id: [16]u8 = @splat('0'),
    /// Owned flat `[deltaLine, deltaStart, length, tokenType, tokenModifiers, …]` array.
    data: []u32 = &.{},
    /// Previous (more-recently-used) slot index in the intrusive doubly-linked list (`NONE_SLOT` at head).
    prev_slot: u32 = NONE_SLOT,
    /// Next (less-recently-used) slot index in the intrusive doubly-linked list (`NONE_SLOT` at tail).
    next_slot: u32 = NONE_SLOT,
    /// `true` when this slot currently holds a live cached entry.
    is_occupied: bool = false,

    /// Sentinel slot index indicating an absent neighbor or free-list end.
    const NONE_SLOT: u32 = std.math.maxInt(u32);
};

/// Dual-bounded $O(1)$ intrusive LRU cache for `textDocument/semanticTokens/full/delta` (`DR-12` §4).
pub const SemanticTokensCache = struct {
    /// Backing allocator owning `slots` and per-entry `data` slices.
    allocator: std.mem.Allocator,
    /// Maximum number of cached file entries (`<= MAX_SEMANTIC_TOKEN_CACHE_ENTRIES`).
    max_entries: usize,
    /// Maximum total byte footprint across all cached `data` arrays (`<= MAX_SEMANTIC_TOKEN_CACHE_BYTES`).
    max_bytes: usize,
    /// Pre-allocated contiguous slot pool of length `max_entries`.
    slots: []SemanticCacheEntry,
    /// $O(1)$ map from `FileId.asInt()` to occupied slot index in `slots`.
    file_to_slot: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// Most-recently-used head slot (`SemanticCacheEntry.NONE_SLOT` when empty).
    mru_head: u32 = SemanticCacheEntry.NONE_SLOT,
    /// Least-recently-used tail slot (`SemanticCacheEntry.NONE_SLOT` when empty).
    lru_tail: u32 = SemanticCacheEntry.NONE_SLOT,
    /// Stack head of unoccupied slot indices (`SemanticCacheEntry.NONE_SLOT` when full).
    free_head: u32 = SemanticCacheEntry.NONE_SLOT,
    /// Current number of live entries in the cache.
    entry_count: usize = 0,
    /// Current total byte footprint (`sum(entry.data.len * @sizeOf(u32))`).
    total_bytes: usize = 0,
    /// Monotonic sequence counter generating unique 16-hex `resultId` tokens.
    next_result_seq: u64 = 1,

    /// Initializes a `SemanticTokensCache` using canonical `MAX_SEMANTIC_TOKEN_CACHE_*` bounds.
    pub fn init(allocator: std.mem.Allocator) !SemanticTokensCache {
        return initWithLimits(
            allocator,
            MAX_SEMANTIC_TOKEN_CACHE_ENTRIES,
            MAX_SEMANTIC_TOKEN_CACHE_BYTES,
        );
    }

    /// Initializes a `SemanticTokensCache` with explicit `(max_entries, max_bytes)` caps.
    pub fn initWithLimits(
        allocator: std.mem.Allocator,
        max_entries: usize,
        max_bytes: usize,
    ) !SemanticTokensCache {
        const clamped_entries = @max(max_entries, 1);
        const slots = try allocator.alloc(SemanticCacheEntry, clamped_entries);
        var i: usize = 0;
        while (i < clamped_entries) : (i += 1) {
            slots[i] = .{
                .next_slot = if (i + 1 < clamped_entries)
                    @intCast(i + 1)
                else
                    SemanticCacheEntry.NONE_SLOT,
            };
        }
        return .{
            .allocator = allocator,
            .max_entries = max_entries,
            .max_bytes = max_bytes,
            .slots = slots,
            .free_head = if (max_entries > 0) 0 else SemanticCacheEntry.NONE_SLOT,
        };
    }

    /// Releases all cached token slices, hash map storage, and slot array.
    pub fn deinit(self: *SemanticTokensCache) void {
        for (self.slots) |*slot| {
            if (slot.is_occupied and slot.data.len > 0) {
                self.allocator.free(slot.data);
            }
        }
        self.allocator.free(self.slots);
        self.file_to_slot.deinit(self.allocator);
        self.* = undefined;
    }

    /// Allocates and formats the next 16-character lowercase hexadecimal `resultId`.
    pub fn allocNextResultId(self: *SemanticTokensCache) [16]u8 {
        const seq = self.next_result_seq;
        self.next_result_seq +%= 1;
        var out_id: [16]u8 = @splat('0');
        _ = std.fmt.bufPrint(&out_id, "{x:0>16}", .{seq}) catch unreachable;
        return out_id;
    }

    /// Looks up `(file_id, expected_result_id)` in $O(1)$ time and promotes the slot to MRU if matched.
    pub fn getMatchingResult(
        self: *SemanticTokensCache,
        file_id: FileId,
        expected_result_id: []const u8,
    ) ?[]const u32 {
        const slot_idx = self.file_to_slot.get(file_id.asInt()) orelse return null;
        const slot = &self.slots[slot_idx];
        if (!slot.is_occupied or !std.mem.eql(u8, &slot.result_id, expected_result_id)) {
            return null;
        }
        self.promoteSlotToMru(slot_idx);
        return slot.data;
    }

    /// Removes and frees any cached entry for `file_id` in $O(1)$ time.
    pub fn removeFile(self: *SemanticTokensCache, file_id: FileId) void {
        const kv = self.file_to_slot.fetchRemove(file_id.asInt()) orelse return;
        self.releaseOccupiedSlot(kv.value);
    }

    /// Inserts or replaces `file_id`'s token array, enforcing both entry-count and byte-size LRU caps.
    pub fn putCloned(
        self: *SemanticTokensCache,
        file_id: FileId,
        result_id: [16]u8,
        tokens_data: []const u32,
    ) !void {
        const entry_bytes = tokens_data.len * @sizeOf(u32);
        if (self.max_entries == 0 or entry_bytes > self.max_bytes) {
            self.removeFile(file_id);
            return;
        }

        if (self.file_to_slot.get(file_id.asInt())) |existing_slot| {
            self.removeFile(file_id);
            _ = existing_slot;
        }

        while (self.lru_tail != SemanticCacheEntry.NONE_SLOT and
            (self.entry_count >= self.max_entries or self.total_bytes + entry_bytes > self.max_bytes))
        {
            const victim_slot = self.lru_tail;
            _ = self.file_to_slot.remove(self.slots[victim_slot].file_id.asInt());
            self.releaseOccupiedSlot(victim_slot);
        }

        if (self.free_head == SemanticCacheEntry.NONE_SLOT) return;
        const cloned_data: []u32 = if (tokens_data.len > 0)
            try self.allocator.dupe(u32, tokens_data)
        else
            &.{};
        errdefer if (cloned_data.len > 0) self.allocator.free(cloned_data);

        const slot_idx = self.free_head;
        self.free_head = self.slots[slot_idx].next_slot;
        try self.file_to_slot.put(self.allocator, file_id.asInt(), slot_idx);

        self.slots[slot_idx] = .{
            .file_id = file_id,
            .result_id = result_id,
            .data = cloned_data,
            .prev_slot = SemanticCacheEntry.NONE_SLOT,
            .next_slot = self.mru_head,
            .is_occupied = true,
        };
        if (self.mru_head != SemanticCacheEntry.NONE_SLOT) {
            self.slots[self.mru_head].prev_slot = slot_idx;
        } else {
            self.lru_tail = slot_idx;
        }
        self.mru_head = slot_idx;
        self.entry_count += 1;
        self.total_bytes += entry_bytes;
    }

    /// Unlinks `slot_idx` from its current position and moves it to `mru_head` in $O(1)$ time.
    fn promoteSlotToMru(self: *SemanticTokensCache, slot_idx: u32) void {
        if (self.mru_head == slot_idx) return;
        self.unlinkSlotFromList(slot_idx);
        self.slots[slot_idx].prev_slot = SemanticCacheEntry.NONE_SLOT;
        self.slots[slot_idx].next_slot = self.mru_head;
        if (self.mru_head != SemanticCacheEntry.NONE_SLOT) {
            self.slots[self.mru_head].prev_slot = slot_idx;
        } else {
            self.lru_tail = slot_idx;
        }
        self.mru_head = slot_idx;
    }

    /// Detaches `slot_idx` from the doubly-linked MRU..LRU list in $O(1)$ time.
    fn unlinkSlotFromList(self: *SemanticTokensCache, slot_idx: u32) void {
        const prev_idx = self.slots[slot_idx].prev_slot;
        const next_idx = self.slots[slot_idx].next_slot;
        if (prev_idx != SemanticCacheEntry.NONE_SLOT) {
            self.slots[prev_idx].next_slot = next_idx;
        } else {
            self.mru_head = next_idx;
        }
        if (next_idx != SemanticCacheEntry.NONE_SLOT) {
            self.slots[next_idx].prev_slot = prev_idx;
        } else {
            self.lru_tail = prev_idx;
        }
    }

    /// Frees `slot_idx`'s buffer, updates counters, and pushes `slot_idx` onto `free_head`.
    fn releaseOccupiedSlot(self: *SemanticTokensCache, slot_idx: u32) void {
        if (!self.slots[slot_idx].is_occupied) return;
        self.unlinkSlotFromList(slot_idx);
        const freed_bytes = self.slots[slot_idx].data.len * @sizeOf(u32);
        if (self.slots[slot_idx].data.len > 0) {
            self.allocator.free(self.slots[slot_idx].data);
        }
        self.total_bytes -|= freed_bytes;
        self.entry_count -|= 1;
        self.slots[slot_idx] = .{
            .next_slot = self.free_head,
            .is_occupied = false,
        };
        self.free_head = slot_idx;
    }
};

// ---------------- LSP Wire Geometry & Records -----------------

/// Zero-based LSP 3.17 `(line, character)` position under the negotiated `PositionEncoding`.
const LspPosition = struct {
    /// Zero-based line number.
    line: u32 = 0,
    /// Zero-based UTF-8 byte or UTF-16 code-unit column offset.
    character: u32 = 0,
};

/// Half-open LSP 3.17 `[start, end)` text range.
const LspRange = struct {
    /// Inclusive range start position.
    start: LspPosition = .{},
    /// Exclusive range end position.
    end: LspPosition = .{},
};

/// Single pre-encoded semantic token span prior to 5-int delta compression.
const RawSemanticToken = struct {
    /// Zero-based line index.
    line_0: u32,
    /// Zero-based encoded column offset under `position_encoding`.
    start_char_0: u32,
    /// Encoded length in UTF-8 bytes or UTF-16 code units under `position_encoding`.
    length: u32,
    /// Index into `SEMANTIC_TOKEN_TYPES`.
    token_type: u32,
    /// Bitmask over `SEMANTIC_TOKEN_MODIFIERS`.
    modifiers: u32,
};

/// Deduplicated compiler diagnostic bundled with optional dynamically resolved `E0220` fix.
const CollectedDiagnostic = struct {
    /// Borrowed underlying compiler `Diagnostic`.
    diag: Diagnostic,
    /// Optional extra `SuggestedFix` synthesized via `CompilerDb.resolveBangFixSuggestion`.
    extra_bang_fix: ?SuggestedFix = null,
};

/// Resolved semantic entity under the editor cursor for hover, definition, references, and rename.
const CursorTarget = struct {
    /// Token index at or immediately preceding the cursor (`TokenIndex.none` when none).
    token_index: TokenIndex = .none,
    /// Effective sub-token kind when cursor resolves inside a `.fmt_string_lit` interpolation hole (`null` otherwise).
    resolved_token_kind: ?TokenKind = null,
    /// Source byte span of the focal token.
    token_span: Span = Span.ZERO,
    /// Resolved symbol handle (`SymbolIndex.none` when expression-only or built-in keyword).
    symbol_index: SymbolIndex = .none,
    /// Resolved expression or symbol `TypeId` (`TypeId.err_ty` when untyped).
    type_id: TypeId = .err_ty,
    /// Enclosing top-level `DefId` (`DefId.NONE` when at module top level).
    enclosing_def_id: DefId = .NONE,
    /// External module `FileId` when cursor rests on an external `mod child;` item.
    external_mod_file_id: FileId = .none,
};

/// Single intra-file or cross-file reference occurrence with read/write access classification.
const ReferenceHit = struct {
    /// Exact identifier byte span of the occurrence.
    span: Span,
    /// `true` when the occurrence mutates, initializes, moves (`own`), or declares the target.
    is_write_access: bool = false,
    /// Lexical `ScopeId` active at the reference site (`.none` when module-level).
    ref_scope: ScopeId = .none,
};

/// Planned surgical source byte replacement emitted by cross-file `textDocument/rename`.
const RenamePlanEdit = struct {
    /// Target file `FileId` inside `PackageId.root`.
    file_id: FileId,
    /// Inclusive start byte offset in `file_id`.
    start_byte: u32,
    /// Exclusive end byte offset in `file_id`.
    end_byte: u32,
    /// Arena-allocated replacement text (`new_name` or expanded shorthand `old: new`).
    replacement: []const u8,
};

/// Ranked workspace symbol match candidate for `workspace/symbol`.
const WorkspaceSymbolCandidate = struct {
    /// Symbol name slice.
    name: []const u8,
    /// LSP `SymbolKind` integer (`1..26`).
    lsp_kind: u8,
    /// Live declaration `Span` resolved via `CompilerDb.resolveLiveSymbolDeclSpan`.
    live_span: Span,
    /// Optional container module/type name.
    container_name: []const u8,
    /// Match quality tier (`0` = exact, `1` = icase exact, `2` = prefix, `3` = icase prefix, `4` = substring).
    rank: u8,
    /// `true` when annotated with `@deprecated`.
    is_deprecated: bool,
};

/// Ranked completion item candidate for `textDocument/completion`.
const CompletionCandidate = struct {
    /// Primary completion label inserted on acceptance.
    label: []const u8,
    /// LSP `CompletionItemKind` integer (`1..25`).
    kind: u8,
    /// Concise signature or type detail string.
    detail: []const u8 = "",
    /// Sort priority (`0` = field/local, `1` = inherent method/variant, `2` = module/fn, `3` = keyword).
    sort_tier: u8 = 2,
    /// `true` when target symbol carries `@deprecated`.
    is_deprecated: bool = false,
};

/// Hierarchical outline node emitted by `textDocument/documentSymbol`.
const DocumentSymbolItem = struct {
    /// Symbol display name.
    name: []const u8,
    /// Optional signature or type detail.
    detail: []const u8 = "",
    /// LSP `SymbolKind` integer (`1..26`).
    kind: u8,
    /// `true` if annotated with `@deprecated`.
    is_deprecated: bool = false,
    /// Full enclosing declaration byte span.
    full_span: Span,
    /// Identifier token selection byte span (clamped inside `full_span`).
    selection_span: Span,
    /// Nested child symbols (fields, variants, trait/impl methods, inline module items).
    children: []const DocumentSymbolItem = &.{},
};

/// Grouped `TextEdit` list for a single target URI inside a `CodeAction` `WorkspaceEdit.changes` map.
const CodeActionUriGroup = struct {
    /// Target document `FileId`.
    file_id: FileId,
    /// Resolved outbound document URI key.
    uri: []const u8,
    /// Ordered `TextEdit` items targeting `uri`.
    edits: std.ArrayListUnmanaged(diagnostic.TextEdit) = .empty,
};

/// Canonical signature and prose summary rendered on `textDocument/hover` for built-in `@` items.
const HoverDocSpec = struct {
    /// Signature header rendered inside a fenced ` ```corex ` code block.
    signature: []const u8,
    /// Concise human-readable explanation rendered below the signature separator.
    summary: []const u8,
};

/// Stateful CoreX LSP 3.17 session owning `CompilerDb`, `VfsSourceMap`, and bounded caches.
pub const LspSession = struct {
    /// Long-lived allocator for persistent session structures.
    allocator: std.mem.Allocator,
    /// Zig `0.17.0` `std.Io` capability handle for VFS and workspace manifest reads.
    io: std.Io,
    /// Optional process environment map for `COREX_HOME` resolution.
    environ_map: ?*const std.process.Environ.Map,
    /// Startup server configuration (`is_internal_core`).
    options: LspServerOptions,
    /// Demand-driven Stage 0 compiler query database.
    db: CompilerDb,
    /// Virtual filesystem and editor overlay source map bound to `db.interner`.
    vfs: VfsSourceMap,
    /// Per-turn scratch arena reset after every JSON-RPC dispatch.
    turn_arena: BumpArena,
    /// Reusable allocating writer buffer for assembling outbound JSON-RPC frames.
    outbound_buf: std.Io.Writer.Allocating,
    /// Dual-bounded $O(1)$ LRU cache for semantic token delta snapshots.
    semantic_tokens_cache: SemanticTokensCache,
    /// 256-slot priority pre-drain ring buffer for `$/cancelRequest` IDs.
    canceled_ring: CanceledRequestRing = .{},
    /// Current protocol lifecycle state.
    state: LifecycleState = .uninitialized,
    /// Negotiated column encoding (`utf-8` preferred when client supports it, else `utf-16`).
    position_encoding: PositionEncoding = .utf16,
    /// `true` when client advertised `capabilities.textDocument.diagnostic` pull support.
    is_pull_diagnostics_enabled: bool = false,
    /// Current `$/setTrace` mode.
    trace_mode: TraceMode = .off,
    /// Owned normalized workspace root directory path (`null` when single-file/untitled).
    workspace_root_dir: ?[]u8 = null,
    /// Owned normalized `corex.toml` path if discovered during `initialize`.
    manifest_path: ?[]u8 = null,
    /// Effective `[lsp]` configuration resolved from `corex.toml` (`DR-25` §3.1 & Ruling 2.2).
    lsp_config: pkg_manifest.LspConfig = .{},
    /// Last valid normalized dependency/build BLAKE3 digest of `corex.toml` for zero-teardown reload.
    last_manifest_blake3: [32]u8 = @splat(0),
    /// `true` once `last_manifest_blake3` has been recorded from a workspace manifest mount.
    has_manifest_blake3: bool = false,
    /// Cached workspace manifest directory path last probed by `checkStrayToolConfigDotfiles`.
    cached_stray_dotfile_dir: ?[]u8 = null,
    /// Cached result of `checkStrayToolConfigDotfiles` (`false` avoids 16 NTFS stats on live reload).
    cached_has_stray_dotfiles: bool = false,
    /// Ordered list of workspace/dependency `FileId`s mounted into `db`.
    mounted_files: std.ArrayListUnmanaged(FileId) = .empty,
    /// $O(1)$ membership set of `FileId.asInt()` values already present in `mounted_files`.
    mounted_file_set: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Latest client `version` integer for currently open editor overlays (`FileId.asInt() -> version`).
    open_doc_versions: std.AutoHashMapUnmanaged(u32, i64) = .empty,
    /// Exact client `didOpen` URI strings keyed by `FileId.asInt()` for lossless URI echoing.
    file_id_to_client_uri: std.AutoHashMapUnmanaged(u32, []u8) = .empty,
    /// Aggregate byte footprint of owned URI strings stored in `file_id_to_client_uri`.
    client_uri_total_bytes: usize = 0,
    /// Open `FileId`s awaiting deferred push diagnostics once interactive requests in the batch finish.
    pending_push_diag_files: std.ArrayListUnmanaged(FileId) = .empty,
    /// Optional diagnostic/trace writer (`stderr` or test log sink; never `stdout`).
    log_writer: ?*std.Io.Writer = null,

    /// Initializes a fresh `LspSession` with lazy compiler and VFS state.
    pub fn init(
        allocator: std.mem.Allocator,
        io: std.Io,
        environ_map: ?*const std.process.Environ.Map,
        log_writer: ?*std.Io.Writer,
        options: LspServerOptions,
    ) !LspSession {
        var db = try CompilerDb.init(allocator);
        errdefer db.deinit();
        if (options.is_internal_core) {
            try db.setInternalCore(true);
        }
        db.setIncludeTests(true);
        db.setEmbedIo(io);
        db.setTargetSpec(codegen_abi.TargetSpec.host());

        var sem_cache = try SemanticTokensCache.init(allocator);
        errdefer sem_cache.deinit();

        var vfs = VfsSourceMap.init(allocator, &db.interner);
        vfs.allow_mutable_mmap = (@import("builtin").os.tag != .windows);

        return .{
            .allocator = allocator,
            .io = io,
            .environ_map = environ_map,
            .options = options,
            .vfs = vfs,
            .db = db,
            .turn_arena = BumpArena.init(allocator),
            .outbound_buf = std.Io.Writer.Allocating.init(allocator),
            .semantic_tokens_cache = sem_cache,
            .log_writer = log_writer,
        };
    }

    /// Binds internal self-referential pointers (`db.vfs_source_map`) once `LspSession` is pinned on stack.
    pub fn bindInternalPointers(self: *LspSession) void {
        self.vfs.interner = &self.db.interner;
        self.db.setVfsSourceMap(&self.vfs);
    }

    /// Releases all owned arenas, maps, strings, VFS buffers, and `CompilerDb` artifacts.
    pub fn deinit(self: *LspSession) void {
        var uri_iter = self.file_id_to_client_uri.valueIterator();
        while (uri_iter.next()) |uri_ptr| {
            self.allocator.free(uri_ptr.*);
        }
        self.file_id_to_client_uri.deinit(self.allocator);
        self.client_uri_total_bytes = 0;
        self.pending_push_diag_files.deinit(self.allocator);
        self.open_doc_versions.deinit(self.allocator);
        self.mounted_file_set.deinit(self.allocator);
        self.mounted_files.deinit(self.allocator);
        if (self.workspace_root_dir) |ws_dir| self.allocator.free(ws_dir);
        if (self.manifest_path) |m_path| self.allocator.free(m_path);
        if (self.cached_stray_dotfile_dir) |dot_dir| self.allocator.free(dot_dir);
        self.semantic_tokens_cache.deinit();
        self.outbound_buf.deinit();
        self.turn_arena.deinit();
        self.vfs.deinit(self.io);
        self.db.deinit();
        self.* = undefined;
    }

    /// Returns `true` when `file_id` is currently open in an editor tab (`didOpen` without `didClose`).
    pub inline fn isFileOpen(self: *const LspSession, file_id: FileId) bool {
        if (file_id.isNone()) return false;
        return self.open_doc_versions.contains(file_id.asInt());
    }

    /// Registers `file_id` in `mounted_files` in $O(1)$ if not yet tracked.
    pub fn recordMountedFile(self: *LspSession, file_id: FileId) !void {
        if (file_id.isNone()) return;
        const gop = try self.mounted_file_set.getOrPut(self.allocator, file_id.asInt());
        if (!gop.found_existing) {
            try self.mounted_files.append(self.allocator, file_id);
        }
    }

    /// Evicts one closed (`!isFileOpen`) entry from `file_id_to_client_uri`, returning `true` if one was freed.
    fn evictOneClosedClientUri(self: *LspSession) bool {
        var victim_key: ?u32 = null;
        var key_iter = self.file_id_to_client_uri.keyIterator();
        while (key_iter.next()) |key_ptr| {
            if (!self.open_doc_versions.contains(key_ptr.*)) {
                victim_key = key_ptr.*;
                break;
            }
        }
        if (victim_key) |fid_raw| {
            if (self.file_id_to_client_uri.fetchRemove(fid_raw)) |removed_kv| {
                self.client_uri_total_bytes -|= removed_kv.value.len;
                self.allocator.free(removed_kv.value);
                return true;
            }
        }
        return false;
    }

    /// Removes and frees any cached client URI string for `file_id`, decrementing `client_uri_total_bytes`.
    pub fn removeClientUri(self: *LspSession, file_id: FileId) void {
        if (file_id.isNone()) return;
        if (self.file_id_to_client_uri.fetchRemove(file_id.asInt())) |removed_kv| {
            self.client_uri_total_bytes -|= removed_kv.value.len;
            self.allocator.free(removed_kv.value);
        }
    }

    /// Records or updates the client's exact URI spelling for `file_id` within `MAX_CLIENT_URI_MAP_*` bounds.
    pub fn recordClientUri(self: *LspSession, file_id: FileId, raw_uri: []const u8) !void {
        if (file_id.isNone() or raw_uri.len == 0 or raw_uri.len > MAX_LSP_URI_BYTES) return;
        if (self.file_id_to_client_uri.getPtr(file_id.asInt())) |existing_ptr| {
            if (std.mem.eql(u8, existing_ptr.*, raw_uri)) return;
            while ((self.client_uri_total_bytes -| existing_ptr.*.len) + raw_uri.len > MAX_CLIENT_URI_MAP_BYTES) {
                if (!self.evictOneClosedClientUri()) {
                    self.removeClientUri(file_id);
                    return;
                }
            }
            const refreshed_ptr = self.file_id_to_client_uri.getPtr(file_id.asInt()) orelse return;
            const duped_uri = try self.allocator.dupe(u8, raw_uri);
            self.client_uri_total_bytes = (self.client_uri_total_bytes -| refreshed_ptr.*.len) + duped_uri.len;
            self.allocator.free(refreshed_ptr.*);
            refreshed_ptr.* = duped_uri;
            return;
        }
        while (self.file_id_to_client_uri.count() >= MAX_CLIENT_URI_MAP_ENTRIES or
            self.client_uri_total_bytes + raw_uri.len > MAX_CLIENT_URI_MAP_BYTES)
        {
            if (!self.evictOneClosedClientUri()) return;
        }
        const duped_uri = try self.allocator.dupe(u8, raw_uri);
        errdefer self.allocator.free(duped_uri);
        try self.file_id_to_client_uri.put(self.allocator, file_id.asInt(), duped_uri);
        self.client_uri_total_bytes += duped_uri.len;
    }

    /// Runs the framed JSON-RPC event loop on `self` until EOF or `exit` notification.
    pub fn feedStream(self: *LspSession, reader: *std.Io.Reader, writer: *std.Io.Writer) !u8 {
        var explicit_exit_code: ?u8 = null;
        while (try drainAndDispatchInboundTurn(self, reader, writer, &explicit_exit_code)) {}
        writer.flush() catch {};
        if (self.log_writer) |lw| lw.flush() catch {};
        if (explicit_exit_code) |code_val| return code_val;
        return 0;
    }
};

/// Capability bit-to-label descriptor for `DR-17` §4.4 hover rendering.
const CapabilityDisplayEntry = struct {
    /// Capability bitmask flag from `symbol_resolver.CapabilityBits`.
    bit: u16,
    /// Canonical lowercase display label rendered in hover bullets.
    label: []const u8,
};

/// Cursor probe coordinate and request ID for LSP unit tests.
const TestCursorSpec = struct {
    /// JSON-RPC request identifier.
    req_id: u32,
    /// Zero-based LSP line number.
    line: u32,
    /// Zero-based LSP character column.
    col: u32,
};

// --------------------------------------- CONSTS ----------------------------------------

// --------------- Untrusted-Input Resource Caps ----------------

/// Maximum byte length of an HTTP-style LSP frame header block (`8 KiB`, `AGENTS.md` §2).
pub const MAX_LSP_HEADER_BYTES: usize = 8 * 1024;
/// Maximum byte length of a single JSON-RPC 2.0 frame body (`16 MiB`, `AGENTS.md` §2).
pub const MAX_LSP_CONTENT_LENGTH: usize = 16 * 1024 * 1024;
/// Maximum JSON object/array nesting depth accepted by the non-backtracking parser (`64`).
pub const MAX_LSP_JSON_DEPTH: usize = 64;
/// Maximum byte length of a single document or workspace `file://` URI (`4 KiB`, `AGENTS.md` §2).
pub const MAX_LSP_URI_BYTES: usize = 4096;
/// Maximum number of client URI entries retained in `LspSession.file_id_to_client_uri` (`512`).
pub const MAX_CLIENT_URI_MAP_ENTRIES: usize = 512;
/// Maximum aggregate byte footprint retained in `LspSession.file_id_to_client_uri` (`1 MiB`).
pub const MAX_CLIENT_URI_MAP_BYTES: usize = 1024 * 1024;
/// Maximum number of file snapshots retained in `SemanticTokensCache` (`64`).
pub const MAX_SEMANTIC_TOKEN_CACHE_ENTRIES: usize = 64;
/// Maximum cumulative byte footprint retained in `SemanticTokensCache` (`8 MiB`).
pub const MAX_SEMANTIC_TOKEN_CACHE_BYTES: usize = 8 * 1024 * 1024;
/// Maximum number of `CompletionItem`s returned by `textDocument/completion` (`256`).
pub const MAX_COMPLETION_ITEMS: usize = 256;
/// Maximum number of `SymbolInformation` items returned by `workspace/symbol` (`256`).
pub const MAX_WORKSPACE_SYMBOLS: usize = 256;
/// Maximum number of `Location`s returned by `textDocument/references` (`1024`).
pub const MAX_REFERENCES: usize = 1024;
/// Maximum number of `InlayHint`s returned by `textDocument/inlayHint` (`1024`).
pub const MAX_INLAY_HINTS: usize = 1024;
/// Maximum number of `CodeAction`s returned by `textDocument/codeAction` (`64`).
pub const MAX_CODE_ACTIONS: usize = 64;
/// Capacity of the `$/cancelRequest` ID ring buffer (`256`).
pub const MAX_CANCELED_REQUEST_IDS: usize = 256;
/// Maximum number of buffered inbound frames pre-drained per turn (`64`).
pub const MAX_BATCHED_INBOUND_FRAMES: usize = 64;

/// Maximum recursive `mod <child>;` discovery depth when mounting workspace modules (`64`).
const MAX_MODULE_DISCOVERY_DEPTH: u32 = 64;
/// Maximum parent directory hops walked upward when searching for `corex.toml` (`32`).
const MAX_MANIFEST_ANCESTOR_HOPS: usize = 32;

// ----------------- JSON-RPC & LSP Error Codes -----------------

/// JSON-RPC 2.0 parse error code (`-32700`).
const JSONRPC_PARSE_ERROR: i32 = -32700;
/// JSON-RPC 2.0 invalid request error code (`-32600`).
const JSONRPC_INVALID_REQUEST: i32 = -32600;
/// JSON-RPC 2.0 unknown method error code (`-32601`).
const JSONRPC_METHOD_NOT_FOUND: i32 = -32601;
/// JSON-RPC 2.0 invalid method parameters error code (`-32602`).
const JSONRPC_INVALID_PARAMS: i32 = -32602;
/// JSON-RPC 2.0 internal server error code (`-32603`).
const JSONRPC_INTERNAL_ERROR: i32 = -32603;
/// LSP 3.17 request received prior to `initialize` (`-32002`).
const LSP_SERVER_NOT_INITIALIZED: i32 = -32002;
/// LSP 3.17 semantic or hygiene failure (`-32803`).
const LSP_REQUEST_FAILED: i32 = -32803;
/// LSP 3.17 server-initiated cancellation (`-32802`).
const LSP_SERVER_CANCELED: i32 = -32802;
/// LSP 3.17 client-initiated `$/cancelRequest` cancellation (`-32800`).
const LSP_REQUEST_CANCELED: i32 = -32800;

// ----------- Semantic Token Legend & Modifier Bits ------------

/// Canonical LSP 3.17 semantic token types advertised during `initialize`.
const SEMANTIC_TOKEN_TYPES = [_][]const u8{
    "namespace",
    "type",
    "struct",
    "enum",
    "interface",
    "typeParameter",
    "parameter",
    "variable",
    "property",
    "enumMember",
    "function",
    "method",
    "macro",
    "keyword",
    "modifier",
    "comment",
    "string",
    "number",
    "operator",
    "decorator",
};

/// Canonical CoreX MVS, ownership, and effect semantic token modifiers (`DR-12` §4).
const SEMANTIC_TOKEN_MODIFIERS = [_][]const u8{
    "declaration",
    "definition",
    "readonly",
    "static",
    "deprecated",
    "abstract",
    "async",
    "modification",
    "documentation",
    "defaultLibrary",
    "mutable",
    "consumedMove",
    "unsafe",
    "attribute",
    "linearResource",
};

/// Semantic token type index for `namespace` (`0`).
const SEM_TOK_NAMESPACE: u32 = 0;
/// Semantic token type index for `type` (`1`).
const SEM_TOK_TYPE: u32 = 1;
/// Semantic token type index for `struct` (`2`).
const SEM_TOK_STRUCT: u32 = 2;
/// Semantic token type index for `enum` (`3`).
const SEM_TOK_ENUM: u32 = 3;
/// Semantic token type index for `interface` (`4`).
const SEM_TOK_INTERFACE: u32 = 4;
/// Semantic token type index for `typeParameter` (`5`).
const SEM_TOK_TYPE_PARAM: u32 = 5;
/// Semantic token type index for `parameter` (`6`).
const SEM_TOK_PARAMETER: u32 = 6;
/// Semantic token type index for `variable` (`7`).
const SEM_TOK_VARIABLE: u32 = 7;
/// Semantic token type index for `property` (`8`).
const SEM_TOK_PROPERTY: u32 = 8;
/// Semantic token type index for `enumMember` (`9`).
const SEM_TOK_ENUM_MEMBER: u32 = 9;
/// Semantic token type index for `function` (`10`).
const SEM_TOK_FUNCTION: u32 = 10;
/// Semantic token type index for `method` (`11`).
const SEM_TOK_METHOD: u32 = 11;
/// Semantic token type index for `macro` (`12`).
const SEM_TOK_MACRO: u32 = 12;
/// Semantic token type index for `keyword` (`13`).
const SEM_TOK_KEYWORD: u32 = 13;
/// Semantic token type index for `modifier` (`14`).
const SEM_TOK_MODIFIER: u32 = 14;
/// Semantic token type index for `comment` (`15`).
const SEM_TOK_COMMENT: u32 = 15;
/// Semantic token type index for `string` (`16`).
const SEM_TOK_STRING: u32 = 16;
/// Semantic token type index for `number` (`17`).
const SEM_TOK_NUMBER: u32 = 17;
/// Semantic token type index for `operator` (`18`).
const SEM_TOK_OPERATOR: u32 = 18;
/// Semantic token type index for `decorator` (`19`).
const SEM_TOK_DECORATOR: u32 = 19;

/// Semantic token modifier bit for `declaration` (`bit 0`).
const SEM_MOD_DECLARATION: u32 = 1 << 0;
/// Semantic token modifier bit for `definition` (`bit 1`).
const SEM_MOD_DEFINITION: u32 = 1 << 1;
/// Semantic token modifier bit for `readonly` (`bit 2`).
const SEM_MOD_READONLY: u32 = 1 << 2;
/// Semantic token modifier bit for `static` (`bit 3`).
const SEM_MOD_STATIC: u32 = 1 << 3;
/// Semantic token modifier bit for `deprecated` (`bit 4`).
const SEM_MOD_DEPRECATED: u32 = 1 << 4;
/// Semantic token modifier bit for `async` (`bit 6`).
const SEM_MOD_ASYNC: u32 = 1 << 6;
/// Semantic token modifier bit for `modification` (`bit 7`).
const SEM_MOD_MODIFICATION: u32 = 1 << 7;
/// Semantic token modifier bit for `documentation` (`bit 8`).
const SEM_MOD_DOCUMENTATION: u32 = 1 << 8;
/// Semantic token modifier bit for `defaultLibrary` (`bit 9`).
const SEM_MOD_DEFAULT_LIB: u32 = 1 << 9;
/// Semantic token modifier bit for `mutable` (`bit 10`).
const SEM_MOD_MUTABLE: u32 = 1 << 10;
/// Semantic token modifier bit for `consumedMove` (`bit 11`).
const SEM_MOD_CONSUMED_MOVE: u32 = 1 << 11;
/// Semantic token modifier bit for `unsafe` (`bit 12`).
const SEM_MOD_UNSAFE: u32 = 1 << 12;
/// Semantic token modifier bit for `attribute` (`bit 13`).
const SEM_MOD_ATTRIBUTE: u32 = 1 << 13;
/// Semantic token modifier bit for `linearResource` (`bit 14`).
const SEM_MOD_LINEAR: u32 = 1 << 14;

// ----------------- Static O(1) Lookup Tables ------------------

/// $O(1)$ method dispatch table mapping JSON-RPC method names to `LspMethod` tags.
const LSP_METHOD_MAP = std.StaticStringMap(LspMethod).initComptime(.{
    .{ "$/cancelRequest", .cancel_request },
    .{ "$/setTrace", .set_trace },
    .{ "exit", .exit },
    .{ "initialize", .initialize },
    .{ "initialized", .initialized },
    .{ "shutdown", .shutdown },
    .{ "textDocument/codeAction", .code_action },
    .{ "textDocument/codeLens", .code_lens },
    .{ "textDocument/completion", .completion },
    .{ "textDocument/definition", .definition },
    .{ "textDocument/diagnostic", .document_diagnostic },
    .{ "textDocument/didChange", .did_change },
    .{ "textDocument/didClose", .did_close },
    .{ "textDocument/didOpen", .did_open },
    .{ "textDocument/didSave", .did_save },
    .{ "textDocument/documentHighlight", .document_highlight },
    .{ "textDocument/documentSymbol", .document_symbol },
    .{ "textDocument/formatting", .formatting },
    .{ "textDocument/hover", .hover },
    .{ "textDocument/inlayHint", .inlay_hint },
    .{ "textDocument/prepareRename", .prepare_rename },
    .{ "textDocument/rangeFormatting", .range_formatting },
    .{ "textDocument/references", .references },
    .{ "textDocument/rename", .rename },
    .{ "textDocument/semanticTokens/full", .semantic_tokens_full },
    .{ "textDocument/semanticTokens/full/delta", .semantic_tokens_delta },
    .{ "textDocument/semanticTokens/range", .semantic_tokens_range },
    .{ "textDocument/signatureHelp", .signature_help },
    .{ "textDocument/typeDefinition", .type_definition },
    .{ "workspace/didChangeWatchedFiles", .did_change_watched_files },
    .{ "workspace/symbol", .workspace_symbol },
});

/// $O(1)$ set of hub module basenames whose `mod child;` files reside directly in `parent_dir`.
const HUB_MODULE_BASENAME_SET = std.StaticStringMap(void).initComptime(.{
    .{ "lib.cx", {} },
    .{ "main.cx", {} },
    .{ "mod.cx", {} },
    .{ "root.cx", {} },
});

/// $O(1)$ set of built-in root module namespace identifiers highlighted as `defaultLibrary` namespaces.
const BUILTIN_ROOT_NAMESPACE_SET = std.StaticStringMap(void).initComptime(.{
    .{ "core", {} },
    .{ "cx", {} },
    .{ "pkg", {} },
});

/// $O(1)$ set of reserved root/receiver identifiers rejected by `prepareRename` and `rename`.
const NON_RENAMABLE_IDENT_SET = std.StaticStringMap(void).initComptime(.{
    .{ "Self", {} },
    .{ "_", {} },
    .{ "core", {} },
    .{ "cx", {} },
    .{ "main", {} },
    .{ "pkg", {} },
    .{ "self", {} },
});

/// $O(1)$ set of built-in prelude `Option[T]` and `Result[T, E]` variant identifiers.
const BUILTIN_VARIANT_SET = std.StaticStringMap(void).initComptime(.{
    .{ "Err", {} },
    .{ "None", {} },
    .{ "Ok", {} },
    .{ "Some", {} },
});

/// $O(1)$ set of retired standalone layout/linkage `@attribute` names excluded from `@` completions (`ADR-24C`).
const RETIRED_BUILTIN_ATTR_SET = std.StaticStringMap(void).initComptime(.{
    .{ "align", {} },
    .{ "cache_aligned", {} },
    .{ "link_name", {} },
    .{ "link_section", {} },
    .{ "packed", {} },
    .{ "repr_c", {} },
    .{ "zero_pad", {} },
});

/// $O(1)$ hover documentation catalog for built-in `@attribute` keys in `type_system.BUILTIN_ATTRIBUTE_MAP`.
const BUILTIN_ATTR_HOVER_MAP = std.StaticStringMap(HoverDocSpec).initComptime(.{
    .{
        "align",
        HoverDocSpec{
            .signature = "@repr(align: bytes)",
            .summary = "Retired standalone `@align(N)`; migrate to `@repr(align: N)` (`E0239`, `ADR-24C`).",
        },
    },
    .{
        "allow",
        HoverDocSpec{
            .signature = "@allow(rule, …, reason: \"…\")",
            .summary = "Unverified lint suppression; prefer `@expect(rule, …, reason: \"…\")` so resolved lints trigger `W0002`.",
        },
    },
    .{
        "attribute_schema",
        HoverDocSpec{
            .signature = "@attribute_schema(targets: […])",
            .summary = "Declares a strongly typed compile-time attribute schema struct validated on annotated items.",
        },
    },
    .{
        "bench",
        HoverDocSpec{
            .signature = "@bench(…)",
            .summary = "Configures statistical microbenchmark execution parameters on a `bench` item.",
        },
    },
    .{
        "borrowed",
        HoverDocSpec{
            .signature = "@borrowed",
            .summary = "FFI parameter contract declaring that the callee borrows the pointer without retaining or freeing it.",
        },
    },
    .{
        "builder",
        HoverDocSpec{
            .signature = "@builder",
            .summary = "Marks a function or type constructor as accepting trailing declarative child-item blocks.",
        },
    },
    .{
        "builder_item",
        HoverDocSpec{
            .signature = "@builder_item",
            .summary = "Marks a function or constructor as an implicit child element inside an enclosing `@builder` block.",
        },
    },
    .{
        "byte_len",
        HoverDocSpec{
            .signature = "@byte_len(param_or_expr)",
            .summary = "FFI spatial contract binding a raw buffer pointer's accessible byte length to a companion parameter (`E0307`, `E0312`).",
        },
    },
    .{
        "cache_aligned",
        HoverDocSpec{
            .signature = "@repr(align: .CacheLine)",
            .summary = "Retired standalone `@cache_aligned`; migrate to `@repr(align: .CacheLine)` (`E0239`, `ADR-24C`).",
        },
    },
    .{
        "cfg",
        HoverDocSpec{
            .signature = "@cfg(predicate)",
            .summary = "Conditionally includes the annotated declaration when `predicate` evaluates to `true` at compile time.",
        },
    },
    .{
        "cold",
        HoverDocSpec{
            .signature = "@cold",
            .summary = "Hints to the optimizer and branch predictor that this function is rarely executed (e.g., error or slow paths).",
        },
    },
    .{
        "constructor",
        HoverDocSpec{
            .signature = "@constructor",
            .summary = "Permits a `PascalCase` factory function name that constructs a value or declarative `cx.ui` component.",
        },
    },
    .{
        "consumes",
        HoverDocSpec{
            .signature = "@consumes",
            .summary = "FFI parameter contract declaring that ownership of an `@owned_by_caller` pointer transfers into the callee (`E0310`).",
        },
    },
    .{
        "deprecated",
        HoverDocSpec{
            .signature = "@deprecated(since: str, reason: str, upgrade: str = …)",
            .summary = "Marks an item as deprecated, surfacing warnings and automated `corex upgrade` rewrite metadata.",
        },
    },
    .{
        "derive",
        HoverDocSpec{
            .signature = "@derive(Trait1, Trait2, …)",
            .summary = "Synthesizes compile-time trait impls (`Copy`, `Clone`, `Equatable`, `Comparable`, `Hash`, `Debug`, `Default`, `From`).",
        },
    },
    .{
        "escapes",
        HoverDocSpec{
            .signature = "@escapes",
            .summary = "FFI parameter contract declaring that the callee stores the pointer beyond the call's return (`E0306` provenance check).",
        },
    },
    .{
        "expect",
        HoverDocSpec{
            .signature = "@expect(rule, …, reason: \"…\")",
            .summary = "Verified scoped lint suppression (`DR-25`): silences listed rules and emits `W0002` once resolved.",
        },
    },
    .{
        "export",
        HoverDocSpec{
            .signature = "@export",
            .summary = "Exports a function or static symbol in the compiled object/shared-library symbol table with external linkage.",
        },
    },
    .{
        "extern",
        HoverDocSpec{
            .signature = "@extern",
            .summary = "Declares external FFI linkage on a declaration or ABI boundary item.",
        },
    },
    .{
        "fix_inline",
        HoverDocSpec{
            .signature = "@fix_inline",
            .summary = "Provides an inline template used by `corex upgrade` / `corex fix` to migrate deprecated call sites automatically.",
        },
    },
    .{
        "free_with",
        HoverDocSpec{
            .signature = "@free_with(fn_name)",
            .summary = "FFI return contract pairing an `@owned_by_caller` pointer with its mandatory deallocation function (`E0310`).",
        },
    },
    .{
        "from",
        HoverDocSpec{
            .signature = "@from",
            .summary = "Synthesizes an automatic `FromError` error-conversion branch on an `enum` error variant for `?` propagation.",
        },
    },
    .{
        "gpu_kernel",
        HoverDocSpec{
            .signature = "@gpu_kernel",
            .summary = "Marks a device compute kernel entry point, enforcing `@no_alloc` / `@no_panic` device safety contracts (`DR-24`).",
        },
    },
    .{
        "ifunc",
        HoverDocSpec{
            .signature = "@ifunc(resolver_fn)",
            .summary = "Binds a symbol to a runtime CPU-feature dispatch resolver on targets supporting indirect functions.",
        },
    },
    .{
        "inline",
        HoverDocSpec{
            .signature = "@inline | @inline(always | never)",
            .summary = "Configures `.cxi` inlining (`@inline`), forced hot-path inlining (`@inline(always)`), or `@inline(never)`.",
        },
    },
    .{
        "linear",
        HoverDocSpec{
            .signature = "@linear",
            .summary = "Marks a resource type as must-consume (`Tier 3`): values cannot be implicitly dropped or leaked on any path (`E0304`).",
        },
    },
    .{
        "link",
        HoverDocSpec{
            .signature = "@link(name: \"symbol\", section: \".section\")",
            .summary = "Overrides the linker symbol name and/or object-file section for a function or static item (`ADR-24C`).",
        },
    },
    .{
        "link_lib",
        HoverDocSpec{
            .signature = "@link_lib(\"name\")",
            .summary = "Instructs the built-in linker driver to link against native system or static library `name`.",
        },
    },
    .{
        "link_name",
        HoverDocSpec{
            .signature = "@link(name: \"symbol\")",
            .summary = "Retired standalone `@link_name(\"…\")`; migrate to `@link(name: \"…\")` (`E0239`, `ADR-24C`).",
        },
    },
    .{
        "link_section",
        HoverDocSpec{
            .signature = "@link(section: \".section\")",
            .summary = "Retired standalone `@link_section(\"…\")`; migrate to `@link(section: \"…\")` (`E0239`, `ADR-24C`).",
        },
    },
    .{
        "local",
        HoverDocSpec{
            .signature = "@local",
            .summary = "Restricts a parameter or closure to stack-scoped non-escaping execution without heap capture.",
        },
    },
    .{
        "max_stack",
        HoverDocSpec{
            .signature = "@max_stack(bytes: usize)",
            .summary = "Compile-time call-graph stack budget contract rejecting transitive stack usage above `bytes` or recursion (`E0321`).",
        },
    },
    .{
        "may_be_null",
        HoverDocSpec{
            .signature = "@may_be_null",
            .summary = "FFI pointer contract requiring an explicit null check before dereferencing (`E0311`).",
        },
    },
    .{
        "must_use",
        HoverDocSpec{
            .signature = "@must_use",
            .summary = "Emits a diagnostic (`E0413`) whenever a call's return value (or returned type) is ignored without `_ = expr;`.",
        },
    },
    .{
        "must_vectorize",
        HoverDocSpec{
            .signature = "@must_vectorize",
            .summary = "Asserts that the annotated loop vectorizes cleanly without scalarizing dependencies.",
        },
    },
    .{
        "no_alloc",
        HoverDocSpec{
            .signature = "@no_alloc",
            .summary = "Compile-time effect contract verifying zero transitive heap allocations across the call graph (`E0320`).",
        },
    },
    .{
        "no_block",
        HoverDocSpec{
            .signature = "@no_block",
            .summary = "Compile-time effect contract forbidding blocking syscalls or thread locks inside async/real-time paths (`E0322`).",
        },
    },
    .{
        "no_panic",
        HoverDocSpec{
            .signature = "@no_panic",
            .summary = "Compile-time effect contract verifying that no panic, trap, or unchecked bounds/overflow failure is reachable (`E0320`).",
        },
    },
    .{
        "noinline",
        HoverDocSpec{
            .signature = "@noinline",
            .summary = "Prevents the MIR and backend optimizers from inlining calls to this function.",
        },
    },
    .{
        "non_null",
        HoverDocSpec{
            .signature = "@non_null",
            .summary = "FFI pointer contract asserting that the pointer is guaranteed non-null across the ABI boundary (`E0311`).",
        },
    },
    .{
        "not_send",
        HoverDocSpec{
            .signature = "@not_send",
            .summary = "Opts a type out of cross-thread ownership transfer (`Send`), rejecting cross-worker `TaskGroup.spawn` captures (`E0309`).",
        },
    },
    .{
        "not_sync",
        HoverDocSpec{
            .signature = "@not_sync",
            .summary = "Opts a type out of concurrent shared-reference access (`Sync`) across threads (`E0309`).",
        },
    },
    .{
        "null_terminated",
        HoverDocSpec{
            .signature = "@null_terminated",
            .summary = "FFI pointer contract requiring a verified trailing NUL (`0`) byte on C string pointers (`E0308`).",
        },
    },
    .{
        "out_param",
        HoverDocSpec{
            .signature = "@out_param",
            .summary = "FFI parameter contract marking a raw mutable pointer as write-only output initialized by the callee.",
        },
    },
    .{
        "overload",
        HoverDocSpec{
            .signature = "@overload",
            .summary = "Enables explicit static arity/type-disjoint function overloading within an explicit overload set.",
        },
    },
    .{
        "owned_by_caller",
        HoverDocSpec{
            .signature = "@owned_by_caller",
            .summary = "FFI return contract requiring the caller to release the returned pointer via its `@free_with` disposer (`E0310`).",
        },
    },
    .{
        "packed",
        HoverDocSpec{
            .signature = "@repr(packed: 1 | 2 | 4 | 8 | 16)",
            .summary = "Retired standalone `@packed`; migrate to `@repr(packed: true)` or `@repr(packed: k)` (`E0239`, `ADR-24C`).",
        },
    },
    .{
        "repr",
        HoverDocSpec{
            .signature = "@repr(C | transparent, packed: 1 | 2 | 4 | 8 | 16, align: N | .CacheLine, zero_pad: true)",
            .summary = "Specifies deterministic memory, alignment, packing, and ABI layout of a `struct`, `enum`, or `union` (`ADR-24C`).",
        },
    },
    .{
        "repr_c",
        HoverDocSpec{
            .signature = "@repr(C)",
            .summary = "Retired standalone `@repr_c`; migrate to `@repr(C)` (`E0239`, `ADR-24C`).",
        },
    },
    .{
        "secret",
        HoverDocSpec{
            .signature = "@secret",
            .summary = "Marks cryptographic key/secret data for constant-time handling, zeroization on drop, and redacted debug output.",
        },
    },
    .{
        "simd",
        HoverDocSpec{
            .signature = "@simd",
            .summary = "Marks a fixed-lane vector type as mapping directly to hardware SIMD registers.",
        },
    },
    .{
        "slice_len",
        HoverDocSpec{
            .signature = "@slice_len(param_or_expr)",
            .summary = "FFI spatial contract binding a raw element pointer's valid count to a companion length parameter (`E0307`, `E0312`).",
        },
    },
    .{
        "soa",
        HoverDocSpec{
            .signature = "@soa",
            .summary = "Enables Structure-of-Arrays (`#soa [T]`) multi-array column layout transformation for cache-dense SIMD iteration.",
        },
    },
    .{
        "std_cap_boundary",
        HoverDocSpec{
            .signature = "@std_cap_boundary(clears: […])",
            .summary = "Internal `core`/`stdlib` capability boundary discharging audited low-level `unsafe_op` / `ffi` effects.",
        },
    },
    .{
        "test",
        HoverDocSpec{
            .signature = "@test(…)",
            .summary = "Configures deterministic simulation (`--sim`), timeout, or property-testing options on a `test` item.",
        },
    },
    .{
        "thread_local",
        HoverDocSpec{
            .signature = "@thread_local",
            .summary = "Places a static variable in thread-local storage (TLS) and forbids cross-thread pointer escape (`E0309`).",
        },
    },
    .{
        "trusted",
        HoverDocSpec{
            .signature = "@trusted",
            .summary = "Audited FFI safety contract asserting that an external function upholds its declared pointer/spatial invariants.",
        },
    },
    .{
        "vectorize_width",
        HoverDocSpec{
            .signature = "@vectorize_width(lanes: usize)",
            .summary = "Specifies the target SIMD lane width for loop auto-vectorization.",
        },
    },
    .{
        "wasm_export",
        HoverDocSpec{
            .signature = "@wasm_export(\"name\")",
            .summary = "Exports a function in a WebAssembly module's export table under `name`.",
        },
    },
    .{
        "wasm_import",
        HoverDocSpec{
            .signature = "@wasm_import(module: \"env\", name: \"fn\")",
            .summary = "Imports an `extern` function from a WebAssembly host module and symbol name.",
        },
    },
    .{
        "zero_pad",
        HoverDocSpec{
            .signature = "@repr(zero_pad: true)",
            .summary = "Retired standalone `@zero_pad`; migrate to `@repr(zero_pad: true)` (`E0239`, `ADR-24C`).",
        },
    },
});

/// $O(1)$ hover documentation catalog for built-in primitive types and Constrained Type Groups.
const BUILTIN_PRIM_HOVER_MAP = std.StaticStringMap(HoverDocSpec).initComptime(.{
    .{
        "Float",
        HoverDocSpec{
            .signature = "type_group Float = f32 | f64",
            .summary = "Bind-Once Constrained Type Group matching IEEE-754 floating-point scalars (`f32`, `f64`).",
        },
    },
    .{
        "Integer",
        HoverDocSpec{
            .signature = "type_group Integer = SignedInt | UnsignedInt",
            .summary = "Bind-Once Constrained Type Group matching all signed and unsigned integer scalars.",
        },
    },
    .{
        "Number",
        HoverDocSpec{
            .signature = "type_group Number = Integer | Float",
            .summary = "Bind-Once Constrained Type Group matching all numeric scalar primitives.",
        },
    },
    .{
        "SignedInt",
        HoverDocSpec{
            .signature = "type_group SignedInt = i8 | i16 | i32 | i64 | i128 | isize",
            .summary = "Bind-Once Constrained Type Group matching two's-complement signed integers.",
        },
    },
    .{
        "UnsignedInt",
        HoverDocSpec{
            .signature = "type_group UnsignedInt = u8 | u16 | u32 | u64 | u128 | usize",
            .summary = "Bind-Once Constrained Type Group matching unsigned integer scalars.",
        },
    },
    .{
        "bool",
        HoverDocSpec{
            .signature = "bool",
            .summary = "1-byte boolean scalar (`false` = `0`, `true` = `1`) with niche-optimized `bool?` layout (`1` byte).",
        },
    },
    .{
        "char",
        HoverDocSpec{
            .signature = "char",
            .summary = "4-byte Unicode scalar value (`U+0000..=U+D7FF` or `U+E000..=U+10FFFF`), excluding surrogates.",
        },
    },
    .{
        "f32",
        HoverDocSpec{
            .signature = "f32",
            .summary = "32-bit IEEE-754 binary32 floating-point scalar (`4` bytes).",
        },
    },
    .{
        "f64",
        HoverDocSpec{
            .signature = "f64",
            .summary = "64-bit IEEE-754 binary64 floating-point scalar (`8` bytes).",
        },
    },
    .{
        "i128",
        HoverDocSpec{
            .signature = "i128",
            .summary = "128-bit two's-complement signed integer (`16` bytes).",
        },
    },
    .{
        "i16",
        HoverDocSpec{
            .signature = "i16",
            .summary = "16-bit two's-complement signed integer (`2` bytes, range `-32_768..=32_767`).",
        },
    },
    .{
        "i32",
        HoverDocSpec{
            .signature = "i32",
            .summary = "32-bit two's-complement signed integer (`4` bytes, range `-2_147_483_648..=2_147_483_647`).",
        },
    },
    .{
        "i64",
        HoverDocSpec{
            .signature = "i64",
            .summary = "64-bit two's-complement signed integer (`8` bytes).",
        },
    },
    .{
        "i8",
        HoverDocSpec{
            .signature = "i8",
            .summary = "8-bit two's-complement signed integer (`1` byte, range `-128..=127`).",
        },
    },
    .{
        "isize",
        HoverDocSpec{
            .signature = "isize",
            .summary = "Pointer-sized two's-complement signed integer (`8` bytes on 64-bit targets, `4` bytes on `wasm32`).",
        },
    },
    .{
        "never",
        HoverDocSpec{
            .signature = "never",
            .summary = "Uninhabited bottom type (`0` bytes) returned by diverging expressions (`return`, `break`, `panic`).",
        },
    },
    .{
        "opaque",
        HoverDocSpec{
            .signature = "opaque",
            .summary = "Unsized type-erased pointee (`*opaque` / `*mut opaque`) replacing C `void*`; never instantiated by value.",
        },
    },
    .{
        "str",
        HoverDocSpec{
            .signature = "str",
            .summary = "Immutable borrowed UTF-8 string slice (`Copy`, `{ ptr: *u8, len: usize }`, `16` bytes on 64-bit targets).",
        },
    },
    .{
        "u128",
        HoverDocSpec{
            .signature = "u128",
            .summary = "128-bit unsigned integer (`16` bytes).",
        },
    },
    .{
        "u16",
        HoverDocSpec{
            .signature = "u16",
            .summary = "16-bit unsigned integer (`2` bytes, range `0..=65_535`).",
        },
    },
    .{
        "u32",
        HoverDocSpec{
            .signature = "u32",
            .summary = "32-bit unsigned integer (`4` bytes, range `0..=4_294_967_295`).",
        },
    },
    .{
        "u64",
        HoverDocSpec{
            .signature = "u64",
            .summary = "64-bit unsigned integer (`8` bytes, range `0..=18_446_744_073_709_551_615`).",
        },
    },
    .{
        "u8",
        HoverDocSpec{
            .signature = "u8",
            .summary = "8-bit unsigned byte scalar (`1` byte, range `0..=255`).",
        },
    },
    .{
        "unit",
        HoverDocSpec{
            .signature = "unit",
            .summary = "Zero-sized unit type (`0` bytes) of statements and functions without an explicit `-> ReturnType`.",
        },
    },
    .{
        "usize",
        HoverDocSpec{
            .signature = "usize",
            .summary = "Pointer-sized unsigned integer (`8` bytes on 64-bit, `4` bytes on `wasm32`) for lengths and indices.",
        },
    },
});

/// $O(1)$ hover documentation catalog for all 71 canonical compiler `@intrinsic` operations.
const INTRINSIC_HOVER_MAP = std.StaticStringMap(HoverDocSpec).initComptime(.{
    .{
        "align_of",
        HoverDocSpec{
            .signature = "@align_of[T]() -> usize",
            .summary = "Returns the compile-time minimum byte alignment of type `T`.",
        },
    },
    .{
        "as_bytes",
        HoverDocSpec{
            .signature = "@as_bytes[T](val: &T) -> &[u8]",
            .summary = "Reinterprets an immutable `IntoBytes`-safe value reference as a zero-copy read-only byte slice.",
        },
    },
    .{
        "atomic_cmpxchg",
        HoverDocSpec{
            .signature = "@atomic_cmpxchg[T](ptr: *mut T, expected: T, desired: T, ok_ord: u8, fail_ord: u8) -> (T, bool)",
            .summary = "Atomically compares `ptr.*` with `expected`, stores `desired` if equal, and returns `(prev, swapped)`. Requires `unsafe`.",
        },
    },
    .{
        "atomic_fence",
        HoverDocSpec{
            .signature = "@atomic_fence(order: u8)",
            .summary = "Emits a hardware/compiler memory ordering fence (`Acquire = 1`, `Release = 2`, `AcqRel = 3`, `SeqCst = 4`).",
        },
    },
    .{
        "atomic_load",
        HoverDocSpec{
            .signature = "@atomic_load[T](ptr: *T, order: u8) -> T",
            .summary = "Atomically loads and returns the value at `ptr` using memory ordering `order`. Requires `unsafe`.",
        },
    },
    .{
        "atomic_rmw_add",
        HoverDocSpec{
            .signature = "@atomic_rmw_add[T](ptr: *mut T, delta: T, order: u8) -> T",
            .summary = "Atomically adds `delta` to `ptr.*` (wrapping) and returns the previous value. Requires `unsafe`.",
        },
    },
    .{
        "atomic_rmw_sub",
        HoverDocSpec{
            .signature = "@atomic_rmw_sub[T](ptr: *mut T, delta: T, order: u8) -> T",
            .summary = "Atomically subtracts `delta` from `ptr.*` (wrapping) and returns the previous value. Requires `unsafe`.",
        },
    },
    .{
        "atomic_rmw_xchg",
        HoverDocSpec{
            .signature = "@atomic_rmw_xchg[T](ptr: *mut T, new_val: T, order: u8) -> T",
            .summary = "Atomically replaces `ptr.*` with `new_val` and returns the previous value. Requires `unsafe`.",
        },
    },
    .{
        "atomic_store",
        HoverDocSpec{
            .signature = "@atomic_store[T](ptr: *mut T, val: T, order: u8)",
            .summary = "Atomically stores `val` into `ptr` using memory ordering `order`. Requires `unsafe`.",
        },
    },
    .{
        "bit_cast",
        HoverDocSpec{
            .signature = "@bit_cast[Dst, Src](val: Src) -> Dst",
            .summary = "Reinterprets the bit pattern of `val` as `Dst`; statically verifies `@size_of[Src]() == @size_of[Dst]()` and bit validity.",
        },
    },
    .{
        "c_import",
        HoverDocSpec{
            .signature = "@c_import(\"header.h\", …)",
            .summary = "Parses and translates C11/C23 declarations from `header.h` in-process without `libclang`, caching bindings in `CompilerDb`.",
        },
    },
    .{
        "caller_location",
        HoverDocSpec{
            .signature = "@caller_location() -> SourceLoc",
            .summary = "Captures the caller's compile-time file, line, and column `SourceLoc` at the call site.",
        },
    },
    .{
        "compile_assert",
        HoverDocSpec{
            .signature = "@compile_assert(cond: bool, msg: str = …)",
            .summary = "Evaluates `cond` at compile time and emits a compilation error if `false`.",
        },
    },
    .{
        "compile_error",
        HoverDocSpec{
            .signature = "@compile_error(msg: str) -> never",
            .summary = "Unconditionally aborts compilation with diagnostic message `msg` when reached during semantic/comptime evaluation.",
        },
    },
    .{
        "ctx_next_rng_seed",
        HoverDocSpec{
            .signature = "@ctx_next_rng_seed() -> u64",
            .summary = "Deterministically advances `context.rng_seed` in place via WyRand and returns the next 64-bit seed.",
        },
    },
    .{
        "default_init",
        HoverDocSpec{
            .signature = "@default_init[T]() -> T",
            .summary = "Constructs the canonical zero/default representation of scalar, pointer, or default-initializable type `T`.",
        },
    },
    .{
        "drop_in_place",
        HoverDocSpec{
            .signature = "@drop_in_place[T](ptr: *mut T)",
            .summary = "Runs the destructor glue of `T` in place at `ptr` without deallocating backing storage. Requires `unsafe`.",
        },
    },
    .{
        "drop_trace",
        HoverDocSpec{
            .signature = "@drop_trace(tag: i64)",
            .summary = "Records deterministic drop-elaboration trace marker `tag` in `MirVm` and backend verification harnesses.",
        },
    },
    .{
        "embed_bytes",
        HoverDocSpec{
            .signature = "@embed_bytes(\"relative/path\") -> &[u8]",
            .summary = "Embeds a workspace-sandboxed file directly into `.rodata` at compile time as an immutable byte slice.",
        },
    },
    .{
        "field",
        HoverDocSpec{
            .signature = "@field(target, comptime field_name: str)",
            .summary = "Accesses or projects struct field `field_name` statically at compile time during reflection/serialization.",
        },
    },
    .{
        "field_attr_lookup",
        HoverDocSpec{
            .signature = "@field_attr_lookup[T, Attr](comptime field_name: str) -> Attr?",
            .summary = "Queries compile-time `@attribute_schema` metadata `Attr` attached to field `field_name` of `T`.",
        },
    },
    .{
        "fmt_write",
        HoverDocSpec{
            .signature = "@fmt_write(out: &mut FmtWriter, args: FmtArgs) -> unit!FmtError",
            .summary = "Streams formatted `FmtArgs` pieces and typed arguments directly into `FmtWriter` with zero heap allocation.",
        },
    },
    .{
        "forget",
        HoverDocSpec{
            .signature = "@forget[T](val: own T)",
            .summary = "Takes ownership of `val` without running its destructor (`AutoDrop`).",
        },
    },
    .{
        "from_be_bytes",
        HoverDocSpec{
            .signature = "@from_be_bytes[T](bytes: [u8; @size_of[T]()]) -> T",
            .summary = "Decodes scalar `T` from big-endian byte array `bytes`.",
        },
    },
    .{
        "from_bytes",
        HoverDocSpec{
            .signature = "@from_bytes[T](bytes: &[u8]) -> T",
            .summary = "Reads a `FromBytes`-verified value `T` from `bytes` with compile-time/checked size validation.",
        },
    },
    .{
        "from_le_bytes",
        HoverDocSpec{
            .signature = "@from_le_bytes[T](bytes: [u8; @size_of[T]()]) -> T",
            .summary = "Decodes scalar `T` from little-endian byte array `bytes`.",
        },
    },
    .{
        "has_field",
        HoverDocSpec{
            .signature = "@has_field[T](comptime field_name: str) -> bool",
            .summary = "Returns `true` at compile time if nominal type `T` declares a field named `field_name`.",
        },
    },
    .{
        "implements",
        HoverDocSpec{
            .signature = "@implements[T, Trait]() -> bool",
            .summary = "Returns `true` at compile time if type `T` satisfies trait or Constrained Type Group `Trait`.",
        },
    },
    .{
        "memcpy",
        HoverDocSpec{
            .signature = "@memcpy(dst: *mut u8, src: *u8, byte_len: usize)",
            .summary = "Copies `byte_len` non-overlapping bytes from `src` to `dst`. Requires `unsafe`.",
        },
    },
    .{
        "memmove",
        HoverDocSpec{
            .signature = "@memmove(dst: *mut u8, src: *u8, byte_len: usize)",
            .summary = "Copies `byte_len` potentially overlapping bytes from `src` to `dst`. Requires `unsafe`.",
        },
    },
    .{
        "memset",
        HoverDocSpec{
            .signature = "@memset(dst: *mut u8, byte_val: u8, byte_len: usize)",
            .summary = "Fills `byte_len` bytes starting at `dst` with `byte_val`. Requires `unsafe`.",
        },
    },
    .{
        "panic",
        HoverDocSpec{
            .signature = "@panic(msg: str) -> never",
            .summary = "Triggers an immediate unrecoverable panic abort/unwind with message `msg`.",
        },
    },
    .{
        "poll_reload",
        HoverDocSpec{
            .signature = "@poll_reload() -> bool",
            .summary = "Polls the development hot-reload coordinator for updated module artifacts.",
        },
    },
    .{
        "ptr_copy",
        HoverDocSpec{
            .signature = "@ptr_copy[T](src: *T, dst: *mut T, count: usize)",
            .summary = "Copies `count` potentially overlapping elements of `T` from `src` to `dst`. Requires `unsafe`.",
        },
    },
    .{
        "ptr_copy_nonoverlapping",
        HoverDocSpec{
            .signature = "@ptr_copy_nonoverlapping[T](src: *T, dst: *mut T, count: usize)",
            .summary = "Copies `count` non-overlapping elements of `T` from `src` to `dst`. Requires `unsafe`.",
        },
    },
    .{
        "ptr_read",
        HoverDocSpec{
            .signature = "@ptr_read[T](ptr: *T) -> T",
            .summary = "Bitwise-reads a value of `T` from `ptr` without moving out of safe references. Requires `unsafe`.",
        },
    },
    .{
        "ptr_write",
        HoverDocSpec{
            .signature = "@ptr_write[T](ptr: *mut T, val: own T)",
            .summary = "Bitwise-writes `val` into uninitialized memory at `ptr` without dropping old contents. Requires `unsafe`.",
        },
    },
    .{
        "simd_add",
        HoverDocSpec{
            .signature = "@simd_add[T, const N: usize](lhs: Simd[T, N], rhs: Simd[T, N]) -> Simd[T, N]",
            .summary = "Performs lane-wise hardware SIMD addition across `N` lanes of `T`.",
        },
    },
    .{
        "simd_and",
        HoverDocSpec{
            .signature = "@simd_and(lhs: [u8; 16], rhs: [u8; 16]) -> [u8; 16]",
            .summary = "Performs 128-bit lane-wise bitwise AND across 16 byte lanes.",
        },
    },
    .{
        "simd_bitmask",
        HoverDocSpec{
            .signature = "@simd_bitmask(vec: [u8; 16]) -> u16",
            .summary = "Extracts the most-significant bit of each of the 16 byte lanes into a 16-bit mask.",
        },
    },
    .{
        "simd_eq",
        HoverDocSpec{
            .signature = "@simd_eq(lhs: [u8; 16], rhs: [u8; 16]) -> [u8; 16]",
            .summary = "Compares 16 byte lanes for equality (`0xFF` where equal, `0x00` otherwise).",
        },
    },
    .{
        "simd_gt_s8",
        HoverDocSpec{
            .signature = "@simd_gt_s8(lhs: [u8; 16], rhs: [u8; 16]) -> [u8; 16]",
            .summary = "Compares 16 signed `i8` lanes for `>` (`0xFF` where greater, `0x00` otherwise).",
        },
    },
    .{
        "simd_load_unaligned",
        HoverDocSpec{
            .signature = "@simd_load_unaligned[Vec](ptr: *u8) -> Vec",
            .summary = "Loads an unaligned SIMD vector `Vec` from `ptr`. Requires `unsafe`.",
        },
    },
    .{
        "simd_lt_s8",
        HoverDocSpec{
            .signature = "@simd_lt_s8(lhs: [u8; 16], rhs: [u8; 16]) -> [u8; 16]",
            .summary = "Compares 16 signed `i8` lanes for `<` (`0xFF` where less, `0x00` otherwise).",
        },
    },
    .{
        "simd_mul",
        HoverDocSpec{
            .signature = "@simd_mul[T, const N: usize](lhs: Simd[T, N], rhs: Simd[T, N]) -> Simd[T, N]",
            .summary = "Performs lane-wise hardware SIMD multiplication across `N` lanes of `T`.",
        },
    },
    .{
        "simd_or",
        HoverDocSpec{
            .signature = "@simd_or(lhs: [u8; 16], rhs: [u8; 16]) -> [u8; 16]",
            .summary = "Performs 128-bit lane-wise bitwise OR across 16 byte lanes.",
        },
    },
    .{
        "simd_reduce_add",
        HoverDocSpec{
            .signature = "@simd_reduce_add[T, const N: usize](vec: Simd[T, N]) -> T",
            .summary = "Horizontally sums all `N` lanes of `vec` into a single scalar `T`.",
        },
    },
    .{
        "simd_shl_u8",
        HoverDocSpec{
            .signature = "@simd_shl_u8(vec: [u8; 16], shift: u32) -> [u8; 16]",
            .summary = "Shifts each of the 16 unsigned byte lanes left by `shift` bits.",
        },
    },
    .{
        "simd_shr_u8",
        HoverDocSpec{
            .signature = "@simd_shr_u8(vec: [u8; 16], shift: u32) -> [u8; 16]",
            .summary = "Shifts each of the 16 unsigned byte lanes logically right by `shift` bits.",
        },
    },
    .{
        "simd_splat",
        HoverDocSpec{
            .signature = "@simd_splat[T, const N: usize](scalar: T) -> Simd[T, N]",
            .summary = "Broadcasts `scalar` across all `N` lanes of a `Simd[T, N]` vector.",
        },
    },
    .{
        "simd_sub",
        HoverDocSpec{
            .signature = "@simd_sub[T, const N: usize](lhs: Simd[T, N], rhs: Simd[T, N]) -> Simd[T, N]",
            .summary = "Performs lane-wise hardware SIMD subtraction across `N` lanes of `T`.",
        },
    },
    .{
        "simd_swizzle",
        HoverDocSpec{
            .signature = "@simd_swizzle(table: [u8; 16], indices: [u8; 16]) -> [u8; 16]",
            .summary = "Byte-wise table lookup (`pshufb` / `tbl` / `i8x16.swizzle`), yielding `0` when index `>= 16`.",
        },
    },
    .{
        "simd_xor",
        HoverDocSpec{
            .signature = "@simd_xor(lhs: [u8; 16], rhs: [u8; 16]) -> [u8; 16]",
            .summary = "Performs 128-bit lane-wise bitwise XOR across 16 byte lanes.",
        },
    },
    .{
        "size_of",
        HoverDocSpec{
            .signature = "@size_of[T]() -> usize",
            .summary = "Returns the compile-time stride size in bytes of type `T`.",
        },
    },
    .{
        "slice_from_raw_parts",
        HoverDocSpec{
            .signature = "@slice_from_raw_parts[T](ptr: *T, len: usize) -> &[T]",
            .summary = "Constructs an immutable slice view over `len` initialized elements at `ptr`. Requires `unsafe`.",
        },
    },
    .{
        "slice_from_raw_parts_mut",
        HoverDocSpec{
            .signature = "@slice_from_raw_parts_mut[T](ptr: *mut T, len: usize) -> &mut [T]",
            .summary = "Constructs an exclusive mutable slice view over `len` initialized elements at `ptr`. Requires `unsafe`.",
        },
    },
    .{
        "sqrt",
        HoverDocSpec{
            .signature = "@sqrt(val: Float) -> Float",
            .summary = "Computes the IEEE-754 hardware square root of `f32` or `f64` value `val`.",
        },
    },
    .{
        "str_from_utf8_unchecked",
        HoverDocSpec{
            .signature = "@str_from_utf8_unchecked(bytes: &[u8]) -> str",
            .summary = "Reinterprets pre-validated UTF-8 `bytes` as `str` in O(1) time. Requires `unsafe`.",
        },
    },
    .{
        "sys_exit",
        HoverDocSpec{
            .signature = "@sys_exit(code: i32) -> never",
            .summary = "Terminates the current process immediately with status `code` via target OS/WASI syscall.",
        },
    },
    .{
        "sys_mmap",
        HoverDocSpec{
            .signature = "@sys_mmap(byte_len: usize) -> *mut u8",
            .summary = "Requests page-aligned anonymous virtual memory from the OS (`VirtualAlloc` / `mmap`), or null on failure.",
        },
    },
    .{
        "sys_munmap",
        HoverDocSpec{
            .signature = "@sys_munmap(ptr: *mut u8, byte_len: usize)",
            .summary = "Releases anonymous virtual pages previously mapped via `@sys_mmap`. Requires `unsafe`.",
        },
    },
    .{
        "sys_write",
        HoverDocSpec{
            .signature = "@sys_write(fd: i32, ptr: *u8, len: usize) -> isize",
            .summary = "Writes `len` bytes from `ptr` to file descriptor `fd` via low-level target syscall.",
        },
    },
    .{
        "tls_alloc_state",
        HoverDocSpec{
            .signature = "@tls_alloc_state() -> *mut opaque",
            .summary = "Returns the zero-initialized 256-byte thread-local `System` allocator bin state pointer.",
        },
    },
    .{
        "tls_scratch_ptr",
        HoverDocSpec{
            .signature = "@tls_scratch_ptr() -> *mut opaque",
            .summary = "Returns the zero-initialized 64-byte thread-local `[Arena; 2]` dual-scratch backing pointer.",
        },
    },
    .{
        "to_be_bytes",
        HoverDocSpec{
            .signature = "@to_be_bytes[T](val: T) -> [u8; @size_of[T]()]",
            .summary = "Encodes scalar `val` into its big-endian fixed-size byte array representation.",
        },
    },
    .{
        "to_le_bytes",
        HoverDocSpec{
            .signature = "@to_le_bytes[T](val: T) -> [u8; @size_of[T]()]",
            .summary = "Encodes scalar `val` into its little-endian fixed-size byte array representation.",
        },
    },
    .{
        "trap",
        HoverDocSpec{
            .signature = "@trap() -> never",
            .summary = "Emits an immediate hardware illegal-instruction trap (`ud2` / `brk` / `unreachable`).",
        },
    },
    .{
        "type_info",
        HoverDocSpec{
            .signature = "@type_info[T]() -> TypeInfo",
            .summary = "Returns the compile-time `cx.meta.TypeInfo` structural reflection mirror for `T`.",
        },
    },
    .{
        "type_name",
        HoverDocSpec{
            .signature = "@type_name[T]() -> str",
            .summary = "Returns the canonical compile-time UTF-8 string name of type `T`.",
        },
    },
    .{
        "view_bytes",
        HoverDocSpec{
            .signature = "@view_bytes[T](ptr: *T, byte_len: usize) -> &[u8]",
            .summary = "Constructs a bounded read-only byte slice view over `byte_len` bytes starting at `ptr`. Requires `unsafe`.",
        },
    },
    .{
        "wasm_memory_grow",
        HoverDocSpec{
            .signature = "@wasm_memory_grow(mem_idx: u32, delta_pages: usize) -> usize",
            .summary = "Grows WebAssembly linear memory `mem_idx` by `delta_pages` 64-KiB pages (`usize.MAX` on failure).",
        },
    },
});

comptime {
    @setEvalBranchQuota(16_384);
    if (BUILTIN_ATTR_HOVER_MAP.keys().len != type_system.BUILTIN_ATTRIBUTE_MAP.keys().len) {
        @compileError("BUILTIN_ATTR_HOVER_MAP drifted from type_system.BUILTIN_ATTRIBUTE_MAP");
    }
    for (type_system.BUILTIN_ATTRIBUTE_MAP.keys()) |attr_key| {
        if (!BUILTIN_ATTR_HOVER_MAP.has(attr_key)) {
            @compileError("Missing LSP hover documentation for @" ++ attr_key);
        }
    }
    if (INTRINSIC_HOVER_MAP.keys().len != type_system.INTRINSIC_NAME_MAP.keys().len) {
        @compileError("INTRINSIC_HOVER_MAP drifted from type_system.INTRINSIC_NAME_MAP");
    }
    for (type_system.INTRINSIC_NAME_MAP.keys()) |intr_key| {
        if (!INTRINSIC_HOVER_MAP.has(intr_key)) {
            @compileError("Missing LSP hover documentation for @" ++ intr_key);
        }
    }
}

/// Sorted CoreX surface keywords offered during lexical scope completion.
const COMPLETION_KEYWORDS = [_][]const u8{
    "and",
    "as",
    "async",
    "await",
    "bench",
    "bit_field",
    "break",
    "catch",
    "comptime",
    "const",
    "context",
    "continue",
    "defer",
    "else",
    "enum",
    "errdefer",
    "extern",
    "false",
    "fn",
    "for",
    "if",
    "impl",
    "in",
    "is",
    "let",
    "loop",
    "match",
    "mod",
    "mut",
    "not",
    "or",
    "orelse",
    "own",
    "pub",
    "return",
    "self",
    "struct",
    "subscript",
    "test",
    "trait",
    "true",
    "type",
    "union",
    "unreachable",
    "unsafe",
    "use",
    "var",
    "where",
    "while",
    "with",
    "yield",
};

/// Canonical capability display labels for `DR-17` §4.4 hover rendering (uses `"unsafe_op"`).
const CAPABILITY_DISPLAY_TABLE = [_]CapabilityDisplayEntry{
    .{ .bit = symbol_resolver.CapabilityBits.FS, .label = "fs" },
    .{ .bit = symbol_resolver.CapabilityBits.NET, .label = "net" },
    .{ .bit = symbol_resolver.CapabilityBits.ENV, .label = "env" },
    .{ .bit = symbol_resolver.CapabilityBits.PROCESS, .label = "process" },
    .{ .bit = symbol_resolver.CapabilityBits.FFI, .label = "ffi" },
    .{ .bit = symbol_resolver.CapabilityBits.UNSAFE_OP, .label = "unsafe_op" },
    .{ .bit = symbol_resolver.CapabilityBits.ALLOC, .label = "alloc" },
    .{ .bit = symbol_resolver.CapabilityBits.MAY_PANIC, .label = "may_panic" },
    .{ .bit = symbol_resolver.CapabilityBits.CLOCK, .label = "clock" },
    .{ .bit = symbol_resolver.CapabilityBits.ENTROPY, .label = "entropy" },
    .{ .bit = symbol_resolver.CapabilityBits.BLOCKING_SYNC, .label = "blocking_sync" },
    .{ .bit = symbol_resolver.CapabilityBits.INDIRECT_OPAQUE, .label = "indirect_opaque" },
};

// -------------------------------------- INTERNALS --------------------------------------

// ------------ Non-Backtracking JSON-RPC 2.0 Codec -------------

/// Parses a single ASCII hexadecimal nibble (`0..15`), returning `null` on non-hex bytes.
inline fn extractHexNibble(byte_val: u8) ?u8 {
    return switch (byte_val) {
        '0'...'9' => byte_val - '0',
        'a'...'f' => byte_val - 'a' + 10,
        'A'...'F' => byte_val - 'A' + 10,
        else => null,
    };
}

/// Parses 4 ASCII hexadecimal digits (`\uXXXX`) into a 16-bit UTF-16 code unit.
fn extractHexCodeUnit16(hex_quad: []const u8) ?u16 {
    if (hex_quad.len < 4) return null;
    var acc: u16 = 0;
    for (hex_quad[0..4]) |hex_ch| {
        const nib = extractHexNibble(hex_ch) orelse return null;
        acc = (acc << 4) | @as(u16, nib);
    }
    return acc;
}

/// Non-backtracking single-pass JSON scanner allocating DOM slices in `BumpArena`.
const JsonScanner = struct {
    /// Validated UTF-8 JSON source slice.
    src: []const u8,
    /// Current byte read cursor in `src`.
    cursor: usize = 0,
    /// Scratch arena allocator owning decoded strings, arrays, and objects.
    arena_alloc: std.mem.Allocator,

    /// Advances `cursor` past JSON RFC 8259 whitespace (`0x20`, `0x09`, `0x0A`, `0x0D`).
    fn skipWhitespace(self: *JsonScanner) void {
        while (self.cursor < self.src.len) {
            switch (self.src[self.cursor]) {
                ' ', '\t', '\n', '\r' => self.cursor += 1,
                else => break,
            }
        }
    }

    /// Parses one JSON value at `depth`, enforcing `depth < MAX_LSP_JSON_DEPTH`.
    fn parseValue(self: *JsonScanner, depth: usize) JsonParseError!JsonValue {
        if (depth >= MAX_LSP_JSON_DEPTH) return error.MaxDepthExceeded;
        self.skipWhitespace();
        if (self.cursor >= self.src.len) return error.InvalidJsonSyntax;

        return switch (self.src[self.cursor]) {
            '{' => self.parseObject(depth + 1),
            '[' => self.parseArray(depth + 1),
            '"' => .{ .string_val = try self.parseString() },
            't' => self.parseTrue(),
            'f' => self.parseFalse(),
            'n' => self.parseNull(),
            '-', '0'...'9' => self.parseNumber(),
            else => error.InvalidJsonSyntax,
        };
    }

    /// Parses literal `true`.
    fn parseTrue(self: *JsonScanner) JsonParseError!JsonValue {
        if (self.cursor + 4 > self.src.len or !std.mem.eql(u8, self.src[self.cursor .. self.cursor + 4], "true")) {
            return error.InvalidJsonSyntax;
        }
        self.cursor += 4;
        return .{ .bool_val = true };
    }

    /// Parses literal `false`.
    fn parseFalse(self: *JsonScanner) JsonParseError!JsonValue {
        if (self.cursor + 5 > self.src.len or !std.mem.eql(u8, self.src[self.cursor .. self.cursor + 5], "false")) {
            return error.InvalidJsonSyntax;
        }
        self.cursor += 5;
        return .{ .bool_val = false };
    }

    /// Parses literal `null`.
    fn parseNull(self: *JsonScanner) JsonParseError!JsonValue {
        if (self.cursor + 4 > self.src.len or !std.mem.eql(u8, self.src[self.cursor .. self.cursor + 4], "null")) {
            return error.InvalidJsonSyntax;
        }
        self.cursor += 4;
        return .{ .null_val = {} };
    }

    /// Parses an RFC 8259 JSON number into `.int_val` or `.float_val` without backtracking.
    fn parseNumber(self: *JsonScanner) JsonParseError!JsonValue {
        const start_pos = self.cursor;
        if (self.src[self.cursor] == '-') {
            self.cursor += 1;
            if (self.cursor >= self.src.len) return error.InvalidJsonSyntax;
        }
        if (self.src[self.cursor] == '0') {
            self.cursor += 1;
            if (self.cursor < self.src.len and std.ascii.isDigit(self.src[self.cursor])) {
                return error.InvalidJsonSyntax;
            }
        } else if (std.ascii.isDigit(self.src[self.cursor])) {
            while (self.cursor < self.src.len and std.ascii.isDigit(self.src[self.cursor])) {
                self.cursor += 1;
            }
        } else {
            return error.InvalidJsonSyntax;
        }

        var is_floating = false;
        if (self.cursor < self.src.len and self.src[self.cursor] == '.') {
            is_floating = true;
            self.cursor += 1;
            if (self.cursor >= self.src.len or !std.ascii.isDigit(self.src[self.cursor])) {
                return error.InvalidJsonSyntax;
            }
            while (self.cursor < self.src.len and std.ascii.isDigit(self.src[self.cursor])) {
                self.cursor += 1;
            }
        }
        if (self.cursor < self.src.len and (self.src[self.cursor] == 'e' or self.src[self.cursor] == 'E')) {
            is_floating = true;
            self.cursor += 1;
            if (self.cursor < self.src.len and (self.src[self.cursor] == '+' or self.src[self.cursor] == '-')) {
                self.cursor += 1;
            }
            if (self.cursor >= self.src.len or !std.ascii.isDigit(self.src[self.cursor])) {
                return error.InvalidJsonSyntax;
            }
            while (self.cursor < self.src.len and std.ascii.isDigit(self.src[self.cursor])) {
                self.cursor += 1;
            }
        }

        const num_slice = self.src[start_pos..self.cursor];
        if (!is_floating) {
            if (std.fmt.parseInt(i64, num_slice, 10)) |parsed_int| {
                return .{ .int_val = parsed_int };
            } else |_| {}
        }
        const parsed_float = std.fmt.parseFloat(f64, num_slice) catch return error.InvalidJsonSyntax;
        return .{ .float_val = parsed_float };
    }

    /// Parses a JSON string, rejecting control bytes `< 0x20` and lone UTF-16 surrogates.
    fn parseString(self: *JsonScanner) JsonParseError![]const u8 {
        if (self.cursor >= self.src.len or self.src[self.cursor] != '"') return error.InvalidJsonSyntax;
        self.cursor += 1;
        const body_start = self.cursor;
        var has_escapes = false;

        while (self.cursor < self.src.len) {
            const byte_val = self.src[self.cursor];
            if (byte_val == '"') {
                const raw_slice = self.src[body_start..self.cursor];
                self.cursor += 1;
                if (!has_escapes) {
                    return try self.arena_alloc.dupe(u8, raw_slice);
                }
                return self.unescapeJsonString(raw_slice);
            } else if (byte_val < 0x20) {
                return error.InvalidJsonSyntax;
            } else if (byte_val == '\\') {
                has_escapes = true;
                self.cursor += 1;
                if (self.cursor >= self.src.len or self.src[self.cursor] < 0x20) {
                    return error.InvalidJsonSyntax;
                }
            }
            self.cursor += 1;
        }
        return error.InvalidJsonSyntax;
    }

    /// Decodes escape sequences (including `\uD800..\uDBFF\uDC00..\uDFFF` surrogate pairs) to UTF-8.
    fn unescapeJsonString(self: *JsonScanner, raw_slice: []const u8) JsonParseError![]const u8 {
        var out_bytes: std.ArrayListUnmanaged(u8) = .empty;
        try out_bytes.ensureTotalCapacity(self.arena_alloc, raw_slice.len);

        var pos: usize = 0;
        while (pos < raw_slice.len) {
            const byte_val = raw_slice[pos];
            if (byte_val != '\\') {
                if (byte_val < 0x20) return error.InvalidJsonSyntax;
                try out_bytes.append(self.arena_alloc, byte_val);
                pos += 1;
                continue;
            }
            pos += 1;
            if (pos >= raw_slice.len) return error.InvalidJsonSyntax;
            const esc_char = raw_slice[pos];
            pos += 1;
            switch (esc_char) {
                '"', '\\', '/' => try out_bytes.append(self.arena_alloc, esc_char),
                'b' => try out_bytes.append(self.arena_alloc, 0x08),
                'f' => try out_bytes.append(self.arena_alloc, 0x0C),
                'n' => try out_bytes.append(self.arena_alloc, '\n'),
                'r' => try out_bytes.append(self.arena_alloc, '\r'),
                't' => try out_bytes.append(self.arena_alloc, '\t'),
                'u' => {
                    if (pos + 4 > raw_slice.len) return error.InvalidJsonSyntax;
                    const first_unit = extractHexCodeUnit16(raw_slice[pos .. pos + 4]) orelse
                        return error.InvalidJsonSyntax;
                    pos += 4;

                    var scalar: u21 = 0;
                    if (first_unit >= 0xD800 and first_unit <= 0xDBFF) {
                        if (pos + 6 > raw_slice.len or raw_slice[pos] != '\\' or raw_slice[pos + 1] != 'u') {
                            return error.InvalidJsonSyntax;
                        }
                        const low_unit = extractHexCodeUnit16(raw_slice[pos + 2 .. pos + 6]) orelse
                            return error.InvalidJsonSyntax;
                        if (low_unit < 0xDC00 or low_unit > 0xDFFF) {
                            return error.InvalidJsonSyntax;
                        }
                        pos += 6;
                        scalar = 0x10000 +
                            ((@as(u21, first_unit - 0xD800) << 10) | @as(u21, low_unit - 0xDC00));
                    } else if (first_unit >= 0xDC00 and first_unit <= 0xDFFF) {
                        return error.InvalidJsonSyntax;
                    } else {
                        scalar = @intCast(first_unit);
                    }

                    var utf8_seq: [4]u8 = undefined;
                    const seq_len = std.unicode.utf8Encode(scalar, &utf8_seq) catch
                        return error.InvalidJsonSyntax;
                    try out_bytes.appendSlice(self.arena_alloc, utf8_seq[0..seq_len]);
                },
                else => return error.InvalidJsonSyntax,
            }
        }
        return out_bytes.items;
    }

    /// Parses a JSON array `[v0, v1, …]` at `next_depth`.
    fn parseArray(self: *JsonScanner, next_depth: usize) JsonParseError!JsonValue {
        self.cursor += 1;
        self.skipWhitespace();
        if (self.cursor >= self.src.len) return error.InvalidJsonSyntax;
        if (self.src[self.cursor] == ']') {
            self.cursor += 1;
            return .{ .array_val = &.{} };
        }

        var items: std.ArrayListUnmanaged(JsonValue) = .empty;
        while (true) {
            try items.append(self.arena_alloc, try self.parseValue(next_depth));
            self.skipWhitespace();
            if (self.cursor >= self.src.len) return error.InvalidJsonSyntax;
            switch (self.src[self.cursor]) {
                ',' => {
                    self.cursor += 1;
                    continue;
                },
                ']' => {
                    self.cursor += 1;
                    return .{ .array_val = items.items };
                },
                else => return error.InvalidJsonSyntax,
            }
        }
    }

    /// Parses a JSON object `{"k": v, …}` at `next_depth`.
    fn parseObject(self: *JsonScanner, next_depth: usize) JsonParseError!JsonValue {
        self.cursor += 1;
        self.skipWhitespace();
        if (self.cursor >= self.src.len) return error.InvalidJsonSyntax;
        if (self.src[self.cursor] == '}') {
            self.cursor += 1;
            return .{ .object_val = &.{} };
        }

        var fields: std.ArrayListUnmanaged(JsonObjectField) = .empty;
        while (true) {
            self.skipWhitespace();
            if (self.cursor >= self.src.len or self.src[self.cursor] != '"') {
                return error.InvalidJsonSyntax;
            }
            const key_str = try self.parseString();
            self.skipWhitespace();
            if (self.cursor >= self.src.len or self.src[self.cursor] != ':') {
                return error.InvalidJsonSyntax;
            }
            self.cursor += 1;
            const field_val = try self.parseValue(next_depth);
            try fields.append(self.arena_alloc, .{ .key = key_str, .value = field_val });

            self.skipWhitespace();
            if (self.cursor >= self.src.len) return error.InvalidJsonSyntax;
            switch (self.src[self.cursor]) {
                ',' => {
                    self.cursor += 1;
                    continue;
                },
                '}' => {
                    self.cursor += 1;
                    return .{ .object_val = fields.items };
                },
                else => return error.InvalidJsonSyntax,
            }
        }
    }
};

/// Validates UTF-8 and parses an entire JSON-RPC payload in `arena_alloc` without backtracking.
fn parseJsonPayload(arena_alloc: std.mem.Allocator, payload: []const u8) JsonParseError!JsonValue {
    if (!std.unicode.utf8ValidateSlice(payload)) return error.InvalidJsonSyntax;
    var scanner = JsonScanner{
        .src = payload,
        .arena_alloc = arena_alloc,
    };
    const root_val = try scanner.parseValue(0);
    scanner.skipWhitespace();
    if (scanner.cursor != payload.len) return error.InvalidJsonSyntax;
    return root_val;
}

/// Extracts a `JsonRpcId` from a parsed JSON-RPC object (`missing` when `"id"` is absent).
fn extractJsonRpcId(msg_obj: JsonValue) !JsonRpcId {
    const raw_id = msg_obj.getField("id") orelse return .missing;
    return switch (raw_id) {
        .null_val => .null_id,
        .int_val => |int_val| .{ .int_id = int_val },
        .string_val => |str_val| .{ .string_id = str_val },
        else => error.InvalidRequestId,
    };
}

/// Writes RFC 8259 escaped JSON string literal `"…"` directly to `writer`.
fn writeJsonString(writer: *std.Io.Writer, text: []const u8) !void {
    try writer.writeByte('"');
    var clean_start: usize = 0;
    var i: usize = 0;
    while (i < text.len) : (i += 1) {
        const byte_val = text[i];
        if (byte_val != '"' and byte_val != '\\' and byte_val >= 0x20) continue;
        if (i > clean_start) {
            try writer.writeAll(text[clean_start..i]);
        }
        switch (byte_val) {
            '"' => try writer.writeAll("\\\""),
            '\\' => try writer.writeAll("\\\\"),
            '\n' => try writer.writeAll("\\n"),
            '\r' => try writer.writeAll("\\r"),
            '\t' => try writer.writeAll("\\t"),
            0x08 => try writer.writeAll("\\b"),
            0x0C => try writer.writeAll("\\f"),
            else => try writer.print("\\u{x:0>4}", .{byte_val}),
        }
        clean_start = i + 1;
    }
    if (clean_start < text.len) {
        try writer.writeAll(text[clean_start..]);
    }
    try writer.writeByte('"');
}

/// Writes a `JsonRpcId` token (`null`, integer, or quoted string) to `writer`.
fn writeJsonRpcId(writer: *std.Io.Writer, rpc_id: JsonRpcId) !void {
    switch (rpc_id) {
        .missing, .null_id => try writer.writeAll("null"),
        .int_id => |int_val| try writer.print("{d}", .{int_val}),
        .string_id => |str_val| try writeJsonString(writer, str_val),
    }
}

/// Flushes a complete `Content-Length: <N>\r\n\r\n<json>` JSON-RPC 2.0 frame onto `out_writer`.
fn flushOutboundJsonFrame(out_writer: *std.Io.Writer, json_bytes: []const u8) !void {
    try out_writer.print("Content-Length: {d}\r\n\r\n", .{json_bytes.len});
    try out_writer.writeAll(json_bytes);
    try out_writer.flush();
}

/// Emits a JSON-RPC 2.0 error response frame and flushes `out_writer`.
fn sendJsonRpcError(
    session: *LspSession,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
    error_code: i32,
    message: []const u8,
) !void {
    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.print(",\"error\":{{\"code\":{d},\"message\":", .{error_code});
    try writeJsonString(body_writer, message);
    try body_writer.writeAll("}}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

// -------- std.Io Framing & Buffered Priority Pre-Drain --------

/// Parses an HTTP-style LSP header block (`header_bytes` excluding final `\r\n\r\n`) for `Content-Length`.
fn extractHeaderContentLength(header_bytes: []const u8) ParsedContentLength {
    var parsed_state: ?ParsedContentLength = null;
    var line_iter = std.mem.splitScalar(u8, header_bytes, '\n');
    while (line_iter.next()) |raw_line| {
        const line = std.mem.trimEnd(u8, raw_line, "\r");
        if (line.len == 0) continue;
        const colon_idx = std.mem.indexOfScalar(u8, line, ':') orelse return .invalid;
        const header_name = std.mem.trim(u8, line[0..colon_idx], " \t");
        const header_val = std.mem.trim(u8, line[colon_idx + 1 ..], " \t");
        if (std.ascii.eqlIgnoreCase(header_name, "content-length")) {
            if (header_val.len == 0) return .invalid;
            for (header_val) |digit_ch| {
                if (!std.ascii.isDigit(digit_ch)) return .invalid;
            }
            if (std.fmt.parseUnsigned(usize, header_val, 10)) |len_val| {
                if (parsed_state) |prev_state| {
                    if (prev_state != .ok or prev_state.ok != len_val) return .invalid;
                }
                parsed_state = .{ .ok = len_val };
            } else |parse_err| switch (parse_err) {
                error.Overflow => {
                    if (parsed_state) |prev_state| {
                        if (prev_state != .overflow) return .invalid;
                    }
                    parsed_state = .overflow;
                },
                error.InvalidCharacter => return .invalid,
            }
        } else if (std.ascii.eqlIgnoreCase(header_name, "content-type")) {
            if (header_val.len == 0) return .invalid;
        }
    }
    return parsed_state orelse .invalid;
}

/// Reads a single LSP frame from `reader`, enforcing `MAX_LSP_HEADER_BYTES` and `MAX_LSP_CONTENT_LENGTH`.
fn readSingleInboundFrame(allocator: std.mem.Allocator, reader: *std.Io.Reader) !InboundFrame {
    var header_buf: [MAX_LSP_HEADER_BYTES]u8 = undefined;
    var header_len: usize = 0;
    var has_header_end = false;

    while (header_len < MAX_LSP_HEADER_BYTES) {
        var one_byte: [1]u8 = undefined;
        const got_n = try reader.readSliceShort(&one_byte);
        if (got_n == 0) {
            if (header_len == 0) return .eof;
            return .header_parse_error;
        }
        header_buf[header_len] = one_byte[0];
        header_len += 1;

        if (header_len >= 4 and
            header_buf[header_len - 4] == '\r' and
            header_buf[header_len - 3] == '\n' and
            header_buf[header_len - 2] == '\r' and
            header_buf[header_len - 1] == '\n')
        {
            has_header_end = true;
            header_len -= 4;
            break;
        }
    }

    if (!has_header_end) {
        // Drain until `\r\n\r\n` or bounded limit so subsequent frames can recover cleanly:
        var match_state: u8 = 0;
        var drain_budget: usize = MAX_LSP_HEADER_BYTES * 4;
        while (drain_budget > 0) : (drain_budget -= 1) {
            var ch_buf: [1]u8 = undefined;
            const got_n = try reader.readSliceShort(&ch_buf);
            if (got_n == 0) break;
            const ch_val = ch_buf[0];
            match_state = switch (match_state) {
                0 => if (ch_val == '\r') 1 else 0,
                1 => if (ch_val == '\n') 2 else if (ch_val == '\r') 1 else 0,
                2 => if (ch_val == '\r') 3 else 0,
                3 => if (ch_val == '\n') 4 else if (ch_val == '\r') 1 else 0,
                else => 4,
            };
            if (match_state == 4) break;
        }
        return .header_parse_error;
    }

    const content_len: usize = switch (extractHeaderContentLength(header_buf[0..header_len])) {
        .invalid => return .header_parse_error,
        .overflow => {
            const buffered_len = reader.bufferedLen();
            if (buffered_len > 0) reader.toss(buffered_len);
            return .{ .content_too_large = true };
        },
        .ok => |parsed_len| parsed_len,
    };
    if (content_len > MAX_LSP_CONTENT_LENGTH) {
        const buffered_len = reader.bufferedLen();
        if (content_len <= buffered_len) {
            reader.toss(content_len);
            return .{ .content_too_large = false };
        }
        if (buffered_len > 0) reader.toss(buffered_len);
        return .{ .content_too_large = true };
    }

    const payload_buf = try allocator.alloc(u8, content_len);
    errdefer allocator.free(payload_buf);
    if (content_len > 0) {
        reader.readSliceAll(payload_buf) catch |read_err| switch (read_err) {
            error.EndOfStream => {
                allocator.free(payload_buf);
                return .header_parse_error;
            },
            error.ReadFailed => return error.ReadFailed,
        };
    }
    return .{ .payload = payload_buf };
}

/// Non-blockingly inspects `reader.buffered()` and extracts one complete frame if already resident.
fn tryExtractCompleteBufferedFrame(
    allocator: std.mem.Allocator,
    reader: *std.Io.Reader,
) !?InboundFrame {
    const avail = reader.buffered();
    if (avail.len < 4) return null;

    const sep_pos = std.mem.indexOf(
        u8,
        avail[0..@min(avail.len, MAX_LSP_HEADER_BYTES)],
        "\r\n\r\n",
    ) orelse return null;
    const body_start = sep_pos + 4;
    const content_len: usize = switch (extractHeaderContentLength(avail[0..sep_pos])) {
        .invalid => {
            reader.toss(body_start);
            return .header_parse_error;
        },
        .overflow => {
            reader.toss(avail.len);
            return .{ .content_too_large = true };
        },
        .ok => |parsed_len| parsed_len,
    };
    if (content_len > MAX_LSP_CONTENT_LENGTH) {
        if (std.math.add(usize, body_start, content_len)) |oversized_end| {
            if (avail.len >= oversized_end) {
                reader.toss(oversized_end);
                return .{ .content_too_large = false };
            }
        } else |_| {}
        reader.toss(avail.len);
        return .{ .content_too_large = true };
    }
    const frame_end = std.math.add(usize, body_start, content_len) catch {
        reader.toss(avail.len);
        return .{ .content_too_large = true };
    };
    if (avail.len < frame_end) return null;

    const payload_copy = try allocator.dupe(u8, avail[body_start..frame_end]);
    reader.toss(frame_end);
    return .{ .payload = payload_copy };
}

// -------- Cross-Platform file:// URI Codec & Positions --------

/// Percent-decodes `input` into `out_buf`, returning `null` if the decoded length exceeds `out_buf.len`.
fn decodePercentSliceBounded(out_buf: []u8, input: []const u8) ?[]const u8 {
    var out_len: usize = 0;
    var i: usize = 0;
    while (i < input.len) {
        if (out_len >= out_buf.len) return null;
        if (input[i] == '%' and i + 2 < input.len) {
            if (extractHexNibble(input[i + 1])) |hi_nib| {
                if (extractHexNibble(input[i + 2])) |lo_nib| {
                    out_buf[out_len] = (hi_nib << 4) | lo_nib;
                    out_len += 1;
                    i += 3;
                    continue;
                }
            }
        }
        out_buf[out_len] = input[i];
        out_len += 1;
        i += 1;
    }
    return out_buf[0..out_len];
}

/// Percent-decodes `%XX` sequences in `input` and normalizes `\` separators to `/`.
fn appendPercentDecodedNormalized(
    out_list: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    input: []const u8,
) !void {
    try out_list.ensureUnusedCapacity(allocator, input.len);
    var i: usize = 0;
    while (i < input.len) {
        if (input[i] == '%' and i + 2 < input.len) {
            if (extractHexNibble(input[i + 1])) |hi_nib| {
                if (extractHexNibble(input[i + 2])) |lo_nib| {
                    const decoded_byte: u8 = (hi_nib << 4) | lo_nib;
                    out_list.appendAssumeCapacity(if (decoded_byte == '\\') '/' else decoded_byte);
                    i += 3;
                    continue;
                }
            }
        }
        out_list.appendAssumeCapacity(if (input[i] == '\\') '/' else input[i]);
        i += 1;
    }
}

/// Extracts `params.textDocument.uri` and validates `1 <= uri.len <= MAX_LSP_URI_BYTES`, or emits `-32602`.
fn extractValidatedRequestUri(
    session: *LspSession,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !?[]const u8 {
    const td_obj = params.getField("textDocument") orelse {
        try sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing textDocument");
        return null;
    };
    const raw_uri = td_obj.getStringField("uri") orelse {
        try sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing uri");
        return null;
    };
    if (raw_uri.len == 0 or raw_uri.len > MAX_LSP_URI_BYTES) {
        try sendJsonRpcError(
            session,
            out_writer,
            rpc_id,
            JSONRPC_INVALID_PARAMS,
            "URI is empty or exceeds MAX_LSP_URI_BYTES",
        );
        return null;
    }
    return raw_uri;
}

/// Extracts `params.textDocument.uri` for notifications, returning `null` if absent, empty, or `> MAX_LSP_URI_BYTES`.
fn extractValidatedNotificationUri(params: JsonValue) ?[]const u8 {
    const td_obj = params.getField("textDocument") orelse return null;
    const raw_uri = td_obj.getStringField("uri") orelse return null;
    if (raw_uri.len == 0 or raw_uri.len > MAX_LSP_URI_BYTES) return null;
    return raw_uri;
}

/// Resolves the outbound URI string for `file_id`, echoing the client's `didOpen` URI when known.
fn resolveOutboundUri(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    file_id: FileId,
) ![]const u8 {
    if (session.file_id_to_client_uri.get(file_id.asInt())) |client_uri| {
        return client_uri;
    }
    const raw_vpath = session.vfs.getFilePath(file_id);
    const vfs_path = if (raw_vpath.len > 0) raw_vpath else "untitled.cx";
    if (session.workspace_root_dir) |ws_root| {
        const is_abs_path = std.mem.startsWith(u8, vfs_path, "/") or
            (vfs_path.len >= 2 and std.ascii.isAlphabetic(vfs_path[0]) and vfs_path[1] == ':');
        if (!is_abs_path) {
            const joined = try std.fmt.allocPrint(arena_alloc, "{s}/{s}", .{ ws_root, vfs_path });
            return encodePathToFileUri(arena_alloc, joined);
        }
    }
    return encodePathToFileUri(arena_alloc, vfs_path);
}

/// Returns the live UTF-8 source for `file_id`, re-hydrating `session.vfs` + `LineIndex` from `CompilerDb` if LRU-evicted.
fn getLiveDocumentSource(session: *LspSession, file_id: FileId) ?[]const u8 {
    if (file_id.isNone()) return null;
    if (session.open_doc_versions.contains(file_id.asInt())) {
        if (session.db.source_inputs.get(file_id.asInt())) |src_input| {
            const db_text = src_input.owned_text;
            if (file_id.asInt() < session.vfs.entries.items.len) {
                const vfs_entry = &session.vfs.entries.items[file_id.asInt()];
                if (!vfs_entry.is_open_in_editor or
                    !session.vfs.overlay_cache.file_to_slot.contains(file_id) or
                    vfs_entry.content.len != db_text.len)
                {
                    const vfs_path = session.vfs.getFilePath(file_id);
                    if (vfs_path.len > 0 and db_text.len <= vfs_sourcemap.MAX_OPEN_OVERLAY_BYTES) {
                        const pkg_id = session.db.symbol_table.getFilePackageId(file_id);
                        if (session.vfs.setEditorOverlay(session.io, vfs_path, db_text, pkg_id, true)) |_| {
                            _ = session.vfs.getLineIndex(file_id) catch {};
                        } else |_| {}
                    }
                }
            }
            return db_text;
        }
    }
    if (session.vfs.getFileSource(file_id)) |vfs_text| {
        return vfs_text;
    }
    if (session.db.source_inputs.get(file_id.asInt())) |src_input| {
        return src_input.owned_text;
    }
    return null;
}

/// Converts `byte_offset` into a zero-based `LspPosition` using pre-fetched `src` and `line_idx`.
fn byteOffsetToLspPositionFast(
    src: []const u8,
    line_idx: *const LineIndex,
    encoding: PositionEncoding,
    byte_offset: u32,
) LspPosition {
    const clamped_off: u32 = @intCast(@min(@as(usize, byte_offset), src.len));
    const lc = line_idx.resolveLineCol(src, clamped_off);
    return .{
        .line = lc.line -| 1,
        .character = LineIndex.extractLspCharacter0(lc, encoding),
    };
}

/// Converts `span` into a half-open `LspRange` using pre-fetched `src` and `line_idx`.
fn spanToLspRangeFast(
    src: []const u8,
    line_idx: *const LineIndex,
    encoding: PositionEncoding,
    span: Span,
) LspRange {
    const end_byte = @max(span.start_byte, span.end_byte);
    return .{
        .start = byteOffsetToLspPositionFast(src, line_idx, encoding, span.start_byte),
        .end = byteOffsetToLspPositionFast(src, line_idx, encoding, end_byte),
    };
}

/// Converts a byte offset in `file_id` into a zero-based `LspPosition` under `session.position_encoding`.
fn byteOffsetToLspPosition(session: *LspSession, file_id: FileId, byte_offset: u32) LspPosition {
    const src = getLiveDocumentSource(session, file_id) orelse "";
    const line_idx = session.vfs.getLineIndex(file_id) catch return .{};
    return byteOffsetToLspPositionFast(src, line_idx, session.position_encoding, byte_offset);
}

/// Converts a `Span` into a half-open `LspRange` under `session.position_encoding`.
fn spanToLspRange(session: *LspSession, fallback_fid: FileId, span: Span) LspRange {
    const target_fid = if (!span.file_id.isNone()) span.file_id else fallback_fid;
    const src = getLiveDocumentSource(session, target_fid) orelse "";
    const line_idx = session.vfs.getLineIndex(target_fid) catch return .{};
    return spanToLspRangeFast(src, line_idx, session.position_encoding, span);
}

/// Extracts an `LspPosition` `(line, character)` from a JSON `Position` object.
fn extractJsonPosition(pos_obj: JsonValue) ?LspPosition {
    if (pos_obj != .object_val) return null;
    const raw_line = pos_obj.getIntField("line") orelse return null;
    const raw_char = pos_obj.getIntField("character") orelse return null;
    if (raw_line < 0 or raw_char < 0) return null;
    return .{
        .line = @intCast(@min(raw_line, std.math.maxInt(u32))),
        .character = @intCast(@min(raw_char, std.math.maxInt(u32))),
    };
}

/// Extracts an `LspRange` `(start, end)` from a JSON `Range` object.
fn extractJsonRange(range_obj: JsonValue) ?LspRange {
    if (range_obj != .object_val) return null;
    const start_pos = extractJsonPosition(range_obj.getField("start") orelse return null) orelse return null;
    const end_pos = extractJsonPosition(range_obj.getField("end") orelse return null) orelse return null;
    return .{ .start = start_pos, .end = end_pos };
}

/// Resolves an `LspPosition` inside `file_id` to a clamped source byte offset.
fn lspPositionToByteOffset(session: *LspSession, file_id: FileId, pos: LspPosition) u32 {
    const src = getLiveDocumentSource(session, file_id) orelse return 0;
    const line_idx = session.vfs.getLineIndex(file_id) catch return 0;
    const resolved = line_idx.resolveByteOffset(src, pos.line, pos.character, session.position_encoding);
    return @intCast(@min(resolved, src.len));
}

/// Writes an `LspRange` JSON object `{"start":{"line":…,"character":…},"end":{…}}` to `writer`.
fn writeLspRangeJson(writer: *std.Io.Writer, range: LspRange) !void {
    try writer.print(
        "{{\"start\":{{\"line\":{d},\"character\":{d}}},\"end\":{{\"line\":{d},\"character\":{d}}}}}",
        .{ range.start.line, range.start.character, range.end.line, range.end.character },
    );
}

/// Writes an LSP `Location` JSON object `{"uri":…,"range":…}` to `writer`.
fn writeLspLocationJson(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    writer: *std.Io.Writer,
    span: Span,
) !void {
    const uri_str = try resolveOutboundUri(session, arena_alloc, span.file_id);
    const range = spanToLspRange(session, span.file_id, span);
    try writer.writeAll("{\"uri\":");
    try writeJsonString(writer, uri_str);
    try writer.writeAll(",\"range\":");
    try writeLspRangeJson(writer, range);
    try writer.writeByte('}');
}

// --------- Lazy Workspace, Manifest & Stdlib Mounting ---------

/// Resolves the `COREX_HOME` cache directory path from `environ_map` (falling back to `.corex`).
fn resolveCorexHomeDir(
    allocator: std.mem.Allocator,
    environ_map: ?*const std.process.Environ.Map,
) ![]u8 {
    if (environ_map) |env| {
        if (env.get("COREX_HOME")) |explicit_home| {
            if (explicit_home.len > 0) return allocator.dupe(u8, explicit_home);
        }
        if (env.get("HOME") orelse env.get("USERPROFILE")) |user_home| {
            if (user_home.len > 0) {
                return std.fmt.allocPrint(allocator, "{s}/.corex", .{user_home});
            }
        }
    }
    return allocator.dupe(u8, ".corex");
}

/// Discovers `corex.toml` walking upward from `start_dir` up to `MAX_MANIFEST_ANCESTOR_HOPS` levels.
fn findNearestManifestToml(
    allocator: std.mem.Allocator,
    io: std.Io,
    start_dir: []const u8,
) !?[]u8 {
    var cur_dir: []const u8 = start_dir;
    var hop: usize = 0;
    while (hop < MAX_MANIFEST_ANCESTOR_HOPS) : (hop += 1) {
        const cand_toml = try std.fmt.allocPrint(allocator, "{s}/corex.toml", .{std.mem.trimEnd(u8, cur_dir, "/")});
        if (std.Io.Dir.cwd().openFile(io, cand_toml, .{ .mode = .read_only })) |opened_file| {
            opened_file.close(io);
            return cand_toml;
        } else |_| {
            allocator.free(cand_toml);
        }
        const parent_dir = std.fs.path.dirname(cur_dir) orelse break;
        if (std.mem.eql(u8, parent_dir, cur_dir)) break;
        cur_dir = parent_dir;
    }
    return null;
}

/// Shallowly mounts `parent_fid` and binds its external `mod <child>;` disk files without body typechecking.
fn mountExternalSubmodulesShallow(
    session: *LspSession,
    parent_fid: FileId,
    parent_path: []const u8,
    default_durability: Durability,
    pkg_id: PackageId,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
    depth: u32,
) !void {
    if (depth >= MAX_MODULE_DISCOVERY_DEPTH or visited_fids.contains(parent_fid.asInt())) return;
    try visited_fids.put(session.allocator, parent_fid.asInt(), {});
    try session.recordMountedFile(parent_fid);

    const is_open_overlay = session.open_doc_versions.contains(parent_fid.asInt());
    const parent_src = getLiveDocumentSource(session, parent_fid) orelse "";
    _ = session.vfs.getLineIndex(parent_fid) catch {};
    const effective_dur: Durability = if (is_open_overlay) .low else default_durability;

    if (!is_open_overlay or !session.db.source_inputs.contains(parent_fid.asInt())) {
        _ = try session.db.setInput(parent_fid, parent_src, effective_dur);
    }
    if (pkg_id != .root) {
        try session.db.setFilePackageId(parent_fid, pkg_id);
    }
    try session.db.setFilePath(parent_fid, parent_path);

    var ext_mod_names: std.ArrayListUnmanaged([]const u8) = .empty;
    defer ext_mod_names.deinit(session.allocator);
    {
        const parsed_art = session.db.parseCst(parent_fid) catch return;
        const item_tree = session.db.extractItemTree(parent_fid) catch return;
        for (item_tree.entries) |entry| {
            if (entry.kind != .mod_decl or entry.name_text.len == 0) continue;
            if (!entry.ast_node.isNone() and
                entry.ast_node.asInt() < parsed_art.ast_arena.countNodes() and
                parsed_art.ast_arena.getNode(entry.ast_node).rhs.tag == .extra)
            {
                continue;
            }
            try ext_mod_names.append(session.allocator, entry.name_text);
        }
    }

    const parent_dir = std.fs.path.dirname(parent_path) orelse ".";
    const parent_base = std.fs.path.basename(parent_path);
    const parent_stem = std.fs.path.stem(parent_path);
    const is_hub_file = HUB_MODULE_BASENAME_SET.has(parent_base);

    for (ext_mod_names.items) |mod_name| {
        var cand_paths: [4]?[]u8 = @splat(null);
        defer {
            for (cand_paths) |maybe_path| {
                if (maybe_path) |owned_p| session.allocator.free(owned_p);
            }
        }
        var cand_len: usize = 0;
        if (!is_hub_file) {
            cand_paths[cand_len] = try std.fmt.allocPrint(
                session.allocator,
                "{s}/{s}/{s}.cx",
                .{ parent_dir, parent_stem, mod_name },
            );
            cand_len += 1;
            cand_paths[cand_len] = try std.fmt.allocPrint(
                session.allocator,
                "{s}/{s}/{s}/mod.cx",
                .{ parent_dir, parent_stem, mod_name },
            );
            cand_len += 1;
        }
        cand_paths[cand_len] = try std.fmt.allocPrint(session.allocator, "{s}/{s}.cx", .{ parent_dir, mod_name });
        cand_len += 1;
        cand_paths[cand_len] = try std.fmt.allocPrint(
            session.allocator,
            "{s}/{s}/mod.cx",
            .{ parent_dir, mod_name },
        );
        cand_len += 1;

        var i: usize = 0;
        while (i < cand_len) : (i += 1) {
            const cand_str = cand_paths[i].?;
            if (session.vfs.resolveOrCreatePath(session.io, cand_str, pkg_id)) |child_fid| {
                _ = session.vfs.getLineIndex(child_fid) catch {};
                try session.db.bindExternalModule(parent_fid, mod_name, child_fid);
                const child_dur: Durability = if (pkg_id == .std_core)
                    .high
                else if (pkg_id == .root)
                    .medium
                else
                    default_durability;
                try mountExternalSubmodulesShallow(
                    session,
                    child_fid,
                    cand_str,
                    child_dur,
                    pkg_id,
                    visited_fids,
                    depth + 1,
                );
                break;
            } else |_| {}
        }
    }
}

/// Shallowly mounts virtual `/cx/<pkg>@<ver>/…` `.cxtree` modules at `Durability.high`.
fn mountCxTreeSubmodulesShallow(
    session: *LspSession,
    parent_fid: FileId,
    parent_vpath: []const u8,
    pkg_id: PackageId,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
    depth: u32,
) !void {
    if (depth >= MAX_MODULE_DISCOVERY_DEPTH or visited_fids.contains(parent_fid.asInt())) return;
    try visited_fids.put(session.allocator, parent_fid.asInt(), {});
    try session.recordMountedFile(parent_fid);

    const parent_src = session.vfs.faultCxTreeFile(parent_fid) catch return;
    _ = session.vfs.getLineIndex(parent_fid) catch {};
    _ = try session.db.setInput(parent_fid, parent_src, .high);
    try session.db.setFilePackageId(parent_fid, pkg_id);
    try session.db.setFilePath(parent_fid, parent_vpath);

    var ext_mod_names: std.ArrayListUnmanaged([]const u8) = .empty;
    defer ext_mod_names.deinit(session.allocator);
    {
        const parsed_art = session.db.parseCst(parent_fid) catch return;
        const item_tree = session.db.extractItemTree(parent_fid) catch return;
        for (item_tree.entries) |entry| {
            if (entry.kind != .mod_decl or entry.name_text.len == 0) continue;
            if (!entry.ast_node.isNone() and
                parsed_art.ast_arena.getNode(entry.ast_node).rhs.tag == .extra)
            {
                continue;
            }
            try ext_mod_names.append(session.allocator, entry.name_text);
        }
    }

    const parent_dir = std.fs.path.dirname(parent_vpath) orelse "";
    const parent_base = std.fs.path.basename(parent_vpath);
    const parent_stem = std.fs.path.stem(parent_vpath);
    const is_hub_file = HUB_MODULE_BASENAME_SET.has(parent_base);

    for (ext_mod_names.items) |mod_name| {
        var cand_paths: [4]?[]u8 = @splat(null);
        defer {
            for (cand_paths) |maybe_p| {
                if (maybe_p) |owned_p| session.allocator.free(owned_p);
            }
        }
        var cand_len: usize = 0;
        if (!is_hub_file) {
            cand_paths[cand_len] = try std.fmt.allocPrint(
                session.allocator,
                "{s}/{s}/{s}.cx",
                .{ parent_dir, parent_stem, mod_name },
            );
            cand_len += 1;
            cand_paths[cand_len] = try std.fmt.allocPrint(
                session.allocator,
                "{s}/{s}/{s}/mod.cx",
                .{ parent_dir, parent_stem, mod_name },
            );
            cand_len += 1;
        }
        cand_paths[cand_len] = try std.fmt.allocPrint(session.allocator, "{s}/{s}.cx", .{ parent_dir, mod_name });
        cand_len += 1;
        cand_paths[cand_len] = try std.fmt.allocPrint(
            session.allocator,
            "{s}/{s}/mod.cx",
            .{ parent_dir, mod_name },
        );
        cand_len += 1;

        var i: usize = 0;
        while (i < cand_len) : (i += 1) {
            const cand_vpath = cand_paths[i].?;
            const vpath_id = session.vfs.interner.lookup(cand_vpath) orelse continue;
            const child_fid = session.vfs.path_to_file_id.get(vpath_id) orelse continue;
            try session.db.bindExternalModule(parent_fid, mod_name, child_fid);
            try mountCxTreeSubmodulesShallow(
                session,
                child_fid,
                cand_vpath,
                pkg_id,
                visited_fids,
                depth + 1,
            );
            break;
        }
    }
}

/// Lazily mounts `core/root.cx` and optional `stdlib/cx/mod.cx` (`PackageId.std_core`) in `session`.
fn mountWorkspaceCoreStdlibLazy(
    session: *LspSession,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
) !void {
    const core_durability: Durability = if (session.options.is_internal_core) .medium else .high;
    var prefix_opt: ?[]u8 = null;
    defer if (prefix_opt) |owned_p| session.allocator.free(owned_p);
    var core_path_opt: ?[]u8 = null;
    defer if (core_path_opt) |owned_c| session.allocator.free(owned_c);

    var core_fid: FileId = .none;
    if (session.workspace_root_dir) |ws_root| {
        const trimmed = std.mem.trimEnd(u8, ws_root, "/");
        const ws_prefix = try std.fmt.allocPrint(session.allocator, "{s}/", .{trimmed});
        const ws_core = try std.fmt.allocPrint(session.allocator, "{s}core/root.cx", .{ws_prefix});
        if (session.vfs.resolveOrCreatePath(session.io, ws_core, .std_core)) |fid| {
            prefix_opt = ws_prefix;
            core_path_opt = ws_core;
            core_fid = fid;
        } else |_| {
            session.allocator.free(ws_core);
            session.allocator.free(ws_prefix);
        }
    }

    if (core_fid.isNone()) {
        if (session.vfs.resolveOrCreatePath(session.io, "core/root.cx", .std_core)) |fid| {
            prefix_opt = try session.allocator.dupe(u8, "");
            core_path_opt = try session.allocator.dupe(u8, "core/root.cx");
            core_fid = fid;
        } else |_| {}
    }

    if (core_fid.isNone()) {
        if (std.process.executableDirPathAlloc(session.io, session.allocator)) |exe_dir| {
            defer session.allocator.free(exe_dir);
            const rel_parents = [_][]const u8{ "..", "../..", "../../.." };
            for (rel_parents) |rel_up| {
                const cand_prefix = try std.fmt.allocPrint(session.allocator, "{s}/{s}/", .{ exe_dir, rel_up });
                const cand_core = try std.fmt.allocPrint(session.allocator, "{s}core/root.cx", .{cand_prefix});
                if (session.vfs.resolveOrCreatePath(session.io, cand_core, .std_core)) |fid| {
                    prefix_opt = cand_prefix;
                    core_path_opt = cand_core;
                    core_fid = fid;
                    break;
                } else |_| {
                    session.allocator.free(cand_core);
                    session.allocator.free(cand_prefix);
                }
            }
        } else |_| {}
    }

    if (core_fid.isNone()) return;
    const active_prefix = prefix_opt.?;
    const chosen_core_path = core_path_opt.?;

    _ = session.vfs.getLineIndex(core_fid) catch {};
    try mountExternalSubmodulesShallow(
        session,
        core_fid,
        chosen_core_path,
        core_durability,
        .std_core,
        visited_fids,
        0,
    );
    try session.db.registerRootModule("core", core_fid);

    const cx_mod_path = try std.fmt.allocPrint(session.allocator, "{s}stdlib/cx/mod.cx", .{active_prefix});
    defer session.allocator.free(cx_mod_path);
    if (session.vfs.resolveOrCreatePath(session.io, cx_mod_path, .std_core)) |cx_fid| {
        _ = session.vfs.getLineIndex(cx_fid) catch {};
        try mountExternalSubmodulesShallow(
            session,
            cx_fid,
            cx_mod_path,
            core_durability,
            .std_core,
            visited_fids,
            0,
        );
        try session.db.registerCxStdlibPreludeRoot(cx_fid);
        _ = session.db.resolveSignatures(core_fid) catch {};
    } else |_| {
        try session.db.registerRootModule("cx", core_fid);
        _ = session.db.resolveSignatures(core_fid) catch {};
    }
}

/// Walks `<dir_path>` and mounts any additional `.cx` files at `Durability.medium` without typechecking bodies.
fn mountDirectoryCxFilesShallow(
    session: *LspSession,
    dir_path: []const u8,
    pkg_id: PackageId,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
) !void {
    var opened_dir = std.Io.Dir.cwd().openDir(session.io, dir_path, .{ .iterate = true }) catch return;
    defer opened_dir.close(session.io);

    var walker = opened_dir.walk(session.allocator) catch return;
    defer walker.deinit();

    while (walker.next(session.io) catch null) |entry| {
        if (entry.kind != .file or !std.mem.endsWith(u8, entry.path, ".cx")) continue;
        const full_cx = try std.fmt.allocPrint(
            session.allocator,
            "{s}/{s}",
            .{ std.mem.trimEnd(u8, dir_path, "/"), entry.path },
        );
        defer session.allocator.free(full_cx);
        for (full_cx) |*ch_ptr| {
            if (ch_ptr.* == '\\') ch_ptr.* = '/';
        }
        const fid = session.vfs.resolveOrCreatePath(session.io, full_cx, pkg_id) catch continue;
        try mountExternalSubmodulesShallow(session, fid, full_cx, .medium, pkg_id, visited_fids, 0);
    }
}

/// Mounts `corex.toml` + `corex.lock` (`.cxtree` at `.high`, workspace `.cx` at `.medium`) lazily on `initialize` / reload.
fn mountWorkspaceGraphLazy(session: *LspSession) !void {
    var visited_fids: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer visited_fids.deinit(session.allocator);

    try mountWorkspaceCoreStdlibLazy(session, &visited_fids);

    const ws_root = session.workspace_root_dir orelse return;
    session.db.setEmbedSandbox(ws_root, null);

    if (session.manifest_path == null) {
        session.manifest_path = try findNearestManifestToml(session.allocator, session.io, ws_root);
    }

    if (session.manifest_path) |toml_path| {
        var scratch_sink = DiagnosticSink.init(session.allocator);
        defer scratch_sink.deinit();

        if (session.vfs.resolveOrCreatePath(session.io, toml_path, .root)) |toml_fid| {
            _ = session.vfs.getLineIndex(toml_fid) catch {};
            const active_target = codegen_abi.TargetSpec.host();
            const cfg_env = symbol_resolver.CfgEnv.fromTargetSpec(active_target, true);
            if (pkg_manifest.loadWorkspaceManifestBundle(
                session.io,
                session.allocator,
                &session.db.interner,
                toml_path,
                toml_fid,
                &cfg_env,
                &scratch_sink,
            )) |loaded_bundle_val| {
                var manifest_bundle = loaded_bundle_val;
                defer manifest_bundle.deinit();

                session.lsp_config = manifest_bundle.root_manifest.lsp;
                session.last_manifest_blake3 = manifest_bundle.root_manifest_blake3;
                session.has_manifest_blake3 = true;
                try session.db.setPackageLintSemanticSettings(.root, manifest_bundle.root_manifest.lint.settings, null);
                try session.db.setPackageLintFilterConfig(
                    .root,
                    manifest_bundle.workspace_root_dir,
                    manifest_bundle.root_manifest.lint,
                    null,
                );

                const toml_dir = std.fs.path.dirname(toml_path) orelse ws_root;
                const lock_path = try std.fmt.allocPrint(
                    session.allocator,
                    "{s}/corex.lock",
                    .{std.mem.trimEnd(u8, toml_dir, "/")},
                );
                defer session.allocator.free(lock_path);

                var lock_arena = BumpArena.init(session.allocator);
                defer lock_arena.deinit();
                var existing_lock: ?pkg_manifest.Lockfile = null;
                if (std.Io.Dir.cwd().readFileAlloc(
                    session.io,
                    lock_path,
                    session.allocator,
                    .limited(pkg_manifest.MAX_TOML_BYTES),
                )) |lock_bytes| {
                    defer session.allocator.free(lock_bytes);
                    if (session.vfs.setEditorOverlay(session.io, lock_path, lock_bytes, .root, false)) |lock_fid| {
                        existing_lock = pkg_manifest.parseLockfile(
                            session.allocator,
                            &lock_arena,
                            &session.db.interner,
                            lock_fid,
                            lock_bytes,
                            null,
                            &scratch_sink,
                        ) catch null;
                    } else |_| {}
                } else |_| {}

                const corex_home = try resolveCorexHomeDir(session.allocator, session.environ_map);
                defer session.allocator.free(corex_home);

                if (pkg_resolver.resolveProjectGraph(
                    session.allocator,
                    &session.db.interner,
                    &session.vfs,
                    &manifest_bundle,
                    if (existing_lock) |*lck| lck else null,
                    .{
                        .io = session.io,
                        .target_spec = active_target,
                        .is_including_tests = true,
                        .is_offline = true,
                        .corex_home_dir = corex_home,
                        .environ_map = session.environ_map,
                    },
                    &scratch_sink,
                ) catch null) |resolved_val| {
                    var resolved = resolved_val;
                    defer resolved.deinit(session.allocator);

                    session.db.setPackageGraphMounted(true);
                    var cache = try pkg_cache.PkgCache.init(
                        session.allocator,
                        corex_home,
                        pkg_cache.DEFAULT_MAX_LRU_ENTRIES,
                        pkg_cache.DEFAULT_MAX_LRU_BYTES,
                    );
                    defer cache.deinit();
                    const blobs_dir = try std.fmt.allocPrint(session.allocator, "{s}/blobs", .{cache.cas_root});
                    defer session.allocator.free(blobs_dir);

                    var pkg_root_fids: std.AutoHashMapUnmanaged(PackageId, FileId) = .empty;
                    defer pkg_root_fids.deinit(session.allocator);

                    for (resolved.packages) |pkg_node| {
                        const ver_str = try pkg_node.version.formatAlloc(session.allocator, &session.db.interner);
                        defer session.allocator.free(ver_str);

                        const is_virtual_cxtree = (pkg_node.pkg_id != .root) and
                            (pkg_node.source_kind != .workspace_member) and
                            (pkg_node.source_kind != .local_path) and
                            (pkg_node.cxtree_blake3 != null);

                        var node_root_fid: FileId = .none;
                        if (is_virtual_cxtree) {
                            if (cache.readVerifiedCxTreeAlloc(
                                session.io,
                                pkg_node.cxtree_blake3.?,
                                &scratch_sink,
                                pkg_node.manifest_span,
                            )) |cxtree_bytes| {
                                defer session.allocator.free(cxtree_bytes);
                                const mounted_ids = try session.vfs.mountCxTreePackage(
                                    session.io,
                                    pkg_node.pkg_id,
                                    pkg_node.canonical_name,
                                    ver_str,
                                    cxtree_bytes,
                                    blobs_dir,
                                );
                                session.allocator.free(mounted_ids);

                                const entry_rel = pkg_node.lib_root_rel_path orelse
                                    pkg_node.bin_root_rel_path orelse "src/root.cx";
                                const entry_vpath = try std.fmt.allocPrint(
                                    session.allocator,
                                    "/cx/{s}@{s}/{s}",
                                    .{ pkg_node.canonical_name, ver_str, entry_rel },
                                );
                                defer session.allocator.free(entry_vpath);

                                if (session.vfs.interner.lookup(entry_vpath)) |vpath_id| {
                                    node_root_fid = session.vfs.path_to_file_id.get(vpath_id) orelse .none;
                                    if (!node_root_fid.isNone()) {
                                        try mountCxTreeSubmodulesShallow(
                                            session,
                                            node_root_fid,
                                            entry_vpath,
                                            pkg_node.pkg_id,
                                            &visited_fids,
                                            0,
                                        );
                                    }
                                }
                                const virtual_prefix = try std.fmt.allocPrint(
                                    session.allocator,
                                    "/cx/{s}@{s}",
                                    .{ pkg_node.canonical_name, ver_str },
                                );
                                defer session.allocator.free(virtual_prefix);
                                try session.db.setPackageEmbedJail(pkg_node.pkg_id, .{
                                    .cxtree_only = .{
                                        .pkg_id = pkg_node.pkg_id,
                                        .virtual_root_prefix = virtual_prefix,
                                    },
                                });
                            } else |_| {}
                        } else {
                            // Mount local root, workspace member, or path dependency at `Durability.medium`:
                            const disk_dur: Durability = if (pkg_node.pkg_id == .root) .medium else .high;
                            var entry_rels: [2]?[]const u8 = .{
                                pkg_node.lib_root_rel_path,
                                pkg_node.bin_root_rel_path,
                            };
                            if (entry_rels[0] == null and entry_rels[1] == null) {
                                entry_rels[0] = "src/root.cx";
                                entry_rels[1] = "src/main.cx";
                            }
                            for (entry_rels) |maybe_rel| {
                                const rel_p = maybe_rel orelse continue;
                                const joined_entry = try std.fmt.allocPrint(
                                    session.allocator,
                                    "{s}/{s}",
                                    .{ std.mem.trimEnd(u8, pkg_node.package_root_path, "/"), rel_p },
                                );
                                defer session.allocator.free(joined_entry);
                                for (joined_entry) |*ch_ptr| {
                                    if (ch_ptr.* == '\\') ch_ptr.* = '/';
                                }
                                if (session.vfs.resolveOrCreatePath(session.io, joined_entry, pkg_node.pkg_id)) |efid| {
                                    if (node_root_fid.isNone()) node_root_fid = efid;
                                    try mountExternalSubmodulesShallow(
                                        session,
                                        efid,
                                        joined_entry,
                                        disk_dur,
                                        pkg_node.pkg_id,
                                        &visited_fids,
                                        0,
                                    );
                                } else |_| {}
                            }
                            try session.db.setPackageEmbedJail(
                                pkg_node.pkg_id,
                                .{ .host_dir_jailed = pkg_node.package_root_path },
                            );
                        }

                        if (!node_root_fid.isNone()) {
                            try pkg_root_fids.put(session.allocator, pkg_node.pkg_id, node_root_fid);
                            try session.db.registerPackageRootFile(pkg_node.pkg_id, node_root_fid);
                            if (pkg_node.pkg_id == .root and pkg_node.default_snake_name.len > 0) {
                                try session.db.bindPackageDepFile(
                                    .root,
                                    try session.db.interner.intern(pkg_node.default_snake_name),
                                    node_root_fid,
                                );
                            }
                            try session.db.setPackageCfgFeatures(
                                pkg_node.pkg_id,
                                pkg_node.enabled_features,
                                if (pkg_node.has_feature_manifest) pkg_node.declared_features else null,
                            );
                            try session.db.setPackageCapPolicy(pkg_node.pkg_id, pkg_node.cap_policy);
                            try session.db.symbol_table.setPackageIdentityMeta(
                                &session.db.interner,
                                pkg_node.pkg_id,
                                pkg_node.canonical_name,
                                ver_str,
                                pkg_node.default_snake_name,
                                node_root_fid,
                            );
                            try session.db.symbol_table.markPackageDepsConfigured(pkg_node.pkg_id);
                            if (pkg_node.pkg_id == .root) {
                                var active_root_m: *const pkg_manifest.Manifest = &manifest_bundle.root_manifest;
                                if (active_root_m.package == null) {
                                    for (manifest_bundle.members) |*ws_mem| {
                                        if (ws_mem.manifest.package) |mem_pkg| {
                                            if (std.mem.eql(
                                                u8,
                                                session.db.interner.get(mem_pkg.name_kebab),
                                                pkg_node.canonical_name,
                                            )) {
                                                active_root_m = &ws_mem.manifest;
                                                break;
                                            }
                                        }
                                    }
                                }
                                session.lsp_config = active_root_m.lsp;
                                try session.db.setPackageLintSemanticSettings(.root, active_root_m.lint.settings, null);
                                try session.db.setPackageLintFilterConfig(
                                    .root,
                                    pkg_node.package_root_path,
                                    active_root_m.lint,
                                    null,
                                );
                            } else if (pkg_node.source_kind == .workspace_member) {
                                for (manifest_bundle.members) |*ws_mem| {
                                    if (ws_mem.manifest.package) |mem_pkg| {
                                        if (std.mem.eql(
                                            u8,
                                            session.db.interner.get(mem_pkg.name_kebab),
                                            pkg_node.canonical_name,
                                        )) {
                                            try session.db.setPackageLintSemanticSettings(
                                                pkg_node.pkg_id,
                                                ws_mem.manifest.lint.settings,
                                                null,
                                            );
                                            try session.db.setPackageLintFilterConfig(
                                                pkg_node.pkg_id,
                                                ws_mem.abs_dir,
                                                ws_mem.manifest.lint,
                                                null,
                                            );
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }

                    for (resolved.packages) |pkg_node| {
                        for (pkg_node.dependencies) |dep_bind| {
                            if (pkg_root_fids.get(dep_bind.target_pkg_id)) |target_fid| {
                                try session.db.bindPackageDepFile(
                                    pkg_node.pkg_id,
                                    try session.db.interner.intern(dep_bind.alias_text),
                                    target_fid,
                                );
                            }
                        }
                    }
                }
            } else |_| {}
        } else |_| {}
    }

    // Also scan `<workspace_root>/src` (and `<workspace_root>` top-level) for unopened `.cx` files at `.medium`:
    const ws_src_dir = try std.fmt.allocPrint(
        session.allocator,
        "{s}/src",
        .{std.mem.trimEnd(u8, ws_root, "/")},
    );
    defer session.allocator.free(ws_src_dir);
    try mountDirectoryCxFilesShallow(session, ws_src_dir, .root, &visited_fids);
}

// ------------ Lifecycle & Document Synchronization ------------

/// Handles `initialize`: negotiates UTF-8/UTF-16 & pull diagnostics, lazily mounts workspace, and writes capabilities.
fn handleInitializeRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    session.position_encoding = .utf16;
    session.is_pull_diagnostics_enabled = false;

    if (params.getField("capabilities")) |caps_obj| {
        if (caps_obj.getField("general")) |gen_obj| {
            if (gen_obj.getField("positionEncodings")) |enc_arr| {
                if (enc_arr == .array_val) {
                    for (enc_arr.array_val) |enc_item| {
                        if (enc_item == .string_val and std.ascii.eqlIgnoreCase(enc_item.string_val, "utf-8")) {
                            session.position_encoding = .utf8;
                            break;
                        }
                    }
                }
            }
        }
        if (caps_obj.getField("textDocument")) |td_obj| {
            if (td_obj.getField("diagnostic")) |diag_cap| {
                if (diag_cap != .null_val) {
                    session.is_pull_diagnostics_enabled = true;
                }
            }
        }
    }

    // Extract workspace root directory from `workspaceFolders[0].uri`, `rootUri`, or `rootPath`:
    var raw_root_uri: ?[]const u8 = null;
    if (params.getField("workspaceFolders")) |wf_val| {
        if (wf_val == .array_val and wf_val.array_val.len > 0) {
            raw_root_uri = wf_val.array_val[0].getStringField("uri");
        }
    }
    if (raw_root_uri == null) {
        raw_root_uri = params.getStringField("rootUri");
    }
    if (raw_root_uri) |uri_str| {
        if (uri_str.len > 0 and uri_str.len <= MAX_LSP_URI_BYTES) {
            if (session.workspace_root_dir) |old_ws| session.allocator.free(old_ws);
            session.workspace_root_dir = try decodeFileUriToNormalizedPath(session.allocator, uri_str);
        }
    } else if (params.getStringField("rootPath")) |root_path_str| {
        if (root_path_str.len > 0 and root_path_str.len <= MAX_LSP_URI_BYTES) {
            if (session.workspace_root_dir) |old_ws| session.allocator.free(old_ws);
            session.workspace_root_dir = try decodeFileUriToNormalizedPath(session.allocator, root_path_str);
        }
    }
    _ = arena_alloc;

    try mountWorkspaceGraphLazy(session);
    session.state = .initialized;

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":{\"capabilities\":{\"positionEncoding\":");
    try writeJsonString(body_writer, if (session.position_encoding == .utf8) "utf-8" else "utf-16");
    try body_writer.writeAll(",\"textDocumentSync\":{\"openClose\":true,\"change\":2,\"save\":{\"includeText\":true}}");
    try body_writer.writeAll(",\"diagnosticProvider\":{\"interFileDependencies\":true,\"workspaceDiagnostics\":false}");
    try body_writer.writeAll(",\"semanticTokensProvider\":{\"legend\":{\"tokenTypes\":[");
    for (SEMANTIC_TOKEN_TYPES, 0..) |tok_type_name, i| {
        if (i > 0) try body_writer.writeByte(',');
        try writeJsonString(body_writer, tok_type_name);
    }
    try body_writer.writeAll("],\"tokenModifiers\":[");
    for (SEMANTIC_TOKEN_MODIFIERS, 0..) |mod_name, i| {
        if (i > 0) try body_writer.writeByte(',');
        try writeJsonString(body_writer, mod_name);
    }
    try body_writer.writeAll("]},\"range\":true,\"full\":{\"delta\":true}}");
    try body_writer.writeAll(",\"hoverProvider\":true,\"definitionProvider\":true,\"typeDefinitionProvider\":true");
    try body_writer.writeAll(",\"referencesProvider\":true,\"documentHighlightProvider\":true");
    try body_writer.writeAll(",\"documentSymbolProvider\":true,\"workspaceSymbolProvider\":true");
    try body_writer.writeAll(",\"completionProvider\":{\"triggerCharacters\":[\".\",\"@\",\":\"],\"resolveProvider\":false}");
    try body_writer.writeAll(",\"signatureHelpProvider\":{\"triggerCharacters\":[\"(\",\",\",\"[\"],\"retriggerCharacters\":[\",\"]}");
    try body_writer.writeAll(",\"inlayHintProvider\":true");
    try body_writer.writeAll(",\"codeActionProvider\":{\"codeActionKinds\":[\"quickfix\"]}");
    try body_writer.writeAll(",\"codeLensProvider\":{\"resolveProvider\":false}");
    try body_writer.writeAll(",\"documentFormattingProvider\":true,\"documentRangeFormattingProvider\":true");
    try body_writer.writeAll(",\"renameProvider\":{\"prepareProvider\":true}}");
    try body_writer.writeAll(",\"serverInfo\":{\"name\":\"corex-lsp\",\"version\":\"0.1.0\"}}}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Looks up an already-mounted `FileId` for `norm_path` (`/`-normalized) via VFS caches or `resolvePath`.
fn lookupMountedFileId(session: *LspSession, norm_path: []const u8) ?FileId {
    if (session.vfs.interner.lookup(norm_path)) |direct_id| {
        if (session.vfs.path_to_file_id.get(direct_id)) |existing_fid| {
            return existing_fid;
        }
    }
    const resolved_id = session.vfs.resolvePath(session.io, norm_path) catch return null;
    return session.vfs.path_to_file_id.get(resolved_id);
}

/// Returns `true` when `norm_path` refers to a `corex.toml` manifest file.
fn isCorexTomlPath(norm_path: []const u8) bool {
    return std.mem.eql(u8, std.fs.path.basename(norm_path), "corex.toml");
}

/// Reloads `[lint]` / `[fmt]` / `[lsp]` from `toml_path` without tearing down `CompilerDb` when `BLAKE3` is unchanged.
fn reloadManifestToolingLive(
    session: *LspSession,
    toml_fid: FileId,
    toml_path: []const u8,
    live_text_opt: ?[]const u8,
) !void {
    if (session.manifest_path == null) {
        session.manifest_path = try session.allocator.dupe(u8, toml_path);
    }
    const toml_dir = std.fs.path.dirname(toml_path) orelse (session.workspace_root_dir orelse ".");
    const cfg_env = symbol_resolver.CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.host(), true);

    var toml_sink = DiagnosticSink.init(session.allocator);
    defer toml_sink.deinit();

    if (live_text_opt) |live_toml| {
        var toml_arena = BumpArena.init(session.allocator);
        defer toml_arena.deinit();
        if (pkg_manifest.parseManifest(
            session.allocator,
            &toml_arena,
            &session.db.interner,
            toml_fid,
            live_toml,
            &cfg_env,
            &toml_sink,
        )) |parsed_res| {
            var parsed_m = parsed_res;
            defer parsed_m.doc.deinit(session.allocator);
            probeWorkspaceStrayDotfilesCached(session, toml_dir, toml_fid, &toml_sink);
            if (!toml_sink.hasErrors()) {
                session.lsp_config = parsed_m.manifest.lsp;
                try session.db.setPackageLintSemanticSettings(.root, parsed_m.manifest.lint.settings, null);
                try session.db.setPackageLintFilterConfig(.root, toml_dir, parsed_m.manifest.lint, null);
                session.last_manifest_blake3 = parsed_m.manifest.root_manifest_blake3;
                session.has_manifest_blake3 = true;
            }
        } else |_| {}
    } else {
        if (pkg_manifest.loadWorkspaceManifestBundle(
            session.io,
            session.allocator,
            &session.db.interner,
            toml_path,
            toml_fid,
            &cfg_env,
            &toml_sink,
        )) |loaded_b| {
            var bundle = loaded_b;
            defer bundle.deinit();
            if (!toml_sink.hasErrors()) {
                if (session.has_manifest_blake3 and
                    std.mem.eql(u8, &bundle.root_manifest_blake3, &session.last_manifest_blake3))
                {
                    session.lsp_config = bundle.root_manifest.lsp;
                    try session.db.setPackageLintSemanticSettings(.root, bundle.root_manifest.lint.settings, null);
                    try session.db.setPackageLintFilterConfig(
                        .root,
                        bundle.workspace_root_dir,
                        bundle.root_manifest.lint,
                        null,
                    );
                } else {
                    try mountWorkspaceGraphLazy(session);
                }
            }
        } else |_| {}
    }

    if (!toml_fid.isNone() and session.isFileOpen(toml_fid)) {
        try queuePushDiagnostics(session, toml_fid);
    }
    var open_it = session.open_doc_versions.keyIterator();
    while (open_it.next()) |open_raw_ptr| {
        const open_fid = FileId.fromInt(open_raw_ptr.*);
        if (open_fid != toml_fid) {
            try queuePushDiagnostics(session, open_fid);
        }
    }
}

/// Resolves or mounts a document URI into `FileId`, returning `.none` if not found on disk or in VFS.
fn resolveDocumentFileId(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    raw_uri: []const u8,
) !FileId {
    if (raw_uri.len == 0 or raw_uri.len > MAX_LSP_URI_BYTES) return .none;
    const norm_path = try decodeFileUriToNormalizedPath(arena_alloc, raw_uri);
    if (lookupMountedFileId(session, norm_path)) |existing_fid| {
        return existing_fid;
    }
    if (session.vfs.resolveOrCreatePath(session.io, norm_path, .root)) |disk_fid| {
        _ = session.vfs.getLineIndex(disk_fid) catch {};
        if (std.mem.endsWith(u8, norm_path, ".cx")) {
            var visited: std.AutoHashMapUnmanaged(u32, void) = .empty;
            defer visited.deinit(session.allocator);
            try mountExternalSubmodulesShallow(session, disk_fid, norm_path, .medium, .root, &visited, 0);
        }
        return disk_fid;
    } else |_| {}
    return .none;
}

/// Enqueues `fid` onto `pending_push_diag_files` (deduplicated) when push diagnostics are active.
fn queuePushDiagnostics(session: *LspSession, fid: FileId) !void {
    if (session.is_pull_diagnostics_enabled) return;
    for (session.pending_push_diag_files.items) |queued_fid| {
        if (queued_fid == fid) return;
    }
    try session.pending_push_diag_files.append(session.allocator, fid);
}

/// Handles `textDocument/didOpen`: installs `Durability.low` overlay, binds submodules, and queues diagnostics.
fn handleDidOpenNotification(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
) !void {
    const raw_uri = extractValidatedNotificationUri(params) orelse return;
    const td_obj = params.getField("textDocument") orelse return;
    const doc_text = td_obj.getStringField("text") orelse "";
    const doc_version = td_obj.getIntField("version") orelse 0;

    const norm_path = try decodeFileUriToNormalizedPath(arena_alloc, raw_uri);
    var pkg_id: PackageId = .root;
    var overlay_path: []const u8 = norm_path;
    if (lookupMountedFileId(session, norm_path)) |existing_fid| {
        pkg_id = session.db.symbol_table.getFilePackageId(existing_fid);
        const existing_vpath = session.vfs.getFilePath(existing_fid);
        if (existing_vpath.len > 0) overlay_path = existing_vpath;
    }

    const fid = session.vfs.setEditorOverlay(session.io, overlay_path, doc_text, pkg_id, true) catch return;
    _ = session.vfs.getLineIndex(fid) catch {};
    try session.recordClientUri(fid, raw_uri);
    try session.open_doc_versions.put(session.allocator, fid.asInt(), doc_version);

    if (isCorexTomlPath(norm_path)) {
        try reloadManifestToolingLive(session, fid, norm_path, doc_text);
        return;
    }

    try session.recordMountedFile(fid);

    const effective_vpath = session.vfs.getFilePath(fid);
    const canonical_vpath = if (effective_vpath.len > 0) effective_vpath else overlay_path;
    _ = try session.db.setInput(fid, doc_text, .low);
    try session.db.setFilePath(fid, canonical_vpath);

    var visited: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer visited.deinit(session.allocator);
    try mountExternalSubmodulesShallow(session, fid, canonical_vpath, .low, pkg_id, &visited, 0);

    try queuePushDiagnostics(session, fid);
}

/// Applies one or more `TextDocumentContentChangeEvent` batches onto `fid` using `S_k` `LineIndex` + `coalesceEditRanges`.
fn handleDidChangeNotificationBatch(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    change_params_batch: []const JsonValue,
) !void {
    if (change_params_batch.len == 0) return;
    const raw_uri = extractValidatedNotificationUri(change_params_batch[0]) orelse return;
    const norm_path = try decodeFileUriToNormalizedPath(arena_alloc, raw_uri);
    const fid = lookupMountedFileId(session, norm_path) orelse return;
    const existing_vpath = session.vfs.getFilePath(fid);
    const overlay_path = if (existing_vpath.len > 0) existing_vpath else norm_path;
    const pkg_id = session.db.symbol_table.getFilePackageId(fid);

    var latest_version: ?i64 = null;
    var total_change_items: usize = 0;
    for (change_params_batch) |p_item| {
        if (p_item.getField("textDocument")) |td_item| {
            if (td_item.getIntField("version")) |ver_num| latest_version = ver_num;
        }
        if (p_item.getField("contentChanges")) |changes_arr| {
            if (changes_arr == .array_val) total_change_items += changes_arr.array_val.len;
        }
    }
    if (latest_version) |ver_num| {
        try session.open_doc_versions.put(session.allocator, fid.asInt(), ver_num);
    }
    if (total_change_items == 0) return;

    const initial_src = getLiveDocumentSource(session, fid) orelse "";
    const is_toml_doc = isCorexTomlPath(norm_path);

    // Fast path; single ranged edit uses the already-cached `vfs.getLineIndex(fid)` directly:
    if (change_params_batch.len == 1 and total_change_items == 1) {
        const single_change = change_params_batch[0].getField("contentChanges").?.array_val[0];
        const repl_text = single_change.getStringField("text") orelse return;
        if (single_change.getField("range")) |range_val| {
            if (extractJsonRange(range_val)) |lsp_range| {
                const line_idx = try session.vfs.getLineIndex(fid);
                const start_off = @min(
                    line_idx.resolveByteOffset(
                        initial_src,
                        lsp_range.start.line,
                        lsp_range.start.character,
                        session.position_encoding,
                    ),
                    initial_src.len,
                );
                const end_off = @max(
                    start_off,
                    @min(
                        line_idx.resolveByteOffset(
                            initial_src,
                            lsp_range.end.line,
                            lsp_range.end.character,
                            session.position_encoding,
                        ),
                        initial_src.len,
                    ),
                );
                const new_len = start_off + repl_text.len + (initial_src.len - end_off);
                if (new_len > vfs_sourcemap.MAX_OPEN_OVERLAY_BYTES) return;
                const spliced = try arena_alloc.alloc(u8, new_len);
                @memcpy(spliced[0..start_off], initial_src[0..start_off]);
                @memcpy(spliced[start_off .. start_off + repl_text.len], repl_text);
                @memcpy(spliced[start_off + repl_text.len ..], initial_src[end_off..]);

                const edit_range = parser.EditRange{
                    .start_byte = @intCast(start_off),
                    .old_end_byte = @intCast(end_off),
                    .new_end_byte = @intCast(start_off + repl_text.len),
                };
                _ = session.vfs.setEditorOverlay(session.io, overlay_path, spliced, pkg_id, true) catch return;
                _ = session.vfs.getLineIndex(fid) catch {};
                if (is_toml_doc) {
                    try reloadManifestToolingLive(session, fid, norm_path, spliced);
                    return;
                }
                _ = try session.db.setInputWithEdit(fid, spliced, .low, edit_range);
                try queuePushDiagnostics(session, fid);
                return;
            }
        }
        // Single full-document sync (`range == null`):
        if (repl_text.len > vfs_sourcemap.MAX_OPEN_OVERLAY_BYTES) return;
        _ = session.vfs.setEditorOverlay(session.io, overlay_path, repl_text, pkg_id, true) catch return;
        _ = session.vfs.getLineIndex(fid) catch {};
        if (is_toml_doc) {
            try reloadManifestToolingLive(session, fid, norm_path, repl_text);
            return;
        }
        _ = try session.db.setInput(fid, repl_text, .low);
        try queuePushDiagnostics(session, fid);
        return;
    }

    // Multi-change / coalesced-batch path; `contentChanges[k].range` is relative to intermediate `S_k`:
    var working_src: []const u8 = initial_src;
    var folded_edit: ?parser.EditRange = null;
    var has_full_sync = false;

    for (change_params_batch) |batch_param| {
        const changes_val = batch_param.getField("contentChanges") orelse continue;
        if (changes_val != .array_val) continue;
        for (changes_val.array_val) |change_obj| {
            const repl_text = change_obj.getStringField("text") orelse continue;
            if (change_obj.getField("range")) |range_val| {
                if (extractJsonRange(range_val)) |lsp_range| {
                    var step_line_idx = try LineIndex.build(session.allocator, working_src);
                    defer step_line_idx.deinit(session.allocator);

                    const start_off = @min(
                        step_line_idx.resolveByteOffset(
                            working_src,
                            lsp_range.start.line,
                            lsp_range.start.character,
                            session.position_encoding,
                        ),
                        working_src.len,
                    );
                    const end_off = @max(
                        start_off,
                        @min(
                            step_line_idx.resolveByteOffset(
                                working_src,
                                lsp_range.end.line,
                                lsp_range.end.character,
                                session.position_encoding,
                            ),
                            working_src.len,
                        ),
                    );
                    const next_len = start_off + repl_text.len + (working_src.len - end_off);
                    if (next_len > vfs_sourcemap.MAX_OPEN_OVERLAY_BYTES) return;
                    const next_buf = try arena_alloc.alloc(u8, next_len);
                    @memcpy(next_buf[0..start_off], working_src[0..start_off]);
                    @memcpy(next_buf[start_off .. start_off + repl_text.len], repl_text);
                    @memcpy(next_buf[start_off + repl_text.len ..], working_src[end_off..]);
                    working_src = next_buf;

                    const step_edit = parser.EditRange{
                        .start_byte = @intCast(start_off),
                        .old_end_byte = @intCast(end_off),
                        .new_end_byte = @intCast(start_off + repl_text.len),
                    };
                    if (!has_full_sync) {
                        if (folded_edit) |prev_edit| {
                            if (query_db.coalesceEditRanges(prev_edit, step_edit)) |merged_edit| {
                                folded_edit = merged_edit;
                            } else {
                                has_full_sync = true;
                                folded_edit = null;
                            }
                        } else {
                            folded_edit = step_edit;
                        }
                    }
                    continue;
                }
            }
            // Full-content replacement entry:
            if (repl_text.len > vfs_sourcemap.MAX_OPEN_OVERLAY_BYTES) return;
            working_src = repl_text;
            has_full_sync = true;
            folded_edit = null;
        }
    }

    _ = session.vfs.setEditorOverlay(session.io, overlay_path, working_src, pkg_id, true) catch return;
    _ = session.vfs.getLineIndex(fid) catch {};
    if (is_toml_doc) {
        try reloadManifestToolingLive(session, fid, norm_path, working_src);
        return;
    }
    if (!has_full_sync and folded_edit != null) {
        _ = try session.db.setInputWithEdit(fid, working_src, .low, folded_edit.?);
    } else {
        _ = try session.db.setInput(fid, working_src, .low);
    }
    try queuePushDiagnostics(session, fid);
}

/// Handles `textDocument/didSave`: syncs optional `text`, binds new submodules, and queues diagnostics.
fn handleDidSaveNotification(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
) !void {
    const raw_uri = extractValidatedNotificationUri(params) orelse return;
    const norm_path = try decodeFileUriToNormalizedPath(arena_alloc, raw_uri);
    const fid = lookupMountedFileId(session, norm_path) orelse return;
    const existing_vpath = session.vfs.getFilePath(fid);
    const overlay_path = if (existing_vpath.len > 0) existing_vpath else norm_path;
    const pkg_id = session.db.symbol_table.getFilePackageId(fid);

    if (isCorexTomlPath(norm_path)) {
        if (params.getStringField("text")) |saved_toml| {
            if (saved_toml.len <= vfs_sourcemap.MAX_OPEN_OVERLAY_BYTES) {
                _ = session.vfs.setEditorOverlay(session.io, overlay_path, saved_toml, pkg_id, true) catch return;
                _ = session.vfs.getLineIndex(fid) catch {};
                try reloadManifestToolingLive(session, fid, norm_path, saved_toml);
                return;
            }
        }
        try reloadManifestToolingLive(session, fid, norm_path, null);
        return;
    }

    if (params.getStringField("text")) |saved_text| {
        const cur_src = getLiveDocumentSource(session, fid) orelse "";
        if (!std.mem.eql(u8, cur_src, saved_text) and saved_text.len <= vfs_sourcemap.MAX_OPEN_OVERLAY_BYTES) {
            _ = session.vfs.setEditorOverlay(session.io, overlay_path, saved_text, pkg_id, true) catch return;
            _ = try session.db.setInput(fid, saved_text, .low);
        }
    }

    var visited: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer visited.deinit(session.allocator);
    try mountExternalSubmodulesShallow(session, fid, overlay_path, .low, pkg_id, &visited, 0);

    try queuePushDiagnostics(session, fid);
}

/// Handles `textDocument/didClose`: reverts overlay to disk (`Durability.medium`) or clears virtual squiggles.
fn handleDidCloseNotification(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
) !void {
    const raw_uri = extractValidatedNotificationUri(params) orelse return;
    const norm_path = try decodeFileUriToNormalizedPath(arena_alloc, raw_uri);
    const fid = lookupMountedFileId(session, norm_path) orelse return;
    const pkg_id = session.db.symbol_table.getFilePackageId(fid);

    _ = session.open_doc_versions.remove(fid.asInt());
    {
        var q_idx: usize = 0;
        while (q_idx < session.pending_push_diag_files.items.len) {
            if (session.pending_push_diag_files.items[q_idx] == fid) {
                _ = session.pending_push_diag_files.orderedRemove(q_idx);
            } else {
                q_idx += 1;
            }
        }
    }

    if (session.vfs.closeOverlay(session.io, fid) catch false) {
        const disk_src = session.vfs.getFileSource(fid) orelse "";
        const demoted_dur: Durability = if (pkg_id == .root) .medium else .high;
        _ = try session.db.setInput(fid, disk_src, demoted_dur);
    } else {
        session.semantic_tokens_cache.removeFile(fid);
        _ = try session.db.setInput(fid, "", .medium);
    }
    if (!session.is_pull_diagnostics_enabled) {
        session.outbound_buf.clearRetainingCapacity();
        const body_writer = &session.outbound_buf.writer;
        try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":");
        try writeJsonString(body_writer, raw_uri);
        try body_writer.writeAll(",\"diagnostics\":[]}}");
        try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
    }

    session.removeClientUri(fid);
}

/// Probes `toml_dir` for forbidden stray tool dotfiles, caching clean negative results across live edits.
fn probeWorkspaceStrayDotfilesCached(
    session: *LspSession,
    toml_dir: []const u8,
    file_id: FileId,
    sink: *DiagnosticSink,
) void {
    if (session.cached_stray_dotfile_dir) |cached_dir| {
        if (std.mem.eql(u8, cached_dir, toml_dir)) {
            if (session.cached_has_stray_dotfiles) {
                _ = pkg_manifest.checkStrayToolConfigDotfiles(session.io, toml_dir, file_id, sink) catch false;
            }
            return;
        }
        session.allocator.free(cached_dir);
        session.cached_stray_dotfile_dir = null;
    }
    const found = pkg_manifest.checkStrayToolConfigDotfiles(session.io, toml_dir, file_id, sink) catch false;
    session.cached_stray_dotfile_dir = session.allocator.dupe(u8, toml_dir) catch null;
    session.cached_has_stray_dotfiles = found;
}

/// Handles `workspace/didChangeWatchedFiles`: reloads `corex.toml`/`corex.lock` and unopened disk `.cx` files.
fn handleDidChangeWatchedFilesNotification(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
) !void {
    const changes_val = params.getField("changes") orelse return;
    if (changes_val != .array_val) return;

    var has_manifest_change = false;
    if (session.cached_stray_dotfile_dir) |dot_dir| {
        session.allocator.free(dot_dir);
        session.cached_stray_dotfile_dir = null;
    }
    session.cached_has_stray_dotfiles = false;
    for (changes_val.array_val) |ev_obj| {
        const raw_uri = ev_obj.getStringField("uri") orelse continue;
        if (raw_uri.len == 0 or raw_uri.len > MAX_LSP_URI_BYTES) continue;
        const change_kind = ev_obj.getIntField("type") orelse 2;
        const norm_path = try decodeFileUriToNormalizedPath(arena_alloc, raw_uri);
        const base_name = std.fs.path.basename(norm_path);

        if (std.mem.eql(u8, base_name, "corex.toml") or std.mem.eql(u8, base_name, "corex.lock")) {
            has_manifest_change = true;
            continue;
        }
        if (!std.mem.endsWith(u8, norm_path, ".cx")) continue;

        const existing_fid_opt = lookupMountedFileId(session, norm_path);
        if (existing_fid_opt) |existing_fid| {
            if (session.isFileOpen(existing_fid)) continue;
            if (change_kind == 3) {
                _ = try session.db.setInput(existing_fid, "", .medium);
                continue;
            }
        }
        if (change_kind != 3) {
            if (std.Io.Dir.cwd().readFileAlloc(
                session.io,
                norm_path,
                arena_alloc,
                .limited(vfs_sourcemap.MAX_SOURCE_FILE_BYTES),
            )) |disk_bytes| {
                var pkg_id: PackageId = .root;
                var overlay_path: []const u8 = norm_path;
                if (existing_fid_opt) |existing_fid| {
                    pkg_id = session.db.symbol_table.getFilePackageId(existing_fid);
                    const existing_vpath = session.vfs.getFilePath(existing_fid);
                    if (existing_vpath.len > 0) overlay_path = existing_vpath;
                }
                const fid = try session.vfs.setEditorOverlay(
                    session.io,
                    overlay_path,
                    disk_bytes,
                    pkg_id,
                    false,
                );
                _ = session.vfs.getLineIndex(fid) catch {};
                try session.recordMountedFile(fid);
                const dur: Durability = if (pkg_id == .root) .medium else .high;
                _ = try session.db.setInput(fid, disk_bytes, dur);
            } else |_| {}
        }
    }

    if (has_manifest_change) {
        if (session.manifest_path) |m_path| {
            const m_fid = session.vfs.resolveOrCreatePath(session.io, m_path, .root) catch .none;
            if (!m_fid.isNone()) {
                if (std.Io.Dir.cwd().readFileAlloc(
                    session.io,
                    m_path,
                    arena_alloc,
                    .limited(pkg_manifest.MAX_TOML_BYTES),
                )) |disk_toml| {
                    _ = session.vfs.setEditorOverlay(
                        session.io,
                        m_path,
                        disk_toml,
                        .root,
                        session.isFileOpen(m_fid),
                    ) catch {};
                    _ = session.vfs.getLineIndex(m_fid) catch {};
                } else |_| {}
                try reloadManifestToolingLive(session, m_fid, m_path, null);
                return;
            }
        }
        try mountWorkspaceGraphLazy(session);
        var open_it = session.open_doc_versions.keyIterator();
        while (open_it.next()) |open_raw_ptr| {
            try queuePushDiagnostics(session, FileId.fromInt(open_raw_ptr.*));
        }
    }
}

// --------- Push & Pull Diagnostics (LSP 3.17 + E0220) ---------

/// Appends diagnostics from `sink` targeting `file_id` into `out_list` with deduplication (`0` DB queries while reading `sink`).
fn appendFileDiagnosticsDedup(
    arena_alloc: std.mem.Allocator,
    file_id: FileId,
    sink: *const DiagnosticSink,
    seen_keys: *std.StringHashMapUnmanaged(void),
    out_list: *std.ArrayListUnmanaged(CollectedDiagnostic),
) !void {
    for (sink.diagnostics.items) |diag_item| {
        const span_fid = diag_item.primary_span.file_id;
        if (!span_fid.isNone() and span_fid != file_id) continue;

        const dedup_key = try std.fmt.allocPrint(
            arena_alloc,
            "{d}:{d}:{d}:{s}",
            .{
                @backingInt(diag_item.code),
                diag_item.primary_span.start_byte,
                diag_item.primary_span.end_byte,
                diag_item.message,
            },
        );
        if ((try seen_keys.getOrPut(arena_alloc, dedup_key)).found_existing) continue;

        try out_list.append(arena_alloc, .{
            .diag = diag_item,
            .extra_bang_fix = null,
        });
    }
}

/// Collects all syntax, signature, body typecheck, SAST/MIR, `comptime`, and projected lint diagnostics for `file_id`.
fn collectFileDiagnostics(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    file_id: FileId,
) ![]const CollectedDiagnostic {
    var collected: std.ArrayListUnmanaged(CollectedDiagnostic) = .empty;
    var seen_keys: std.StringHashMapUnmanaged(void) = .empty;

    const vfs_path = session.vfs.getFilePath(file_id);
    if (isCorexTomlPath(vfs_path)) {
        const toml_src = getLiveDocumentSource(session, file_id) orelse "";
        const toml_dir = std.fs.path.dirname(vfs_path) orelse (session.workspace_root_dir orelse ".");
        const cfg_env = symbol_resolver.CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.host(), true);
        var toml_arena = BumpArena.init(arena_alloc);
        var toml_sink = DiagnosticSink.init(arena_alloc);
        if (pkg_manifest.parseManifest(
            arena_alloc,
            &toml_arena,
            &session.db.interner,
            file_id,
            toml_src,
            &cfg_env,
            &toml_sink,
        )) |parsed_toml| {
            var tmp_doc = parsed_toml.doc;
            tmp_doc.deinit(arena_alloc);
        } else |_| {}
        probeWorkspaceStrayDotfilesCached(session, toml_dir, file_id, &toml_sink);
        for (toml_sink.diagnostics.items) |diag_item| {
            const cloned_msg = try arena_alloc.dupe(u8, diag_item.message);
            var cloned_diag = diag_item;
            cloned_diag.message = cloned_msg;
            if (cloned_diag.primary_span.file_id.isNone()) {
                cloned_diag.primary_span.file_id = file_id;
            }
            try collected.append(arena_alloc, .{ .diag = cloned_diag });
        }
        return collected.items;
    }

    // [1] Run leaf `projectFileDiagnostics` (`parseCst`, `resolveSignatures`, `typecheckBody`, `verifySastMir`, & lint filter):
    _ = try session.db.projectFileDiagnostics(file_id);
    const entries = try arena_alloc.dupe(
        query_db.ItemTreeEntry,
        (try session.db.extractItemTree(file_id)).entries,
    );

    // Run `evalComptimeDef` on `.const_decl` / `.extern_block` items when free of upstream errors:
    const has_proj_errors = if (session.db.projected_file_diagnostics.getPtr(file_id.asInt())) |proj_ptr|
        proj_ptr.hasErrors()
    else
        false;
    if (!has_proj_errors) {
        for (entries) |entry| {
            try session.db.unwindIfCanceled();
            if (entry.kind == .const_decl or entry.kind == .extern_block) {
                _ = session.db.evalComptimeDef(entry.def_id) catch |ct_err| switch (ct_err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.Canceled => return error.Canceled,
                    else => {},
                };
            }
        }
    }

    // Pre-resolve any `E0220` retired-bang fixes before borrowing `*const DiagnosticSink` pointers:
    var pending_bang_spans: std.ArrayListUnmanaged(Span) = .empty;
    if (session.db.projected_file_diagnostics.getPtr(file_id.asInt())) |proj_ptr| {
        for (proj_ptr.diagnostics.items) |diag_item| {
            if (diag_item.code == .e0220_retired_bang_prefix and diag_item.suggestions.len == 0) {
                try pending_bang_spans.append(arena_alloc, diag_item.primary_span);
            }
        }
    }
    for (pending_bang_spans.items) |bang_span| {
        _ = try session.db.resolveBangFixSuggestion(file_id, bang_span);
    }

    // [2] Read projected file sink + `comptime` sinks fresh from quiescent `CompilerDb` maps:
    if (session.db.projected_file_diagnostics.getPtr(file_id.asInt())) |proj_ptr| {
        try appendFileDiagnosticsDedup(arena_alloc, file_id, proj_ptr, &seen_keys, &collected);
    }
    for (entries) |entry| {
        if (entry.kind == .const_decl or entry.kind == .extern_block) {
            if (session.db.getComptimeDiagnostics(entry.def_id)) |ct_sink| {
                try appendFileDiagnosticsDedup(arena_alloc, file_id, ct_sink, &seen_keys, &collected);
            }
        }
    }

    // [3] Post-resolve any remaining `E0220` bang fixes after all `DiagnosticSink` borrows have ended:
    for (collected.items) |*collected_item| {
        if (collected_item.diag.code == .e0220_retired_bang_prefix and collected_item.diag.suggestions.len == 0) {
            collected_item.extra_bang_fix = try session.db.resolveBangFixSuggestion(
                file_id,
                collected_item.diag.primary_span,
            );
        }
    }
    return collected.items;
}

/// Maps `DiagnosticCode` to optional LSP 3.17 `DiagnosticTag` (`1 = Unnecessary`, `2 = Deprecated`, `DR-25` §3.4).
fn classifyLspDiagnosticTag(code: DiagnosticCode) ?u8 {
    if (code.asLintRuleId()) |rule_id| {
        if (code == .w0403_deprecated_symbol) return 2;
        if (rule_id.asMeta().is_unnecessary_tag) return 1;
        return null;
    }
    return switch (code) {
        .w0401_unreachable_pattern_arm,
        .w0402_unused_binding,
        .w0308_unused_region_allocation,
        => 1,
        .w0403_deprecated_symbol,
        .w0001_deprecated_cli_option,
        => 2,
        else => null,
    };
}

/// Writes a single LSP 3.17 `Diagnostic` JSON object (including `"W0xxx/slug"`, `tags`, and `relatedInformation`).
fn writeSingleLspDiagnosticJson(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    file_id: FileId,
    diag_item: Diagnostic,
    writer: *std.Io.Writer,
) !void {
    const primary_range = spanToLspRange(session, file_id, diag_item.primary_span);
    const maybe_lint_rule = diag_item.code.asLintRuleId();
    const lsp_severity: u8 = if (maybe_lint_rule != null)
        2
    else switch (diag_item.severity) {
        .err => 1,
        .warning => 2,
        .note => 3,
        .help => 4,
    };

    var code_buf: [80]u8 = undefined;
    const lsp_code_str: []const u8 = if (maybe_lint_rule) |rule_id|
        (std.fmt.bufPrint(&code_buf, "{s}/{s}", .{ diag_item.code.asCodeStr(), rule_id.asSlug() }) catch
            diag_item.code.asCodeStr())
    else
        diag_item.code.asCodeStr();

    try writer.writeAll("{\"range\":");
    try writeLspRangeJson(writer, primary_range);
    try writer.print(",\"severity\":{d},\"code\":", .{lsp_severity});
    try writeJsonString(writer, lsp_code_str);
    try writer.writeAll(",\"source\":\"corex\",\"message\":");

    if (diag_item.notes.len == 0) {
        try writeJsonString(writer, diag_item.message);
    } else {
        var full_msg: std.ArrayListUnmanaged(u8) = .empty;
        try full_msg.appendSlice(arena_alloc, diag_item.message);
        for (diag_item.notes) |note_line| {
            if (std.mem.startsWith(u8, note_line, "help:") or std.mem.startsWith(u8, note_line, "note:")) {
                try full_msg.appendSlice(arena_alloc, "\n");
            } else {
                try full_msg.appendSlice(arena_alloc, "\n• ");
            }
            try full_msg.appendSlice(arena_alloc, note_line);
        }
        try writeJsonString(writer, full_msg.items);
    }

    if (classifyLspDiagnosticTag(diag_item.code)) |tag_num| {
        try writer.print(",\"tags\":[{d}]", .{tag_num});
    }

    if (diag_item.labels.len > 0) {
        try writer.writeAll(",\"relatedInformation\":[");
        var emitted_rel: usize = 0;
        for (diag_item.labels) |lbl| {
            if (lbl.label.len == 0) continue;
            const rel_fid = if (!lbl.span.file_id.isNone()) lbl.span.file_id else file_id;
            const rel_span = Span.init(rel_fid, lbl.span.start_byte, lbl.span.end_byte);
            if (emitted_rel > 0) try writer.writeByte(',');
            try writer.writeAll("{\"location\":");
            try writeLspLocationJson(session, arena_alloc, writer, rel_span);
            try writer.writeAll(",\"message\":");
            try writeJsonString(writer, lbl.label);
            try writer.writeByte('}');
            emitted_rel += 1;
        }
        try writer.writeByte(']');
    }
    try writer.writeByte('}');
}

/// Pushes a `textDocument/publishDiagnostics` notification for `file_id` onto `out_writer`.
fn publishDiagnosticsNotification(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    file_id: FileId,
    out_writer: *std.Io.Writer,
) !void {
    session.db.clearCancellation();
    const collected = collectFileDiagnostics(session, arena_alloc, file_id) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return,
    };
    const uri_str = try resolveOutboundUri(session, arena_alloc, file_id);

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":");
    try writeJsonString(body_writer, uri_str);
    if (session.open_doc_versions.get(file_id.asInt())) |doc_ver| {
        try body_writer.print(",\"version\":{d}", .{doc_ver});
    }
    try body_writer.writeAll(",\"diagnostics\":[");
    for (collected, 0..) |entry, i| {
        if (i > 0) try body_writer.writeByte(',');
        try writeSingleLspDiagnosticJson(session, arena_alloc, file_id, entry.diag, body_writer);
    }
    try body_writer.writeAll("]}}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Handles `textDocument/diagnostic` pull diagnostics with 32-hex `Fingerprint128` `"unchanged"` caching.
fn handlePullDiagnosticRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const prev_result_id = params.getStringField("previousResultId");

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) {
        session.outbound_buf.clearRetainingCapacity();
        const body_writer = &session.outbound_buf.writer;
        try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
        try writeJsonRpcId(body_writer, rpc_id);
        try body_writer.writeAll(",\"result\":{\"kind\":\"full\",\"items\":[]}}");
        return flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
    }

    const collected = try collectFileDiagnostics(session, arena_alloc, fid);
    var items_alloc_writer = std.Io.Writer.Allocating.init(arena_alloc);
    const items_writer = &items_alloc_writer.writer;
    try items_writer.writeByte('[');
    for (collected, 0..) |entry, i| {
        if (i > 0) try items_writer.writeByte(',');
        try writeSingleLspDiagnosticJson(session, arena_alloc, fid, entry.diag, items_writer);
    }
    try items_writer.writeByte(']');
    const items_json = items_alloc_writer.written();

    const digest = Fingerprint128.hashBytes(items_json);
    var hex_result_id: [32]u8 = undefined;
    _ = std.fmt.bufPrint(&hex_result_id, "{x:0>16}{x:0>16}", .{ digest.high, digest.low }) catch unreachable;

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    if (prev_result_id != null and std.mem.eql(u8, prev_result_id.?, &hex_result_id)) {
        try body_writer.writeAll(",\"result\":{\"kind\":\"unchanged\",\"resultId\":");
        try writeJsonString(body_writer, &hex_result_id);
        try body_writer.writeAll("}}");
    } else {
        try body_writer.writeAll(",\"result\":{\"kind\":\"full\",\"resultId\":");
        try writeJsonString(body_writer, &hex_result_id);
        try body_writer.writeAll(",\"items\":");
        try body_writer.writeAll(items_json);
        try body_writer.writeAll("}}");
    }
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

// ----------- Semantic Tokens (Full, Delta & Range) ------------

/// Compares `RawSemanticToken` items strictly by `(line_0 ASC, start_char_0 ASC)`.
fn isSemanticTokenBefore(_: void, lhs_tok: RawSemanticToken, rhs_tok: RawSemanticToken) bool {
    if (lhs_tok.line_0 != rhs_tok.line_0) return lhs_tok.line_0 < rhs_tok.line_0;
    return lhs_tok.start_char_0 < rhs_tok.start_char_0;
}

/// Splits a source byte span `[start_byte .. end_byte]` per line and appends `RawSemanticToken` segments.
fn appendSplitSemanticSpan(
    arena_alloc: std.mem.Allocator,
    src: []const u8,
    line_idx: *const LineIndex,
    encoding: PositionEncoding,
    start_byte: u32,
    end_byte: u32,
    token_type: u32,
    modifiers: u32,
    range_filter: ?LspRange,
    out_tokens: *std.ArrayListUnmanaged(RawSemanticToken),
) !void {
    if (end_byte <= start_byte or start_byte >= src.len) return;
    const clamped_end: usize = @min(@as(usize, end_byte), src.len);
    var seg_start: usize = start_byte;

    while (seg_start < clamped_end) {
        var seg_end = seg_start;
        while (seg_end < clamped_end and src[seg_end] != '\n' and src[seg_end] != '\r') : (seg_end += 1) {}
        if (seg_end > seg_start) {
            const start_lc = line_idx.resolveLineCol(src, @intCast(seg_start));
            const end_lc = line_idx.resolveLineCol(src, @intCast(seg_end));
            const line_0 = start_lc.line -| 1;
            const char_start = LineIndex.extractLspCharacter0(start_lc, encoding);
            const char_end = LineIndex.extractLspCharacter0(end_lc, encoding);
            if (char_end > char_start) {
                var is_in_range = true;
                if (range_filter) |flt| {
                    if (line_0 < flt.start.line or line_0 > flt.end.line) is_in_range = false;
                }
                if (is_in_range) {
                    try out_tokens.append(arena_alloc, .{
                        .line_0 = line_0,
                        .start_char_0 = char_start,
                        .length = char_end - char_start,
                        .token_type = token_type,
                        .modifiers = modifiers,
                    });
                }
            }
        }
        if (seg_end < clamped_end and src[seg_end] == '\r') seg_end += 1;
        if (seg_end < clamped_end and src[seg_end] == '\n') seg_end += 1;
        seg_start = seg_end;
    }
}

/// Maps a resolved `SymbolRecord` to `(semantic_token_type, semantic_modifier_bits)`.
fn classifySymbolSemanticStyle(
    session: *LspSession,
    sym_idx: SymbolIndex,
    is_decl_site: bool,
) struct { tok_type: u32, mod_bits: u32 } {
    const sym = session.db.symbol_table.getSymbol(sym_idx).*;
    var mods: u32 = if (is_decl_site) (SEM_MOD_DECLARATION | SEM_MOD_DEFINITION) else 0;
    const is_local_or_param = (sym.kind == .local_let_sym or
        sym.kind == .local_var_sym or
        sym.kind == .param_sym);
    if (!is_local_or_param and
        (sym.flags.is_builtin or session.db.symbol_table.getFilePackageId(sym.decl_span.file_id) == .std_core))
    {
        mods |= SEM_MOD_DEFAULT_LIB;
    }
    if (sym.extra_flags.is_deprecated or session.db.symbol_table.getDeprecatedMeta(sym_idx) != null) {
        mods |= SEM_MOD_DEPRECATED;
    }
    if (sym.contract_flags.is_linear or
        (!sym.type_id.isPrimitiveOrSentinel() and
            type_system.classifyOwnershipTier(&session.db.type_pool, &session.db.symbol_table, sym.type_id) == .linear_tier))
    {
        mods |= SEM_MOD_LINEAR;
    }

    const tok_type: u32 = switch (sym.kind) {
        .module_sym => SEM_TOK_NAMESPACE,
        .struct_sym, .union_sym, .bit_field_sym => SEM_TOK_STRUCT,
        .enum_sym => SEM_TOK_ENUM,
        .trait_sym, .type_group_sym => SEM_TOK_INTERFACE,
        .type_alias_sym, .distinct_type_sym, .refined_type_sym => SEM_TOK_TYPE,
        .type_param_sym => SEM_TOK_TYPE_PARAM,
        .param_sym => blk: {
            if (sym.flags.is_mut) mods |= SEM_MOD_MUTABLE;
            break :blk SEM_TOK_PARAMETER;
        },
        .local_let_sym => SEM_TOK_VARIABLE,
        .local_var_sym => blk: {
            mods |= SEM_MOD_MUTABLE;
            break :blk SEM_TOK_VARIABLE;
        },
        .const_sym, .const_param_sym => blk: {
            mods |= SEM_MOD_READONLY | SEM_MOD_STATIC;
            break :blk SEM_TOK_VARIABLE;
        },
        .field_sym => SEM_TOK_PROPERTY,
        .enum_variant_sym => SEM_TOK_ENUM_MEMBER,
        .extern_static_sym => blk: {
            mods |= SEM_MOD_STATIC | SEM_MOD_UNSAFE;
            break :blk SEM_TOK_VARIABLE;
        },
        .fn_sym, .overload_group_sym => blk: {
            if (!sym.type_id.isPrimitiveOrSentinel()) {
                if (session.db.type_pool.getFnSignatureView(sym.type_id)) |sig_v| {
                    if (sig_v.is_async) mods |= SEM_MOD_ASYNC;
                }
            }
            if (sym.flags.is_extern) mods |= SEM_MOD_UNSAFE;
            if (!sym.def_id.isNone()) {
                if (session.db.getSastSummary(sym.def_id)) |sum| {
                    const sum_eff = sum.inferredEffects();
                    if (sum_eff.unsafe_op or sum_eff.ffi) mods |= SEM_MOD_UNSAFE;
                }
            }
            const is_method = !sym.scope_id.isNone() and
                sym.scope_id.asInt() < session.db.symbol_table.scope_arena.countScopes() and
                switch (session.db.symbol_table.scope_arena.getScope(sym.scope_id).kind) {
                    .nominal_type_scope, .trait_scope, .impl_scope => true,
                    else => false,
                };
            break :blk if (is_method) SEM_TOK_METHOD else SEM_TOK_FUNCTION;
        },
        .use_alias_sym => blk: {
            const unwrapped = session.db.symbol_table.unwrapAliasSymbolIdx(sym_idx);
            if (unwrapped != sym_idx and !unwrapped.isNone()) {
                return classifySymbolSemanticStyle(session, unwrapped, is_decl_site);
            }
            break :blk SEM_TOK_VARIABLE;
        },
    };
    return .{ .tok_type = tok_type, .mod_bits = mods };
}

/// Resolves the identifier `TokenIndex` representing `ast_id` (unwrapping `.` on variants/members and `@` on intrinsics).
fn resolveAstNodeFocalToken(
    parsed_art: *const query_db.ParsedCstArtifact,
    ast_id: NodeIndex,
) TokenIndex {
    const ast_node = parsed_art.ast_arena.getNode(ast_id);
    const tok_count = parsed_art.token_buffer.countTokens();
    switch (ast_node.tag) {
        .field_access => {
            if (ast_node.rhs.tag == .token and ast_node.rhs.payload < tok_count) {
                return TokenIndex.fromInt(ast_node.rhs.payload);
            }
        },
        .method_call => {
            if (ast_node.rhs.tag == .extra and ast_node.rhs.payload < parsed_art.ast_arena.extra_data.items.len) {
                const member_raw = parsed_art.ast_arena.extra_data.items[ast_node.rhs.payload];
                if (member_raw < tok_count) return TokenIndex.fromInt(member_raw);
            }
        },
        .contextual_variant => {
            if (ast_node.lhs.tag == .token and ast_node.lhs.payload < tok_count) {
                return TokenIndex.fromInt(ast_node.lhs.payload);
            }
        },
        .incomplete_call => {
            if (ast_node.lhs.tag == .token and ast_node.lhs.payload < tok_count and
                !ast_node.main_token.isNone() and ast_node.main_token.asInt() < tok_count and
                parsed_art.token_buffer.getToken(ast_node.main_token).kind == .dot)
            {
                return TokenIndex.fromInt(ast_node.lhs.payload);
            }
        },
        .ident_expr => {
            if (ast_node.lhs.tag == .token and ast_node.lhs.payload < tok_count and
                !ast_node.main_token.isNone() and ast_node.main_token.asInt() < tok_count and
                parsed_art.token_buffer.getToken(ast_node.main_token).kind == .at)
            {
                return TokenIndex.fromInt(ast_node.lhs.payload);
            }
        },
        .variant_pat => {
            const pat_cst = parsed_art.ast_arena.getCstOrigin(ast_id);
            if (!pat_cst.isNone() and pat_cst.asInt() < parsed_art.cst_arena.countNodes()) {
                const start_idx: usize = pat_cst.asInt();
                const end_idx = @min(
                    start_idx + @max(@as(usize, parsed_art.cst_arena.getNode(pat_cst).subtree_size), 1),
                    parsed_art.cst_arena.countNodes(),
                );
                var last_ident_tok: TokenIndex = .none;
                var cur = start_idx + 1;
                while (cur < end_idx) : (cur += 1) {
                    const sub = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
                    if (sub.subtree_size <= 1 and !sub.flags.is_bracketed and
                        !sub.flags.is_missing_or_injected and !sub.token.isNone() and
                        sub.token.asInt() < tok_count)
                    {
                        const leaf_kind = parsed_art.token_buffer.getToken(sub.token).kind;
                        if (leaf_kind == .lparen or leaf_kind == .lbrace) break;
                        if (symbol_resolver.isIdentifierToken(leaf_kind)) {
                            last_ident_tok = sub.token;
                        }
                    }
                }
                if (!last_ident_tok.isNone()) return last_ident_tok;
            }
        },
        else => {},
    }
    return ast_node.main_token;
}

/// Emits semantic comment spans for `piece`, splitting `TRIVIA_FLAG_COALESCED` runs into individual comments.
fn appendCommentTriviaSemanticSpans(
    arena_alloc: std.mem.Allocator,
    src: []const u8,
    line_idx: *const LineIndex,
    encoding: PositionEncoding,
    piece: syntax_arenas.TriviaPiece,
    range_filter: ?LspRange,
    out_tokens: *std.ArrayListUnmanaged(RawSemanticToken),
) !void {
    const piece_start: usize = piece.byte_offset;
    const piece_end: usize = @min(@as(usize, piece.byte_offset) + @as(usize, piece.byte_len), src.len);
    if (piece_start >= piece_end) return;

    if ((piece.flags & syntax_arenas.TRIVIA_FLAG_COALESCED) == 0) {
        switch (piece.kind) {
            .doc_comment, .module_doc_comment => {
                // Scope only the 2-byte `/|` / `/#` marker so TextMate Markdown scopes inside docstrings stay intact:
                const marker_end: u32 = @intCast(@min(piece_start + 2, piece_end));
                try appendSplitSemanticSpan(
                    arena_alloc,
                    src,
                    line_idx,
                    encoding,
                    piece.byte_offset,
                    marker_end,
                    SEM_TOK_COMMENT,
                    SEM_MOD_DOCUMENTATION,
                    range_filter,
                    out_tokens,
                );
            },
            .line_comment => {
                try appendSplitSemanticSpan(
                    arena_alloc,
                    src,
                    line_idx,
                    encoding,
                    piece.byte_offset,
                    @intCast(piece_end),
                    SEM_TOK_COMMENT,
                    0,
                    range_filter,
                    out_tokens,
                );
            },
            else => {},
        }
        return;
    }

    var cursor: usize = piece_start;
    while (cursor < piece_end) {
        if (src[cursor] == '#' and cursor == 0 and cursor + 1 < piece_end and src[cursor + 1] == '!') {
            while (cursor < piece_end and src[cursor] != '\n' and src[cursor] != '\r') : (cursor += 1) {}
            continue;
        }
        if (src[cursor] == '/' and cursor + 1 < piece_end) {
            const next_byte = src[cursor + 1];
            if (next_byte == '|' or next_byte == '#' or next_byte == '/') {
                const com_start = cursor;
                const is_doc = (next_byte == '|' or next_byte == '#');
                cursor += 2;
                while (cursor < piece_end and src[cursor] != '\n' and src[cursor] != '\r') : (cursor += 1) {}
                const emit_end: usize = if (is_doc) @min(com_start + 2, cursor) else cursor;
                try appendSplitSemanticSpan(
                    arena_alloc,
                    src,
                    line_idx,
                    encoding,
                    @intCast(com_start),
                    @intCast(emit_end),
                    SEM_TOK_COMMENT,
                    if (is_doc) SEM_MOD_DOCUMENTATION else 0,
                    range_filter,
                    out_tokens,
                );
                continue;
            }
        }
        cursor += 1;
    }
}

/// Orders `InterpHoleSpec` entries by `(rel_brace_open_byte ASC, rel_brace_close_byte DESC)` so outer holes precede nested inner holes.
fn isInterpHoleBefore(_: void, lhs_hole: type_system.InterpHoleSpec, rhs_hole: type_system.InterpHoleSpec) bool {
    if (lhs_hole.rel_brace_open_byte != rhs_hole.rel_brace_open_byte) {
        return lhs_hole.rel_brace_open_byte < rhs_hole.rel_brace_open_byte;
    }
    return lhs_hole.rel_brace_close_byte > rhs_hole.rel_brace_close_byte;
}

/// Recursively emits non-overlapping semantic spans across `[seg_start, seg_end)` of an `f"…"` literal and its nested holes.
fn appendFmtSegmentSemanticSpans(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    src: []const u8,
    line_idx: *const LineIndex,
    fmt_tok_base: u32,
    seg_start: u32,
    seg_end: u32,
    sorted_holes: []const type_system.InterpHoleSpec,
    range_filter: ?LspRange,
    out_tokens: *std.ArrayListUnmanaged(RawSemanticToken),
    depth: u8,
) anyerror!void {
    if (seg_start >= seg_end) return;
    if (sorted_holes.len == 0 or depth >= 16) {
        try appendSplitSemanticSpan(
            arena_alloc,
            src,
            line_idx,
            session.position_encoding,
            seg_start,
            seg_end,
            SEM_TOK_STRING,
            0,
            range_filter,
            out_tokens,
        );
        return;
    }

    var str_seg_start: u32 = seg_start;
    for (sorted_holes) |hole| {
        const raw_open = fmt_tok_base +| hole.rel_brace_open_byte;
        const raw_close = fmt_tok_base +| hole.rel_brace_close_byte;
        if (raw_open < seg_start or raw_open >= seg_end or raw_close >= seg_end) continue;
        if (raw_open < str_seg_start) continue;

        const open_abs = raw_open;
        const close_abs = raw_close;
        const close_inclusive = @min(close_abs +| 1, seg_end);

        // [1] Emit preceding string literal text segment `[str_seg_start .. open_abs]`:
        if (str_seg_start < open_abs) {
            try appendSplitSemanticSpan(
                arena_alloc,
                src,
                line_idx,
                session.position_encoding,
                str_seg_start,
                open_abs,
                SEM_TOK_STRING,
                0,
                range_filter,
                out_tokens,
            );
        }

        // [2] Emit opening `{` delimiter as `SEM_TOK_OPERATOR`:
        try appendSplitSemanticSpan(
            arena_alloc,
            src,
            line_idx,
            session.position_encoding,
            open_abs,
            @min(open_abs +| 1, close_inclusive),
            SEM_TOK_OPERATOR,
            0,
            range_filter,
            out_tokens,
        );

        // [3] Emit semantic tokens for resolved sub-AST expression tokens inside `{expr…}`:
        var hole_prev_at = false;
        var hole_prev_kind: TokenKind = .eof;
        var hole_prev_prev_kind: TokenKind = .eof;
        var prev_htok_end: u32 = @min(open_abs +| 1, close_abs);
        for (hole.tokens) |htok| {
            if (htok.byte_len == 0) continue;
            const htok_start = fmt_tok_base +| htok.rel_byte;
            const htok_end = @min(htok_start +| @as(u32, htok.byte_len), close_abs);
            if (htok_start < prev_htok_end or htok_start >= htok_end) continue;
            prev_htok_end = htok_end;

            if (htok.kind == .fmt_string_lit) {
                hole_prev_at = false;
                try appendFmtSegmentSemanticSpans(
                    session,
                    arena_alloc,
                    src,
                    line_idx,
                    fmt_tok_base,
                    htok_start,
                    htok_end,
                    sorted_holes,
                    range_filter,
                    out_tokens,
                    depth + 1,
                );
                hole_prev_prev_kind = hole_prev_kind;
                hole_prev_kind = htok.kind;
                continue;
            }

            const htok_lex = src[@min(@as(usize, htok_start), src.len)..@min(@as(usize, htok_end), src.len)];

            if (htok.kind == .at) {
                hole_prev_at = true;
                try appendSplitSemanticSpan(
                    arena_alloc,
                    src,
                    line_idx,
                    session.position_encoding,
                    htok_start,
                    htok_end,
                    SEM_TOK_DECORATOR,
                    SEM_MOD_ATTRIBUTE,
                    range_filter,
                    out_tokens,
                );
            } else if (hole_prev_at and isIdentifierOrKeywordToken(htok.kind)) {
                hole_prev_at = false;
                const intr_type: u32 = if (type_system.INTRINSIC_NAME_MAP.has(htok_lex))
                    SEM_TOK_MACRO
                else
                    SEM_TOK_DECORATOR;
                try appendSplitSemanticSpan(
                    arena_alloc,
                    src,
                    line_idx,
                    session.position_encoding,
                    htok_start,
                    htok_end,
                    intr_type,
                    SEM_MOD_ATTRIBUTE,
                    range_filter,
                    out_tokens,
                );
            } else if (!htok.symbol_index.isNone()) {
                hole_prev_at = false;
                const sym_style = classifySymbolSemanticStyle(session, htok.symbol_index, false);
                try appendSplitSemanticSpan(
                    arena_alloc,
                    src,
                    line_idx,
                    session.position_encoding,
                    htok_start,
                    htok_end,
                    sym_style.tok_type,
                    sym_style.mod_bits,
                    range_filter,
                    out_tokens,
                );
            } else {
                hole_prev_at = false;
                const is_dot_var = htok.kind == .type_ident and hole_prev_kind == .dot and hole_prev_prev_kind != .ident;
                const htok_class: ?struct { tok_type: u32, mod_bits: u32 } = switch (htok.kind) {
                    .prim_type => .{ .tok_type = SEM_TOK_TYPE, .mod_bits = SEM_MOD_DEFAULT_LIB },
                    .type_ident => if (is_dot_var)
                        .{
                            .tok_type = SEM_TOK_ENUM_MEMBER,
                            .mod_bits = if (BUILTIN_VARIANT_SET.has(htok_lex)) SEM_MOD_DEFAULT_LIB else 0,
                        }
                    else if (symbol_resolver.BUILTIN_TYPE_AND_GROUP_MAP.has(htok_lex))
                        .{ .tok_type = SEM_TOK_TYPE, .mod_bits = SEM_MOD_DEFAULT_LIB }
                    else
                        .{ .tok_type = SEM_TOK_TYPE, .mod_bits = 0 },
                    .const_ident => .{ .tok_type = SEM_TOK_VARIABLE, .mod_bits = SEM_MOD_READONLY | SEM_MOD_STATIC },
                    .ident => if (BUILTIN_ROOT_NAMESPACE_SET.has(htok_lex))
                        .{ .tok_type = SEM_TOK_NAMESPACE, .mod_bits = SEM_MOD_DEFAULT_LIB }
                    else
                        .{ .tok_type = SEM_TOK_VARIABLE, .mod_bits = 0 },
                    .kw_self_val => .{ .tok_type = SEM_TOK_PARAMETER, .mod_bits = 0 },
                    .kw_self_type => .{ .tok_type = SEM_TOK_TYPE, .mod_bits = 0 },
                    .kw_own => .{ .tok_type = SEM_TOK_MODIFIER, .mod_bits = SEM_MOD_CONSUMED_MOVE },
                    .kw_mut, .kw_var => .{ .tok_type = SEM_TOK_MODIFIER, .mod_bits = SEM_MOD_MUTABLE },
                    .kw_async, .kw_await => .{ .tok_type = SEM_TOK_KEYWORD, .mod_bits = SEM_MOD_ASYNC },
                    .kw_unsafe, .kw_extern => .{ .tok_type = SEM_TOK_KEYWORD, .mod_bits = SEM_MOD_UNSAFE },
                    .kw_true, .kw_false, .char_lit, .byte_lit => null,
                    .string_lit, .byte_string_lit, .fmt_string_lit => .{ .tok_type = SEM_TOK_STRING, .mod_bits = 0 },
                    .int_lit, .float_lit => .{ .tok_type = SEM_TOK_NUMBER, .mod_bits = 0 },
                    else => if (@backingInt(htok.kind) <= @backingInt(TokenKind.kw_not))
                        .{ .tok_type = SEM_TOK_KEYWORD, .mod_bits = 0 }
                    else
                        null,
                };
                if (htok_class) |cls| {
                    try appendSplitSemanticSpan(
                        arena_alloc,
                        src,
                        line_idx,
                        session.position_encoding,
                        htok_start,
                        htok_end,
                        cls.tok_type,
                        cls.mod_bits,
                        range_filter,
                        out_tokens,
                    );
                }
            }
            hole_prev_prev_kind = hole_prev_kind;
            hole_prev_kind = htok.kind;
        }

        // [4] Emit `[=][:spec]}` suffix from first non-whitespace byte after `rel_expr_end_byte` through `}`:
        var suffix_start = @min(@max(fmt_tok_base +| hole.rel_expr_end_byte, prev_htok_end), close_abs);
        while (suffix_start < close_abs and @as(usize, suffix_start) < src.len) : (suffix_start += 1) {
            const ch_val = src[suffix_start];
            if (ch_val != ' ' and ch_val != '\t' and ch_val != '\r' and ch_val != '\n') break;
        }
        if (suffix_start < close_inclusive) {
            try appendSplitSemanticSpan(
                arena_alloc,
                src,
                line_idx,
                session.position_encoding,
                suffix_start,
                close_inclusive,
                SEM_TOK_OPERATOR,
                0,
                range_filter,
                out_tokens,
            );
        }
        str_seg_start = close_inclusive;
    }

    // [5] Emit trailing string literal text segment `[str_seg_start .. seg_end]`:
    if (str_seg_start < seg_end) {
        try appendSplitSemanticSpan(
            arena_alloc,
            src,
            line_idx,
            session.position_encoding,
            str_seg_start,
            seg_end,
            SEM_TOK_STRING,
            0,
            range_filter,
            out_tokens,
        );
    }
}

/// Emits interleaved `SEM_TOK_STRING`, `{` / `[=][:spec]}` `SEM_TOK_OPERATOR`, and inner expression semantic tokens for `f"…"`.
fn appendFmtStringSemanticSpans(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    src: []const u8,
    line_idx: *const LineIndex,
    fmt_tok_base: u32,
    fmt_tok_end: u32,
    holes: []const type_system.InterpHoleSpec,
    range_filter: ?LspRange,
    out_tokens: *std.ArrayListUnmanaged(RawSemanticToken),
) !void {
    var sorted_holes: []const type_system.InterpHoleSpec = holes;
    if (holes.len > 1) {
        const duped_holes = try arena_alloc.dupe(type_system.InterpHoleSpec, holes);
        std.mem.sort(type_system.InterpHoleSpec, duped_holes, {}, isInterpHoleBefore);
        sorted_holes = duped_holes;
    }
    try appendFmtSegmentSemanticSpans(
        session,
        arena_alloc,
        src,
        line_idx,
        fmt_tok_base,
        fmt_tok_base,
        fmt_tok_end,
        sorted_holes,
        range_filter,
        out_tokens,
        0,
    );
}

/// Computes the 5-`u32`-per-token delta-encoded semantic token stream for `file_id` (optionally clipped to `range_opt`).
fn computeSemanticTokensData(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    file_id: FileId,
    range_opt: ?LspRange,
) ![]const u32 {
    const src = getLiveDocumentSource(session, file_id) orelse return &.{};
    const line_idx = try session.vfs.getLineIndex(file_id);
    _ = try session.db.parseCst(file_id);
    _ = try session.db.resolveSignatures(file_id);
    const entries = try arena_alloc.dupe(
        query_db.ItemTreeEntry,
        (try session.db.extractItemTree(file_id)).entries,
    );
    var parsed_art = session.db.parsed_artifacts.getPtr(file_id.asInt()) orelse return &.{};

    const tok_count = parsed_art.token_buffer.countTokens();
    var tok_symbols = try arena_alloc.alloc(SymbolIndex, tok_count);
    @memset(tok_symbols, .none);
    var tok_extra_mods = try arena_alloc.alloc(u32, tok_count);
    @memset(tok_extra_mods, 0);
    var tok_is_decl = try arena_alloc.alloc(bool, tok_count);
    @memset(tok_is_decl, false);
    var tok_variant_tier = try arena_alloc.alloc(u8, tok_count);
    @memset(tok_variant_tier, 0);
    var fmt_interps_by_tok: std.AutoHashMapUnmanaged(u32, []const type_system.InterpHoleSpec) = .empty;

    // Map AST nodes and MVS move/mutation sites from per-`DefId` `BodySemanticSideTables`:
    for (entries) |entry| {
        try session.db.unwindIfCanceled();
        switch (entry.kind) {
            .mod_decl, .use_decl, .ffi_extern_block => continue,
            else => {},
        }
        const side_tables = (try session.db.getDefSideTables(entry.def_id)) orelse continue;
        parsed_art = session.db.parsed_artifacts.getPtr(file_id.asInt()) orelse return &.{};
        const ast_limit = @min(side_tables.ast_end, @as(u32, @intCast(parsed_art.ast_arena.countNodes())));

        var interp_it = side_tables.string_interps.iterator();
        while (interp_it.next()) |interp_kv| {
            const fmt_ast_raw = side_tables.ast_start + interp_kv.key_ptr.*;
            if (fmt_ast_raw >= ast_limit) continue;
            const fmt_main_tok = parsed_art.ast_arena.getNode(NodeIndex.fromInt(fmt_ast_raw)).main_token;
            if (!fmt_main_tok.isNone() and fmt_main_tok.asInt() < tok_count) {
                if (fmt_interps_by_tok.get(fmt_main_tok.asInt())) |existing_holes| {
                    const merged_holes = try arena_alloc.alloc(
                        type_system.InterpHoleSpec,
                        existing_holes.len + interp_kv.value_ptr.holes.len,
                    );
                    @memcpy(merged_holes[0..existing_holes.len], existing_holes);
                    @memcpy(merged_holes[existing_holes.len..], interp_kv.value_ptr.holes);
                    try fmt_interps_by_tok.put(arena_alloc, fmt_main_tok.asInt(), merged_holes);
                } else {
                    try fmt_interps_by_tok.put(arena_alloc, fmt_main_tok.asInt(), interp_kv.value_ptr.holes);
                }
            }
        }

        var ast_raw = side_tables.ast_start;
        while (ast_raw < ast_limit) : (ast_raw += 1) {
            const ast_id = NodeIndex.fromInt(ast_raw);
            const ast_node = parsed_art.ast_arena.getNode(ast_id);
            const resolved_sym = side_tables.getNodeSymbol(ast_id);
            const focal_tok = resolveAstNodeFocalToken(parsed_art, ast_id);
            if (!focal_tok.isNone() and focal_tok.asInt() < tok_count) {
                if (!resolved_sym.isNone()) {
                    tok_symbols[focal_tok.asInt()] = resolved_sym;
                    if (ast_node.tag == .bind_pat or ast_node.tag == .local_var_decl) {
                        tok_is_decl[focal_tok.asInt()] = true;
                    }
                } else if (parsed_art.token_buffer.getToken(focal_tok).kind == .type_ident) {
                    const focal_lex = symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, focal_tok);
                    const is_dot_variant = ast_node.tag == .contextual_variant or
                        (ast_node.tag == .incomplete_call and ast_node.lhs.tag == .token and
                            !ast_node.main_token.isNone() and ast_node.main_token.asInt() < tok_count and
                            parsed_art.token_buffer.getToken(ast_node.main_token).kind == .dot) or
                        (ast_node.tag == .variant_pat and !ast_node.main_token.isNone() and
                            ast_node.main_token.asInt() < tok_count and
                            parsed_art.token_buffer.getToken(ast_node.main_token).kind == .dot);
                    if (is_dot_variant or
                        ((ast_node.tag == .variant_pat or ast_node.tag == .field_access or ast_node.tag == .method_call) and
                            BUILTIN_VARIANT_SET.has(focal_lex)))
                    {
                        tok_variant_tier[focal_tok.asInt()] = if (BUILTIN_VARIANT_SET.has(focal_lex)) 2 else 1;
                    }
                }
            }

            // Annotate `own expr` (`consumedMove`) and `&mut expr` / assignment LHS (`modification`):
            if (ast_node.tag == .unary_expr) {
                if (!ast_node.main_token.isNone() and ast_node.main_token.asInt() < tok_count) {
                    const main_kind = parsed_art.token_buffer.getToken(ast_node.main_token).kind;
                    if (main_kind == .kw_own and ast_node.lhs.tag == .node) {
                        const target_node = parsed_art.ast_arena.getNode(NodeIndex.fromInt(ast_node.lhs.payload));
                        if (!target_node.main_token.isNone() and target_node.main_token.asInt() < tok_count) {
                            tok_extra_mods[target_node.main_token.asInt()] |= SEM_MOD_CONSUMED_MOVE;
                        }
                    } else if (main_kind == .kw_mut or main_kind == .kw_var) {
                        if (ast_node.lhs.tag == .node) {
                            const target_node = parsed_art.ast_arena.getNode(NodeIndex.fromInt(ast_node.lhs.payload));
                            if (!target_node.main_token.isNone() and target_node.main_token.asInt() < tok_count) {
                                tok_extra_mods[target_node.main_token.asInt()] |= SEM_MOD_MODIFICATION | SEM_MOD_MUTABLE;
                            }
                        }
                    }
                }
            } else if (ast_node.tag == .assign_stmt and ast_node.lhs.tag == .node) {
                const lhs_node = parsed_art.ast_arena.getNode(NodeIndex.fromInt(ast_node.lhs.payload));
                if (!lhs_node.main_token.isNone() and lhs_node.main_token.asInt() < tok_count) {
                    tok_extra_mods[lhs_node.main_token.asInt()] |= SEM_MOD_MODIFICATION;
                }
            }
        }
    }

    // Map live Pass-1 declaration spans in `file_id`:
    if (session.db.getFileLiveSymbolBounds(file_id)) |bounds| {
        var sym_raw = bounds.sym_start;
        while (sym_raw < bounds.sym_end and sym_raw < session.db.symbol_table.countSymbols()) : (sym_raw += 1) {
            const sym_idx = SymbolIndex.fromInt(sym_raw);
            const sym = session.db.symbol_table.getSymbol(sym_idx).*;
            if (sym.decl_span.file_id != file_id or sym.flags.is_imported) continue;
            const live_span = resolveLiveSymbolDeclSpanFast(
                session,
                sym_idx,
                file_id,
                src,
                parsed_art,
            ) catch continue;
            parsed_art = session.db.parsed_artifacts.getPtr(file_id.asInt()) orelse return &.{};
            if (live_span.file_id != file_id) continue;
            if (findExactTokenAtByteOffset(&parsed_art.token_buffer, live_span.start_byte)) |decl_tok| {
                if (decl_tok.asInt() < tok_count) {
                    const decl_lex = symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, decl_tok);
                    if (std.mem.eql(u8, sym.name_text, decl_lex)) {
                        tok_symbols[decl_tok.asInt()] = sym_idx;
                        tok_is_decl[decl_tok.asInt()] = true;
                    }
                }
            }
        }
    }

    var raw_tokens: std.ArrayListUnmanaged(RawSemanticToken) = .empty;
    var is_prev_at = false;

    var tok_i: usize = 0;
    while (tok_i < tok_count) : (tok_i += 1) {
        const tok_id = TokenIndex.fromInt(@intCast(tok_i));
        const tok_rec = parsed_art.token_buffer.getToken(tok_id);

        // Emit comment trivia attached to `tok_rec` (expanding `TRIVIA_FLAG_COALESCED` runs):
        const triv_start: usize = tok_rec.trivia_span.start_index;
        const triv_total: usize = @as(usize, tok_rec.trivia_span.leading_count) +
            @as(usize, tok_rec.trivia_span.trailing_count);
        if (triv_total > 0 and triv_start + triv_total <= parsed_art.token_buffer.trivia.items.len) {
            for (parsed_art.token_buffer.trivia.items[triv_start .. triv_start + triv_total]) |piece| {
                try appendCommentTriviaSemanticSpans(
                    arena_alloc,
                    src,
                    line_idx,
                    session.position_encoding,
                    piece,
                    range_opt,
                    &raw_tokens,
                );
            }
        }

        if (tok_rec.flags.is_synthesized or tok_rec.byte_len == 0 or tok_rec.kind == .eof) continue;
        const tok_start = tok_rec.byte_offset;
        const tok_end = tok_rec.byte_offset +| tok_rec.byte_len;
        const lexeme = src[tok_start..@min(@as(usize, tok_end), src.len)];

        if (tok_rec.kind == .fmt_string_lit) {
            is_prev_at = false;
            const fmt_holes = fmt_interps_by_tok.get(@intCast(tok_i)) orelse &.{};
            try appendFmtStringSemanticSpans(
                session,
                arena_alloc,
                src,
                line_idx,
                tok_start,
                tok_end,
                fmt_holes,
                range_opt,
                &raw_tokens,
            );
            continue;
        }
        if ((tok_rec.kind == .string_lit or tok_rec.kind == .byte_string_lit) and
            std.mem.indexOfScalar(u8, lexeme, '\n') != null)
        {
            is_prev_at = false;
            try appendSplitSemanticSpan(
                arena_alloc,
                src,
                line_idx,
                session.position_encoding,
                tok_start,
                tok_end,
                SEM_TOK_STRING,
                0,
                range_opt,
                &raw_tokens,
            );
            continue;
        }

        if (tok_rec.kind == .at) {
            is_prev_at = true;
            try appendSplitSemanticSpan(
                arena_alloc,
                src,
                line_idx,
                session.position_encoding,
                tok_start,
                tok_end,
                SEM_TOK_DECORATOR,
                SEM_MOD_ATTRIBUTE,
                range_opt,
                &raw_tokens,
            );
            continue;
        }
        if (is_prev_at and isIdentifierOrKeywordToken(tok_rec.kind)) {
            is_prev_at = false;
            const attr_type: u32 = if (type_system.INTRINSIC_NAME_MAP.has(lexeme))
                SEM_TOK_MACRO
            else
                SEM_TOK_DECORATOR;
            try appendSplitSemanticSpan(
                arena_alloc,
                src,
                line_idx,
                session.position_encoding,
                tok_start,
                tok_end,
                attr_type,
                SEM_MOD_ATTRIBUTE,
                range_opt,
                &raw_tokens,
            );
            continue;
        }
        is_prev_at = false;

        if (!tok_symbols[tok_i].isNone()) {
            const sym_style = classifySymbolSemanticStyle(session, tok_symbols[tok_i], tok_is_decl[tok_i]);
            try appendSplitSemanticSpan(
                arena_alloc,
                src,
                line_idx,
                session.position_encoding,
                tok_start,
                tok_end,
                sym_style.tok_type,
                sym_style.mod_bits | tok_extra_mods[tok_i],
                range_opt,
                &raw_tokens,
            );
            continue;
        }

        if (tok_variant_tier[tok_i] != 0) {
            const var_mods: u32 = if (tok_variant_tier[tok_i] == 2) SEM_MOD_DEFAULT_LIB else 0;
            try appendSplitSemanticSpan(
                arena_alloc,
                src,
                line_idx,
                session.position_encoding,
                tok_start,
                tok_end,
                SEM_TOK_ENUM_MEMBER,
                var_mods | tok_extra_mods[tok_i],
                range_opt,
                &raw_tokens,
            );
            continue;
        }

        const is_contextual_or_qual_variant = tok_rec.kind == .type_ident and tok_i > 0 and
            parsed_art.token_buffer.getToken(TokenIndex.fromInt(@intCast(tok_i - 1))).kind == .dot and
            (tok_i == 1 or
                parsed_art.token_buffer.getToken(TokenIndex.fromInt(@intCast(tok_i - 2))).kind != .ident);

        const lexical_class: ?struct { tok_type: u32, mod_bits: u32 } = switch (tok_rec.kind) {
            .prim_type => .{ .tok_type = SEM_TOK_TYPE, .mod_bits = SEM_MOD_DEFAULT_LIB },
            .type_ident => if (is_contextual_or_qual_variant)
                .{
                    .tok_type = SEM_TOK_ENUM_MEMBER,
                    .mod_bits = (if (BUILTIN_VARIANT_SET.has(lexeme)) SEM_MOD_DEFAULT_LIB else @as(u32, 0)) |
                        tok_extra_mods[tok_i],
                }
            else if (symbol_resolver.BUILTIN_TYPE_AND_GROUP_MAP.has(lexeme))
                .{ .tok_type = SEM_TOK_TYPE, .mod_bits = SEM_MOD_DEFAULT_LIB }
            else
                .{ .tok_type = SEM_TOK_TYPE, .mod_bits = tok_extra_mods[tok_i] },
            .const_ident => .{
                .tok_type = SEM_TOK_VARIABLE,
                .mod_bits = SEM_MOD_READONLY | SEM_MOD_STATIC | tok_extra_mods[tok_i],
            },
            .ident => if (BUILTIN_ROOT_NAMESPACE_SET.has(lexeme))
                .{ .tok_type = SEM_TOK_NAMESPACE, .mod_bits = SEM_MOD_DEFAULT_LIB }
            else
                .{ .tok_type = SEM_TOK_VARIABLE, .mod_bits = tok_extra_mods[tok_i] },
            .kw_self_val => .{ .tok_type = SEM_TOK_PARAMETER, .mod_bits = tok_extra_mods[tok_i] },
            .kw_self_type => .{ .tok_type = SEM_TOK_TYPE, .mod_bits = 0 },
            .kw_own => .{ .tok_type = SEM_TOK_MODIFIER, .mod_bits = SEM_MOD_CONSUMED_MOVE },
            .kw_mut, .kw_var => .{ .tok_type = SEM_TOK_MODIFIER, .mod_bits = SEM_MOD_MUTABLE },
            .kw_pub, .kw_comptime => .{ .tok_type = SEM_TOK_MODIFIER, .mod_bits = 0 },
            .kw_async, .kw_await => .{ .tok_type = SEM_TOK_KEYWORD, .mod_bits = SEM_MOD_ASYNC },
            .kw_unsafe, .kw_extern => .{ .tok_type = SEM_TOK_KEYWORD, .mod_bits = SEM_MOD_UNSAFE },
            .kw_true, .kw_false, .string_lit, .char_lit, .byte_lit, .byte_string_lit => null,
            .int_lit, .float_lit => .{ .tok_type = SEM_TOK_NUMBER, .mod_bits = 0 },
            else => if (@backingInt(tok_rec.kind) <= @backingInt(TokenKind.kw_not))
                .{ .tok_type = SEM_TOK_KEYWORD, .mod_bits = 0 }
            else
                null,
        };

        if (lexical_class) |cls| {
            try appendSplitSemanticSpan(
                arena_alloc,
                src,
                line_idx,
                session.position_encoding,
                tok_start,
                tok_end,
                cls.tok_type,
                cls.mod_bits,
                range_opt,
                &raw_tokens,
            );
        }
    }

    std.mem.sort(RawSemanticToken, raw_tokens.items, {}, isSemanticTokenBefore);

    var encoded: std.ArrayListUnmanaged(u32) = .empty;
    try encoded.ensureTotalCapacity(arena_alloc, raw_tokens.items.len * 5);
    var prev_line: u32 = 0;
    var prev_char: u32 = 0;
    for (raw_tokens.items, 0..) |item, idx| {
        if (idx > 0 and item.line_0 == prev_line and item.start_char_0 == prev_char) continue;
        const delta_line = item.line_0 -| prev_line;
        const delta_start = if (delta_line == 0) item.start_char_0 -| prev_char else item.start_char_0;
        encoded.appendAssumeCapacity(delta_line);
        encoded.appendAssumeCapacity(delta_start);
        encoded.appendAssumeCapacity(item.length);
        encoded.appendAssumeCapacity(item.token_type);
        encoded.appendAssumeCapacity(item.modifiers);
        prev_line = item.line_0;
        prev_char = item.start_char_0;
    }
    return encoded.items;
}

/// Handles `textDocument/semanticTokens/full` and `textDocument/semanticTokens/range`.
fn handleSemanticTokensFullOrRange(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    is_range_request: bool,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const range_opt: ?LspRange = if (is_range_request)
        extractJsonRange(params.getField("range") orelse JsonValue{ .null_val = {} })
    else
        null;

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) {
        session.outbound_buf.clearRetainingCapacity();
        const body_writer = &session.outbound_buf.writer;
        try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
        try writeJsonRpcId(body_writer, rpc_id);
        try body_writer.writeAll(",\"result\":{\"data\":[]}}");
        return flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
    }

    const encoded_data = try computeSemanticTokensData(session, arena_alloc, fid, range_opt);
    var res_id_opt: ?[16]u8 = null;
    if (!is_range_request) {
        const res_id = session.semantic_tokens_cache.allocNextResultId();
        try session.semantic_tokens_cache.putCloned(fid, res_id, encoded_data);
        res_id_opt = res_id;
    }

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":{");
    if (res_id_opt) |res_id| {
        try body_writer.writeAll("\"resultId\":");
        try writeJsonString(body_writer, &res_id);
        try body_writer.writeByte(',');
    }
    try body_writer.writeAll("\"data\":[");
    for (encoded_data, 0..) |val, i| {
        if (i > 0) try body_writer.writeByte(',');
        try body_writer.print("{d}", .{val});
    }
    try body_writer.writeAll("]}}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Handles `textDocument/semanticTokens/full/delta` using $O(N)$ prefix/suffix diffing against `SemanticTokensCache`.
fn handleSemanticTokensDelta(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const prev_result_id = params.getStringField("previousResultId") orelse "";

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) {
        session.outbound_buf.clearRetainingCapacity();
        const body_writer = &session.outbound_buf.writer;
        try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
        try writeJsonRpcId(body_writer, rpc_id);
        try body_writer.writeAll(",\"result\":{\"edits\":[]}}");
        return flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
    }

    const new_data = try computeSemanticTokensData(session, arena_alloc, fid, null);
    const prev_snapshot_copy: ?[]const u32 = if (session.semantic_tokens_cache.getMatchingResult(fid, prev_result_id)) |old_ref|
        try arena_alloc.dupe(u32, old_ref)
    else
        null;

    const new_res_id = session.semantic_tokens_cache.allocNextResultId();
    try session.semantic_tokens_cache.putCloned(fid, new_res_id, new_data);

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":{\"resultId\":");
    try writeJsonString(body_writer, &new_res_id);

    if (prev_snapshot_copy) |old_data| {
        var prefix_len: usize = 0;
        const min_len = @min(old_data.len, new_data.len);
        while (prefix_len < min_len and old_data[prefix_len] == new_data[prefix_len]) : (prefix_len += 1) {}

        if (prefix_len == old_data.len and old_data.len == new_data.len) {
            try body_writer.writeAll(",\"edits\":[]}}");
            return flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
        }

        var suffix_len: usize = 0;
        const max_suffix = min_len - prefix_len;
        while (suffix_len < max_suffix and
            old_data[old_data.len - 1 - suffix_len] == new_data[new_data.len - 1 - suffix_len]) : (suffix_len += 1)
        {}

        const delete_count = old_data.len - prefix_len - suffix_len;
        const replacement_slice = new_data[prefix_len .. new_data.len - suffix_len];
        try body_writer.print(
            ",\"edits\":[{{\"start\":{d},\"deleteCount\":{d},\"data\":[",
            .{ prefix_len, delete_count },
        );
        for (replacement_slice, 0..) |val, i| {
            if (i > 0) try body_writer.writeByte(',');
            try body_writer.print("{d}", .{val});
        }
        try body_writer.writeAll("]}]}}");
    } else {
        // Cache miss fallback; return full `SemanticTokens` payload per LSP 3.17 `SemanticTokens | SemanticTokensDelta`:
        try body_writer.writeAll(",\"data\":[");
        for (new_data, 0..) |val, i| {
            if (i > 0) try body_writer.writeByte(',');
            try body_writer.print("{d}", .{val});
        }
        try body_writer.writeAll("]}}");
    }
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

// ---------- Token, CST & Semantic Cursor Resolution -----------

/// Returns `true` when `kind` is a surface identifier or keyword token that can spell a symbol or attribute.
inline fn isIdentifierOrKeywordToken(kind: TokenKind) bool {
    return switch (kind) {
        .ident, .type_ident, .const_ident, .prim_type, .kw_self_val, .kw_self_type => true,
        else => @backingInt(kind) <= @backingInt(TokenKind.kw_not),
    };
}

/// Returns `true` when `kind` is a strict user-declarable identifier token (`.ident`, `.type_ident`, `.const_ident`).
inline fn isUserIdentifierToken(kind: TokenKind) bool {
    return kind == .ident or kind == .type_ident or kind == .const_ident;
}

/// Binary-searches `token_buffer` for a non-synthesized token starting at exact `start_byte`.
fn findExactTokenAtByteOffset(token_buffer: *const TokenBuffer, start_byte: u32) ?TokenIndex {
    const tok_count = token_buffer.countTokens();
    var low: usize = 0;
    var high: usize = tok_count;
    while (low < high) {
        const mid = low + (high - low) / 2;
        const mid_off = token_buffer.getToken(TokenIndex.fromInt(@intCast(mid))).byte_offset;
        if (mid_off < start_byte) {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    while (low < tok_count) : (low += 1) {
        const cand_id = TokenIndex.fromInt(@intCast(low));
        const cand_rec = token_buffer.getToken(cand_id);
        if (cand_rec.byte_offset != start_byte) break;
        if (!cand_rec.flags.is_synthesized and cand_rec.kind != .eof) return cand_id;
    }
    return null;
}

/// Resolves the live declaration `Span` of `sym_idx` in $O(\log T)$ against pre-fetched `parsed_art` when unshifted.
fn resolveLiveSymbolDeclSpanFast(
    session: *LspSession,
    sym_idx: SymbolIndex,
    file_id: FileId,
    src: []const u8,
    parsed_art: *const query_db.ParsedCstArtifact,
) query_db.QueryError!Span {
    if (sym_idx.isNone() or sym_idx.asInt() >= session.db.symbol_table.countSymbols()) return Span.ZERO;
    const sym = session.db.symbol_table.getSymbol(sym_idx).*;
    if (sym.decl_span.file_id == file_id) {
        if (findExactTokenAtByteOffset(&parsed_art.token_buffer, sym.decl_span.start_byte)) |cand_tok| {
            const cand_rec = parsed_art.token_buffer.getToken(cand_tok);
            if (cand_rec.byte_offset + cand_rec.byte_len == sym.decl_span.end_byte and
                (sym.name_text.len == 0 or
                    std.mem.eql(
                        u8,
                        symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, cand_tok),
                        sym.name_text,
                    )))
            {
                return sym.decl_span;
            }
        }
    }
    return session.db.resolveLiveSymbolDeclSpan(sym_idx);
}

/// Finds the focal token at `cursor_byte` (preferring an identifier when `cursor_byte` touches its right edge).
fn findTokenAtCursorByte(token_buffer: *const TokenBuffer, cursor_byte: u32) TokenIndex {
    const tok_count = token_buffer.countTokens();
    if (tok_count == 0) return .none;

    var best_tok: TokenIndex = .none;
    var i: usize = 0;
    while (i < tok_count) : (i += 1) {
        const tok_id = TokenIndex.fromInt(@intCast(i));
        const rec = token_buffer.getToken(tok_id);
        if (rec.flags.is_synthesized or rec.byte_len == 0 or rec.kind == .eof) continue;
        const start_b = rec.byte_offset;
        const end_b = rec.byte_offset +| rec.byte_len;
        if (cursor_byte >= start_b and cursor_byte < end_b) {
            if (isUserIdentifierToken(rec.kind) or rec.kind == .kw_self_val or rec.kind == .kw_self_type) {
                return tok_id;
            }
            best_tok = tok_id;
        } else if (cursor_byte == end_b and
            (isUserIdentifierToken(rec.kind) or rec.kind == .kw_self_val or rec.kind == .kw_self_type or
                (i > 0 and isIdentifierOrKeywordToken(rec.kind) and
                    token_buffer.getToken(TokenIndex.fromInt(@intCast(i - 1))).kind == .at)))
        {
            return tok_id;
        }
    }
    return best_tok;
}

/// Computes the inclusive-exclusive `[min_byte, max_byte)` span of all non-synthesized leaf tokens in `cst_node`.
fn computeCstSubtreeByteSpan(
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    cst_node: CstNodeIndex,
) ?Span {
    if (cst_node.isNone() or cst_node.asInt() >= cst_arena.countNodes()) return null;
    const start_idx: usize = cst_node.asInt();
    const root_rec = cst_arena.getNode(cst_node);
    const end_idx = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );
    const tok_count = token_buffer.countTokens();
    var min_b: u32 = std.math.maxInt(u32);
    var max_b: u32 = 0;
    var has_any = false;

    var cur = start_idx;
    while (cur < end_idx) : (cur += 1) {
        const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
        if (sub.subtree_size <= 1 and !sub.flags.is_missing_or_injected and
            !sub.token.isNone() and sub.token.asInt() < tok_count)
        {
            const tok_rec = token_buffer.getToken(sub.token);
            if (tok_rec.flags.is_synthesized or tok_rec.kind == .eof) continue;
            min_b = @min(min_b, tok_rec.byte_offset);
            max_b = @max(max_b, tok_rec.byte_offset +| tok_rec.byte_len);
            has_any = true;
        }
    }
    if (!has_any or min_b > max_b) return null;
    return Span.init(file_id, min_b, max_b);
}

/// Unwraps references, pointers, slices, arrays, optionals, results, and futures to reach a nominal `SymbolIndex`.
fn unwrapTypeToNominalSymbol(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_type_id: TypeId,
) SymbolIndex {
    var cur_ty = raw_type_id;
    var depth: u32 = 0;
    while (!cur_ty.isError() and depth < 32) : (depth += 1) {
        if (cur_ty.isPrimitiveOrSentinel()) {
            return sym_table.type_to_symbol.get(cur_ty.toU32()) orelse .none;
        }
        const node = pool.getNode(cur_ty);
        switch (node.tag) {
            .struct_ty, .enum_ty, .union_ty, .bit_field_ty, .trait_ty, .distinct_ty, .user_group => {
                const sym_idx = SymbolIndex.fromInt(node.rhs);
                if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.countSymbols()) {
                    return sym_idx;
                }
                return .none;
            },
            .refined_ty => {
                if (pool.getRefinementBounds(cur_ty)) |bounds| {
                    if (!bounds.sym_idx.isNone() and bounds.sym_idx.asInt() < sym_table.countSymbols()) {
                        return bounds.sym_idx;
                    }
                    cur_ty = bounds.base_ty;
                    continue;
                }
                cur_ty = TypeId.fromInt(node.lhs);
            },
            .ref_ty,
            .mut_ref_ty,
            .raw_ptr_ty,
            .slice_ty,
            .soa_slice_ty,
            .array_ty,
            .soa_array_ty,
            .soa_vec_ty,
            .optional_ty,
            .future_ty,
            .dyn_trait_ty,
            .tilde_approx,
            => {
                cur_ty = TypeId.fromInt(node.lhs);
            },
            .result_ty => {
                const ok_sym = unwrapTypeToNominalSymbol(pool, sym_table, TypeId.fromInt(node.lhs));
                if (!ok_sym.isNone()) return ok_sym;
                cur_ty = TypeId.fromInt(node.rhs);
            },
            else => return sym_table.type_to_symbol.get(cur_ty.toU32()) orelse .none,
        }
    }
    return .none;
}

/// Resolves an explicit `.field_init` (`Point { x: 1 }`) or `.field_pat` (`Point { x: p }`) field token at `tok_idx`.
fn tryResolveExplicitFieldTokenInDef(
    session: *LspSession,
    file_id: FileId,
    src: []const u8,
    parsed_art: *const query_db.ParsedCstArtifact,
    side_tables: *const BodySemanticSideTables,
    tok_idx: TokenIndex,
) SymbolIndex {
    const tok_lex = symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, tok_idx);
    if (tok_lex.len == 0) return .none;
    const field_name_id = session.db.interner.lookup(tok_lex) orelse return .none;

    var ast_raw = side_tables.ast_start;
    const ast_limit = @min(side_tables.ast_end, @as(u32, @intCast(parsed_art.ast_arena.countNodes())));
    while (ast_raw < ast_limit) : (ast_raw += 1) {
        const ast_id = NodeIndex.fromInt(ast_raw);
        const ast_node = parsed_art.ast_arena.getNode(ast_id);
        if (ast_node.tag != .struct_lit and ast_node.tag != .struct_pat and ast_node.tag != .variant_pat) {
            continue;
        }
        const cst_origin = parsed_art.ast_arena.getCstOrigin(ast_id);
        if (cst_origin.isNone()) continue;
        const cst_span = computeCstSubtreeByteSpan(
            file_id,
            &parsed_art.token_buffer,
            &parsed_art.cst_arena,
            cst_origin,
        ) orelse continue;
        const tok_off = parsed_art.token_buffer.getToken(tok_idx).byte_offset;
        if (tok_off < cst_span.start_byte or tok_off >= cst_span.end_byte) continue;

        const container_ty = side_tables.getNodeType(ast_id);
        const nom_sym_idx = unwrapTypeToNominalSymbol(&session.db.type_pool, &session.db.symbol_table, container_ty);
        if (nom_sym_idx.isNone()) continue;
        const nom_sym = session.db.symbol_table.getSymbol(nom_sym_idx).*;
        if (nom_sym.target_scope.isNone()) continue;

        // Check whether `tok_idx` is the leading field label of a `.field_init` or `.field_pat` CST child:
        const cst_start: usize = cst_origin.asInt();
        const cst_end = @min(
            cst_start + @max(@as(usize, parsed_art.cst_arena.getNode(cst_origin).subtree_size), 1),
            parsed_art.cst_arena.countNodes(),
        );
        var cur = cst_start + 1;
        while (cur < cst_end) : (cur += 1) {
            const sub_cst = CstNodeIndex.fromInt(@intCast(cur));
            const sub_rec = parsed_art.cst_arena.getNode(sub_cst);
            if (sub_rec.kind != .field_init and sub_rec.kind != .field_pat) continue;
            const field_end = @min(cur + @max(@as(usize, sub_rec.subtree_size), 1), cst_end);
            var first_ident: TokenIndex = .none;
            var has_colon = false;
            var f_cur = cur + 1;
            while (f_cur < field_end) : (f_cur += 1) {
                const leaf = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(f_cur)));
                if (leaf.subtree_size > 1 or leaf.token.isNone() or
                    leaf.token.asInt() >= parsed_art.token_buffer.countTokens())
                {
                    continue;
                }
                const lk = parsed_art.token_buffer.getToken(leaf.token).kind;
                if (first_ident.isNone() and isUserIdentifierToken(lk)) {
                    first_ident = leaf.token;
                } else if (!first_ident.isNone() and lk == .colon) {
                    has_colon = true;
                    break;
                } else if (!first_ident.isNone()) {
                    break;
                }
            }
            if (has_colon and first_ident == tok_idx) {
                if (nom_sym.kind == .enum_sym and ast_node.tag == .variant_pat) {
                    const var_sym = side_tables.getNodeSymbol(ast_id);
                    if (!var_sym.isNone()) {
                        const var_rec = session.db.symbol_table.getSymbol(var_sym).*;
                        if (!var_rec.target_scope.isNone()) {
                            const found_vfield = session.db.symbol_table.lookupInScopeDirect(
                                var_rec.target_scope,
                                field_name_id,
                                NamespaceMask.VALUE_ONLY,
                            );
                            if (!found_vfield.isNone()) return found_vfield;
                        }
                    }
                }
                const found_field = session.db.symbol_table.lookupInScopeDirect(
                    nom_sym.target_scope,
                    field_name_id,
                    NamespaceMask.VALUE_ONLY,
                );
                if (!found_field.isNone()) return found_field;
            }
        }
    }
    return .none;
}

/// Sub-token hit resolved inside an `f"…"` / `f#"…"#` interpolation hole (`ADR-24B`).
const InterpHoleCursorHit = struct {
    /// Enclosing `.fmt_string_lit` token live start byte (`fmt_tok_base`).
    fmt_tok_base: u32,
    /// Matched `InterpHoleSpec` containing the cursor.
    hole: type_system.InterpHoleSpec,
    /// Index of `token_info` inside `hole.tokens`.
    token_idx_in_hole: usize,
    /// Matched sub-AST token metadata.
    token_info: type_system.InterpHoleTokenInfo,
};

/// Resolves the innermost sub-AST token at `cursor_byte` inside `.fmt_string_lit` token `fmt_tok_idx`.
fn findInterpHoleTokenAtByte(
    side_tables: *const BodySemanticSideTables,
    parsed_art: *const query_db.ParsedCstArtifact,
    fmt_tok_idx: TokenIndex,
    cursor_byte: u32,
) ?InterpHoleCursorHit {
    if (fmt_tok_idx.isNone() or fmt_tok_idx.asInt() >= parsed_art.token_buffer.countTokens()) return null;
    const ast_limit = @min(side_tables.ast_end, @as(u32, @intCast(parsed_art.ast_arena.countNodes())));

    var best_hit: ?InterpHoleCursorHit = null;
    var best_hole_span: u32 = std.math.maxInt(u32);

    var interp_it = side_tables.string_interps.iterator();
    while (interp_it.next()) |interp_kv| {
        const fmt_ast_raw = side_tables.ast_start + interp_kv.key_ptr.*;
        if (fmt_ast_raw >= ast_limit) continue;
        const fmt_main_tok = parsed_art.ast_arena.getNode(NodeIndex.fromInt(fmt_ast_raw)).main_token;
        if (fmt_main_tok != fmt_tok_idx) continue;

        const fmt_tok_base = parsed_art.token_buffer.getToken(fmt_main_tok).byte_offset;
        for (interp_kv.value_ptr.holes) |hole| {
            const open_abs = fmt_tok_base +| hole.rel_brace_open_byte;
            const close_abs = fmt_tok_base +| hole.rel_brace_close_byte;
            const expr_end_abs = @min(fmt_tok_base +| hole.rel_expr_end_byte, close_abs);
            if (cursor_byte <= open_abs or cursor_byte > expr_end_abs) continue;
            const hole_span_len = expr_end_abs -| open_abs;
            if (best_hit != null and hole_span_len >= best_hole_span) continue;

            for (hole.tokens, 0..) |htok, idx_in_hole| {
                if (htok.byte_len == 0 or htok.kind == .fmt_string_lit) continue;
                const htok_start = fmt_tok_base +| htok.rel_byte;
                const htok_end = htok_start +| @as(u32, htok.byte_len);
                if (cursor_byte >= htok_start and cursor_byte < htok_end) {
                    best_hit = .{
                        .fmt_tok_base = fmt_tok_base,
                        .hole = hole,
                        .token_idx_in_hole = idx_in_hole,
                        .token_info = htok,
                    };
                    best_hole_span = hole_span_len;
                    break;
                }
                if (cursor_byte == htok_end and isIdentifierOrKeywordToken(htok.kind)) {
                    const has_next_ident_at_cursor = idx_in_hole + 1 < hole.tokens.len and
                        (fmt_tok_base +| hole.tokens[idx_in_hole + 1].rel_byte) == cursor_byte and
                        isIdentifierOrKeywordToken(hole.tokens[idx_in_hole + 1].kind);
                    if (!has_next_ident_at_cursor) {
                        best_hit = .{
                            .fmt_tok_base = fmt_tok_base,
                            .hole = hole,
                            .token_idx_in_hole = idx_in_hole,
                            .token_info = htok,
                        };
                        best_hole_span = hole_span_len;
                        break;
                    }
                }
            }
        }
    }
    return best_hit;
}

/// Resolves the semantic symbol and type at `(file_id, pos)` across AST side tables, `use` trees, and declarations.
fn resolveCursorTarget(
    session: *LspSession,
    file_id: FileId,
    pos: LspPosition,
) !CursorTarget {
    var result = CursorTarget{};
    const src = getLiveDocumentSource(session, file_id) orelse return result;
    const cursor_byte = lspPositionToByteOffset(session, file_id, pos);
    _ = try session.db.parseCst(file_id);
    _ = try session.db.resolveSignatures(file_id);
    const item_tree = try session.db.extractItemTree(file_id);
    var parsed_art = session.db.parsed_artifacts.getPtr(file_id.asInt()) orelse return result;

    var tok_idx = findTokenAtCursorByte(&parsed_art.token_buffer, cursor_byte);
    if (tok_idx.isNone()) return result;
    // Normalize `&self` / `&mut self` / `own self` receiver prefix clicks onto the adjacent `self` token:
    {
        const raw_idx = tok_idx.asInt();
        const total_toks = parsed_art.token_buffer.countTokens();
        const init_kind = parsed_art.token_buffer.getToken(tok_idx).kind;
        if (init_kind == .amp and raw_idx + 1 < total_toks) {
            const next_one = TokenIndex.fromInt(raw_idx + 1);
            const next_kind = parsed_art.token_buffer.getToken(next_one).kind;
            if (next_kind == .kw_self_val) {
                tok_idx = next_one;
            } else if (next_kind == .kw_mut and raw_idx + 2 < total_toks and
                parsed_art.token_buffer.getToken(TokenIndex.fromInt(raw_idx + 2)).kind == .kw_self_val)
            {
                tok_idx = TokenIndex.fromInt(raw_idx + 2);
            }
        } else if ((init_kind == .kw_mut or init_kind == .kw_own) and raw_idx + 1 < total_toks and
            parsed_art.token_buffer.getToken(TokenIndex.fromInt(raw_idx + 1)).kind == .kw_self_val)
        {
            tok_idx = TokenIndex.fromInt(raw_idx + 1);
        }
    }
    result.token_index = tok_idx;
    result.token_span = parsed_art.token_buffer.getTokenSpan(file_id, tok_idx);
    const tok_rec = parsed_art.token_buffer.getToken(tok_idx);
    const tok_lex = symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, tok_idx);

    // [1] Locate enclosing `ItemTreeEntry` (`DefId`) containing `result.token_span`:
    for (item_tree.entries) |entry| {
        const entry_span = computeCstSubtreeByteSpan(
            file_id,
            &parsed_art.token_buffer,
            &parsed_art.cst_arena,
            entry.cst_node,
        ) orelse continue;
        if (result.token_span.start_byte >= entry_span.start_byte and
            result.token_span.start_byte <= entry_span.end_byte)
        {
            result.enclosing_def_id = entry.def_id;
            if (entry.kind == .mod_decl and std.mem.eql(u8, entry.name_text, tok_lex)) {
                const mod_key_id = session.db.interner.lookup(tok_lex) orelse .empty;
                if (!mod_key_id.isNone()) {
                    const ext_key: u64 = (@as(u64, file_id.asInt()) << 32) | @as(u64, mod_key_id.asInt());
                    if (session.db.external_mod_files.get(ext_key)) |bound_child_fid| {
                        result.external_mod_file_id = bound_child_fid;
                    }
                }
            }
            break;
        }
    }

    // [2] Inspect enclosing `DefId` `BodySemanticSideTables` for exact token symbol/type hit:
    if (!result.enclosing_def_id.isNone()) {
        if (item_tree.getEntry(result.enclosing_def_id)) |enc_entry| {
            if (enc_entry.kind != .mod_decl and enc_entry.kind != .use_decl and
                enc_entry.kind != .ffi_extern_block)
            {
                if (try session.db.getDefSideTables(result.enclosing_def_id)) |side_tables| {
                    parsed_art = session.db.parsed_artifacts.getPtr(file_id.asInt()) orelse return result;
                    if (tok_rec.kind == .fmt_string_lit) {
                        if (findInterpHoleTokenAtByte(
                            side_tables,
                            parsed_art,
                            tok_idx,
                            @intCast(@min(cursor_byte, std.math.maxInt(u32))),
                        )) |hole_hit| {
                            const htok_start = hole_hit.fmt_tok_base +| hole_hit.token_info.rel_byte;
                            const htok_end = htok_start +| @as(u32, hole_hit.token_info.byte_len);
                            result.token_span = Span.init(file_id, htok_start, htok_end);
                            result.resolved_token_kind = hole_hit.token_info.kind;
                            result.symbol_index = hole_hit.token_info.symbol_index;
                            if (!hole_hit.token_info.type_id.isError()) {
                                result.type_id = hole_hit.token_info.type_id;
                            } else if (!hole_hit.token_info.symbol_index.isNone()) {
                                result.type_id = session.db.symbol_table.getSymbol(
                                    hole_hit.token_info.symbol_index,
                                ).type_id;
                            }
                        } else {
                            result.token_index = .none;
                        }
                        return result;
                    }

                    var ast_raw = side_tables.ast_start;
                    const ast_limit = @min(
                        side_tables.ast_end,
                        @as(u32, @intCast(parsed_art.ast_arena.countNodes())),
                    );
                    while (ast_raw < ast_limit) : (ast_raw += 1) {
                        const ast_id = NodeIndex.fromInt(ast_raw);
                        if (resolveAstNodeFocalToken(parsed_art, ast_id) != tok_idx) continue;

                        const cand_sym = side_tables.getNodeSymbol(ast_id);
                        const cand_ty = side_tables.getNodeType(ast_id);
                        if (!cand_sym.isNone()) {
                            result.symbol_index = cand_sym;
                            if (!cand_ty.isError()) {
                                result.type_id = cand_ty;
                            } else {
                                result.type_id = session.db.symbol_table.getSymbol(cand_sym).type_id;
                            }
                            return result;
                        }
                        if (!cand_ty.isError() and result.type_id.isError()) {
                            result.type_id = cand_ty;
                        }
                    }

                    const explicit_field = tryResolveExplicitFieldTokenInDef(
                        session,
                        file_id,
                        src,
                        parsed_art,
                        side_tables,
                        tok_idx,
                    );
                    if (!explicit_field.isNone()) {
                        result.symbol_index = explicit_field;
                        result.type_id = session.db.symbol_table.getSymbol(explicit_field).type_id;
                        return result;
                    }
                }

                // Match live parameter symbols (including `&self` / `&mut self` / `own self` in method headers)
                // and `Self` inside `impl` / `trait` items:
                var live_param_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty;
                try collectEntryLiveScopeParamSymbols(
                    session,
                    session.turn_arena.asAllocator(),
                    enc_entry.*,
                    &live_param_syms,
                );
                parsed_art = session.db.parsed_artifacts.getPtr(file_id.asInt()) orelse return result;
                for (live_param_syms.items) |param_sym_idx| {
                    if (param_sym_idx.isNone() or param_sym_idx.asInt() >= session.db.symbol_table.countSymbols()) {
                        continue;
                    }
                    const param_sym = session.db.symbol_table.getSymbol(param_sym_idx).*;
                    if (!std.mem.eql(u8, param_sym.name_text, tok_lex)) continue;
                    const param_span = session.db.resolveLiveSymbolDeclSpan(param_sym_idx) catch param_sym.decl_span;
                    parsed_art = session.db.parsed_artifacts.getPtr(file_id.asInt()) orelse return result;
                    if (param_span.file_id == file_id and
                        param_span.start_byte <= result.token_span.start_byte and
                        result.token_span.end_byte <= param_span.end_byte)
                    {
                        result.symbol_index = param_sym_idx;
                        result.type_id = param_sym.type_id;
                        return result;
                    }
                }
                if (tok_rec.kind == .kw_self_type or tok_rec.kind == .kw_self_val) {
                    for (live_param_syms.items) |param_sym_idx| {
                        if (param_sym_idx.isNone() or param_sym_idx.asInt() >= session.db.symbol_table.countSymbols()) {
                            continue;
                        }
                        const param_sym = session.db.symbol_table.getSymbol(param_sym_idx).*;
                        if (!std.mem.eql(u8, param_sym.name_text, "self")) continue;
                        const nom_sym_idx = unwrapTypeToNominalSymbol(
                            &session.db.type_pool,
                            &session.db.symbol_table,
                            param_sym.type_id,
                        );
                        if (tok_rec.kind == .kw_self_type and !nom_sym_idx.isNone()) {
                            result.symbol_index = nom_sym_idx;
                            result.type_id = session.db.symbol_table.getSymbol(nom_sym_idx).type_id;
                            return result;
                        }
                    }
                }
            }
        }
    }

    // [3] Match live Pass-1 / signature declaration spans in `file_id`:
    if (session.db.getFileLiveSymbolBounds(file_id)) |bounds| {
        var sym_raw = bounds.sym_start;
        while (sym_raw < bounds.sym_end and sym_raw < session.db.symbol_table.countSymbols()) : (sym_raw += 1) {
            const sym_idx = SymbolIndex.fromInt(sym_raw);
            const sym = session.db.symbol_table.getSymbol(sym_idx).*;
            if (!std.mem.eql(u8, sym.name_text, tok_lex)) continue;
            // Glob imports have `decl_span.file_id != file_id`; skip unless declared in `file_id`:
            if (sym.decl_span.file_id == file_id) {
                const live_span = session.db.resolveLiveSymbolDeclSpan(sym_idx) catch sym.decl_span;
                if (live_span.file_id == file_id and
                    live_span.start_byte == result.token_span.start_byte and
                    live_span.end_byte == result.token_span.end_byte)
                {
                    result.symbol_index = sym_idx;
                    result.type_id = sym.type_id;
                    return result;
                }
            }
        }
    }

    // [4] Fallback lexical lookup in `file_module_scopes[file_id]` (e.g., types in signatures, `use` paths, prelude):
    if (tok_rec.kind == .prim_type or symbol_resolver.BUILTIN_TYPE_AND_GROUP_MAP.has(tok_lex)) {
        if (symbol_resolver.BUILTIN_TYPE_AND_GROUP_MAP.get(tok_lex)) |builtin_tid| {
            result.type_id = builtin_tid;
            if (session.db.symbol_table.type_to_symbol.get(builtin_tid.toU32())) |b_sym| {
                result.symbol_index = b_sym;
            }
            return result;
        }
    }

    if (session.db.symbol_table.file_module_scopes.get(file_id.asInt())) |mod_scope| {
        const tok_raw = tok_idx.asInt();
        const tok_total = parsed_art.token_buffer.countTokens();
        const prev_kind: TokenKind = if (tok_raw > 0)
            parsed_art.token_buffer.getToken(TokenIndex.fromInt(tok_raw - 1)).kind
        else
            .eof;
        const next_kind: TokenKind = if (tok_raw + 1 < tok_total)
            parsed_art.token_buffer.getToken(TokenIndex.fromInt(tok_raw + 1)).kind
        else
            .eof;

        // Resolve dotted module/type paths (`cx.async.Poll`, `use cx.sys.wasi;`, `cx.ffi.CStr`):
        if (prev_kind == .dot or next_kind == .dot) {
            var rev_segs: [16]TokenIndex = undefined;
            var rev_len: usize = 0;
            var walk_tok: usize = tok_raw;
            while (rev_len < rev_segs.len) {
                const walk_id = TokenIndex.fromInt(@intCast(walk_tok));
                const walk_kind = parsed_art.token_buffer.getToken(walk_id).kind;
                if (!isIdentifierOrKeywordToken(walk_kind)) break;
                rev_segs[rev_len] = walk_id;
                rev_len += 1;
                if (walk_tok < 2) break;
                if (parsed_art.token_buffer.getToken(TokenIndex.fromInt(@intCast(walk_tok - 1))).kind != .dot) break;
                walk_tok -= 2;
            }

            if (rev_len >= 2 or (rev_len == 1 and next_kind == .dot)) {
                var cur_scope: ScopeId = mod_scope;
                var resolved_chain_sym: SymbolIndex = .none;
                var step_idx: usize = rev_len;
                while (step_idx > 0) {
                    step_idx -= 1;
                    const seg_tok = rev_segs[step_idx];
                    const seg_lex = symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, seg_tok);
                    const is_first_seg = (step_idx + 1 == rev_len);
                    resolved_chain_sym = .none;

                    if (is_first_seg and (std.mem.eql(u8, seg_lex, "cx") or
                        (session.options.is_internal_core and std.mem.eql(u8, seg_lex, "core"))))
                    {
                        const cx_scope = try session.db.symbol_table.ensureCxRootScope(&session.db.interner);
                        if (session.db.interner.lookup("cx")) |cx_id| {
                            resolved_chain_sym = session.db.symbol_table.lookupInScopeDirect(
                                session.db.symbol_table.prelude_scope,
                                cx_id,
                                NamespaceMask.VALUE_ONLY,
                            );
                        }
                        cur_scope = cx_scope;
                        continue;
                    } else if (is_first_seg and std.mem.eql(u8, seg_lex, "pkg")) {
                        cur_scope = session.db.symbol_table.resolveCallerPackageRootScope(file_id, mod_scope);
                        continue;
                    } else if (is_first_seg and std.mem.eql(u8, seg_lex, "self")) {
                        cur_scope = mod_scope;
                        continue;
                    } else if (is_first_seg and std.mem.eql(u8, seg_lex, "super")) {
                        const mod_rec = session.db.symbol_table.scope_arena.getScope(mod_scope);
                        cur_scope = if (!mod_rec.parent_module.isNone()) mod_rec.parent_module else mod_rec.parent;
                        continue;
                    }

                    const seg_name_id = session.db.interner.lookup(seg_lex) orelse break;
                    const seg_found: SymbolIndex = if (is_first_seg) blk_first: {
                        switch (session.db.symbol_table.lookupLexical(cur_scope, seg_name_id, NamespaceMask.ALL)) {
                            .found => |found_idx| break :blk_first found_idx,
                            else => break :blk_first .none,
                        }
                    } else if (!cur_scope.isNone())
                        session.db.symbol_table.lookupInScopeDirect(cur_scope, seg_name_id, NamespaceMask.ALL)
                    else
                        .none;

                    if (seg_found.isNone()) break;
                    resolved_chain_sym = seg_found;
                    const unwrapped_seg = session.db.symbol_table.unwrapAliasSymbolIdx(seg_found);
                    cur_scope = session.db.symbol_table.getSymbol(unwrapped_seg).target_scope;
                }

                if (!resolved_chain_sym.isNone()) {
                    result.symbol_index = resolved_chain_sym;
                    result.type_id = session.db.symbol_table.getSymbol(resolved_chain_sym).type_id;
                    return result;
                }
            }
        }

        const is_contextual_mod_kw = tok_rec.kind == .kw_async and
            (prev_kind == .dot or prev_kind == .kw_mod or prev_kind == .kw_use or prev_kind == .lbrace);
        if (isUserIdentifierToken(tok_rec.kind) or
            tok_rec.kind == .kw_self_val or
            tok_rec.kind == .kw_self_type or
            is_contextual_mod_kw)
        {
            if (session.db.interner.lookup(tok_lex)) |name_id| {
                const ns_mask: NamespaceMask = switch (tok_rec.kind) {
                    .type_ident => NamespaceMask.TYPE_OR_VALUE,
                    .const_ident => NamespaceMask.CONST_ONLY,
                    else => NamespaceMask.ALL,
                };
                switch (session.db.symbol_table.lookupLexical(mod_scope, name_id, ns_mask)) {
                    .found => |found_sym| {
                        result.symbol_index = found_sym;
                        result.type_id = session.db.symbol_table.getSymbol(found_sym).type_id;
                    },
                    else => {},
                }
            }
        }
    }
    return result;
}

// ----------- Hover (Signature + DR-17 4.4 + Trivia) -----------

/// Joins extracted doc-comment lines into a single `\n`-separated Markdown slice inside `arena_alloc`.
fn joinDocLines(arena_alloc: std.mem.Allocator, lines: []const []const u8) ![]const u8 {
    if (lines.len == 0) return "";
    var joined: std.ArrayListUnmanaged(u8) = .empty;
    for (lines, 0..) |line_str, i| {
        if (i > 0) try joined.append(arena_alloc, '\n');
        try joined.appendSlice(arena_alloc, line_str);
    }
    return joined.items;
}

/// Advances `start_offset` past an optional UTF-8 BOM (`0xEF 0xBB 0xBF`), `#!` shebang, and `---` script frontmatter.
fn skipLeadingBomAndShebang(src: []const u8) usize {
    var cursor: usize = 0;
    if (src.len >= 3 and src[0] == 0xEF and src[1] == 0xBB and src[2] == 0xBF) {
        cursor = 3;
    }
    if (cursor + 1 < src.len and src[cursor] == '#' and src[cursor + 1] == '!') {
        while (cursor < src.len and src[cursor] != '\n') : (cursor += 1) {}
        if (cursor < src.len and src[cursor] == '\n') cursor += 1;
    }
    // Skip optional `---` script frontmatter block before top-of-file `/#` module docs:
    var probe = cursor;
    while (probe < src.len and (src[probe] == ' ' or src[probe] == '\t' or src[probe] == '\r' or src[probe] == '\n')) : (probe += 1) {}
    if (probe + 3 <= src.len and std.mem.eql(u8, src[probe .. probe + 3], "---")) {
        var fm_line_end = probe + 3;
        while (fm_line_end < src.len and (src[fm_line_end] == ' ' or src[fm_line_end] == '\t' or src[fm_line_end] == '\r')) : (fm_line_end += 1) {}
        if (fm_line_end == src.len or src[fm_line_end] == '\n') {
            var scan = if (fm_line_end < src.len) fm_line_end + 1 else src.len;
            while (scan < src.len) {
                var close_end = scan;
                while (close_end < src.len and src[close_end] != '\n') : (close_end += 1) {}
                const trimmed_close = std.mem.trim(u8, src[scan..close_end], " \t\r");
                scan = if (close_end < src.len) close_end + 1 else src.len;
                if (std.mem.eql(u8, trimmed_close, "---")) {
                    cursor = scan;
                    break;
                }
            }
        }
    }
    return cursor;
}

/// Extracts contiguous top-of-file `/#` module doc comments from `mod_fid` (or `""` if none exist at the top).
fn extractFileModuleDocComments(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    mod_fid: FileId,
) ![]const u8 {
    if (mod_fid.isNone()) return "";
    const src = getLiveDocumentSource(session, mod_fid) orelse return "";
    var cursor = skipLeadingBomAndShebang(src);
    var doc_lines: std.ArrayListUnmanaged([]const u8) = .empty;

    while (cursor < src.len) {
        var line_end = cursor;
        while (line_end < src.len and src[line_end] != '\n') : (line_end += 1) {}
        const raw_line = std.mem.trimEnd(u8, src[cursor..line_end], "\r");
        const trimmed_start = std.mem.trimStart(u8, raw_line, " \t");
        if (trimmed_start.len == 0 and doc_lines.items.len == 0) {
            cursor = if (line_end < src.len) line_end + 1 else src.len;
            continue;
        }
        if (!std.mem.startsWith(u8, trimmed_start, "/#")) break;

        var content_slice = trimmed_start[2..];
        if (content_slice.len > 0 and content_slice[0] == ' ') {
            content_slice = content_slice[1..];
        }
        try doc_lines.append(arena_alloc, content_slice);
        cursor = if (line_end < src.len) line_end + 1 else src.len;
    }
    return joinDocLines(arena_alloc, doc_lines.items);
}

/// Resolves the backing `.cx` `FileId` for a file-backed `.module_sym` (or `.none` for inline `mod { … }`).
fn resolveModuleBackingFileId(
    session: *LspSession,
    target: CursorTarget,
    sym: SymbolRecord,
) FileId {
    if (!target.external_mod_file_id.isNone()) return target.external_mod_file_id;

    // Check whether `sym` is an inline `mod foo { … }` block (`rhs.tag == .extra`):
    if (!sym.decl_span.file_id.isNone()) {
        const decl_fid = sym.decl_span.file_id;
        _ = session.db.parseCst(decl_fid) catch {};
        if (session.db.parsed_artifacts.getPtr(decl_fid.asInt())) |parsed_art| {
            var check_ast = sym.ast_node;
            if (!sym.def_id.isNone() and sym.def_id.fileId() == decl_fid) {
                if (session.db.extractItemTree(decl_fid) catch null) |tree| {
                    if (tree.getEntry(sym.def_id)) |live_entry| {
                        check_ast = live_entry.ast_node;
                    }
                }
            }
            if (!check_ast.isNone() and check_ast.asInt() < parsed_art.ast_arena.countNodes()) {
                const mod_ast = parsed_art.ast_arena.getNode(check_ast);
                if (mod_ast.tag == .mod_decl and mod_ast.rhs.tag == .extra) {
                    return .none;
                }
            }
        }
        if (!sym.name.isNone()) {
            const ext_key: u64 = (@as(u64, decl_fid.asInt()) << 32) | @as(u64, sym.name.asInt());
            if (session.db.external_mod_files.get(ext_key)) |bound_fid| {
                return bound_fid;
            }
        }
    }

    if (!sym.target_scope.isNone() and sym.target_scope.asInt() < session.db.symbol_table.scope_arena.countScopes()) {
        const scope_rec = session.db.symbol_table.scope_arena.getScope(sym.target_scope);
        if (scope_rec.owner_def_id.isNone() and !scope_rec.file_id.isNone()) {
            return scope_rec.file_id;
        }
    }

    // Built-in `cx` / `core` root or `cx.<submod>` bridge fallback via `root_module_files` + `external_mod_files`:
    if (session.db.interner.lookup("core") orelse session.db.interner.lookup("cx")) |root_id| {
        if (session.db.root_module_files.get(root_id.asInt())) |core_root_fid| {
            if (std.mem.eql(u8, sym.name_text, "cx") or std.mem.eql(u8, sym.name_text, "core")) {
                return core_root_fid;
            }
            if (!sym.name.isNone()) {
                const sub_key: u64 = (@as(u64, core_root_fid.asInt()) << 32) | @as(u64, sym.name.asInt());
                if (session.db.external_mod_files.get(sub_key)) |sub_fid| {
                    return sub_fid;
                }
            }
        }
    }
    return .none;
}

/// Extracts outer `///` doc comments attached to an inline `mod foo { … }` declaration (`ADR-23A`).
fn extractInlineModDocComments(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    decl_span: Span,
    sym_def_id: DefId,
    fallback_cst_node: CstNodeIndex,
) ![]const u8 {
    return extractDeclarationDocComments(session, arena_alloc, decl_span, sym_def_id, fallback_cst_node);
}

/// Extracts outer `///` doc comment lines attached to `decl_span` (immune to `TRIVIA_FLAG_COALESCED` & `//!` headers).
fn extractDeclarationDocComments(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    decl_span: Span,
    sym_def_id: DefId,
    fallback_cst_node: CstNodeIndex,
) ![]const u8 {
    if (decl_span.file_id.isNone() or !session.db.source_inputs.contains(decl_span.file_id.asInt())) return "";
    const decl_fid = decl_span.file_id;
    const src = getLiveDocumentSource(session, decl_fid) orelse return "";
    _ = session.db.parseCst(decl_fid) catch return "";
    const item_tree_opt = session.db.extractItemTree(decl_fid) catch null;
    const parsed_art = session.db.parsed_artifacts.getPtr(decl_fid.asInt()) orelse return "";
    const tok_count = parsed_art.token_buffer.countTokens();
    if (tok_count == 0) return "";

    // Resolve live `ItemTreeEntry.cst_node` for `sym_def_id` so Early-Cutoff body edits never read stale CST indices:
    const cst_node_count = parsed_art.cst_arena.countNodes();
    var live_cst_node: CstNodeIndex = .none;
    if (!sym_def_id.isNone() and sym_def_id.fileId() == decl_fid) {
        if (item_tree_opt) |item_tree| {
            if (item_tree.getEntry(sym_def_id)) |live_entry| {
                if (!live_entry.cst_node.isNone() and live_entry.cst_node.asInt() < cst_node_count) {
                    live_cst_node = live_entry.cst_node;
                }
            }
        }
    } else if (!fallback_cst_node.isNone() and fallback_cst_node.asInt() < cst_node_count) {
        if (computeCstSubtreeByteSpan(
            decl_fid,
            &parsed_art.token_buffer,
            &parsed_art.cst_arena,
            fallback_cst_node,
        )) |fallback_span| {
            if (decl_span.start_byte >= fallback_span.start_byte and
                decl_span.end_byte <= fallback_span.end_byte)
            {
                live_cst_node = fallback_cst_node;
            }
        }
    }

    // Locate the first token of the declaration item (including `@attributes` and `pub`):
    var first_tok: TokenIndex = .none;
    if (!live_cst_node.isNone() and live_cst_node.asInt() < cst_node_count) {
        const start_idx: usize = live_cst_node.asInt();
        const end_idx = @min(
            start_idx + @max(@as(usize, parsed_art.cst_arena.getNode(live_cst_node).subtree_size), 1),
            cst_node_count,
        );
        var cur = start_idx;
        while (cur < end_idx) : (cur += 1) {
            const leaf = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (leaf.subtree_size <= 1 and !leaf.flags.is_missing_or_injected and
                !leaf.token.isNone() and leaf.token.asInt() < tok_count and
                !parsed_art.token_buffer.getToken(leaf.token).flags.is_synthesized)
            {
                first_tok = leaf.token;
                break;
            }
        }
    }
    if (first_tok.isNone()) {
        first_tok = findExactTokenAtByteOffset(&parsed_art.token_buffer, decl_span.start_byte) orelse return "";
        // Walk backward over same-declaration modifiers (`pub`, `fn`, `struct`, `const`, `async`, `unsafe`):
        while (first_tok.asInt() > 0) {
            const prev_id = TokenIndex.fromInt(first_tok.asInt() - 1);
            const prev_rec = parsed_art.token_buffer.getToken(prev_id);
            if (prev_rec.flags.is_synthesized) break;
            const is_header_mod = switch (prev_rec.kind) {
                .kw_pub,
                .kw_fn,
                .kw_struct,
                .kw_enum,
                .kw_union,
                .kw_trait,
                .kw_const,
                .kw_type,
                .kw_async,
                .kw_unsafe,
                .kw_comptime,
                .kw_bit_field,
                .kw_mod,
                => true,
                else => false,
            };
            if (!is_header_mod) break;
            first_tok = prev_id;
        }
    }

    const region_end: usize = @min(@as(usize, parsed_art.token_buffer.getToken(first_tok).byte_offset), src.len);
    var prev_real_end: ?usize = null;
    var back_idx: usize = first_tok.asInt();
    while (back_idx > 0) {
        back_idx -= 1;
        const cand_rec = parsed_art.token_buffer.getToken(TokenIndex.fromInt(@intCast(back_idx)));
        if (!cand_rec.flags.is_synthesized and cand_rec.byte_len > 0) {
            prev_real_end = @min(@as(usize, cand_rec.byte_offset) + @as(usize, cand_rec.byte_len), region_end);
            break;
        }
    }

    // Advance `region_start` past any trailing trivia on `prev_real_tok`'s closing line:
    const region_start: usize = if (prev_real_end) |prev_end| blk_start: {
        var skip_cur = prev_end;
        while (skip_cur < region_end) {
            if (src[skip_cur] == '\n') {
                skip_cur += 1;
                break;
            }
            if (src[skip_cur] == '/' and skip_cur + 1 < region_end) {
                if (src[skip_cur + 1] == '/' or src[skip_cur + 1] == '|' or src[skip_cur + 1] == '#') {
                    while (skip_cur < region_end and src[skip_cur] != '\n') : (skip_cur += 1) {}
                    if (skip_cur < region_end and src[skip_cur] == '\n') skip_cur += 1;
                    break;
                }
            }
            skip_cur += 1;
        }
        break :blk_start skip_cur;
    } else @min(skipLeadingBomAndShebang(src), region_end);

    if (region_start >= region_end) return "";

    // Scan `[region_start, region_end)` directly: keep only the contiguous `/|` block attached to `first_tok`.
    var doc_lines: std.ArrayListUnmanaged([]const u8) = .empty;
    var consecutive_newlines: u32 = 0;
    var cursor: usize = region_start;
    while (cursor < region_end) {
        const byte_val = src[cursor];
        if (byte_val == ' ' or byte_val == '\t' or byte_val == '\r') {
            cursor += 1;
        } else if (byte_val == '\n') {
            consecutive_newlines += 1;
            if (consecutive_newlines >= 2 and doc_lines.items.len > 0) {
                doc_lines.clearRetainingCapacity();
            }
            cursor += 1;
        } else if (byte_val == '/' and cursor + 1 < region_end and
            (src[cursor + 1] == '|' or src[cursor + 1] == '/' or src[cursor + 1] == '#'))
        {
            const com_start = cursor;
            while (cursor < region_end and src[cursor] != '\n') : (cursor += 1) {}
            const raw_comment = std.mem.trimEnd(u8, src[com_start..cursor], "\r\n");
            if (std.mem.startsWith(u8, raw_comment, "/|")) {
                consecutive_newlines = 0;
                var content_slice = raw_comment[2..];
                if (content_slice.len > 0 and content_slice[0] == ' ') {
                    content_slice = content_slice[1..];
                }
                try doc_lines.append(arena_alloc, content_slice);
            } else {
                // `/#` module header or `//` / `////` separator comment breaks any earlier doc block:
                doc_lines.clearRetainingCapacity();
                consecutive_newlines = 0;
            }
        } else {
            cursor += 1;
        }
    }
    return joinDocLines(arena_alloc, doc_lines.items);
}

/// Formats a function or method signature string (with generics and `/` / `*` parameter zones) into `writer`.
fn writeFormattedFnSignature(
    session: *LspSession,
    sym_idx: SymbolIndex,
    sym: SymbolRecord,
    is_stripping_self_receiver: bool,
    writer: *std.Io.Writer,
    param_labels_out: ?*std.ArrayListUnmanaged([]const u8),
    arena_alloc: std.mem.Allocator,
) !void {
    if (!is_stripping_self_receiver and sym.visibility != .private) {
        try writer.print("{s} ", .{sym.visibility.asKeywordSlice()});
    }
    if (sym.flags.is_comptime) try writer.writeAll("comptime ");
    const sig_view_opt = if (!sym.type_id.isPrimitiveOrSentinel())
        session.db.type_pool.getFnSignatureView(sym.type_id)
    else
        null;
    if (sig_view_opt) |sig_v| {
        if (sig_v.is_async) try writer.writeAll("async ");
    }
    if (sym.flags.is_extern) try writer.writeAll("extern ");
    try writer.print("fn {s}", .{sym.name_text});

    const gen_specs = session.db.symbol_table.getGenericParamSpecs(sym_idx);
    if (gen_specs.len > 0) {
        try writer.writeByte('[');
        for (gen_specs, 0..) |gspec, i| {
            if (i > 0) try writer.writeAll(", ");
            if (gspec.is_const) try writer.writeAll("const ");
            try writer.writeAll(gspec.name_text);
        }
        try writer.writeByte(']');
    }

    try writer.writeByte('(');
    const param_specs = session.db.symbol_table.getFnParamSpecs(sym_idx);
    const arity: usize = if (sig_view_opt) |sv| sv.paramCount() else param_specs.len;
    const start_param: usize = if (is_stripping_self_receiver and param_specs.len > 0 and
        std.mem.eql(u8, param_specs[0].name_text, "self"))
        1
    else
        0;

    var has_emitted_slash = false;
    var has_emitted_star = false;
    var written_items: usize = 0;
    var type_buf: [512]u8 = undefined;

    var p_idx: usize = start_param;
    while (p_idx < @max(arity, param_specs.len)) : (p_idx += 1) {
        const p_spec: FnParamSpec = if (p_idx < param_specs.len) param_specs[p_idx] else .{};
        if (p_idx > start_param and !has_emitted_slash and
            p_idx > 0 and p_idx - 1 < param_specs.len and
            param_specs[p_idx - 1].is_positional_only and !p_spec.is_positional_only)
        {
            if (written_items > 0) try writer.writeAll(", ");
            try writer.writeByte('/');
            written_items += 1;
            has_emitted_slash = true;
        }
        if (!has_emitted_star and p_spec.is_keyword_only) {
            if (written_items > 0) try writer.writeAll(", ");
            try writer.writeByte('*');
            written_items += 1;
            has_emitted_star = true;
        }

        if (written_items > 0) try writer.writeAll(", ");
        var one_param_buf = std.Io.Writer.Allocating.init(arena_alloc);
        const param_writer = &one_param_buf.writer;

        if (p_spec.is_variadic) {
            try param_writer.writeAll("...");
        } else {
            const p_mode: ParamMode = if (sig_view_opt != null and p_idx < sig_view_opt.?.paramCount())
                sig_view_opt.?.getParamMode(p_idx)
            else
                .let_mode;
            const p_ty: TypeId = if (sig_view_opt != null and p_idx < sig_view_opt.?.paramCount())
                sig_view_opt.?.getParamType(p_idx)
            else
                .err_ty;

            if (std.mem.eql(u8, p_spec.name_text, "self")) {
                switch (p_mode) {
                    .sink_mode => try param_writer.writeAll("own self"),
                    .set_mode => try param_writer.writeAll("&out self"),
                    .inout_mode => try param_writer.writeAll("&mut self"),
                    .let_mode => {
                        if (!p_ty.isPrimitiveOrSentinel()) {
                            const p_tag = session.db.type_pool.getTag(p_ty);
                            if (p_tag == .mut_ref_ty) {
                                try param_writer.writeAll("&mut self");
                            } else if (p_tag == .ref_ty) {
                                try param_writer.writeAll("&self");
                            } else {
                                try param_writer.writeAll("self");
                            }
                        } else {
                            try param_writer.writeAll("self");
                        }
                    },
                }
            } else {
                if (p_spec.is_local_var) try param_writer.writeAll("var ");
                if (p_spec.name_text.len > 0) {
                    try param_writer.print("{s}: ", .{p_spec.name_text});
                } else {
                    try param_writer.writeAll("_: ");
                }
                switch (p_mode) {
                    .sink_mode => try param_writer.writeAll("own "),
                    .set_mode => try param_writer.writeAll("&out "),
                    .inout_mode => {
                        if (p_ty.isPrimitiveOrSentinel() or session.db.type_pool.getTag(p_ty) != .mut_ref_ty) {
                            try param_writer.writeAll("&mut ");
                        }
                    },
                    .let_mode => {},
                }
                const formatted_pty = session.db.type_pool.formatType(p_ty, &session.db.symbol_table, &type_buf);
                try param_writer.writeAll(formatted_pty);
                if (p_spec.has_default) {
                    try param_writer.writeAll(" = …");
                }
            }
        }

        const param_str = one_param_buf.written();
        try writer.writeAll(param_str);
        if (param_labels_out) |out_labels| {
            try out_labels.append(arena_alloc, param_str);
        }
        written_items += 1;
    }
    if (!has_emitted_slash and param_specs.len > start_param and
        param_specs[param_specs.len - 1].is_positional_only)
    {
        if (written_items > 0) try writer.writeAll(", ");
        try writer.writeByte('/');
    }
    try writer.writeByte(')');

    if (sig_view_opt) |sv| {
        if (sv.ret_ty != .unit_ty and !sv.ret_ty.isError()) {
            const formatted_ret = session.db.type_pool.formatType(sv.ret_ty, &session.db.symbol_table, &type_buf);
            try writer.print(" -> {s}", .{formatted_ret});
        }
    }
}

/// Appends the compact CommonMark `DR-17` §4.4 contract, capability, stack, and non-trivial provenance footer.
fn appendFnHoverContractBullets(
    session: *LspSession,
    sym_idx: SymbolIndex,
    sym: SymbolRecord,
    md_writer: *std.Io.Writer,
) !void {
    var summary_opt: ?FnRegionSummary = null;
    if (!sym.def_id.isNone()) {
        summary_opt = session.db.getSastSummaryProj(sym.def_id) catch null;
    } else if (!sym.owner_def_id.isNone()) {
        _ = session.db.verifySastMir(sym.owner_def_id) catch {};
        summary_opt = session.db.sast_sym_summaries.get(sym_idx.asInt());
    }
    const summary = summary_opt orelse return;
    const inferred_eff = summary.inferredEffects();
    const eff_bits = inferred_eff.asBits();

    // [1] Format compact contract & capability badge line:
    const alloc_status: []const u8 = if (sym.contract_flags.is_no_alloc or !inferred_eff.alloc)
        "✓ `@no_alloc`"
    else
        "⚠ allocates";

    const panic_status: []const u8 = if (sym.contract_flags.is_no_panic or !inferred_eff.may_panic)
        "✓ `@no_panic`"
    else
        "⚠ may panic";

    const block_status: []const u8 = if (sym.contract_flags.is_no_block or
        !inferred_eff.hasAnyBits(EffectCapabilityMask.BLOCKING_BITS))
        "✓ `@no_block`"
    else
        "⚠ may block";

    try md_writer.print(
        "\n\n---\n\n{s} · {s} · {s} · ",
        .{ alloc_status, panic_status, block_status },
    );

    if (eff_bits == 0) {
        try md_writer.writeAll("**caps:** none (pure)");
    } else {
        try md_writer.writeAll("**caps:** `[");
        var cap_written: usize = 0;
        for (CAPABILITY_DISPLAY_TABLE) |cap_entry| {
            if ((eff_bits & cap_entry.bit) != 0) {
                if (cap_written > 0) try md_writer.writeAll(", ");
                try md_writer.writeAll(cap_entry.label);
                cap_written += 1;
            }
        }
        try md_writer.writeAll("]`");
    }

    // [2] Format compact stack & non-trivial provenance line:
    if (summary.max_subtree_bytes == FnRegionSummary.STACK_UNBOUNDED or
        summary.contractsScratch().is_scc_recursive)
    {
        try md_writer.print(
            "\n\n**stack:** `{d} B` own · unbounded (recursive)",
            .{summary.own_frame_bytes},
        );
    } else {
        try md_writer.print(
            "\n\n**stack:** `{d} B` own · `{d} B` max",
            .{ summary.own_frame_bytes, summary.max_subtree_bytes },
        );
        if (sym.contract_flags.has_max_stack) {
            try md_writer.print(" (budget: {d} B)", .{sym.max_stack_bytes});
        }
    }

    if (summary.ret_provenance_mask != 0 or summary.consumed_param_mask != 0) {
        if (summary.ret_provenance_mask != 0) {
            try md_writer.writeAll(" · **borrows:** param");
            var bit_i: u6 = 0;
            while (true) : (bit_i += 1) {
                if ((summary.ret_provenance_mask & (@as(u64, 1) << bit_i)) != 0) {
                    try md_writer.print(" `#{d}`", .{bit_i});
                }
                if (bit_i == 63) break;
            }
        }
        if (summary.consumed_param_mask != 0) {
            try md_writer.writeAll(" · **consumes:** param");
            var bit_j: u6 = 0;
            while (bit_j < 32) : (bit_j += 1) {
                if ((summary.consumed_param_mask & (@as(u32, 1) << @intCast(bit_j))) != 0) {
                    try md_writer.print(" `#{d}`", .{bit_j});
                }
            }
        }
    }
}

/// Formats a hover response JSON-RPC frame for `(hover_span, markdown_text)` and flushes `out_writer`.
fn writeMarkdownHoverFrame(
    session: *LspSession,
    fid: FileId,
    hover_span: Span,
    markdown_text: []const u8,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const hover_range = spanToLspRange(session, fid, hover_span);
    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":");
    try writeJsonString(body_writer, markdown_text);
    try body_writer.writeAll("},\"range\":");
    try writeLspRangeJson(body_writer, hover_range);
    try body_writer.writeAll("}}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Unwraps reference/pointer layers around `raw_ty` so `.optional_ty`, `.result_ty`, or `.enum_ty` can be inspected.
fn unwrapHoverValueType(pool: *const InternPool, raw_ty: TypeId) TypeId {
    var cur_ty = raw_ty;
    var depth: u32 = 0;
    while (!cur_ty.isError() and !cur_ty.isPrimitiveOrSentinel() and depth < 16) : (depth += 1) {
        const node = pool.getNode(cur_ty);
        if (node.tag == .ref_ty or node.tag == .mut_ref_ty) {
            cur_ty = TypeId.fromInt(node.lhs);
        } else {
            break;
        }
    }
    return cur_ty;
}

/// Handles `textDocument/hover`: renders ` ```corex ` signature + `DR-17` §4.4 bullets + `///`/`//!` docs.
fn handleHoverRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    var pos = extractJsonPosition(params.getField("position") orelse JsonValue{ .null_val = {} }) orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing position");
    };

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) {
        return writeNullResultFrame(session, out_writer, rpc_id);
    }

    // [1] Literal suppression, `&self`/`&mut self`/`own self` redirect, and `@attribute`/`@intrinsic` hover:
    var receiver_prefix_span: ?Span = null;
    if (getLiveDocumentSource(session, fid)) |live_src| {
        const parsed_cst = try session.db.parseCst(fid);
        const cursor_byte = lspPositionToByteOffset(session, fid, pos);
        const raw_tok = findTokenAtCursorByte(&parsed_cst.token_buffer, cursor_byte);
        const tok_count = parsed_cst.token_buffer.countTokens();
        if (!raw_tok.isNone() and raw_tok.asInt() < tok_count) {
            const cur_rec = parsed_cst.token_buffer.getToken(raw_tok);
            switch (cur_rec.kind) {
                .int_lit,
                .float_lit,
                .string_lit,
                .char_lit,
                .byte_lit,
                .byte_string_lit,
                .kw_true,
                .kw_false,
                => return writeNullResultFrame(session, out_writer, rpc_id),
                .amp, .kw_mut, .kw_own => {
                    var scan_i: usize = raw_tok.asInt();
                    var start_i: usize = scan_i;
                    if (cur_rec.kind == .kw_mut and start_i > 0 and
                        parsed_cst.token_buffer.getToken(TokenIndex.fromInt(@intCast(start_i - 1))).kind == .amp)
                    {
                        start_i -= 1;
                    }
                    while (scan_i + 1 < tok_count) : (scan_i += 1) {
                        const nxt_k = parsed_cst.token_buffer.getToken(TokenIndex.fromInt(@intCast(scan_i + 1))).kind;
                        if (nxt_k == .kw_mut) continue;
                        if (nxt_k == .kw_self_val) {
                            const self_tok_id = TokenIndex.fromInt(@intCast(scan_i + 1));
                            const start_rec = parsed_cst.token_buffer.getToken(TokenIndex.fromInt(@intCast(start_i)));
                            const self_rec = parsed_cst.token_buffer.getToken(self_tok_id);
                            receiver_prefix_span = Span.init(
                                fid,
                                start_rec.byte_offset,
                                self_rec.byte_offset +| self_rec.byte_len,
                            );
                            pos = byteOffsetToLspPosition(session, fid, self_rec.byte_offset);
                        }
                        break;
                    }
                },
                .prim_type => {
                    const prim_lex = symbol_resolver.extractTokenSlice(live_src, &parsed_cst.token_buffer, raw_tok);
                    if (BUILTIN_PRIM_HOVER_MAP.get(prim_lex)) |prim_spec| {
                        const prim_md = try std.fmt.allocPrint(
                            arena_alloc,
                            "```corex\n{s}\n```\n\n{s}",
                            .{ prim_spec.signature, prim_spec.summary },
                        );
                        const prim_span = parsed_cst.token_buffer.getTokenSpan(fid, raw_tok);
                        return writeMarkdownHoverFrame(session, fid, prim_span, prim_md, out_writer, rpc_id);
                    }
                },
                .fmt_string_lit => {
                    _ = try session.db.resolveSignatures(fid);
                    const item_tree = try session.db.extractItemTree(fid);
                    const fmt_span = parsed_cst.token_buffer.getTokenSpan(fid, raw_tok);
                    for (item_tree.entries) |entry| {
                        if (entry.kind == .mod_decl or entry.kind == .use_decl or entry.kind == .ffi_extern_block) {
                            continue;
                        }
                        const live_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse break;
                        const entry_span = computeCstSubtreeByteSpan(
                            fid,
                            &live_art.token_buffer,
                            &live_art.cst_arena,
                            entry.cst_node,
                        ) orelse continue;
                        if (fmt_span.start_byte < entry_span.start_byte or fmt_span.start_byte > entry_span.end_byte) {
                            continue;
                        }
                        if (try session.db.getDefSideTables(entry.def_id)) |side_tables| {
                            const refreshed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse break;
                            const hole_hit = findInterpHoleTokenAtByte(
                                side_tables,
                                refreshed_art,
                                raw_tok,
                                @intCast(@min(cursor_byte, std.math.maxInt(u32))),
                            ) orelse return writeNullResultFrame(session, out_writer, rpc_id);
                            const htok = hole_hit.token_info;
                            const htok_start = hole_hit.fmt_tok_base +| htok.rel_byte;
                            const htok_end = htok_start +| @as(u32, htok.byte_len);
                            const clamped_start = @min(@as(usize, htok_start), live_src.len);
                            const clamped_end = @min(@max(@as(usize, htok_end), clamped_start), live_src.len);
                            const htok_lex = live_src[clamped_start..clamped_end];
                            switch (htok.kind) {
                                .int_lit,
                                .float_lit,
                                .string_lit,
                                .char_lit,
                                .byte_lit,
                                .byte_string_lit,
                                .kw_true,
                                .kw_false,
                                => return writeNullResultFrame(session, out_writer, rpc_id),
                                .prim_type => {
                                    if (BUILTIN_PRIM_HOVER_MAP.get(htok_lex)) |prim_spec| {
                                        const prim_md = try std.fmt.allocPrint(
                                            arena_alloc,
                                            "```corex\n{s}\n```\n\n{s}",
                                            .{ prim_spec.signature, prim_spec.summary },
                                        );
                                        return writeMarkdownHoverFrame(
                                            session,
                                            fid,
                                            Span.init(fid, htok_start, htok_end),
                                            prim_md,
                                            out_writer,
                                            rpc_id,
                                        );
                                    }
                                },
                                else => {},
                            }
                            var intr_at_idx: ?usize = null;
                            var intr_name_idx: ?usize = null;
                            if (htok.kind == .at and hole_hit.token_idx_in_hole + 1 < hole_hit.hole.tokens.len and
                                isIdentifierOrKeywordToken(hole_hit.hole.tokens[hole_hit.token_idx_in_hole + 1].kind))
                            {
                                intr_at_idx = hole_hit.token_idx_in_hole;
                                intr_name_idx = hole_hit.token_idx_in_hole + 1;
                            } else if (hole_hit.token_idx_in_hole > 0 and
                                isIdentifierOrKeywordToken(htok.kind) and
                                hole_hit.hole.tokens[hole_hit.token_idx_in_hole - 1].kind == .at)
                            {
                                intr_at_idx = hole_hit.token_idx_in_hole - 1;
                                intr_name_idx = hole_hit.token_idx_in_hole;
                            }
                            if (intr_at_idx != null and intr_name_idx != null) {
                                const at_info = hole_hit.hole.tokens[intr_at_idx.?];
                                const nm_info = hole_hit.hole.tokens[intr_name_idx.?];
                                const nm_start = hole_hit.fmt_tok_base +| nm_info.rel_byte;
                                const nm_end = nm_start +| @as(u32, nm_info.byte_len);
                                const nm_clamped_start = @min(@as(usize, nm_start), live_src.len);
                                const nm_clamped_end = @min(@max(@as(usize, nm_end), nm_clamped_start), live_src.len);
                                const nm_lex = live_src[nm_clamped_start..nm_clamped_end];
                                if (INTRINSIC_HOVER_MAP.get(nm_lex)) |intr_spec| {
                                    const intr_md = try std.fmt.allocPrint(
                                        arena_alloc,
                                        "```corex\n{s}\n```\n\n{s}",
                                        .{ intr_spec.signature, intr_spec.summary },
                                    );
                                    const full_intr_span = Span.init(
                                        fid,
                                        hole_hit.fmt_tok_base +| at_info.rel_byte,
                                        nm_end,
                                    );
                                    return writeMarkdownHoverFrame(
                                        session,
                                        fid,
                                        full_intr_span,
                                        intr_md,
                                        out_writer,
                                        rpc_id,
                                    );
                                }
                            }
                        }
                        break;
                    }
                },
                else => {},
            }

            var at_tok: TokenIndex = .none;
            var name_tok: TokenIndex = .none;
            if (cur_rec.kind == .at and raw_tok.asInt() + 1 < tok_count) {
                const next_id = TokenIndex.fromInt(raw_tok.asInt() + 1);
                if (isIdentifierOrKeywordToken(parsed_cst.token_buffer.getToken(next_id).kind)) {
                    at_tok = raw_tok;
                    name_tok = next_id;
                }
            } else if (raw_tok.asInt() > 0 and isIdentifierOrKeywordToken(cur_rec.kind)) {
                const prev_id = TokenIndex.fromInt(raw_tok.asInt() - 1);
                if (parsed_cst.token_buffer.getToken(prev_id).kind == .at) {
                    at_tok = prev_id;
                    name_tok = raw_tok;
                }
            }

            if (!at_tok.isNone() and !name_tok.isNone()) {
                const at_rec = parsed_cst.token_buffer.getToken(at_tok);
                const name_rec = parsed_cst.token_buffer.getToken(name_tok);
                const name_lex = symbol_resolver.extractTokenSlice(live_src, &parsed_cst.token_buffer, name_tok);
                const maybe_at_spec: ?HoverDocSpec = INTRINSIC_HOVER_MAP.get(name_lex) orelse
                    BUILTIN_ATTR_HOVER_MAP.get(name_lex);
                if (maybe_at_spec) |doc_spec| {
                    const doc_md = try std.fmt.allocPrint(
                        arena_alloc,
                        "```corex\n{s}\n```\n\n{s}",
                        .{ doc_spec.signature, doc_spec.summary },
                    );
                    const full_at_span = Span.init(fid, at_rec.byte_offset, name_rec.byte_offset +| name_rec.byte_len);
                    return writeMarkdownHoverFrame(session, fid, full_at_span, doc_md, out_writer, rpc_id);
                }
                if (cur_rec.kind == .at) {
                    pos = byteOffsetToLspPosition(session, fid, name_rec.byte_offset);
                }
            }

            if (try tryBuildLintSelectorHover(
                arena_alloc,
                fid,
                live_src,
                &parsed_cst.token_buffer,
                &parsed_cst.cst_arena,
                cursor_byte,
            )) |lint_hover| {
                return writeMarkdownHoverFrame(
                    session,
                    fid,
                    lint_hover.span,
                    lint_hover.markdown,
                    out_writer,
                    rpc_id,
                );
            }
        }
    }

    var target = try resolveCursorTarget(session, fid, pos);
    if (receiver_prefix_span) |full_recv_span| {
        target.token_span = full_recv_span;
    }
    if (target.token_index.isNone()) {
        return writeNullResultFrame(session, out_writer, rpc_id);
    }

    // [1b] `self` / `&self` / `&mut self` / `own self` signature parameter & `Self` fallback:
    if (target.symbol_index.isNone() and !target.enclosing_def_id.isNone()) {
        if (session.db.parsed_artifacts.getPtr(fid.asInt())) |parsed_art| {
            const tok_rec = parsed_art.token_buffer.getToken(target.token_index);
            if (tok_rec.kind == .kw_self_val or tok_rec.kind == .kw_self_type) {
                if (session.db.symbol_table.def_to_symbol.get(target.enclosing_def_id.asInt())) |enc_sym_idx| {
                    const enc_sym = session.db.symbol_table.getSymbol(enc_sym_idx).*;
                    if (!enc_sym.owner_def_id.isNone()) {
                        if (session.db.symbol_table.def_to_symbol.get(enc_sym.owner_def_id.asInt())) |owner_idx| {
                            const owner_sym = session.db.symbol_table.getSymbol(owner_idx).*;
                            if (tok_rec.kind == .kw_self_val and !enc_sym.type_id.isPrimitiveOrSentinel()) {
                                if (session.db.type_pool.getFnSignatureView(enc_sym.type_id)) |sig_v| {
                                    if (sig_v.paramCount() > 0) {
                                        var recv_buf: [256]u8 = undefined;
                                        const recv_ty_str = session.db.type_pool.formatType(
                                            sig_v.getParamType(0),
                                            &session.db.symbol_table,
                                            &recv_buf,
                                        );
                                        const p_specs = session.db.symbol_table.getFnParamSpecs(enc_sym_idx);
                                        const var_prefix: []const u8 = if (p_specs.len > 0 and p_specs[0].is_local_var)
                                            "var "
                                        else
                                            "";
                                        const nom_span = session.db.resolveLiveSymbolDeclSpan(owner_idx) catch owner_sym.decl_span;
                                        const owner_doc = try extractDeclarationDocComments(
                                            session,
                                            arena_alloc,
                                            nom_span,
                                            owner_sym.def_id,
                                            owner_sym.cst_node,
                                        );
                                        const self_md = if (owner_doc.len > 0)
                                            try std.fmt.allocPrint(
                                                arena_alloc,
                                                "```corex\n{s}self: {s}\n```\n\n{s}",
                                                .{ var_prefix, recv_ty_str, owner_doc },
                                            )
                                        else
                                            try std.fmt.allocPrint(
                                                arena_alloc,
                                                "```corex\n{s}self: {s}\n```",
                                                .{ var_prefix, recv_ty_str },
                                            );
                                        return writeMarkdownHoverFrame(
                                            session,
                                            fid,
                                            target.token_span,
                                            self_md,
                                            out_writer,
                                            rpc_id,
                                        );
                                    }
                                }
                            }
                            target.symbol_index = owner_idx;
                            target.type_id = owner_sym.type_id;
                        }
                    }
                }
            }
        }
    }

    // [2] Built-in prelude `Option[T]` / `Result[T, E]` variant hover (`.Some`, `.None`, `.Ok`, `.Err`):
    if (target.symbol_index.isNone()) {
        if (getLiveDocumentSource(session, fid)) |live_src| {
            if (session.db.parsed_artifacts.getPtr(fid.asInt())) |parsed_art| {
                const tok_raw = target.token_index.asInt();
                const is_preceded_by_dot = if (target.resolved_token_kind != null)
                    (target.token_span.start_byte > 0 and
                        @as(usize, target.token_span.start_byte) <= live_src.len and
                        live_src[target.token_span.start_byte - 1] == '.')
                else
                    (tok_raw > 0 and tok_raw < parsed_art.token_buffer.countTokens() and
                        parsed_art.token_buffer.getToken(TokenIndex.fromInt(tok_raw - 1)).kind == .dot);
                if (is_preceded_by_dot) {
                    const sp_start = @min(@as(usize, target.token_span.start_byte), live_src.len);
                    const sp_end = @min(@max(@as(usize, target.token_span.end_byte), sp_start), live_src.len);
                    const var_lex = if (target.resolved_token_kind != null)
                        live_src[sp_start..sp_end]
                    else
                        symbol_resolver.extractTokenSlice(
                            live_src,
                            &parsed_art.token_buffer,
                            target.token_index,
                        );
                    if (BUILTIN_VARIANT_SET.has(var_lex)) {
                        var inner_buf_a: [256]u8 = undefined;
                        var inner_buf_b: [256]u8 = undefined;
                        const unwrapped_ty = unwrapHoverValueType(&session.db.type_pool, target.type_id);
                        var sig_line: []const u8 = "";
                        var summary_line: []const u8 = "";

                        if (std.mem.eql(u8, var_lex, "Some") or std.mem.eql(u8, var_lex, "None")) {
                            const inner_str: []const u8 = if (!unwrapped_ty.isError() and
                                !unwrapped_ty.isPrimitiveOrSentinel() and
                                session.db.type_pool.getNode(unwrapped_ty).tag == .optional_ty)
                                session.db.type_pool.formatType(
                                    TypeId.fromInt(session.db.type_pool.getNode(unwrapped_ty).lhs),
                                    &session.db.symbol_table,
                                    &inner_buf_a,
                                )
                            else
                                "T";
                            if (std.mem.eql(u8, var_lex, "Some")) {
                                sig_line = try std.fmt.allocPrint(
                                    arena_alloc,
                                    "Option[{s}].Some({s})",
                                    .{ inner_str, inner_str },
                                );
                                summary_line = "Present value variant of `Option[T]` (`T?`).";
                            } else {
                                sig_line = try std.fmt.allocPrint(arena_alloc, "Option[{s}].None", .{inner_str});
                                summary_line = "Absent value variant of `Option[T]` (`T?`).";
                            }
                        } else {
                            const has_res = !unwrapped_ty.isError() and
                                !unwrapped_ty.isPrimitiveOrSentinel() and
                                session.db.type_pool.getNode(unwrapped_ty).tag == .result_ty;
                            const ok_str: []const u8 = if (has_res)
                                session.db.type_pool.formatType(
                                    TypeId.fromInt(session.db.type_pool.getNode(unwrapped_ty).lhs),
                                    &session.db.symbol_table,
                                    &inner_buf_a,
                                )
                            else
                                "T";
                            const err_str: []const u8 = if (has_res)
                                session.db.type_pool.formatType(
                                    TypeId.fromInt(session.db.type_pool.getNode(unwrapped_ty).rhs),
                                    &session.db.symbol_table,
                                    &inner_buf_b,
                                )
                            else
                                "E";
                            if (std.mem.eql(u8, var_lex, "Ok")) {
                                sig_line = try std.fmt.allocPrint(
                                    arena_alloc,
                                    "Result[{s}, {s}].Ok({s})",
                                    .{ ok_str, err_str, ok_str },
                                );
                                summary_line = "Success payload variant of `Result[T, E]` (`T!E`).";
                            } else {
                                sig_line = try std.fmt.allocPrint(
                                    arena_alloc,
                                    "Result[{s}, {s}].Err({s})",
                                    .{ ok_str, err_str, err_str },
                                );
                                summary_line = "Error payload variant of `Result[T, E]` (`T!E`).";
                            }
                        }

                        const builtin_md = try std.fmt.allocPrint(
                            arena_alloc,
                            "```corex\n{s}\n```\n\n---\n\n{s}",
                            .{ sig_line, summary_line },
                        );
                        return writeMarkdownHoverFrame(session, fid, target.token_span, builtin_md, out_writer, rpc_id);
                    }
                }
            }
        }
    }

    if (target.symbol_index.isNone() and target.type_id.isError()) {
        return writeNullResultFrame(session, out_writer, rpc_id);
    }

    var md_alloc = std.Io.Writer.Allocating.init(arena_alloc);
    const mw = &md_alloc.writer;
    var type_buf: [512]u8 = undefined;

    const raw_sym_idx = target.symbol_index;
    const sym_idx = if (!raw_sym_idx.isNone())
        resolveLiveCanonicalSymbol(session, raw_sym_idx)
    else
        SymbolIndex.none;

    if (!sym_idx.isNone() and sym_idx.asInt() < session.db.symbol_table.countSymbols()) {
        const sym = session.db.symbol_table.getSymbol(sym_idx).*;
        if (sym.flags.is_builtin) {
            if (BUILTIN_PRIM_HOVER_MAP.get(sym.name_text)) |prim_spec| {
                const prim_md = try std.fmt.allocPrint(
                    arena_alloc,
                    "```corex\n{s}\n```\n\n{s}",
                    .{ prim_spec.signature, prim_spec.summary },
                );
                return writeMarkdownHoverFrame(session, fid, target.token_span, prim_md, out_writer, rpc_id);
            }
        }
        try mw.writeAll("```corex\n");
        switch (sym.kind) {
            .fn_sym => {
                try writeFormattedFnSignature(session, sym_idx, sym, false, mw, null, arena_alloc);
            },
            .overload_group_sym => {
                if (sym.target_symbol.asInt() < session.db.symbol_table.overload_sets.items.len) {
                    const ov_set = session.db.symbol_table.overload_sets.items[sym.target_symbol.asInt()];
                    for (ov_set.members.items, 0..) |mem_idx, i| {
                        if (i > 0) try mw.writeByte('\n');
                        const mem_sym = session.db.symbol_table.getSymbol(mem_idx).*;
                        try mw.writeAll("@overload ");
                        try writeFormattedFnSignature(session, mem_idx, mem_sym, false, mw, null, arena_alloc);
                    }
                } else {
                    try mw.print("@overload fn {s}(…)", .{sym.name_text});
                }
            },
            .struct_sym => {
                if (sym.contract_flags.is_linear) try mw.writeAll("@linear ");
                if (sym.flags.is_soa_annotated) try mw.writeAll("@soa ");
                if (sym.visibility != .private) try mw.print("{s} ", .{sym.visibility.asKeywordSlice()});
                try mw.print("struct {s}", .{sym.name_text});
            },
            .enum_sym => {
                if (sym.contract_flags.is_linear) try mw.writeAll("@linear ");
                if (sym.visibility != .private) try mw.print("{s} ", .{sym.visibility.asKeywordSlice()});
                try mw.print("enum {s}", .{sym.name_text});
            },
            .union_sym => {
                if (sym.visibility != .private) try mw.print("{s} ", .{sym.visibility.asKeywordSlice()});
                try mw.print("union {s}", .{sym.name_text});
            },
            .bit_field_sym => {
                if (sym.visibility != .private) try mw.print("{s} ", .{sym.visibility.asKeywordSlice()});
                try mw.print("bit_field {s}", .{sym.name_text});
            },
            .trait_sym => {
                if (sym.visibility != .private) try mw.print("{s} ", .{sym.visibility.asKeywordSlice()});
                try mw.print("trait {s}", .{sym.name_text});
            },
            .type_alias_sym, .distinct_type_sym, .refined_type_sym, .type_group_sym => {
                const eff_ty = if (!target.type_id.isError()) target.type_id else sym.type_id;
                const ty_str = session.db.type_pool.formatType(eff_ty, &session.db.symbol_table, &type_buf);
                if (std.mem.eql(u8, sym.name_text, ty_str)) {
                    try mw.print("type {s}", .{sym.name_text});
                } else {
                    try mw.print("type {s} = {s}", .{ sym.name_text, ty_str });
                }
            },
            .const_sym, .const_param_sym => {
                const eff_ty = if (!target.type_id.isError()) target.type_id else sym.type_id;
                const ty_str = session.db.type_pool.formatType(eff_ty, &session.db.symbol_table, &type_buf);
                try mw.print("const {s}: {s}", .{ sym.name_text, ty_str });
            },
            .local_let_sym => {
                const eff_ty = if (!target.type_id.isError()) target.type_id else sym.type_id;
                const ty_str = session.db.type_pool.formatType(eff_ty, &session.db.symbol_table, &type_buf);
                try mw.print("let {s}: {s}", .{ sym.name_text, ty_str });
            },
            .local_var_sym => {
                const eff_ty = if (!target.type_id.isError()) target.type_id else sym.type_id;
                const ty_str = session.db.type_pool.formatType(eff_ty, &session.db.symbol_table, &type_buf);
                try mw.print("{s} {s}: {s}", .{ if (sym.flags.is_mut) "var" else "let", sym.name_text, ty_str });
            },
            .param_sym => {
                const eff_ty = if (!target.type_id.isError()) target.type_id else sym.type_id;
                const ty_str = session.db.type_pool.formatType(eff_ty, &session.db.symbol_table, &type_buf);
                if (sym.flags.is_mut) {
                    try mw.print("var {s}: {s}", .{ sym.name_text, ty_str });
                } else {
                    try mw.print("{s}: {s}", .{ sym.name_text, ty_str });
                }
            },
            .field_sym => {
                const eff_ty = if (!target.type_id.isError()) target.type_id else sym.type_id;
                const ty_str = session.db.type_pool.formatType(eff_ty, &session.db.symbol_table, &type_buf);
                if (sym.visibility != .private) try mw.print("{s} ", .{sym.visibility.asKeywordSlice()});
                try mw.print("{s}: {s}", .{ sym.name_text, ty_str });
            },
            .enum_variant_sym => {
                var enum_buf: [256]u8 = undefined;
                const unwrapped_enum = unwrapHoverValueType(&session.db.type_pool, target.type_id);
                const enum_prefix: []const u8 = if (!unwrapped_enum.isError() and
                    !unwrapped_enum.isPrimitiveOrSentinel() and
                    session.db.type_pool.getNode(unwrapped_enum).tag == .enum_ty)
                    session.db.type_pool.formatType(unwrapped_enum, &session.db.symbol_table, &enum_buf)
                else if (!sym.owner_def_id.isNone()) blk_owner: {
                    if (session.db.symbol_table.def_to_symbol.get(sym.owner_def_id.asInt())) |owner_idx| {
                        break :blk_owner session.db.symbol_table.getSymbol(owner_idx).name_text;
                    }
                    break :blk_owner "";
                } else "";

                if (enum_prefix.len > 0) {
                    try mw.print("{s}.{s}", .{ enum_prefix, sym.name_text });
                } else {
                    try mw.print(".{s}", .{sym.name_text});
                }
                if (sym.type_id != .unit_ty and !sym.type_id.isError()) {
                    const payload_str = session.db.type_pool.formatType(
                        sym.type_id,
                        &session.db.symbol_table,
                        &type_buf,
                    );
                    try mw.print("({s})", .{payload_str});
                }
            },
            .module_sym => {
                try mw.print("mod {s}", .{sym.name_text});
            },
            .type_param_sym => {
                try mw.print("type {s}", .{sym.name_text});
            },
            .extern_static_sym => {
                const ty_str = session.db.type_pool.formatType(sym.type_id, &session.db.symbol_table, &type_buf);
                try mw.print("extern static {s}: {s}", .{ sym.name_text, ty_str });
            },
            .use_alias_sym => {
                try mw.print("use {s}", .{sym.name_text});
            },
        }
        try mw.writeAll("\n```");

        if (session.db.symbol_table.getDeprecatedMeta(sym_idx)) |dep_meta| {
            if (dep_meta.is_deprecated) {
                try mw.writeAll("\n\n⚠ **Deprecated**");
                if (dep_meta.since_sym != .empty) {
                    try mw.print(" (since `{s}`)", .{session.db.interner.get(dep_meta.since_sym)});
                }
                if (dep_meta.reason_sym != .empty) {
                    try mw.print(": {s}", .{session.db.interner.get(dep_meta.reason_sym)});
                }
                if (dep_meta.upgrade_sym != .empty) {
                    try mw.print(" – upgrade: `{s}`", .{session.db.interner.get(dep_meta.upgrade_sym)});
                }
            }
        }

        const live_decl_span = session.db.resolveLiveSymbolDeclSpan(sym_idx) catch sym.decl_span;
        var doc_md = if (sym.kind == .module_sym) blk_mod_doc: {
            const mod_fid = resolveModuleBackingFileId(session, target, sym);
            if (!mod_fid.isNone()) {
                break :blk_mod_doc try extractFileModuleDocComments(session, arena_alloc, mod_fid);
            }
            break :blk_mod_doc try extractInlineModDocComments(
                session,
                arena_alloc,
                live_decl_span,
                sym.def_id,
                sym.cst_node,
            );
        } else try extractDeclarationDocComments(
            session,
            arena_alloc,
            live_decl_span,
            sym.def_id,
            sym.cst_node,
        );

        // Enrich `self` / `&self` / `&mut self` / `own self` receiver hovers with enclosing nominal type docs:
        if (doc_md.len == 0 and sym.kind == .param_sym and std.mem.eql(u8, sym.name_text, "self")) {
            const recv_ty = if (!target.type_id.isError()) target.type_id else sym.type_id;
            const nom_sym_idx = unwrapTypeToNominalSymbol(&session.db.type_pool, &session.db.symbol_table, recv_ty);
            if (!nom_sym_idx.isNone() and nom_sym_idx.asInt() < session.db.symbol_table.countSymbols()) {
                const nom_sym = session.db.symbol_table.getSymbol(nom_sym_idx).*;
                const nom_span = session.db.resolveLiveSymbolDeclSpan(nom_sym_idx) catch nom_sym.decl_span;
                doc_md = try extractDeclarationDocComments(
                    session,
                    arena_alloc,
                    nom_span,
                    nom_sym.def_id,
                    nom_sym.cst_node,
                );
            }
        }

        if (doc_md.len > 0) {
            try mw.writeAll("\n\n");
            try mw.writeAll(doc_md);
        }

        if (sym.kind == .fn_sym) {
            try appendFnHoverContractBullets(session, sym_idx, sym, mw);
        }
    } else {
        const eff_tok_kind: ?TokenKind = target.resolved_token_kind orelse blk_tk: {
            if (session.db.parsed_artifacts.getPtr(fid.asInt())) |parsed_art| {
                if (target.token_index.asInt() < parsed_art.token_buffer.countTokens()) {
                    break :blk_tk parsed_art.token_buffer.getToken(target.token_index).kind;
                }
            }
            break :blk_tk null;
        };
        const can_render_bare_type = if (eff_tok_kind) |tok_kind|
            (symbol_resolver.isIdentifierToken(tok_kind) or
                tok_kind == .kw_self_val or
                tok_kind == .kw_self_type or
                tok_kind == .prim_type)
        else
            false;
        if (!can_render_bare_type) {
            return writeNullResultFrame(session, out_writer, rpc_id);
        }
        const ty_str = session.db.type_pool.formatType(target.type_id, &session.db.symbol_table, &type_buf);
        if (BUILTIN_PRIM_HOVER_MAP.get(ty_str)) |prim_spec| {
            try mw.print("```corex\n{s}\n```\n\n{s}", .{ prim_spec.signature, prim_spec.summary });
        } else {
            try mw.print("```corex\n{s}\n```", .{ty_str});
        }
    }

    return writeMarkdownHoverFrame(session, fid, target.token_span, md_alloc.written(), out_writer, rpc_id);
}

/// Builds hover documentation when `cursor_byte` rests on a lint rule selector inside `@expect(…)` / `@allow(…)`.
fn tryBuildLintSelectorHover(
    arena_alloc: std.mem.Allocator,
    fid: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    cursor_byte: u32,
) !?struct { span: Span, markdown: []const u8 } {
    if (cursor_byte >= source.len) return null;
    const total_nodes = cst_arena.countNodes();
    var idx: usize = 0;
    while (idx < total_nodes) {
        const node_id = CstNodeIndex.fromInt(@intCast(idx));
        const node_rec = cst_arena.getNode(node_id);
        if (node_rec.kind != .attribute) {
            idx += 1;
            continue;
        }
        const attr_span = computeCstSubtreeByteSpan(fid, token_buffer, cst_arena, node_id) orelse {
            idx += @max(@as(usize, 1), node_rec.subtree_size);
            continue;
        };
        if (cursor_byte < attr_span.start_byte or cursor_byte > attr_span.end_byte) {
            idx += @max(@as(usize, 1), node_rec.subtree_size);
            continue;
        }

        const end_idx = @min(total_nodes, idx + @max(@as(usize, 1), node_rec.subtree_size));
        var attr_name: []const u8 = "";
        var lparen_byte: ?u32 = null;
        var cur = idx + 1;
        while (cur < end_idx) : (cur += 1) {
            const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
            if (leaf.subtree_size > 1 or leaf.token.isNone() or leaf.token.asInt() >= token_buffer.countTokens()) {
                continue;
            }
            const t_rec = token_buffer.getToken(leaf.token);
            if (t_rec.kind == .at) continue;
            if (attr_name.len == 0 and isIdentifierOrKeywordToken(t_rec.kind)) {
                attr_name = symbol_resolver.extractTokenSlice(source, token_buffer, leaf.token);
                continue;
            }
            if (t_rec.kind == .lparen) {
                lparen_byte = t_rec.byte_offset;
                break;
            }
        }
        if ((!std.mem.eql(u8, attr_name, "expect") and !std.mem.eql(u8, attr_name, "allow")) or
            lparen_byte == null or cursor_byte <= lparen_byte.?)
        {
            return null;
        }

        var sel_lo: usize = @min(@as(usize, cursor_byte), source.len);
        while (sel_lo > 0 and (std.ascii.isAlphanumeric(source[sel_lo - 1]) or
            source[sel_lo - 1] == '-' or source[sel_lo - 1] == '_')) : (sel_lo -= 1)
        {}
        var sel_hi: usize = @min(@as(usize, cursor_byte), source.len);
        while (sel_hi < source.len and (std.ascii.isAlphanumeric(source[sel_hi]) or
            source[sel_hi] == '-' or source[sel_hi] == '_')) : (sel_hi += 1)
        {}
        if (sel_lo >= sel_hi) return null;
        const sel_slice = source[sel_lo..sel_hi];
        switch (diagnostic.lookupLintRuleBySelector(sel_slice)) {
            .rule => |rule_id| {
                const meta = rule_id.asMeta();
                const cat_entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(meta.diag_code)];
                const fix_label: []const u8 = switch (meta.default_applicability) {
                    .machine_applicable => "safe autofix (`--fix`)",
                    .maybe_incorrect => "unsafe autofix (`--fix-unsafe`)",
                    else => "diagnostic only",
                };
                const md_text = try std.fmt.allocPrint(
                    arena_alloc,
                    "```corex\n{s}/{s} // [{s}] ({s})\n```\n\n**{s}**\n\n{s}",
                    .{
                        meta.diag_code.asCodeStr(),
                        meta.slug,
                        meta.category.asStr(),
                        fix_label,
                        cat_entry.title,
                        cat_entry.explanation,
                    },
                );
                return .{
                    .span = Span.init(fid, @intCast(sel_lo), @intCast(sel_hi)),
                    .markdown = md_text,
                };
            },
            else => return null,
        }
    }
    return null;
}

/// Writes `{"jsonrpc":"2.0","id":…,"result":null}` and flushes `out_writer`.
fn writeNullResultFrame(
    session: *LspSession,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":null}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

// ----------- Definition & Type Definition Handlers ------------

/// Handles `textDocument/definition` and `textDocument/typeDefinition` via `resolveLiveSymbolDeclSpan`.
fn handleDefinitionOrTypeDefinition(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    is_type_def: bool,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const pos = extractJsonPosition(params.getField("position") orelse JsonValue{ .null_val = {} }) orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing position");
    };

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) {
        return writeNullResultFrame(session, out_writer, rpc_id);
    }

    const target = try resolveCursorTarget(session, fid, pos);
    if (!is_type_def and !target.external_mod_file_id.isNone()) {
        const mod_span = Span.init(target.external_mod_file_id, 0, 0);
        session.outbound_buf.clearRetainingCapacity();
        const body_writer = &session.outbound_buf.writer;
        try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
        try writeJsonRpcId(body_writer, rpc_id);
        try body_writer.writeAll(",\"result\":");
        try writeLspLocationJson(session, arena_alloc, body_writer, mod_span);
        try body_writer.writeByte('}');
        return flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
    }

    var target_sym: SymbolIndex = .none;
    if (is_type_def) {
        var eff_ty = target.type_id;
        if (eff_ty.isError() and !target.symbol_index.isNone()) {
            const unwrapped = resolveLiveCanonicalSymbol(session, target.symbol_index);
            eff_ty = session.db.symbol_table.getSymbol(unwrapped).type_id;
        }
        target_sym = unwrapTypeToNominalSymbol(&session.db.type_pool, &session.db.symbol_table, eff_ty);
    } else if (!target.symbol_index.isNone()) {
        target_sym = resolveLiveCanonicalSymbol(session, target.symbol_index);
    }

    if (target_sym.isNone() or target_sym.asInt() >= session.db.symbol_table.countSymbols()) {
        return writeNullResultFrame(session, out_writer, rpc_id);
    }

    var live_span = try session.db.resolveLiveSymbolDeclSpan(target_sym);
    // When invoking `definition` directly on `&self` in a method signature, jump to the nominal `impl` type:
    if (!is_type_def and live_span.file_id == fid and
        live_span.start_byte <= target.token_span.start_byte and
        target.token_span.end_byte <= live_span.end_byte)
    {
        const cur_sym = session.db.symbol_table.getSymbol(target_sym).*;
        if (cur_sym.kind == .param_sym and std.mem.eql(u8, cur_sym.name_text, "self")) {
            const recv_ty = if (!target.type_id.isError()) target.type_id else cur_sym.type_id;
            const nom_idx = unwrapTypeToNominalSymbol(&session.db.type_pool, &session.db.symbol_table, recv_ty);
            if (!nom_idx.isNone() and nom_idx.asInt() < session.db.symbol_table.countSymbols()) {
                target_sym = nom_idx;
                live_span = try session.db.resolveLiveSymbolDeclSpan(target_sym);
            }
        }
    }
    if (live_span.file_id.isNone() or !session.db.source_inputs.contains(live_span.file_id.asInt())) {
        return writeNullResultFrame(session, out_writer, rpc_id);
    }

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":");
    try writeLspLocationJson(session, arena_alloc, body_writer, live_span);
    try body_writer.writeByte('}');
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

// ----- Visibility-Pruned References & Document Highlight ------

/// Appends a `ReferenceHit` into `hits` if no hit at the exact `(file_id, start_byte, end_byte)` exists yet.
fn appendUniqueRefHit(
    arena_alloc: std.mem.Allocator,
    hits: *std.ArrayListUnmanaged(ReferenceHit),
    cand_hit: ReferenceHit,
    max_cap: usize,
) !void {
    if (hits.items.len >= max_cap or cand_hit.span.file_id.isNone()) return;
    for (hits.items) |*existing| {
        if (existing.span.file_id == cand_hit.span.file_id and
            existing.span.start_byte == cand_hit.span.start_byte and
            existing.span.end_byte == cand_hit.span.end_byte)
        {
            if (cand_hit.is_write_access) existing.is_write_access = true;
            return;
        }
    }
    try hits.append(arena_alloc, cand_hit);
}

/// Scans `cst_root` (`use_item` or inline `mod_item`) for `<orig_name> as <alias_name>` leaves and records `orig_name` spans.
fn collectUseAliasOriginHitsInSubtree(
    arena_alloc: std.mem.Allocator,
    scan_fid: FileId,
    source_text: []const u8,
    parsed_art: *const query_db.ParsedCstArtifact,
    cst_root: CstNodeIndex,
    orig_name: []const u8,
    alias_name: []const u8,
    mod_scope: ScopeId,
    max_cap: usize,
    out_hits: *std.ArrayListUnmanaged(ReferenceHit),
) !void {
    const cst_total = parsed_art.cst_arena.countNodes();
    if (cst_root.isNone() or cst_root.asInt() >= cst_total) return;
    const root_start: usize = cst_root.asInt();
    const root_rec = parsed_art.cst_arena.getNode(cst_root);
    const root_end = @min(root_start + @max(@as(usize, root_rec.subtree_size), 1), cst_total);
    const tok_total = parsed_art.token_buffer.countTokens();

    var node_cur = root_start;
    while (node_cur < root_end) {
        const sub_rec = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(node_cur)));
        if (sub_rec.kind == .use_item) {
            const use_end = @min(node_cur + @max(@as(usize, sub_rec.subtree_size), 1), root_end);
            var use_cur = node_cur + 1;
            while (use_cur + 1 < use_end) : (use_cur += 1) {
                const orig_leaf = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(use_cur)));
                if (orig_leaf.subtree_size > 1 or orig_leaf.flags.is_missing_or_injected or
                    orig_leaf.token.isNone() or orig_leaf.token.asInt() >= tok_total)
                {
                    continue;
                }
                const orig_lex = symbol_resolver.extractTokenSlice(
                    source_text,
                    &parsed_art.token_buffer,
                    orig_leaf.token,
                );
                if (!std.mem.eql(u8, orig_lex, orig_name)) continue;

                // Verify `orig_leaf` is immediately followed by `as <alias_name>` in this `use_item`:
                var has_seen_as = false;
                var look_cur = use_cur + 1;
                while (look_cur < use_end) : (look_cur += 1) {
                    const next_leaf = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(look_cur)));
                    if (next_leaf.subtree_size > 1 or next_leaf.flags.is_missing_or_injected or
                        next_leaf.token.isNone() or next_leaf.token.asInt() >= tok_total)
                    {
                        continue;
                    }
                    const next_rec = parsed_art.token_buffer.getToken(next_leaf.token);
                    if (next_rec.flags.is_synthesized) continue;
                    if (!has_seen_as) {
                        if (next_rec.kind == .kw_as) {
                            has_seen_as = true;
                            continue;
                        }
                        break;
                    }
                    const alias_lex = symbol_resolver.extractTokenSlice(
                        source_text,
                        &parsed_art.token_buffer,
                        next_leaf.token,
                    );
                    if (std.mem.eql(u8, alias_lex, alias_name)) {
                        try appendUniqueRefHit(arena_alloc, out_hits, .{
                            .span = parsed_art.token_buffer.getTokenSpan(scan_fid, orig_leaf.token),
                            .is_write_access = false,
                            .ref_scope = mod_scope,
                        }, max_cap);
                    }
                    break;
                }
            }
            node_cur = use_end;
            continue;
        }
        node_cur += 1;
    }
}

/// Maps `sym_idx` (through `use` aliases and detached pre-cutoff Pass-1 slots) to its live canonical `SymbolIndex`.
fn resolveLiveCanonicalSymbol(session: *const LspSession, sym_idx: SymbolIndex) SymbolIndex {
    const unwrapped = session.db.symbol_table.unwrapAliasSymbolIdx(sym_idx);
    if (unwrapped.isNone() or unwrapped.asInt() >= session.db.symbol_table.countSymbols()) return unwrapped;
    const sym = session.db.symbol_table.getSymbol(unwrapped).*;
    if (sym.flags.is_builtin) return unwrapped;
    switch (sym.kind) {
        .local_let_sym, .local_var_sym, .param_sym, .type_param_sym, .const_param_sym, .use_alias_sym => {
            return unwrapped;
        },
        else => {},
    }

    if (!sym.def_id.isNone()) {
        if (session.db.symbol_table.def_to_symbol.get(sym.def_id.asInt())) |live_idx| {
            if (!live_idx.isNone() and live_idx.asInt() < session.db.symbol_table.countSymbols()) {
                const live_sym = session.db.symbol_table.getSymbol(live_idx).*;
                if (live_sym.kind == sym.kind and live_sym.namespace == sym.namespace and
                    live_sym.name == sym.name)
                {
                    return live_idx;
                }
            }
        }
    }

    const decl_fid = sym.decl_span.file_id;
    if (decl_fid.isNone()) return unwrapped;
    const bounds = session.db.getFileLiveSymbolBounds(decl_fid) orelse return unwrapped;
    if (unwrapped.asInt() >= bounds.sym_start and unwrapped.asInt() < bounds.sym_end) {
        return unwrapped;
    }
    const clamped_end = @min(bounds.sym_end, session.db.symbol_table.countSymbols());
    var cand_raw: u32 = bounds.sym_start;
    while (cand_raw < clamped_end) : (cand_raw += 1) {
        const cand_idx = SymbolIndex.fromInt(cand_raw);
        const cand_sym = session.db.symbol_table.getSymbol(cand_idx).*;
        if (cand_sym.kind == sym.kind and
            cand_sym.namespace == sym.namespace and
            cand_sym.name == sym.name and
            cand_sym.decl_span.file_id == decl_fid and
            cand_sym.def_id == sym.def_id and
            cand_sym.owner_def_id == sym.owner_def_id)
        {
            return cand_idx;
        }
    }
    return unwrapped;
}

/// Maps a local `use … as alias` symbol (possibly from a backdated body side table) to its live slot in `file_id`.
fn resolveLiveExplicitAliasSymbol(
    session: *const LspSession,
    file_id: FileId,
    alias_idx: SymbolIndex,
) SymbolIndex {
    if (alias_idx.isNone() or alias_idx.asInt() >= session.db.symbol_table.countSymbols()) return alias_idx;
    const alias_sym = session.db.symbol_table.getSymbol(alias_idx).*;
    if (alias_sym.kind != .use_alias_sym or alias_sym.decl_span.file_id != file_id) return alias_idx;
    const bounds = session.db.getFileLiveSymbolBounds(file_id) orelse return alias_idx;
    if (alias_idx.asInt() >= bounds.sym_start and alias_idx.asInt() < bounds.sym_end) return alias_idx;

    const target_live = resolveLiveCanonicalSymbol(session, alias_idx);
    const clamped_end = @min(bounds.sym_end, session.db.symbol_table.countSymbols());
    var cand_raw: u32 = bounds.sym_start;
    while (cand_raw < clamped_end) : (cand_raw += 1) {
        const cand_idx = SymbolIndex.fromInt(cand_raw);
        const cand_sym = session.db.symbol_table.getSymbol(cand_idx).*;
        if (cand_sym.kind == .use_alias_sym and
            cand_sym.decl_span.file_id == file_id and
            cand_sym.name == alias_sym.name and
            resolveLiveCanonicalSymbol(session, cand_idx) == target_live)
        {
            return cand_idx;
        }
    }
    return alias_idx;
}

/// Collects occurrences of `canonical_sym` inside `scan_fid` (optionally restricted to `only_def_id`).
fn collectSymbolOccurrencesInFile(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    scan_fid: FileId,
    canonical_sym: SymbolIndex,
    is_explicit_local_alias: bool,
    is_including_declaration: bool,
    only_def_id: DefId,
    max_cap: usize,
    out_hits: *std.ArrayListUnmanaged(ReferenceHit),
) !void {
    if (out_hits.items.len >= max_cap) return;
    const sym = session.db.symbol_table.getSymbol(canonical_sym).*;
    const src = getLiveDocumentSource(session, scan_fid) orelse return;
    _ = session.db.parseCst(scan_fid) catch return;
    _ = session.db.resolveSignatures(scan_fid) catch return;
    const entries = try arena_alloc.dupe(
        query_db.ItemTreeEntry,
        (session.db.extractItemTree(scan_fid) catch return).entries,
    );
    var parsed_art = session.db.parsed_artifacts.getPtr(scan_fid.asInt()) orelse return;
    const mod_scope = session.db.symbol_table.file_module_scopes.get(scan_fid.asInt()) orelse ScopeId.none;

    // Pre-resolve canonical declaration span once when declared inside `scan_fid`:
    const live_canonical_decl: ?Span = if (sym.decl_span.file_id == scan_fid) blk: {
        const resolved = resolveLiveSymbolDeclSpanFast(
            session,
            canonical_sym,
            scan_fid,
            src,
            parsed_art,
        ) catch sym.decl_span;
        parsed_art = session.db.parsed_artifacts.getPtr(scan_fid.asInt()) orelse return;
        break :blk if (resolved.file_id == scan_fid) resolved else null;
    } else null;

    // [1] Include declaration site if `is_including_declaration` and declared in `scan_fid`:
    if (is_including_declaration) {
        if (live_canonical_decl) |live_decl| {
            try appendUniqueRefHit(arena_alloc, out_hits, .{
                .span = live_decl,
                .is_write_access = true,
                .ref_scope = sym.scope_id,
            }, max_cap);
        }
    }

    // [2] Scan `use` import trees and signature type references when not restricted to a single body:
    if (only_def_id.isNone()) {
        if (session.db.getFileLiveSymbolBounds(scan_fid)) |bounds| {
            var s_raw = bounds.sym_start;
            while (s_raw < bounds.sym_end and s_raw < session.db.symbol_table.countSymbols()) : (s_raw += 1) {
                const cand_idx = SymbolIndex.fromInt(s_raw);
                const cand_rec = session.db.symbol_table.getSymbol(cand_idx).*;
                if (cand_rec.kind != .use_alias_sym) continue;
                if (!cand_rec.scope_id.isNone() and
                    cand_rec.scope_id.asInt() < session.db.symbol_table.scope_arena.countScopes() and
                    session.db.symbol_table.scope_arena.getScope(cand_rec.scope_id).file_id != scan_fid)
                {
                    continue;
                }
                const unwrapped = resolveLiveCanonicalSymbol(session, cand_idx);
                if (unwrapped != canonical_sym and cand_idx != canonical_sym) continue;

                if (is_explicit_local_alias) {
                    if (cand_idx == canonical_sym and cand_rec.decl_span.file_id == scan_fid) {
                        const live_sp = resolveLiveSymbolDeclSpanFast(
                            session,
                            cand_idx,
                            scan_fid,
                            src,
                            parsed_art,
                        ) catch cand_rec.decl_span;
                        parsed_art = session.db.parsed_artifacts.getPtr(scan_fid.asInt()) orelse return;
                        try appendUniqueRefHit(arena_alloc, out_hits, .{
                            .span = live_sp,
                            .is_write_access = true,
                            .ref_scope = mod_scope,
                        }, max_cap);
                    }
                    continue;
                }

                // Non-glob `use prefix.bar;` (`cand_rec.name == sym.name` and `decl_span.file_id == scan_fid`):
                if (cand_rec.decl_span.file_id == scan_fid and cand_rec.name == sym.name) {
                    const live_sp = resolveLiveSymbolDeclSpanFast(
                        session,
                        cand_idx,
                        scan_fid,
                        src,
                        parsed_art,
                    ) catch cand_rec.decl_span;
                    parsed_art = session.db.parsed_artifacts.getPtr(scan_fid.asInt()) orelse return;
                    try appendUniqueRefHit(arena_alloc, out_hits, .{
                        .span = live_sp,
                        .is_write_access = false,
                        .ref_scope = mod_scope,
                    }, max_cap);
                } else if (cand_rec.name != sym.name) {
                    // Scan live `ItemTree` `.use_decl` / `.mod_decl` CST subtrees for `use prefix.{bar as my_alias}`:
                    for (entries) |live_item| {
                        if (live_item.kind != .use_decl and live_item.kind != .mod_decl) continue;
                        try collectUseAliasOriginHitsInSubtree(
                            arena_alloc,
                            scan_fid,
                            src,
                            parsed_art,
                            live_item.cst_node,
                            sym.name_text,
                            cand_rec.name_text,
                            mod_scope,
                            max_cap,
                            out_hits,
                        );
                    }
                }
            }
        }
    }

    // [3] Scan `ItemTree` entries (`only_def_id` when local/param, else byte-pre-filtered `DefId`s):
    for (entries) |entry| {
        if (out_hits.items.len >= max_cap) break;
        if (!only_def_id.isNone() and entry.def_id != only_def_id) continue;
        if (entry.kind == .mod_decl or entry.kind == .use_decl or entry.kind == .ffi_extern_block) continue;

        if (only_def_id.isNone()) {
            if (computeCstSubtreeByteSpan(
                scan_fid,
                &parsed_art.token_buffer,
                &parsed_art.cst_arena,
                entry.cst_node,
            )) |entry_span| {
                const sub_bytes = src[entry_span.start_byte..@min(@as(usize, entry_span.end_byte), src.len)];
                // Skip typechecking `DefId` bodies that do not mention `sym.name_text` unless aliased in `scan_fid`:
                if (std.mem.indexOf(u8, sub_bytes, sym.name_text) == null and
                    !hasExplicitFileAliasForTarget(session, scan_fid, canonical_sym))
                {
                    continue;
                }
            }
        }

        // Also scan non-body item header type tokens (e.g., struct field types, fn param/return types):
        if (only_def_id.isNone() and sym.namespace == .type_ns) {
            try scanSignatureTypeTokensInEntry(
                session,
                arena_alloc,
                scan_fid,
                src,
                parsed_art,
                entry,
                canonical_sym,
                is_explicit_local_alias,
                mod_scope,
                max_cap,
                out_hits,
            );
            parsed_art = session.db.parsed_artifacts.getPtr(scan_fid.asInt()) orelse return;
        }

        const side_tables = (session.db.getDefSideTables(entry.def_id) catch continue) orelse continue;
        parsed_art = session.db.parsed_artifacts.getPtr(scan_fid.asInt()) orelse return;

        // Precompute write-access token indices inside `[ast_start .. ast_end)`:
        var write_tok_set: std.AutoHashMapUnmanaged(u32, void) = .empty;
        var ast_scan = side_tables.ast_start;
        const ast_limit = @min(side_tables.ast_end, @as(u32, @intCast(parsed_art.ast_arena.countNodes())));
        while (ast_scan < ast_limit) : (ast_scan += 1) {
            const n_id = NodeIndex.fromInt(ast_scan);
            const n_rec = parsed_art.ast_arena.getNode(n_id);
            if (n_rec.tag == .bind_pat or n_rec.tag == .local_var_decl) {
                if (!n_rec.main_token.isNone()) try write_tok_set.put(arena_alloc, n_rec.main_token.asInt(), {});
            } else if (n_rec.tag == .assign_stmt and n_rec.lhs.tag == .node) {
                const lhs_n = parsed_art.ast_arena.getNode(NodeIndex.fromInt(n_rec.lhs.payload));
                if (!lhs_n.main_token.isNone()) try write_tok_set.put(arena_alloc, lhs_n.main_token.asInt(), {});
            } else if (n_rec.tag == .unary_expr and
                !n_rec.main_token.isNone() and n_rec.lhs.tag == .node)
            {
                const mk = parsed_art.token_buffer.getToken(n_rec.main_token).kind;
                if (mk == .kw_own or mk == .kw_mut or mk == .kw_var) {
                    const inner_n = parsed_art.ast_arena.getNode(NodeIndex.fromInt(n_rec.lhs.payload));
                    if (!inner_n.main_token.isNone()) {
                        try write_tok_set.put(arena_alloc, inner_n.main_token.asInt(), {});
                    }
                }
            }
        }

        var ast_raw = side_tables.ast_start;
        while (ast_raw < ast_limit) : (ast_raw += 1) {
            const ast_id = NodeIndex.fromInt(ast_raw);
            const ast_node = parsed_art.ast_arena.getNode(ast_id);
            const raw_node_sym = side_tables.getNodeSymbol(ast_id);
            if (!raw_node_sym.isNone()) {
                const is_matched = if (is_explicit_local_alias)
                    (resolveLiveExplicitAliasSymbol(session, scan_fid, raw_node_sym) == canonical_sym)
                else
                    (resolveLiveCanonicalSymbol(session, raw_node_sym) == canonical_sym);

                if (is_matched) {
                    const hit_tok = resolveAstNodeFocalToken(parsed_art, ast_id);
                    if (!hit_tok.isNone() and hit_tok.asInt() < parsed_art.token_buffer.countTokens()) {
                        const cand_sp = parsed_art.token_buffer.getTokenSpan(scan_fid, hit_tok);
                        if (!is_including_declaration) {
                            if (live_canonical_decl) |live_decl| {
                                if (cand_sp.start_byte == live_decl.start_byte and cand_sp.end_byte == live_decl.end_byte) {
                                    continue;
                                }
                            }
                        }
                        try appendUniqueRefHit(arena_alloc, out_hits, .{
                            .span = cand_sp,
                            .is_write_access = write_tok_set.contains(hit_tok.asInt()),
                            .ref_scope = mod_scope,
                        }, max_cap);
                    }
                }
            }

            // Check `.struct_lit` / `.struct_pat` / `.variant_pat` explicit & shorthand `.field_sym` hits:
            if (sym.kind == .field_sym and
                (ast_node.tag == .struct_lit or ast_node.tag == .struct_pat or ast_node.tag == .variant_pat))
            {
                const container_ty = side_tables.getNodeType(ast_id);
                const nom_idx = unwrapTypeToNominalSymbol(&session.db.type_pool, &session.db.symbol_table, container_ty);
                if (!nom_idx.isNone() and session.db.symbol_table.getSymbol(nom_idx).target_scope == sym.scope_id) {
                    const cst_orig = parsed_art.ast_arena.getCstOrigin(ast_id);
                    if (!cst_orig.isNone()) {
                        try collectStructFieldInitOrPatHits(
                            arena_alloc,
                            scan_fid,
                            src,
                            parsed_art,
                            cst_orig,
                            sym.name_text,
                            ast_node.tag == .struct_lit,
                            mod_scope,
                            max_cap,
                            out_hits,
                        );
                    }
                }
            }
        }

        // Also collect occurrences inside `f"…"` / `f#"…"#` interpolation holes via live `fmt_tok_base`:
        var interp_it = side_tables.string_interps.iterator();
        while (interp_it.next()) |interp_kv| {
            const fmt_ast_raw = side_tables.ast_start + interp_kv.key_ptr.*;
            if (fmt_ast_raw >= ast_limit) continue;
            const fmt_main_tok = parsed_art.ast_arena.getNode(NodeIndex.fromInt(fmt_ast_raw)).main_token;
            if (fmt_main_tok.isNone() or fmt_main_tok.asInt() >= parsed_art.token_buffer.countTokens()) continue;
            const fmt_tok_base = parsed_art.token_buffer.getToken(fmt_main_tok).byte_offset;

            for (interp_kv.value_ptr.holes) |hole| {
                for (hole.tokens, 0..) |htok, htok_idx| {
                    if (htok.byte_len == 0) continue;
                    const htok_start = fmt_tok_base +| htok.rel_byte;
                    const htok_end = htok_start +| @as(u32, htok.byte_len);

                    if (!htok.symbol_index.isNone()) {
                        const is_matched = if (is_explicit_local_alias)
                            (resolveLiveExplicitAliasSymbol(session, scan_fid, htok.symbol_index) == canonical_sym)
                        else
                            (resolveLiveCanonicalSymbol(session, htok.symbol_index) == canonical_sym);
                        if (is_matched) {
                            const cand_sp = Span.init(scan_fid, htok_start, htok_end);
                            if (!is_including_declaration) {
                                if (live_canonical_decl) |live_decl| {
                                    if (cand_sp.start_byte == live_decl.start_byte and cand_sp.end_byte == live_decl.end_byte) {
                                        continue;
                                    }
                                }
                            }
                            const is_field_init_label = sym.kind == .field_sym and
                                htok_idx + 1 < hole.tokens.len and hole.tokens[htok_idx + 1].kind == .colon;
                            try appendUniqueRefHit(arena_alloc, out_hits, .{
                                .span = cand_sp,
                                .is_write_access = is_field_init_label,
                                .ref_scope = mod_scope,
                            }, max_cap);
                            continue;
                        }
                    }

                    // Also match shorthand `Point { x }` inside `hole.tokens` when searching for `.field_sym`:
                    if (sym.kind == .field_sym and isUserIdentifierToken(htok.kind) and
                        htok_idx >= 2 and htok_idx + 1 < hole.tokens.len and
                        (hole.tokens[htok_idx - 1].kind == .lbrace or hole.tokens[htok_idx - 1].kind == .comma) and
                        (hole.tokens[htok_idx + 1].kind == .comma or hole.tokens[htok_idx + 1].kind == .rbrace))
                    {
                        const htok_lex = src[@min(@as(usize, htok_start), src.len)..@min(@as(usize, htok_end), src.len)];
                        if (std.mem.eql(u8, htok_lex, sym.name_text)) {
                            var brace_scan = htok_idx - 1;
                            var depth_count: u32 = 0;
                            var struct_open_idx: ?usize = null;
                            while (true) {
                                const prev_k = hole.tokens[brace_scan].kind;
                                if (prev_k == .rbrace) {
                                    depth_count += 1;
                                } else if (prev_k == .lbrace) {
                                    if (depth_count == 0) {
                                        struct_open_idx = brace_scan;
                                        break;
                                    }
                                    depth_count -= 1;
                                }
                                if (brace_scan == 0) break;
                                brace_scan -= 1;
                            }
                            if (struct_open_idx) |open_pos| {
                                if (open_pos > 0 and !hole.tokens[open_pos - 1].symbol_index.isNone()) {
                                    const head_sym = resolveLiveCanonicalSymbol(session, hole.tokens[open_pos - 1].symbol_index);
                                    if (!head_sym.isNone() and
                                        session.db.symbol_table.getSymbol(head_sym).target_scope == sym.scope_id)
                                    {
                                        try appendUniqueRefHit(arena_alloc, out_hits, .{
                                            .span = Span.init(scan_fid, htok_start, htok_end),
                                            .is_write_access = true,
                                            .ref_scope = mod_scope,
                                        }, max_cap);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Collects `.field_init` and `.field_pat` field label tokens matching `field_name` inside `container_cst`.
fn collectStructFieldInitOrPatHits(
    arena_alloc: std.mem.Allocator,
    file_id: FileId,
    src: []const u8,
    parsed_art: *const query_db.ParsedCstArtifact,
    container_cst: CstNodeIndex,
    field_name: []const u8,
    is_write_init: bool,
    ref_scope: ScopeId,
    max_cap: usize,
    out_hits: *std.ArrayListUnmanaged(ReferenceHit),
) !void {
    const c_start: usize = container_cst.asInt();
    const c_end = @min(
        c_start + @max(@as(usize, parsed_art.cst_arena.getNode(container_cst).subtree_size), 1),
        parsed_art.cst_arena.countNodes(),
    );
    var cur = c_start + 1;
    while (cur < c_end) {
        const sub = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
        if (sub.kind == .field_init or sub.kind == .field_pat) {
            const f_end = @min(cur + @max(@as(usize, sub.subtree_size), 1), c_end);
            var ident_tok: TokenIndex = .none;
            var f_cur = cur + 1;
            while (f_cur < f_end) : (f_cur += 1) {
                const leaf = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(f_cur)));
                if (leaf.subtree_size > 1 or leaf.token.isNone() or
                    leaf.token.asInt() >= parsed_art.token_buffer.countTokens())
                {
                    continue;
                }
                const lk = parsed_art.token_buffer.getToken(leaf.token).kind;
                if (lk == .kw_var or lk == .kw_mut or lk == .kw_own or lk == .amp) continue;
                if (isUserIdentifierToken(lk)) {
                    ident_tok = leaf.token;
                }
                break;
            }
            if (!ident_tok.isNone()) {
                const lex = symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, ident_tok);
                if (std.mem.eql(u8, lex, field_name)) {
                    try appendUniqueRefHit(arena_alloc, out_hits, .{
                        .span = parsed_art.token_buffer.getTokenSpan(file_id, ident_tok),
                        .is_write_access = is_write_init,
                        .ref_scope = ref_scope,
                    }, max_cap);
                }
            }
            cur = f_end;
            continue;
        }
        cur += 1;
    }
}

/// Scans header/signature `.type_ident` tokens in `entry.cst_node` (outside body blocks) for `canonical_sym`.
fn scanSignatureTypeTokensInEntry(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    file_id: FileId,
    src: []const u8,
    parsed_art: *const query_db.ParsedCstArtifact,
    entry: query_db.ItemTreeEntry,
    canonical_sym: SymbolIndex,
    is_explicit_local_alias: bool,
    mod_scope: ScopeId,
    max_cap: usize,
    out_hits: *std.ArrayListUnmanaged(ReferenceHit),
) !void {
    if (entry.cst_node.isNone() or mod_scope.isNone()) return;
    const start_idx: usize = entry.cst_node.asInt();
    const end_idx = @min(
        start_idx + @max(@as(usize, parsed_art.cst_arena.getNode(entry.cst_node).subtree_size), 1),
        parsed_art.cst_arena.countNodes(),
    );
    const body_cst_idx: usize = if (!entry.body_cst_node.isNone()) entry.body_cst_node.asInt() else end_idx;

    var cur = start_idx + 1;
    while (cur < end_idx) : (cur += 1) {
        if (cur == body_cst_idx and body_cst_idx < end_idx) {
            const body_sub = parsed_art.cst_arena.getNode(entry.body_cst_node).subtree_size;
            cur += @max(@as(usize, body_sub), 1) - 1;
            continue;
        }
        const leaf = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
        if (leaf.subtree_size > 1 or leaf.flags.is_missing_or_injected or
            leaf.token.isNone() or leaf.token.asInt() >= parsed_art.token_buffer.countTokens())
        {
            continue;
        }
        const tok_rec = parsed_art.token_buffer.getToken(leaf.token);
        if (tok_rec.kind != .type_ident) continue;
        const lex = symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, leaf.token);
        const name_id = session.db.interner.lookup(lex) orelse continue;
        switch (session.db.symbol_table.lookupLexical(mod_scope, name_id, NamespaceMask.TYPE_ONLY)) {
            .found => |found_sym| {
                const is_matching = if (is_explicit_local_alias)
                    (resolveLiveExplicitAliasSymbol(session, file_id, found_sym) == canonical_sym)
                else
                    (resolveLiveCanonicalSymbol(session, found_sym) == canonical_sym);
                if (is_matching) {
                    const tok_sp = parsed_art.token_buffer.getTokenSpan(file_id, leaf.token);
                    const target_sym_rec = session.db.symbol_table.getSymbol(canonical_sym).*;
                    if (target_sym_rec.decl_span.file_id == file_id) {
                        const live_decl = resolveLiveSymbolDeclSpanFast(
                            session,
                            canonical_sym,
                            file_id,
                            src,
                            parsed_art,
                        ) catch target_sym_rec.decl_span;
                        if (tok_sp.start_byte == live_decl.start_byte and tok_sp.end_byte == live_decl.end_byte) {
                            continue;
                        }
                    }
                    try appendUniqueRefHit(arena_alloc, out_hits, .{
                        .span = tok_sp,
                        .is_write_access = false,
                        .ref_scope = mod_scope,
                    }, max_cap);
                }
            },
            else => {},
        }
    }
}

/// Returns `true` if `file_id` declares a `use … as alias` binding targeting `canonical_sym`.
fn hasExplicitFileAliasForTarget(
    session: *LspSession,
    file_id: FileId,
    canonical_sym: SymbolIndex,
) bool {
    const bounds = session.db.getFileLiveSymbolBounds(file_id) orelse return false;
    var sym_raw = bounds.sym_start;
    while (sym_raw < bounds.sym_end and sym_raw < session.db.symbol_table.countSymbols()) : (sym_raw += 1) {
        const cand_idx = SymbolIndex.fromInt(sym_raw);
        const cand_sym = session.db.symbol_table.getSymbol(cand_idx).*;
        if (cand_sym.kind == .use_alias_sym and
            resolveLiveCanonicalSymbol(session, cand_idx) == canonical_sym)
        {
            return true;
        }
    }
    return false;
}

/// Handles `textDocument/documentHighlight`: intra-file `Read = 2` vs `Write = 3` symbol highlights.
fn handleDocumentHighlightRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const pos = extractJsonPosition(params.getField("position") orelse JsonValue{ .null_val = {} }) orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing position");
    };

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);

    const target = try resolveCursorTarget(session, fid, pos);
    if (target.symbol_index.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);

    const canonical_sym = resolveLiveCanonicalSymbol(session, target.symbol_index);
    const sym = session.db.symbol_table.getSymbol(canonical_sym).*;
    const is_local = switch (sym.kind) {
        .local_let_sym, .local_var_sym, .param_sym, .type_param_sym, .const_param_sym => true,
        else => false,
    };
    const restrict_def = if (is_local) target.enclosing_def_id else DefId.NONE;

    var hits: std.ArrayListUnmanaged(ReferenceHit) = .empty;
    try collectSymbolOccurrencesInFile(
        session,
        arena_alloc,
        fid,
        canonical_sym,
        false,
        true,
        restrict_def,
        MAX_REFERENCES,
        &hits,
    );

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":[");
    for (hits.items, 0..) |hit, i| {
        if (i > 0) try body_writer.writeByte(',');
        const range = spanToLspRange(session, fid, hit.span);
        try body_writer.writeAll("{\"range\":");
        try writeLspRangeJson(body_writer, range);
        try body_writer.print(",\"kind\":{d}}}", .{@as(u8, if (hit.is_write_access) 3 else 2)});
    }
    try body_writer.writeAll("]}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Handles `textDocument/references`: `Visibility`-pruned + `std.mem.indexOf` pre-filtered (`<= MAX_REFERENCES`).
fn handleReferencesRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const pos = extractJsonPosition(params.getField("position") orelse JsonValue{ .null_val = {} }) orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing position");
    };
    const is_including_declaration = if (params.getField("context")) |ctx_obj|
        (ctx_obj.getBoolField("includeDeclaration") orelse true)
    else
        true;

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);

    const target = try resolveCursorTarget(session, fid, pos);
    if (target.symbol_index.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);

    const canonical_sym = resolveLiveCanonicalSymbol(session, target.symbol_index);
    const sym = session.db.symbol_table.getSymbol(canonical_sym).*;
    const is_local = switch (sym.kind) {
        .local_let_sym, .local_var_sym, .param_sym, .type_param_sym, .const_param_sym => true,
        else => false,
    };

    var hits: std.ArrayListUnmanaged(ReferenceHit) = .empty;
    if (is_local) {
        // Fast path; local/parameter symbols scan ONLY the single enclosing `DefId`:
        try collectSymbolOccurrencesInFile(
            session,
            arena_alloc,
            fid,
            canonical_sym,
            false,
            is_including_declaration,
            target.enclosing_def_id,
            MAX_REFERENCES,
            &hits,
        );
    } else {
        const decl_fid = sym.decl_span.file_id;
        const def_pkg_id = session.db.symbol_table.getFilePackageId(decl_fid);
        const def_mod_scope: ScopeId = if (!sym.scope_id.isNone() and
            sym.scope_id.asInt() < session.db.symbol_table.scope_arena.countScopes())
            session.db.symbol_table.scope_arena.getScope(sym.scope_id).enclosing_module
        else
            .none;

        for (session.mounted_files.items) |cand_fid| {
            if (hits.items.len >= MAX_REFERENCES) break;
            try session.db.unwindIfCanceled();

            const cand_src = getLiveDocumentSource(session, cand_fid) orelse continue;
            // Fast raw-byte pre-filter BEFORE resolving signatures or body side tables:
            if (cand_fid != decl_fid and std.mem.indexOf(u8, cand_src, sym.name_text) == null) {
                continue;
            }

            if (cand_fid != decl_fid and sym.visibility != .public) {
                const caller_pkg_id = session.db.symbol_table.getFilePackageId(cand_fid);
                if (sym.visibility == .private or sym.visibility == .pub_super or sym.visibility == .pub_pkg) {
                    if (def_pkg_id != caller_pkg_id) continue;
                }
                _ = session.db.resolveSignatures(cand_fid) catch continue;
                if (session.db.symbol_table.file_module_scopes.get(cand_fid.asInt())) |caller_mod_scope| {
                    if (!sym.visibility.isVisibleFrom(
                        def_mod_scope,
                        def_pkg_id,
                        caller_mod_scope,
                        caller_pkg_id,
                        &session.db.symbol_table.scope_arena,
                    )) {
                        continue;
                    }
                }
            }

            try collectSymbolOccurrencesInFile(
                session,
                arena_alloc,
                cand_fid,
                canonical_sym,
                false,
                is_including_declaration,
                .NONE,
                MAX_REFERENCES,
                &hits,
            );
        }
    }

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":[");
    for (hits.items, 0..) |hit, i| {
        if (i > 0) try body_writer.writeByte(',');
        try writeLspLocationJson(session, arena_alloc, body_writer, hit.span);
    }
    try body_writer.writeAll("]}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

// ------------- Document Symbol & Workspace Symbol -------------

/// Maps a CoreX `SymbolKind` to its LSP 3.17 `SymbolKind` integer (`1..26`).
fn toLspSymbolKind(kind: SymbolKind) u8 {
    return switch (kind) {
        .module_sym => 2,
        .struct_sym, .union_sym, .bit_field_sym => 23,
        .enum_sym => 10,
        .trait_sym, .type_group_sym => 11,
        .fn_sym, .overload_group_sym => 12,
        .const_sym, .const_param_sym => 14,
        .field_sym => 8,
        .enum_variant_sym => 22,
        .type_param_sym, .type_alias_sym, .distinct_type_sym, .refined_type_sym => 26,
        else => 13,
    };
}

/// Recursively serializes a `DocumentSymbolItem` JSON object (enforcing `selectionRange` containment).
fn writeDocumentSymbolJson(
    session: *LspSession,
    file_id: FileId,
    src: []const u8,
    line_idx_opt: ?*const LineIndex,
    item: DocumentSymbolItem,
    writer: *std.Io.Writer,
) !void {
    const clamped_sel = Span.init(
        file_id,
        @max(item.full_span.start_byte, @min(item.selection_span.start_byte, item.full_span.end_byte)),
        @max(item.full_span.start_byte, @min(item.selection_span.end_byte, item.full_span.end_byte)),
    );
    const full_range = if (line_idx_opt) |li|
        spanToLspRangeFast(src, li, session.position_encoding, item.full_span)
    else
        spanToLspRange(session, file_id, item.full_span);
    const sel_range = if (line_idx_opt) |li|
        spanToLspRangeFast(src, li, session.position_encoding, clamped_sel)
    else
        spanToLspRange(session, file_id, clamped_sel);
    try writer.writeAll("{\"name\":");
    try writeJsonString(writer, if (item.name.len > 0) item.name else "<anonymous>");
    if (item.detail.len > 0) {
        try writer.writeAll(",\"detail\":");
        try writeJsonString(writer, item.detail);
    }
    try writer.print(",\"kind\":{d}", .{item.kind});
    if (item.is_deprecated) {
        try writer.writeAll(",\"tags\":[1]");
    }
    try writer.writeAll(",\"range\":");
    try writeLspRangeJson(writer, full_range);
    try writer.writeAll(",\"selectionRange\":");
    try writeLspRangeJson(writer, sel_range);
    if (item.children.len > 0) {
        try writer.writeAll(",\"children\":[");
        for (item.children, 0..) |child_sym, i| {
            if (i > 0) try writer.writeByte(',');
            try writeDocumentSymbolJson(session, file_id, src, line_idx_opt, child_sym, writer);
        }
        try writer.writeByte(']');
    }
    try writer.writeByte('}');
}

/// Comparator ordering `DocumentSymbolItem` children monotonically by `(start_byte ASC, end_byte ASC)`.
fn isDocumentSymbolBefore(_: void, lhs_sym: DocumentSymbolItem, rhs_sym: DocumentSymbolItem) bool {
    if (lhs_sym.full_span.start_byte != rhs_sym.full_span.start_byte) {
        return lhs_sym.full_span.start_byte < rhs_sym.full_span.start_byte;
    }
    return lhs_sym.full_span.end_byte < rhs_sym.full_span.end_byte;
}

/// Appends candidate member symbols from `bucket` whose live declaration spans lie inside `full_span`.
fn appendContainerDocumentSymbolChildren(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    fid: FileId,
    src: []const u8,
    matched_sym_idx: SymbolIndex,
    full_span: Span,
    bucket: []const SymbolIndex,
    type_buf: *[256]u8,
    out_children: *std.ArrayListUnmanaged(DocumentSymbolItem),
) !void {
    for (bucket) |c_idx| {
        if (c_idx == matched_sym_idx) continue;
        const c_sym = session.db.symbol_table.getSymbol(c_idx).*;
        const parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse return;
        const c_live = resolveLiveSymbolDeclSpanFast(
            session,
            c_idx,
            fid,
            src,
            parsed_art,
        ) catch c_sym.decl_span;
        if (c_live.file_id != fid or
            c_live.start_byte < full_span.start_byte or
            c_live.end_byte > full_span.end_byte)
        {
            continue;
        }
        const c_detail: []const u8 = if (!c_sym.type_id.isError() and c_sym.type_id != .unit_ty)
            try arena_alloc.dupe(
                u8,
                session.db.type_pool.formatType(c_sym.type_id, &session.db.symbol_table, type_buf),
            )
        else
            "";
        try out_children.append(arena_alloc, .{
            .name = c_sym.name_text,
            .detail = c_detail,
            .kind = toLspSymbolKind(c_sym.kind),
            .is_deprecated = c_sym.extra_flags.is_deprecated or
                session.db.symbol_table.getDeprecatedMeta(c_idx) != null,
            .full_span = c_live,
            .selection_span = c_live,
        });
    }
}

/// Handles `textDocument/documentSymbol`: builds hierarchical `DocumentSymbol[]` in $O(E + S)$ time.
fn handleDocumentSymbolRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);

    _ = try session.db.parseCst(fid);
    _ = try session.db.resolveSignatures(fid);
    const entries = try arena_alloc.dupe(
        query_db.ItemTreeEntry,
        (try session.db.extractItemTree(fid)).entries,
    );
    const src = getLiveDocumentSource(session, fid) orelse "";
    var parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse
        return writeNullResultFrame(session, out_writer, rpc_id);

    // [1] Partition file-local member symbols into `owner_def_id` and unowned `scope_id` buckets in one $O(S)$ pass:
    var members_by_owner_def: std.AutoHashMapUnmanaged(u32, std.ArrayListUnmanaged(SymbolIndex)) = .empty;
    var members_by_scope: std.AutoHashMapUnmanaged(u32, std.ArrayListUnmanaged(SymbolIndex)) = .empty;
    if (session.db.getFileLiveSymbolBounds(fid)) |bounds| {
        var s_raw = bounds.sym_start;
        while (s_raw < bounds.sym_end and s_raw < session.db.symbol_table.countSymbols()) : (s_raw += 1) {
            const c_idx = SymbolIndex.fromInt(s_raw);
            const c_sym = session.db.symbol_table.getSymbol(c_idx).*;
            if (c_sym.flags.is_imported or c_sym.decl_span.file_id != fid) continue;
            const is_member_kind = switch (c_sym.kind) {
                .field_sym, .enum_variant_sym, .fn_sym, .const_sym, .type_alias_sym => true,
                else => false,
            };
            if (!is_member_kind) continue;

            if (!c_sym.owner_def_id.isNone()) {
                const gop = try members_by_owner_def.getOrPut(arena_alloc, c_sym.owner_def_id.asInt());
                if (!gop.found_existing) gop.value_ptr.* = .empty;
                try gop.value_ptr.append(arena_alloc, c_idx);
            } else if (!c_sym.scope_id.isNone()) {
                const gop = try members_by_scope.getOrPut(arena_alloc, c_sym.scope_id.asInt());
                if (!gop.found_existing) gop.value_ptr.* = .empty;
                try gop.value_ptr.append(arena_alloc, c_idx);
            }
        }
    }

    var doc_items: std.ArrayListUnmanaged(DocumentSymbolItem) = .empty;
    var type_buf: [256]u8 = undefined;

    // [2] Assemble top-level `DocumentSymbolItem`s with $O(1)$ bucket lookups per `ItemTreeEntry`:
    for (entries) |entry| {
        if (entry.kind == .use_decl or entry.kind == .ffi_extern_block) continue;
        parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse
            return writeNullResultFrame(session, out_writer, rpc_id);
        const full_span = computeCstSubtreeByteSpan(
            fid,
            &parsed_art.token_buffer,
            &parsed_art.cst_arena,
            entry.cst_node,
        ) orelse continue;

        var sel_span = full_span;
        const matched_sym_idx: SymbolIndex = session.db.symbol_table.def_to_symbol.get(entry.def_id.asInt()) orelse .none;
        if (!matched_sym_idx.isNone()) {
            const live_sp = resolveLiveSymbolDeclSpanFast(
                session,
                matched_sym_idx,
                fid,
                src,
                parsed_art,
            ) catch full_span;
            parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse
                return writeNullResultFrame(session, out_writer, rpc_id);
            if (live_sp.file_id == fid) sel_span = live_sp;
        } else if (!entry.ast_node.isNone() and entry.ast_node.asInt() < parsed_art.ast_arena.countNodes()) {
            const main_tok = parsed_art.ast_arena.getNode(entry.ast_node).main_token;
            if (!main_tok.isNone() and main_tok.asInt() < parsed_art.token_buffer.countTokens()) {
                sel_span = parsed_art.token_buffer.getTokenSpan(fid, main_tok);
            }
        }

        var child_list: std.ArrayListUnmanaged(DocumentSymbolItem) = .empty;
        var has_both_buckets = false;
        if (!entry.def_id.isNone()) {
            if (members_by_owner_def.get(entry.def_id.asInt())) |owner_bucket| {
                try appendContainerDocumentSymbolChildren(
                    session,
                    arena_alloc,
                    fid,
                    src,
                    matched_sym_idx,
                    full_span,
                    owner_bucket.items,
                    &type_buf,
                    &child_list,
                );
            }
        }
        if (!matched_sym_idx.isNone()) {
            const target_scope = session.db.symbol_table.getSymbol(matched_sym_idx).target_scope;
            if (!target_scope.isNone()) {
                if (members_by_scope.get(target_scope.asInt())) |scope_bucket| {
                    has_both_buckets = child_list.items.len > 0;
                    try appendContainerDocumentSymbolChildren(
                        session,
                        arena_alloc,
                        fid,
                        src,
                        matched_sym_idx,
                        full_span,
                        scope_bucket.items,
                        &type_buf,
                        &child_list,
                    );
                }
            }
        }
        if (has_both_buckets and child_list.items.len > 1) {
            std.mem.sort(DocumentSymbolItem, child_list.items, {}, isDocumentSymbolBefore);
        }

        const lsp_kind: u8 = switch (entry.kind) {
            .mod_decl => 2,
            .fn_decl, .test_decl, .bench_decl, .subscript_decl => 12,
            .struct_decl, .union_decl => 23,
            .enum_decl => 10,
            .trait_decl => 11,
            .impl_decl => 5,
            .type_alias_decl => 26,
            .const_decl, .extern_static => 14,
            else => 13,
        };
        const disp_name = if (entry.name_text.len > 0)
            entry.name_text
        else if (entry.kind == .impl_decl)
            "impl"
        else
            "<item>";

        try doc_items.append(arena_alloc, .{
            .name = disp_name,
            .kind = lsp_kind,
            .is_deprecated = !matched_sym_idx.isNone() and
                session.db.symbol_table.getDeprecatedMeta(matched_sym_idx) != null,
            .full_span = full_span,
            .selection_span = sel_span,
            .children = child_list.items,
        });
    }

    const line_idx_opt: ?*const LineIndex = if (session.vfs.getLineIndex(fid)) |li| li else |_| null;
    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":[");
    for (doc_items.items, 0..) |doc_sym, i| {
        if (i > 0) try body_writer.writeByte(',');
        try writeDocumentSymbolJson(session, fid, src, line_idx_opt, doc_sym, body_writer);
    }
    try body_writer.writeAll("]}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Returns `true` when `haystack` contains `needle` under ASCII case-insensitive comparison.
fn hasAsciiSubstringIgnoreCase(haystack: []const u8, needle: []const u8) bool {
    if (needle.len == 0) return true;
    if (needle.len > haystack.len) return false;
    const max_start = haystack.len - needle.len;
    var start_idx: usize = 0;
    while (start_idx <= max_start) : (start_idx += 1) {
        if (std.ascii.eqlIgnoreCase(haystack[start_idx .. start_idx + needle.len], needle)) {
            return true;
        }
    }
    return false;
}

/// Scores `name_text` against `query_text` (`0..5`, or `null` on no match; prefix ranks strictly above substring).
fn scoreWorkspaceSymbolMatch(name_text: []const u8, query_text: []const u8) ?u8 {
    if (name_text.len == 0) return null;
    if (query_text.len == 0) return 5;
    if (std.mem.eql(u8, name_text, query_text)) return 0;
    if (std.ascii.eqlIgnoreCase(name_text, query_text)) return 1;
    if (std.mem.startsWith(u8, name_text, query_text)) return 2;
    if (std.ascii.startsWithIgnoreCase(name_text, query_text)) return 3;
    if (hasAsciiSubstringIgnoreCase(name_text, query_text)) return 4;
    return null;
}

/// Comparator ordering `WorkspaceSymbolCandidate`s by `(rank ASC, name.len ASC, name ASC)`.
fn isWorkspaceCandidateBetter(_: void, lhs_cand: WorkspaceSymbolCandidate, rhs_cand: WorkspaceSymbolCandidate) bool {
    if (lhs_cand.rank != rhs_cand.rank) return lhs_cand.rank < rhs_cand.rank;
    if (lhs_cand.name.len != rhs_cand.name.len) return lhs_cand.name.len < rhs_cand.name.len;
    return std.mem.order(u8, lhs_cand.name, rhs_cand.name) == .lt;
}

/// Handles `workspace/symbol`: filters stale pre-`sym_start` symbols, skips `.std_core`, caps at `<= 256`.
fn handleWorkspaceSymbolRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const query_str = params.getStringField("query") orelse "";
    var candidates: std.ArrayListUnmanaged(WorkspaceSymbolCandidate) = .empty;

    for (session.mounted_files.items) |cand_fid| {
        try session.db.unwindIfCanceled();
        const pkg_id = session.db.symbol_table.getFilePackageId(cand_fid);
        if (pkg_id == .std_core and !session.options.is_internal_core) continue;

        _ = session.db.resolveSignatures(cand_fid) catch continue;
        const bounds = session.db.getFileLiveSymbolBounds(cand_fid) orelse continue;
        const file_path = session.vfs.getFilePath(cand_fid);
        const mod_stem = std.fs.path.stem(file_path);
        const cand_src = getLiveDocumentSource(session, cand_fid) orelse "";

        var sym_raw = bounds.sym_start;
        while (sym_raw < bounds.sym_end and sym_raw < session.db.symbol_table.countSymbols()) : (sym_raw += 1) {
            const sym_idx = SymbolIndex.fromInt(sym_raw);
            const sym = session.db.symbol_table.getSymbol(sym_idx).*;
            if (sym.flags.is_builtin or sym.flags.is_imported) continue;
            switch (sym.kind) {
                .param_sym,
                .local_let_sym,
                .local_var_sym,
                .type_param_sym,
                .const_param_sym,
                .use_alias_sym,
                .field_sym,
                => continue,
                else => {},
            }

            const rank = scoreWorkspaceSymbolMatch(sym.name_text, query_str) orelse continue;
            const live_span = if (session.db.parsed_artifacts.getPtr(cand_fid.asInt())) |cand_parsed|
                resolveLiveSymbolDeclSpanFast(session, sym_idx, cand_fid, cand_src, cand_parsed) catch continue
            else
                session.db.resolveLiveSymbolDeclSpan(sym_idx) catch continue;
            if (live_span.file_id.isNone()) continue;

            try candidates.append(arena_alloc, .{
                .name = sym.name_text,
                .lsp_kind = toLspSymbolKind(sym.kind),
                .live_span = live_span,
                .container_name = mod_stem,
                .rank = rank,
                .is_deprecated = sym.extra_flags.is_deprecated or
                    session.db.symbol_table.getDeprecatedMeta(sym_idx) != null,
            });
        }
    }

    std.mem.sort(WorkspaceSymbolCandidate, candidates.items, {}, isWorkspaceCandidateBetter);
    const emit_len = @min(candidates.items.len, MAX_WORKSPACE_SYMBOLS);

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":[");
    for (candidates.items[0..emit_len], 0..) |cand, i| {
        if (i > 0) try body_writer.writeByte(',');
        try body_writer.writeAll("{\"name\":");
        try writeJsonString(body_writer, cand.name);
        try body_writer.print(",\"kind\":{d}", .{cand.lsp_kind});
        if (cand.is_deprecated) {
            try body_writer.writeAll(",\"tags\":[1]");
        }
        if (cand.container_name.len > 0) {
            try body_writer.writeAll(",\"containerName\":");
            try writeJsonString(body_writer, cand.container_name);
        }
        try body_writer.writeAll(",\"location\":");
        try writeLspLocationJson(session, arena_alloc, body_writer, cand.live_span);
        try body_writer.writeByte('}');
    }
    try body_writer.writeAll("]}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

// ------------ Completion (<= 256) & Signature Help ------------

/// Maps a CoreX `SymbolKind` to its LSP 3.17 `CompletionItemKind` integer (`1..25`).
fn toLspCompletionKind(kind: SymbolKind, scope_arena: *const symbol_resolver.ScopeArena, scope_id: ScopeId) u8 {
    return switch (kind) {
        .module_sym => 9,
        .struct_sym, .union_sym, .bit_field_sym => 22,
        .enum_sym => 13,
        .trait_sym, .type_group_sym => 8,
        .type_alias_sym, .distinct_type_sym, .refined_type_sym => 22,
        .type_param_sym => 25,
        .const_sym, .const_param_sym => 21,
        .field_sym => 5,
        .enum_variant_sym => 20,
        .param_sym, .local_let_sym, .local_var_sym, .extern_static_sym, .use_alias_sym => 6,
        .fn_sym, .overload_group_sym => blk: {
            const is_method = !scope_id.isNone() and scope_id.asInt() < scope_arena.countScopes() and
                switch (scope_arena.getScope(scope_id).kind) {
                    .nominal_type_scope, .trait_scope, .impl_scope => true,
                    else => false,
                };
            break :blk if (is_method) 2 else 3;
        },
    };
}

/// Appends a `CompletionCandidate` to `out_items` if it matches `prefix` and has not yet been emitted.
fn appendUniqueCompletion(
    arena_alloc: std.mem.Allocator,
    seen_labels: *std.StringHashMapUnmanaged(void),
    out_items: *std.ArrayListUnmanaged(CompletionCandidate),
    prefix: []const u8,
    cand: CompletionCandidate,
) !void {
    if (cand.label.len == 0 or out_items.items.len >= MAX_COMPLETION_ITEMS) return;
    if (prefix.len > 0 and !std.ascii.startsWithIgnoreCase(cand.label, prefix)) return;
    if ((try seen_labels.getOrPut(arena_alloc, cand.label)).found_existing) return;
    try out_items.append(arena_alloc, cand);
}

/// Orders `CompletionCandidate` items by `(sort_tier ASC, label ASC)`.
fn isCompletionCandidateBefore(_: void, lhs_item: CompletionCandidate, rhs_item: CompletionCandidate) bool {
    if (lhs_item.sort_tier != rhs_item.sort_tier) return lhs_item.sort_tier < rhs_item.sort_tier;
    return std.mem.order(u8, lhs_item.label, rhs_item.label) == .lt;
}

/// Returns `true` when `fn_sym_idx`'s first parameter is a `self` value/reference receiver.
fn hasMethodSelfReceiver(sym_table: *const SymbolTable, fn_sym_idx: SymbolIndex) bool {
    const specs = sym_table.getFnParamSpecs(fn_sym_idx);
    if (specs.len == 0) return false;
    return std.mem.eql(u8, specs[0].name_text, "self");
}

/// Returns `true` when the `.` receiver expression at `(side_tables_opt, recv_ast_id, dot_byte_offset)` is mutable.
fn isCompletionDotReceiverMutable(
    session: *const LspSession,
    source_text: []const u8,
    parsed_art: *const query_db.ParsedCstArtifact,
    mod_scope: ScopeId,
    side_tables_opt: ?*const BodySemanticSideTables,
    recv_ast_id: NodeIndex,
    raw_recv_ty: TypeId,
    dot_byte_offset: u32,
) bool {
    if (raw_recv_ty.isError()) return false;
    const unwrapped_raw = session.db.type_pool.unwrapUnderlyingType(raw_recv_ty);
    if (!unwrapped_raw.isPrimitiveOrSentinel()) {
        switch (session.db.type_pool.getTag(unwrapped_raw)) {
            .mut_ref_ty => return true,
            .ref_ty => return false,
            .raw_ptr_ty => return session.db.type_pool.getNode(unwrapped_raw).rhs != 0,
            else => {},
        }
    }

    // Walk receiver AST place chain when available (`arr.`, `holder.arr.`, `slice_mut[i].`):
    if (side_tables_opt) |side_tables| {
        if (!recv_ast_id.isNone() and recv_ast_id.asInt() < parsed_art.ast_arena.countNodes()) {
            var cur_ast = recv_ast_id;
            var hops: u32 = 0;
            while (!cur_ast.isNone() and cur_ast.asInt() < parsed_art.ast_arena.countNodes() and hops < 16) : (hops += 1) {
                const cur_node = parsed_art.ast_arena.getNode(cur_ast);
                switch (cur_node.tag) {
                    .ident_expr, .self_val => {
                        const sym_idx = side_tables.getNodeSymbol(cur_ast);
                        if (!sym_idx.isNone() and sym_idx.asInt() < session.db.symbol_table.countSymbols()) {
                            return session.db.symbol_table.getSymbol(sym_idx).flags.is_mut;
                        }
                        break;
                    },
                    .deref_expr => {
                        if (cur_node.lhs.tag != .node) return false;
                        const inner_ty = session.db.type_pool.unwrapUnderlyingType(
                            side_tables.getNodeType(NodeIndex.fromInt(cur_node.lhs.payload)),
                        );
                        if (inner_ty.isPrimitiveOrSentinel()) return false;
                        const inner_node = session.db.type_pool.getNode(inner_ty);
                        return switch (inner_node.tag) {
                            .mut_ref_ty => true,
                            .raw_ptr_ty => inner_node.rhs != 0,
                            else => false,
                        };
                    },
                    .field_access, .index_expr => {
                        if (cur_node.lhs.tag != .node) return false;
                        const base_ast = NodeIndex.fromInt(cur_node.lhs.payload);
                        const base_ty = session.db.type_pool.unwrapUnderlyingType(side_tables.getNodeType(base_ast));
                        if (!base_ty.isPrimitiveOrSentinel()) {
                            const base_node = session.db.type_pool.getNode(base_ty);
                            switch (base_node.tag) {
                                .mut_ref_ty => return true,
                                .ref_ty => return false,
                                .raw_ptr_ty => return base_node.rhs != 0,
                                else => {},
                            }
                        }
                        cur_ast = base_ast;
                    },
                    else => return false,
                }
            }
        }
    }

    // Fallback; inspect identifier token immediately preceding `.`:
    if (dot_byte_offset > 0) {
        const recv_tok = findTokenAtCursorByte(&parsed_art.token_buffer, dot_byte_offset - 1);
        if (!recv_tok.isNone()) {
            if (parsed_art.token_buffer.getToken(recv_tok).kind == .fmt_string_lit) {
                if (side_tables_opt) |side_tables| {
                    if (findInterpHoleTokenAtByte(side_tables, parsed_art, recv_tok, dot_byte_offset - 1)) |recv_hit| {
                        const recv_sym = recv_hit.token_info.symbol_index;
                        if (!recv_sym.isNone() and recv_sym.asInt() < session.db.symbol_table.countSymbols()) {
                            return session.db.symbol_table.getSymbol(
                                session.db.symbol_table.unwrapAliasSymbolIdx(recv_sym),
                            ).flags.is_mut;
                        }
                    }
                }
                return false;
            }
            if (side_tables_opt) |side_tables| {
                var ast_raw = side_tables.ast_start;
                const ast_limit = @min(side_tables.ast_end, @as(u32, @intCast(parsed_art.ast_arena.countNodes())));
                while (ast_raw < ast_limit) : (ast_raw += 1) {
                    const cand_ast = NodeIndex.fromInt(ast_raw);
                    if (parsed_art.ast_arena.getNode(cand_ast).main_token == recv_tok) {
                        const cand_sym = side_tables.getNodeSymbol(cand_ast);
                        if (!cand_sym.isNone() and cand_sym.asInt() < session.db.symbol_table.countSymbols()) {
                            return session.db.symbol_table.getSymbol(cand_sym).flags.is_mut;
                        }
                    }
                }
            }
            const recv_lex = symbol_resolver.extractTokenSlice(source_text, &parsed_art.token_buffer, recv_tok);
            if (session.db.interner.lookup(recv_lex)) |recv_id| {
                switch (session.db.symbol_table.lookupLexical(mod_scope, recv_id, NamespaceMask.VALUE_ONLY)) {
                    .found => |found_idx| {
                        return session.db.symbol_table.getSymbol(
                            session.db.symbol_table.unwrapAliasSymbolIdx(found_idx),
                        ).flags.is_mut;
                    },
                    else => {},
                }
            }
        }
    }
    return false;
}

/// Populates dot-completion candidates for `dot_target` into `out_items`, enforcing `Visibility.isVisibleFrom`.
fn populateDotTargetCompletions(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    caller_scope: ScopeId,
    caller_pkg_id: PackageId,
    dot_target: IncompleteDotTarget,
    is_mutable_recv: bool,
    prefix: []const u8,
    seen_labels: *std.StringHashMapUnmanaged(void),
    out_items: *std.ArrayListUnmanaged(CompletionCandidate),
) !void {
    var type_buf: [256]u8 = undefined;
    switch (dot_target) {
        .module_ns => |mod_scope_raw| {
            const mod_scope = if (mod_scope_raw.isNone())
                try session.db.symbol_table.ensureCxRootScope(&session.db.interner)
            else
                mod_scope_raw;
            if (mod_scope.isNone()) return;

            for (session.db.symbol_table.getScopeMembers(mod_scope)) |mem_idx| {
                if (out_items.items.len >= MAX_COMPLETION_ITEMS) break;
                const mem_sym = session.db.symbol_table.getSymbol(mem_idx).*;
                if (std.mem.startsWith(u8, mem_sym.name_text, "_")) continue;
                const def_scope = session.db.symbol_table.scope_arena.getScope(mem_sym.scope_id);
                if (!mem_sym.flags.is_builtin and !mem_sym.visibility.isVisibleFrom(
                    def_scope.enclosing_module,
                    def_scope.pkg_id,
                    caller_scope,
                    caller_pkg_id,
                    &session.db.symbol_table.scope_arena,
                )) {
                    continue;
                }
                const detail_str: []const u8 = if (!mem_sym.type_id.isError() and mem_sym.type_id != .unit_ty)
                    try arena_alloc.dupe(
                        u8,
                        session.db.type_pool.formatType(mem_sym.type_id, &session.db.symbol_table, &type_buf),
                    )
                else
                    "";
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = mem_sym.name_text,
                    .kind = toLspCompletionKind(mem_sym.kind, &session.db.symbol_table.scope_arena, mem_sym.scope_id),
                    .detail = detail_str,
                    .sort_tier = 1,
                    .is_deprecated = mem_sym.extra_flags.is_deprecated or
                        session.db.symbol_table.getDeprecatedMeta(mem_idx) != null,
                });
            }
        },
        .type_ns => |raw_ty| {
            const base_ty = session.db.type_pool.unwrapUnderlyingType(raw_ty);
            if (base_ty.isSizedPrimitive()) {
                if (type_system.TypeGroupMask.containsPrimitive(type_system.TypeGroupMask.INTEGER, base_ty)) {
                    for ([_][]const u8{ "MIN", "MAX", "BITS" }) |int_const| {
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = int_const,
                            .kind = 21,
                            .detail = session.db.type_pool.formatType(base_ty, &session.db.symbol_table, &type_buf),
                            .sort_tier = 0,
                        });
                    }
                } else if (type_system.TypeGroupMask.containsPrimitive(type_system.TypeGroupMask.FLOAT, base_ty)) {
                    for ([_][]const u8{ "NAN", "INFINITY", "NEG_INFINITY", "EPSILON", "MIN", "MAX" }) |flt_const| {
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = flt_const,
                            .kind = 21,
                            .detail = session.db.type_pool.formatType(base_ty, &session.db.symbol_table, &type_buf),
                            .sort_tier = 0,
                        });
                    }
                }
            }
            const nom_idx = unwrapTypeToNominalSymbol(&session.db.type_pool, &session.db.symbol_table, raw_ty);
            if (nom_idx.isNone()) return;
            const nom_sym = session.db.symbol_table.getSymbol(nom_idx).*;
            if (nom_sym.target_scope.isNone()) return;

            for (session.db.symbol_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                if (out_items.items.len >= MAX_COMPLETION_ITEMS) break;
                const mem_sym = session.db.symbol_table.getSymbol(mem_idx).*;
                if (mem_sym.kind == .field_sym) continue;
                if (mem_sym.kind == .fn_sym and hasMethodSelfReceiver(&session.db.symbol_table, mem_idx)) continue;

                const def_scope = session.db.symbol_table.scope_arena.getScope(mem_sym.scope_id);
                if (!mem_sym.flags.is_builtin and !mem_sym.visibility.isVisibleFrom(
                    def_scope.enclosing_module,
                    def_scope.pkg_id,
                    caller_scope,
                    caller_pkg_id,
                    &session.db.symbol_table.scope_arena,
                )) {
                    continue;
                }
                const detail_str: []const u8 = if (!mem_sym.type_id.isError() and mem_sym.type_id != .unit_ty)
                    try arena_alloc.dupe(
                        u8,
                        session.db.type_pool.formatType(mem_sym.type_id, &session.db.symbol_table, &type_buf),
                    )
                else
                    "";
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = mem_sym.name_text,
                    .kind = toLspCompletionKind(mem_sym.kind, &session.db.symbol_table.scope_arena, mem_sym.scope_id),
                    .detail = detail_str,
                    .sort_tier = if (mem_sym.kind == .enum_variant_sym) 0 else 1,
                    .is_deprecated = mem_sym.extra_flags.is_deprecated or
                        session.db.symbol_table.getDeprecatedMeta(mem_idx) != null,
                });
            }
        },
        .value_expr => |raw_recv_ty| {
            if (raw_recv_ty.isError()) return;
            // Auto-dereference `&T`, `&mut T`, `*T`, `*mut T` for member lookup while checking raw pointer/Future first:
            var deref_ty = raw_recv_ty;
            var hops: u32 = 0;
            while (!deref_ty.isPrimitiveOrSentinel() and hops < 8) : (hops += 1) {
                const n_tag = session.db.type_pool.getTag(deref_ty);
                if (n_tag == .ref_ty or n_tag == .mut_ref_ty) {
                    deref_ty = TypeId.fromInt(session.db.type_pool.getNode(deref_ty).lhs);
                } else {
                    break;
                }
            }

            if (!deref_ty.isPrimitiveOrSentinel()) {
                const recv_node = session.db.type_pool.getNode(deref_ty);
                switch (recv_node.tag) {
                    .future_ty => {
                        const out_ty = TypeId.fromInt(recv_node.lhs);
                        const out_str = try arena_alloc.dupe(
                            u8,
                            session.db.type_pool.formatType(out_ty, &session.db.symbol_table, &type_buf),
                        );
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "await",
                            .kind = 14,
                            .detail = out_str,
                            .sort_tier = 0,
                        });
                    },
                    .raw_ptr_ty => {
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "is_null",
                            .kind = 2,
                            .detail = "fn(&self) -> bool",
                            .sort_tier = 1,
                        });
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "offset",
                            .kind = 2,
                            .detail = "unsafe fn(self, count: isize) -> Self",
                            .sort_tier = 1,
                        });
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "add",
                            .kind = 2,
                            .detail = "unsafe fn(self, count: usize) -> Self",
                            .sort_tier = 1,
                        });
                    },
                    .slice_ty, .array_ty => {
                        const elem_ty = TypeId.fromInt(recv_node.lhs);
                        const elem_str = session.db.type_pool.formatType(
                            elem_ty,
                            &session.db.symbol_table,
                            &type_buf,
                        );
                        const as_ptr_detail = try std.fmt.allocPrint(
                            arena_alloc,
                            "fn(&self) -> *{s}",
                            .{elem_str},
                        );
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "len",
                            .kind = 2,
                            .detail = "fn(&self) -> usize",
                            .sort_tier = 1,
                        });
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "as_ptr",
                            .kind = 2,
                            .detail = as_ptr_detail,
                            .sort_tier = 1,
                        });
                        if (is_mutable_recv) {
                            const as_mut_ptr_detail = try std.fmt.allocPrint(
                                arena_alloc,
                                "fn(&mut self) -> *mut {s}",
                                .{elem_str},
                            );
                            try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                                .label = "as_mut_ptr",
                                .kind = 2,
                                .detail = as_mut_ptr_detail,
                                .sort_tier = 1,
                            });
                        }
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "is_empty",
                            .kind = 2,
                            .detail = "fn(&self) -> bool",
                            .sort_tier = 1,
                        });
                    },
                    .soa_slice_ty, .soa_array_ty, .soa_vec_ty => {
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "len",
                            .kind = 2,
                            .detail = "fn(&self) -> usize",
                            .sort_tier = 1,
                        });
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "is_empty",
                            .kind = 2,
                            .detail = "fn(&self) -> bool",
                            .sort_tier = 1,
                        });
                        // Expose visible `#soa` per-field column slices (`[FieldType]`):
                        const elem_ty = TypeId.fromInt(recv_node.lhs);
                        const elem_nom = unwrapTypeToNominalSymbol(
                            &session.db.type_pool,
                            &session.db.symbol_table,
                            elem_ty,
                        );
                        if (!elem_nom.isNone()) {
                            const elem_sym = session.db.symbol_table.getSymbol(elem_nom).*;
                            if (!elem_sym.target_scope.isNone()) {
                                const elem_def_scope = session.db.symbol_table.scope_arena.getScope(elem_sym.scope_id);
                                const elem_def_mod = elem_def_scope.enclosing_module;
                                const elem_pkg = elem_def_scope.pkg_id;
                                for (session.db.symbol_table.getScopeMembers(elem_sym.target_scope)) |field_idx| {
                                    const field_sym = session.db.symbol_table.getSymbol(field_idx).*;
                                    if (field_sym.kind != .field_sym) continue;
                                    if (!field_sym.flags.is_builtin and !field_sym.visibility.isVisibleFrom(
                                        elem_def_mod,
                                        elem_pkg,
                                        caller_scope,
                                        caller_pkg_id,
                                        &session.db.symbol_table.scope_arena,
                                    )) {
                                        continue;
                                    }
                                    const field_ty_str = session.db.type_pool.formatType(
                                        field_sym.type_id,
                                        &session.db.symbol_table,
                                        &type_buf,
                                    );
                                    const col_detail = try std.fmt.allocPrint(arena_alloc, "[{s}]", .{field_ty_str});
                                    try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                                        .label = field_sym.name_text,
                                        .kind = 5,
                                        .detail = col_detail,
                                        .sort_tier = 0,
                                    });
                                }
                            }
                        }
                        return;
                    },
                    .optional_ty => {
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "is_some",
                            .kind = 2,
                            .detail = "fn(&self) -> bool",
                            .sort_tier = 1,
                        });
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "is_none",
                            .kind = 2,
                            .detail = "fn(&self) -> bool",
                            .sort_tier = 1,
                        });
                    },
                    .result_ty => {
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "is_ok",
                            .kind = 2,
                            .detail = "fn(&self) -> bool",
                            .sort_tier = 1,
                        });
                        try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                            .label = "is_err",
                            .kind = 2,
                            .detail = "fn(&self) -> bool",
                            .sort_tier = 1,
                        });
                    },
                    else => {},
                }
            } else if (deref_ty == .str_ty) {
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = "len",
                    .kind = 2,
                    .detail = "fn(&self) -> usize",
                    .sort_tier = 1,
                });
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = "as_ptr",
                    .kind = 2,
                    .detail = "fn(&self) -> *u8",
                    .sort_tier = 1,
                });
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = "is_empty",
                    .kind = 2,
                    .detail = "fn(&self) -> bool",
                    .sort_tier = 1,
                });
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = "as_bytes",
                    .kind = 2,
                    .detail = "fn(self) -> [u8]",
                    .sort_tier = 1,
                });
            } else if (type_system.TypeGroupMask.containsPrimitive(type_system.TypeGroupMask.INTEGER, deref_ty)) {
                for ([_][]const u8{
                    "count_ones",
                    "leading_zeros",
                    "trailing_zeros",
                    "swap_bytes",
                    "wrapping_add",
                    "saturating_add",
                    "narrow",
                    "try_narrow",
                }) |int_method| {
                    try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                        .label = int_method,
                        .kind = 2,
                        .detail = "integer intrinsic method",
                        .sort_tier = 1,
                    });
                }
            }

            // Nominal fields, inherent methods, trait methods, and `@derive(…)` synthesized methods:
            const nom_idx = unwrapTypeToNominalSymbol(&session.db.type_pool, &session.db.symbol_table, deref_ty);
            if (nom_idx.isNone()) return;
            const nom_sym = session.db.symbol_table.getSymbol(nom_idx).*;
            if (!nom_sym.target_scope.isNone()) {
                for (session.db.symbol_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                    if (out_items.items.len >= MAX_COMPLETION_ITEMS) break;
                    const mem_sym = session.db.symbol_table.getSymbol(mem_idx).*;
                    const is_field = (mem_sym.kind == .field_sym);
                    const is_instance_method = (mem_sym.kind == .fn_sym and
                        hasMethodSelfReceiver(&session.db.symbol_table, mem_idx)) or
                        (mem_sym.kind == .overload_group_sym);
                    if (!is_field and !is_instance_method) continue;

                    const def_scope = session.db.symbol_table.scope_arena.getScope(mem_sym.scope_id);
                    if (!mem_sym.flags.is_builtin and !mem_sym.visibility.isVisibleFrom(
                        def_scope.enclosing_module,
                        def_scope.pkg_id,
                        caller_scope,
                        caller_pkg_id,
                        &session.db.symbol_table.scope_arena,
                    )) {
                        continue;
                    }
                    const detail_str: []const u8 = if (!mem_sym.type_id.isError() and mem_sym.type_id != .unit_ty)
                        try arena_alloc.dupe(
                            u8,
                            session.db.type_pool.formatType(mem_sym.type_id, &session.db.symbol_table, &type_buf),
                        )
                    else
                        "";
                    try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                        .label = mem_sym.name_text,
                        .kind = if (is_field) 5 else 2,
                        .detail = detail_str,
                        .sort_tier = if (is_field) 0 else 1,
                        .is_deprecated = mem_sym.extra_flags.is_deprecated or
                            session.db.symbol_table.getDeprecatedMeta(mem_idx) != null,
                    });
                }
            }

            // `@derive(Equatable, Comparable, Hash, Debug, Clone)` synthesized methods:
            if (nom_sym.derive_mask.has_equatable) {
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = "eq",
                    .kind = 2,
                    .detail = "fn(&self, other: &Self) -> bool",
                    .sort_tier = 1,
                });
            }
            if (nom_sym.derive_mask.has_comparable) {
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = "cmp",
                    .kind = 2,
                    .detail = "fn(&self, other: &Self) -> Ordering",
                    .sort_tier = 1,
                });
            }
            if (nom_sym.derive_mask.has_hash) {
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = "hash",
                    .kind = 2,
                    .detail = "fn(&self) -> u64",
                    .sort_tier = 1,
                });
            }
            if (nom_sym.derive_mask.has_debug) {
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = "debug",
                    .kind = 2,
                    .detail = "fn(&self) -> str",
                    .sort_tier = 1,
                });
            }
            if (nom_sym.derive_mask.has_clone) {
                try appendUniqueCompletion(arena_alloc, seen_labels, out_items, prefix, .{
                    .label = "clone",
                    .kind = 2,
                    .detail = "fn(&self) -> Self",
                    .sort_tier = 1,
                });
            }
        },
    }
}

/// Appends live `.param_sym`, `.type_param_sym`, and `.const_param_sym` handles owned by `entry` into `out_syms`.
fn collectEntryLiveScopeParamSymbols(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    entry: query_db.ItemTreeEntry,
    out_syms: *std.ArrayListUnmanaged(SymbolIndex),
) !void {
    if (entry.def_id.isNone()) return;
    const entry_fid = entry.def_id.fileId();
    _ = session.db.resolveSignatures(entry_fid) catch {};
    if (entry.kind != .mod_decl and entry.kind != .use_decl and entry.kind != .ffi_extern_block) {
        _ = session.db.getDefSignature(entry.def_id) catch {};
    }

    if (session.db.symbol_table.def_to_symbol.get(entry.def_id.asInt())) |entry_sym_idx| {
        const entry_sym = session.db.symbol_table.getSymbol(entry_sym_idx).*;
        if (!entry_sym.target_scope.isNone()) {
            for (session.db.symbol_table.getScopeMembers(entry_sym.target_scope)) |mem_idx| {
                const mem_sym = session.db.symbol_table.getSymbol(mem_idx).*;
                switch (mem_sym.kind) {
                    .param_sym, .type_param_sym, .const_param_sym => try out_syms.append(arena_alloc, mem_idx),
                    .fn_sym => {
                        if (!mem_sym.target_scope.isNone()) {
                            for (session.db.symbol_table.getScopeMembers(mem_sym.target_scope)) |sub_idx| {
                                const sub_sym = session.db.symbol_table.getSymbol(sub_idx).*;
                                switch (sub_sym.kind) {
                                    .param_sym, .type_param_sym, .const_param_sym => {
                                        try out_syms.append(arena_alloc, sub_idx);
                                    },
                                    else => {},
                                }
                            }
                        }
                    },
                    else => {},
                }
            }
        }
    }

    if (session.db.getFileLiveSymbolBounds(entry_fid)) |bounds| {
        var sym_raw = bounds.sym_start;
        while (sym_raw < bounds.sym_end and sym_raw < session.db.symbol_table.countSymbols()) : (sym_raw += 1) {
            const cand_idx = SymbolIndex.fromInt(sym_raw);
            const cand_sym = session.db.symbol_table.getSymbol(cand_idx).*;
            if (cand_sym.owner_def_id != entry.def_id) continue;
            if (!cand_sym.target_scope.isNone()) {
                for (session.db.symbol_table.getScopeMembers(cand_sym.target_scope)) |param_idx| {
                    const param_sym = session.db.symbol_table.getSymbol(param_idx).*;
                    switch (param_sym.kind) {
                        .param_sym, .type_param_sym, .const_param_sym => {
                            try out_syms.append(arena_alloc, param_idx);
                        },
                        else => {},
                    }
                }
            }
        }
    }
}

/// Emits an empty completion list `{"isIncomplete":false,"items":[]}` JSON-RPC frame.
fn writeEmptyCompletionListFrame(
    session: *LspSession,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":{\"isIncomplete\":false,\"items\":[]}}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Returns whether `slice[start_idx..]` begins with at least `expected_hashes` `'#'` bytes.
inline fn hasFmtHashRunAt(slice: []const u8, start_idx: usize, expected_hashes: usize) bool {
    if (start_idx + expected_hashes > slice.len) return false;
    var hash_idx: usize = 0;
    while (hash_idx < expected_hashes) : (hash_idx += 1) {
        if (slice[start_idx + hash_idx] != '#') return false;
    }
    return true;
}

/// Returns whether `byte_val` can continue an ASCII identifier (`[A-Za-z0-9_]`).
inline fn isFmtIdentContinueByte(byte_val: u8) bool {
    return std.ascii.isAlphanumeric(byte_val) or byte_val == '_';
}

/// Skips a non-interpolated `'…'`, `b'…'`, `"…"`, or `b"…"` literal starting right after its opening quote.
fn skipPlainQuotedInFmtHole(slice: []const u8, after_open_idx: usize, quote_byte: u8) usize {
    var cursor = after_open_idx;
    while (cursor < slice.len) {
        if (slice[cursor] == '\\') {
            cursor = @min(cursor + 2, slice.len);
            continue;
        }
        if (slice[cursor] == quote_byte) return cursor + 1;
        cursor += 1;
    }
    return slice.len;
}

/// Skips a raw `r"…"`, `r#"…"#`, `br"…"`, or `br#"…"#` literal starting right after `'r'`.
fn skipRawQuotedInFmtHole(slice: []const u8, after_r_idx: usize) ?struct { body_open: usize, lit_end: usize } {
    var cursor = after_r_idx;
    var hash_count: usize = 0;
    while (cursor < slice.len and slice[cursor] == '#') : (cursor += 1) {
        hash_count += 1;
    }
    if (cursor >= slice.len or slice[cursor] != '"') return null;
    const body_open = cursor;
    cursor += 1;
    while (cursor < slice.len) : (cursor += 1) {
        if (slice[cursor] == '"' and hasFmtHashRunAt(slice, cursor + 1, hash_count)) {
            return .{ .body_open = body_open, .lit_end = cursor + 1 + hash_count };
        }
    }
    return .{ .body_open = body_open, .lit_end = slice.len };
}

/// Scans to the closing `"#*` of a nested `f"…"` / `f#"…"#` literal starting at `'f'` (`f_idx`).
fn findNestedFmtStringEndInHole(slice: []const u8, f_idx: usize, depth: u8) ?usize {
    if (depth >= 16 or f_idx + 1 >= slice.len or slice[f_idx] != 'f') return null;
    var cursor = f_idx + 1;
    var hash_count: usize = 0;
    while (cursor < slice.len and slice[cursor] == '#') : (cursor += 1) {
        hash_count += 1;
    }
    if (cursor >= slice.len or slice[cursor] != '"') return null;
    cursor += 1;

    while (cursor < slice.len) {
        const cur_byte = slice[cursor];
        if (hash_count == 0 and cur_byte == '\\') {
            cursor = @min(cursor + 2, slice.len);
            continue;
        }
        if (cur_byte == '"' and hasFmtHashRunAt(slice, cursor + 1, hash_count)) {
            return cursor + 1 + hash_count;
        }
        if (cur_byte == '{') {
            if (cursor + 1 < slice.len and slice[cursor + 1] == '{') {
                cursor += 2;
                continue;
            }
            cursor += 1;
            var inner_braces: u32 = 1;
            while (cursor < slice.len and inner_braces > 0) {
                const hole_ch = slice[cursor];
                if (hole_ch == '{') {
                    inner_braces += 1;
                    cursor += 1;
                } else if (hole_ch == '}') {
                    inner_braces -= 1;
                    cursor += 1;
                } else if (hole_ch == 'f' and
                    (cursor == 0 or !isFmtIdentContinueByte(slice[cursor - 1])) and
                    cursor + 1 < slice.len and (slice[cursor + 1] == '"' or slice[cursor + 1] == '#'))
                {
                    if (findNestedFmtStringEndInHole(slice, cursor, depth + 1)) |nested_end| {
                        cursor = nested_end;
                    } else {
                        cursor += 1;
                    }
                } else if (hole_ch == 'r' and
                    (cursor == 0 or !isFmtIdentContinueByte(slice[cursor - 1])) and
                    cursor + 1 < slice.len and (slice[cursor + 1] == '"' or slice[cursor + 1] == '#'))
                {
                    if (skipRawQuotedInFmtHole(slice, cursor + 1)) |raw_span| {
                        cursor = raw_span.lit_end;
                    } else {
                        cursor += 1;
                    }
                } else if (hole_ch == 'b' and
                    (cursor == 0 or !isFmtIdentContinueByte(slice[cursor - 1])) and
                    cursor + 1 < slice.len)
                {
                    if (slice[cursor + 1] == '\'' or slice[cursor + 1] == '"') {
                        cursor = skipPlainQuotedInFmtHole(slice, cursor + 2, slice[cursor + 1]);
                    } else if (slice[cursor + 1] == 'r') {
                        if (skipRawQuotedInFmtHole(slice, cursor + 2)) |raw_span| {
                            cursor = raw_span.lit_end;
                        } else {
                            cursor += 1;
                        }
                    } else {
                        cursor += 1;
                    }
                } else if (hole_ch == '"' or hole_ch == '\'') {
                    cursor = skipPlainQuotedInFmtHole(slice, cursor + 1, hole_ch);
                } else if (hole_ch == '/' and cursor + 1 < slice.len and slice[cursor + 1] == '/') {
                    cursor += 2;
                    while (cursor < slice.len and slice[cursor] != '\n' and slice[cursor] != '\r') : (cursor += 1) {}
                } else {
                    cursor += 1;
                }
            }
            continue;
        }
        cursor += 1;
    }
    return slice.len;
}

/// Bounded recursive worker checking whether `rel_cursor` sits inside an active `{…}` hole of `fmt_lexeme`.
fn isCursorInsideFmtStringHoleDepth(fmt_lexeme: []const u8, rel_cursor: usize, depth: u8) bool {
    if (depth >= 16) return false;
    const body_info = lexer.extractStringBodyInfo(.fmt_string_lit, fmt_lexeme);
    const body_start: usize = @min(@as(usize, body_info.body_start), fmt_lexeme.len);
    const body_end: usize = @min(@as(usize, body_info.body_end), fmt_lexeme.len);
    if (rel_cursor < body_start or rel_cursor > body_end) return false;

    const body_limit_slice = fmt_lexeme[0..body_end];
    const scan_limit = @min(rel_cursor, body_end);
    var brace_depth: u32 = 0;
    var idx: usize = body_start;
    while (idx < scan_limit) {
        const ch_val = fmt_lexeme[idx];
        if (brace_depth == 0) {
            if (!body_info.is_raw and ch_val == '\\') {
                idx = @min(idx + 2, scan_limit);
                continue;
            }
            if (ch_val == '{') {
                if (idx + 1 < body_end and fmt_lexeme[idx + 1] == '{') {
                    idx = @min(idx + 2, scan_limit);
                    continue;
                }
                brace_depth = 1;
            } else if (ch_val == '}' and idx + 1 < body_end and fmt_lexeme[idx + 1] == '}') {
                idx = @min(idx + 2, scan_limit);
                continue;
            }
            idx += 1;
        } else {
            if (ch_val == 'f' and
                (idx == body_start or !isFmtIdentContinueByte(fmt_lexeme[idx - 1])) and
                idx + 1 < body_end and (fmt_lexeme[idx + 1] == '"' or fmt_lexeme[idx + 1] == '#'))
            {
                if (findNestedFmtStringEndInHole(body_limit_slice, idx, depth + 1)) |nested_end| {
                    if (rel_cursor < nested_end) {
                        return isCursorInsideFmtStringHoleDepth(fmt_lexeme[idx..nested_end], rel_cursor - idx, depth + 1);
                    }
                    idx = @min(nested_end, scan_limit);
                    continue;
                }
            } else if (ch_val == 'r' and
                (idx == body_start or !isFmtIdentContinueByte(fmt_lexeme[idx - 1])) and
                idx + 1 < body_end and (fmt_lexeme[idx + 1] == '"' or fmt_lexeme[idx + 1] == '#'))
            {
                if (skipRawQuotedInFmtHole(body_limit_slice, idx + 1)) |raw_span| {
                    if (rel_cursor > raw_span.body_open and rel_cursor < raw_span.lit_end) return false;
                    idx = @min(raw_span.lit_end, scan_limit);
                    continue;
                }
            } else if (ch_val == 'b' and
                (idx == body_start or !isFmtIdentContinueByte(fmt_lexeme[idx - 1])) and
                idx + 1 < body_end)
            {
                if (fmt_lexeme[idx + 1] == '\'' or fmt_lexeme[idx + 1] == '"') {
                    const lit_end = skipPlainQuotedInFmtHole(body_limit_slice, idx + 2, fmt_lexeme[idx + 1]);
                    if (rel_cursor > idx + 1 and rel_cursor < lit_end) return false;
                    idx = @min(lit_end, scan_limit);
                    continue;
                } else if (fmt_lexeme[idx + 1] == 'r') {
                    if (skipRawQuotedInFmtHole(body_limit_slice, idx + 2)) |raw_span| {
                        if (rel_cursor > raw_span.body_open and rel_cursor < raw_span.lit_end) return false;
                        idx = @min(raw_span.lit_end, scan_limit);
                        continue;
                    }
                }
            } else if (ch_val == '"' or ch_val == '\'') {
                const lit_end = skipPlainQuotedInFmtHole(body_limit_slice, idx + 1, ch_val);
                if (rel_cursor > idx and rel_cursor < lit_end) return false;
                idx = @min(lit_end, scan_limit);
                continue;
            } else if (ch_val == '/' and idx + 1 < body_end and fmt_lexeme[idx + 1] == '/') {
                var cmt_end = idx + 2;
                while (cmt_end < body_end and fmt_lexeme[cmt_end] != '\n' and fmt_lexeme[cmt_end] != '\r') : (cmt_end += 1) {}
                if (rel_cursor <= cmt_end) return false;
                idx = @min(cmt_end, scan_limit);
                continue;
            }

            if (ch_val == '{') {
                brace_depth += 1;
            } else if (ch_val == '}') {
                brace_depth -= 1;
            }
            idx += 1;
        }
    }
    return brace_depth > 0;
}

/// Returns `true` when `cursor_byte` sits inside the `(…)` selector list of `@expect(…)` or `@allow(…)`.
fn isCursorInsideLintAttrArgs(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cursor_byte: u32,
) bool {
    var paren_stack: [32]TokenIndex = undefined;
    var stack_len: usize = 0;
    const tok_count = token_buffer.countTokens();
    var i: usize = 0;
    while (i < tok_count) : (i += 1) {
        const tok_id = TokenIndex.fromInt(@intCast(i));
        const tok_rec = token_buffer.getToken(tok_id);
        if (tok_rec.flags.is_synthesized or tok_rec.kind == .eof) continue;
        if (tok_rec.byte_offset >= cursor_byte) break;
        if (tok_rec.kind == .lparen) {
            if (stack_len < paren_stack.len) {
                paren_stack[stack_len] = tok_id;
                stack_len += 1;
            }
        } else if (tok_rec.kind == .rparen) {
            if (stack_len > 0) stack_len -= 1;
        }
    }
    if (stack_len == 0) return false;
    const open_paren = paren_stack[stack_len - 1];
    if (open_paren.asInt() < 2) return false;
    const name_tok = TokenIndex.fromInt(open_paren.asInt() - 1);
    const at_tok = TokenIndex.fromInt(open_paren.asInt() - 2);
    if (token_buffer.getToken(at_tok).kind != .at) return false;
    const attr_name = symbol_resolver.extractTokenSlice(source, token_buffer, name_tok);
    return std.mem.eql(u8, attr_name, "expect") or std.mem.eql(u8, attr_name, "allow");
}

/// Handles `textDocument/completion`: dot-completion (`IncompleteDotTarget`), `@` attributes, and lexical scope (`<= 256`).
fn handleCompletionRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const pos = extractJsonPosition(params.getField("position") orelse JsonValue{ .null_val = {} }) orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing position");
    };

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);

    const src = getLiveDocumentSource(session, fid) orelse "";
    const cursor_byte = lspPositionToByteOffset(session, fid, pos);
    _ = try session.db.parseCst(fid);
    _ = try session.db.resolveSignatures(fid);
    const entries = try arena_alloc.dupe(
        query_db.ItemTreeEntry,
        (try session.db.extractItemTree(fid)).entries,
    );
    var parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse
        return writeNullResultFrame(session, out_writer, rpc_id);

    const caller_pkg_id = session.db.symbol_table.getFilePackageId(fid);
    const mod_scope = session.db.symbol_table.file_module_scopes.get(fid.asInt()) orelse
        session.db.symbol_table.prelude_scope;

    // Extract typed identifier prefix and inspect preceding punctuation (`.` or `@`):
    var ident_start: usize = cursor_byte;
    while (ident_start > 0) {
        const prev_ch = src[ident_start - 1];
        if (std.ascii.isAlphanumeric(prev_ch) or prev_ch == '_') {
            ident_start -= 1;
        } else {
            break;
        }
    }
    const prefix = src[ident_start..cursor_byte];
    var trigger_pos: usize = ident_start;
    while (trigger_pos > 0 and (src[trigger_pos - 1] == ' ' or src[trigger_pos - 1] == '\t')) : (trigger_pos -= 1) {}
    const is_after_at = (trigger_pos > 0 and src[trigger_pos - 1] == '@');
    const is_after_dot = (trigger_pos > 0 and src[trigger_pos - 1] == '.');
    const dot_byte_offset: u32 = if (is_after_dot) @intCast(trigger_pos - 1) else 0;

    var items: std.ArrayListUnmanaged(CompletionCandidate) = .empty;
    var seen_labels: std.StringHashMapUnmanaged(void) = .empty;

    // Suppress completions inside non-interpolated string/char literals or outside `{…}` inside `.fmt_string_lit`:
    var is_inside_fmt_hole = false;
    {
        const container_tok = findTokenAtCursorByte(&parsed_art.token_buffer, cursor_byte);
        if (!container_tok.isNone() and container_tok.asInt() < parsed_art.token_buffer.countTokens()) {
            const container_rec = parsed_art.token_buffer.getToken(container_tok);
            const tok_start_u: usize = container_rec.byte_offset;
            const tok_end_u: usize = container_rec.byte_offset +| container_rec.byte_len;
            if (cursor_byte > tok_start_u and cursor_byte < tok_end_u) {
                switch (container_rec.kind) {
                    .string_lit, .byte_string_lit, .char_lit, .byte_lit => {
                        return writeEmptyCompletionListFrame(session, out_writer, rpc_id);
                    },
                    .fmt_string_lit => {
                        is_inside_fmt_hole = isCursorInsideFmtStringHoleDepth(
                            src[tok_start_u..@min(tok_end_u, src.len)],
                            cursor_byte - tok_start_u,
                            0,
                        );
                        if (!is_inside_fmt_hole) {
                            return writeEmptyCompletionListFrame(session, out_writer, rpc_id);
                        }
                    },
                    else => {},
                }
            }
        }
    }

    const is_inside_lint_attr = !is_inside_fmt_hole and
        isCursorInsideLintAttrArgs(src, &parsed_art.token_buffer, cursor_byte);

    if (is_inside_lint_attr) {
        var lint_start: usize = cursor_byte;
        while (lint_start > 0) {
            const prev_ch = src[lint_start - 1];
            if (std.ascii.isAlphanumeric(prev_ch) or prev_ch == '-' or prev_ch == '_') {
                lint_start -= 1;
            } else {
                break;
            }
        }
        const lint_prefix = src[lint_start..cursor_byte];
        for (diagnostic.DIAGNOSTIC_LINT_CATALOG) |lint_meta| {
            try appendUniqueCompletion(arena_alloc, &seen_labels, &items, lint_prefix, .{
                .label = lint_meta.slug,
                .kind = 20,
                .detail = lint_meta.diag_code.asCodeStr(),
                .sort_tier = 0,
            });
        }
        try appendUniqueCompletion(arena_alloc, &seen_labels, &items, lint_prefix, .{
            .label = "reason",
            .kind = 10,
            .detail = "reason: \"…\" rationale",
            .sort_tier = 1,
        });
    } else if (is_after_at) {
        if (!is_inside_fmt_hole) {
            try appendUniqueCompletion(arena_alloc, &seen_labels, &items, prefix, .{
                .label = "expect",
                .kind = 24,
                .detail = "@attribute",
                .sort_tier = 0,
            });
            for (type_system.BUILTIN_ATTRIBUTE_MAP.keys()) |attr_name| {
                if (RETIRED_BUILTIN_ATTR_SET.has(attr_name)) continue;
                try appendUniqueCompletion(arena_alloc, &seen_labels, &items, prefix, .{
                    .label = attr_name,
                    .kind = 24,
                    .detail = "@attribute",
                    .sort_tier = 0,
                });
            }
        }
        for (type_system.INTRINSIC_NAME_MAP.keys()) |intr_name| {
            try appendUniqueCompletion(arena_alloc, &seen_labels, &items, prefix, .{
                .label = intr_name,
                .kind = 3,
                .detail = "@intrinsic",
                .sort_tier = 1,
            });
        }
    } else if (is_after_dot) {
        var resolved_dot_target: ?IncompleteDotTarget = null;
        var matched_side_tables: ?*const BodySemanticSideTables = null;
        var matched_recv_ast: NodeIndex = .none;

        // Locate enclosing `DefId` and match `.incomplete_member_access` or `.field_access`/`.method_call`:
        for (entries) |entry| {
            if (entry.kind == .mod_decl or entry.kind == .use_decl or entry.kind == .ffi_extern_block) continue;
            const entry_span = computeCstSubtreeByteSpan(
                fid,
                &parsed_art.token_buffer,
                &parsed_art.cst_arena,
                entry.cst_node,
            ) orelse continue;
            if (dot_byte_offset < entry_span.start_byte or dot_byte_offset > entry_span.end_byte) continue;

            if (try session.db.getDefSideTables(entry.def_id)) |side_tables| {
                parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse
                    return writeNullResultFrame(session, out_writer, rpc_id);
                matched_side_tables = side_tables;
                var ast_raw = side_tables.ast_start;
                const ast_limit = @min(side_tables.ast_end, @as(u32, @intCast(parsed_art.ast_arena.countNodes())));
                while (ast_raw < ast_limit) : (ast_raw += 1) {
                    const ast_id = NodeIndex.fromInt(ast_raw);
                    const ast_node = parsed_art.ast_arena.getNode(ast_id);
                    if (ast_node.tag == .incomplete_member_access) {
                        if (side_tables.getIncompleteDotTarget(ast_id)) |dot_tgt| {
                            const cand_recv = if (ast_node.lhs.tag == .node)
                                NodeIndex.fromInt(ast_node.lhs.payload)
                            else
                                NodeIndex.none;
                            if (!ast_node.main_token.isNone() and
                                ast_node.main_token.asInt() < parsed_art.token_buffer.countTokens())
                            {
                                const m_off = parsed_art.token_buffer.getToken(ast_node.main_token).byte_offset;
                                if (m_off == dot_byte_offset) {
                                    resolved_dot_target = dot_tgt;
                                    matched_recv_ast = cand_recv;
                                    break;
                                }
                            }
                            if (resolved_dot_target == null) {
                                resolved_dot_target = dot_tgt;
                                matched_recv_ast = cand_recv;
                            }
                        }
                    } else if ((ast_node.tag == .field_access or ast_node.tag == .method_call) and
                        !ast_node.main_token.isNone() and
                        ast_node.main_token.asInt() < parsed_art.token_buffer.countTokens())
                    {
                        const m_off = parsed_art.token_buffer.getToken(ast_node.main_token).byte_offset;
                        if (m_off == dot_byte_offset and ast_node.lhs.tag == .node) {
                            const recv_id = NodeIndex.fromInt(ast_node.lhs.payload);
                            matched_recv_ast = recv_id;
                            const recv_sym = side_tables.getNodeSymbol(recv_id);
                            const recv_ty = side_tables.getNodeType(recv_id);
                            if (!recv_sym.isNone()) {
                                const r_rec = session.db.symbol_table.getSymbol(
                                    session.db.symbol_table.unwrapAliasSymbolIdx(recv_sym),
                                ).*;
                                if (r_rec.kind == .module_sym) {
                                    resolved_dot_target = .{ .module_ns = r_rec.target_scope };
                                    break;
                                } else if (r_rec.namespace == .type_ns) {
                                    resolved_dot_target = .{ .type_ns = r_rec.type_id };
                                    break;
                                }
                            }
                            if (!recv_ty.isError()) {
                                resolved_dot_target = .{ .value_expr = recv_ty };
                                break;
                            }
                        }
                    }
                }

                // Also inspect `side_tables.string_interps` (`incomplete_dots` + `hole.tokens`) via live `fmt_tok_base`:
                if (resolved_dot_target == null) {
                    var best_dot_hole_span: u32 = std.math.maxInt(u32);
                    var interp_it = side_tables.string_interps.iterator();
                    while (interp_it.next()) |interp_kv| {
                        const fmt_ast_raw = side_tables.ast_start + interp_kv.key_ptr.*;
                        if (fmt_ast_raw >= ast_limit) continue;
                        const fmt_main_tok = parsed_art.ast_arena.getNode(NodeIndex.fromInt(fmt_ast_raw)).main_token;
                        if (fmt_main_tok.isNone() or fmt_main_tok.asInt() >= parsed_art.token_buffer.countTokens()) {
                            continue;
                        }
                        const fmt_rec = parsed_art.token_buffer.getToken(fmt_main_tok);
                        const fmt_tok_base = fmt_rec.byte_offset;
                        const fmt_tok_end = fmt_tok_base +| fmt_rec.byte_len;
                        if (dot_byte_offset < fmt_tok_base or dot_byte_offset >= fmt_tok_end) continue;

                        for (interp_kv.value_ptr.holes) |hole| {
                            const open_abs = fmt_tok_base +| hole.rel_brace_open_byte;
                            const close_abs = fmt_tok_base +| hole.rel_brace_close_byte;
                            if (dot_byte_offset <= open_abs or dot_byte_offset >= close_abs) continue;
                            const cand_hole_span = close_abs -| open_abs;
                            if (resolved_dot_target != null and cand_hole_span >= best_dot_hole_span) continue;

                            var hole_dot_target: ?IncompleteDotTarget = null;
                            for (hole.incomplete_dots) |dot_info| {
                                if (fmt_tok_base +| dot_info.rel_trigger_end_byte == dot_byte_offset +| 1 and
                                    !dot_info.receiver_type_id.isError())
                                {
                                    var is_type_ns_recv = false;
                                    for (hole.tokens) |cand_htok| {
                                        const cand_end = fmt_tok_base +| cand_htok.rel_byte +| @as(u32, cand_htok.byte_len);
                                        if (cand_end == dot_byte_offset and !cand_htok.symbol_index.isNone()) {
                                            const unwrapped_cand = session.db.symbol_table.unwrapAliasSymbolIdx(
                                                cand_htok.symbol_index,
                                            );
                                            if (session.db.symbol_table.getSymbol(unwrapped_cand).namespace == .type_ns) {
                                                is_type_ns_recv = true;
                                            }
                                            break;
                                        }
                                    }
                                    hole_dot_target = if (is_type_ns_recv)
                                        .{ .type_ns = dot_info.receiver_type_id }
                                    else
                                        .{ .value_expr = dot_info.receiver_type_id };
                                    break;
                                }
                            }

                            if (hole_dot_target == null) {
                                for (hole.tokens, 0..) |htok, htok_i| {
                                    if (htok.kind != .dot or fmt_tok_base +| htok.rel_byte != dot_byte_offset) continue;
                                    if (htok_i == 0) break;
                                    const recv_htok = hole.tokens[htok_i - 1];
                                    if (!recv_htok.symbol_index.isNone()) {
                                        const recv_rec = session.db.symbol_table.getSymbol(
                                            session.db.symbol_table.unwrapAliasSymbolIdx(recv_htok.symbol_index),
                                        ).*;
                                        if (recv_rec.kind == .module_sym) {
                                            hole_dot_target = .{ .module_ns = recv_rec.target_scope };
                                        } else if (recv_rec.namespace == .type_ns) {
                                            hole_dot_target = .{ .type_ns = recv_rec.type_id };
                                        } else if (!recv_htok.type_id.isError()) {
                                            hole_dot_target = .{ .value_expr = recv_htok.type_id };
                                        } else if (!recv_rec.type_id.isError()) {
                                            hole_dot_target = .{ .value_expr = recv_rec.type_id };
                                        }
                                    } else if (!recv_htok.type_id.isError()) {
                                        hole_dot_target = .{ .value_expr = recv_htok.type_id };
                                    }
                                    break;
                                }
                            }

                            if (hole_dot_target) |matched_target| {
                                resolved_dot_target = matched_target;
                                best_dot_hole_span = cand_hole_span;
                            }
                        }
                    }
                }
            }
            break;
        }

        // Fallback token-before-dot lookup (`cx.`, `pkg.`, `ModName.`, `EnumName.`, including inside `f"…"` holes):
        if (resolved_dot_target == null and dot_byte_offset > 0) {
            const recv_tok = findTokenAtCursorByte(&parsed_art.token_buffer, dot_byte_offset - 1);
            var recv_lex: []const u8 = "";
            if (!recv_tok.isNone()) {
                if (parsed_art.token_buffer.getToken(recv_tok).kind == .fmt_string_lit) {
                    var scan_end: usize = @min(@as(usize, dot_byte_offset), src.len);
                    while (scan_end > 0 and (src[scan_end - 1] == ' ' or src[scan_end - 1] == '\t')) : (scan_end -= 1) {}
                    var scan_start = scan_end;
                    while (scan_start > 0 and
                        (std.ascii.isAlphanumeric(src[scan_start - 1]) or src[scan_start - 1] == '_')) : (scan_start -= 1)
                    {}
                    recv_lex = src[scan_start..scan_end];
                } else {
                    recv_lex = symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, recv_tok);
                }
            }
            if (recv_lex.len > 0) {
                if (std.mem.eql(u8, recv_lex, "cx") or
                    (session.options.is_internal_core and std.mem.eql(u8, recv_lex, "core")))
                {
                    const cx_scope = try session.db.symbol_table.ensureCxRootScope(&session.db.interner);
                    resolved_dot_target = .{ .module_ns = cx_scope };
                } else if (session.db.interner.lookup(recv_lex)) |recv_name_id| {
                    switch (session.db.symbol_table.lookupLexical(mod_scope, recv_name_id, NamespaceMask.ALL)) {
                        .found => |found_idx| {
                            const found_sym = session.db.symbol_table.getSymbol(
                                session.db.symbol_table.unwrapAliasSymbolIdx(found_idx),
                            ).*;
                            if (found_sym.kind == .module_sym) {
                                resolved_dot_target = .{ .module_ns = found_sym.target_scope };
                            } else if (found_sym.namespace == .type_ns) {
                                resolved_dot_target = .{ .type_ns = found_sym.type_id };
                            } else if (!found_sym.type_id.isError()) {
                                resolved_dot_target = .{ .value_expr = found_sym.type_id };
                            }
                        },
                        else => {},
                    }
                }
            }
        }

        if (resolved_dot_target) |dot_tgt| {
            const is_mutable_recv = switch (dot_tgt) {
                .value_expr => |raw_recv_ty| isCompletionDotReceiverMutable(
                    session,
                    src,
                    parsed_art,
                    mod_scope,
                    matched_side_tables,
                    matched_recv_ast,
                    raw_recv_ty,
                    dot_byte_offset,
                ),
                .module_ns, .type_ns => false,
            };
            try populateDotTargetCompletions(
                session,
                arena_alloc,
                mod_scope,
                caller_pkg_id,
                dot_tgt,
                is_mutable_recv,
                prefix,
                &seen_labels,
                &items,
            );
        }
    } else {
        // Lexical scope completion; active `DefId` live locals/params + module chain + `cx` + keywords:
        var type_buf: [256]u8 = undefined;
        for (entries) |entry| {
            if (entry.kind == .mod_decl or entry.kind == .use_decl or entry.kind == .ffi_extern_block) continue;
            const entry_span = computeCstSubtreeByteSpan(
                fid,
                &parsed_art.token_buffer,
                &parsed_art.cst_arena,
                entry.cst_node,
            ) orelse continue;
            if (cursor_byte < entry_span.start_byte or cursor_byte > entry_span.end_byte) continue;

            var live_param_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty;
            try collectEntryLiveScopeParamSymbols(session, arena_alloc, entry, &live_param_syms);
            for (live_param_syms.items) |param_idx| {
                if (items.items.len >= MAX_COMPLETION_ITEMS) break;
                const param_sym = session.db.symbol_table.getSymbol(param_idx).*;
                const detail_str: []const u8 = if (!param_sym.type_id.isError() and param_sym.type_id != .unit_ty)
                    try arena_alloc.dupe(
                        u8,
                        session.db.type_pool.formatType(param_sym.type_id, &session.db.symbol_table, &type_buf),
                    )
                else
                    "";
                try appendUniqueCompletion(arena_alloc, &seen_labels, &items, prefix, .{
                    .label = param_sym.name_text,
                    .kind = toLspCompletionKind(param_sym.kind, &session.db.symbol_table.scope_arena, param_sym.scope_id),
                    .detail = detail_str,
                    .sort_tier = 0,
                });
            }

            if (session.db.getDefSideTables(entry.def_id) catch null) |side_tables| {
                parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse
                    return writeNullResultFrame(session, out_writer, rpc_id);
                var seen_local_syms: std.AutoHashMapUnmanaged(u32, void) = .empty;
                var ast_raw = side_tables.ast_start;
                const ast_limit = @min(side_tables.ast_end, @as(u32, @intCast(parsed_art.ast_arena.countNodes())));
                while (ast_raw < ast_limit and items.items.len < MAX_COMPLETION_ITEMS) : (ast_raw += 1) {
                    const ast_id = NodeIndex.fromInt(ast_raw);
                    const sym_idx = side_tables.getNodeSymbol(ast_id);
                    if (sym_idx.isNone() or sym_idx.asInt() >= session.db.symbol_table.countSymbols()) continue;
                    const sym = session.db.symbol_table.getSymbol(sym_idx).*;
                    const is_local_binding = switch (sym.kind) {
                        .local_let_sym, .local_var_sym, .param_sym => true,
                        else => false,
                    };
                    if (!is_local_binding) continue;
                    if ((try seen_local_syms.getOrPut(arena_alloc, sym_idx.asInt())).found_existing) continue;
                    const main_tok = parsed_art.ast_arena.getNode(ast_id).main_token;
                    if (!main_tok.isNone() and main_tok.asInt() < parsed_art.token_buffer.countTokens()) {
                        if (parsed_art.token_buffer.getToken(main_tok).byte_offset > cursor_byte) continue;
                    }
                    const detail_str: []const u8 = if (!sym.type_id.isError() and sym.type_id != .unit_ty)
                        try arena_alloc.dupe(
                            u8,
                            session.db.type_pool.formatType(sym.type_id, &session.db.symbol_table, &type_buf),
                        )
                    else
                        "";
                    try appendUniqueCompletion(arena_alloc, &seen_labels, &items, prefix, .{
                        .label = sym.name_text,
                        .kind = toLspCompletionKind(sym.kind, &session.db.symbol_table.scope_arena, sym.scope_id),
                        .detail = detail_str,
                        .sort_tier = 0,
                    });
                }
            }
            break;
        }

        // Walk `mod_scope` -> `.global_prelude` enforcing `Visibility.isVisibleFrom`:
        var cur_scope = mod_scope;
        var scope_hops: usize = 0;
        while (!cur_scope.isNone() and cur_scope.asInt() < session.db.symbol_table.scope_arena.countScopes() and
            scope_hops < 32 and items.items.len < MAX_COMPLETION_ITEMS) : (scope_hops += 1)
        {
            for (session.db.symbol_table.getScopeMembers(cur_scope)) |mem_idx| {
                if (items.items.len >= MAX_COMPLETION_ITEMS) break;
                const mem_sym = session.db.symbol_table.getSymbol(mem_idx).*;
                if (!session.options.is_internal_core and std.mem.eql(u8, mem_sym.name_text, "core")) continue;
                const def_scope = session.db.symbol_table.scope_arena.getScope(mem_sym.scope_id);
                if (!mem_sym.flags.is_builtin and !mem_sym.visibility.isVisibleFrom(
                    def_scope.enclosing_module,
                    def_scope.pkg_id,
                    mod_scope,
                    caller_pkg_id,
                    &session.db.symbol_table.scope_arena,
                )) {
                    continue;
                }
                const detail_str: []const u8 = if (!mem_sym.type_id.isError() and mem_sym.type_id != .unit_ty)
                    try arena_alloc.dupe(
                        u8,
                        session.db.type_pool.formatType(mem_sym.type_id, &session.db.symbol_table, &type_buf),
                    )
                else
                    "";
                try appendUniqueCompletion(arena_alloc, &seen_labels, &items, prefix, .{
                    .label = mem_sym.name_text,
                    .kind = toLspCompletionKind(mem_sym.kind, &session.db.symbol_table.scope_arena, mem_sym.scope_id),
                    .detail = detail_str,
                    .sort_tier = if (cur_scope == mod_scope) 1 else 2,
                    .is_deprecated = mem_sym.extra_flags.is_deprecated or
                        session.db.symbol_table.getDeprecatedMeta(mem_idx) != null,
                });
            }
            cur_scope = session.db.symbol_table.scope_arena.getScope(cur_scope).parent;
        }

        try appendUniqueCompletion(arena_alloc, &seen_labels, &items, prefix, .{
            .label = "cx",
            .kind = 9,
            .detail = "CoreX standard library namespace",
            .sort_tier = 1,
        });
        try appendUniqueCompletion(arena_alloc, &seen_labels, &items, prefix, .{
            .label = "pkg",
            .kind = 9,
            .detail = "current package root namespace",
            .sort_tier = 1,
        });

        for (COMPLETION_KEYWORDS) |kw_str| {
            if (items.items.len >= MAX_COMPLETION_ITEMS) break;
            try appendUniqueCompletion(arena_alloc, &seen_labels, &items, prefix, .{
                .label = kw_str,
                .kind = 14,
                .sort_tier = 3,
            });
        }
    }

    std.mem.sort(CompletionCandidate, items.items, {}, isCompletionCandidateBefore);
    const configured_max: usize = @min(
        @max(@as(usize, session.lsp_config.max_completion_items), 16),
        MAX_COMPLETION_ITEMS,
    );
    const out_count = @min(items.items.len, configured_max);
    const is_incomplete = items.items.len > out_count or items.items.len >= MAX_COMPLETION_ITEMS;

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.print(
        ",\"result\":{{\"isIncomplete\":{s},\"items\":[",
        .{if (is_incomplete) "true" else "false"},
    );
    for (items.items[0..out_count], 0..) |cand_item, i| {
        if (i > 0) try body_writer.writeByte(',');
        try body_writer.writeAll("{\"label\":");
        try writeJsonString(body_writer, cand_item.label);
        try body_writer.print(",\"kind\":{d}", .{cand_item.kind});
        if (cand_item.detail.len > 0) {
            try body_writer.writeAll(",\"detail\":");
            try writeJsonString(body_writer, cand_item.detail);
        }
        if (cand_item.is_deprecated) {
            try body_writer.writeAll(",\"tags\":[1]");
        }
        try body_writer.writeByte('}');
    }
    try body_writer.writeAll("]}}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Handles `textDocument/signatureHelp`: innermost call, `self` stripping, `/` & `*` zones, and `@overload` sets.
fn handleSignatureHelpRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const pos = extractJsonPosition(params.getField("position") orelse JsonValue{ .null_val = {} }) orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing position");
    };

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);

    const src = getLiveDocumentSource(session, fid) orelse return writeNullResultFrame(session, out_writer, rpc_id);
    const cursor_byte = lspPositionToByteOffset(session, fid, pos);
    _ = try session.db.parseCst(fid);
    _ = try session.db.resolveSignatures(fid);
    const entries = try arena_alloc.dupe(
        query_db.ItemTreeEntry,
        (try session.db.extractItemTree(fid)).entries,
    );
    var parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse
        return writeNullResultFrame(session, out_writer, rpc_id);

    // Find the innermost enclosing `(` in `TokenBuffer` before `cursor_byte` whose matching `)` is `>= cursor_byte`:
    var open_paren_tok: TokenIndex = .none;
    {
        var paren_stack: [64]TokenIndex = undefined;
        var stack_len: usize = 0;
        const tok_count = parsed_art.token_buffer.countTokens();
        var i: usize = 0;
        while (i < tok_count) : (i += 1) {
            const t_id = TokenIndex.fromInt(@intCast(i));
            const t_rec = parsed_art.token_buffer.getToken(t_id);
            if (t_rec.flags.is_synthesized or t_rec.kind == .eof) continue;
            if (t_rec.byte_offset >= cursor_byte) break;
            if (t_rec.kind == .lparen) {
                if (stack_len < paren_stack.len) {
                    paren_stack[stack_len] = t_id;
                    stack_len += 1;
                }
            } else if (t_rec.kind == .rparen) {
                if (stack_len > 0) stack_len -= 1;
            }
        }
        if (stack_len > 0) open_paren_tok = paren_stack[stack_len - 1];
    }
    if (open_paren_tok.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);

    const lparen_rec = parsed_art.token_buffer.getToken(open_paren_tok);

    // Count top-level commas and detect `label:` named arguments before `cursor_byte`:
    var comma_count: usize = 0;
    var active_named_label: ?[]const u8 = null;
    var seen_named_labels: std.ArrayListUnmanaged([]const u8) = .empty;
    {
        var depth_paren: u32 = 0;
        var depth_brack: u32 = 0;
        var depth_brace: u32 = 0;
        var slot_first_ident: ?[]const u8 = null;
        var has_slot_colon = false;

        var t_cur: usize = open_paren_tok.asInt() + 1;
        const tok_count = parsed_art.token_buffer.countTokens();
        while (t_cur < tok_count) : (t_cur += 1) {
            const t_id = TokenIndex.fromInt(@intCast(t_cur));
            const t_rec = parsed_art.token_buffer.getToken(t_id);
            if (t_rec.flags.is_synthesized or t_rec.kind == .eof) continue;
            if (t_rec.byte_offset >= cursor_byte) break;

            switch (t_rec.kind) {
                .lparen => depth_paren += 1,
                .rparen => if (depth_paren > 0) {
                    depth_paren -= 1;
                } else {
                    break;
                },
                .lbracket => depth_brack += 1,
                .rbracket => depth_brack -|= 1,
                .lbrace => depth_brace += 1,
                .rbrace => depth_brace -|= 1,
                .comma => {
                    if (depth_paren == 0 and depth_brack == 0 and depth_brace == 0) {
                        if (has_slot_colon and slot_first_ident != null) {
                            try seen_named_labels.append(arena_alloc, slot_first_ident.?);
                        }
                        comma_count += 1;
                        slot_first_ident = null;
                        has_slot_colon = false;
                    }
                },
                .colon => {
                    if (depth_paren == 0 and depth_brack == 0 and depth_brace == 0 and
                        slot_first_ident != null and !has_slot_colon)
                    {
                        has_slot_colon = true;
                    }
                },
                else => {
                    if (depth_paren == 0 and depth_brack == 0 and depth_brace == 0 and
                        slot_first_ident == null and isUserIdentifierToken(t_rec.kind))
                    {
                        slot_first_ident = symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, t_id);
                    }
                },
            }
        }
        if (has_slot_colon and slot_first_ident != null) {
            active_named_label = slot_first_ident;
        }
    }

    // Resolve callee symbol + method-call flag from enclosing `DefId` AST side tables or token before `(`:
    var callee_sym: SymbolIndex = .none;
    var resolved_overload_sym: SymbolIndex = .none;
    var is_method_syntax = false;

    var ident_before_paren: TokenIndex = .none;
    if (open_paren_tok.asInt() > 0) {
        var back_idx: usize = open_paren_tok.asInt();
        var generic_brack_depth: u32 = 0;
        while (back_idx > 0) {
            back_idx -= 1;
            const prev_id = TokenIndex.fromInt(@intCast(back_idx));
            const prev_kind = parsed_art.token_buffer.getToken(prev_id).kind;
            if (prev_kind == .rbracket) {
                generic_brack_depth += 1;
                continue;
            }
            if (generic_brack_depth > 0) {
                if (prev_kind == .lbracket) generic_brack_depth -= 1;
                continue;
            }
            if (isUserIdentifierToken(prev_kind)) {
                ident_before_paren = prev_id;
                if (back_idx > 0 and
                    parsed_art.token_buffer.getToken(TokenIndex.fromInt(@intCast(back_idx - 1))).kind == .dot)
                {
                    is_method_syntax = true;
                }
            }
            break;
        }
    }

    for (entries) |entry| {
        if (entry.kind == .mod_decl or entry.kind == .use_decl or entry.kind == .ffi_extern_block) continue;
        const entry_span = computeCstSubtreeByteSpan(
            fid,
            &parsed_art.token_buffer,
            &parsed_art.cst_arena,
            entry.cst_node,
        ) orelse continue;
        if (lparen_rec.byte_offset < entry_span.start_byte or lparen_rec.byte_offset > entry_span.end_byte) continue;

        if (try session.db.getDefSideTables(entry.def_id)) |side_tables| {
            parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse
                return writeNullResultFrame(session, out_writer, rpc_id);
            var ast_raw = side_tables.ast_start;
            const ast_limit = @min(side_tables.ast_end, @as(u32, @intCast(parsed_art.ast_arena.countNodes())));
            while (ast_raw < ast_limit) : (ast_raw += 1) {
                const ast_id = NodeIndex.fromInt(ast_raw);
                const ast_node = parsed_art.ast_arena.getNode(ast_id);
                const is_call_tag = switch (ast_node.tag) {
                    .call_expr, .generic_call, .method_call, .incomplete_call => true,
                    else => false,
                };
                if (!is_call_tag) continue;

                var is_matching_call = (ast_node.main_token == open_paren_tok);
                if (!is_matching_call and !ident_before_paren.isNone()) {
                    if (ast_node.tag == .method_call and ast_node.rhs.tag == .extra) {
                        const mem_raw = parsed_art.ast_arena.extra_data.items[ast_node.rhs.payload];
                        is_matching_call = (TokenIndex.fromInt(mem_raw) == ident_before_paren);
                    } else if (ast_node.lhs.tag == .node) {
                        const lhs_n = parsed_art.ast_arena.getNode(NodeIndex.fromInt(ast_node.lhs.payload));
                        is_matching_call = (lhs_n.main_token == ident_before_paren);
                    }
                }
                if (!is_matching_call) continue;

                if (ast_node.tag == .method_call) is_method_syntax = true;
                const call_sym = side_tables.getNodeSymbol(ast_id);
                if (!call_sym.isNone()) {
                    resolved_overload_sym = session.db.symbol_table.unwrapAliasSymbolIdx(call_sym);
                    callee_sym = resolved_overload_sym;
                } else if (ast_node.lhs.tag == .node) {
                    const lhs_sym = side_tables.getNodeSymbol(NodeIndex.fromInt(ast_node.lhs.payload));
                    if (!lhs_sym.isNone()) {
                        callee_sym = session.db.symbol_table.unwrapAliasSymbolIdx(lhs_sym);
                    }
                }
            }
        }
        break;
    }

    // Fallback lexical lookup on `ident_before_paren` (also discovers `overload_group_sym`!):
    if (!ident_before_paren.isNone()) {
        const callee_lex = symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, ident_before_paren);
        if (session.db.symbol_table.file_module_scopes.get(fid.asInt())) |mod_scope| {
            if (session.db.interner.lookup(callee_lex)) |c_name_id| {
                switch (session.db.symbol_table.lookupLexical(mod_scope, c_name_id, NamespaceMask.VALUE_ONLY)) {
                    .found => |lex_sym| {
                        const unwrapped = session.db.symbol_table.unwrapAliasSymbolIdx(lex_sym);
                        if (session.db.symbol_table.getSymbol(unwrapped).kind == .overload_group_sym or
                            callee_sym.isNone())
                        {
                            callee_sym = unwrapped;
                        }
                    },
                    else => {},
                }
            }
        }
    }

    if (callee_sym.isNone() or callee_sym.asInt() >= session.db.symbol_table.countSymbols()) {
        return writeNullResultFrame(session, out_writer, rpc_id);
    }

    var candidate_fns: std.ArrayListUnmanaged(SymbolIndex) = .empty;
    const base_callee = session.db.symbol_table.getSymbol(callee_sym).*;
    if (base_callee.kind == .overload_group_sym and
        base_callee.target_symbol.asInt() < session.db.symbol_table.overload_sets.items.len)
    {
        const ov_set = session.db.symbol_table.overload_sets.items[base_callee.target_symbol.asInt()];
        for (ov_set.members.items) |mem_fn_idx| {
            try candidate_fns.append(arena_alloc, mem_fn_idx);
        }
    } else if (base_callee.kind == .fn_sym) {
        try candidate_fns.append(arena_alloc, callee_sym);
    } else {
        return writeNullResultFrame(session, out_writer, rpc_id);
    }

    if (candidate_fns.items.len == 0) return writeNullResultFrame(session, out_writer, rpc_id);

    var active_sig_idx: usize = 0;
    var active_param_for_sig: u32 = 0;

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":{\"signatures\":[");

    for (candidate_fns.items, 0..) |fn_idx, sig_i| {
        if (sig_i > 0) try body_writer.writeByte(',');
        const fn_sym = session.db.symbol_table.getSymbol(fn_idx).*;
        var sig_label_buf = std.Io.Writer.Allocating.init(arena_alloc);
        var param_labels: std.ArrayListUnmanaged([]const u8) = .empty;
        try writeFormattedFnSignature(
            session,
            fn_idx,
            fn_sym,
            is_method_syntax,
            &sig_label_buf.writer,
            &param_labels,
            arena_alloc,
        );

        // Compute `activeParameter` for this candidate signature:
        const all_specs = session.db.symbol_table.getFnParamSpecs(fn_idx);
        const start_p: usize = if (is_method_syntax and all_specs.len > 0 and
            std.mem.eql(u8, all_specs[0].name_text, "self"))
            1
        else
            0;
        const visible_specs = if (start_p <= all_specs.len) all_specs[start_p..] else &.{};

        var computed_param: usize = @min(comma_count, if (param_labels.items.len > 0) param_labels.items.len - 1 else 0);
        var is_compatible = (comma_count < @max(param_labels.items.len, 1));
        if (active_named_label) |named_lbl| {
            is_compatible = false;
            for (visible_specs, 0..) |vspec, v_i| {
                if (std.mem.eql(u8, vspec.name_text, named_lbl)) {
                    computed_param = v_i;
                    is_compatible = true;
                    break;
                }
            }
        } else if (seen_named_labels.items.len > 0) {
            // Post-named `, ` slot; select the first visible parameter not yet named or filled positionally:
            const pos_filled = comma_count -| seen_named_labels.items.len;
            for (visible_specs, 0..) |vspec, v_i| {
                if (v_i < pos_filled) continue;
                var is_already_used = false;
                for (seen_named_labels.items) |used_lbl| {
                    if (std.mem.eql(u8, vspec.name_text, used_lbl)) {
                        is_already_used = true;
                        break;
                    }
                }
                if (!is_already_used) {
                    computed_param = v_i;
                    break;
                }
            }
        }

        if (fn_idx == resolved_overload_sym or (sig_i > 0 and active_sig_idx == 0 and is_compatible)) {
            if (fn_idx == resolved_overload_sym) {
                active_sig_idx = sig_i;
                active_param_for_sig = @intCast(computed_param);
            }
        }
        if (sig_i == 0) {
            active_param_for_sig = @intCast(computed_param);
        }

        try body_writer.writeAll("{\"label\":");
        try writeJsonString(body_writer, sig_label_buf.written());
        try body_writer.writeAll(",\"parameters\":[");
        for (param_labels.items, 0..) |p_lbl, p_i| {
            if (p_i > 0) try body_writer.writeByte(',');
            try body_writer.writeAll("{\"label\":");
            try writeJsonString(body_writer, p_lbl);
            try body_writer.writeByte('}');
        }
        try body_writer.print("],\"activeParameter\":{d}}}", .{computed_param});
    }

    try body_writer.print(
        "],\"activeSignature\":{d},\"activeParameter\":{d}}}}}",
        .{ active_sig_idx, active_param_for_sig },
    );
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

// ------ Inlay Hints (<= 1024), Code Actions & Formatting ------

/// Handles `textDocument/inlayHint`: `: <Type>` (with `textEdits`) and `<param>:` hints (`<= 1024`).
fn handleInlayHintRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const req_range = extractJsonRange(params.getField("range") orelse JsonValue{ .null_val = {} }) orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing range");
    };

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);

    const src = getLiveDocumentSource(session, fid) orelse return writeNullResultFrame(session, out_writer, rpc_id);
    const start_byte = lspPositionToByteOffset(session, fid, req_range.start);
    const end_byte = @max(start_byte, lspPositionToByteOffset(session, fid, req_range.end));

    _ = try session.db.parseCst(fid);
    _ = try session.db.resolveSignatures(fid);
    const entries = try arena_alloc.dupe(
        query_db.ItemTreeEntry,
        (try session.db.extractItemTree(fid)).entries,
    );
    var parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse
        return writeNullResultFrame(session, out_writer, rpc_id);
    const extra_ends = try syntax_arenas.computeAstNodeExtraEnds(arena_alloc, &parsed_art.ast_arena);

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":[");

    var emitted_hints: usize = 0;
    var type_buf: [256]u8 = undefined;

    for (entries) |entry| {
        if (emitted_hints >= MAX_INLAY_HINTS) break;
        if (entry.kind == .mod_decl or entry.kind == .use_decl or entry.kind == .ffi_extern_block) continue;
        parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse break;
        const entry_span = computeCstSubtreeByteSpan(
            fid,
            &parsed_art.token_buffer,
            &parsed_art.cst_arena,
            entry.cst_node,
        ) orelse continue;
        if (entry_span.end_byte < start_byte or entry_span.start_byte > end_byte) continue;

        const side_tables = (try session.db.getDefSideTables(entry.def_id)) orelse continue;
        parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse break;

        // [0] Optional inferred effect summary hint on `fn` headers when `inlay-hints-effects = "all"`:
        if (session.lsp_config.inlay_hints_effects == .all and entry.kind == .fn_decl and
            emitted_hints < MAX_INLAY_HINTS and entry_span.start_byte >= start_byte)
        {
            if (session.db.getSastSummaryProj(entry.def_id) catch null) |fn_sum| {
                const eff = fn_sum.inferredEffects();
                const eff_lbl: []const u8 = if (!eff.alloc and !eff.may_panic)
                    " /* pure */"
                else if (eff.alloc and eff.may_panic)
                    " /* alloc, panic */"
                else if (eff.alloc)
                    " /* alloc */"
                else
                    " /* panic */";
                const hdr_pos = byteOffsetToLspPosition(session, fid, entry_span.end_byte);
                if (emitted_hints > 0) try body_writer.writeByte(',');
                try body_writer.print(
                    "{{\"position\":{{\"line\":{d},\"character\":{d}}},\"label\":",
                    .{ hdr_pos.line, hdr_pos.character },
                );
                try writeJsonString(body_writer, eff_lbl);
                try body_writer.writeAll(",\"paddingLeft\":true}");
                emitted_hints += 1;
            }
        }

        var ast_raw = side_tables.ast_start;
        const ast_limit = @min(side_tables.ast_end, @as(u32, @intCast(parsed_art.ast_arena.countNodes())));

        while (ast_raw < ast_limit and emitted_hints < MAX_INLAY_HINTS) : (ast_raw += 1) {
            const ast_id = NodeIndex.fromInt(ast_raw);
            const ast_node = parsed_art.ast_arena.getNode(ast_id);

            // [1] Inferred `: <Type>` on unannotated single-binding `let` / `var` declarations (with `textEdits`!):
            if (session.lsp_config.inlay_hints_types and ast_node.tag == .local_var_decl) {
                const cst_orig = parsed_art.ast_arena.getCstOrigin(ast_id);
                if (!cst_orig.isNone()) {
                    var has_explicit_colon = false;
                    var bind_ident_tok: TokenIndex = .none;
                    const c_start: usize = cst_orig.asInt();
                    const c_end = @min(
                        c_start + @max(@as(usize, parsed_art.cst_arena.getNode(cst_orig).subtree_size), 1),
                        parsed_art.cst_arena.countNodes(),
                    );
                    var c_cur = c_start + 1;
                    while (c_cur < c_end) : (c_cur += 1) {
                        const leaf = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(c_cur)));
                        if (leaf.subtree_size > 1 or leaf.token.isNone() or
                            leaf.token.asInt() >= parsed_art.token_buffer.countTokens())
                        {
                            continue;
                        }
                        const lk = parsed_art.token_buffer.getToken(leaf.token).kind;
                        if (lk == .eq) break;
                        if (lk == .colon or lk == .lparen or lk == .lbrace or lk == .lbracket or lk == .dot) {
                            has_explicit_colon = true;
                            break;
                        }
                        if (bind_ident_tok.isNone() and isUserIdentifierToken(lk)) {
                            bind_ident_tok = leaf.token;
                        }
                    }

                    if (!has_explicit_colon and !bind_ident_tok.isNone()) {
                        const tok_sp = parsed_art.token_buffer.getTokenSpan(fid, bind_ident_tok);
                        if (tok_sp.end_byte >= start_byte and tok_sp.start_byte <= end_byte) {
                            var inferred_ty = side_tables.getNodeType(ast_id);
                            if ((inferred_ty.isError() or inferred_ty == .unit_ty) and ast_node.lhs.tag == .node) {
                                inferred_ty = side_tables.getNodeType(NodeIndex.fromInt(ast_node.lhs.payload));
                            }
                            if (!inferred_ty.isError() and inferred_ty != .unit_ty and
                                inferred_ty != .untyped_int_ty and inferred_ty != .untyped_float_ty)
                            {
                                const ty_str = session.db.type_pool.formatType(
                                    inferred_ty,
                                    &session.db.symbol_table,
                                    &type_buf,
                                );
                                const label_str = try std.fmt.allocPrint(arena_alloc, ": {s}", .{ty_str});
                                const ins_pos = byteOffsetToLspPosition(session, fid, tok_sp.end_byte);
                                if (emitted_hints > 0) try body_writer.writeByte(',');
                                try body_writer.print(
                                    "{{\"position\":{{\"line\":{d},\"character\":{d}}},\"label\":",
                                    .{ ins_pos.line, ins_pos.character },
                                );
                                try writeJsonString(body_writer, label_str);
                                try body_writer.writeAll(",\"kind\":1,\"textEdits\":[{\"range\":");
                                try writeLspRangeJson(body_writer, .{ .start = ins_pos, .end = ins_pos });
                                try body_writer.writeAll(",\"newText\":");
                                try writeJsonString(body_writer, label_str);
                                try body_writer.writeAll("}]}");
                                emitted_hints += 1;
                            }
                        }
                    }
                }
            }

            // [2] Implicit MVS autoref hints (`(&mut)` / `(own)`) on method receivers when `inlay-hints-mvs-modes = true`:
            if (session.lsp_config.inlay_hints_mvs_modes and ast_node.tag == .method_call and
                emitted_hints < MAX_INLAY_HINTS and ast_node.lhs.tag == .node)
            {
                const m_callee = session.db.symbol_table.unwrapAliasSymbolIdx(side_tables.getNodeSymbol(ast_id));
                if (!m_callee.isNone() and m_callee.asInt() < session.db.symbol_table.countSymbols()) {
                    const m_sym = session.db.symbol_table.getSymbol(m_callee).*;
                    if (session.db.type_pool.getFnSignatureView(m_sym.type_id)) |m_sv| {
                        if (m_sv.paramCount() > 0) {
                            const recv_mode = m_sv.getParamMode(0);
                            const recv_ty = m_sv.getParamType(0);
                            const is_mut_recv = recv_mode == .inout_mode or
                                (!recv_ty.isPrimitiveOrSentinel() and
                                    session.db.type_pool.getTag(recv_ty) == .mut_ref_ty);
                            const mvs_badge: ?[]const u8 = if (recv_mode == .sink_mode)
                                "(own) "
                            else if (is_mut_recv)
                                "(&mut) "
                            else
                                null;
                            if (mvs_badge) |badge_str| {
                                const recv_ast = NodeIndex.fromInt(ast_node.lhs.payload);
                                const recv_cst = parsed_art.ast_arena.getCstOrigin(recv_ast);
                                if (computeCstSubtreeByteSpan(
                                    fid,
                                    &parsed_art.token_buffer,
                                    &parsed_art.cst_arena,
                                    recv_cst,
                                )) |recv_sp| {
                                    if (recv_sp.start_byte >= start_byte and recv_sp.start_byte <= end_byte) {
                                        const recv_pos = byteOffsetToLspPosition(session, fid, recv_sp.start_byte);
                                        if (emitted_hints > 0) try body_writer.writeByte(',');
                                        try body_writer.print(
                                            "{{\"position\":{{\"line\":{d},\"character\":{d}}},\"label\":",
                                            .{ recv_pos.line, recv_pos.character },
                                        );
                                        try writeJsonString(body_writer, badge_str);
                                        try body_writer.writeByte('}');
                                        emitted_hints += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // [3] Positional argument `<param>:` hints on `.call_expr`, `.generic_call`, `.method_call`:
            if (session.lsp_config.inlay_hints_parameter_names != .none and
                (ast_node.tag == .call_expr or ast_node.tag == .generic_call or ast_node.tag == .method_call))
            {
                var callee_idx = side_tables.getNodeSymbol(ast_id);
                if (callee_idx.isNone() and ast_node.lhs.tag == .node) {
                    callee_idx = side_tables.getNodeSymbol(NodeIndex.fromInt(ast_node.lhs.payload));
                }
                if (callee_idx.isNone()) continue;
                callee_idx = session.db.symbol_table.unwrapAliasSymbolIdx(callee_idx);
                const param_specs = session.db.symbol_table.getFnParamSpecs(callee_idx);
                if (param_specs.len == 0) continue;

                const self_offset: usize = if (ast_node.tag == .method_call and
                    std.mem.eql(u8, param_specs[0].name_text, "self"))
                    1
                else
                    0;

                if (ast_node.rhs.tag == .extra and ast_id.asInt() < extra_ends.len) {
                    const ex_start: usize = ast_node.rhs.payload;
                    const ex_end: usize = extra_ends[ast_id.asInt()];
                    const gen_specs = session.db.symbol_table.getGenericParamSpecs(callee_idx);
                    var arg_offset: usize = ex_start;
                    if (ast_node.tag == .method_call) arg_offset += 1;
                    if (ast_node.tag == .generic_call) arg_offset += gen_specs.len;
                    if (arg_offset >= ex_end or ex_end > parsed_art.ast_arena.extra_data.items.len) continue;

                    const arg_nodes = parsed_art.ast_arena.extra_data.items[arg_offset..ex_end];
                    for (arg_nodes, 0..) |raw_arg_node, pos_i| {
                        if (emitted_hints >= MAX_INLAY_HINTS) break;
                        const arg_id = NodeIndex.fromInt(raw_arg_node);
                        if (arg_id.isNone() or arg_id.asInt() >= parsed_art.ast_arena.countNodes()) continue;
                        const arg_rec = parsed_art.ast_arena.getNode(arg_id);
                        if (arg_rec.tag == .named_arg) continue;
                        if (arg_rec.main_token.isNone() or
                            arg_rec.main_token.asInt() >= parsed_art.token_buffer.countTokens())
                        {
                            continue;
                        }

                        const spec_idx = self_offset + pos_i;
                        if (spec_idx >= param_specs.len) break;
                        const p_name = param_specs[spec_idx].name_text;
                        if (p_name.len == 0 or std.mem.startsWith(u8, p_name, "_")) continue;

                        // Suppress redundant `foo(count: count)` under `"non-matching"` when argument matches `p_name`:
                        if (session.lsp_config.inlay_hints_parameter_names == .non_matching and
                            arg_rec.tag == .ident_expr)
                        {
                            const arg_lex = symbol_resolver.extractTokenSlice(
                                src,
                                &parsed_art.token_buffer,
                                arg_rec.main_token,
                            );
                            if (std.mem.eql(u8, arg_lex, p_name)) continue;
                        }

                        const cst_arg = parsed_art.ast_arena.getCstOrigin(arg_id);
                        const arg_start_b = if (computeCstSubtreeByteSpan(
                            fid,
                            &parsed_art.token_buffer,
                            &parsed_art.cst_arena,
                            cst_arg,
                        )) |sp|
                            sp.start_byte
                        else
                            parsed_art.token_buffer.getToken(arg_rec.main_token).byte_offset;

                        if (arg_start_b < start_byte or arg_start_b > end_byte) continue;
                        const arg_pos = byteOffsetToLspPosition(session, fid, arg_start_b);
                        const param_hint_lbl = try std.fmt.allocPrint(arena_alloc, "{s}:", .{p_name});
                        if (emitted_hints > 0) try body_writer.writeByte(',');
                        try body_writer.print(
                            "{{\"position\":{{\"line\":{d},\"character\":{d}}},\"label\":",
                            .{ arg_pos.line, arg_pos.character },
                        );
                        try writeJsonString(body_writer, param_hint_lbl);
                        try body_writer.writeAll(",\"kind\":2,\"paddingRight\":true}");
                        emitted_hints += 1;
                    }
                }
            }
        }
    }

    try body_writer.writeAll("]}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Returns `true` when `file_id` belongs to an external/read-only `.std_core`, `.cxtree`, `@c_import`, or `.high` file.
fn isReadOnlyNonWorkspaceFile(session: *const LspSession, file_id: FileId) bool {
    if (file_id.isNone() or file_id.asInt() >= query_db.VIRTUAL_C_IMPORT_FILE_ID_BASE) return true;
    const vfs_path = session.vfs.getFilePath(file_id);
    if (std.mem.startsWith(u8, vfs_path, "/cx/")) return true;
    const pkg_id = session.db.symbol_table.getFilePackageId(file_id);
    if (pkg_id == .std_core) return !session.options.is_internal_core;
    if (pkg_id != .root) return true;
    if (session.db.isStdlibFile(file_id)) return !session.options.is_internal_core;
    if (session.db.source_inputs.get(file_id.asInt())) |src_in| {
        if (src_in.durability == .high) return true;
    }
    return false;
}

/// Emits a JSON-RPC 2.0 empty-array response `{"jsonrpc":"2.0","id":…,"result":[]}` to `out_writer`.
fn writeEmptyArrayResultFrame(session: *LspSession, out_writer: *std.Io.Writer, rpc_id: JsonRpcId) !void {
    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":[]}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Handles `textDocument/codeAction`: converts overlapping `SuggestedFix` entries into `"quickfix"` `CodeAction`s (`<= 64`).
fn handleCodeActionRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const req_range = extractJsonRange(params.getField("range") orelse JsonValue{ .null_val = {} }) orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing range");
    };

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);
    if (isReadOnlyNonWorkspaceFile(session, fid)) return writeEmptyArrayResultFrame(session, out_writer, rpc_id);

    const req_start = lspPositionToByteOffset(session, fid, req_range.start);
    const req_end = @max(req_start, lspPositionToByteOffset(session, fid, req_range.end));
    const collected = try collectFileDiagnostics(session, arena_alloc, fid);

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":[");

    var action_count: usize = 0;
    for (collected) |entry| {
        if (action_count >= MAX_CODE_ACTIONS) break;
        const d_span = entry.diag.primary_span;
        if (d_span.start_byte > req_end or d_span.end_byte < req_start) continue;

        var all_fixes: std.ArrayListUnmanaged(SuggestedFix) = .empty;
        for (entry.diag.suggestions) |fix_item| {
            try all_fixes.append(arena_alloc, fix_item);
        }
        if (entry.extra_bang_fix) |bang_fix| {
            if (all_fixes.items.len == 0) try all_fixes.append(arena_alloc, bang_fix);
        }

        for (all_fixes.items) |fix| {
            if (action_count >= MAX_CODE_ACTIONS) break;
            if (fix.edits.len == 0) continue;
            if (fix.applicability != .machine_applicable and fix.applicability != .maybe_incorrect) continue;

            var uri_groups: std.ArrayListUnmanaged(CodeActionUriGroup) = .empty;
            var uri_to_group_idx: std.StringHashMapUnmanaged(usize) = .empty;
            var is_fix_valid = true;

            for (fix.edits) |edit_rec| {
                const edit_fid = if (!edit_rec.file_id.isNone()) edit_rec.file_id else fid;
                if (isReadOnlyNonWorkspaceFile(session, edit_fid)) {
                    is_fix_valid = false;
                    break;
                }
                if (session.vfs.getFilePath(edit_fid).len == 0 and
                    !session.file_id_to_client_uri.contains(edit_fid.asInt()))
                {
                    is_fix_valid = false;
                    break;
                }
                const target_uri = resolveOutboundUri(session, arena_alloc, edit_fid) catch {
                    is_fix_valid = false;
                    break;
                };
                if (target_uri.len == 0) {
                    is_fix_valid = false;
                    break;
                }
                const gop = try uri_to_group_idx.getOrPut(arena_alloc, target_uri);
                if (!gop.found_existing) {
                    gop.value_ptr.* = uri_groups.items.len;
                    try uri_groups.append(arena_alloc, .{
                        .file_id = edit_fid,
                        .uri = target_uri,
                    });
                }
                try uri_groups.items[gop.value_ptr.*].edits.append(arena_alloc, edit_rec);
            }
            if (!is_fix_valid or uri_groups.items.len == 0) continue;

            const base_title = if (fix.message.len > 0) fix.message else "Apply CoreX quick fix";
            const action_title = if (fix.applicability == .maybe_incorrect and
                std.mem.indexOf(u8, base_title, "unsafe") == null)
                try std.fmt.allocPrint(arena_alloc, "{s} (unsafe fix)", .{base_title})
            else
                base_title;

            if (action_count > 0) try body_writer.writeByte(',');
            try body_writer.writeAll("{\"title\":");
            try writeJsonString(body_writer, action_title);
            try body_writer.print(
                ",\"kind\":\"quickfix\",\"isPreferred\":{s},\"diagnostics\":[",
                .{if (fix.applicability == .machine_applicable) "true" else "false"},
            );
            try writeSingleLspDiagnosticJson(session, arena_alloc, fid, entry.diag, body_writer);
            try body_writer.writeAll("],\"edit\":{\"changes\":{");
            for (uri_groups.items, 0..) |group, group_i| {
                if (group_i > 0) try body_writer.writeByte(',');
                try writeJsonString(body_writer, group.uri);
                try body_writer.writeAll(":[");
                for (group.edits.items, 0..) |edit_rec, edit_i| {
                    const repl_str = session.db.interner.get(edit_rec.replacement_id);
                    const edit_range = spanToLspRange(
                        session,
                        group.file_id,
                        Span.init(group.file_id, edit_rec.start_byte, edit_rec.end_byte),
                    );
                    if (edit_i > 0) try body_writer.writeByte(',');
                    try body_writer.writeAll("{\"range\":");
                    try writeLspRangeJson(body_writer, edit_range);
                    try body_writer.writeAll(",\"newText\":");
                    try writeJsonString(body_writer, repl_str);
                    try body_writer.writeByte('}');
                }
                try body_writer.writeByte(']');
            }
            try body_writer.writeAll("}}}");
            action_count += 1;
        }

        // Secondary Quick Fix (`isPreferred: false`): suppress lint rule with line-scoped `// corex check: expect(…)`:
        if (action_count < MAX_CODE_ACTIONS) {
            if (entry.diag.code.asLintRuleId()) |rule_id| {
                if (rule_id != .unused_suppression and rule_id != .prefer_expect_over_allow) {
                    if (getLiveDocumentSource(session, fid)) |live_src| {
                        const target_uri = resolveOutboundUri(session, arena_alloc, fid) catch "";
                        if (target_uri.len > 0) {
                            const diag_start = @min(@as(usize, d_span.start_byte), live_src.len);
                            var multiline_tok_start: ?usize = null;
                            if (session.db.parsed_artifacts.getPtr(fid.asInt())) |parsed_ptr| {
                                const tok_total = parsed_ptr.token_buffer.countTokens();
                                var t_lo: usize = 0;
                                var t_hi: usize = tok_total;
                                while (t_lo < t_hi) {
                                    const t_mid = t_lo + (t_hi - t_lo) / 2;
                                    const tr = parsed_ptr.token_buffer.getToken(TokenIndex.fromInt(@intCast(t_mid)));
                                    if (@as(usize, tr.byte_offset) + tr.byte_len <= diag_start) {
                                        t_lo = t_mid + 1;
                                    } else {
                                        t_hi = t_mid;
                                    }
                                }
                                if (t_lo < tok_total) {
                                    const tr = parsed_ptr.token_buffer.getToken(TokenIndex.fromInt(@intCast(t_lo)));
                                    const t_s: usize = @min(@as(usize, tr.byte_offset), live_src.len);
                                    const t_e: usize = @min(t_s + tr.byte_len, live_src.len);
                                    const is_str_like = tr.kind == .string_lit or
                                        tr.kind == .fmt_string_lit or
                                        tr.kind == .byte_string_lit;
                                    if (is_str_like and diag_start >= t_s and diag_start < t_e and
                                        std.mem.indexOfScalar(u8, live_src[t_s..t_e], '\n') != null)
                                    {
                                        var anchor_start = t_s;
                                        const cst_total = parsed_ptr.cst_arena.countNodes();
                                        var best_cst_start: ?usize = null;
                                        var c_i: usize = 1;
                                        while (c_i < cst_total) : (c_i += 1) {
                                            const cid = CstNodeIndex.fromInt(@intCast(c_i));
                                            const ck = parsed_ptr.cst_arena.getNode(cid).kind;
                                            const is_stmt_or_item = switch (ck) {
                                                .local_decl_stmt,
                                                .assign_stmt,
                                                .return_stmt,
                                                .expr_stmt,
                                                .const_item,
                                                .fn_item,
                                                .test_item,
                                                .bench_item,
                                                => true,
                                                else => false,
                                            };
                                            if (!is_stmt_or_item) continue;
                                            if (symbol_resolver.computeCstSubtreeSpan(
                                                fid,
                                                &parsed_ptr.token_buffer,
                                                &parsed_ptr.cst_arena,
                                                cid,
                                            )) |csp| {
                                                if (t_s >= csp.start_byte and t_e <= csp.end_byte) {
                                                    best_cst_start = @min(@as(usize, csp.start_byte), live_src.len);
                                                }
                                            }
                                        }
                                        if (best_cst_start) |bcs| anchor_start = bcs;
                                        multiline_tok_start = anchor_start;
                                    }
                                }
                            }

                            const sup_title = try std.fmt.allocPrint(
                                arena_alloc,
                                "Suppress `{s}` with `@expect`",
                                .{rule_id.asSlug()},
                            );
                            var ins_pos: LspPosition = undefined;
                            var sup_text: []const u8 = "";
                            if (multiline_tok_start) |anchor_byte| {
                                var line_start = anchor_byte;
                                while (line_start > 0 and live_src[line_start - 1] != '\n') : (line_start -= 1) {}
                                var indent_end = line_start;
                                while (indent_end < live_src.len and
                                    (live_src[indent_end] == ' ' or live_src[indent_end] == '\t')) : (indent_end += 1)
                                {}
                                const indent_slice = live_src[line_start..indent_end];
                                ins_pos = byteOffsetToLspPosition(session, fid, @intCast(line_start));
                                sup_text = try std.fmt.allocPrint(
                                    arena_alloc,
                                    "{s}@expect({s}, reason: \"explain suppression\")\n",
                                    .{ indent_slice, rule_id.asSlug() },
                                );
                            } else {
                                var line_end = diag_start;
                                while (line_end < live_src.len and
                                    live_src[line_end] != '\n' and live_src[line_end] != '\r') : (line_end += 1)
                                {}
                                ins_pos = byteOffsetToLspPosition(session, fid, @intCast(line_end));
                                sup_text = try std.fmt.allocPrint(
                                    arena_alloc,
                                    " // corex check: expect({s}) -- explain suppression",
                                    .{rule_id.asSlug()},
                                );
                            }

                            if (action_count > 0) try body_writer.writeByte(',');
                            try body_writer.writeAll("{\"title\":");
                            try writeJsonString(body_writer, sup_title);
                            try body_writer.writeAll(",\"kind\":\"quickfix\",\"isPreferred\":false,\"diagnostics\":[");
                            try writeSingleLspDiagnosticJson(session, arena_alloc, fid, entry.diag, body_writer);
                            try body_writer.writeAll("],\"edit\":{\"changes\":{");
                            try writeJsonString(body_writer, target_uri);
                            try body_writer.writeAll(":[{\"range\":");
                            try writeLspRangeJson(body_writer, .{ .start = ins_pos, .end = ins_pos });
                            try body_writer.writeAll(",\"newText\":");
                            try writeJsonString(body_writer, sup_text);
                            try body_writer.writeAll("}]}}}");
                            action_count += 1;
                        }
                    }
                }
            }
        }
    }

    try body_writer.writeAll("]}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Handles `textDocument/codeLens`: emits runnable `▸ Run test` / `▸ Run bench` CodeLenses when enabled (`[lsp]`).
fn handleCodeLensRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    if (!session.lsp_config.code_lens_test_bench) {
        return writeEmptyArrayResultFrame(session, out_writer, rpc_id);
    }

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone() or isCorexTomlPath(session.vfs.getFilePath(fid))) {
        return writeEmptyArrayResultFrame(session, out_writer, rpc_id);
    }

    _ = try session.db.parseCst(fid);
    const entries = try arena_alloc.dupe(
        query_db.ItemTreeEntry,
        (try session.db.extractItemTree(fid)).entries,
    );
    const parsed_art = session.db.parsed_artifacts.getPtr(fid.asInt()) orelse
        return writeEmptyArrayResultFrame(session, out_writer, rpc_id);
    const target_uri = try resolveOutboundUri(session, arena_alloc, fid);

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":[");

    var lens_count: usize = 0;
    for (entries) |entry| {
        if (entry.kind != .test_decl and entry.kind != .bench_decl) continue;
        const entry_span = computeCstSubtreeByteSpan(
            fid,
            &parsed_art.token_buffer,
            &parsed_art.cst_arena,
            entry.cst_node,
        ) orelse continue;
        const lens_range = spanToLspRange(session, fid, entry_span);
        const is_bench = (entry.kind == .bench_decl);
        if (lens_count > 0) try body_writer.writeByte(',');
        try body_writer.writeAll("{\"range\":");
        try writeLspRangeJson(body_writer, lens_range);
        try body_writer.writeAll(",\"command\":{\"title\":");
        try writeJsonString(body_writer, if (is_bench) "▸ Run bench" else "▸ Run test");
        try body_writer.writeAll(",\"command\":");
        try writeJsonString(body_writer, if (is_bench) "corex.runBench" else "corex.runTest");
        try body_writer.writeAll(",\"arguments\":[");
        try writeJsonString(body_writer, target_uri);
        try body_writer.writeByte(',');
        try writeJsonString(body_writer, entry.name_text);
        try body_writer.writeAll("]}}");
        lens_count += 1;
    }

    try body_writer.writeAll("]}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Handles `textDocument/formatting` and `textDocument/rangeFormatting` via `fmt_engine` (`0` disk writes).
fn handleFormattingRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    is_range_fmt: bool,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);
    if (isReadOnlyNonWorkspaceFile(session, fid)) return writeEmptyArrayResultFrame(session, out_writer, rpc_id);

    const src = getLiveDocumentSource(session, fid) orelse return writeNullResultFrame(session, out_writer, rpc_id);
    const parsed_art = try session.db.parseCst(fid);
    if (parsed_art.has_parse_errors) {
        return writeEmptyArrayResultFrame(session, out_writer, rpc_id);
    }

    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":[");

    if (is_range_fmt) {
        const req_range = extractJsonRange(params.getField("range") orelse JsonValue{ .null_val = {} }) orelse {
            return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing range");
        };
        const r_start = lspPositionToByteOffset(session, fid, req_range.start);
        const r_end = @max(r_start, lspPositionToByteOffset(session, fid, req_range.end));
        const line_idx = try session.vfs.getLineIndex(fid);
        if (try fmt_engine.formatByteRange(
            arena_alloc,
            src,
            &parsed_art.token_buffer,
            &parsed_art.cst_arena,
            line_idx,
            r_start,
            r_end,
            .{},
        )) |range_edit_val| {
            var range_edit = range_edit_val;
            defer range_edit.deinit(arena_alloc);
            const edit_lsp_range = spanToLspRange(
                session,
                fid,
                Span.init(fid, range_edit.start_byte, range_edit.end_byte),
            );
            try body_writer.writeAll("{\"range\":");
            try writeLspRangeJson(body_writer, edit_lsp_range);
            try body_writer.writeAll(",\"newText\":");
            try writeJsonString(body_writer, range_edit.replacement);
            try body_writer.writeByte('}');
        }
    } else {
        var fmt_res = try fmt_engine.formatTokensAndCst(
            arena_alloc,
            src,
            &parsed_art.token_buffer,
            &parsed_art.cst_arena,
            .{},
        );
        defer fmt_res.deinit(arena_alloc);
        if (fmt_res.is_changed and !std.mem.eql(u8, src, fmt_res.formatted_text)) {
            const full_range = spanToLspRange(session, fid, Span.init(fid, 0, @intCast(src.len)));
            try body_writer.writeAll("{\"range\":");
            try writeLspRangeJson(body_writer, full_range);
            try body_writer.writeAll(",\"newText\":");
            try writeJsonString(body_writer, fmt_res.formatted_text);
            try body_writer.writeByte('}');
        }
    }

    try body_writer.writeAll("]}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

// ----- Hygiene-Checked Cross-File PrepareRename & Rename ------

/// Resolved validated rename target shared between `prepareRename` and `rename`.
const ValidatedRenameTarget = struct {
    /// Canonical symbol (or explicit `use … as alias` symbol) to rename.
    target_sym_idx: SymbolIndex,
    /// `true` when renaming ONLY a local `use foo.{bar as alias}` alias in the active file.
    is_explicit_local_alias: bool,
    /// Exact token span under the cursor.
    cursor_token_span: Span,
    /// Current identifier spelling.
    old_name: []const u8,
    /// Enclosing `DefId` at cursor (used for local/parameter scope restriction).
    enclosing_def_id: DefId,
};

/// Validates whether the cursor sits on a renamable workspace symbol (`null` when read-only or built-in).
fn validateRenamableSymbolAtCursor(
    session: *LspSession,
    file_id: FileId,
    pos: LspPosition,
) !?ValidatedRenameTarget {
    if (isReadOnlyNonWorkspaceFile(session, file_id)) return null;

    const src = getLiveDocumentSource(session, file_id) orelse return null;
    const target = try resolveCursorTarget(session, file_id, pos);
    if (target.token_index.isNone() or target.symbol_index.isNone()) return null;
    const parsed_art = try session.db.parseCst(file_id);

    const tok_rec = parsed_art.token_buffer.getToken(target.token_index);
    const effective_tok_kind = target.resolved_token_kind orelse tok_rec.kind;
    if (!isUserIdentifierToken(effective_tok_kind)) return null;
    const span_start = @min(@as(usize, target.token_span.start_byte), src.len);
    const span_end = @min(@max(@as(usize, target.token_span.end_byte), span_start), src.len);
    const cursor_lexeme = if (target.resolved_token_kind != null)
        src[span_start..span_end]
    else
        symbol_resolver.extractTokenSlice(src, &parsed_art.token_buffer, target.token_index);
    if (cursor_lexeme.len == 0 or NON_RENAMABLE_IDENT_SET.has(cursor_lexeme)) return null;

    // Distinguish explicit `use pkg.foo.{bar as alias}` (cursor on `alias`) vs `bar`:
    const raw_sym = session.db.symbol_table.getSymbol(target.symbol_index).*;
    const unwrapped_idx = resolveLiveCanonicalSymbol(session, target.symbol_index);
    if (unwrapped_idx.isNone() or unwrapped_idx.asInt() >= session.db.symbol_table.countSymbols()) return null;
    const unwrapped_sym = session.db.symbol_table.getSymbol(unwrapped_idx).*;

    const is_explicit_alias = (raw_sym.kind == .use_alias_sym and
        unwrapped_idx != target.symbol_index and
        raw_sym.name != unwrapped_sym.name and
        std.mem.eql(u8, cursor_lexeme, raw_sym.name_text));

    const effective_idx = if (is_explicit_alias)
        resolveLiveExplicitAliasSymbol(session, file_id, target.symbol_index)
    else
        unwrapped_idx;
    const effective_sym = session.db.symbol_table.getSymbol(effective_idx).*;

    if (effective_sym.flags.is_builtin) return null;
    if (NON_RENAMABLE_IDENT_SET.has(effective_sym.name_text)) return null;

    const decl_fid = effective_sym.decl_span.file_id;
    if (!session.db.source_inputs.contains(decl_fid.asInt())) return null;
    if (isReadOnlyNonWorkspaceFile(session, decl_fid)) return null;

    // Reject external `mod foo;` file declarations (only inline `mod foo { … }` is a pure text rename):
    if (effective_sym.kind == .module_sym) {
        if (!target.external_mod_file_id.isNone()) return null;
        const mod_name_id = session.db.interner.lookup(effective_sym.name_text) orelse .empty;
        if (!mod_name_id.isNone()) {
            const ext_key: u64 = (@as(u64, decl_fid.asInt()) << 32) | @as(u64, mod_name_id.asInt());
            if (session.db.external_mod_files.contains(ext_key)) return null;
        }
        _ = try session.db.parseCst(decl_fid);
        const decl_tree = try session.db.extractItemTree(decl_fid);
        var decl_parsed = session.db.parsed_artifacts.getPtr(decl_fid.asInt()) orelse return null;
        var live_mod_ast: NodeIndex = .none;
        if (!effective_sym.def_id.isNone() and effective_sym.def_id.fileId() == decl_fid) {
            if (decl_tree.getEntry(effective_sym.def_id)) |mod_entry| {
                if (!mod_entry.ast_node.isNone() and mod_entry.ast_node.asInt() < decl_parsed.ast_arena.countNodes()) {
                    live_mod_ast = mod_entry.ast_node;
                }
            }
        }
        if (!live_mod_ast.isNone()) {
            if (decl_parsed.ast_arena.getNode(live_mod_ast).rhs.tag != .extra) return null;
        } else {
            const live_mod_span = try session.db.resolveLiveSymbolDeclSpan(effective_idx);
            decl_parsed = session.db.parsed_artifacts.getPtr(decl_fid.asInt()) orelse return null;
            if (findExactTokenAtByteOffset(&decl_parsed.token_buffer, live_mod_span.start_byte)) |mod_ident_tok| {
                const next_tok_raw = mod_ident_tok.asInt() + 1;
                if (next_tok_raw >= decl_parsed.token_buffer.countTokens() or
                    decl_parsed.token_buffer.getToken(TokenIndex.fromInt(next_tok_raw)).kind != .lbrace)
                {
                    return null;
                }
            } else if (!effective_sym.ast_node.isNone() and
                effective_sym.ast_node.asInt() < decl_parsed.ast_arena.countNodes())
            {
                if (decl_parsed.ast_arena.getNode(effective_sym.ast_node).rhs.tag != .extra) return null;
            } else {
                return null;
            }
        }
    }

    return .{
        .target_sym_idx = effective_idx,
        .is_explicit_local_alias = is_explicit_alias,
        .cursor_token_span = target.token_span,
        .old_name = effective_sym.name_text,
        .enclosing_def_id = target.enclosing_def_id,
    };
}

/// Validates `new_name` against `DR-03` identifier syntax and casing rules for `sym`.
fn isValidDr03RenameIdentifier(sym: SymbolRecord, new_name: []const u8) bool {
    if (new_name.len == 0 or NON_RENAMABLE_IDENT_SET.has(new_name)) return false;
    // Verify every byte is valid ASCII identifier syntax (`[A-Za-z_][A-Za-z0-9_]*`):
    if (!std.ascii.isAlphabetic(new_name[0]) and new_name[0] != '_') return false;
    for (new_name[1..]) |ch_val| {
        if (!std.ascii.isAlphanumeric(ch_val) and ch_val != '_') return false;
    }

    const classified = lexer.classifyIdentifierOrKeyword(new_name);
    if (!isUserIdentifierToken(classified.kind)) return false;
    if (symbol_resolver.BUILTIN_TYPE_AND_GROUP_MAP.has(new_name)) return false;

    const is_expecting_pascal = switch (sym.kind) {
        .struct_sym,
        .enum_sym,
        .union_sym,
        .bit_field_sym,
        .trait_sym,
        .type_alias_sym,
        .type_group_sym,
        .distinct_type_sym,
        .refined_type_sym,
        .type_param_sym,
        .enum_variant_sym,
        => true,
        .use_alias_sym => sym.namespace == .type_ns,
        else => false,
    };
    const is_expecting_screaming = switch (sym.kind) {
        .const_sym, .const_param_sym => true,
        .use_alias_sym => sym.namespace == .const_ns,
        else => false,
    };

    if (is_expecting_pascal) {
        return classified.kind == .type_ident and classified.is_canonical;
    } else if (is_expecting_screaming) {
        return classified.kind == .const_ident and classified.is_canonical;
    }
    return classified.kind == .ident and classified.is_canonical;
}

/// Checks whether `(file_id, ident_span)` sits inside a shorthand `.field_init` or `SE-15` `.field_pat`, returning expanded edit.
fn tryBuildShorthandExpansionEdit(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    file_id: FileId,
    src: []const u8,
    parsed_art: *const query_db.ParsedCstArtifact,
    ident_span: Span,
    old_name: []const u8,
    new_name: []const u8,
    is_renaming_field: bool,
) !?RenamePlanEdit {
    const cst_count = parsed_art.cst_arena.countNodes();
    var cur: usize = 0;
    while (cur < cst_count) : (cur += 1) {
        const c_id = CstNodeIndex.fromInt(@intCast(cur));
        const c_rec = parsed_art.cst_arena.getNode(c_id);
        if (c_rec.kind != .field_init and c_rec.kind != .field_pat) continue;

        const f_end = @min(cur + @max(@as(usize, c_rec.subtree_size), 1), cst_count);
        var first_leaf_tok: TokenIndex = .none;
        var ident_tok: TokenIndex = .none;
        var has_colon = false;
        var has_extra_expr_tokens = false;

        var f_cur = cur + 1;
        while (f_cur < f_end) : (f_cur += 1) {
            const leaf = parsed_art.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(f_cur)));
            if (leaf.subtree_size > 1 or leaf.flags.is_missing_or_injected or
                leaf.token.isNone() or leaf.token.asInt() >= parsed_art.token_buffer.countTokens())
            {
                continue;
            }
            const t_rec = parsed_art.token_buffer.getToken(leaf.token);
            if (t_rec.flags.is_synthesized) continue;
            if (first_leaf_tok.isNone()) first_leaf_tok = leaf.token;

            if (t_rec.kind == .colon) {
                has_colon = true;
                break;
            }
            if (ident_tok.isNone() and isUserIdentifierToken(t_rec.kind)) {
                ident_tok = leaf.token;
            } else if (!ident_tok.isNone()) {
                has_extra_expr_tokens = true;
            }
        }

        if (has_colon or has_extra_expr_tokens or ident_tok.isNone() or first_leaf_tok.isNone()) continue;
        const tok_sp = parsed_art.token_buffer.getTokenSpan(file_id, ident_tok);
        if (tok_sp.start_byte != ident_span.start_byte or tok_sp.end_byte != ident_span.end_byte) continue;

        if (c_rec.kind == .field_init) {
            // Struct init shorthand `Point { x }`:
            const expanded = if (is_renaming_field)
                try std.fmt.allocPrint(arena_alloc, "{s}: {s}", .{ new_name, old_name })
            else
                try std.fmt.allocPrint(arena_alloc, "{s}: {s}", .{ old_name, new_name });
            return .{
                .file_id = file_id,
                .start_byte = tok_sp.start_byte,
                .end_byte = tok_sp.end_byte,
                .replacement = expanded,
            };
        } else {
            // `SE-15` struct/variant pattern shorthand `Point { x }` or `Point { var x }` / `Point { &mut x }`:
            const first_sp = parsed_art.token_buffer.getTokenSpan(file_id, first_leaf_tok);
            const mod_prefix = if (first_sp.start_byte < tok_sp.start_byte)
                src[first_sp.start_byte..tok_sp.start_byte]
            else
                "";
            const expanded = if (is_renaming_field)
                try std.fmt.allocPrint(arena_alloc, "{s}: {s}{s}", .{ new_name, mod_prefix, old_name })
            else
                try std.fmt.allocPrint(arena_alloc, "{s}: {s}{s}", .{ old_name, mod_prefix, new_name });
            return .{
                .file_id = file_id,
                .start_byte = first_sp.start_byte,
                .end_byte = tok_sp.end_byte,
                .replacement = expanded,
            };
        }
    }

    // Also inspect `f"…"` interpolation hole tokens for struct-init shorthands (`f"{Point { x }}"`):
    const container_tok = findTokenAtCursorByte(&parsed_art.token_buffer, ident_span.start_byte);
    if (!container_tok.isNone() and container_tok.asInt() < parsed_art.token_buffer.countTokens() and
        parsed_art.token_buffer.getToken(container_tok).kind == .fmt_string_lit)
    {
        const entries = try arena_alloc.dupe(
            query_db.ItemTreeEntry,
            (try session.db.extractItemTree(file_id)).entries,
        );
        for (entries) |entry| {
            if (entry.kind == .mod_decl or entry.kind == .use_decl or entry.kind == .ffi_extern_block) continue;
            const side_tables = (try session.db.getDefSideTables(entry.def_id)) orelse continue;
            const live_parsed = session.db.parsed_artifacts.getPtr(file_id.asInt()) orelse break;
            const ast_limit = @min(side_tables.ast_end, @as(u32, @intCast(live_parsed.ast_arena.countNodes())));

            var interp_it = side_tables.string_interps.iterator();
            while (interp_it.next()) |interp_kv| {
                const fmt_ast_raw = side_tables.ast_start + interp_kv.key_ptr.*;
                if (fmt_ast_raw >= ast_limit) continue;
                const fmt_main_tok = live_parsed.ast_arena.getNode(NodeIndex.fromInt(fmt_ast_raw)).main_token;
                if (fmt_main_tok.isNone() or fmt_main_tok.asInt() >= live_parsed.token_buffer.countTokens()) continue;
                const fmt_tok_base = live_parsed.token_buffer.getToken(fmt_main_tok).byte_offset;

                for (interp_kv.value_ptr.holes) |hole| {
                    for (hole.tokens, 0..) |htok, htok_idx| {
                        const htok_start = fmt_tok_base +| htok.rel_byte;
                        const htok_end = htok_start +| @as(u32, htok.byte_len);
                        if (htok_start != ident_span.start_byte or htok_end != ident_span.end_byte) continue;
                        if (htok_idx < 2 or htok_idx + 1 >= hole.tokens.len) continue;
                        const prev_kind = hole.tokens[htok_idx - 1].kind;
                        const next_kind = hole.tokens[htok_idx + 1].kind;
                        if ((prev_kind != .lbrace and prev_kind != .comma) or
                            (next_kind != .comma and next_kind != .rbrace))
                        {
                            continue;
                        }
                        var scan_idx = htok_idx - 1;
                        var brace_depth: u32 = 0;
                        var open_brace_pos: ?usize = null;
                        while (true) {
                            const cur_kind = hole.tokens[scan_idx].kind;
                            if (cur_kind == .rbrace) {
                                brace_depth += 1;
                            } else if (cur_kind == .lbrace) {
                                if (brace_depth == 0) {
                                    open_brace_pos = scan_idx;
                                    break;
                                }
                                brace_depth -= 1;
                            }
                            if (scan_idx == 0) break;
                            scan_idx -= 1;
                        }
                        if (open_brace_pos) |open_pos| {
                            if (open_pos > 0 and hole.tokens[open_pos - 1].kind == .type_ident) {
                                const expanded = if (is_renaming_field)
                                    try std.fmt.allocPrint(arena_alloc, "{s}: {s}", .{ new_name, old_name })
                                else
                                    try std.fmt.allocPrint(arena_alloc, "{s}: {s}", .{ old_name, new_name });
                                return .{
                                    .file_id = file_id,
                                    .start_byte = ident_span.start_byte,
                                    .end_byte = ident_span.end_byte,
                                    .replacement = expanded,
                                };
                            }
                        }
                    }
                }
            }
        }
    }
    return null;
}

/// Verifies `E0408` sibling collisions and upward/downward lexical shadowing hazards (`true` when hazard detected).
fn hasRenameCollisionOrShadowingHazard(
    session: *LspSession,
    validated: ValidatedRenameTarget,
    new_name: []const u8,
    hits: []const ReferenceHit,
) !bool {
    const target_sym = session.db.symbol_table.getSymbol(validated.target_sym_idx).*;

    // [1] Check direct `E0408` sibling collision in `target_sym.scope_id`:
    for (session.db.symbol_table.getScopeMembers(target_sym.scope_id)) |sib_idx| {
        if (sib_idx == validated.target_sym_idx) continue;
        const sib_sym = session.db.symbol_table.getSymbol(sib_idx).*;
        if (sib_sym.namespace == target_sym.namespace and std.mem.eql(u8, sib_sym.name_text, new_name)) {
            return true;
        }
    }

    const is_local = switch (target_sym.kind) {
        .local_let_sym, .local_var_sym, .param_sym, .type_param_sym, .const_param_sym => true,
        else => false,
    };

    // [2] Local/parameter upward capture & downward shadowing check inside `validated.enclosing_def_id`:
    if (is_local and !validated.enclosing_def_id.isNone()) {
        const local_fid = validated.cursor_token_span.file_id;
        _ = try session.db.parseCst(local_fid);
        if ((try session.db.extractItemTree(local_fid)).getEntry(validated.enclosing_def_id)) |enc_entry_ptr| {
            var parsed_art = session.db.parsed_artifacts.getPtr(local_fid.asInt()) orelse return false;
            if (computeCstSubtreeByteSpan(
                local_fid,
                &parsed_art.token_buffer,
                &parsed_art.cst_arena,
                enc_entry_ptr.cst_node,
            )) |def_span| {
                if (try session.db.getDefSideTables(validated.enclosing_def_id)) |side_tables| {
                    parsed_art = session.db.parsed_artifacts.getPtr(local_fid.asInt()) orelse return false;
                    // Check if any other symbol named `new_name` in the same namespace is declared or referenced in an overlapping scope:
                    var ast_raw = side_tables.ast_start;
                    const ast_limit = @min(
                        side_tables.ast_end,
                        @as(u32, @intCast(parsed_art.ast_arena.countNodes())),
                    );
                    while (ast_raw < ast_limit) : (ast_raw += 1) {
                        const ast_id = NodeIndex.fromInt(ast_raw);
                        const other_idx = side_tables.getNodeSymbol(ast_id);
                        if (other_idx.isNone() or other_idx == validated.target_sym_idx) continue;
                        const unwrapped_other = resolveLiveCanonicalSymbol(session, other_idx);
                        if (unwrapped_other == validated.target_sym_idx) continue;
                        const other_sym = session.db.symbol_table.getSymbol(unwrapped_other).*;
                        if (other_sym.namespace != target_sym.namespace or
                            !std.mem.eql(u8, other_sym.name_text, new_name))
                        {
                            continue;
                        }
                        // Check scope ancestor relationship between `target_sym.scope_id` and `other_sym.scope_id`:
                        if (isScopeAncestorOrEqual(&session.db.symbol_table.scope_arena, other_sym.scope_id, target_sym.scope_id) or
                            isScopeAncestorOrEqual(&session.db.symbol_table.scope_arena, target_sym.scope_id, other_sym.scope_id))
                        {
                            // Verify the conflicting reference or declaration sits inside `def_span`:
                            const n_tok = resolveAstNodeFocalToken(parsed_art, ast_id);
                            if (!n_tok.isNone() and n_tok.asInt() < parsed_art.token_buffer.countTokens()) {
                                const n_off = parsed_art.token_buffer.getToken(n_tok).byte_offset;
                                if (n_off >= def_span.start_byte and n_off <= def_span.end_byte) {
                                    return true;
                                }
                            }
                        }
                    }

                    // Also check unreferenced live parameters or inner locals named `new_name` in `enc_entry_ptr`:
                    const scratch_alloc = session.turn_arena.asAllocator();
                    var live_param_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty;
                    try collectEntryLiveScopeParamSymbols(session, scratch_alloc, enc_entry_ptr.*, &live_param_syms);
                    for (live_param_syms.items) |cand_idx| {
                        if (cand_idx == validated.target_sym_idx) continue;
                        const cand_sym = session.db.symbol_table.getSymbol(cand_idx).*;
                        if (cand_sym.namespace == target_sym.namespace and
                            std.mem.eql(u8, cand_sym.name_text, new_name))
                        {
                            if (enc_entry_ptr.kind != .impl_decl or
                                isScopeAncestorOrEqual(
                                    &session.db.symbol_table.scope_arena,
                                    target_sym.scope_id,
                                    cand_sym.scope_id,
                                ) or isScopeAncestorOrEqual(
                                &session.db.symbol_table.scope_arena,
                                cand_sym.scope_id,
                                target_sym.scope_id,
                            )) {
                                return true;
                            }
                        }
                    }

                    for (side_tables.node_symbols) |recorded_idx| {
                        if (recorded_idx.isNone() or recorded_idx == validated.target_sym_idx) continue;
                        if (recorded_idx.asInt() >= session.db.symbol_table.countSymbols()) continue;
                        const cand_sym = session.db.symbol_table.getSymbol(recorded_idx).*;
                        const is_body_local = switch (cand_sym.kind) {
                            .local_let_sym, .local_var_sym, .param_sym, .type_param_sym, .const_param_sym => true,
                            else => false,
                        };
                        if (!is_body_local) continue;
                        if (cand_sym.namespace == target_sym.namespace and
                            std.mem.eql(u8, cand_sym.name_text, new_name))
                        {
                            if (isScopeAncestorOrEqual(
                                &session.db.symbol_table.scope_arena,
                                target_sym.scope_id,
                                cand_sym.scope_id,
                            ) or isScopeAncestorOrEqual(
                                &session.db.symbol_table.scope_arena,
                                cand_sym.scope_id,
                                target_sym.scope_id,
                            )) {
                                return true;
                            }
                        }
                    }

                    // Also check symbol references inside `f"…"` interpolation holes in `side_tables`:
                    var interp_it = side_tables.string_interps.iterator();
                    while (interp_it.next()) |interp_kv| {
                        const fmt_ast_raw = side_tables.ast_start + interp_kv.key_ptr.*;
                        if (fmt_ast_raw >= ast_limit) continue;
                        const fmt_main_tok = parsed_art.ast_arena.getNode(NodeIndex.fromInt(fmt_ast_raw)).main_token;
                        if (fmt_main_tok.isNone() or fmt_main_tok.asInt() >= parsed_art.token_buffer.countTokens()) {
                            continue;
                        }
                        const fmt_tok_base = parsed_art.token_buffer.getToken(fmt_main_tok).byte_offset;
                        for (interp_kv.value_ptr.holes) |hole| {
                            for (hole.tokens) |htok| {
                                if (htok.symbol_index.isNone() or htok.symbol_index == validated.target_sym_idx) continue;
                                const unwrapped_htok = resolveLiveCanonicalSymbol(session, htok.symbol_index);
                                if (unwrapped_htok.isNone() or unwrapped_htok == validated.target_sym_idx) continue;
                                const other_sym = session.db.symbol_table.getSymbol(unwrapped_htok).*;
                                if (other_sym.namespace != target_sym.namespace or
                                    !std.mem.eql(u8, other_sym.name_text, new_name))
                                {
                                    continue;
                                }
                                if (isScopeAncestorOrEqual(
                                    &session.db.symbol_table.scope_arena,
                                    other_sym.scope_id,
                                    target_sym.scope_id,
                                ) or isScopeAncestorOrEqual(
                                    &session.db.symbol_table.scope_arena,
                                    target_sym.scope_id,
                                    other_sym.scope_id,
                                )) {
                                    const abs_off = fmt_tok_base +| htok.rel_byte;
                                    if (abs_off >= def_span.start_byte and abs_off <= def_span.end_byte) {
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    // [3] Module / nominal symbol cross-file collision & inner-local shadowing check across all touched files:
    if (target_sym.kind != .field_sym) {
        const scratch_alloc = session.turn_arena.asAllocator();
        var checked_files: std.AutoHashMapUnmanaged(u32, void) = .empty;
        for (hits) |hit| {
            const h_fid = hit.span.file_id;
            if ((try checked_files.getOrPut(scratch_alloc, h_fid.asInt())).found_existing) {
                continue;
            }
            _ = try session.db.resolveSignatures(h_fid);
            // Check module-scope collision in `h_fid` (e.g., imported via `use foo.bar;` or `use foo.*;`):
            if (session.db.symbol_table.file_module_scopes.get(h_fid.asInt())) |h_mod_scope| {
                for (session.db.symbol_table.getScopeMembers(h_mod_scope)) |m_idx| {
                    const unwrapped_m = resolveLiveCanonicalSymbol(session, m_idx);
                    if (m_idx == validated.target_sym_idx or unwrapped_m == validated.target_sym_idx) continue;
                    const m_sym = session.db.symbol_table.getSymbol(m_idx).*;
                    if (m_sym.namespace == target_sym.namespace and std.mem.eql(u8, m_sym.name_text, new_name)) {
                        return true;
                    }
                }
            }

            // Check whether any item containing a reference hit in `h_fid` binds a live local/param named `new_name`:
            _ = try session.db.parseCst(h_fid);
            const h_entries = try scratch_alloc.dupe(
                query_db.ItemTreeEntry,
                (try session.db.extractItemTree(h_fid)).entries,
            );
            for (h_entries) |entry| {
                const h_parsed = session.db.parsed_artifacts.getPtr(h_fid.asInt()) orelse break;
                const entry_sp = computeCstSubtreeByteSpan(
                    h_fid,
                    &h_parsed.token_buffer,
                    &h_parsed.cst_arena,
                    entry.cst_node,
                ) orelse continue;
                var has_hit_in_entry = false;
                for (hits) |cand_h| {
                    if (cand_h.span.file_id == h_fid and
                        cand_h.span.start_byte >= entry_sp.start_byte and
                        cand_h.span.end_byte <= entry_sp.end_byte)
                    {
                        has_hit_in_entry = true;
                        break;
                    }
                }
                if (!has_hit_in_entry) continue;

                var entry_params: std.ArrayListUnmanaged(SymbolIndex) = .empty;
                try collectEntryLiveScopeParamSymbols(session, scratch_alloc, entry, &entry_params);
                for (entry_params.items) |param_idx| {
                    if (param_idx == validated.target_sym_idx) continue;
                    const param_sym = session.db.symbol_table.getSymbol(param_idx).*;
                    if (param_sym.namespace == target_sym.namespace and
                        std.mem.eql(u8, param_sym.name_text, new_name))
                    {
                        return true;
                    }
                }

                if (entry.kind != .mod_decl and entry.kind != .use_decl and entry.kind != .ffi_extern_block) {
                    if (try session.db.getDefSideTables(entry.def_id)) |entry_side_tables| {
                        for (entry_side_tables.node_symbols) |recorded_idx| {
                            if (recorded_idx.isNone() or recorded_idx == validated.target_sym_idx) continue;
                            if (recorded_idx.asInt() >= session.db.symbol_table.countSymbols()) continue;
                            const loc_sym = session.db.symbol_table.getSymbol(recorded_idx).*;
                            const is_inner_local = switch (loc_sym.kind) {
                                .local_let_sym,
                                .local_var_sym,
                                .param_sym,
                                .type_param_sym,
                                .const_param_sym,
                                => true,
                                else => false,
                            };
                            if (is_inner_local and loc_sym.namespace == target_sym.namespace and
                                std.mem.eql(u8, loc_sym.name_text, new_name))
                            {
                                return true;
                            }
                        }
                        var entry_interp_it = entry_side_tables.string_interps.valueIterator();
                        while (entry_interp_it.next()) |interp_ptr| {
                            for (interp_ptr.holes) |hole| {
                                for (hole.tokens) |htok| {
                                    if (htok.symbol_index.isNone() or htok.symbol_index == validated.target_sym_idx) {
                                        continue;
                                    }
                                    if (htok.symbol_index.asInt() >= session.db.symbol_table.countSymbols()) continue;
                                    const loc_sym = session.db.symbol_table.getSymbol(htok.symbol_index).*;
                                    const is_inner_local = switch (loc_sym.kind) {
                                        .local_let_sym,
                                        .local_var_sym,
                                        .param_sym,
                                        .type_param_sym,
                                        .const_param_sym,
                                        => true,
                                        else => false,
                                    };
                                    if (is_inner_local and loc_sym.namespace == target_sym.namespace and
                                        std.mem.eql(u8, loc_sym.name_text, new_name))
                                    {
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    return false;
}

/// Returns `true` when `ancestor` equals `descendant` or lies on `descendant`'s parent chain.
fn isScopeAncestorOrEqual(
    scope_arena: *const symbol_resolver.ScopeArena,
    ancestor: ScopeId,
    descendant: ScopeId,
) bool {
    if (ancestor.isNone() or descendant.isNone()) return false;
    var cur = descendant;
    var steps: usize = 0;
    while (!cur.isNone() and cur.asInt() < scope_arena.countScopes() and steps < 128) : (steps += 1) {
        if (cur == ancestor) return true;
        cur = scope_arena.getScope(cur).parent;
    }
    return false;
}

/// Handles `textDocument/prepareRename`: returns `{range, placeholder}` or `null` when non-renamable.
fn handlePrepareRenameRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const pos = extractJsonPosition(params.getField("position") orelse JsonValue{ .null_val = {} }) orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing position");
    };

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone()) return writeNullResultFrame(session, out_writer, rpc_id);

    const validated = (try validateRenamableSymbolAtCursor(session, fid, pos)) orelse {
        return writeNullResultFrame(session, out_writer, rpc_id);
    };

    const tok_range = spanToLspRange(session, fid, validated.cursor_token_span);
    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":{\"range\":");
    try writeLspRangeJson(body_writer, tok_range);
    try body_writer.writeAll(",\"placeholder\":");
    try writeJsonString(body_writer, validated.old_name);
    try body_writer.writeAll("}}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

/// Orders `RenamePlanEdit` records by `(file_id ASC, start_byte ASC, end_byte ASC)`.
fn isRenameEditBefore(_: void, lhs_edit: RenamePlanEdit, rhs_edit: RenamePlanEdit) bool {
    if (lhs_edit.file_id.asInt() != rhs_edit.file_id.asInt()) {
        return lhs_edit.file_id.asInt() < rhs_edit.file_id.asInt();
    }
    if (lhs_edit.start_byte != rhs_edit.start_byte) return lhs_edit.start_byte < rhs_edit.start_byte;
    return lhs_edit.end_byte < rhs_edit.end_byte;
}

/// Handles `textDocument/rename`: enforces `PackageId.root`, `DR-03` casing, shorthand expansion & shadowing hygiene.
fn handleRenameRequest(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    params: JsonValue,
    out_writer: *std.Io.Writer,
    rpc_id: JsonRpcId,
) !void {
    const raw_uri = (try extractValidatedRequestUri(session, params, out_writer, rpc_id)) orelse return;
    const pos = extractJsonPosition(params.getField("position") orelse JsonValue{ .null_val = {} }) orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing position");
    };
    const new_name = params.getStringField("newName") orelse {
        return sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INVALID_PARAMS, "missing newName");
    };

    const fid = try resolveDocumentFileId(session, arena_alloc, raw_uri);
    if (fid.isNone() or isReadOnlyNonWorkspaceFile(session, fid)) {
        return sendJsonRpcError(
            session,
            out_writer,
            rpc_id,
            LSP_REQUEST_FAILED,
            "document is read-only or not mounted in workspace",
        );
    }

    const validated = (try validateRenamableSymbolAtCursor(session, fid, pos)) orelse {
        return sendJsonRpcError(
            session,
            out_writer,
            rpc_id,
            LSP_REQUEST_FAILED,
            "symbol cannot be renamed (external package, built-in, keyword, or file module)",
        );
    };

    const target_sym = session.db.symbol_table.getSymbol(validated.target_sym_idx).*;
    if (!isValidDr03RenameIdentifier(target_sym, new_name)) {
        return sendJsonRpcError(
            session,
            out_writer,
            rpc_id,
            JSONRPC_INVALID_PARAMS,
            "invalid CoreX identifier or DR-03 casing violation for symbol namespace",
        );
    }

    if (std.mem.eql(u8, new_name, validated.old_name)) {
        session.outbound_buf.clearRetainingCapacity();
        const body_writer = &session.outbound_buf.writer;
        try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
        try writeJsonRpcId(body_writer, rpc_id);
        try body_writer.writeAll(",\"result\":{\"changes\":{}}}");
        return flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
    }

    const is_local = switch (target_sym.kind) {
        .local_let_sym, .local_var_sym, .param_sym, .type_param_sym, .const_param_sym => true,
        else => false,
    };

    // Collect all occurrences across `PackageId.root` (both open `.low` and unopened `.medium` `.cx` files!):
    var hits: std.ArrayListUnmanaged(ReferenceHit) = .empty;
    if (is_local or validated.is_explicit_local_alias) {
        try collectSymbolOccurrencesInFile(
            session,
            arena_alloc,
            fid,
            validated.target_sym_idx,
            validated.is_explicit_local_alias,
            true,
            if (is_local) validated.enclosing_def_id else .NONE,
            MAX_REFERENCES * 4,
            &hits,
        );
    } else {
        const decl_fid = target_sym.decl_span.file_id;
        for (session.mounted_files.items) |cand_fid| {
            try session.db.unwindIfCanceled();
            if (isReadOnlyNonWorkspaceFile(session, cand_fid)) continue;
            const cand_src = getLiveDocumentSource(session, cand_fid) orelse continue;
            if (cand_fid != decl_fid and std.mem.indexOf(u8, cand_src, validated.old_name) == null) {
                continue;
            }
            try collectSymbolOccurrencesInFile(
                session,
                arena_alloc,
                cand_fid,
                validated.target_sym_idx,
                false,
                true,
                .NONE,
                MAX_REFERENCES * 4,
                &hits,
            );
        }
    }

    // Verify `E0408` sibling collisions and upward/downward lexical shadowing hazards BEFORE emitting edits:
    if (try hasRenameCollisionOrShadowingHazard(session, validated, new_name, hits.items)) {
        return sendJsonRpcError(
            session,
            out_writer,
            rpc_id,
            LSP_REQUEST_FAILED,
            "rename rejected due to scope collision (E0408) or lexical shadowing hazard",
        );
    }

    // Build surgical `RenamePlanEdit`s, expanding `Point { x }` and `Point { var x }` shorthands:
    const is_renaming_field = (target_sym.kind == .field_sym);
    const is_shorthand_candidate = is_renaming_field or
        target_sym.kind == .local_let_sym or
        target_sym.kind == .local_var_sym or
        target_sym.kind == .param_sym or
        target_sym.kind == .const_sym;

    var planned_edits: std.ArrayListUnmanaged(RenamePlanEdit) = .empty;
    for (hits.items) |hit| {
        const h_fid = hit.span.file_id;
        const h_src = getLiveDocumentSource(session, h_fid) orelse continue;
        const decl_live = session.db.resolveLiveSymbolDeclSpan(validated.target_sym_idx) catch target_sym.decl_span;
        const h_parsed = try session.db.parseCst(h_fid);

        const is_decl_span = (h_fid == decl_live.file_id and
            hit.span.start_byte == decl_live.start_byte and
            hit.span.end_byte == decl_live.end_byte);

        if (is_shorthand_candidate and (!is_decl_span or
            target_sym.kind == .local_let_sym or target_sym.kind == .local_var_sym))
        {
            if (try tryBuildShorthandExpansionEdit(
                session,
                arena_alloc,
                h_fid,
                h_src,
                h_parsed,
                hit.span,
                validated.old_name,
                new_name,
                is_renaming_field,
            )) |shorthand_edit| {
                try planned_edits.append(arena_alloc, shorthand_edit);
                continue;
            }
        }

        try planned_edits.append(arena_alloc, .{
            .file_id = h_fid,
            .start_byte = hit.span.start_byte,
            .end_byte = hit.span.end_byte,
            .replacement = new_name,
        });
    }

    std.mem.sort(RenamePlanEdit, planned_edits.items, {}, isRenameEditBefore);

    // Emit `WorkspaceEdit.changes` grouped by client URI, deduplicating identical spans:
    session.outbound_buf.clearRetainingCapacity();
    const body_writer = &session.outbound_buf.writer;
    try body_writer.writeAll("{\"jsonrpc\":\"2.0\",\"id\":");
    try writeJsonRpcId(body_writer, rpc_id);
    try body_writer.writeAll(",\"result\":{\"changes\":{");

    var edit_idx: usize = 0;
    var file_group_count: usize = 0;
    while (edit_idx < planned_edits.items.len) {
        const group_fid = planned_edits.items[edit_idx].file_id;
        const group_uri = try resolveOutboundUri(session, arena_alloc, group_fid);
        if (file_group_count > 0) try body_writer.writeByte(',');
        try writeJsonString(body_writer, group_uri);
        try body_writer.writeAll(":[");

        var item_in_file: usize = 0;
        var prev_end_byte: u32 = 0;
        var has_prev = false;
        while (edit_idx < planned_edits.items.len and planned_edits.items[edit_idx].file_id == group_fid) : (edit_idx += 1) {
            const ed = planned_edits.items[edit_idx];
            if (has_prev and ed.start_byte < prev_end_byte) continue;
            const ed_range = spanToLspRange(session, group_fid, Span.init(group_fid, ed.start_byte, ed.end_byte));
            if (item_in_file > 0) try body_writer.writeByte(',');
            try body_writer.writeAll("{\"range\":");
            try writeLspRangeJson(body_writer, ed_range);
            try body_writer.writeAll(",\"newText\":");
            try writeJsonString(body_writer, ed.replacement);
            try body_writer.writeByte('}');
            prev_end_byte = ed.end_byte;
            has_prev = true;
            item_in_file += 1;
        }
        try body_writer.writeByte(']');
        file_group_count += 1;
    }

    try body_writer.writeAll("}}}");
    try flushOutboundJsonFrame(out_writer, session.outbound_buf.written());
}

// ---------- Batch Pre-Drain & JSON-RPC Dispatch Loop ----------

/// Parsed batch slot used by `drainAndDispatchBatch` to pre-register `$/cancelRequest` and coalesce `didChange`.
const ParsedBatchSlot = struct {
    /// Raw frame read status (`.payload`, `.header_parse_error`, `.content_too_large`, `.eof`).
    frame_tag: std.meta.Tag(InboundFrame),
    /// `true` when `.content_too_large` left unconsumed body bytes on the stream, requiring clean session halt.
    is_unrecoverable_stream: bool = false,
    /// Owned raw payload slice to free after turn (`&.{}` when non-payload).
    owned_payload: []u8 = &.{},
    /// JSON parse error code when `has_parse_error` is `true`.
    has_parse_error: bool = false,
    /// Parsed root JSON value when valid.
    json_root: JsonValue = .{ .null_val = {} },
    /// Extracted JSON-RPC `id` (`.missing` on notifications).
    rpc_id: JsonRpcId = .missing,
    /// Extracted `"method"` name (`""` when missing).
    method_str: []const u8 = "",
    /// `true` once consumed by priority `$/cancelRequest` pre-pass or `didChange` coalescing.
    is_consumed: bool = false,
};

/// Flushes deferred `didOpen` push diagnostics once interactive requests in the active batch complete.
fn flushPendingPushDiagnostics(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    out_writer: *std.Io.Writer,
) !void {
    if (session.is_pull_diagnostics_enabled or session.pending_push_diag_files.items.len == 0) {
        session.pending_push_diag_files.clearRetainingCapacity();
        return;
    }
    const pending_copy = try arena_alloc.dupe(FileId, session.pending_push_diag_files.items);
    session.pending_push_diag_files.clearRetainingCapacity();
    for (pending_copy) |fid| {
        if (!session.open_doc_versions.contains(fid.asInt())) continue;
        try publishDiagnosticsNotification(session, arena_alloc, fid, out_writer);
    }
}

/// Dispatches a single validated JSON-RPC request or notification onto `session`.
fn dispatchSingleJsonMessage(
    session: *LspSession,
    arena_alloc: std.mem.Allocator,
    msg_obj: JsonValue,
    rpc_id: JsonRpcId,
    method_str: []const u8,
    out_writer: *std.Io.Writer,
    exit_code_out: *?u8,
) !void {
    const is_notification = (rpc_id == .missing);
    const params = msg_obj.getField("params") orelse JsonValue{ .object_val = &.{} };
    const method_opt = LSP_METHOD_MAP.get(method_str);

    // `exit` notification terminates immediately regardless of initialization state (`0` after `shutdown`, else `1`):
    if (method_opt == .exit) {
        exit_code_out.* = if (session.state == .shutting_down) 0 else 1;
        return;
    }

    // Lifecycle guard before `initialize`:
    if (session.state == .uninitialized) {
        if (method_opt != .initialize) {
            if (!is_notification) {
                try sendJsonRpcError(
                    session,
                    out_writer,
                    rpc_id,
                    LSP_SERVER_NOT_INITIALIZED,
                    "server has not received initialize request",
                );
            }
            return;
        }
    } else if (session.state == .shutting_down) {
        if (!is_notification) {
            try sendJsonRpcError(
                session,
                out_writer,
                rpc_id,
                JSONRPC_INVALID_REQUEST,
                "server is shutting down; only exit notification is permitted",
            );
        }
        return;
    }

    // Check pre-drained `$/cancelRequest` ring buffer before running any query work:
    if (!is_notification and session.canceled_ring.consumeIfCanceled(rpc_id)) {
        return sendJsonRpcError(session, out_writer, rpc_id, LSP_REQUEST_CANCELED, "request canceled by client");
    }

    const method_tag = method_opt orelse {
        if (!is_notification) {
            try sendJsonRpcError(
                session,
                out_writer,
                rpc_id,
                JSONRPC_METHOD_NOT_FOUND,
                "unsupported LSP method",
            );
        }
        return;
    };

    if (session.log_writer) |log_w| {
        if (session.trace_mode != .off) {
            log_w.print("[corex-lsp] -> {s}\n", .{method_str}) catch {};
            log_w.flush() catch {};
        }
    }

    session.db.clearCancellation();

    const dispatch_res: anyerror!void = switch (method_tag) {
        .initialize => blk: {
            if (session.state != .uninitialized) {
                break :blk sendJsonRpcError(
                    session,
                    out_writer,
                    rpc_id,
                    JSONRPC_INVALID_REQUEST,
                    "initialize may only be called once",
                );
            }
            break :blk handleInitializeRequest(session, arena_alloc, params, out_writer, rpc_id);
        },
        .initialized => {},
        .shutdown => blk: {
            try flushPendingPushDiagnostics(session, arena_alloc, out_writer);
            session.state = .shutting_down;
            break :blk writeNullResultFrame(session, out_writer, rpc_id);
        },
        .exit => unreachable,
        .set_trace => {
            if (params.getStringField("value")) |trace_str| {
                if (std.mem.eql(u8, trace_str, "verbose")) {
                    session.trace_mode = .verbose;
                } else if (std.mem.eql(u8, trace_str, "messages")) {
                    session.trace_mode = .messages;
                } else {
                    session.trace_mode = .off;
                }
            }
        },
        .cancel_request => {
            if (extractJsonRpcId(params) catch null) |cancel_id| {
                session.canceled_ring.insert(cancel_id);
            }
        },
        .did_open => handleDidOpenNotification(session, arena_alloc, params),
        .did_change => blk_dc: {
            try flushPendingPushDiagnostics(session, arena_alloc, out_writer);
            break :blk_dc handleDidChangeNotificationBatch(session, arena_alloc, &.{params});
        },
        .did_save => handleDidSaveNotification(session, arena_alloc, params),
        .did_close => blk_cl: {
            try flushPendingPushDiagnostics(session, arena_alloc, out_writer);
            break :blk_cl handleDidCloseNotification(session, arena_alloc, params, out_writer);
        },
        .did_change_watched_files => handleDidChangeWatchedFilesNotification(session, arena_alloc, params),
        .document_diagnostic => handlePullDiagnosticRequest(session, arena_alloc, params, out_writer, rpc_id),
        .semantic_tokens_full => handleSemanticTokensFullOrRange(
            session,
            arena_alloc,
            params,
            false,
            out_writer,
            rpc_id,
        ),
        .semantic_tokens_range => handleSemanticTokensFullOrRange(
            session,
            arena_alloc,
            params,
            true,
            out_writer,
            rpc_id,
        ),
        .semantic_tokens_delta => handleSemanticTokensDelta(session, arena_alloc, params, out_writer, rpc_id),
        .hover => handleHoverRequest(session, arena_alloc, params, out_writer, rpc_id),
        .definition => handleDefinitionOrTypeDefinition(session, arena_alloc, params, false, out_writer, rpc_id),
        .type_definition => handleDefinitionOrTypeDefinition(session, arena_alloc, params, true, out_writer, rpc_id),
        .document_highlight => handleDocumentHighlightRequest(session, arena_alloc, params, out_writer, rpc_id),
        .references => handleReferencesRequest(session, arena_alloc, params, out_writer, rpc_id),
        .document_symbol => handleDocumentSymbolRequest(session, arena_alloc, params, out_writer, rpc_id),
        .workspace_symbol => handleWorkspaceSymbolRequest(session, arena_alloc, params, out_writer, rpc_id),
        .completion => handleCompletionRequest(session, arena_alloc, params, out_writer, rpc_id),
        .signature_help => handleSignatureHelpRequest(session, arena_alloc, params, out_writer, rpc_id),
        .inlay_hint => handleInlayHintRequest(session, arena_alloc, params, out_writer, rpc_id),
        .code_action => blk_ca: {
            try flushPendingPushDiagnostics(session, arena_alloc, out_writer);
            break :blk_ca handleCodeActionRequest(session, arena_alloc, params, out_writer, rpc_id);
        },
        .code_lens => handleCodeLensRequest(session, arena_alloc, params, out_writer, rpc_id),
        .formatting => handleFormattingRequest(session, arena_alloc, params, false, out_writer, rpc_id),
        .range_formatting => handleFormattingRequest(session, arena_alloc, params, true, out_writer, rpc_id),
        .prepare_rename => handlePrepareRenameRequest(session, arena_alloc, params, out_writer, rpc_id),
        .rename => handleRenameRequest(session, arena_alloc, params, out_writer, rpc_id),
    };

    dispatch_res catch |err| switch (err) {
        error.Canceled => {
            session.db.clearCancellation();
            if (!is_notification) {
                const cancel_code: i32 = if (session.canceled_ring.consumeIfCanceled(rpc_id))
                    LSP_REQUEST_CANCELED
                else
                    LSP_SERVER_CANCELED;
                try sendJsonRpcError(session, out_writer, rpc_id, cancel_code, "request canceled");
            }
        },
        error.OutOfMemory => return error.OutOfMemory,
        else => {
            if (session.log_writer) |log_w| {
                log_w.print("[corex-lsp] error in {s}: {s}\n", .{ method_str, @errorName(err) }) catch {};
                log_w.flush() catch {};
            }
            if (!is_notification) {
                try sendJsonRpcError(session, out_writer, rpc_id, JSONRPC_INTERNAL_ERROR, "internal compiler error");
            }
        },
    };
}

/// Reads 1 blocking frame + up to `63` buffered frames, pre-registers `$/cancelRequest`, and coalesces `didChange`.
fn drainAndDispatchInboundTurn(
    session: *LspSession,
    reader: *std.Io.Reader,
    out_writer: *std.Io.Writer,
    exit_code_out: *?u8,
) !bool {
    session.turn_arena.resetRetainingCapacity();
    const arena_alloc = session.turn_arena.asAllocator();

    var batch: [MAX_BATCHED_INBOUND_FRAMES]ParsedBatchSlot = undefined;
    var batch_count: usize = 0;
    defer {
        var k_idx: usize = 0;
        while (k_idx < batch_count) : (k_idx += 1) {
            if (batch[k_idx].owned_payload.len > 0) {
                session.allocator.free(batch[k_idx].owned_payload);
            }
        }
    }

    const first_frame = try readSingleInboundFrame(session.allocator, reader);
    if (first_frame == .eof) return false;
    batch[0] = populateBatchSlot(arena_alloc, first_frame);
    batch_count = 1;

    // Drain any already-buffered complete frames (`<= MAX_BATCHED_INBOUND_FRAMES`):
    while (!batch[batch_count - 1].is_unrecoverable_stream and
        batch_count < MAX_BATCHED_INBOUND_FRAMES and
        reader.bufferedLen() > 0)
    {
        const next_frame = (try tryExtractCompleteBufferedFrame(session.allocator, reader)) orelse break;
        if (next_frame == .eof) break;
        batch[batch_count] = populateBatchSlot(arena_alloc, next_frame);
        batch_count += 1;
    }

    // Priority pre-pass; pre-register `$/cancelRequest` IDs before dispatching preceding requests in `batch`:
    var i: usize = 0;
    while (i < batch_count) : (i += 1) {
        if (batch[i].frame_tag != .payload or batch[i].has_parse_error) continue;
        if (std.mem.eql(u8, batch[i].method_str, "$/cancelRequest")) {
            if (batch[i].json_root.getField("params")) |cancel_params| {
                if (extractJsonRpcId(cancel_params) catch null) |cancel_id| {
                    session.canceled_ring.insert(cancel_id);
                }
            }
            batch[i].is_consumed = true;
        }
    }

    // Sequential dispatch with consecutive same-URI `textDocument/didChange` coalescing:
    var slot_idx: usize = 0;
    while (slot_idx < batch_count) : (slot_idx += 1) {
        const slot = batch[slot_idx];
        if (slot.is_consumed) continue;

        switch (slot.frame_tag) {
            .eof => return false,
            .header_parse_error => {
                try sendJsonRpcError(
                    session,
                    out_writer,
                    .null_id,
                    JSONRPC_PARSE_ERROR,
                    "malformed or oversized LSP frame header",
                );
                continue;
            },
            .content_too_large => {
                try sendJsonRpcError(
                    session,
                    out_writer,
                    .null_id,
                    JSONRPC_INVALID_REQUEST,
                    "LSP frame Content-Length exceeds 16 MiB maximum",
                );
                if (slot.is_unrecoverable_stream) return false;
                continue;
            },
            .payload => {},
        }

        if (slot.has_parse_error) {
            try sendJsonRpcError(
                session,
                out_writer,
                .null_id,
                JSONRPC_PARSE_ERROR,
                "invalid JSON-RPC payload or nesting depth exceeded",
            );
            continue;
        }

        if (slot.json_root != .object_val) {
            try sendJsonRpcError(
                session,
                out_writer,
                .null_id,
                JSONRPC_INVALID_REQUEST,
                "JSON-RPC root value must be an object",
            );
            continue;
        }
        if (!std.mem.eql(u8, slot.json_root.getStringField("jsonrpc") orelse "", "2.0") or
            slot.method_str.len == 0)
        {
            try sendJsonRpcError(
                session,
                out_writer,
                slot.rpc_id,
                JSONRPC_INVALID_REQUEST,
                "invalid JSON-RPC 2.0 envelope",
            );
            continue;
        }

        // Coalesce consecutive buffered `textDocument/didChange` notifications targeting the same URI:
        if (session.state == .initialized and
            slot.rpc_id == .missing and
            std.mem.eql(u8, slot.method_str, "textDocument/didChange"))
        {
            const first_params = slot.json_root.getField("params") orelse JsonValue{ .object_val = &.{} };
            const first_uri = if (first_params.getField("textDocument")) |td|
                (td.getStringField("uri") orelse "")
            else
                "";

            if (first_uri.len > 0 and first_uri.len <= MAX_LSP_URI_BYTES) {
                var coalesced_params: std.ArrayListUnmanaged(JsonValue) = .empty;
                try coalesced_params.append(arena_alloc, first_params);

                var look_idx = slot_idx + 1;
                while (look_idx < batch_count) : (look_idx += 1) {
                    if (batch[look_idx].is_consumed) continue;
                    if (batch[look_idx].frame_tag != .payload or batch[look_idx].has_parse_error) break;
                    if (batch[look_idx].rpc_id != .missing or
                        !std.mem.eql(u8, batch[look_idx].method_str, "textDocument/didChange"))
                    {
                        break;
                    }
                    const next_params = batch[look_idx].json_root.getField("params") orelse break;
                    const next_td = next_params.getField("textDocument") orelse break;
                    const next_uri = next_td.getStringField("uri") orelse break;
                    if (!std.mem.eql(u8, first_uri, next_uri)) break;

                    try coalesced_params.append(arena_alloc, next_params);
                    batch[look_idx].is_consumed = true;
                }

                try flushPendingPushDiagnostics(session, arena_alloc, out_writer);
                try handleDidChangeNotificationBatch(session, arena_alloc, coalesced_params.items);
                continue;
            }
        }

        try dispatchSingleJsonMessage(
            session,
            arena_alloc,
            slot.json_root,
            slot.rpc_id,
            slot.method_str,
            out_writer,
            exit_code_out,
        );
        if (exit_code_out.* != null) return false;
    }

    try flushPendingPushDiagnostics(session, arena_alloc, out_writer);
    return true;
}

/// Parses an `InboundFrame` into a `ParsedBatchSlot` inside `arena_alloc`.
fn populateBatchSlot(arena_alloc: std.mem.Allocator, frame: InboundFrame) ParsedBatchSlot {
    switch (frame) {
        .eof => return .{ .frame_tag = .eof },
        .header_parse_error => return .{ .frame_tag = .header_parse_error },
        .content_too_large => |is_unrecoverable| return .{
            .frame_tag = .content_too_large,
            .is_unrecoverable_stream = is_unrecoverable,
        },
        .payload => |owned_bytes| {
            const parsed_val = parseJsonPayload(arena_alloc, owned_bytes) catch {
                return .{
                    .frame_tag = .payload,
                    .owned_payload = owned_bytes,
                    .has_parse_error = true,
                };
            };
            if (parsed_val != .object_val) {
                return .{
                    .frame_tag = .payload,
                    .owned_payload = owned_bytes,
                    .json_root = parsed_val,
                };
            }
            const extracted_id = extractJsonRpcId(parsed_val) catch {
                return .{
                    .frame_tag = .payload,
                    .owned_payload = owned_bytes,
                    .json_root = .{ .null_val = {} },
                };
            };
            return .{
                .frame_tag = .payload,
                .owned_payload = owned_bytes,
                .json_root = parsed_val,
                .rpc_id = extracted_id,
                .method_str = parsed_val.getStringField("method") orelse "",
            };
        },
    }
}

/// Wraps a raw JSON body in a `Content-Length: <N>\r\n\r\n<body>` frame inside `out_buf`.
fn appendTestLspFrame(
    allocator: std.mem.Allocator,
    out_buf: *std.ArrayListUnmanaged(u8),
    json_body: []const u8,
) !void {
    const frame_str = try std.fmt.allocPrint(
        allocator,
        "Content-Length: {d}\r\n\r\n{s}",
        .{ json_body.len, json_body },
    );
    defer allocator.free(frame_str);
    try out_buf.appendSlice(allocator, frame_str);
}

/// Extracts all outbound JSON-RPC frame bodies from a captured `Content-Length` wire stream.
fn extractTestOutboundPayloads(
    allocator: std.mem.Allocator,
    wire_bytes: []const u8,
) ![][]const u8 {
    var bodies: std.ArrayListUnmanaged([]const u8) = .empty;
    errdefer bodies.deinit(allocator);
    var cursor: usize = 0;
    while (cursor < wire_bytes.len) {
        const sep = std.mem.indexOfPos(u8, wire_bytes, cursor, "\r\n\r\n") orelse break;
        const len_val = switch (extractHeaderContentLength(wire_bytes[cursor..sep])) {
            .ok => |byte_len| byte_len,
            .overflow, .invalid => break,
        };
        if (len_val > MAX_LSP_CONTENT_LENGTH) break;
        const start_byte = sep + 4;
        const end_byte = std.math.add(usize, start_byte, len_val) catch break;
        if (end_byte > wire_bytes.len) break;
        try bodies.append(allocator, wire_bytes[start_byte..end_byte]);
        cursor = end_byte;
    }
    return bodies.toOwnedSlice(allocator);
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Decodes a `file://` URI into a normalized `/` path matching `VfsSourceMap` (`d:/…` on Windows, `/cx/…` on `.cxtree`).
pub fn decodeFileUriToNormalizedPath(allocator: std.mem.Allocator, raw_uri: []const u8) ![]u8 {
    var path_part: []const u8 = raw_uri;
    if (std.ascii.startsWithIgnoreCase(raw_uri, "file://")) {
        const after_scheme = raw_uri["file://".len..];
        if (std.mem.startsWith(u8, after_scheme, "/")) {
            path_part = after_scheme;
        } else if (std.mem.indexOfScalar(u8, after_scheme, '/')) |slash_idx| {
            const host_part = after_scheme[0..slash_idx];
            var host_buf: [128]u8 = undefined;
            const decoded_host_opt = decodePercentSliceBounded(&host_buf, host_part);
            if (decoded_host_opt != null and std.ascii.eqlIgnoreCase(decoded_host_opt.?, "localhost")) {
                path_part = after_scheme[slash_idx..];
            } else if (decoded_host_opt != null and
                decoded_host_opt.?.len == 2 and
                std.ascii.isAlphabetic(decoded_host_opt.?[0]) and
                decoded_host_opt.?[1] == ':')
            {
                path_part = after_scheme;
            } else {
                // Preserve UNC authority (`file://server/share/` -> `//server/share`):
                var unc_buf: std.ArrayListUnmanaged(u8) = .empty;
                errdefer unc_buf.deinit(allocator);
                try unc_buf.appendSlice(allocator, "//");
                try appendPercentDecodedNormalized(&unc_buf, allocator, after_scheme);
                while (unc_buf.items.len > 2 and unc_buf.items[unc_buf.items.len - 1] == '/') {
                    unc_buf.items.len -= 1;
                }
                return unc_buf.toOwnedSlice(allocator);
            }
        } else {
            path_part = after_scheme;
        }
    }

    var decoded: std.ArrayListUnmanaged(u8) = .empty;
    errdefer decoded.deinit(allocator);
    try appendPercentDecodedNormalized(&decoded, allocator, path_part);

    var slice = decoded.items;
    // Strip leading `/` before Windows drive letters (`/D:/foo` or `/d%3A/foo` -> `d:/foo`):
    if (slice.len >= 3 and slice[0] == '/' and std.ascii.isAlphabetic(slice[1]) and slice[2] == ':') {
        const lower_drive = std.ascii.toLower(slice[1]);
        std.mem.copyForwards(u8, slice[0 .. slice.len - 1], slice[1..]);
        slice[0] = lower_drive;
        decoded.items.len -= 1;
        slice = decoded.items;
    } else if (slice.len >= 2 and std.ascii.isAlphabetic(slice[0]) and slice[1] == ':') {
        slice[0] = std.ascii.toLower(slice[0]);
    }

    // Trim redundant trailing `/` except on filesystem roots (`"/"`, `"d:/"`, or UNC `"//"`):
    const min_keep_len: usize = if (std.mem.startsWith(u8, slice, "//")) 2 else 1;
    while (slice.len > min_keep_len and slice[slice.len - 1] == '/') {
        if (slice.len == 3 and std.ascii.isAlphabetic(slice[0]) and slice[1] == ':') break;
        decoded.items.len -= 1;
        slice = decoded.items;
    }
    return decoded.toOwnedSlice(allocator);
}

/// Encodes a normalized VFS path (`d:/foo/bar.cx`, `/home/u/a.cx`, `/cx/pkg@1.0.0/src/lib.cx`) into a `file://` URI.
pub fn encodePathToFileUri(allocator: std.mem.Allocator, raw_path: []const u8) ![]u8 {
    var uri_buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer uri_buf.deinit(allocator);

    if (std.mem.startsWith(u8, raw_path, "//")) {
        try uri_buf.appendSlice(allocator, "file:");
    } else if (raw_path.len >= 2 and std.ascii.isAlphabetic(raw_path[0]) and raw_path[1] == ':') {
        try uri_buf.appendSlice(allocator, "file:///");
    } else if (std.mem.startsWith(u8, raw_path, "/")) {
        try uri_buf.appendSlice(allocator, "file://");
    } else {
        try uri_buf.appendSlice(allocator, "file:///");
    }

    for (raw_path) |raw_ch| {
        const ch_val: u8 = if (raw_ch == '\\') '/' else raw_ch;
        const is_unreserved = std.ascii.isAlphanumeric(ch_val) or
            ch_val == '/' or ch_val == '-' or ch_val == '_' or
            ch_val == '.' or ch_val == '~' or ch_val == ':' or ch_val == '@';
        if (is_unreserved) {
            try uri_buf.append(allocator, ch_val);
        } else {
            var pct_tmp: [3]u8 = undefined;
            _ = std.fmt.bufPrint(&pct_tmp, "%{X:0>2}", .{ch_val}) catch unreachable;
            try uri_buf.appendSlice(allocator, &pct_tmp);
        }
    }
    return uri_buf.toOwnedSlice(allocator);
}

/// Starts the built-in CoreX LSP 3.17 daemon over `stdin` / `stdout` using Zig `0.17.0` streaming I/O.
pub fn runServerStdio(
    allocator: std.mem.Allocator,
    io: std.Io,
    environ_map: ?*const std.process.Environ.Map,
    options: LspServerOptions,
) !u8 {
    var stdin_buffer: [64 * 1024]u8 = undefined;
    var stdout_buffer: [64 * 1024]u8 = undefined;
    var stderr_buffer: [8 * 1024]u8 = undefined;

    var stdin_reader = std.Io.File.stdin().readerStreaming(io, &stdin_buffer);
    var stdout_writer = std.Io.File.stdout().writerStreaming(io, &stdout_buffer);
    var stderr_writer = std.Io.File.stderr().writerStreaming(io, &stderr_buffer);

    return runServerStream(
        allocator,
        io,
        environ_map,
        &stdin_reader.interface,
        &stdout_writer.interface,
        &stderr_writer.interface,
        options,
    );
}

/// Runs the CoreX LSP 3.17 event loop over arbitrary `*std.Io.Reader` / `*std.Io.Writer` streams.
pub fn runServerStream(
    allocator: std.mem.Allocator,
    io: std.Io,
    environ_map: ?*const std.process.Environ.Map,
    reader: *std.Io.Reader,
    writer: *std.Io.Writer,
    log_writer: ?*std.Io.Writer,
    options: LspServerOptions,
) !u8 {
    var session = try LspSession.init(allocator, io, environ_map, log_writer, options);
    defer session.deinit();
    session.bindInternalPointers();
    return session.feedStream(reader, writer);
}

/// Returns `true` when `rel_cursor` sits strictly inside an active `{…}` interpolation hole of `fmt_lexeme`.
pub fn isCursorInsideFmtStringHole(fmt_lexeme: []const u8, rel_cursor: usize) bool {
    return isCursorInsideFmtStringHoleDepth(fmt_lexeme, rel_cursor, 0);
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_lsp_framing_json_security_caps_surrogates_uri_codec_and_lifecycle" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Cross-platform Windows, POSIX, and `.cxtree` URI decoding:
    {
        const win_upper = try decodeFileUriToNormalizedPath(allocator, "file:///D:/GitHub/corex/src/main.cx");
        defer allocator.free(win_upper);
        try std.testing.expectEqualStrings("d:/GitHub/corex/src/main.cx", win_upper);

        const win_pct = try decodeFileUriToNormalizedPath(allocator, "file:///d%3A/my%20proj/lib.cx");
        defer allocator.free(win_pct);
        try std.testing.expectEqualStrings("d:/my proj/lib.cx", win_pct);

        const cxtree_uri = try decodeFileUriToNormalizedPath(allocator, "file:///cx/http@1.2.0/src/root.cx");
        defer allocator.free(cxtree_uri);
        try std.testing.expectEqualStrings("/cx/http@1.2.0/src/root.cx", cxtree_uri);
    }

    // [2] Surrogate-pair decoding (`\uD800\uDF48` -> `\u{10348}`), lone-surrogate rejection & depth cap:
    {
        var arena = BumpArena.init(allocator);
        defer arena.deinit();

        const ok_val = try parseJsonPayload(arena.asAllocator(), "{\"text\":\"\\uD800\\uDF48\"}");
        try std.testing.expectEqualStrings("𐍈", ok_val.getStringField("text").?);

        try std.testing.expectError(
            error.InvalidJsonSyntax,
            parseJsonPayload(arena.asAllocator(), "{\"bad\":\"\\uD800\"}"),
        );
        try std.testing.expectError(
            error.InvalidJsonSyntax,
            parseJsonPayload(arena.asAllocator(), "{\"bad\":\"\\uDC00\"}"),
        );

        var deep_json: [140]u8 = undefined;
        @memset(deep_json[0..70], '[');
        @memset(deep_json[70..140], ']');
        try std.testing.expectError(
            error.MaxDepthExceeded,
            parseJsonPayload(arena.asAllocator(), &deep_json),
        );
    }

    // [3] Oversized header (`-32700`), oversized Content-Length (`-32600`), and `-32002` before `initialize`:
    {
        var inbound: std.ArrayListUnmanaged(u8) = .empty;
        defer inbound.deinit(allocator);

        // Request before `initialize` -> `-32002`:
        try appendTestLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"textDocument/hover\",\"params\":{}}",
        );
        // Oversized Content-Length (`16 MiB + 1` with 0 body bytes at EOF -> `-32600` without allocating 16 MiB!):
        const huge_hdr = try std.fmt.allocPrint(
            allocator,
            "Content-Length: {d}\r\n\r\n",
            .{MAX_LSP_CONTENT_LENGTH + 1},
        );
        defer allocator.free(huge_hdr);
        try inbound.appendSlice(allocator, huge_hdr);

        var fixed_reader = std.Io.Reader.fixed(inbound.items);
        var out_alloc = std.Io.Writer.Allocating.init(allocator);
        defer out_alloc.deinit();

        const exit_status = try runServerStream(
            allocator,
            io,
            null,
            &fixed_reader,
            &out_alloc.writer,
            null,
            .{},
        );
        try std.testing.expectEqual(@as(u8, 0), exit_status);

        const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
        defer allocator.free(frames);
        try std.testing.expectEqual(@as(usize, 2), frames.len);
        try std.testing.expect(std.mem.indexOf(u8, frames[0], "-32002") != null);
        try std.testing.expect(std.mem.indexOf(u8, frames[1], "-32600") != null);
    }
}

test "test_lsp_utf8_vs_utf16_did_change_and_multi_change_coalescing" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // Non-BMP Gothic letter `\u{10348}` (`𐍈`) spans 4 UTF-8 bytes vs 2 UTF-16 code units;
    // compare `utf-16` (`"𐍈"` = cols `13..15`) against negotiated `utf-8` across multi-change batches:
    for ([_]bool{ false, true }) |is_utf8_preferred| {
        var inbound: std.ArrayListUnmanaged(u8) = .empty;
        defer inbound.deinit(allocator);

        const init_json = if (is_utf8_preferred)
            "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
                "\"general\":{\"positionEncodings\":[\"utf-8\",\"utf-16\"]},\"textDocument\":{\"diagnostic\":{}}}}}"
        else
            "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
                "\"general\":{\"positionEncodings\":[\"utf-16\"]},\"textDocument\":{\"diagnostic\":{}}}}}";
        try appendTestLspFrame(allocator, &inbound, init_json);

        try appendTestLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{" ++
                "\"uri\":\"file:///D%3A/virt/enc.cx\",\"languageId\":\"corex\",\"version\":1," ++
                "\"text\":\"pub fn check() -> i32 {\\n    let _label = \\\"𐍈\\\"; let val = 10;\\n    1000 + val * 2\\n}\\n\"}}}",
        );

        // Replace `10` with `42` on line 1 (`"    let _label = \"𐍈\"; let val = "` = 35 UTF-8 cols vs 33 UTF-16 cols):
        const start_col: u32 = if (is_utf8_preferred) 35 else 33;
        const change_json = try std.fmt.allocPrint(
            allocator,
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{" ++
                "\"textDocument\":{{\"uri\":\"file:///D%3A/virt/enc.cx\",\"version\":2}}," ++
                "\"contentChanges\":[{{\"range\":{{\"start\":{{\"line\":1,\"character\":{d}}}," ++
                "\"end\":{{\"line\":1,\"character\":{d}}}}},\"text\":\"42\"}}," ++
                "{{\"range\":{{\"start\":{{\"line\":2,\"character\":11}}," ++
                "\"end\":{{\"line\":2,\"character\":14}}}},\"text\":\"val\"}}]}}}}",
            .{ start_col, start_col + 2 },
        );
        defer allocator.free(change_json);
        try appendTestLspFrame(allocator, &inbound, change_json);

        try appendTestLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/diagnostic\"," ++
                "\"params\":{\"textDocument\":{\"uri\":\"file:///D%3A/virt/enc.cx\"}}}",
        );
        try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"shutdown\",\"params\":null}");
        try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

        var fixed_reader = std.Io.Reader.fixed(inbound.items);
        var out_alloc = std.Io.Writer.Allocating.init(allocator);
        defer out_alloc.deinit();

        const code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
        try std.testing.expectEqual(@as(u8, 0), code);

        const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
        defer allocator.free(frames);
        try std.testing.expect(frames.len >= 3);
        const expected_enc = if (is_utf8_preferred) "\"positionEncoding\":\"utf-8\"" else "\"positionEncoding\":\"utf-16\"";
        try std.testing.expect(std.mem.indexOf(u8, frames[0], expected_enc) != null);
        // Clean pull diagnostic with zero syntax/type errors after UTF-8 / UTF-16 multi-change edit:
        try std.testing.expect(std.mem.indexOf(u8, frames[1], "\"items\":[]") != null);
    }
}

test "test_lsp_pipelined_cancel_request_and_semantic_tokens_lru_cache" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Dual-bounded `SemanticTokensCache` $O(1)$ entry-count and byte-size LRU eviction:
    {
        var cache = try SemanticTokensCache.initWithLimits(allocator, 2, 48);
        defer cache.deinit();

        const id_one = cache.allocNextResultId();
        const id_two = cache.allocNextResultId();
        const id_three = cache.allocNextResultId();

        try cache.putCloned(FileId.fromInt(1), id_one, &.{ 0, 0, 3, 1, 0 });
        try cache.putCloned(FileId.fromInt(2), id_two, &.{ 1, 0, 4, 2, 0 });
        // Touch FileId(1) so FileId(2) becomes LRU victim:
        try std.testing.expect(cache.getMatchingResult(FileId.fromInt(1), &id_one) != null);

        // Insert `FileId(3)`; entry cap `2` evicts `FileId(2)`, preserving MRU `FileId(1)`:
        try cache.putCloned(FileId.fromInt(3), id_three, &.{ 2, 0, 5, 3, 0 });
        try std.testing.expect(cache.getMatchingResult(FileId.fromInt(2), &id_two) == null);
        try std.testing.expect(cache.getMatchingResult(FileId.fromInt(1), &id_one) != null);
        try std.testing.expect(cache.getMatchingResult(FileId.fromInt(3), &id_three) != null);

        // Byte-budget eviction (`32` bytes holds one `20`-byte slice, evicting LRU on the second):
        var byte_cache = try SemanticTokensCache.initWithLimits(allocator, 8, 32);
        defer byte_cache.deinit();
        const bid_one = byte_cache.allocNextResultId();
        const bid_two = byte_cache.allocNextResultId();
        try byte_cache.putCloned(FileId.fromInt(10), bid_one, &.{ 0, 0, 3, 1, 0 });
        try byte_cache.putCloned(FileId.fromInt(11), bid_two, &.{ 1, 0, 4, 2, 0 });
        try std.testing.expect(byte_cache.getMatchingResult(FileId.fromInt(10), &bid_one) == null);
        try std.testing.expect(byte_cache.getMatchingResult(FileId.fromInt(11), &bid_two) != null);
    }

    // [2] Buffered pipelined `[Request #7][$/cancelRequest #7]` deterministically responds `-32800`:
    {
        var inbound: std.ArrayListUnmanaged(u8) = .empty;
        defer inbound.deinit(allocator);

        try appendTestLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":" ++
                "{\"capabilities\":{\"textDocument\":{\"diagnostic\":{}}}}}",
        );

        // Pipelined batch in buffer (`[Request #7][$/cancelRequest #7][shutdown #8][exit]`):
        try appendTestLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"workspace/symbol\",\"params\":{\"query\":\"foo\"}}",
        );
        try appendTestLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"method\":\"$/cancelRequest\",\"params\":{\"id\":7}}",
        );
        try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"shutdown\",\"params\":null}");
        try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

        var fixed_reader = std.Io.Reader.fixed(inbound.items);
        var out_alloc = std.Io.Writer.Allocating.init(allocator);
        defer out_alloc.deinit();

        const code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
        try std.testing.expectEqual(@as(u8, 0), code);

        const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
        defer allocator.free(frames);
        var has_seen_canceled_7 = false;
        for (frames) |frame_json| {
            if (std.mem.indexOf(u8, frame_json, "\"id\":7") != null and
                std.mem.indexOf(u8, frame_json, "-32800") != null)
            {
                has_seen_canceled_7 = true;
            }
        }
        try std.testing.expect(has_seen_canceled_7);
    }
}

test "test_lsp_hover_dr17_bullets_doc_trivia_and_dot_completion" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
            "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
    );

    const sample_cx =
        "pub const PREV_ITEM: i32 = 1; /| trailing comment on previous item\n" ++
        "/| Computes doubled coordinate sum.\n" ++
        "pub fn sum_point(pt: Point) -> i32 {\n" ++
        "    return pt.x_val + pt.y_val;\n" ++
        "}\n" ++
        "pub struct Point {\n" ++
        "    pub x_val: i32,\n" ++
        "    pub y_val: i32,\n" ++
        "}\n" ++
        "pub fn complete_me(pt: Point) -> i32 {\n" ++
        "    return pt.\n" ++
        "}\n";

    var open_msg_buf = std.Io.Writer.Allocating.init(allocator);
    defer open_msg_buf.deinit();
    try open_msg_buf.writer.writeAll(
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///virt/hover.cx\",\"languageId\":\"corex\",\"version\":1,\"text\":",
    );
    try writeJsonString(&open_msg_buf.writer, sample_cx);
    try open_msg_buf.writer.writeAll("}}}");
    try appendTestLspFrame(allocator, &inbound, open_msg_buf.written());

    // Hover on `sum_point` (line 2, col 8):
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":" ++
            "{\"textDocument\":{\"uri\":\"file:///virt/hover.cx\"},\"position\":{\"line\":2,\"character\":8}}}",
    );
    // Dot-completion right after `pt.` (line 10, col 14):
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/completion\",\"params\":" ++
            "{\"textDocument\":{\"uri\":\"file:///virt/hover.cx\"},\"position\":{\"line\":10,\"character\":14}}}",
    );
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"shutdown\",\"params\":null}");
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var fixed_reader = std.Io.Reader.fixed(inbound.items);
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();

    const code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
    try std.testing.expectEqual(@as(u8, 0), code);

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expect(frames.len >= 4);

    const hover_resp = frames[1];
    try std.testing.expect(std.mem.indexOf(u8, hover_resp, "fn sum_point") != null);
    try std.testing.expect(std.mem.indexOf(u8, hover_resp, "Computes doubled coordinate sum.") != null);
    try std.testing.expect(std.mem.indexOf(u8, hover_resp, "`@no_alloc`") != null);
    try std.testing.expect(std.mem.indexOf(u8, hover_resp, "**caps:** none (pure)") != null);
    try std.testing.expect(std.mem.indexOf(u8, hover_resp, "**stack:**") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, hover_resp, "Computes doubled coordinate sum.").? <
            std.mem.indexOf(u8, hover_resp, "**stack:**").?,
    );
    // Trailing comment on `PREV_ITEM` line must NOT bleed into `sum_point`'s hover:
    try std.testing.expect(std.mem.indexOf(u8, hover_resp, "trailing comment on previous item") == null);

    const comp_resp = frames[2];
    try std.testing.expect(std.mem.indexOf(u8, comp_resp, "\"label\":\"x_val\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, comp_resp, "\"label\":\"y_val\"") != null);
}

test "test_lsp_shorthand_init_and_se15_pattern_rename_plus_dr03_and_collision_hygiene" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
            "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
    );

    const rename_cx =
        "pub struct Point {\n" ++
        "    pub x: i32,\n" ++
        "    pub y: i32,\n" ++
        "}\n" ++
        "pub fn build_and_unpack(val: i32) -> i32 {\n" ++
        "    let x = val;\n" ++
        "    let pt = Point { x, y: 2 };\n" ++
        "    let Point { var x, y: other_y } = pt;\n" ++
        "    x = x + other_y;\n" ++
        "    return x;\n" ++
        "}\n";

    var open_buf = std.Io.Writer.Allocating.init(allocator);
    defer open_buf.deinit();
    try open_buf.writer.writeAll(
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///D%3A/proj/shorthand.cx\",\"languageId\":\"corex\",\"version\":1,\"text\":",
    );
    try writeJsonString(&open_buf.writer, rename_cx);
    try open_buf.writer.writeAll("}}}");
    try appendTestLspFrame(allocator, &inbound, open_buf.written());

    // [1] Rename local `let x` (line 5, col 8) -> `coord_x`; `Point { x, … }` expands to `x: coord_x`:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/rename\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///D%3A/proj/shorthand.cx\"},\"position\":{\"line\":5,\"character\":8},\"newName\":\"coord_x\"}}",
    );
    // [2] Rename `SE-15` pattern binding `var x` (line 7, col 20) -> `mut_x`; `Point { var x, … }` -> `x: var mut_x`:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/rename\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///D%3A/proj/shorthand.cx\"},\"position\":{\"line\":7,\"character\":20},\"newName\":\"mut_x\"}}",
    );
    // [3] Rename struct field `pub x` (line 1, col 8) -> `x_pos`; expand `x_pos: x` and `x_pos: var x`:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/rename\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///D%3A/proj/shorthand.cx\"},\"position\":{\"line\":1,\"character\":8},\"newName\":\"x_pos\"}}",
    );
    // [4] Invalid `DR-03` casing on struct field (`PascalCase` instead of `snake_case`) -> `-32602`:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/rename\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///D%3A/proj/shorthand.cx\"},\"position\":{\"line\":1,\"character\":8},\"newName\":\"BadField\"}}",
    );
    // [5] Sibling collision `E0408` renaming field `x` -> existing field `y` -> `-32803`:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"textDocument/rename\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///D%3A/proj/shorthand.cx\"},\"position\":{\"line\":1,\"character\":8},\"newName\":\"y\"}}",
    );
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"shutdown\",\"params\":null}");
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var fixed_reader = std.Io.Reader.fixed(inbound.items);
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();

    const code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
    try std.testing.expectEqual(@as(u8, 0), code);

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expect(frames.len >= 6);

    // Exact client URI `"file:///D%3A/proj/shorthand.cx"` echoed in `WorkspaceEdit.changes`:
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "file:///D%3A/proj/shorthand.cx") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "\"newText\":\"x: coord_x\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[2], "\"newText\":\"x: var mut_x\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[3], "\"newText\":\"x_pos: x\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[3], "\"newText\":\"x_pos: var x\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "-32602") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[5], "-32803") != null);
}

test "test_lsp_redteam_oversized_content_length_overflow_and_halt" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] `extractHeaderContentLength` distinguishes `.ok`, `.overflow` (`> usize.max`), and `.invalid`:
    try std.testing.expect(extractHeaderContentLength("Content-Length: 42") == .ok);
    try std.testing.expectEqual(
        @as(usize, 42),
        extractHeaderContentLength("Content-Length: 42").ok,
    );
    try std.testing.expect(
        extractHeaderContentLength("Content-Length: 99999999999999999999999999999") == .overflow,
    );
    try std.testing.expect(extractHeaderContentLength("Content-Length: abc") == .invalid);

    // [2] `extractTestOutboundPayloads` must not overflow `usize` on `usize.max` `Content-Length`:
    {
        const empty_payloads = try extractTestOutboundPayloads(
            allocator,
            "Content-Length: 18446744073709551615\r\n\r\nx",
        );
        defer allocator.free(empty_payloads);
        try std.testing.expectEqual(@as(usize, 0), empty_payloads.len);
    }

    // [3] Buffered `tryExtractCompleteBufferedFrame` with `usize.max` must NOT overflow-panic and must halt stream:
    {
        var inbound: std.ArrayListUnmanaged(u8) = .empty;
        defer inbound.deinit(allocator);

        try appendTestLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"textDocument/hover\",\"params\":{}}",
        );
        try inbound.appendSlice(allocator, "Content-Length: 18446744073709551615\r\n\r\nx");
        try appendTestLspFrame(
            allocator,
            &inbound,
            "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":{}}",
        );

        var fixed_reader = std.Io.Reader.fixed(inbound.items);
        var out_alloc = std.Io.Writer.Allocating.init(allocator);
        defer out_alloc.deinit();

        const exit_code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
        try std.testing.expectEqual(@as(u8, 0), exit_code);

        const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
        defer allocator.free(frames);
        try std.testing.expectEqual(@as(usize, 2), frames.len);
        try std.testing.expect(std.mem.indexOf(u8, frames[0], "-32002") != null);
        try std.testing.expect(std.mem.indexOf(u8, frames[1], "-32600") != null);
    }

    // [4] `readSingleInboundFrame` with `> 20`-digit `Content-Length` emits `-32600` (not `-32700`) and halts:
    {
        const overflow_wire =
            "Content-Length: 99999999999999999999999999999\r\n\r\nx" ++
            "Content-Length: 69\r\n\r\n{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/hover\",\"params\":{}}";
        var fixed_reader = std.Io.Reader.fixed(overflow_wire);
        var out_alloc = std.Io.Writer.Allocating.init(allocator);
        defer out_alloc.deinit();

        const exit_code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
        try std.testing.expectEqual(@as(u8, 0), exit_code);

        const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
        defer allocator.free(frames);
        try std.testing.expectEqual(@as(usize, 1), frames.len);
        try std.testing.expect(std.mem.indexOf(u8, frames[0], "-32600") != null);
    }
}

test "test_lsp_redteam_257_overlay_lru_eviction_formatting_and_did_change" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Direct `fmt_engine` out-of-bounds source slice guard when `source` is shorter than token offsets:
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        const guard_fid = FileId.fromInt(1);
        _ = try db.setInput(guard_fid, "   pub fn guard_fn() -> i32 { 1 }\n", .low);
        const parsed_art = try db.parseCst(guard_fid);
        var fmt_res = try fmt_engine.formatTokensAndCst(
            allocator,
            "",
            &parsed_art.token_buffer,
            &parsed_art.cst_arena,
            .{},
        );
        defer fmt_res.deinit(allocator);
    }

    // [2] Open 257 overlays (`0..256`) to LRU-evict `evict_0` and `evict_1`, then run `formatting` & `didChange`:
    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
            "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
    );

    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{" ++
            "\"uri\":\"file:///virt/evict_0.cx\",\"languageId\":\"corex\",\"version\":1," ++
            "\"text\":\"   pub fn   first_fn ( ) -> i32 { 7 }\\n\"}}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{" ++
            "\"uri\":\"file:///virt/evict_1.cx\",\"languageId\":\"corex\",\"version\":1," ++
            "\"text\":\"pub fn second_fn(seed: i32) -> i32 {\\n    seed + 7\\n}\\n\"}}}",
    );

    var file_idx: usize = 2;
    while (file_idx <= vfs_sourcemap.MAX_OPEN_OVERLAYS) : (file_idx += 1) {
        const extra_open = try std.fmt.allocPrint(
            allocator,
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{" ++
                "\"uri\":\"file:///virt/evict_{d}.cx\",\"languageId\":\"corex\",\"version\":1," ++
                "\"text\":\"pub fn pad_{d}() -> i32 {{ return 0; }}\\n\"}}}}}}",
            .{ file_idx, file_idx },
        );
        defer allocator.free(extra_open);
        try appendTestLspFrame(allocator, &inbound, extra_open);
    }

    // `evict_0.cx` is now LRU-evicted from `OverlayCache`; `formatting` re-hydrates it (evicting `evict_1.cx`):
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/formatting\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/evict_0.cx\"},\"options\":{\"tabSize\":4,\"insertSpaces\":true}}}",
    );

    // `evict_1.cx` is now LRU-evicted; ranged `didChange` replaces `7` with `99` on line 1 col 11..12:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/evict_1.cx\",\"version\":2}," ++
            "\"contentChanges\":[{\"range\":{\"start\":{\"line\":1,\"character\":11}," ++
            "\"end\":{\"line\":1,\"character\":12}},\"text\":\"99\"}]}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/diagnostic\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/evict_1.cx\"}}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/formatting\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/evict_1.cx\"},\"options\":{\"tabSize\":4,\"insertSpaces\":true}}}",
    );
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"shutdown\",\"params\":null}");
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var fixed_reader = std.Io.Reader.fixed(inbound.items);
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();

    const exit_code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
    try std.testing.expectEqual(@as(u8, 0), exit_code);

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expect(frames.len >= 5);
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "pub fn first_fn() -> i32") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[2], "\"items\":[]") != null);
    // `evict_1.cx` after splicing `"99"` is already canonically formatted (`"result":[]`):
    try std.testing.expect(std.mem.indexOf(u8, frames[3], "\"result\":[]") != null);
}

test "test_lsp_redteam_early_cutoff_shrunk_fn_stale_cst_references_rename_hover" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
            "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
    );

    const cutoff_src =
        "pub fn shrink_me() -> i32 {\n" ++
        "    let alpha = 10;\n" ++
        "    let beta = 20;\n" ++
        "    let gamma = 30;\n" ++
        "    let delta = 40;\n" ++
        "    return alpha + beta + gamma + delta;\n" ++
        "}\n" ++
        "pub mod sub_ns {\n" ++
        "    pub fn target_op() -> i32 {\n" ++
        "        return 5;\n" ++
        "    }\n" ++
        "}\n" ++
        "use sub_ns.{target_op as op_alias};\n" ++
        "/| Doc on trailing struct after shrink.\n" ++
        "pub struct AfterStruct {\n" ++
        "    pub val: i32,\n" ++
        "}\n" ++
        "pub mod inline_after {\n" ++
        "    pub fn call_it() -> i32 {\n" ++
        "        return 1;\n" ++
        "    }\n" ++
        "}\n" ++
        "pub fn use_site() -> i32 {\n" ++
        "    return op_alias();\n" ++
        "}\n";

    var open_buf = std.Io.Writer.Allocating.init(allocator);
    defer open_buf.deinit();
    try open_buf.writer.writeAll(
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///virt/cutoff.cx\",\"languageId\":\"corex\",\"version\":1,\"text\":",
    );
    try writeJsonString(&open_buf.writer, cutoff_src);
    try open_buf.writer.writeAll("}}}");
    try appendTestLspFrame(allocator, &inbound, open_buf.written());

    // Populate initial Pass-1/Pass-2 symbols before shrinking `shrink_me`:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/references\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/cutoff.cx\"}," ++
            "\"position\":{\"line\":8,\"character\":11},\"context\":{\"includeDeclaration\":true}}}",
    );

    // Shrink `shrink_me` body (`lines 1..6` -> `"    return 1;\n"`), triggering body-only Early Cutoff:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/cutoff.cx\",\"version\":2}," ++
            "\"contentChanges\":[{\"range\":{\"start\":{\"line\":1,\"character\":0}," ++
            "\"end\":{\"line\":6,\"character\":0}},\"text\":\"    return 1;\\n\"}]}}",
    );

    // [1] `references` on `target_op` (now line 4, col 11) must locate `use sub_ns.{target_op as op_alias}` on line 8:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/references\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/cutoff.cx\"}," ++
            "\"position\":{\"line\":4,\"character\":11},\"context\":{\"includeDeclaration\":true}}}",
    );
    // [2] `hover` on `AfterStruct` (now line 10, col 11) must extract doc comment via live `ItemTree`:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/cutoff.cx\"},\"position\":{\"line\":10,\"character\":11}}}",
    );
    // [3] `rename` on inline `mod inline_after` (now line 13, col 8) must resolve live `ItemTree` AST node:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/rename\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/cutoff.cx\"}," ++
            "\"position\":{\"line\":13,\"character\":8},\"newName\":\"renamed_inline\"}}",
    );
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"shutdown\",\"params\":null}");
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var fixed_reader = std.Io.Reader.fixed(inbound.items);
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();

    const exit_code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
    try std.testing.expectEqual(@as(u8, 0), exit_code);

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expect(frames.len >= 6);
    try std.testing.expect(std.mem.indexOf(u8, frames[2], "\"line\":8,\"character\":12") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[3], "Doc on trailing struct after shrink.") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "\"newText\":\"renamed_inline\"") != null);
}

test "test_lsp_redteam_readonly_pkg_guards_and_non_empty_code_action_edits" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var session = try LspSession.init(allocator, io, null, null, .{});
    defer session.deinit();
    session.bindInternalPointers();
    session.state = .initialized;

    // Mount a `.std_core` file (`Durability.high`) and an external `PackageId >= 2` `.cxtree` file:
    const std_text = "   pub fn std_fn(flag: bool) -> bool { return !flag; }\n";
    const std_fid = try session.vfs.setEditorOverlay(io, "/cx/std/ro_core.cx", std_text, .std_core, false);
    _ = try session.db.setInput(std_fid, std_text, .high);
    try session.db.setFilePackageId(std_fid, .std_core);
    try session.db.setFilePath(std_fid, "/cx/std/ro_core.cx");
    try session.recordMountedFile(std_fid);

    const ext_pkg = PackageId.fromInt(2);
    const dep_text = "   pub fn dep_fn(flag: bool) -> bool { return !flag; }\n";
    const dep_fid = try session.vfs.setEditorOverlay(io, "/cx/dep@1.0.0/src/lib.cx", dep_text, ext_pkg, false);
    _ = try session.db.setInput(dep_fid, dep_text, .medium);
    try session.db.setFilePackageId(dep_fid, ext_pkg);
    try session.db.setFilePath(dep_fid, "/cx/dep@1.0.0/src/lib.cx");
    try session.recordMountedFile(dep_fid);

    // Mount a `.root` workspace file and attach a synthetic diagnostic whose fix targets ONLY `dep_fid`:
    const ws_text = "pub fn ws_fn() -> i32 {\n    return 1;\n}\n";
    const ws_fid = try session.vfs.setEditorOverlay(io, "d:/proj/ws_main.cx", ws_text, .root, true);
    try session.open_doc_versions.put(allocator, ws_fid.asInt(), 1);
    _ = try session.db.setInput(ws_fid, ws_text, .low);
    try session.db.setFilePath(ws_fid, "d:/proj/ws_main.cx");
    try session.recordMountedFile(ws_fid);
    _ = try session.db.parseCst(ws_fid);
    if (session.db.parsed_artifacts.getPtr(ws_fid.asInt())) |ws_parsed| {
        const sink_alloc = ws_parsed.diagnostics.arena.asAllocator();
        const repl_sym = try session.db.interner.intern("patched");
        const foreign_edits = try sink_alloc.alloc(diagnostic.TextEdit, 1);
        foreign_edits[0] = .{
            .file_id = dep_fid,
            .start_byte = 0,
            .end_byte = 3,
            .replacement_id = repl_sym,
        };
        const foreign_fixes = try sink_alloc.alloc(SuggestedFix, 1);
        foreign_fixes[0] = .{
            .message = "foreign edit only",
            .applicability = .machine_applicable,
            .priority = .syntax_canonicalization,
            .edits = foreign_edits,
        };
        _ = try ws_parsed.diagnostics.emit(.{
            .code = .w0402_unused_binding,
            .severity = .warning,
            .primary_span = Span.init(ws_fid, 0, 6),
            .message = "synthetic foreign-edit warning",
            .suggestions = foreign_fixes,
        });
    }

    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();
    var exit_opt: ?u8 = null;

    const requests = [_][]const u8{
        "{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"textDocument/formatting\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///cx/std/ro_core.cx\"},\"options\":{\"tabSize\":4,\"insertSpaces\":true}}}",
        "{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"textDocument/codeAction\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///cx/std/ro_core.cx\"}," ++
            "\"range\":{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":0,\"character\":50}}}}",
        "{\"jsonrpc\":\"2.0\",\"id\":12,\"method\":\"textDocument/formatting\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///cx/dep@1.0.0/src/lib.cx\"},\"options\":{\"tabSize\":4,\"insertSpaces\":true}}}",
        "{\"jsonrpc\":\"2.0\",\"id\":13,\"method\":\"textDocument/codeAction\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///cx/dep@1.0.0/src/lib.cx\"}," ++
            "\"range\":{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":0,\"character\":50}}}}",
        "{\"jsonrpc\":\"2.0\",\"id\":14,\"method\":\"textDocument/codeAction\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/proj/ws_main.cx\"}," ++
            "\"range\":{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":0,\"character\":10}}}}",
    };

    for (requests) |req_json| {
        session.turn_arena.resetRetainingCapacity();
        const turn_alloc = session.turn_arena.asAllocator();
        const parsed_msg = try parseJsonPayload(turn_alloc, req_json);
        const msg_id = try extractJsonRpcId(parsed_msg);
        const method_name = parsed_msg.getStringField("method").?;
        try dispatchSingleJsonMessage(
            &session,
            turn_alloc,
            parsed_msg,
            msg_id,
            method_name,
            &out_alloc.writer,
            &exit_opt,
        );
    }

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expectEqual(@as(usize, 5), frames.len);
    for (frames[0..4]) |resp_json| {
        try std.testing.expect(std.mem.indexOf(u8, resp_json, "\"result\":[]") != null);
    }
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "foreign edit only") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "/cx/dep") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "Suppress `unused-binding` with `@expect`") != null);
}

test "test_lsp_redteam_dr22_slice_ptr_methods_and_soa_private_field_visibility" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
            "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
    );

    const comp_src =
        "pub mod model {\n" ++
        "    @soa\n" ++
        "    pub struct Particle {\n" ++
        "        pub pub_pos: f32,\n" ++
        "        secret_mass: f32,\n" ++
        "    }\n" ++
        "}\n" ++
        "pub fn comp_shared_slice(shared_sl: &[i32]) {\n" ++
        "    shared_sl.\n" ++
        "}\n" ++
        "pub fn comp_mut_slice(mut_sl: &mut [i32]) {\n" ++
        "    mut_sl.\n" ++
        "}\n" ++
        "pub fn comp_str(text_val: str) {\n" ++
        "    text_val.\n" ++
        "}\n" ++
        "pub fn comp_soa(soa_pts: #soa [model.Particle]) {\n" ++
        "    soa_pts.\n" ++
        "}\n" ++
        "pub fn comp_immut_arr() {\n" ++
        "    let immut_arr: [i32; 2] = [1, 2];\n" ++
        "    immut_arr.\n" ++
        "}\n" ++
        "pub fn comp_mut_arr() {\n" ++
        "    var mut_arr: [i32; 2] = [3, 4];\n" ++
        "    mut_arr.\n" ++
        "}\n";

    var open_buf = std.Io.Writer.Allocating.init(allocator);
    defer open_buf.deinit();
    try open_buf.writer.writeAll(
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///virt/comp_dr22.cx\",\"languageId\":\"corex\",\"version\":1,\"text\":",
    );
    try writeJsonString(&open_buf.writer, comp_src);
    try open_buf.writer.writeAll("}}}");
    try appendTestLspFrame(allocator, &inbound, open_buf.written());

    const cursor_specs = [_]TestCursorSpec{
        .{ .req_id = 2, .line = 8, .col = 14 },
        .{ .req_id = 3, .line = 11, .col = 11 },
        .{ .req_id = 4, .line = 14, .col = 13 },
        .{ .req_id = 5, .line = 17, .col = 12 },
        .{ .req_id = 6, .line = 21, .col = 14 },
        .{ .req_id = 7, .line = 25, .col = 12 },
    };
    for (cursor_specs) |spec| {
        const comp_req = try std.fmt.allocPrint(
            allocator,
            "{{\"jsonrpc\":\"2.0\",\"id\":{d},\"method\":\"textDocument/completion\",\"params\":{{" ++
                "\"textDocument\":{{\"uri\":\"file:///virt/comp_dr22.cx\"}}," ++
                "\"position\":{{\"line\":{d},\"character\":{d}}}}}}}",
            .{ spec.req_id, spec.line, spec.col },
        );
        defer allocator.free(comp_req);
        try appendTestLspFrame(allocator, &inbound, comp_req);
    }
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"shutdown\",\"params\":null}");
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var fixed_reader = std.Io.Reader.fixed(inbound.items);
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();

    const exit_code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
    try std.testing.expectEqual(@as(u8, 0), exit_code);

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expect(frames.len >= 8);

    // `shared_sl: &[i32]` (`frames[1]`); Method `len` + `as_ptr`, no `as_mut_ptr`, no retired `ptr`:
    try std.testing.expect(
        std.mem.indexOf(u8, frames[1], "{\"label\":\"len\",\"kind\":2,\"detail\":\"fn(&self) -> usize\"}") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, frames[1], "{\"label\":\"as_ptr\",\"kind\":2,\"detail\":\"fn(&self) -> *i32\"}") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "\"label\":\"as_mut_ptr\"") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "\"label\":\"ptr\"") == null);

    // `mut_sl: &mut [i32]` (`frames[2]`); Method `len` + `as_ptr` + `as_mut_ptr`, no retired `ptr`:
    try std.testing.expect(
        std.mem.indexOf(u8, frames[2], "{\"label\":\"as_ptr\",\"kind\":2,\"detail\":\"fn(&self) -> *i32\"}") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, frames[2], "{\"label\":\"as_mut_ptr\",\"kind\":2,\"detail\":\"fn(&mut self) -> *mut i32\"}") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, frames[2], "\"label\":\"ptr\"") == null);

    // `text_val: str` (`frames[3]`); Method `len` + `as_ptr` (`*u8`), no `as_mut_ptr`, no retired `ptr`:
    try std.testing.expect(
        std.mem.indexOf(u8, frames[3], "{\"label\":\"len\",\"kind\":2,\"detail\":\"fn(&self) -> usize\"}") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, frames[3], "{\"label\":\"as_ptr\",\"kind\":2,\"detail\":\"fn(&self) -> *u8\"}") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, frames[3], "\"label\":\"as_mut_ptr\"") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[3], "\"label\":\"ptr\"") == null);

    // `soa_pts: #soa [model.Particle]` (`frames[4]`); `len` (`kind: 2`), `pub_pos` (`[f32]`), no private `secret_mass`:
    try std.testing.expect(
        std.mem.indexOf(u8, frames[4], "{\"label\":\"len\",\"kind\":2,\"detail\":\"fn(&self) -> usize\"}") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "\"label\":\"pub_pos\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "\"label\":\"secret_mass\"") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "\"label\":\"as_mut_ptr\"") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "\"label\":\"ptr\"") == null);

    // `let immut_arr` (`frames[5]`) vs `var mut_arr` (`frames[6]`):
    try std.testing.expect(std.mem.indexOf(u8, frames[5], "\"label\":\"as_ptr\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[5], "\"label\":\"as_mut_ptr\"") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[6], "\"label\":\"as_ptr\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[6], "\"label\":\"as_mut_ptr\"") != null);
}

test "test_lsp_redteam_rename_deleted_local_and_shifted_fn_shadowing_hazard" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
            "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
    );

    const hazard_v1 =
        "pub fn pad_fn() -> i32 {\n" ++
        "    return 1;\n" ++
        "}\n" ++
        "pub fn helper_fn() -> i32 {\n" ++
        "    return 9;\n" ++
        "}\n" ++
        "pub fn work_fn(taken_param: i32) -> i32 {\n" ++
        "    let ghost_local = 10;\n" ++
        "    let keep_local = 20;\n" ++
        "    let stay_shadow = 30;\n" ++
        "    return helper_fn() + keep_local + ghost_local + taken_param;\n" ++
        "}\n";

    var open_buf = std.Io.Writer.Allocating.init(allocator);
    defer open_buf.deinit();
    try open_buf.writer.writeAll(
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///virt/rename_hazard.cx\",\"languageId\":\"corex\",\"version\":1,\"text\":",
    );
    try writeJsonString(&open_buf.writer, hazard_v1);
    try open_buf.writer.writeAll("}}}");
    try appendTestLspFrame(allocator, &inbound, open_buf.written());

    // Force initial body typecheck so `ghost_local` enters the append-only `SymbolTable`:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/diagnostic\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/rename_hazard.cx\"}}}",
    );

    // Delete `ghost_local` from `work_fn`:
    const hazard_v2 =
        "pub fn pad_fn() -> i32 {\n" ++
        "    return 1;\n" ++
        "}\n" ++
        "pub fn helper_fn() -> i32 {\n" ++
        "    return 9;\n" ++
        "}\n" ++
        "pub fn work_fn(taken_param: i32) -> i32 {\n" ++
        "    let keep_local = 20;\n" ++
        "    let stay_shadow = 30;\n" ++
        "    return helper_fn() + keep_local + taken_param;\n" ++
        "}\n";
    var change1_buf = std.Io.Writer.Allocating.init(allocator);
    defer change1_buf.deinit();
    try change1_buf.writer.writeAll(
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/rename_hazard.cx\",\"version\":2}," ++
            "\"contentChanges\":[{\"text\":",
    );
    try writeJsonString(&change1_buf.writer, hazard_v2);
    try change1_buf.writer.writeAll("}]}}");
    try appendTestLspFrame(allocator, &inbound, change1_buf.written());

    // [1] Renaming `keep_local` -> deleted `ghost_local` (`id: 3`) and `helper_fn` -> `ghost_local` (`id: 4`) MUST succeed:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/rename\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/rename_hazard.cx\"}," ++
            "\"position\":{\"line\":7,\"character\":8},\"newName\":\"ghost_local\"}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/rename\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/rename_hazard.cx\"}," ++
            "\"position\":{\"line\":3,\"character\":7},\"newName\":\"ghost_local\"}}",
    );

    // [2] Expand `pad_fn` body by +6 lines so `work_fn` shifts by +240 bytes under Early Cutoff (unrebased `decl_span`s):
    const pad_expansion =
        "    let pad_a = 100000;\n" ++
        "    let pad_b = 200000;\n" ++
        "    let pad_c = 300000;\n" ++
        "    let pad_d = 400000;\n" ++
        "    let pad_e = 500000;\n" ++
        "    let pad_f = 600000;\n" ++
        "    return pad_a + pad_b + pad_c + pad_d + pad_e + pad_f;\n";
    var change2_buf = std.Io.Writer.Allocating.init(allocator);
    defer change2_buf.deinit();
    try change2_buf.writer.writeAll(
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/rename_hazard.cx\",\"version\":3}," ++
            "\"contentChanges\":[{\"range\":{\"start\":{\"line\":1,\"character\":0}," ++
            "\"end\":{\"line\":2,\"character\":0}},\"text\":",
    );
    try writeJsonString(&change2_buf.writer, pad_expansion);
    try change2_buf.writer.writeAll("}]}}");
    try appendTestLspFrame(allocator, &inbound, change2_buf.written());

    // Live shadowing hazards in shifted `work_fn` (`taken_param` via `target_scope`, `stay_shadow` via `node_symbols`) -> `-32803`:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/rename\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/rename_hazard.cx\"}," ++
            "\"position\":{\"line\":9,\"character\":7},\"newName\":\"taken_param\"}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"textDocument/rename\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/rename_hazard.cx\"}," ++
            "\"position\":{\"line\":9,\"character\":7},\"newName\":\"stay_shadow\"}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/rename\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/rename_hazard.cx\"}," ++
            "\"position\":{\"line\":13,\"character\":8},\"newName\":\"stay_shadow\"}}",
    );
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"shutdown\",\"params\":null}");
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var fixed_reader = std.Io.Reader.fixed(inbound.items);
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();

    const exit_code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
    try std.testing.expectEqual(@as(u8, 0), exit_code);

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expect(frames.len >= 8);
    try std.testing.expect(std.mem.indexOf(u8, frames[2], "\"newText\":\"ghost_local\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[3], "\"newText\":\"ghost_local\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "-32803") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[5], "-32803") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[6], "-32803") != null);
}

test "test_lsp_redteam_collect_file_diagnostics_hashmap_rehash_no_uaf" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var src_buf = std.Io.Writer.Allocating.init(allocator);
    defer src_buf.deinit();
    try src_buf.writer.writeAll("pub fn fn_0(flag: bool) -> bool {\n    let unused_0 = 1;\n    return !flag;\n}\n");
    var item_idx: usize = 1;
    while (item_idx < 16) : (item_idx += 1) {
        try src_buf.writer.print(
            "pub fn fn_{d}() -> i32 {{\n    let unused_{d} = {d};\n    return {d};\n}}\n",
            .{ item_idx, item_idx, item_idx, item_idx },
        );
    }
    var ct_idx: usize = 0;
    while (ct_idx < 12) : (ct_idx += 1) {
        try src_buf.writer.print("pub const CT_{d}: i32 = 1 / 0;\n", .{ct_idx});
    }

    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
            "\"general\":{\"positionEncodings\":[\"utf-8\"]}}}}",
    );

    var open_buf = std.Io.Writer.Allocating.init(allocator);
    defer open_buf.deinit();
    try open_buf.writer.writeAll(
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///virt/rehash_diags.cx\",\"languageId\":\"corex\",\"version\":1,\"text\":",
    );
    try writeJsonString(&open_buf.writer, src_buf.written());
    try open_buf.writer.writeAll("}}}");
    try appendTestLspFrame(allocator, &inbound, open_buf.written());

    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/diagnostic\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/rehash_diags.cx\"}}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/codeAction\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/rehash_diags.cx\"}," ++
            "\"range\":{\"start\":{\"line\":2,\"character\":0},\"end\":{\"line\":2,\"character\":20}}}}",
    );
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"shutdown\",\"params\":null}");
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var fixed_reader = std.Io.Reader.fixed(inbound.items);
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();

    const exit_code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
    try std.testing.expectEqual(@as(u8, 0), exit_code);

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expect(frames.len >= 5);
    // `frames[1]` (`publishDiagnostics`) & `frames[2]` (`textDocument/diagnostic`) survive all HashMap rehashes:
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "E0220") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "W0402") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "unused_0") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "unused_15") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[2], "unused_0") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[2], "unused_15") != null);
    // `frames[3]` (`codeAction`) emits the `E0220` retired-`!` -> `"not "` quickfix:
    try std.testing.expect(std.mem.indexOf(u8, frames[3], "\"newText\":\"not \"") != null);
}

test "test_lsp_hover_attrs_variants_semantic_tokens_inlay_and_internal_rename" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const sample_src =
        "/| Async poll status.\n" ++
        "pub enum Poll[T] {\n" ++
        "    /| Completed with output value.\n" ++
        "    Ready(T),\n" ++
        "    /| Still pending wakeup.\n" ++
        "    Pending,\n" ++
        "}\n" ++
        "@inline @no_alloc @no_panic\n" ++
        "pub fn check_poll(state: &Poll[u32], opt: u32?, ptr: *mut u32) -> bool {\n" ++
        "    let (prev_val, is_swapped) = unsafe { @atomic_cmpxchg(ptr, 0_u32, 1_u32, 4_u8, 4_u8) };\n" ++
        "    _ = prev_val;\n" ++
        "    _ = is_swapped;\n" ++
        "    let has_opt = match opt {\n" ++
        "        .Some(_) => true,\n" ++
        "        .None => false,\n" ++
        "    };\n" ++
        "    if not has_opt { return false; }\n" ++
        "    return match state {\n" ++
        "        .Ready(_) => true,\n" ++
        "        .Pending => false,\n" ++
        "    };\n" ++
        "}\n" ++
        "pub fn unannotated_helper(val: u32) -> u32 {\n" ++
        "    return val;\n" ++
        "}\n";

    var session = try LspSession.init(allocator, io, null, null, .{ .is_internal_core = true });
    defer session.deinit();
    session.bindInternalPointers();
    session.state = .initialized;
    session.position_encoding = .utf8;

    const core_fid = try session.vfs.setEditorOverlay(io, "d:/corex/core/poll_demo.cx", sample_src, .std_core, true);
    try session.open_doc_versions.put(allocator, core_fid.asInt(), 1);
    _ = try session.db.setInput(core_fid, sample_src, .low);
    try session.db.setFilePackageId(core_fid, .std_core);
    try session.db.setFilePath(core_fid, "d:/corex/core/poll_demo.cx");
    try session.recordMountedFile(core_fid);

    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();
    var exit_opt: ?u8 = null;

    const requests = [_][]const u8{
        // [1] Hover on `@no_alloc` (line 7, col 10):
        "{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/poll_demo.cx\"},\"position\":{\"line\":7,\"character\":10}}}",
        // [2] Hover on `@atomic_cmpxchg` (line 9, col 45):
        "{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/poll_demo.cx\"},\"position\":{\"line\":9,\"character\":45}}}",
        // [3] Hover on `.Some` (line 13, col 10) & `.None` (line 14, col 10):
        "{\"jsonrpc\":\"2.0\",\"id\":12,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/poll_demo.cx\"},\"position\":{\"line\":13,\"character\":10}}}",
        "{\"jsonrpc\":\"2.0\",\"id\":13,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/poll_demo.cx\"},\"position\":{\"line\":14,\"character\":10}}}",
        // [4] Hover on `.Ready` (line 18, col 11):
        "{\"jsonrpc\":\"2.0\",\"id\":14,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/poll_demo.cx\"},\"position\":{\"line\":18,\"character\":11}}}",
        // [5] Inlay hints across entire file (zero `/* • pure` contract hints & zero `: (u32, bool)` tuple hints):
        "{\"jsonrpc\":\"2.0\",\"id\":15,\"method\":\"textDocument/inlayHint\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/poll_demo.cx\"}," ++
            "\"range\":{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":25,\"character\":0}}}}",
        // [6] Semantic tokens across entire file:
        "{\"jsonrpc\":\"2.0\",\"id\":16,\"method\":\"textDocument/semanticTokens/full\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/poll_demo.cx\"}}}",
        // [7] `prepareRename` & `rename` on `.Ready` (line 18, col 11 -> `Completed`) inside `--internal-core` `.std_core`:
        "{\"jsonrpc\":\"2.0\",\"id\":17,\"method\":\"textDocument/prepareRename\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/poll_demo.cx\"},\"position\":{\"line\":18,\"character\":11}}}",
        "{\"jsonrpc\":\"2.0\",\"id\":18,\"method\":\"textDocument/rename\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/poll_demo.cx\"}," ++
            "\"position\":{\"line\":18,\"character\":11},\"newName\":\"Completed\"}}",
    };

    for (requests) |req_json| {
        session.turn_arena.resetRetainingCapacity();
        const turn_alloc = session.turn_arena.asAllocator();
        const parsed_msg = try parseJsonPayload(turn_alloc, req_json);
        const msg_id = try extractJsonRpcId(parsed_msg);
        const method_name = parsed_msg.getStringField("method").?;
        try dispatchSingleJsonMessage(
            &session,
            turn_alloc,
            parsed_msg,
            msg_id,
            method_name,
            &out_alloc.writer,
            &exit_opt,
        );
    }

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expectEqual(@as(usize, 9), frames.len);

    // [1] `@no_alloc` & `@atomic_cmpxchg` hover cards:
    try std.testing.expect(std.mem.indexOf(u8, frames[0], "@no_alloc") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[0], "zero transitive heap allocations") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "@atomic_cmpxchg") != null);

    // [2] `.Some` & `.None` concrete `Option[u32]` hover cards:
    try std.testing.expect(std.mem.indexOf(u8, frames[2], "Option[u32].Some(u32)") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[3], "Option[u32].None") != null);

    // [3] `.Ready` user enum variant hover card + `///` variant doc comment:
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "Poll[u32].Ready") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "Completed with output value.") != null);

    // [4] Inlay hints contain zero `/* • pure` contract clutter and zero `: (u32, bool)` tuple-destructuring bug:
    try std.testing.expect(std.mem.indexOf(u8, frames[5], "pure (") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[5], "@no_alloc-eligible") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[5], ": (u32, bool)") == null);

    // [5] Semantic tokens: verify `.` is never `enumMember` (`length: 1, type: 9`) and `true`/`false` are not `keyword`:
    const sem_tokens = try computeSemanticTokensData(&session, session.turn_arena.asAllocator(), core_fid, null);
    var saw_some_enum_member = false;
    var saw_ready_enum_member = false;
    var cur_line: u32 = 0;
    var cur_col: u32 = 0;
    var idx: usize = 0;
    while (idx + 5 <= sem_tokens.len) : (idx += 5) {
        const d_line = sem_tokens[idx];
        const d_col = sem_tokens[idx + 1];
        const tok_len = sem_tokens[idx + 2];
        const tok_ty = sem_tokens[idx + 3];
        if (d_line > 0) {
            cur_line += d_line;
            cur_col = d_col;
        } else {
            cur_col += d_col;
        }
        // Line 13 (`        .Some(_) => true,`): col 8 is `.`, col 9 is `Some` (len 4), col 20 is `true` (len 4):
        if (cur_line == 13) {
            try std.testing.expect(cur_col != 8);
            if (cur_col == 9 and tok_len == 4 and tok_ty == SEM_TOK_ENUM_MEMBER) saw_some_enum_member = true;
            try std.testing.expect(!(cur_col == 20 and tok_ty == SEM_TOK_KEYWORD));
        }
        // Line 18 (`        .Ready(_) => true,`): col 8 is `.`, col 9 is `Ready` (len 5), col 21 is `true` (len 4):
        if (cur_line == 18) {
            try std.testing.expect(cur_col != 8);
            if (cur_col == 9 and tok_len == 5 and tok_ty == SEM_TOK_ENUM_MEMBER) saw_ready_enum_member = true;
            try std.testing.expect(!(cur_col == 21 and tok_ty == SEM_TOK_KEYWORD));
        }
    }
    try std.testing.expect(saw_some_enum_member);
    try std.testing.expect(saw_ready_enum_member);

    // [6] `prepareRename` & `rename` succeed in `--internal-core` `.std_core` and preserve `.` before `Ready`:
    try std.testing.expect(std.mem.indexOf(u8, frames[7], "\"placeholder\":\"Ready\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[8], "\"newText\":\"Completed\"") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, frames[8], "\"start\":{\"line\":18,\"character\":9},\"end\":{\"line\":18,\"character\":14}") != null,
    );
}

test "test_lsp_module_hover_file_docstring_and_coalesced_trivia_isolation" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var session = try LspSession.init(allocator, io, null, null, .{ .is_internal_core = true });
    defer session.deinit();
    session.bindInternalPointers();
    session.state = .initialized;
    session.position_encoding = .utf8;
    session.workspace_root_dir = try allocator.dupe(u8, "d:/corex");

    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();
    var exit_opt: ?u8 = null;

    // `core/async.cx`: > 15 leading trivia pieces (`TRIVIA_FLAG_COALESCED`) + section divider + `/|` on `Poll`:
    const async_src =
        "/# Structured Cooperative Async Concurrency (`core.async`)\n" ++
        "/#\n" ++
        "/# Defines stackless coroutine polling (`Poll[T]`), cancellation tokens,\n" ++
        "/# and bounded `16 KiB` inline task frames across all execution tiers.\n" ++
        "/#\n" ++
        "/# Paragraph three line one.\n" ++
        "/# Paragraph three line two.\n" ++
        "/# Paragraph three line three.\n" ++
        "/# Paragraph three line four.\n" ++
        "// ---------------------------------------- TYPES ----------------------------------------\n" ++
        "/| Cooperative step outcome returned when polling an asynchronous state machine.\n" ++
        "pub enum Poll[T] {\n" ++
        "    Ready(T),\n" ++
        "    Pending,\n" ++
        "}\n";

    // `core/bare.cx`: NO top-of-file `/#` docstring, starts with `/|` on its first item:
    const bare_src =
        "/| First item doc that must never leak onto `mod bare`.\n" ++
        "pub struct BareItem {\n" ++
        "    pub count: u32,\n" ++
        "}\n";

    const root_src =
        "/# Core Root Module Header (`core`)\n" ++
        "/| One-liner summary on `pub mod async;` in `root.cx`.\n" ++
        "pub mod async;\n" ++
        "/| One-liner summary on `pub mod bare;` in `root.cx`.\n" ++
        "pub mod bare;\n";

    const client_src =
        "use cx.async;\n" ++
        "pub fn check_poll(state: cx.async.Poll[u32]) -> bool {\n" ++
        "    return match state {\n" ++
        "        .Ready(_) => true,\n" ++
        "        .Pending => false,\n" ++
        "    };\n" ++
        "}\n";

    const root_fid = try session.vfs.setEditorOverlay(io, "d:/corex/core/root.cx", root_src, .std_core, true);
    const async_fid = try session.vfs.setEditorOverlay(io, "d:/corex/core/async.cx", async_src, .std_core, true);
    const bare_fid = try session.vfs.setEditorOverlay(io, "d:/corex/core/bare.cx", bare_src, .std_core, true);
    const client_fid = try session.vfs.setEditorOverlay(io, "d:/corex/src/app.cx", client_src, .root, true);

    for ([_]struct { fid: FileId, path: []const u8, src: []const u8, pkg: PackageId }{
        .{ .fid = root_fid, .path = "d:/corex/core/root.cx", .src = root_src, .pkg = .std_core },
        .{ .fid = async_fid, .path = "d:/corex/core/async.cx", .src = async_src, .pkg = .std_core },
        .{ .fid = bare_fid, .path = "d:/corex/core/bare.cx", .src = bare_src, .pkg = .std_core },
        .{ .fid = client_fid, .path = "d:/corex/src/app.cx", .src = client_src, .pkg = .root },
    }) |entry| {
        _ = try session.vfs.getLineIndex(entry.fid);
        _ = try session.db.setInput(entry.fid, entry.src, .low);
        try session.db.setFilePackageId(entry.fid, entry.pkg);
        try session.db.setFilePath(entry.fid, entry.path);
        try session.open_doc_versions.put(allocator, entry.fid.asInt(), 1);
        try session.recordMountedFile(entry.fid);
    }
    try session.db.bindExternalModule(root_fid, "async", async_fid);
    try session.db.bindExternalModule(root_fid, "bare", bare_fid);
    try session.db.registerRootModule("core", root_fid);
    try session.db.registerRootModule("cx", root_fid);
    _ = try session.db.resolveSignatures(root_fid);

    const requests = [_][]const u8{
        // [0] Hover `async` on `pub mod async;` in `core/root.cx` (line 2, col 9):
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/root.cx\"},\"position\":{\"line\":2,\"character\":9}}}",
        // [1] Hover `bare` on `pub mod bare;` in `core/root.cx` (line 4, col 9) -> file has no `//!`, so zero docs:
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/root.cx\"},\"position\":{\"line\":4,\"character\":9}}}",
        // [2] Hover `async` on `use cx.async;` in `src/app.cx` (line 0, col 9):
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/src/app.cx\"},\"position\":{\"line\":0,\"character\":9}}}",
        // [3] Hover `async` in `cx.async.Poll[u32]` in `src/app.cx` (line 1, col 29):
        "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/src/app.cx\"},\"position\":{\"line\":1,\"character\":29}}}",
        // [4] Hover `Poll` in `core/async.cx` (line 11, col 10) -> only `Poll`'s `///`, zero `//!` or `// ----`:
        "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///d:/corex/core/async.cx\"},\"position\":{\"line\":11,\"character\":10}}}",
    };

    for (requests) |req_json| {
        session.turn_arena.resetRetainingCapacity();
        const turn_alloc = session.turn_arena.asAllocator();
        const parsed_msg = try parseJsonPayload(turn_alloc, req_json);
        const msg_id = try extractJsonRpcId(parsed_msg);
        const method_name = parsed_msg.getStringField("method").?;
        try dispatchSingleJsonMessage(
            &session,
            turn_alloc,
            parsed_msg,
            msg_id,
            method_name,
            &out_alloc.writer,
            &exit_opt,
        );
    }

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expectEqual(@as(usize, 5), frames.len);

    // [0], [2], [3] `mod async` hovers all show `core/async.cx`'s multiline `//!` header, never `Poll`'s `///` or 1-liner:
    for ([_]usize{ 0, 2, 3 }) |frame_idx| {
        try std.testing.expect(std.mem.indexOf(u8, frames[frame_idx], "mod async") != null);
        try std.testing.expect(
            std.mem.indexOf(u8, frames[frame_idx], "Structured Cooperative Async Concurrency (`core.async`)") != null,
        );
        try std.testing.expect(std.mem.indexOf(u8, frames[frame_idx], "Paragraph three line four.") != null);
        try std.testing.expect(std.mem.indexOf(u8, frames[frame_idx], "One-liner summary") == null);
        try std.testing.expect(std.mem.indexOf(u8, frames[frame_idx], "Cooperative step outcome") == null);
    }

    // [1] `mod bare` hover shows `mod bare` with NO docstring (neither `root.cx` 1-liner nor `BareItem`'s `///`):
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "mod bare") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "---") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "First item doc") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[1], "One-liner summary") == null);

    // [4] `Poll` hover shows ONLY `Poll`'s outer `/|` docstring, with zero `/#` or `// ----` leakage:
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "pub enum Poll") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, frames[4], "Cooperative step outcome returned when polling") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "Structured Cooperative Async Concurrency") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "TYPES") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "/#") == null);
}

test "test_lsp_dr24_fmt_string_holes_doc_prefixes_and_repr_hover" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var inbound: std.ArrayListUnmanaged(u8) = .empty;
    defer inbound.deinit(allocator);

    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
            "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
    );

    const dr24_src =
        "/# Module Doc Header (`dr24_lsp`)\n" ++
        "/#   - Indented bullet preserved\n" ++
        "\n" ++
        "/| Cache-aligned coordinate pair.\n" ++
        "@repr(C, align: .CacheLine, zero_pad: true)\n" ++
        "pub struct Pair {\n" ++
        "    pub x_val: i32,\n" ++
        "    pub y_val: i32,\n" ++
        "}\n" ++
        "pub fn pad_top() -> i32 {\n" ++
        "    return 1;\n" ++
        "}\n" ++
        "/| Formats pair summary.\n" ++
        "pub fn describe_pair(pt: Pair, scale: i32) -> str {\n" ++
        "    let total = pt.x_val * scale;\n" ++
        "    return f\"pair({total=}, {pt.x_val:04})\";\n" ++
        "}\n" ++
        "pub fn dot_in_hole(pt: Pair) -> str {\n" ++
        "    return f\"val={pt.}\";\n" ++
        "}\n";

    var open_buf = std.Io.Writer.Allocating.init(allocator);
    defer open_buf.deinit();
    try open_buf.writer.writeAll(
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":" ++
            "{\"uri\":\"file:///virt/dr24_lsp.cx\",\"languageId\":\"corex\",\"version\":1,\"text\":",
    );
    try writeJsonString(&open_buf.writer, dr24_src);
    try open_buf.writer.writeAll("}}}");
    try appendTestLspFrame(allocator, &inbound, open_buf.written());

    // [1] Hover `@repr` (`line 4, col 2`) BEFORE Early Cutoff edit (populates initial side tables via `id: 3` too):
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"},\"position\":{\"line\":4,\"character\":2}}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"},\"position\":{\"line\":15,\"character\":20}}}",
    );

    // [2] Expand `pad_top` body (`line 10..11`) by +2 lines to trigger Early Cutoff (`rebaseWindow`) above `describe_pair`:
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\",\"version\":2}," ++
            "\"contentChanges\":[{\"range\":{\"start\":{\"line\":10,\"character\":0}," ++
            "\"end\":{\"line\":11,\"character\":0}}," ++
            "\"text\":\"    let alpha = 100;\\n    let beta = 200;\\n    return alpha + beta;\\n\"}]}}",
    );

    // [3] After Early Cutoff (+2 lines): hover `total` (`line 17, col 20`) vs `:04` (`line 17, col 38` -> `null`):
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"},\"position\":{\"line\":17,\"character\":20}}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/hover\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"},\"position\":{\"line\":17,\"character\":38}}}",
    );
    // [4] `definition` on `x_val` inside `{pt.x_val:04}` (`line 17, col 33` -> `line 6, col 8`):
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"textDocument/definition\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"},\"position\":{\"line\":17,\"character\":33}}}",
    );
    // [5] `references` on `total` inside `{total=}` (`line 17, col 20` -> `line 16` + `line 17`):
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/references\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"}," ++
            "\"position\":{\"line\":17,\"character\":20},\"context\":{\"includeDeclaration\":true}}}",
    );
    // [6] `prepareRename` & `rename` on `total` inside `{total=}` -> `sum_val` (preserves trailing `=`):
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"textDocument/prepareRename\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"},\"position\":{\"line\":17,\"character\":20}}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/rename\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"}," ++
            "\"position\":{\"line\":17,\"character\":20},\"newName\":\"sum_val\"}}",
    );
    // [7] Dot-completion inside `f"val={pt.}"` (`line 20, col 21`) vs outside hole (`line 20, col 15`) vs `@` attrs (`line 4, col 1`):
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"textDocument/completion\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"},\"position\":{\"line\":20,\"character\":21}}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"textDocument/completion\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"},\"position\":{\"line\":20,\"character\":15}}}",
    );
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":12,\"method\":\"textDocument/completion\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"},\"position\":{\"line\":4,\"character\":1}}}",
    );
    // [8] Semantic tokens full (`id: 13`):
    try appendTestLspFrame(
        allocator,
        &inbound,
        "{\"jsonrpc\":\"2.0\",\"id\":13,\"method\":\"textDocument/semanticTokens/full\",\"params\":{" ++
            "\"textDocument\":{\"uri\":\"file:///virt/dr24_lsp.cx\"}}}",
    );
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":14,\"method\":\"shutdown\",\"params\":null}");
    try appendTestLspFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

    var fixed_reader = std.Io.Reader.fixed(inbound.items);
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();

    const exit_code = try runServerStream(allocator, io, null, &fixed_reader, &out_alloc.writer, null, .{});
    try std.testing.expectEqual(@as(u8, 0), exit_code);

    const frames = try extractTestOutboundPayloads(allocator, out_alloc.written());
    defer allocator.free(frames);
    try std.testing.expect(frames.len >= 14);

    // `@repr` hover includes `.CacheLine` (`frames[1]`):
    try std.testing.expect(std.mem.indexOf(u8, frames[1], ".CacheLine") != null);
    // Hover on `total` inside `{total=}` before (`frames[2]`) and after Early Cutoff (`frames[3]`):
    try std.testing.expect(std.mem.indexOf(u8, frames[2], "let total: i32") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[3], "let total: i32") != null);
    // Hover on `:04` outside expression (`frames[4]`) returns `null`:
    try std.testing.expect(std.mem.indexOf(u8, frames[4], "\"result\":null") != null);
    // `definition` on `x_val` inside `{pt.x_val:04}` (`frames[5]`) jumps to `line 6, character 8`:
    try std.testing.expect(std.mem.indexOf(u8, frames[5], "\"line\":6,\"character\":8") != null);
    // `references` on `total` (`frames[6]`) hits `line 16` (`let total`) and `line 17, character 19..24` (`{total=}`):
    try std.testing.expect(std.mem.indexOf(u8, frames[6], "\"line\":16,\"character\":8") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, frames[6], "\"start\":{\"line\":17,\"character\":19},\"end\":{\"line\":17,\"character\":24}") != null,
    );
    // `prepareRename` (`frames[7]`) & `rename` (`frames[8]`) replace `19..24`, keeping trailing `=` at col 24:
    try std.testing.expect(std.mem.indexOf(u8, frames[7], "\"placeholder\":\"total\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[8], "\"newText\":\"sum_val\"") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, frames[8], "\"start\":{\"line\":17,\"character\":19},\"end\":{\"line\":17,\"character\":24}") != null,
    );
    // Dot-completion inside `f"val={pt.}"` (`frames[9]`) finds `x_val` & `y_val`; outside hole (`frames[10]`) is empty:
    try std.testing.expect(std.mem.indexOf(u8, frames[9], "\"label\":\"x_val\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[9], "\"label\":\"y_val\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[10], "\"items\":[]") != null);
    // `@` completion (`frames[11]`) offers `repr` & `link`, excluding retired `repr_c`, `cache_aligned`, `packed`, `link_name`:
    try std.testing.expect(std.mem.indexOf(u8, frames[11], "\"label\":\"repr\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[11], "\"label\":\"link\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, frames[11], "\"label\":\"repr_c\"") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[11], "\"label\":\"cache_aligned\"") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[11], "\"label\":\"packed\"") == null);
    try std.testing.expect(std.mem.indexOf(u8, frames[11], "\"label\":\"link_name\"") == null);
    // Semantic tokens (`frames[12]`) are non-empty:
    try std.testing.expect(std.mem.indexOf(u8, frames[12], "\"data\":[0,0,2,15,256") != null);
}
