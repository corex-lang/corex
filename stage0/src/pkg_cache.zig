//! Content-Addressable Global Package Cache, Bao Streaming & Cryptographic Proofs
//!
//! Implements `~/.corex/cache/blake3/{blobs,trees,cxi,staging,index,tlog,locks}` (`DR-11` §2),
//! `std.Io` advisory `gc.lock` coordination, atomic read-only staging commits, `CRLF`->`LF` source
//! normalization, standalone 7-round `BLAKE3` `.obao` Bao verified streaming, `Ed25519` + RFC 6962
//! transparency-log Merkle proofs, dual-bounded `BoundedMetadataLru`, and `vendor/` materialization.
//!
//! Enforces strict content integrity across every read and publish boundary (`E0015` on any digest,
//! Bao slice, signature, or Merkle proof mismatch) with zero unverified disk mutations.

const std = @import("std");
const builtin = @import("builtin");
const mem_foundation = @import("mem_foundation.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const diagnostic = @import("diag/diagnostic.zig");

const Span = mem_foundation.Span;
const BumpArena = mem_foundation.BumpArena;
const CxTreeHeader = vfs_sourcemap.CxTreeHeader;
const CxTreeEntry = vfs_sourcemap.CxTreeEntry;
const DiagnosticSink = diagnostic.DiagnosticSink;

// ---------------------------------------- TYPES ----------------------------------------

// ------------------- Locking & Vendor Tiers -------------------

/// Advisory lock mode used on `<cache>/blake3/locks/gc.lock` (`DR-11` §2.3).
pub const LockMode = enum(u8) {
    /// Concurrent reader lock acquired by `corex build`, `corex run`, `corex test`, and `corex lsp`.
    shared = 0,
    /// Exclusive writer lock acquired by `corex cache gc`.
    exclusive = 1,
};

/// Cross-platform RAII handle wrapping an `std.Io.File` advisory lock (or no-op when unsupported).
pub const AdvisoryFileLock = struct {
    /// Underlying lock file handle (`null` when advisory file locks are unsupported on the host).
    file: ?std.Io.File = null,
    /// `true` if the OS kernel holds an active advisory lock on `file`.
    is_locked: bool = false,

    /// Unlocks and closes the underlying lock file handle if open.
    pub fn release(self: *AdvisoryFileLock, io: std.Io) void {
        if (self.file) |opened_file| {
            if (self.is_locked) {
                opened_file.unlock(io);
            }
            opened_file.close(io);
        }
        self.* = .{};
    }
};

/// Filesystem cloning strategy selected when materializing a file into `vendor/`.
pub const VendorLinkTier = enum(u8) {
    /// Zero-copy copy-on-write filesystem extent clone (`FICLONE` on Linux).
    cow_reflink = 0,
    /// Read-only POSIX / NTFS directory hardlink (`std.Io.Dir.hardLink`).
    hardlink = 1,
    /// Verified streaming copy hardened to read-only permissions and atomically renamed.
    atomic_copy = 2,
};

/// Summary package descriptor passed to `materializeVendorDir` for `vendor/modules.toml` emission.
pub const VendorPackageRecord = struct {
    /// Canonical `kebab-case` package name.
    name: []const u8,
    /// Canonical SemVer version text (e.g., `"1.4.2"`).
    version: []const u8,
    /// Canonical lockfile source URI.
    source: []const u8,
    /// Expected 256-bit `.cxtree` digest (`tree_hash` in `corex.lock`).
    tree_blake3: [32]u8,
};

/// Telemetry counters returned by `materializeVendorDir`.
pub const VendorMaterializeStats = struct {
    /// Number of files materialized via CoW reflink (`FICLONE`).
    reflink_count: u32 = 0,
    /// Number of files materialized via read-only hardlinks.
    hardlink_count: u32 = 0,
    /// Number of files materialized via verified atomic read-only copies.
    copy_count: u32 = 0,
};

// ---------------- CxTree & Blob Ingest Records ----------------

/// Unpacked file descriptor fed into `computeCxTreeDigest` and `buildCxTreeBytes`.
pub const CxTreeInputEntry = struct {
    /// Normalized POSIX relative path inside the package (`/` separators, no leading `/`).
    rel_path: []const u8,
    /// File mode (`0x01` = regular file, `0x02` = executable file).
    file_mode: u16 = 0x01,
    /// Uncompressed normalized byte length of the file blob.
    file_size: u64,
    /// 256-bit `BLAKE3` content digest of the normalized file blob.
    file_blake3: [32]u8,
};

/// Normalized payload produced prior to hashing and storing a package file in `blobs/`.
pub const NormalizedIngestBlob = struct {
    /// Borrowed or arena-allocated byte slice ready for unkeyed `BLAKE3-256` hashing.
    bytes: []const u8,
    /// Unkeyed 256-bit `BLAKE3` content digest of `bytes`.
    blake3_digest: [32]u8,
    /// `true` if `CRLF` (`\r\n`) sequences were normalized to `LF` (`\n`).
    is_crlf_normalized: bool,
};

// -------------- Dual-Bounded Metadata LRU Cache ---------------

/// Logical artifact namespace partitioning `BoundedMetadataLru` entries.
pub const CacheKeyDomain = enum(u8) {
    /// Validated `.cxtree` binary package directory manifests (`0`).
    cxtree = 0,
    /// Sparse HTTP registry NDJSON metadata files (`1`).
    sparse_index = 1,
    /// Binary `.cxi` public-interface and capability summaries (`2`).
    cxi_summary = 2,
    /// RFC 6962 transparency-log Merkle tiles (`3`).
    tlog_tile = 3,
};

/// Exact 40-byte (`320`-bit, `0` padding) lookup key for `BoundedMetadataLru`.
pub const LruCacheKey = extern struct {
    /// 256-bit `BLAKE3` content or path digest.
    digest: [32]u8,
    /// Sub-cache domain discriminant.
    domain: CacheKeyDomain = .cxtree,
    /// Zeroed trailing bytes guaranteeing zero uninitialized padding for `AutoHashMap` hashing.
    reserved_pad: [7]u8 = @splat(0),
};

/// Intrusive doubly-linked slot inside `BoundedMetadataLru`.
const LruSlot = struct {
    /// Key occupying this slot when `is_occupied == true`.
    key: LruCacheKey,
    /// Owned payload byte buffer (`allocator.free` on eviction or `deinit`).
    payload: []u8,
    /// Previous (more-recently-used) slot index, or `LRU_SENTINEL` at `mru_head`.
    prev_slot: u32 = LRU_SENTINEL,
    /// Next (less-recently-used) slot index, or `LRU_SENTINEL` at `lru_tail`.
    next_slot: u32 = LRU_SENTINEL,
    /// `true` while this slot holds a live cache entry.
    is_occupied: bool = false,
};

/// Deterministic dual-bounded (`max_entries` AND `max_bytes`) intrusive LRU metadata cache.
pub const BoundedMetadataLru = struct {
    /// Backing heap allocator owning `entries`, `free_slots`, `key_to_slot`, and cached payloads.
    allocator: std.mem.Allocator,
    /// Contiguous slot pool indexed by `u32` handles.
    entries: std.ArrayListUnmanaged(LruSlot) = .empty,
    /// Reusable vacant slot indices popped in $O(1)$ on insertion.
    free_slots: std.ArrayListUnmanaged(u32) = .empty,
    /// $O(1)$ hash map from `40B` `LruCacheKey` to slot index.
    key_to_slot: std.AutoHashMapUnmanaged(LruCacheKey, u32) = .empty,
    /// Most-recently-used slot index (`LRU_SENTINEL` when empty).
    mru_head: u32 = LRU_SENTINEL,
    /// Least-recently-used slot index (`LRU_SENTINEL` when empty; first candidate for eviction).
    lru_tail: u32 = LRU_SENTINEL,
    /// Current number of live cached entries (`<= max_entries`).
    live_entries: u32 = 0,
    /// Current sum of live payload byte lengths (`<= max_bytes`).
    live_bytes: u64 = 0,
    /// Hard upper bound on simultaneous cached entry count.
    max_entries: u32 = DEFAULT_MAX_LRU_ENTRIES,
    /// Hard upper bound on total cached payload bytes.
    max_bytes: u64 = DEFAULT_MAX_LRU_BYTES,
    /// Total cache lookup hits observed.
    hit_count: u64 = 0,
    /// Total cache lookup misses observed.
    miss_count: u64 = 0,
    /// Total LRU evictions executed to uphold `(max_entries, max_bytes)` caps.
    eviction_count: u64 = 0,

    /// Initializes an empty `BoundedMetadataLru` governed by `max_entries` and `max_bytes`.
    pub fn init(allocator: std.mem.Allocator, max_entries: u32, max_bytes: u64) BoundedMetadataLru {
        return .{
            .allocator = allocator,
            .max_entries = max_entries,
            .max_bytes = max_bytes,
        };
    }

    /// Releases all cached payload buffers and internal hash/slot tables.
    pub fn deinit(self: *BoundedMetadataLru) void {
        for (self.entries.items) |slot| {
            if (slot.is_occupied) {
                self.allocator.free(slot.payload);
            }
        }
        self.entries.deinit(self.allocator);
        self.free_slots.deinit(self.allocator);
        self.key_to_slot.deinit(self.allocator);
        self.* = undefined;
    }

    /// Looks up `key` in $O(1)$, promoting it to `mru_head` on hit and returning its payload slice.
    pub fn get(self: *BoundedMetadataLru, key: LruCacheKey) ?[]const u8 {
        const slot_idx = self.key_to_slot.get(key) orelse {
            self.miss_count += 1;
            return null;
        };
        self.hit_count += 1;
        self.promoteSlotToMru(slot_idx);
        return self.entries.items[slot_idx].payload;
    }

    /// Inserts or replaces `key` with a copy of `payload`, evicting LRU tail entries until within bounds.
    pub fn put(self: *BoundedMetadataLru, key: LruCacheKey, payload: []const u8) !void {
        if (self.key_to_slot.get(key)) |existing_slot| {
            self.evictSlot(existing_slot, false);
        }
        if (self.max_entries == 0 or payload.len > self.max_bytes) {
            return;
        }

        const payload_bytes_u64: u64 = payload.len;
        while (self.live_entries >= self.max_entries or self.live_bytes + payload_bytes_u64 > self.max_bytes) {
            if (self.lru_tail == LRU_SENTINEL) break;
            self.evictSlot(self.lru_tail, true);
        }

        const cloned_payload = try self.allocator.dupe(u8, payload);
        errdefer self.allocator.free(cloned_payload);

        const slot_idx: u32 = if (self.free_slots.items.len > 0)
            self.free_slots.pop().?
        else blk: {
            const next_idx: u32 = @intCast(self.entries.items.len);
            try self.entries.append(self.allocator, .{ .key = key, .payload = &[_]u8{} });
            break :blk next_idx;
        };

        try self.key_to_slot.put(self.allocator, key, slot_idx);
        self.entries.items[slot_idx] = .{
            .key = key,
            .payload = cloned_payload,
            .prev_slot = LRU_SENTINEL,
            .next_slot = LRU_SENTINEL,
            .is_occupied = true,
        };
        self.attachSlotAtMru(slot_idx);
        self.live_entries += 1;
        self.live_bytes += payload_bytes_u64;
        std.debug.assert(self.live_entries <= self.max_entries and self.live_bytes <= self.max_bytes);
    }

    /// Detaches `slot_idx` from the doubly-linked LRU chain without freeing its payload.
    fn detachSlot(self: *BoundedMetadataLru, slot_idx: u32) void {
        const slot = &self.entries.items[slot_idx];
        if (slot.prev_slot != LRU_SENTINEL) {
            self.entries.items[slot.prev_slot].next_slot = slot.next_slot;
        } else if (self.mru_head == slot_idx) {
            self.mru_head = slot.next_slot;
        }
        if (slot.next_slot != LRU_SENTINEL) {
            self.entries.items[slot.next_slot].prev_slot = slot.prev_slot;
        } else if (self.lru_tail == slot_idx) {
            self.lru_tail = slot.prev_slot;
        }
        slot.prev_slot = LRU_SENTINEL;
        slot.next_slot = LRU_SENTINEL;
    }

    /// Links `slot_idx` at `mru_head`.
    fn attachSlotAtMru(self: *BoundedMetadataLru, slot_idx: u32) void {
        const slot = &self.entries.items[slot_idx];
        slot.prev_slot = LRU_SENTINEL;
        slot.next_slot = self.mru_head;
        if (self.mru_head != LRU_SENTINEL) {
            self.entries.items[self.mru_head].prev_slot = slot_idx;
        } else {
            self.lru_tail = slot_idx;
        }
        self.mru_head = slot_idx;
    }

    /// Moves an already-live `slot_idx` to `mru_head` in $O(1)$.
    fn promoteSlotToMru(self: *BoundedMetadataLru, slot_idx: u32) void {
        if (self.mru_head == slot_idx) return;
        self.detachSlot(slot_idx);
        self.attachSlotAtMru(slot_idx);
    }

    /// Removes `slot_idx` from `key_to_slot` and the LRU list, freeing its payload buffer.
    fn evictSlot(self: *BoundedMetadataLru, slot_idx: u32, is_capacity_eviction: bool) void {
        const slot = &self.entries.items[slot_idx];
        if (!slot.is_occupied) return;
        self.detachSlot(slot_idx);
        _ = self.key_to_slot.remove(slot.key);
        self.live_bytes -= slot.payload.len;
        self.live_entries -= 1;
        self.allocator.free(slot.payload);
        slot.* = .{ .key = slot.key, .payload = &[_]u8{}, .is_occupied = false };
        self.free_slots.append(self.allocator, slot_idx) catch {};
        if (is_capacity_eviction) {
            self.eviction_count += 1;
        }
    }
};

// ------------------ Global CAS Store Handle -------------------

/// Content-addressable global package store rooted at `<corex_home>/cache/blake3`.
pub const PkgCache = struct {
    /// Backing allocator owning path buffers and `metadata_lru`.
    allocator: std.mem.Allocator,
    /// Canonical `COREX_HOME` directory path (e.g., `/home/user/.corex`).
    corex_home: []u8,
    /// Root CAS directory `<corex_home>/cache/blake3`.
    cas_root: []u8,
    /// Blobs root `<corex_home>/cache/blake3/blobs` passed to `VfsSourceMap.mountCxTreePackage`.
    blobs_dir: []u8,
    /// Dual-bounded in-memory LRU cache for `.cxtree`, `.cxi`, sparse index, and transparency tiles.
    metadata_lru: BoundedMetadataLru,
    /// `true` once `{blobs,trees,cxi,staging,index,tlog,locks}` directories have been verified on disk.
    has_ensured_dirs: bool = false,
    /// Monotonic per-instance staging file counter preventing intra-process filename collisions.
    staging_seq: u64 = 0,

    /// Initializes a lazy `PkgCache` handle without touching the host filesystem until first I/O.
    pub fn init(
        allocator: std.mem.Allocator,
        corex_home: []const u8,
        max_lru_entries: u32,
        max_lru_bytes: u64,
    ) !PkgCache {
        const trimmed_home = std.mem.trimEnd(u8, corex_home, "/\\");
        const owned_home = try allocator.dupe(u8, if (trimmed_home.len > 0) trimmed_home else ".corex");
        errdefer allocator.free(owned_home);
        const cas_root = try std.fmt.allocPrint(allocator, "{s}/cache/blake3", .{owned_home});
        errdefer allocator.free(cas_root);
        const blobs_dir = try std.fmt.allocPrint(allocator, "{s}/blobs", .{cas_root});
        errdefer allocator.free(blobs_dir);

        return .{
            .allocator = allocator,
            .corex_home = owned_home,
            .cas_root = cas_root,
            .blobs_dir = blobs_dir,
            .metadata_lru = BoundedMetadataLru.init(allocator, max_lru_entries, max_lru_bytes),
        };
    }

    /// Releases owned path strings and `metadata_lru` buffers.
    pub fn deinit(self: *PkgCache) void {
        self.metadata_lru.deinit();
        self.allocator.free(self.blobs_dir);
        self.allocator.free(self.cas_root);
        self.allocator.free(self.corex_home);
        self.* = undefined;
    }

    /// Lazily creates `{blobs,trees,cxi,staging,index,tlog,locks}` under `cas_root` on first write/lock.
    pub fn ensureLayoutDirs(self: *PkgCache, io: std.Io) !void {
        if (self.has_ensured_dirs) return;
        for (CAS_SUBDIRS) |sub_name| {
            const dir_path = try std.fmt.allocPrint(self.allocator, "{s}/{s}", .{ self.cas_root, sub_name });
            defer self.allocator.free(dir_path);
            try std.Io.Dir.cwd().createDirPath(io, dir_path);
        }
        self.has_ensured_dirs = true;
    }

    /// Acquires a `.shared` or `.exclusive` advisory lock on `locks/gc.lock` (graceful no-op on WASI).
    pub fn acquireGcLock(
        self: *PkgCache,
        io: std.Io,
        mode: LockMode,
        is_non_blocking: bool,
    ) !AdvisoryFileLock {
        try self.ensureLayoutDirs(io);
        const lock_path = try std.fmt.allocPrint(self.allocator, "{s}/locks/gc.lock", .{self.cas_root});
        defer self.allocator.free(lock_path);

        const io_lock: std.Io.File.Lock = switch (mode) {
            .shared => .shared,
            .exclusive => .exclusive,
        };
        if (std.Io.Dir.cwd().createFile(io, lock_path, .{
            .read = true,
            .truncate = false,
            .lock = io_lock,
            .lock_nonblocking = is_non_blocking,
        })) |locked_file| {
            return .{ .file = locked_file, .is_locked = true };
        } else |open_err| switch (open_err) {
            error.FileLocksUnsupported => return .{},
            else => return open_err,
        }
    }

    /// Atomically stages, verifies `BLAKE3(data) == expected_blake3`, marks read-only, and publishes a blob.
    pub fn publishBlob(
        self: *PkgCache,
        io: std.Io,
        data: []const u8,
        expected_blake3: [32]u8,
        sink: ?*DiagnosticSink,
        span: Span,
    ) !void {
        const actual = computeUnkeyedBlake3(data);
        if (!std.crypto.timing_safe.eql([32]u8, actual, expected_blake3)) {
            try emitIntegrityDiagnostic(sink, span, "downloaded or staged blob failed BLAKE3 digest verification");
            return error.CacheIntegrityMismatch;
        }
        try self.publishImmutableArtifact(io, "blobs", "", data, expected_blake3, sink, span);
        if (data.len >= BAO_OUTBOARD_MIN_BYTES) {
            const obao_bytes = try encodeBaoOutboard(self.allocator, data);
            defer self.allocator.free(obao_bytes);
            try self.publishImmutableArtifact(
                io,
                "blobs",
                ".obao",
                obao_bytes,
                expected_blake3,
                sink,
                span,
            );
        }
    }

    /// Atomically verifies `computeCxTreeRawDigest(cxtree_bytes) == expected_tree_blake3` and publishes `.cxtree`.
    pub fn publishCxTree(
        self: *PkgCache,
        io: std.Io,
        cxtree_bytes: []const u8,
        expected_tree_blake3: [32]u8,
        sink: ?*DiagnosticSink,
        span: Span,
    ) !void {
        const view = vfs_sourcemap.validateCxTreeBytes(self.allocator, cxtree_bytes) catch {
            try emitIntegrityDiagnostic(sink, span, "corrupt or unsorted `.cxtree` package manifest header/entries");
            return error.CacheIntegrityMismatch;
        };
        const actual_tree = computeCxTreeViewDigest(view);
        if (!std.crypto.timing_safe.eql([32]u8, actual_tree, expected_tree_blake3)) {
            try emitIntegrityDiagnostic(sink, span, "`.cxtree` Merkle root does not match expected `tree_hash`");
            return error.CacheIntegrityMismatch;
        }
        try self.publishImmutableArtifact(
            io,
            "trees",
            ".cxtree",
            cxtree_bytes,
            expected_tree_blake3,
            sink,
            span,
        );
        try self.metadata_lru.put(.{ .digest = expected_tree_blake3, .domain = .cxtree }, cxtree_bytes);
    }

    /// Atomically publishes an 8-byte-aligned `.cxi` public-interface summary under `cxi/<2-hex>/<62-hex>.cxi`.
    pub fn publishCxiSummary(
        self: *PkgCache,
        io: std.Io,
        cxi_bytes: []const u8,
        cxi_blake3: [32]u8,
        sink: ?*DiagnosticSink,
        span: Span,
    ) !void {
        try self.publishImmutableArtifact(
            io,
            "cxi",
            ".cxi",
            cxi_bytes,
            cxi_blake3,
            sink,
            span,
        );
        try self.metadata_lru.put(.{ .digest = cxi_blake3, .domain = .cxi_summary }, cxi_bytes);
    }

    /// Reads and verifies `.cxtree` bytes from `metadata_lru` or `trees/<2-hex>/<62-hex>.cxtree` (`E0015` on tampering).
    pub fn readVerifiedCxTreeAlloc(
        self: *PkgCache,
        io: std.Io,
        expected_tree_blake3: [32]u8,
        sink: ?*DiagnosticSink,
        span: Span,
    ) ![]align(8) u8 {
        const cache_key = LruCacheKey{ .digest = expected_tree_blake3, .domain = .cxtree };
        if (self.metadata_lru.get(cache_key)) |cached_slice| {
            const aligned_copy = try self.allocator.alignedAlloc(u8, .@"8", cached_slice.len);
            @memcpy(aligned_copy, cached_slice);
            return aligned_copy;
        }

        const raw_bytes = try self.readShardedArtifactAligned8(io, "trees", ".cxtree", expected_tree_blake3);
        errdefer self.allocator.free(raw_bytes);

        const view = vfs_sourcemap.validateCxTreeBytes(self.allocator, raw_bytes) catch {
            try emitIntegrityDiagnostic(sink, span, "cached `.cxtree` manifest is corrupt or contains invalid paths");
            return error.CacheIntegrityMismatch;
        };
        if (!std.crypto.timing_safe.eql([32]u8, computeCxTreeViewDigest(view), expected_tree_blake3)) {
            try emitIntegrityDiagnostic(sink, span, "cached `.cxtree` digest does not match `corex.lock` `tree_hash`");
            return error.CacheIntegrityMismatch;
        }
        try self.metadata_lru.put(cache_key, raw_bytes);
        return raw_bytes;
    }

    /// Reads and `BLAKE3`-verifies a raw blob from `blobs/<2-hex>/<62-hex>` directly into a single `[]u8` buffer (`E0015` on mismatch).
    pub fn readVerifiedBlobAlloc(
        self: *PkgCache,
        io: std.Io,
        expected_blake3: [32]u8,
        sink: ?*DiagnosticSink,
        span: Span,
    ) ![]u8 {
        const raw_bytes = try self.readShardedArtifactAlloc(io, "blobs", "", expected_blake3);
        errdefer self.allocator.free(raw_bytes);
        if (!std.crypto.timing_safe.eql([32]u8, computeUnkeyedBlake3(raw_bytes), expected_blake3)) {
            try emitIntegrityDiagnostic(sink, span, "cached blob failed BLAKE3 integrity verification");
            return error.CacheIntegrityMismatch;
        }
        return raw_bytes;
    }

    /// Reads an optional companion `.obao` Bao outboard file from `blobs/`, returning `null` if absent.
    pub fn readOptionalBaoOutboardAlloc(
        self: *PkgCache,
        io: std.Io,
        blob_blake3: [32]u8,
    ) !?[]u8 {
        return self.readShardedArtifactAlloc(io, "blobs", ".obao", blob_blake3) catch |read_err| switch (read_err) {
            error.FileNotFound => null,
            else => return read_err,
        };
    }

    /// Opens `<bucket>/<2-hex>/<62-hex><ext>` (or 2-level `<2>/<2>/<64><ext>` fallback) in read-only mode.
    fn openShardedCasFile(
        self: *PkgCache,
        io: std.Io,
        bucket: []const u8,
        suffix_ext: []const u8,
        digest: [32]u8,
    ) !std.Io.File {
        const hex = std.fmt.bytesToHex(digest, .lower);
        var stack_buf: [512]u8 = undefined;
        var heap_primary: ?[]u8 = null;
        defer if (heap_primary) |hp| self.allocator.free(hp);

        const primary_path = std.fmt.bufPrint(
            &stack_buf,
            "{s}/{s}/{s}/{s}{s}",
            .{ self.cas_root, bucket, hex[0..2], hex[2..64], suffix_ext },
        ) catch blk_alloc: {
            const allocated = try std.fmt.allocPrint(
                self.allocator,
                "{s}/{s}/{s}/{s}{s}",
                .{ self.cas_root, bucket, hex[0..2], hex[2..64], suffix_ext },
            );
            heap_primary = allocated;
            break :blk_alloc allocated;
        };

        return std.Io.Dir.cwd().openFile(io, primary_path, .{
            .mode = .read_only,
            .allow_directory = false,
        }) catch |primary_err| {
            if (primary_err != error.FileNotFound) return primary_err;
            var fallback_buf: [512]u8 = undefined;
            var heap_fallback: ?[]u8 = null;
            defer if (heap_fallback) |hf| self.allocator.free(hf);

            const fallback_path = std.fmt.bufPrint(
                &fallback_buf,
                "{s}/{s}/{s}/{s}/{s}{s}",
                .{ self.cas_root, bucket, hex[0..2], hex[2..4], hex[0..64], suffix_ext },
            ) catch blk_fb: {
                const allocated_fb = try std.fmt.allocPrint(
                    self.allocator,
                    "{s}/{s}/{s}/{s}/{s}{s}",
                    .{ self.cas_root, bucket, hex[0..2], hex[2..4], hex[0..64], suffix_ext },
                );
                heap_fallback = allocated_fb;
                break :blk_fb allocated_fb;
            };
            return std.Io.Dir.cwd().openFile(io, fallback_path, .{
                .mode = .read_only,
                .allow_directory = false,
            });
        };
    }

    /// Internal helper reading `<bucket>/<2-hex>/<62-hex><ext>` (or 2-level `<2>/<2>/<64><ext>` fallback) into `[]u8`.
    fn readShardedArtifactAlloc(
        self: *PkgCache,
        io: std.Io,
        bucket: []const u8,
        suffix_ext: []const u8,
        digest: [32]u8,
    ) ![]u8 {
        const opened_file = try self.openShardedCasFile(io, bucket, suffix_ext, digest);
        defer opened_file.close(io);

        const stat_info = try opened_file.stat(io);
        if (stat_info.kind == .directory) return error.IsDir;
        if (stat_info.size > MAX_CACHED_BLOB_BYTES) return error.FileTooLarge;
        const byte_len: usize = @intCast(stat_info.size);
        const buf = try self.allocator.alloc(u8, byte_len);
        errdefer self.allocator.free(buf);
        if ((try opened_file.readPositionalAll(io, buf, 0)) != byte_len) {
            return error.UnexpectedEndOfFile;
        }
        return buf;
    }

    /// Internal helper reading `<bucket>/<2-hex>/<62-hex><ext>` (or 2-level `<2>/<2>/<64><ext>` fallback) into `align(8)`.
    fn readShardedArtifactAligned8(
        self: *PkgCache,
        io: std.Io,
        bucket: []const u8,
        suffix_ext: []const u8,
        digest: [32]u8,
    ) ![]align(8) u8 {
        const opened_file = try self.openShardedCasFile(io, bucket, suffix_ext, digest);
        defer opened_file.close(io);

        const stat_info = try opened_file.stat(io);
        if (stat_info.kind == .directory) return error.IsDir;
        if (stat_info.size > MAX_CACHED_BLOB_BYTES) return error.FileTooLarge;
        const byte_len: usize = @intCast(stat_info.size);
        const buf = try self.allocator.alignedAlloc(u8, .@"8", byte_len);
        errdefer self.allocator.free(buf);
        if ((try opened_file.readPositionalAll(io, buf, 0)) != byte_len) {
            return error.UnexpectedEndOfFile;
        }
        return buf;
    }

    /// Verifies that an already-present CAS file at `final_path` matches `payload` byte-for-byte via `BLAKE3`.
    fn verifyExistingImmutableArtifact(
        self: *PkgCache,
        io: std.Io,
        final_path: []const u8,
        payload: []const u8,
        sink: ?*DiagnosticSink,
        span: Span,
    ) !bool {
        const existing_file = std.Io.Dir.cwd().openFile(io, final_path, .{
            .mode = .read_only,
            .allow_directory = false,
        }) catch |open_err| switch (open_err) {
            error.FileNotFound => return false,
            else => {
                try emitIntegrityDiagnostic(sink, span, "existing cached artifact could not be opened for verification");
                return error.CacheIntegrityMismatch;
            },
        };
        defer existing_file.close(io);
        const existing_stat = try existing_file.stat(io);
        if (existing_stat.kind == .directory or existing_stat.size != payload.len) {
            try emitIntegrityDiagnostic(sink, span, "existing cached artifact size mismatch");
            return error.CacheIntegrityMismatch;
        }
        const existing_buf = try self.allocator.alloc(u8, payload.len);
        defer self.allocator.free(existing_buf);
        if ((try existing_file.readPositionalAll(io, existing_buf, 0)) == payload.len and
            std.crypto.timing_safe.eql([32]u8, computeUnkeyedBlake3(existing_buf), computeUnkeyedBlake3(payload)))
        {
            return true;
        }
        try emitIntegrityDiagnostic(sink, span, "existing cached artifact failed BLAKE3 verification");
        return error.CacheIntegrityMismatch;
    }

    /// Internal atomic staging writer hardening permissions to read-only before `std.Io.Dir.rename`.
    fn publishImmutableArtifact(
        self: *PkgCache,
        io: std.Io,
        bucket: []const u8,
        suffix_ext: []const u8,
        payload: []const u8,
        digest: [32]u8,
        sink: ?*DiagnosticSink,
        span: Span,
    ) !void {
        try self.ensureLayoutDirs(io);
        const hex = std.fmt.bytesToHex(digest, .lower);
        const shard_dir = try std.fmt.allocPrint(self.allocator, "{s}/{s}/{s}", .{ self.cas_root, bucket, hex[0..2] });
        defer self.allocator.free(shard_dir);
        try std.Io.Dir.cwd().createDirPath(io, shard_dir);

        const final_path = try std.fmt.allocPrint(
            self.allocator,
            "{s}/{s}{s}",
            .{ shard_dir, hex[2..64], suffix_ext },
        );
        defer self.allocator.free(final_path);

        if (try self.verifyExistingImmutableArtifact(io, final_path, payload, sink, span)) {
            return;
        }

        self.staging_seq +%= 1;
        const salt_hash = std.hash.Wyhash.hash(self.staging_seq, &digest);
        const staging_path = try std.fmt.allocPrint(
            self.allocator,
            "{s}/staging/stage-{x}-{d}.tmp",
            .{ self.cas_root, salt_hash, self.staging_seq },
        );
        defer self.allocator.free(staging_path);

        var is_staged_live = false;
        errdefer if (is_staged_live) {
            std.Io.Dir.cwd().deleteFile(io, staging_path) catch {};
        };

        const staged_file = try std.Io.Dir.cwd().createFile(io, staging_path, .{ .truncate = true });
        is_staged_live = true;
        {
            errdefer staged_file.close(io);
            try staged_file.writeStreamingAll(io, payload);
            try staged_file.sync(io);
            const stat_info = try staged_file.stat(io);
            staged_file.setPermissions(io, stat_info.permissions.setReadOnly(true)) catch {};
        }
        staged_file.close(io);

        if (std.Io.Dir.rename(std.Io.Dir.cwd(), staging_path, std.Io.Dir.cwd(), final_path, io)) |_| {
            is_staged_live = false;
            return;
        } else |rename_err| {
            // Handle concurrent idempotent content-addressed commit (always verifying exact size + BLAKE3 bytes):
            if (rename_err == error.AccessDenied or rename_err == error.PathAlreadyExists) {
                if (try self.verifyExistingImmutableArtifact(io, final_path, payload, sink, span)) {
                    std.Io.Dir.cwd().deleteFile(io, staging_path) catch {};
                    is_staged_live = false;
                    return;
                }
            }
            return rename_err;
        }
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Default maximum entry capacity for `BoundedMetadataLru` (`1,024` artifacts).
pub const DEFAULT_MAX_LRU_ENTRIES: u32 = 1_024;
/// Default maximum byte capacity for `BoundedMetadataLru` (`16 MiB`).
pub const DEFAULT_MAX_LRU_BYTES: u64 = 16 * 1024 * 1024;
/// Minimum blob size (`64 KiB`) that automatically generates a companion `.obao` Bao outboard file.
pub const BAO_OUTBOARD_MIN_BYTES: usize = 64 * 1024;
/// Hard ceiling (`64 MiB`) on any single cached package blob or `.cxtree` manifest.
pub const MAX_CACHED_BLOB_BYTES: u64 = 64 * 1024 * 1024;
/// Domain-separated `BLAKE3` KDF context string for `.cxtree` Merkle manifests (`DR-11` §2.1).
pub const CXTREE_KDF_CONTEXT = "corex-pkg-tree-v1 2026-01-01";
/// Domain-separated prefix signed by `Ed25519` package publisher signatures (`DR-11` §4.2).
pub const PUBLISH_SIG_DOMAIN_PREFIX = "corex-publish-v1\n";
/// Sentinel `u32` slot index representing `null` in `BoundedMetadataLru`.
const LRU_SENTINEL: u32 = std.math.maxInt(u32);
/// `BLAKE3` chunk length in bytes (`1,024`).
const BLAKE3_CHUNK_LEN: usize = 1024;
/// `BLAKE3` compression block length in bytes (`64`).
const BLAKE3_BLOCK_LEN: usize = 64;
/// `BLAKE3` domain flag marking the first 64-byte block of a 1,024-byte chunk.
const BLAKE3_FLAG_CHUNK_START: u8 = 1 << 0;
/// `BLAKE3` domain flag marking the final 64-byte block of a 1,024-byte chunk.
const BLAKE3_FLAG_CHUNK_END: u8 = 1 << 1;
/// `BLAKE3` domain flag marking a parent node combining two 32-byte child chaining values.
const BLAKE3_FLAG_PARENT: u8 = 1 << 2;
/// `BLAKE3` domain flag marking the tree root compression step.
const BLAKE3_FLAG_ROOT: u8 = 1 << 3;

/// Standard `BLAKE3` / `SHA-256` initial 32-bit chaining value words.
const BLAKE3_IV: [8]u32 = .{
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
};

/// Canonical 7-round `BLAKE3` message word permutation schedule.
const BLAKE3_MSG_SCHEDULE: [7][16]u8 = .{
    .{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
    .{ 2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8 },
    .{ 3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1 },
    .{ 10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6 },
    .{ 12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4 },
    .{ 9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7 },
    .{ 11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13 },
};

/// Canonical CAS subdirectories created beneath `<corex_home>/cache/blake3`.
const CAS_SUBDIRS = [_][]const u8{
    "blobs",
    "cxi",
    "index",
    "locks",
    "staging",
    "tlog",
    "trees",
};

/// $O(1)$ static set of known text file extensions eligible for `CRLF`->`LF` normalization on ingest.
const TEXT_EXTENSION_MAP = std.StaticStringMap(void).initComptime(.{
    .{ ".c", {} },
    .{ ".cx", {} },
    .{ ".def", {} },
    .{ ".h", {} },
    .{ ".json", {} },
    .{ ".md", {} },
    .{ ".toml", {} },
    .{ ".txt", {} },
});

/// $O(1)$ static set of extensionless text filenames eligible for `CRLF`->`LF` normalization on ingest.
const TEXT_BASENAME_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "CHANGELOG", {} },
    .{ "COPYRIGHT", {} },
    .{ "LICENSE", {} },
    .{ "NOTICE", {} },
    .{ "README", {} },
});

// -------------------------------------- INTERNALS --------------------------------------

// ----------------- Diagnostics & Path Helpers -----------------

/// Emits `DiagnosticCode.e0015_cache_integrity_mismatch` into `sink` when non-null.
fn emitIntegrityDiagnostic(sink: ?*DiagnosticSink, span: Span, message: []const u8) !void {
    if (sink) |diag_sink| {
        try diag_sink.emit(.{
            .code = .e0015_cache_integrity_mismatch,
            .severity = .err,
            .primary_span = span,
            .message = message,
        });
    }
}

/// Computes standard unkeyed 256-bit `BLAKE3` over `bytes`.
fn computeUnkeyedBlake3(bytes: []const u8) [32]u8 {
    var out: [32]u8 = undefined;
    std.crypto.hash.Blake3.hash(bytes, &out, .{});
    return out;
}

/// Returns `true` if `rel_path` has a recognized source/manifest text filename or extension.
fn hasTextSourceExtension(rel_path: []const u8) bool {
    const slash_pos = std.mem.lastIndexOfAny(u8, rel_path, "/\\");
    const base_name = if (slash_pos) |idx| rel_path[idx + 1 ..] else rel_path;
    if (std.mem.eql(u8, base_name, "corex.toml") or TEXT_BASENAME_MAP.has(base_name)) return true;
    if (std.mem.lastIndexOfScalar(u8, base_name, '.')) |dot_idx| {
        return TEXT_EXTENSION_MAP.has(base_name[dot_idx..]);
    }
    return false;
}

/// Computes `tree_blake3` directly from a validated `CxTreeView`.
fn computeCxTreeViewDigest(view: vfs_sourcemap.CxTreeView) [32]u8 {
    var hasher = std.crypto.hash.Blake3.initKdf(CXTREE_KDF_CONTEXT, .{});
    for (view.entries) |entry| {
        const rel_path = view.asEntryPath(entry);
        const mode_byte = [1]u8{@intCast(entry.file_mode & 0xFF)};
        const len_le = std.mem.toBytes(std.mem.nativeToLittle(u16, entry.rel_path_len));
        const size_le = std.mem.toBytes(std.mem.nativeToLittle(u64, entry.file_size));
        hasher.update(&mode_byte);
        hasher.update(&len_le);
        hasher.update(rel_path);
        hasher.update(&size_le);
        hasher.update(&entry.file_blake3);
    }
    var out: [32]u8 = undefined;
    hasher.final(&out);
    return out;
}

// --------- Standalone 7-Round BLAKE3 Bao Compression ----------

/// Quarter-round mixing step `G` of the 7-round `BLAKE3` compression function.
inline fn blake3MixG(
    state: *[16]u32,
    idx_a: usize,
    idx_b: usize,
    idx_c: usize,
    idx_d: usize,
    word_x: u32,
    word_y: u32,
) void {
    state[idx_a] +%= state[idx_b] +% word_x;
    state[idx_d] = std.math.rotr(u32, state[idx_d] ^ state[idx_a], 16);
    state[idx_c] +%= state[idx_d];
    state[idx_b] = std.math.rotr(u32, state[idx_b] ^ state[idx_c], 12);
    state[idx_a] +%= state[idx_b] +% word_y;
    state[idx_d] = std.math.rotr(u32, state[idx_d] ^ state[idx_a], 8);
    state[idx_c] +%= state[idx_d];
    state[idx_b] = std.math.rotr(u32, state[idx_b] ^ state[idx_c], 7);
}

/// Compresses one 64-byte `BLAKE3` block across all 7 rounds and returns the 32-byte chaining value.
fn blake3CompressBlock(
    chaining_val: [8]u32,
    block_bytes: *const [64]u8,
    block_len: u8,
    counter: u64,
    flags: u8,
) [8]u32 {
    var msg_words: [16]u32 = undefined;
    for (0..16) |i| {
        msg_words[i] = std.mem.readInt(u32, block_bytes[i * 4 ..][0..4], .little);
    }

    var state: [16]u32 = .{
        chaining_val[0],    chaining_val[1],          chaining_val[2], chaining_val[3],
        chaining_val[4],    chaining_val[5],          chaining_val[6], chaining_val[7],
        BLAKE3_IV[0],       BLAKE3_IV[1],             BLAKE3_IV[2],    BLAKE3_IV[3],
        @truncate(counter), @truncate(counter >> 32), block_len,       flags,
    };

    for (0..7) |round_idx| {
        const sched = &BLAKE3_MSG_SCHEDULE[round_idx];
        blake3MixG(&state, 0, 4, 8, 12, msg_words[sched[0]], msg_words[sched[1]]);
        blake3MixG(&state, 1, 5, 9, 13, msg_words[sched[2]], msg_words[sched[3]]);
        blake3MixG(&state, 2, 6, 10, 14, msg_words[sched[4]], msg_words[sched[5]]);
        blake3MixG(&state, 3, 7, 11, 15, msg_words[sched[6]], msg_words[sched[7]]);
        blake3MixG(&state, 0, 5, 10, 15, msg_words[sched[8]], msg_words[sched[9]]);
        blake3MixG(&state, 1, 6, 11, 12, msg_words[sched[10]], msg_words[sched[11]]);
        blake3MixG(&state, 2, 7, 8, 13, msg_words[sched[12]], msg_words[sched[13]]);
        blake3MixG(&state, 3, 4, 9, 14, msg_words[sched[14]], msg_words[sched[15]]);
    }

    var next_cv: [8]u32 = undefined;
    for (0..8) |i| {
        next_cv[i] = state[i] ^ state[i + 8];
    }
    return next_cv;
}

/// Converts 8 little-endian `u32` chaining value words into a 32-byte digest array.
fn cvWordsToBytes(words: [8]u32) [32]u8 {
    var out: [32]u8 = undefined;
    for (0..8) |i| {
        std.mem.writeInt(u32, out[i * 4 ..][0..4], words[i], .little);
    }
    return out;
}

/// Compresses a single `<= 1,024`-byte `BLAKE3` chunk (`CHUNK_START` / `CHUNK_END` / optional `ROOT`).
fn computeBlake3ChunkCv(chunk_bytes: []const u8, chunk_index: u64, is_root: bool) [32]u8 {
    std.debug.assert(chunk_bytes.len <= BLAKE3_CHUNK_LEN);
    var cv_words: [8]u32 = BLAKE3_IV;
    if (chunk_bytes.len == 0) {
        const zero_block: [64]u8 = @splat(0);
        const root_bit: u8 = if (is_root) BLAKE3_FLAG_ROOT else 0;
        return cvWordsToBytes(blake3CompressBlock(
            cv_words,
            &zero_block,
            0,
            chunk_index,
            BLAKE3_FLAG_CHUNK_START | BLAKE3_FLAG_CHUNK_END | root_bit,
        ));
    }

    const block_count = (chunk_bytes.len + BLAKE3_BLOCK_LEN - 1) / BLAKE3_BLOCK_LEN;
    var blk_idx: usize = 0;
    while (blk_idx < block_count) : (blk_idx += 1) {
        const start = blk_idx * BLAKE3_BLOCK_LEN;
        const rem = @min(BLAKE3_BLOCK_LEN, chunk_bytes.len - start);
        var padded_block: [64]u8 = @splat(0);
        @memcpy(padded_block[0..rem], chunk_bytes[start .. start + rem]);

        var flags: u8 = 0;
        if (blk_idx == 0) flags |= BLAKE3_FLAG_CHUNK_START;
        if (blk_idx + 1 == block_count) {
            flags |= BLAKE3_FLAG_CHUNK_END;
            if (is_root) flags |= BLAKE3_FLAG_ROOT;
        }
        cv_words = blake3CompressBlock(cv_words, &padded_block, @intCast(rem), chunk_index, flags);
    }
    return cvWordsToBytes(cv_words);
}

/// Compresses two 32-byte child chaining values (`left_cv || right_cv`) with `PARENT` (and optional `ROOT`).
fn computeBlake3ParentCv(left_cv: [32]u8, right_cv: [32]u8, is_root: bool) [32]u8 {
    var parent_block: [64]u8 = undefined;
    @memcpy(parent_block[0..32], &left_cv);
    @memcpy(parent_block[32..64], &right_cv);
    const flags: u8 = BLAKE3_FLAG_PARENT | (if (is_root) BLAKE3_FLAG_ROOT else 0);
    return cvWordsToBytes(blake3CompressBlock(BLAKE3_IV, &parent_block, 64, 0, flags));
}

/// Returns the left-complete binary subtree chunk count (`2^k` strictly `< chunk_count`) for `chunk_count >= 2`.
inline fn leftSubtreeChunks(chunk_count: u64) u64 {
    std.debug.assert(chunk_count >= 2);
    const shift_amt: u6 = @intCast(63 - @clz(chunk_count - 1));
    return @as(u64, 1) << shift_amt;
}

/// Recursively writes pre-order parent chaining values (`depth <= 54` logarithmic bound) into `out_nodes`.
fn encodeBaoSubtreeRecursive(
    data: []const u8,
    base_chunk: u64,
    chunk_count: u64,
    is_root: bool,
    out_nodes: []u8,
    write_cursor: *usize,
) [32]u8 {
    if (chunk_count == 1) {
        const byte_start: usize = @intCast(base_chunk * BLAKE3_CHUNK_LEN);
        const byte_end: usize = @min(data.len, byte_start + BLAKE3_CHUNK_LEN);
        const slice = if (byte_start <= data.len) data[byte_start..byte_end] else &[_]u8{};
        return computeBlake3ChunkCv(slice, base_chunk, is_root);
    }

    const left_chunks = leftSubtreeChunks(chunk_count);
    const slot_offset = write_cursor.*;
    write_cursor.* += 64;

    const left_cv = encodeBaoSubtreeRecursive(data, base_chunk, left_chunks, false, out_nodes, write_cursor);
    const right_cv = encodeBaoSubtreeRecursive(
        data,
        base_chunk + left_chunks,
        chunk_count - left_chunks,
        false,
        out_nodes,
        write_cursor,
    );
    @memcpy(out_nodes[slot_offset .. slot_offset + 32], &left_cv);
    @memcpy(out_nodes[slot_offset + 32 .. slot_offset + 64], &right_cv);
    return computeBlake3ParentCv(left_cv, right_cv, is_root);
}

/// Recursively verifies a Bao subtree slice against `expected_cv` (`depth <= 54`).
fn verifyBaoSubtreeRecursive(
    expected_cv: [32]u8,
    obao_nodes: []const u8,
    obao_cursor: *usize,
    base_chunk: u64,
    chunk_count: u64,
    total_len: u64,
    slice_start_chunk: u64,
    slice_end_chunk: u64,
    slice_data: []const u8,
    data_cursor: *usize,
    is_root: bool,
) bool {
    if (chunk_count == 1) {
        const chunk_byte_start = base_chunk * BLAKE3_CHUNK_LEN;
        const expected_chunk_len: usize = if (total_len == 0)
            0
        else
            @intCast(@min(@as(u64, BLAKE3_CHUNK_LEN), total_len - chunk_byte_start));
        if (data_cursor.* + expected_chunk_len > slice_data.len) return false;
        const chunk_slice = slice_data[data_cursor.* .. data_cursor.* + expected_chunk_len];
        data_cursor.* += expected_chunk_len;
        const actual_cv = computeBlake3ChunkCv(chunk_slice, base_chunk, is_root);
        return std.crypto.timing_safe.eql([32]u8, actual_cv, expected_cv);
    }

    if (obao_cursor.* + 64 > obao_nodes.len) return false;
    const left_cv = obao_nodes[obao_cursor.*..][0..32].*;
    const right_cv = obao_nodes[obao_cursor.* + 32 ..][0..32].*;
    obao_cursor.* += 64;

    const parent_cv = computeBlake3ParentCv(left_cv, right_cv, is_root);
    if (!std.crypto.timing_safe.eql([32]u8, parent_cv, expected_cv)) return false;

    const left_chunks = leftSubtreeChunks(chunk_count);
    const right_chunks = chunk_count - left_chunks;
    const mid_chunk = base_chunk + left_chunks;

    if (slice_start_chunk < mid_chunk) {
        if (!verifyBaoSubtreeRecursive(
            left_cv,
            obao_nodes,
            obao_cursor,
            base_chunk,
            left_chunks,
            total_len,
            slice_start_chunk,
            slice_end_chunk,
            slice_data,
            data_cursor,
            false,
        )) return false;
    } else {
        const skip_bytes = std.math.mul(usize, @intCast(left_chunks - 1), 64) catch return false;
        if (obao_cursor.* + skip_bytes > obao_nodes.len) return false;
        obao_cursor.* += skip_bytes;
    }

    if (slice_end_chunk > mid_chunk) {
        if (!verifyBaoSubtreeRecursive(
            right_cv,
            obao_nodes,
            obao_cursor,
            mid_chunk,
            right_chunks,
            total_len,
            slice_start_chunk,
            slice_end_chunk,
            slice_data,
            data_cursor,
            false,
        )) return false;
    } else {
        const skip_bytes = std.math.mul(usize, @intCast(right_chunks - 1), 64) catch return false;
        if (obao_cursor.* + skip_bytes > obao_nodes.len) return false;
        obao_cursor.* += skip_bytes;
    }
    return true;
}

// ---------------- Tiered Vendor Clone Helpers -----------------

/// Resolves an existing CAS source file across 1-level `<2>/<62>` and 2-level `<2>/<2>/<64>` shard layouts.
fn resolveShardedCasSourcePathAlloc(
    io: std.Io,
    allocator: std.mem.Allocator,
    cas_root: []const u8,
    bucket: []const u8,
    suffix_ext: []const u8,
    digest: [32]u8,
) ![]u8 {
    const hex = std.fmt.bytesToHex(digest, .lower);
    const primary_path = try std.fmt.allocPrint(
        allocator,
        "{s}/{s}/{s}/{s}{s}",
        .{ cas_root, bucket, hex[0..2], hex[2..64], suffix_ext },
    );
    if (std.Io.Dir.cwd().statFile(io, primary_path, .{})) |_| {
        return primary_path;
    } else |stat_err| {
        allocator.free(primary_path);
        if (stat_err != error.FileNotFound) return stat_err;
    }
    return std.fmt.allocPrint(
        allocator,
        "{s}/{s}/{s}/{s}/{s}{s}",
        .{ cas_root, bucket, hex[0..2], hex[2..4], hex[0..64], suffix_ext },
    );
}

/// Attempts a Linux `FICLONE` copy-on-write reflink from `src_file` onto a newly staged file in `dst_path`.
fn tryCloneFileViaReflink(
    io: std.Io,
    allocator: std.mem.Allocator,
    src_path: []const u8,
    dst_path: []const u8,
) bool {
    if (builtin.os.tag != .linux) return false;

    const src_file = std.Io.Dir.cwd().openFile(io, src_path, .{
        .mode = .read_only,
        .allow_directory = false,
    }) catch return false;
    defer src_file.close(io);

    const tmp_path = std.fmt.allocPrint(allocator, "{s}.reflink.tmp", .{dst_path}) catch return false;
    defer allocator.free(tmp_path);

    const dst_file = std.Io.Dir.cwd().createFile(io, tmp_path, .{ .truncate = true }) catch return false;
    const ficlone_req = std.os.linux.IOCTL.IOW(0x94, 9, c_int);
    const src_fd_usize: usize = @intCast(@as(u32, @bitCast(src_file.handle)));
    const ioctl_rc = std.os.linux.ioctl(dst_file.handle, ficlone_req, src_fd_usize);
    if (std.os.linux.errno(ioctl_rc) != .SUCCESS) {
        dst_file.close(io);
        std.Io.Dir.cwd().deleteFile(io, tmp_path) catch {};
        return false;
    }

    dst_file.sync(io) catch {};
    if (dst_file.stat(io)) |st| {
        dst_file.setPermissions(io, st.permissions.setReadOnly(true)) catch {};
    } else |_| {}
    dst_file.close(io);

    std.Io.Dir.cwd().deleteFile(io, dst_path) catch {};
    if (std.Io.Dir.rename(std.Io.Dir.cwd(), tmp_path, std.Io.Dir.cwd(), dst_path, io)) |_| {
        return true;
    } else |_| {
        std.Io.Dir.cwd().deleteFile(io, tmp_path) catch {};
        return false;
    }
}

/// Materializes immutable `src_path` onto `dst_path` using Tier 1 reflink -> Tier 2 hardlink -> Tier 3 copy.
fn materializeImmutableFileTiered(
    io: std.Io,
    allocator: std.mem.Allocator,
    src_path: []const u8,
    dst_path: []const u8,
) !VendorLinkTier {
    if (std.fs.path.dirname(dst_path)) |parent_dir| {
        if (parent_dir.len > 0) try std.Io.Dir.cwd().createDirPath(io, parent_dir);
    }

    // [1] Tier 1: Copy-on-Write filesystem reflink (`FICLONE` on Linux when supported by underlying FS):
    if (tryCloneFileViaReflink(io, allocator, src_path, dst_path)) {
        return .cow_reflink;
    }

    // [2] Tier 2: Read-only directory hardlink (`follow_symlinks = false`):
    std.Io.Dir.cwd().deleteFile(io, dst_path) catch {};
    if (std.Io.Dir.hardLink(
        std.Io.Dir.cwd(),
        src_path,
        std.Io.Dir.cwd(),
        dst_path,
        io,
        .{ .follow_symlinks = false },
    )) |_| {
        return .hardlink;
    } else |_| {}

    // [3] Tier 3: Cross-device (`EXDEV`) atomic read-only copy:
    const src_file = try std.Io.Dir.cwd().openFile(io, src_path, .{
        .mode = .read_only,
        .allow_directory = false,
    });
    defer src_file.close(io);
    const src_stat = try src_file.stat(io);
    const file_len: usize = @intCast(src_stat.size);
    const copy_buf = try allocator.alloc(u8, file_len);
    defer allocator.free(copy_buf);
    if ((try src_file.readPositionalAll(io, copy_buf, 0)) != file_len) {
        return error.UnexpectedEndOfFile;
    }

    const tmp_path = try std.fmt.allocPrint(allocator, "{s}.copy.tmp", .{dst_path});
    defer allocator.free(tmp_path);
    errdefer std.Io.Dir.cwd().deleteFile(io, tmp_path) catch {};

    const tmp_file = try std.Io.Dir.cwd().createFile(io, tmp_path, .{ .truncate = true });
    {
        errdefer tmp_file.close(io);
        try tmp_file.writeStreamingAll(io, copy_buf);
        try tmp_file.sync(io);
        const tmp_stat = try tmp_file.stat(io);
        tmp_file.setPermissions(io, tmp_stat.permissions.setReadOnly(true)) catch {};
    }
    tmp_file.close(io);

    std.Io.Dir.cwd().deleteFile(io, dst_path) catch {};
    try std.Io.Dir.rename(std.Io.Dir.cwd(), tmp_path, std.Io.Dir.cwd(), dst_path, io);
    return .atomic_copy;
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------ Environment & Normalization Helpers -------------

/// Resolves `COREX_HOME` (`$COREX_HOME` -> OS cache/home directory fallback, `reconciled_overrides.md` §1.5).
pub fn resolveCorexHome(
    allocator: std.mem.Allocator,
    environ_map: ?*const std.process.Environ.Map,
) ![]u8 {
    if (environ_map) |env| {
        if (env.get("COREX_HOME")) |override_home| {
            if (override_home.len > 0) return allocator.dupe(u8, override_home);
        }
        if (builtin.os.tag == .windows) {
            if (env.get("LOCALAPPDATA")) |local_app| {
                if (local_app.len > 0) return std.fmt.allocPrint(allocator, "{s}\\corex", .{local_app});
            }
            if (env.get("USERPROFILE")) |user_prof| {
                if (user_prof.len > 0) return std.fmt.allocPrint(allocator, "{s}\\.corex", .{user_prof});
            }
        } else if (builtin.os.tag == .macos) {
            if (env.get("HOME")) |home_dir| {
                if (home_dir.len > 0) {
                    return std.fmt.allocPrint(allocator, "{s}/Library/Caches/corex", .{home_dir});
                }
            }
        } else {
            if (env.get("XDG_CACHE_HOME")) |xdg_cache| {
                if (xdg_cache.len > 0) return std.fmt.allocPrint(allocator, "{s}/corex", .{xdg_cache});
            }
            if (env.get("HOME")) |home_dir| {
                if (home_dir.len > 0) return std.fmt.allocPrint(allocator, "{s}/.corex", .{home_dir});
            }
        }
    }
    return allocator.dupe(u8, ".corex");
}

/// Normalizes `CRLF`->`LF` for valid UTF-8 source/manifest files while preserving binary `@embed_bytes` assets verbatim.
pub fn normalizeSourceForBlobIngest(
    arena: *BumpArena,
    rel_path: []const u8,
    raw_bytes: []const u8,
) !NormalizedIngestBlob {
    if (!hasTextSourceExtension(rel_path) or
        std.mem.indexOfScalar(u8, raw_bytes, 0) != null or
        std.mem.indexOf(u8, raw_bytes, "\r\n") == null or
        !std.unicode.utf8ValidateSlice(raw_bytes))
    {
        return .{
            .bytes = raw_bytes,
            .blake3_digest = computeUnkeyedBlake3(raw_bytes),
            .is_crlf_normalized = false,
        };
    }

    var crlf_count: usize = 0;
    var i: usize = 0;
    while (i + 1 < raw_bytes.len) : (i += 1) {
        if (raw_bytes[i] == '\r' and raw_bytes[i + 1] == '\n') {
            crlf_count += 1;
            i += 1;
        }
    }

    const out_buf = try arena.allocSlice(u8, raw_bytes.len - crlf_count);
    var write_pos: usize = 0;
    var read_pos: usize = 0;
    while (read_pos < raw_bytes.len) : (read_pos += 1) {
        if (read_pos + 1 < raw_bytes.len and raw_bytes[read_pos] == '\r' and raw_bytes[read_pos + 1] == '\n') {
            out_buf[write_pos] = '\n';
            write_pos += 1;
            read_pos += 1;
        } else {
            out_buf[write_pos] = raw_bytes[read_pos];
            write_pos += 1;
        }
    }
    std.debug.assert(write_pos == out_buf.len);
    return .{
        .bytes = out_buf,
        .blake3_digest = computeUnkeyedBlake3(out_buf),
        .is_crlf_normalized = true,
    };
}

// --------------- CxTree Serialization & Hashing ---------------

/// Serializes `input_entries` into an 8-byte-aligned `.cxtree` buffer and computes its keyed `tree_blake3` digest.
pub fn buildCxTreeBytes(
    allocator: std.mem.Allocator,
    pkg_name: []const u8,
    input_entries: []const CxTreeInputEntry,
    sink: ?*DiagnosticSink,
    span: Span,
) !struct { bytes: []align(8) u8, tree_blake3: [32]u8 } {
    if (input_entries.len > std.math.maxInt(u32)) return error.OutOfMemory;

    const sorted_entries = try allocator.dupe(CxTreeInputEntry, input_entries);
    defer allocator.free(sorted_entries);
    std.mem.sort(CxTreeInputEntry, sorted_entries, {}, struct {
        /// Orders `CxTreeInputEntry` records in ascending bytewise UTF-8 `rel_path` order.
        fn lessThan(_: void, lhs: CxTreeInputEntry, rhs: CxTreeInputEntry) bool {
            return std.mem.order(u8, lhs.rel_path, rhs.rel_path) == .lt;
        }
    }.lessThan);

    // [1] Validate every path, reject duplicates / case-insensitive collisions, and size string table:
    var lower_arena = BumpArena.init(allocator);
    defer lower_arena.deinit();
    var seen_lower: std.StringHashMapUnmanaged(void) = .empty;
    defer seen_lower.deinit(allocator);
    try seen_lower.ensureTotalCapacity(allocator, @intCast(sorted_entries.len));

    var str_table_len: usize = try std.math.add(usize, pkg_name.len, 1);
    for (sorted_entries, 0..) |entry, idx| {
        if (!vfs_sourcemap.isValidCxTreeRelativePath(entry.rel_path) or
            entry.rel_path.len > std.math.maxInt(u16) or
            (entry.file_mode != 0x01 and entry.file_mode != 0x02))
        {
            try emitIntegrityDiagnostic(sink, span, "invalid `.cxtree` relative path or file mode");
            return error.CacheIntegrityMismatch;
        }
        if (idx > 0 and std.mem.eql(u8, sorted_entries[idx - 1].rel_path, entry.rel_path)) {
            try emitIntegrityDiagnostic(sink, span, "duplicate relative path in `.cxtree` manifest");
            return error.CacheIntegrityMismatch;
        }
        const lower_buf = try lower_arena.allocSlice(u8, entry.rel_path.len);
        for (entry.rel_path, 0..) |ch_byte, j| {
            lower_buf[j] = std.ascii.toLower(ch_byte);
        }
        if ((seen_lower.getOrPutAssumeCapacity(lower_buf)).found_existing) {
            try emitIntegrityDiagnostic(sink, span, "case-colliding relative paths in `.cxtree` manifest");
            return error.CacheIntegrityMismatch;
        }
        str_table_len = try std.math.add(usize, str_table_len, entry.rel_path.len);
    }
    if (str_table_len > std.math.maxInt(u32)) return error.OutOfMemory;

    // [2] Allocate 8-byte-aligned `.cxtree` buffer and populate header, entries, and string table:
    const entries_bytes_len = try std.math.mul(usize, sorted_entries.len, @sizeOf(CxTreeEntry));
    const total_len = try std.math.add(
        usize,
        @sizeOf(CxTreeHeader),
        try std.math.add(usize, entries_bytes_len, str_table_len),
    );
    const out = try allocator.alignedAlloc(u8, .@"8", total_len);
    errdefer allocator.free(out);

    std.mem.bytesAsValue(CxTreeHeader, out[0..@sizeOf(CxTreeHeader)]).* = .{
        .entry_count = @intCast(sorted_entries.len),
        .string_table_bytes = @intCast(str_table_len),
        .pkg_name_str_off = 0,
    };

    const str_base = @sizeOf(CxTreeHeader) + entries_bytes_len;
    @memcpy(out[str_base .. str_base + pkg_name.len], pkg_name);
    out[str_base + pkg_name.len] = 0;

    var str_cursor: usize = pkg_name.len + 1;
    const out_entries = std.mem.bytesAsSlice(
        CxTreeEntry,
        out[@sizeOf(CxTreeHeader) .. @sizeOf(CxTreeHeader) + entries_bytes_len],
    );
    var tree_hasher = std.crypto.hash.Blake3.initKdf(CXTREE_KDF_CONTEXT, .{});

    for (sorted_entries, 0..) |entry, idx| {
        @memcpy(out[str_base + str_cursor .. str_base + str_cursor + entry.rel_path.len], entry.rel_path);
        out_entries[idx] = .{
            .rel_path_off = @intCast(str_cursor),
            .rel_path_len = @intCast(entry.rel_path.len),
            .file_mode = entry.file_mode,
            .file_size = entry.file_size,
            .file_blake3 = entry.file_blake3,
        };
        str_cursor += entry.rel_path.len;

        const mode_byte = [1]u8{@intCast(entry.file_mode & 0xFF)};
        const len_le = std.mem.toBytes(std.mem.nativeToLittle(u16, @intCast(entry.rel_path.len)));
        const size_le = std.mem.toBytes(std.mem.nativeToLittle(u64, entry.file_size));
        tree_hasher.update(&mode_byte);
        tree_hasher.update(&len_le);
        tree_hasher.update(entry.rel_path);
        tree_hasher.update(&size_le);
        tree_hasher.update(&entry.file_blake3);
    }

    var tree_digest: [32]u8 = undefined;
    tree_hasher.final(&tree_digest);
    return .{ .bytes = out, .tree_blake3 = tree_digest };
}

/// Computes the keyed `tree_blake3` digest over `input_entries` without allocating a `.cxtree` buffer.
pub fn computeCxTreeDigest(
    allocator: std.mem.Allocator,
    input_entries: []const CxTreeInputEntry,
    sink: ?*DiagnosticSink,
    span: Span,
) ![32]u8 {
    const built = try buildCxTreeBytes(allocator, "", input_entries, sink, span);
    defer allocator.free(built.bytes);
    return built.tree_blake3;
}

// -------------- Bao Verified Streaming (`.obao`) --------------

/// Encodes a pre-order `.obao` Bao outboard Merkle tree (`8B` LE `total_len` + `(chunks - 1) * 64B` parents).
pub fn encodeBaoOutboard(allocator: std.mem.Allocator, data: []const u8) ![]u8 {
    const chunk_count: u64 = if (data.len == 0) 1 else (data.len + BLAKE3_CHUNK_LEN - 1) / BLAKE3_CHUNK_LEN;
    const parent_bytes = try std.math.mul(usize, @intCast(chunk_count - 1), 64);
    const out = try allocator.alloc(u8, try std.math.add(usize, 8, parent_bytes));
    errdefer allocator.free(out);

    std.mem.writeInt(u64, out[0..8], data.len, .little);
    var write_cursor: usize = 0;
    const root_cv = encodeBaoSubtreeRecursive(data, 0, chunk_count, true, out[8..], &write_cursor);
    std.debug.assert(write_cursor == parent_bytes);
    std.debug.assert(std.mem.eql(u8, &root_cv, &computeUnkeyedBlake3(data)));
    return out;
}

/// Verifies a slice `slice_data` at `[slice_offset .. slice_offset + slice_len)` against `obao_bytes` and `expected_root`.
pub fn verifyBaoSlice(
    expected_root: [32]u8,
    obao_bytes: []const u8,
    slice_offset: u64,
    slice_len: u64,
    slice_data: []const u8,
    sink: ?*DiagnosticSink,
    span: Span,
) !void {
    if (obao_bytes.len < 8) {
        try emitIntegrityDiagnostic(sink, span, "truncated `.obao` Bao outboard header (`< 8` bytes)");
        return error.CacheIntegrityMismatch;
    }
    const total_len = std.mem.readInt(u64, obao_bytes[0..8], .little);
    const chunk_count: u64 = if (total_len == 0) 1 else (total_len + BLAKE3_CHUNK_LEN - 1) / BLAKE3_CHUNK_LEN;
    const expected_obao_len = std.math.add(
        usize,
        8,
        std.math.mul(usize, @intCast(chunk_count - 1), 64) catch {
            try emitIntegrityDiagnostic(sink, span, "overflowing `.obao` Bao parent node count");
            return error.CacheIntegrityMismatch;
        },
    ) catch {
        try emitIntegrityDiagnostic(sink, span, "overflowing `.obao` Bao outboard byte size");
        return error.CacheIntegrityMismatch;
    };
    if (obao_bytes.len != expected_obao_len) {
        try emitIntegrityDiagnostic(sink, span, "`.obao` Bao outboard length does not match declared blob size");
        return error.CacheIntegrityMismatch;
    }

    const slice_end_byte = std.math.add(u64, slice_offset, slice_len) catch {
        try emitIntegrityDiagnostic(sink, span, "Bao slice byte range overflows `u64`");
        return error.CacheIntegrityMismatch;
    };
    if (slice_end_byte > total_len) {
        try emitIntegrityDiagnostic(sink, span, "Bao slice range exceeds declared total blob length");
        return error.CacheIntegrityMismatch;
    }

    const slice_start_chunk: u64 = slice_offset / BLAKE3_CHUNK_LEN;
    const slice_end_chunk: u64 = if (total_len == 0 or slice_len == 0)
        slice_start_chunk + 1
    else
        (slice_end_byte + BLAKE3_CHUNK_LEN - 1) / BLAKE3_CHUNK_LEN;

    var obao_cursor: usize = 0;
    var data_cursor: usize = 0;
    const is_ok = verifyBaoSubtreeRecursive(
        expected_root,
        obao_bytes[8..],
        &obao_cursor,
        0,
        chunk_count,
        total_len,
        slice_start_chunk,
        @min(slice_end_chunk, chunk_count),
        slice_data,
        &data_cursor,
        true,
    );
    if (!is_ok or obao_cursor != obao_bytes.len - 8 or data_cursor != slice_data.len) {
        try emitIntegrityDiagnostic(sink, span, "Bao verified streaming slice failed BLAKE3 Merkle check");
        return error.CacheIntegrityMismatch;
    }
}

/// Verifies an entire `data` buffer against its companion `obao_bytes` and `expected_root` (`E0015` on failure).
pub fn verifyBaoOutboard(
    expected_root: [32]u8,
    obao_bytes: []const u8,
    data: []const u8,
    sink: ?*DiagnosticSink,
    span: Span,
) !void {
    return verifyBaoSlice(expected_root, obao_bytes, 0, data.len, data, sink, span);
}

// --------- Ed25519 & RFC 6962 Transparency-Log Proofs ---------

/// Verifies an `Ed25519` signature `sig_bytes` over `message` under `pub_key_bytes` (`catch` -> `E0015`).
pub fn verifyEd25519Signature(
    pub_key_bytes: [32]u8,
    message: []const u8,
    sig_bytes: [64]u8,
    sink: ?*DiagnosticSink,
    span: Span,
) !void {
    const public_key = std.crypto.sign.Ed25519.PublicKey.fromBytes(pub_key_bytes) catch {
        try emitIntegrityDiagnostic(sink, span, "non-canonical or invalid Ed25519 publisher public key");
        return error.CacheIntegrityMismatch;
    };
    const sig = std.crypto.sign.Ed25519.Signature.fromBytes(sig_bytes);
    sig.verify(message, public_key) catch {
        try emitIntegrityDiagnostic(sink, span, "Ed25519 package signature verification failed");
        return error.CacheIntegrityMismatch;
    };
}

/// Verifies a publisher `Ed25519` signature over `"corex-publish-v1\n<name>\n<version>\n<64-hex-tree>"` (`E0015`).
pub fn verifyPublisherSignature(
    allocator: std.mem.Allocator,
    pkg_name: []const u8,
    pkg_version: []const u8,
    tree_blake3: [32]u8,
    pub_key_bytes: [32]u8,
    sig_bytes: [64]u8,
    sink: ?*DiagnosticSink,
    span: Span,
) !void {
    const tree_hex = std.fmt.bytesToHex(tree_blake3, .lower);
    const payload = try std.fmt.allocPrint(
        allocator,
        "{s}{s}\n{s}\n{s}",
        .{ PUBLISH_SIG_DOMAIN_PREFIX, pkg_name, pkg_version, &tree_hex },
    );
    defer allocator.free(payload);
    try verifyEd25519Signature(pub_key_bytes, payload, sig_bytes, sink, span);
}

/// Computes RFC 6962 domain-separated Merkle leaf hash `BLAKE3(0x00 || leaf_bytes)`.
pub fn computeRfc6962LeafHash(leaf_bytes: []const u8) [32]u8 {
    var hasher = std.crypto.hash.Blake3.init(.{});
    hasher.update(&[1]u8{0x00});
    hasher.update(leaf_bytes);
    var out: [32]u8 = undefined;
    hasher.final(&out);
    return out;
}

/// Computes RFC 6962 domain-separated Merkle internal node hash `BLAKE3(0x01 || left || right)`.
pub fn computeRfc6962NodeHash(left: [32]u8, right: [32]u8) [32]u8 {
    var hasher = std.crypto.hash.Blake3.init(.{});
    hasher.update(&[1]u8{0x01});
    hasher.update(&left);
    hasher.update(&right);
    var out: [32]u8 = undefined;
    hasher.final(&out);
    return out;
}

/// Verifies an RFC 6962 / RFC 9162 Merkle inclusion proof for `leaf_bytes` at `leaf_index` in `tree_size` (`E0015`).
pub fn verifyMerkleInclusionProof(
    leaf_index: u64,
    tree_size: u64,
    leaf_bytes: []const u8,
    proof: []const [32]u8,
    expected_root: [32]u8,
    sink: ?*DiagnosticSink,
    span: Span,
) !void {
    if (tree_size == 0 or leaf_index >= tree_size or proof.len > 64) {
        try emitIntegrityDiagnostic(sink, span, "invalid RFC 6962 transparency-log inclusion proof bounds");
        return error.CacheIntegrityMismatch;
    }

    var fn_idx: u64 = leaf_index;
    var sn_idx: u64 = tree_size - 1;
    var running = computeRfc6962LeafHash(leaf_bytes);
    var proof_cursor: usize = 0;

    while (sn_idx > 0) {
        if ((fn_idx & 1) == 1) {
            if (proof_cursor >= proof.len) {
                try emitIntegrityDiagnostic(sink, span, "truncated RFC 6962 Merkle inclusion proof");
                return error.CacheIntegrityMismatch;
            }
            running = computeRfc6962NodeHash(proof[proof_cursor], running);
            proof_cursor += 1;
        } else if (fn_idx < sn_idx) {
            if (proof_cursor >= proof.len) {
                try emitIntegrityDiagnostic(sink, span, "truncated RFC 6962 Merkle inclusion proof");
                return error.CacheIntegrityMismatch;
            }
            running = computeRfc6962NodeHash(running, proof[proof_cursor]);
            proof_cursor += 1;
        }
        fn_idx >>= 1;
        sn_idx >>= 1;
    }

    if (proof_cursor != proof.len or !std.crypto.timing_safe.eql([32]u8, running, expected_root)) {
        try emitIntegrityDiagnostic(sink, span, "RFC 6962 transparency-log inclusion proof root mismatch");
        return error.CacheIntegrityMismatch;
    }
}

/// Verifies an RFC 6962 / RFC 9162 Merkle consistency proof from `first_size` (`first_root`) to `second_size` (`E0015`).
pub fn verifyMerkleConsistencyProof(
    first_size: u64,
    second_size: u64,
    proof: []const [32]u8,
    first_root: [32]u8,
    second_root: [32]u8,
    sink: ?*DiagnosticSink,
    span: Span,
) !void {
    if (first_size == 0 or first_size > second_size or proof.len > 64) {
        try emitIntegrityDiagnostic(sink, span, "invalid RFC 6962 transparency-log consistency bounds");
        return error.CacheIntegrityMismatch;
    }
    if (first_size == second_size) {
        if (proof.len != 0 or !std.crypto.timing_safe.eql([32]u8, first_root, second_root)) {
            try emitIntegrityDiagnostic(sink, span, "RFC 6962 consistency proof failed for equal tree sizes");
            return error.CacheIntegrityMismatch;
        }
        return;
    }
    if (proof.len == 0) {
        try emitIntegrityDiagnostic(sink, span, "empty RFC 6962 consistency proof for distinct tree sizes");
        return error.CacheIntegrityMismatch;
    }

    const is_pow2 = std.math.isPowerOfTwo(first_size);
    var fn_idx: u64 = first_size - 1;
    var sn_idx: u64 = second_size - 1;
    while ((fn_idx & 1) == 1) {
        fn_idx >>= 1;
        sn_idx >>= 1;
    }

    var proof_cursor: usize = 0;
    var first_running: [32]u8 = if (is_pow2) first_root else blk: {
        proof_cursor = 1;
        break :blk proof[0];
    };
    var second_running: [32]u8 = first_running;

    while (sn_idx > 0) {
        if (proof_cursor >= proof.len) {
            try emitIntegrityDiagnostic(sink, span, "truncated RFC 6962 Merkle consistency proof");
            return error.CacheIntegrityMismatch;
        }
        const next_node = proof[proof_cursor];
        proof_cursor += 1;

        if ((fn_idx & 1) == 1 or fn_idx == sn_idx) {
            first_running = computeRfc6962NodeHash(next_node, first_running);
            second_running = computeRfc6962NodeHash(next_node, second_running);
            while (fn_idx > 0 and (fn_idx & 1) == 0) {
                fn_idx >>= 1;
                sn_idx >>= 1;
            }
        } else {
            second_running = computeRfc6962NodeHash(second_running, next_node);
        }
        fn_idx >>= 1;
        sn_idx >>= 1;
    }

    if (proof_cursor != proof.len or
        !std.crypto.timing_safe.eql([32]u8, first_running, first_root) or
        !std.crypto.timing_safe.eql([32]u8, second_running, second_root))
    {
        try emitIntegrityDiagnostic(sink, span, "RFC 6962 transparency-log split-view / consistency mismatch");
        return error.CacheIntegrityMismatch;
    }
}

// ----------------- `vendor/` Materialization ------------------

/// Materializes verified `.cxtree` manifests, blobs, and `modules.toml` into `vendor_dir` (`reflink -> hardlink -> copy`).
pub fn materializeVendorDir(
    cache: *PkgCache,
    io: std.Io,
    vendor_dir: []const u8,
    packages: []const VendorPackageRecord,
    sink: ?*DiagnosticSink,
    span: Span,
) !VendorMaterializeStats {
    var stats = VendorMaterializeStats{};
    const trimmed_vendor = std.mem.trimEnd(u8, vendor_dir, "/\\");
    const vendor_blobs = try std.fmt.allocPrint(cache.allocator, "{s}/blake3/blobs", .{trimmed_vendor});
    defer cache.allocator.free(vendor_blobs);
    const vendor_trees = try std.fmt.allocPrint(cache.allocator, "{s}/blake3/trees", .{trimmed_vendor});
    defer cache.allocator.free(vendor_trees);
    try std.Io.Dir.cwd().createDirPath(io, vendor_blobs);
    try std.Io.Dir.cwd().createDirPath(io, vendor_trees);

    var modules_builder: std.ArrayList(u8) = .empty;
    defer modules_builder.deinit(cache.allocator);
    try modules_builder.appendSlice(
        cache.allocator,
        "# @generated by CoreX vendor. Do not edit manually.\nversion = 1\n",
    );

    var seen_blobs: std.AutoHashMapUnmanaged([32]u8, u64) = .empty;
    defer seen_blobs.deinit(cache.allocator);

    for (packages) |pkg_rec| {
        // [1] Verify `.cxtree` integrity before cloning into `<vendor_dir>/blake3/trees`:
        const cxtree_bytes = try cache.readVerifiedCxTreeAlloc(io, pkg_rec.tree_blake3, sink, span);
        defer cache.allocator.free(cxtree_bytes);
        const view = try vfs_sourcemap.validateCxTreeBytes(cache.allocator, cxtree_bytes);

        const tree_hex = std.fmt.bytesToHex(pkg_rec.tree_blake3, .lower);
        const src_tree_primary = try resolveShardedCasSourcePathAlloc(
            io,
            cache.allocator,
            cache.cas_root,
            "trees",
            ".cxtree",
            pkg_rec.tree_blake3,
        );
        defer cache.allocator.free(src_tree_primary);
        const dst_tree_path = try std.fmt.allocPrint(
            cache.allocator,
            "{s}/{s}/{s}.cxtree",
            .{ vendor_trees, tree_hex[0..2], tree_hex[2..64] },
        );
        defer cache.allocator.free(dst_tree_path);

        const tree_tier = try materializeImmutableFileTiered(io, cache.allocator, src_tree_primary, dst_tree_path);
        switch (tree_tier) {
            .cow_reflink => stats.reflink_count += 1,
            .hardlink => stats.hardlink_count += 1,
            .atomic_copy => stats.copy_count += 1,
        }

        // [2] Materialize each unique `file_blake3` blob referenced by `view` (verifying `file_size` parity):
        for (view.entries) |tree_entry| {
            const gop = try seen_blobs.getOrPut(cache.allocator, tree_entry.file_blake3);
            if (gop.found_existing) {
                if (gop.value_ptr.* != tree_entry.file_size) {
                    try emitIntegrityDiagnostic(
                        sink,
                        span,
                        "cached blob byte length does not match `.cxtree` `file_size`",
                    );
                    return error.CacheIntegrityMismatch;
                }
                continue;
            }
            const verified_blob = try cache.readVerifiedBlobAlloc(io, tree_entry.file_blake3, sink, span);
            defer cache.allocator.free(verified_blob);
            if (verified_blob.len != tree_entry.file_size) {
                _ = seen_blobs.remove(tree_entry.file_blake3);
                try emitIntegrityDiagnostic(
                    sink,
                    span,
                    "cached blob byte length does not match `.cxtree` `file_size`",
                );
                return error.CacheIntegrityMismatch;
            }
            gop.value_ptr.* = verified_blob.len;

            const blob_hex = std.fmt.bytesToHex(tree_entry.file_blake3, .lower);
            const src_blob = try resolveShardedCasSourcePathAlloc(
                io,
                cache.allocator,
                cache.cas_root,
                "blobs",
                "",
                tree_entry.file_blake3,
            );
            defer cache.allocator.free(src_blob);
            const dst_blob = try std.fmt.allocPrint(
                cache.allocator,
                "{s}/{s}/{s}",
                .{ vendor_blobs, blob_hex[0..2], blob_hex[2..64] },
            );
            defer cache.allocator.free(dst_blob);

            const blob_tier = try materializeImmutableFileTiered(io, cache.allocator, src_blob, dst_blob);
            switch (blob_tier) {
                .cow_reflink => stats.reflink_count += 1,
                .hardlink => stats.hardlink_count += 1,
                .atomic_copy => stats.copy_count += 1,
            }
        }

        const mod_entry = try std.fmt.allocPrint(
            cache.allocator,
            "\n[[package]]\nname = \"{s}\"\nversion = \"{s}\"\nsource = \"{s}\"\ntree_hash = \"b3:{s}\"\n",
            .{ pkg_rec.name, pkg_rec.version, pkg_rec.source, &tree_hex },
        );
        defer cache.allocator.free(mod_entry);
        try modules_builder.appendSlice(cache.allocator, mod_entry);
    }

    // [3] Atomically write `<vendor_dir>/modules.toml`:
    const modules_tmp = try std.fmt.allocPrint(cache.allocator, "{s}/modules.toml.tmp", .{trimmed_vendor});
    defer cache.allocator.free(modules_tmp);
    const modules_dst = try std.fmt.allocPrint(cache.allocator, "{s}/modules.toml", .{trimmed_vendor});
    defer cache.allocator.free(modules_dst);

    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = modules_tmp, .data = modules_builder.items });
    std.Io.Dir.cwd().deleteFile(io, modules_dst) catch {};
    try std.Io.Dir.rename(std.Io.Dir.cwd(), modules_tmp, std.Io.Dir.cwd(), modules_dst, io);
    return stats;
}

// ---------------------------------------- MAIN -----------------------------------------

comptime {
    std.debug.assert(@sizeOf(LruCacheKey) == 40 and @alignOf(LruCacheKey) == 1);
    std.debug.assert(@sizeOf(CxTreeHeader) == 32 and @alignOf(CxTreeHeader) == 8);
    std.debug.assert(@sizeOf(CxTreeEntry) == 48 and @alignOf(CxTreeEntry) == 8);
}
