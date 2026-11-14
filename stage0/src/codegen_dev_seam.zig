//! CoreX Stage-0 Forward-Compatible Hot-Reload & SIMD Metadata Seam
//!
//! Implements `DR-19` §1 and `DR-20` Seam Checklist `#3`–`#4` within the strict `< 200` LOC
//! Phase-7 seam budget: 64-byte `CxDevSeamHeader`, 24-byte `CxGotSlotMeta`, 32-byte
//! `CxTypeLayoutRecord`, 64-byte `CxReloadControlBlock`, re-exported `LoopContractMeta` (`8B`),
//! and little-endian `.cx_dev_meta` binary section serialization and validation.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const hir = @import("hir.zig");
const query_db = @import("query_db.zig");

/// Re-exported canonical 32-bit `TypeId` handle.
pub const TypeId = mem_foundation.TypeId;
/// Re-exported workspace-global 32-bit `DefId` handle.
pub const DefId = query_db.DefId;
/// Re-exported canonical 32-bit `DiagId` handle.
pub const DiagId = mem_foundation.DiagId;
/// Re-exported 1-byte `@must_vectorize` / `@vectorize_width` contract flags (`DR-20` Seam `#4`).
pub const LoopContractMask = hir.LoopContractMask;
/// Re-exported 8-byte SIMD loop contract payload (`DR-19` §1.2, `DR-20` Seam `#4`).
pub const LoopContractMeta = hir.LoopContractMeta;

// ---------------------------------------- TYPES ----------------------------------------

/// 64-byte header emitted at byte offset `+0` of `.cx_dev_meta` in `--dev` builds (`DR-19` §1.2).
pub const CxDevSeamHeader = extern struct {
    magic: [8]u8 = CX_DEV_SEAM_MAGIC,
    seam_version: u16 = CX_DEV_SEAM_VERSION,
    arch_os_tag: u16 = 0,
    seam_flags: u32 = 0,
    got_slot_count: u32 = 0,
    type_record_count: u32 = 0,
    static_root_count: u32 = 0,
    loop_contract_count: u32 = 0,
    build_id_lo: u64 = 0,
    build_id_hi: u64 = 0,
    got_rva: u64 = 0,
    ctrl_block_rva: u64 = 0,
};

/// 24-byte descriptor per indirect `.cx_got[got_idx]` callable, closure, or vtable slot (`DR-19` §1.2).
pub const CxGotSlotMeta = extern struct {
    def_id: DefId = .NONE,
    got_idx: u32 = 0,
    abi_sig_hash64: u64 = 0,
    flags: u16 = 0,
    slot_kind: SlotKind = .direct_fn,
    pad0: u8 = 0,
    atom_alloc_cap: u32 = 0,

    /// Callable category dispatched through `.cx_got[got_idx]`.
    pub const SlotKind = enum(u8) {
        direct_fn = 0,
        closure_invoke = 1,
        trait_vtable_entry = 2,
        coro_poll_fn = 3,
    };
};

/// 32-byte layout equivalence record pairing physical `layout_shape_hash64` with `field_hash64` (`DR-19` §1.2).
pub const CxTypeLayoutRecord = extern struct {
    type_id: TypeId,
    byte_size: u32,
    align_log2: u8,
    kind_flags: u8 = 0,
    fields_len: u16 = 0,
    fqn_hash32: u32 = 0,
    layout_shape_hash64: u64 = 0,
    field_hash64: u64 = 0,
};

/// 64-byte runtime safepoint control block emitted into `.cx_dev_ctrl` on a `128B` boundary (`DR-19` §1.2).
pub const CxReloadControlBlock = extern struct {
    pending_patch_gen: u64 = 0,
    applied_patch_gen: u64 = 0,
    ipc_shm_offset: u64 = 0,
    active_workers: u32 = 1,
    arrived_workers: u32 = 0,
    reload_action: u32 = 0,
    status_flags: u32 = 0,
    root_state_addr: u64 = 0,
    root_type_id: u32 = 0xFFFF_FFFF,
    patched_fn_count: u32 = 0,
    root_field_hash64: u64 = 0,
};

/// Error set returned when validating a serialized `.cx_dev_meta` byte buffer.
pub const DevSeamDeserializeError = error{
    TruncatedHeader,
    InvalidMagic,
    UnsupportedVersion,
    PayloadSizeMismatch,
};

/// Zero-copy validated view over a `.cx_dev_meta` binary section payload.
pub const DevSeamMetaView = struct {
    header: CxDevSeamHeader,
    got_slots: []align(1) const CxGotSlotMeta,
    type_records: []align(1) const CxTypeLayoutRecord,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical 8-byte magic sequence at offset `+0` of `.cx_dev_meta`.
pub const CX_DEV_SEAM_MAGIC: [8]u8 = .{ 'C', 'X', 'D', 'E', 'V', '0', '1', 0 };
/// Canonical Phase-7 `.cx_dev_meta` schema version (`1`).
pub const CX_DEV_SEAM_VERSION: u16 = 1;

// ------------------------------------- PUBLIC API --------------------------------------

/// Computes `DR-19` §1.3 `Wyhash(0)` semantic `FieldHash64` from FQN, tier flags, shape, and member digests.
pub fn computeFieldHash64(
    fqn_bytes: []const u8,
    ownership_tier_flags: u8,
    layout_shape_hash64: u64,
    member_hashes: []const u64,
) u64 {
    var hasher = std.hash.Wyhash.init(0);
    hasher.update(fqn_bytes);
    hasher.update(&[_]u8{ownership_tier_flags});
    hasher.update(std.mem.asBytes(&layout_shape_hash64));
    hasher.update(std.mem.sliceAsBytes(member_hashes));
    return hasher.final();
}

/// Serializes `header`, `got_slots`, and `type_records` into a contiguous `.cx_dev_meta` byte buffer.
pub fn serializeDevSeamMeta(
    allocator: std.mem.Allocator,
    header: CxDevSeamHeader,
    got_slots: []const CxGotSlotMeta,
    type_records: []const CxTypeLayoutRecord,
) ![]u8 {
    if (got_slots.len > std.math.maxInt(u32) or type_records.len > std.math.maxInt(u32)) return error.OutOfMemory;
    var normalized_hdr = header;
    normalized_hdr.magic = CX_DEV_SEAM_MAGIC;
    normalized_hdr.seam_version = CX_DEV_SEAM_VERSION;
    normalized_hdr.got_slot_count = @intCast(got_slots.len);
    normalized_hdr.type_record_count = @intCast(type_records.len);
    const got_bytes_len = try std.math.mul(usize, got_slots.len, @sizeOf(CxGotSlotMeta));
    const type_bytes_len = try std.math.mul(usize, type_records.len, @sizeOf(CxTypeLayoutRecord));
    const payload_len = try std.math.add(usize, got_bytes_len, type_bytes_len);
    const out = try allocator.alloc(u8, try std.math.add(usize, @sizeOf(CxDevSeamHeader), payload_len));
    @memcpy(out[0..@sizeOf(CxDevSeamHeader)], std.mem.asBytes(&normalized_hdr));
    if (got_bytes_len > 0) @memcpy(out[64 .. 64 + got_bytes_len], std.mem.sliceAsBytes(got_slots));
    if (type_bytes_len > 0) @memcpy(out[64 + got_bytes_len ..], std.mem.sliceAsBytes(type_records));
    return out;
}

/// Validates and decodes a `.cx_dev_meta` byte slice into a zero-copy `DevSeamMetaView`.
pub fn deserializeDevSeamMeta(bytes: []const u8) DevSeamDeserializeError!DevSeamMetaView {
    if (bytes.len < @sizeOf(CxDevSeamHeader)) return error.TruncatedHeader;
    var hdr: CxDevSeamHeader = undefined;
    @memcpy(std.mem.asBytes(&hdr), bytes[0..@sizeOf(CxDevSeamHeader)]);
    if (!std.mem.eql(u8, &hdr.magic, &CX_DEV_SEAM_MAGIC)) return error.InvalidMagic;
    if (hdr.seam_version != CX_DEV_SEAM_VERSION) return error.UnsupportedVersion;
    const got_bytes = std.math.mul(usize, hdr.got_slot_count, @sizeOf(CxGotSlotMeta)) catch return error.PayloadSizeMismatch;
    const type_bytes = std.math.mul(usize, hdr.type_record_count, @sizeOf(CxTypeLayoutRecord)) catch return error.PayloadSizeMismatch;
    const payload_bytes = std.math.add(usize, got_bytes, type_bytes) catch return error.PayloadSizeMismatch;
    const expected_bytes = std.math.add(usize, @sizeOf(CxDevSeamHeader), payload_bytes) catch return error.PayloadSizeMismatch;
    if (bytes.len != expected_bytes) return error.PayloadSizeMismatch;
    return .{
        .header = hdr,
        .got_slots = std.mem.bytesAsSlice(CxGotSlotMeta, bytes[64 .. 64 + got_bytes]),
        .type_records = std.mem.bytesAsSlice(CxTypeLayoutRecord, bytes[64 + got_bytes ..]),
    };
}

comptime {
    std.debug.assert(@sizeOf(CxDevSeamHeader) == 64 and @alignOf(CxDevSeamHeader) == 8);
    std.debug.assert(@sizeOf(CxGotSlotMeta) == 24 and @alignOf(CxGotSlotMeta) == 8);
    std.debug.assert(@sizeOf(CxTypeLayoutRecord) == 32 and @alignOf(CxTypeLayoutRecord) == 8);
    std.debug.assert(@sizeOf(LoopContractMask) == 1 and @bitSizeOf(LoopContractMask) == 8 and @sizeOf(LoopContractMeta) == 8);
    std.debug.assert(@sizeOf(CxReloadControlBlock) == 64 and @alignOf(CxReloadControlBlock) == 8);
}
