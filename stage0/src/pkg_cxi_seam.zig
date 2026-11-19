//! CoreX Stage-0 `.cxi` Public-Interface & Capability Digest Seam
//!
//! Defines the zero-padding 8-byte-aligned binary `.cxi` summary records (`64B` `CxiHeader`,
//! `64B` `CxiFnRecord`, and `40B` `CxiTypeRecord`), canonical serializer, and keyed `BLAKE3` digest.
//!
//! Implements `DR-17` §4.3 and `DR-20` `D-08` Seam `#7` using domain-separated KDF context
//! `"corex.cxi.v1.2026-04"` for `corex.lock` interface pinning and Early-Cutoff verification.

const std = @import("std");

// ---------------------------------------- TYPES ----------------------------------------

/// Exact 64-byte (`512`-bit, `align(8)`, `0` padding) binary header at offset `+0` of a `.cxi` summary.
pub const CxiHeader = extern struct {
    /// Four-byte `.cxi` magic signature (`"CXI1"`).
    magic: [4]u8 = "CXI1".*,
    /// Binary `.cxi` schema version (`1`).
    schema_version: u16 = 1,
    /// Exported `pub` surface `EffectCapabilityMask` bits (`LOCKFILE_CAP_BITS`).
    surface_caps: u16 = 0,
    /// Package-wide unconditional ambient `EffectCapabilityMask` bits.
    ambient_caps: u16 = 0,
    /// Zeroed reserved header words preserving 8-byte alignment of `body_byte_len`.
    reserved_u16: [3]u16 = .{ 0, 0, 0 },
    /// Count of sorted `CxiFnRecord` entries immediately following this header.
    pub_fn_count: u32 = 0,
    /// Count of sorted `CxiTypeRecord` entries (nominal/alias types and `pub const` digests) following the function table.
    pub_type_count: u32 = 0,
    /// Total payload byte length following this 64-byte header (`pub_fn_count * 64 + pub_type_count * 40`).
    body_byte_len: u64 = 0,
    /// Domain-separated 256-bit `BLAKE3` digest over `(surface_caps, ambient_caps, body_bytes)`.
    cxi_digest: [32]u8 = @splat(0),
};

/// Exact 64-byte (`512`-bit, `align(8)`, `0` padding) record per exported `pub fn` or `pub trait` method.
pub const CxiFnRecord = extern struct { symbol_path_hash: u64 = 0, sig_type_hash: u64 = 0, shape_hash64: u64 = 0, summary_bits: [5]u64 = @splat(0) };
/// Exact 40-byte (`320`-bit, `align(8)`, `0` padding) record per exported `pub` nominal/alias type or `pub const` (`0x8000_0000` tag).
pub const CxiTypeRecord = extern struct { symbol_path_hash: u64 = 0, shape_hash64: u64 = 0, field_hash64: u64 = 0, layout_meta: [4]u32 = @splat(0) };

// ------------------------------------- PUBLIC API --------------------------------------

/// Computes the keyed 256-bit `cxi_blake3` digest over little-endian `(surface_caps, ambient_caps, body_bytes)`.
pub fn computeCxiBlake3(surface_caps: u16, ambient_caps: u16, body_bytes: []const u8) [32]u8 {
    var hasher = std.crypto.hash.Blake3.initKdf("corex.cxi.v1.2026-04", .{});
    hasher.update(std.mem.asBytes(&[2]u16{ std.mem.nativeToLittle(u16, surface_caps), std.mem.nativeToLittle(u16, ambient_caps) }));
    hasher.update(body_bytes);
    var digest: [32]u8 = undefined;
    hasher.final(&digest);
    return digest;
}

/// Serializes pre-sorted `fns` and `types` (`symbol_path_hash ASC`) into an 8-byte-aligned `.cxi` summary buffer.
pub fn serializeCxiSummary(alloc: std.mem.Allocator, surf: u16, amb: u16, fns: []const CxiFnRecord, types: []const CxiTypeRecord) ![]align(8) u8 {
    if (fns.len > std.math.maxInt(u32) or types.len > std.math.maxInt(u32)) return error.Overflow;
    inline for (.{ fns, types }) |recs| for (recs, 0..) |rec, i| if (i > 0) std.debug.assert(recs[i - 1].symbol_path_hash <= rec.symbol_path_hash);
    const fn_end = try std.math.add(usize, 64, try std.math.mul(usize, fns.len, 64));
    const buf = try alloc.alignedAlloc(u8, .@"8", try std.math.add(usize, fn_end, try std.math.mul(usize, types.len, 40)));
    @memcpy(buf[64..fn_end], std.mem.sliceAsBytes(fns));
    @memcpy(buf[fn_end..], std.mem.sliceAsBytes(types));
    const hdr = std.mem.bytesAsValue(CxiHeader, buf[0..64]);
    hdr.* = .{ .surface_caps = surf, .ambient_caps = amb, .pub_fn_count = @intCast(fns.len), .pub_type_count = @intCast(types.len) };
    hdr.body_byte_len = buf.len - 64;
    hdr.cxi_digest = computeCxiBlake3(surf, amb, buf[64..]);
    return buf;
}
