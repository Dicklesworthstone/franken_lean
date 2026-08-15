//! Marrow's compacted-region engine (bead fln-wgp, plan §6.4) — relocation,
//! structural audit, graph materialization, and region construction, all in
//! safe Rust over byte slices.
//!
//! The wire semantics mirror the pinned Reference exactly
//! (`vendor/lean4-src/src/runtime/compact.cpp`):
//!
//! * a region is `[root word][objects…]` — the compactor reserves the root
//!   word first, lays objects out in post-order (children before parents,
//!   `operator()`, compact.cpp:167-205), then patches the root;
//! * stored pointers are absolute against the header's `base_addr`; loading
//!   at `target` rewrites each by `target - base` (`region_reader::read`,
//!   compact.cpp:663-734), scalars (odd words) pass through untouched;
//! * per-category fixups: ctor/array/closure fix child slots; thunk, ref,
//!   task, promise fix exactly one slot (a thunk's `m_closure` is NOT fixed
//!   — the Reference leaves it, compact.cpp:622-625); scalar arrays and
//!   strings move without fixes; mpz relocates its inline limb pointer;
//!   external objects cannot appear (compact.cpp:194);
//! * object byte sizes: small-path categories carry their exact size in
//!   `m_cs_sz` (`lean_set_non_heap_header`, compact.cpp:238); big-path
//!   categories (array/sarray/string) store the sentinel `1` and compute
//!   from salient fields; every step advances by the size rounded up to 8
//!   (`region_reader::move`, compact.cpp:590-596).
//!
//! Everything is offset arithmetic over `&[u8]`/`&mut [u8]` — the engine
//! needs no unsafe. Malformed input yields a typed [`RegionFault`], never a
//! panic and never a silently-partial success (FL-INV-07), and every walk is
//! linear and budget-free by construction (one pass over the buffer, ≥ 8
//! bytes consumed per step, no recursion).
//!
//! The mmap primitive driving this engine at production addresses is
//! `fln_unsafe_region::mapping::RegionMapping`; the olean envelope subset
//! lives in the generated [`crate::region_contract`] partition.

use crate::abi;
use crate::obj::Obj;
use crate::region_contract as rc;
use std::collections::HashMap;

/// Envelope framings this shared reader actually implements. The generated
/// Envelope framings implemented by the shared reader. Closure objects inside
/// a v3 payload remain a separate, typed-unsupported runtime category until
/// the relocation table is wired into the object walk.
const OLEAN_READER_VERSIONS: &[u8] = &[2, 3];

/// Typed region failure. Payload-walk variants carry payload-relative offsets;
/// [`RegionFault::MalformedV3`] instead names the offending file-framing byte.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegionFault {
    /// Payload shorter than the fixed envelope or a read past its end.
    Truncated { offset: usize, wanted: usize },
    /// Envelope magic differs from the generated contract's.
    BadMagic,
    /// Envelope version outside this reader's implemented framing set.
    UnsupportedVersion(u8),
    /// A v3 length-prefixed section is truncated or structurally incoherent.
    MalformedV3 { offset: usize, reason: &'static str },
    /// `base_addr` violates the contract's alignment law.
    MisalignedBase { base: u64 },
    /// Payload length is not a whole number of 8-byte words.
    RaggedPayload { len: usize },
    /// A compacted object whose reference count is not the persistent 0.
    NonPersistentRc { offset: usize, rc: i32 },
    /// A stored pointer resolves outside the region.
    PtrOutOfBounds { offset: usize, ptr: u64 },
    /// A stored pointer is not 8-byte aligned.
    MisalignedPtr { offset: usize, ptr: u64 },
    /// An object byte size that underruns its category minimum.
    BadObjectSize { offset: usize, size: usize },
    /// A tag that cannot appear in a compacted region.
    ForbiddenTag { offset: usize, tag: u8 },
    /// Closures cannot be relocated or materialized in slice 1 (their
    /// `m_fun` needs the library relocation table — plugin-door beads).
    ClosureUnsupported { offset: usize },
    /// String object violating its stored size/length/NUL/UTF-8 laws.
    StringIntegrity { offset: usize, reason: &'static str },
    /// Array object whose `m_size` is past `m_capacity`.
    ArrayIntegrity { offset: usize },
    /// Mpz object with an incoherent limb block.
    MpzIntegrity { offset: usize },
    /// The category is legal but this operation does not support it.
    UnsupportedCategory { tag: u8, operation: &'static str },
    /// Construction input exceeded a contract bound (ctor shape, size…).
    BuildShape { reason: &'static str },
}

impl std::fmt::Display for RegionFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Truncated { offset, wanted } => {
                write!(f, "truncated at offset {offset} (wanted {wanted} bytes)")
            }
            Self::BadMagic => write!(f, "bad olean magic"),
            Self::UnsupportedVersion(v) => write!(f, "unsupported olean version {v}"),
            Self::MalformedV3 { offset, reason } => {
                write!(f, "malformed olean v3 section at {offset}: {reason}")
            }
            Self::MisalignedBase { base } => write!(f, "misaligned base_addr {base:#x}"),
            Self::RaggedPayload { len } => write!(f, "payload length {len} not word-aligned"),
            Self::NonPersistentRc { offset, rc } => {
                write!(f, "object at {offset} has non-persistent rc {rc}")
            }
            Self::PtrOutOfBounds { offset, ptr } => {
                write!(f, "pointer {ptr:#x} at {offset} out of bounds")
            }
            Self::MisalignedPtr { offset, ptr } => {
                write!(f, "pointer {ptr:#x} at {offset} misaligned")
            }
            Self::BadObjectSize { offset, size } => {
                write!(f, "object at {offset} has impossible size {size}")
            }
            Self::ForbiddenTag { offset, tag } => write!(f, "forbidden tag {tag} at {offset}"),
            Self::ClosureUnsupported { offset } => {
                write!(f, "closure at {offset} needs the library relocation table")
            }
            Self::StringIntegrity { offset, reason } => {
                write!(f, "string at {offset}: {reason}")
            }
            Self::ArrayIntegrity { offset } => write!(f, "array at {offset} incoherent"),
            Self::MpzIntegrity { offset } => write!(f, "mpz at {offset} incoherent"),
            Self::UnsupportedCategory { tag, operation } => {
                write!(f, "category tag {tag} unsupported by {operation}")
            }
            Self::BuildShape { reason } => write!(f, "build shape: {reason}"),
        }
    }
}

impl std::error::Error for RegionFault {}

type RResult<T> = Result<T, RegionFault>;

/// The parsed olean envelope: version, stored base, and payload bounds
/// (byte offsets into the FILE image).
///
/// Pointer-base law: the Reference maps the WHOLE FILE at `base_addr`
/// (header included), so stored pointers are file-relative addresses; the
/// payload's own pointer base is therefore `base_addr + payload_offset`
/// ([`payload_base`](Self::payload_base)) — pass THAT as `from` when
/// relocating the payload slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OleanEnvelope {
    pub version: u8,
    pub base_addr: u64,
    pub payload_offset: usize,
    pub payload_len: usize,
}

fn checked_section_end(
    start: usize,
    len: usize,
    file_len: usize,
    reason: &'static str,
) -> RResult<usize> {
    let end = start.checked_add(len).ok_or(RegionFault::MalformedV3 {
        offset: start,
        reason,
    })?;
    if end > file_len {
        return Err(RegionFault::MalformedV3 {
            offset: start,
            reason,
        });
    }
    Ok(end)
}

fn read_v3_u32(file: &[u8], offset: usize, reason: &'static str) -> RResult<u32> {
    let end = checked_section_end(offset, size_of::<u32>(), file.len(), reason)?;
    Ok(u32::from_le_bytes(
        file[offset..end].try_into().expect("checked u32 width"),
    ))
}

fn read_v3_u64(file: &[u8], offset: usize, reason: &'static str) -> RResult<u64> {
    let end = checked_section_end(offset, size_of::<u64>(), file.len(), reason)?;
    Ok(u64::from_le_bytes(
        file[offset..end].try_into().expect("checked u64 width"),
    ))
}

impl OleanEnvelope {
    /// The pointer base of the payload slice (see the type docs).
    pub fn payload_base(&self) -> u64 {
        self.base_addr + self.payload_offset as u64
    }
}

fn header_field(name: &str) -> (usize, usize) {
    let f = rc::OLEAN_HEADER_FIELDS
        .iter()
        .find(|f| f.name == name)
        .expect("generated header table names the field");
    (f.offset, f.size)
}

/// Parse the olean envelope with the generated contract's layout.
pub fn parse_olean_envelope(file: &[u8]) -> RResult<OleanEnvelope> {
    if file.len() < rc::OLEAN_HEADER_SIZE {
        return Err(RegionFault::Truncated {
            offset: 0,
            wanted: rc::OLEAN_HEADER_SIZE,
        });
    }
    let (magic_off, magic_sz) = header_field("marker");
    if &file[magic_off..magic_off + magic_sz] != rc::OLEAN_MAGIC.as_slice() {
        return Err(RegionFault::BadMagic);
    }
    let (ver_off, _) = header_field("version");
    let version = file[ver_off];
    if !rc::OLEAN_ACCEPTED_VERSIONS.contains(&version) {
        return Err(RegionFault::UnsupportedVersion(version));
    }
    if !OLEAN_READER_VERSIONS.contains(&version) {
        return Err(RegionFault::UnsupportedVersion(version));
    }
    let (base_off, base_sz) = header_field("base_addr");
    let base_addr = u64::from_le_bytes(
        file[base_off..base_off + base_sz]
            .try_into()
            .expect("contract-sized field"),
    );
    if !(base_addr as usize).is_multiple_of(rc::REGION_ALIGN) {
        return Err(RegionFault::MisalignedBase { base: base_addr });
    }
    // The one envelope law the rest of the codec leans on: the payload's pointer
    // base plus the file's extent must fit a u64, or every base+offset add
    // downstream either panics (debug) or wraps into an address the audit then
    // cannot tell from a valid one (fln-abaz finding 3).
    let (data_off, _) = header_field("data");
    let extent = base_addr
        .checked_add(file.len() as u64)
        .ok_or(RegionFault::MisalignedBase { base: base_addr })?;
    let _ = extent;

    let (payload_offset, payload_len) = if version == 2 {
        (data_off, file.len() - data_off)
    } else {
        let word_size = base_sz;
        if word_size != size_of::<u64>() {
            return Err(RegionFault::MalformedV3 {
                offset: data_off,
                reason: "generated size_t width is unsupported",
            });
        }
        let data_size = usize::try_from(read_v3_u64(
            file,
            data_off,
            "missing or overflowing data-size prefix",
        )?)
        .map_err(|_| RegionFault::MalformedV3 {
            offset: data_off,
            reason: "data size does not fit the host address space",
        })?;
        let payload_offset = data_off
            .checked_add(word_size)
            .ok_or(RegionFault::MalformedV3 {
                offset: data_off,
                reason: "payload offset overflows",
            })?;
        let payload_end = checked_section_end(
            payload_offset,
            data_size,
            file.len(),
            "data section exceeds the file",
        )?;

        let closure_count = usize::try_from(read_v3_u32(
            file,
            payload_end,
            "missing closure-offset count",
        )?)
        .expect("u32 fits usize");
        let closure_table = payload_end + size_of::<u32>();
        let closure_bytes =
            closure_count
                .checked_mul(size_of::<u64>())
                .ok_or(RegionFault::MalformedV3 {
                    offset: closure_table,
                    reason: "closure-offset table size overflows",
                })?;
        let mut cursor = checked_section_end(
            closure_table,
            closure_bytes,
            file.len(),
            "closure-offset table exceeds the file",
        )?;
        for index in 0..closure_count {
            let offset = usize::try_from(read_v3_u64(
                file,
                closure_table + index * size_of::<u64>(),
                "truncated closure offset",
            )?)
            .map_err(|_| RegionFault::MalformedV3 {
                offset: closure_table + index * size_of::<u64>(),
                reason: "closure offset does not fit the host address space",
            })?;
            if !offset.is_multiple_of(size_of::<u64>())
                || offset
                    .checked_add(size_of::<u64>())
                    .is_none_or(|end| end > data_size)
            {
                return Err(RegionFault::MalformedV3 {
                    offset: closure_table + index * size_of::<u64>(),
                    reason: "closure m_fun offset is outside the data section",
                });
            }
        }

        let library_count = usize::try_from(read_v3_u32(
            file,
            cursor,
            "missing library-relocation count",
        )?)
        .expect("u32 fits usize");
        cursor += size_of::<u32>();
        for _ in 0..library_count {
            cursor = checked_section_end(
                cursor,
                word_size,
                file.len(),
                "truncated library base address",
            )?;
            let id_len = usize::try_from(read_v3_u32(
                file,
                cursor,
                "missing library identifier length",
            )?)
            .expect("u32 fits usize");
            cursor += size_of::<u32>();
            cursor = checked_section_end(
                cursor,
                id_len,
                file.len(),
                "library identifier exceeds the file",
            )?;
        }
        if cursor != file.len() {
            return Err(RegionFault::MalformedV3 {
                offset: cursor,
                reason: "trailing bytes follow the relocation table",
            });
        }
        (payload_offset, data_size)
    };
    Ok(OleanEnvelope {
        version,
        base_addr,
        payload_offset,
        payload_len,
    })
}

/// Relocation/audit report: one entry per completed walk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RegionReport {
    /// Objects visited in the linear walk.
    pub objects: u64,
    /// Pointer fields rewritten (0 when `from == to`).
    pub pointers_fixed: u64,
    /// The root word after the walk (a `to`-based address or boxed scalar).
    pub root: u64,
    /// Payload bytes walked.
    pub bytes: usize,
}

// ---- little helpers over the byte buffer -----------------------------------

fn need(buf: &[u8], offset: usize, wanted: usize) -> RResult<()> {
    if offset.checked_add(wanted).is_none_or(|end| end > buf.len()) {
        return Err(RegionFault::Truncated { offset, wanted });
    }
    Ok(())
}

fn read_u64(buf: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(buf[offset..offset + 8].try_into().expect("bounds checked"))
}

fn write_u64(buf: &mut [u8], offset: usize, v: u64) {
    buf[offset..offset + 8].copy_from_slice(&v.to_le_bytes());
}

fn read_u32(buf: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(buf[offset..offset + 4].try_into().expect("bounds checked"))
}

fn read_i32(buf: &[u8], offset: usize) -> i32 {
    read_u32(buf, offset) as i32
}

fn is_scalar_word(v: u64) -> bool {
    v & 1 == 1
}

fn round8(v: usize) -> usize {
    v.div_ceil(8) * 8
}

/// Loaded region header (byte offsets 0..8 of an object).
struct RHeader {
    rc: i32,
    cs_sz: u16,
    other: u8,
    tag: u8,
}

fn read_header(buf: &[u8], offset: usize) -> RHeader {
    RHeader {
        rc: read_i32(buf, offset),
        cs_sz: u16::from_le_bytes(buf[offset + 4..offset + 6].try_into().expect("bounds")),
        other: buf[offset + 6],
        tag: buf[offset + 7],
    }
}

// Fixed struct sizes on the certified LP64 layout, all asserted against the
// generated contract by the fln-unsafe-abi layout suite.
const HDR: usize = 8;
const ARRAY_FIXED: usize = 24; // header + m_size + m_capacity
const SARRAY_FIXED: usize = 24;
const STRING_FIXED: usize = 32; // header + size + capacity + length
const THUNK_SIZE: usize = 24;
const REF_SIZE: usize = 16;
const TASK_SIZE: usize = 24;
const PROMISE_SIZE: usize = 16;
const MPZ_FIXED: usize = 24; // header + _mp_alloc/_mp_size + limb ptr

/// One walked object: its payload span and the byte offsets (within the
/// payload) of every pointer word the Reference's reader would fix.
struct WalkStep {
    /// Total (unrounded) byte size of the object.
    size: usize,
    /// Payload-relative offsets of child pointer words.
    ptr_fields: Vec<usize>,
    /// Payload-relative offset of the mpz limb pointer, if any.
    limb_ptr: Option<usize>,
}

/// Decode one region object at `offset`, mirroring the reader's per-category
/// dispatch. Pure inspection — no writes.
fn walk_step(buf: &[u8], offset: usize) -> RResult<WalkStep> {
    need(buf, offset, HDR)?;
    let h = read_header(buf, offset);
    if h.rc != 0 {
        return Err(RegionFault::NonPersistentRc { offset, rc: h.rc });
    }
    let mut ptr_fields = Vec::new();
    let mut limb_ptr = None;
    let size = if h.tag <= abi::TAG_MAX_CTOR_TAG {
        let size = usize::from(h.cs_sz);
        let min = HDR + 8 * usize::from(h.other);
        if size < min || !size.is_multiple_of(8) {
            return Err(RegionFault::BadObjectSize { offset, size });
        }
        need(buf, offset, size)?;
        for i in 0..usize::from(h.other) {
            ptr_fields.push(offset + HDR + 8 * i);
        }
        size
    } else if h.tag == abi::TAG_ARRAY {
        need(buf, offset, ARRAY_FIXED)?;
        let n =
            usize::try_from(read_u64(buf, offset + 8)).map_err(|_| RegionFault::BadObjectSize {
                offset,
                size: usize::MAX,
            })?;
        let cap = usize::try_from(read_u64(buf, offset + 16)).map_err(|_| {
            RegionFault::BadObjectSize {
                offset,
                size: usize::MAX,
            }
        })?;
        if n > cap {
            return Err(RegionFault::BadObjectSize { offset, size: n });
        }
        let size = ARRAY_FIXED
            .checked_add(
                cap.checked_mul(8)
                    .ok_or(RegionFault::BadObjectSize { offset, size: cap })?,
            )
            .ok_or(RegionFault::BadObjectSize { offset, size: cap })?;
        need(buf, offset, size)?;
        for i in 0..n {
            ptr_fields.push(offset + ARRAY_FIXED + 8 * i);
        }
        size
    } else if h.tag == abi::TAG_SCALAR_ARRAY {
        need(buf, offset, SARRAY_FIXED)?;
        // `m_other` is the element size. Zero is not a Lean sarray: the
        // materializer would hit `Obj::mk_sarray`'s `elem_size > 0` assert
        // (FL-INV-07). Refuse here so audit/relocate/materialize agree.
        if h.other == 0 {
            return Err(RegionFault::BadObjectSize { offset, size: 0 });
        }
        let n =
            usize::try_from(read_u64(buf, offset + 8)).map_err(|_| RegionFault::BadObjectSize {
                offset,
                size: usize::MAX,
            })?;
        let cap = usize::try_from(read_u64(buf, offset + 16)).map_err(|_| {
            RegionFault::BadObjectSize {
                offset,
                size: usize::MAX,
            }
        })?;
        if n > cap {
            return Err(RegionFault::BadObjectSize { offset, size: n });
        }
        let size = SARRAY_FIXED
            .checked_add(
                cap.checked_mul(usize::from(h.other))
                    .ok_or(RegionFault::BadObjectSize { offset, size: cap })?,
            )
            .ok_or(RegionFault::BadObjectSize { offset, size: cap })?;
        need(buf, offset, size)?;
        size
    } else if h.tag == abi::TAG_STRING {
        need(buf, offset, STRING_FIXED)?;
        let bytes =
            usize::try_from(read_u64(buf, offset + 8)).map_err(|_| RegionFault::BadObjectSize {
                offset,
                size: usize::MAX,
            })?;
        let cap = usize::try_from(read_u64(buf, offset + 16)).map_err(|_| {
            RegionFault::BadObjectSize {
                offset,
                size: usize::MAX,
            }
        })?;
        if bytes == 0 || bytes > cap {
            return Err(RegionFault::StringIntegrity {
                offset,
                reason: "size 0 or beyond capacity",
            });
        }
        let size = STRING_FIXED
            .checked_add(cap)
            .ok_or(RegionFault::BadObjectSize { offset, size: cap })?;
        need(buf, offset, size)?;
        if buf[offset + STRING_FIXED + bytes - 1] != 0 {
            return Err(RegionFault::StringIntegrity {
                offset,
                reason: "missing NUL terminator",
            });
        }
        // Pin `lean_string_object`: `m_length` is the UTF-8 scalar count,
        // the same field `lean_string_length` boxes. Audit/relocate used
        // to check size and NUL only; a drifted `m_length` then passed
        // here and was boxed as a Nat by String.length.
        let payload = &buf[offset + STRING_FIXED..offset + STRING_FIXED + bytes - 1];
        let content = std::str::from_utf8(payload).map_err(|_| RegionFault::StringIntegrity {
            offset,
            reason: "invalid UTF-8",
        })?;
        let stored_length = read_u64(buf, offset + 24);
        let scalars = u64::try_from(content.chars().count()).unwrap_or(u64::MAX);
        if stored_length != scalars {
            return Err(RegionFault::StringIntegrity {
                offset,
                reason: "m_length is not the UTF-8 scalar count",
            });
        }
        size
    } else if h.tag == abi::TAG_CLOSURE {
        return Err(RegionFault::ClosureUnsupported { offset });
    } else if h.tag == abi::TAG_THUNK {
        need(buf, offset, THUNK_SIZE)?;
        // The Reference fixes only m_value (compact.cpp:622-625).
        ptr_fields.push(offset + 8);
        THUNK_SIZE
    } else if h.tag == abi::TAG_REF {
        need(buf, offset, REF_SIZE)?;
        ptr_fields.push(offset + 8);
        REF_SIZE
    } else if h.tag == abi::TAG_TASK {
        need(buf, offset, TASK_SIZE)?;
        ptr_fields.push(offset + 8);
        TASK_SIZE
    } else if h.tag == abi::TAG_PROMISE {
        need(buf, offset, PROMISE_SIZE)?;
        ptr_fields.push(offset + 8);
        PROMISE_SIZE
    } else if h.tag == abi::TAG_MPZ {
        need(buf, offset, MPZ_FIXED)?;
        let mp_size = read_i32(buf, offset + 12);
        let limbs = usize::try_from(mp_size.unsigned_abs()).expect("u32 fits usize");
        // Both fields are attacker-controlled bytes, so the `_mp_alloc >=
        // |_mp_size|` law is checked in the UNSIGNED domain: `i32::MIN.abs()`
        // panics on overflow (debug) or stays negative (release), and a
        // negative `_mp_alloc` is itself incoherent rather than a comparison
        // operand.
        let Ok(alloc) = u32::try_from(read_i32(buf, offset + 8)) else {
            return Err(RegionFault::MpzIntegrity { offset });
        };
        if limbs == 0 || alloc < mp_size.unsigned_abs() {
            return Err(RegionFault::MpzIntegrity { offset });
        }
        let size = MPZ_FIXED
            .checked_add(
                limbs
                    .checked_mul(8)
                    .ok_or(RegionFault::MpzIntegrity { offset })?,
            )
            .ok_or(RegionFault::MpzIntegrity { offset })?;
        need(buf, offset, size)?;
        limb_ptr = Some(offset + 16);
        size
    } else {
        return Err(RegionFault::ForbiddenTag { offset, tag: h.tag });
    };
    Ok(WalkStep {
        size,
        ptr_fields,
        limb_ptr,
    })
}

/// The pointer-word law shared by [`relocate`] and [`audit`]: a scalar word
/// passes (`None`); a pointer must land inside the region, 8-byte aligned
/// (`Some(rel)`); anything else is the typed fault.
fn checked_rel(buf: &[u8], field: usize, from: u64, len: usize) -> RResult<Option<u64>> {
    let v = read_u64(buf, field);
    if is_scalar_word(v) {
        return Ok(None);
    }
    let rel = v.wrapping_sub(from);
    if rel >= len as u64 {
        return Err(RegionFault::PtrOutOfBounds {
            offset: field,
            ptr: v,
        });
    }
    if !rel.is_multiple_of(8) {
        return Err(RegionFault::MisalignedPtr {
            offset: field,
            ptr: v,
        });
    }
    Ok(Some(rel))
}

/// The mpz limb-pointer law shared by [`relocate`], [`audit`], and
/// [`materialize`]: the pin's compactor copies live limbs immediately
/// after the object and rewrites the one pointer to that address. A
/// pointer that is merely *somewhere* in the inline block used to
/// pass; reading `|_mp_size|` limbs from there then treated the next
/// object as this number. The only legal address is the start of the
/// inline block.
fn checked_limb_rel(
    buf: &[u8],
    field: usize,
    from: u64,
    offset: usize,
    _size: usize,
) -> RResult<u64> {
    let v = read_u64(buf, field);
    let rel = v.wrapping_sub(from);
    let inline_start = (offset + MPZ_FIXED) as u64;
    if rel != inline_start {
        return Err(RegionFault::MpzIntegrity { offset });
    }
    Ok(rel)
}

/// Rewrite one stored pointer word from `from`-based to `to`-based, with the
/// full bounds/alignment law. Scalar words pass through.
fn fix_word(
    buf: &mut [u8],
    field: usize,
    from: u64,
    to: u64,
    len: usize,
    fixed: &mut u64,
) -> RResult<()> {
    if let Some(rel) = checked_rel(buf, field, from, len)?
        && from != to
    {
        write_u64(buf, field, to.wrapping_add(rel));
        *fixed += 1;
    }
    Ok(())
}

/// Relocate (or, with `from == to`, audit) a region payload in place: the
/// root word, then the linear object walk with per-category fixups —
/// `region_reader::read` exactly. On success every stored pointer is a
/// `to`-based address within the payload and every object satisfied its
/// category laws; on fault the buffer may be partially rewritten and must be
/// discarded (the caller's mapping is CoW-private, so discarding is free).
pub fn relocate(buf: &mut [u8], from: u64, to: u64) -> RResult<RegionReport> {
    if !buf.len().is_multiple_of(8) {
        return Err(RegionFault::RaggedPayload { len: buf.len() });
    }
    need(buf, 0, 8)?;
    let len = buf.len();
    let mut fixed = 0u64;
    fix_word(buf, 0, from, to, len, &mut fixed)?;
    let mut offset = 8usize;
    let mut objects = 0u64;
    while offset < len {
        let step = walk_step(buf, offset)?;
        for field in step.ptr_fields {
            fix_word(buf, field, from, to, len, &mut fixed)?;
        }
        if let Some(field) = step.limb_ptr {
            // The limb pointer must land INSIDE this object's inline block.
            let rel = checked_limb_rel(buf, field, from, offset, step.size)?;
            if from != to {
                write_u64(buf, field, to.wrapping_add(rel));
                fixed += 1;
            }
        }
        objects += 1;
        offset += round8(step.size);
    }
    Ok(RegionReport {
        objects,
        pointers_fixed: fixed,
        root: read_u64(buf, 0),
        bytes: len,
    })
}

/// Read-only full-surface audit: exactly [`relocate`]'s walk and category
/// laws at `from == to`, over an immutable buffer — the entry the olean
/// codec runs on shared/sealed mappings where no mutable view exists (the
/// §6.4 shared-code-path law). `base` is the payload's current pointer
/// base; the report's `pointers_fixed` is always 0.
pub fn audit(buf: &[u8], base: u64) -> RResult<RegionReport> {
    if !buf.len().is_multiple_of(8) {
        return Err(RegionFault::RaggedPayload { len: buf.len() });
    }
    need(buf, 0, 8)?;
    let len = buf.len();
    checked_rel(buf, 0, base, len)?;
    let mut offset = 8usize;
    let mut objects = 0u64;
    while offset < len {
        let step = walk_step(buf, offset)?;
        for field in step.ptr_fields {
            checked_rel(buf, field, base, len)?;
        }
        if let Some(field) = step.limb_ptr {
            checked_limb_rel(buf, field, base, offset, step.size)?;
        }
        objects += 1;
        offset += round8(step.size);
    }
    Ok(RegionReport {
        objects,
        pointers_fixed: 0,
        root: read_u64(buf, 0),
        bytes: len,
    })
}

/// Canonical relocation-invariant digest: FNV-1a over the linear object
/// stream with every pointer normalized to its region-relative offset. Two
/// loads of one region at different addresses digest identically — the
/// relocate-or-copy proof. `base` is the payload's CURRENT pointer base.
pub fn canonical_digest(buf: &[u8], base: u64) -> RResult<u64> {
    const OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x100_0000_01b3;
    let mut hash = OFFSET_BASIS;
    let mut eat = |bytes: &[u8]| {
        for b in bytes {
            hash ^= u64::from(*b);
            hash = hash.wrapping_mul(PRIME);
        }
    };
    if !buf.len().is_multiple_of(8) {
        return Err(RegionFault::RaggedPayload { len: buf.len() });
    }
    need(buf, 0, 8)?;
    let norm = |v: u64| {
        if is_scalar_word(v) {
            v
        } else {
            v.wrapping_sub(base)
        }
    };
    eat(&norm(read_u64(buf, 0)).to_le_bytes());
    let mut offset = 8usize;
    while offset < buf.len() {
        let step = walk_step(buf, offset)?;
        let mut ptr_set: Vec<usize> = step.ptr_fields.clone();
        if let Some(l) = step.limb_ptr {
            ptr_set.push(l);
        }
        ptr_set.sort_unstable();
        let mut cursor = offset;
        for field in &ptr_set {
            eat(&buf[cursor..*field]);
            eat(&norm(read_u64(buf, *field)).to_le_bytes());
            cursor = field + 8;
        }
        eat(&buf[cursor..offset + step.size]);
        offset += round8(step.size);
    }
    Ok(hash)
}

/// Materialize the region graph as live CompatHeap objects, sharing
/// preserved via an offset memo (region offsets ARE object identity). The
/// payload must already be relocated to `base`.
///
/// The walk is one LINEAR pass exploiting the writer's post-order law:
/// children are compacted before their parents, so every child pointer
/// refers to a strictly earlier offset (`object_compactor::operator()`).
/// A forward or self pointer is therefore a hostile input, reported as a
/// typed fault — which is also the termination proof (offsets strictly
/// increase, each object is built exactly once).
pub fn materialize(buf: &[u8], base: u64) -> RResult<Obj> {
    if !buf.len().is_multiple_of(8) {
        return Err(RegionFault::RaggedPayload { len: buf.len() });
    }
    need(buf, 0, 8)?;
    let root_word = read_u64(buf, 0);
    if is_scalar_word(root_word) {
        return Ok(Obj::mk_nat(usize::try_from(root_word >> 1).expect("word")));
    }

    let mut memo: HashMap<usize, Obj> = HashMap::new();
    // Resolve a child word to an already-built Obj (post-order law: the
    // child's offset must be strictly below the current object's).
    let child_of =
        |memo: &HashMap<usize, Obj>, v: u64, at: usize, current: usize| -> RResult<Obj> {
            if is_scalar_word(v) {
                return Ok(Obj::mk_nat(usize::try_from(v >> 1).expect("word")));
            }
            let rel = v.wrapping_sub(base);
            if rel >= buf.len() as u64 || !rel.is_multiple_of(8) {
                return Err(RegionFault::PtrOutOfBounds { offset: at, ptr: v });
            }
            let off = usize::try_from(rel).expect("bounded by len");
            match memo.get(&off) {
                Some(o) if off < current => Ok(o.clone_ref()),
                _ => Err(RegionFault::PtrOutOfBounds { offset: at, ptr: v }),
            }
        };

    let mut off = 8usize;
    while off < buf.len() {
        let step = walk_step(buf, off)?;
        let h = read_header(buf, off);
        let mut children: Vec<Obj> = Vec::with_capacity(step.ptr_fields.len());
        for field in &step.ptr_fields {
            children.push(child_of(&memo, read_u64(buf, *field), *field, off)?);
        }
        let built = if h.tag <= abi::TAG_MAX_CTOR_TAG {
            let n = usize::from(h.other);
            let scalar = &buf[off + HDR + 8 * n..off + step.size];
            if scalar.len() >= 1024 {
                return Err(RegionFault::BuildShape {
                    reason: "ctor scalar area exceeds the contract maximum",
                });
            }
            Obj::mk_ctor(h.tag, children, scalar)
        } else if h.tag == abi::TAG_ARRAY {
            Obj::mk_array(children)
        } else if h.tag == abi::TAG_SCALAR_ARRAY {
            let n = usize::try_from(read_u64(buf, off + 8)).expect("validated");
            let elem = usize::from(h.other);
            Obj::mk_sarray(
                h.other,
                &buf[off + SARRAY_FIXED..off + SARRAY_FIXED + n * elem],
            )
        } else if h.tag == abi::TAG_STRING {
            let bytes = usize::try_from(read_u64(buf, off + 8)).expect("validated");
            let data = &buf[off + STRING_FIXED..off + STRING_FIXED + bytes - 1];
            let s = std::str::from_utf8(data).map_err(|_| RegionFault::StringIntegrity {
                offset: off,
                reason: "invalid UTF-8",
            })?;
            Obj::mk_string(s)
        } else if h.tag == abi::TAG_THUNK {
            Obj::mk_thunk_value(children.pop().expect("one fixed slot"))
        } else if h.tag == abi::TAG_REF {
            Obj::mk_ref(children.pop().expect("one fixed slot"))
        } else if h.tag == abi::TAG_TASK {
            Obj::mk_task_pure(children.pop().expect("one fixed slot"))
        } else if h.tag == abi::TAG_MPZ {
            // `walk_step` proved alloc/size coherence and the inline
            // extent. It does not see `base`, so the limb POINTER is
            // this reader's job. Audit already refused a foreign or
            // mid-block pointer; materialize used to ignore it and
            // always copy from `off + MPZ_FIXED`.
            checked_limb_rel(buf, off + 16, base, off, step.size)?;
            let mp_size = read_i32(buf, off + 12);
            let limbs = usize::try_from(mp_size.unsigned_abs()).expect("u32");
            let mut vals = Vec::with_capacity(limbs);
            for i in 0..limbs {
                vals.push(read_u64(buf, off + MPZ_FIXED + 8 * i));
            }
            Obj::mk_mpz(&vals, mp_size < 0)
        } else {
            return Err(RegionFault::UnsupportedCategory {
                tag: h.tag,
                operation: "materialize",
            });
        };
        memo.insert(off, built);
        off += round8(step.size);
    }
    // The root points at one of the walked objects (usually the last).
    let rel = root_word.wrapping_sub(base);
    let root_off = usize::try_from(rel).map_err(|_| RegionFault::PtrOutOfBounds {
        offset: 0,
        ptr: root_word,
    })?;
    memo.get(&root_off)
        .map(Obj::clone_ref)
        .ok_or(RegionFault::PtrOutOfBounds {
            offset: 0,
            ptr: root_word,
        })
}

/// Compact a live object graph into region bytes against `base` — the
/// writer half of the shared code path (`object_compactor`): root word
/// reserved first, objects in post-order (children before parents), sharing
/// preserved via identity, headers in the persistent non-heap form, padding
/// zeroed. Slice-1 categories: scalars, ctors, arrays, strings, and mpz —
/// the shapes real pinned-toolchain regions contain (G0-1 item 11); the
/// cell categories (thunk/ref/task, no live read view yet), scalar arrays
/// (same), and closures (no library table) are typed-unsupported.
pub fn compact(root: &Obj, base: u64) -> RResult<Vec<u8>> {
    let mut out = vec![0u8; 8];
    let mut memo: HashMap<usize, u64> = HashMap::new();

    // The Reference's retry loop (`object_compactor::operator()`): an object
    // stays on the stack until every heap child is already compacted, so a
    // child shared by two parents is emitted exactly once and always before
    // either parent. Termination: handle-built graphs are structurally
    // acyclic (constructors consume their children), each object is emitted
    // once, and a retry only runs after new children enter the memo.
    let mut stack: Vec<Obj> = vec![root.clone_ref()];
    while let Some(o) = stack.last() {
        if o.is_scalar() || memo.contains_key(&o.identity_token()) {
            stack.pop();
            continue;
        }
        let o = o.clone_ref();
        let tag = o.header().tag;
        let mut children: Vec<Obj> = Vec::new();
        if tag <= abi::TAG_MAX_CTOR_TAG {
            for i in 0..usize::from(o.header().other) {
                let Some(child) = o.try_ctor_child(i) else {
                    return Err(RegionFault::BuildShape {
                        reason: "ctor slot is past the allocated object",
                    });
                };
                children.push(child);
            }
        } else if tag == abi::TAG_ARRAY {
            let Some((n, _)) = o.try_array_view() else {
                // The region has not been emitted yet, so there is no
                // file offset to name. 0 is the pre-placement form.
                return Err(RegionFault::ArrayIntegrity { offset: 0 });
            };
            for i in 0..n {
                children.push(o.array_child(i));
            }
        } else if tag == abi::TAG_STRING || tag == abi::TAG_MPZ || tag == abi::TAG_SCALAR_ARRAY {
            // leaves
        } else {
            return Err(RegionFault::UnsupportedCategory {
                tag,
                operation: "compact",
            });
        }
        let mut pending = false;
        for c in children {
            if !c.is_scalar() && !memo.contains_key(&c.identity_token()) {
                stack.push(c);
                pending = true;
            }
        }
        if pending {
            continue;
        }
        {
            {
                let h = o.header();
                let offset = out.len() as u64;
                let word_of = |c: &Obj, memo: &HashMap<usize, u64>| -> u64 {
                    if c.is_scalar() {
                        ((c.unbox() as u64) << 1) | 1
                    } else {
                        base.wrapping_add(memo[&c.identity_token()])
                    }
                };
                let emit_header = |out: &mut Vec<u8>, sz: usize, tag: u8, other: u8| {
                    // lean_set_non_heap_header: rc=0, exact size for the
                    // small path; big-path categories store the sentinel 1.
                    let cs: u16 = if tag == abi::TAG_ARRAY
                        || tag == abi::TAG_SCALAR_ARRAY
                        || tag == abi::TAG_STRING
                    {
                        1
                    } else {
                        u16::try_from(sz).expect("small-path size fits u16")
                    };
                    out.extend_from_slice(&0i32.to_le_bytes());
                    out.extend_from_slice(&cs.to_le_bytes());
                    out.push(other);
                    out.push(tag);
                };
                if h.tag <= abi::TAG_MAX_CTOR_TAG {
                    let n = usize::from(h.other);
                    let heap_size = usize::from(h.cs_sz);
                    // Walk refuses an unaligned ctor extent. The scalar
                    // loop below steps by 8 and then `ctor_scalar_u64`
                    // asserts `off + 8 <= cs_sz - 8`. A leftover tail
                    // shorter than a word used to abort instead of a
                    // typed BuildShape (FL-INV-07).
                    if heap_size < HDR + 8 * n || !heap_size.is_multiple_of(8) {
                        return Err(RegionFault::BuildShape {
                            reason: "constructor extent below its minimum or unaligned",
                        });
                    }
                    emit_header(&mut out, heap_size, h.tag, h.other);
                    for i in 0..n {
                        let Some(c) = o.try_ctor_child(i) else {
                            return Err(RegionFault::BuildShape {
                                reason: "ctor slot is past the allocated object",
                            });
                        };
                        let w = word_of(&c, &memo);
                        out.extend_from_slice(&w.to_le_bytes());
                    }
                    // Scalar area (incl. the zeroed padding law) via the
                    // word-aligned safe reads.
                    let mut off = 8 * n;
                    while off < heap_size - HDR {
                        out.extend_from_slice(&o.ctor_scalar_u64(off).to_le_bytes());
                        off += 8;
                    }
                } else if h.tag == abi::TAG_ARRAY {
                    let Some((n, _)) = o.try_array_view() else {
                        return Err(RegionFault::ArrayIntegrity {
                            offset: offset as usize,
                        });
                    };
                    emit_header(&mut out, ARRAY_FIXED + 8 * n, h.tag, 0);
                    out.extend_from_slice(&(n as u64).to_le_bytes());
                    out.extend_from_slice(&(n as u64).to_le_bytes());
                    for i in 0..n {
                        let c = o.array_child(i);
                        let w = word_of(&c, &memo);
                        out.extend_from_slice(&w.to_le_bytes());
                    }
                } else if h.tag == abi::TAG_SCALAR_ARRAY {
                    let Some((elem, n, _, data)) = o.try_sarray_view() else {
                        return Err(RegionFault::BadObjectSize {
                            offset: offset as usize,
                            size: 0,
                        });
                    };
                    emit_header(&mut out, SARRAY_FIXED + data.len(), h.tag, elem);
                    out.extend_from_slice(&(n as u64).to_le_bytes());
                    out.extend_from_slice(&(n as u64).to_le_bytes());
                    out.extend_from_slice(&data);
                } else if h.tag == abi::TAG_STRING {
                    let Some((size, _, length, data)) = o.try_string_view() else {
                        return Err(RegionFault::StringIntegrity {
                            offset: offset as usize,
                            reason: "hostile or inconsistent string header",
                        });
                    };
                    emit_header(&mut out, STRING_FIXED + size, h.tag, 0);
                    out.extend_from_slice(&(size as u64).to_le_bytes());
                    out.extend_from_slice(&(size as u64).to_le_bytes());
                    out.extend_from_slice(&(length as u64).to_le_bytes());
                    out.extend_from_slice(&data);
                } else if h.tag == abi::TAG_MPZ {
                    let Some((_, mp_size, limbs)) = o.try_mpz_view() else {
                        return Err(RegionFault::MpzIntegrity {
                            offset: offset as usize,
                        });
                    };
                    emit_header(&mut out, MPZ_FIXED + 8 * limbs.len(), h.tag, 0);
                    let alloc =
                        i32::try_from(limbs.len()).map_err(|_| RegionFault::MpzIntegrity {
                            offset: offset as usize,
                        })?;
                    out.extend_from_slice(&alloc.to_le_bytes());
                    out.extend_from_slice(&mp_size.to_le_bytes());
                    let limb_addr = base.wrapping_add(offset + MPZ_FIXED as u64);
                    out.extend_from_slice(&limb_addr.to_le_bytes());
                    for l in limbs {
                        out.extend_from_slice(&l.to_le_bytes());
                    }
                } else {
                    return Err(RegionFault::UnsupportedCategory {
                        tag: h.tag,
                        operation: "compact",
                    });
                }
                // Padding law: alloc() zero-fills to the 8-byte quantum.
                while !out.len().is_multiple_of(8) {
                    out.push(0);
                }
                memo.insert(o.identity_token(), offset);
            }
        }
        stack.pop();
    }
    let root_word = if root.is_scalar() {
        ((root.unbox() as u64) << 1) | 1
    } else {
        base.wrapping_add(memo[&root.identity_token()])
    };
    out[0..8].copy_from_slice(&root_word.to_le_bytes());
    Ok(out)
}

/// The staging file name for `path` in THIS process and THIS thread.
///
/// The token is per-(process, thread, target) rather than per-process. Keying
/// it on the pid alone means two THREADS publishing the same target share one
/// staging file, and `File::create` truncates: T1 writes half its bytes, T2
/// truncates and writes its own, T1 fsyncs and renames a MIXTURE into place.
/// That is a corrupt artifact published through the path whose whole job is to
/// make publication atomic, and it is reachable the moment anything publishes
/// in parallel — which is the point of a deterministic-parallel build fabric.
///
/// Keeping it a pure function of (pid, thread, target) is what lets
/// [`atomic_staging_path`] still predict it for the crash drill; a counter or a
/// random token would be unique but unpredictable.
fn staging_name(path: &std::path::Path) -> String {
    let thread: String = format!("{:?}", std::thread::current().id())
        .chars()
        .filter(char::is_ascii_digit)
        .collect();
    format!(
        ".{}.tmp.{}.{}",
        path.file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "artifact".to_string()),
        std::process::id(),
        thread
    )
}

/// Atomically publish a file: write to a sibling temp file, fsync it,
/// rename over the target, fsync the directory. A crash at ANY point leaves
/// either the old target or no target — never a half-published file (the
/// fln-wgp staging drill kills the process between temp write and rename and
/// asserts exactly that).
///
/// Concurrency: safe for two threads publishing the SAME target, because the
/// staging file is per-thread (see [`staging_name`]) and `rename` is atomic —
/// the target ends up as exactly one caller's bytes, never a mixture. Which
/// caller wins is the last rename, which is the caller's problem to care about,
/// not this function's.
pub fn write_file_atomic(bytes: &[u8], path: &std::path::Path) -> std::io::Result<()> {
    let mut control = |_step| Ok::<(), std::convert::Infallible>(());
    match write_file_atomic_controlled(bytes, path, &mut control) {
        Ok(()) => Ok(()),
        Err(AtomicWriteError::Io { source, .. }) => Err(source),
        Err(AtomicWriteError::Control { source, .. }) => match source {},
    }
}

static NEW_FILE_STAGING_SEQUENCE: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
const NEW_FILE_STAGING_ATTEMPTS: usize = 1_024;

fn new_file_staging_path(path: &std::path::Path, sequence: u64) -> std::path::PathBuf {
    let dir = path.parent().unwrap_or_else(|| std::path::Path::new("."));
    let thread: String = format!("{:?}", std::thread::current().id())
        .chars()
        .filter(char::is_ascii_digit)
        .collect();
    let name = path
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| "artifact".to_owned());
    dir.join(format!(
        ".{name}.new.{}.{}.{sequence}",
        std::process::id(),
        thread
    ))
}

/// One fallible boundary in atomic no-clobber publication.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomicCreateStep {
    CreateStaging,
    WriteChunk {
        offset: u64,
        chunk_len: u64,
        total_len: u64,
    },
    SyncStaging,
    LinkTarget,
    SyncDirectoryAfterLink,
    RemoveStaging,
    SyncDirectoryAfterCleanup,
}

impl std::fmt::Display for AtomicCreateStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CreateStaging => f.write_str("create unique staging file"),
            Self::WriteChunk {
                offset,
                chunk_len,
                total_len,
            } => write!(
                f,
                "write {chunk_len} bytes at offset {offset} of {total_len}"
            ),
            Self::SyncStaging => f.write_str("sync staging file"),
            Self::LinkTarget => f.write_str("create target link"),
            Self::SyncDirectoryAfterLink => f.write_str("sync target directory after link"),
            Self::RemoveStaging => f.write_str("remove staging link"),
            Self::SyncDirectoryAfterCleanup => {
                f.write_str("sync target directory after staging cleanup")
            }
        }
    }
}

/// Typed failure from [`write_file_atomic_new_controlled`].
///
/// `target_created` is the linearization boundary. When true, the final name
/// already denotes the complete, file-synced bytes even though later cleanup or
/// directory durability work failed.
#[derive(Debug)]
pub enum AtomicCreateError<E> {
    Control {
        step: AtomicCreateStep,
        target_created: bool,
        source: E,
    },
    Io {
        step: AtomicCreateStep,
        target_created: bool,
        source: std::io::Error,
    },
    Cleanup {
        primary: Box<Self>,
        cleanup: Box<Self>,
    },
}

impl<E> AtomicCreateError<E> {
    pub const fn step(&self) -> AtomicCreateStep {
        match self {
            Self::Control { step, .. } | Self::Io { step, .. } => *step,
            Self::Cleanup { primary, .. } => primary.step(),
        }
    }

    pub const fn target_created(&self) -> bool {
        match self {
            Self::Control { target_created, .. } | Self::Io { target_created, .. } => {
                *target_created
            }
            Self::Cleanup { primary, .. } => primary.target_created(),
        }
    }

    /// Returns the primary I/O failure kind, retaining the cause that made
    /// publication fail even when removing its staging link also failed.
    pub fn primary_io_error_kind(&self) -> Option<std::io::ErrorKind> {
        match self {
            Self::Control { .. } => None,
            Self::Io { source, .. } => Some(source.kind()),
            Self::Cleanup { primary, .. } => primary.primary_io_error_kind(),
        }
    }
}

impl<E: std::fmt::Display> std::fmt::Display for AtomicCreateError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let state = if self.target_created() {
            "complete target already created"
        } else {
            "target not created"
        };
        match self {
            Self::Control { step, source, .. } => {
                write!(
                    f,
                    "publication control refused at {step} ({state}): {source}"
                )
            }
            Self::Io { step, source, .. } => {
                write!(f, "publication I/O failed at {step} ({state}): {source}")
            }
            Self::Cleanup { primary, cleanup } => write!(
                f,
                "{primary}; staging cleanup also failed without replacing the primary cause: {cleanup}"
            ),
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for AtomicCreateError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Control { source, .. } => Some(source),
            Self::Io { source, .. } => Some(source),
            Self::Cleanup { primary, .. } => Some(primary.as_ref()),
        }
    }
}

fn atomic_create_checkpoint<E, C>(
    control: &mut C,
    step: AtomicCreateStep,
    target_created: bool,
) -> Result<(), AtomicCreateError<E>>
where
    C: FnMut(AtomicCreateStep) -> Result<(), E> + ?Sized,
{
    control(step).map_err(|source| AtomicCreateError::Control {
        step,
        target_created,
        source,
    })
}

fn atomic_create_io<E>(
    step: AtomicCreateStep,
    target_created: bool,
    source: std::io::Error,
) -> AtomicCreateError<E> {
    AtomicCreateError::Io {
        step,
        target_created,
        source,
    }
}

fn cleanup_staging_after_create_failure<E, C>(
    tmp: &std::path::Path,
    control: &mut C,
    primary: AtomicCreateError<E>,
) -> AtomicCreateError<E>
where
    C: FnMut(AtomicCreateStep) -> Result<(), E> + ?Sized,
{
    let cleanup = atomic_create_checkpoint(control, AtomicCreateStep::RemoveStaging, false)
        .and_then(|()| {
            std::fs::remove_file(tmp)
                .map_err(|error| atomic_create_io(AtomicCreateStep::RemoveStaging, false, error))
        });
    match cleanup {
        Ok(()) => primary,
        Err(cleanup) => AtomicCreateError::Cleanup {
            primary: Box::new(primary),
            cleanup: Box::new(cleanup),
        },
    }
}

/// Atomically publish a new file without replacing any existing directory entry.
///
/// The bytes are written and synced through a sibling staging file, then linked
/// into place with [`std::fs::hard_link`]. Creating that final hard link is one
/// atomic no-clobber operation: if another process, a symlink, a directory, or
/// any prior file already names `path`, publication fails and the existing entry
/// is untouched. A check followed by [`std::fs::rename`] cannot provide this
/// property because another publisher can win between those two operations.
///
/// Filesystems without same-directory hard-link support refuse this operation;
/// they never fall back to replacement or expose a partially written target.
/// The parent directory is assumed to be a trusted, stable namespace; safe
/// `std` does not expose directory-handle-relative operations that would defend
/// against a same-user ancestor or staging-name replacement race.
pub fn write_file_atomic_new(
    bytes: &[u8],
    path: &std::path::Path,
) -> Result<(), AtomicCreateError<std::convert::Infallible>> {
    let mut control = |_step| Ok::<(), std::convert::Infallible>(());
    write_file_atomic_new_controlled(bytes, path, &mut control)
}

/// Controlled form of [`write_file_atomic_new`] for exact fault drills.
pub fn write_file_atomic_new_controlled<E, C>(
    bytes: &[u8],
    path: &std::path::Path,
    control: &mut C,
) -> Result<(), AtomicCreateError<E>>
where
    C: FnMut(AtomicCreateStep) -> Result<(), E> + ?Sized,
{
    let dir = path.parent().unwrap_or_else(|| std::path::Path::new("."));
    let (tmp, mut file) = {
        let mut selected = None;
        for _ in 0..NEW_FILE_STAGING_ATTEMPTS {
            atomic_create_checkpoint(control, AtomicCreateStep::CreateStaging, false)?;
            let sequence =
                NEW_FILE_STAGING_SEQUENCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let candidate = new_file_staging_path(path, sequence);
            match std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&candidate)
            {
                Ok(file) => {
                    selected = Some((candidate, file));
                    break;
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(atomic_create_io(
                        AtomicCreateStep::CreateStaging,
                        false,
                        error,
                    ));
                }
            }
        }
        selected.ok_or_else(|| {
            atomic_create_io(
                AtomicCreateStep::CreateStaging,
                false,
                std::io::Error::new(
                    std::io::ErrorKind::AlreadyExists,
                    "no unique staging name remained within the bounded attempt budget",
                ),
            )
        })?
    };
    let staged = (|| -> Result<(), AtomicCreateError<E>> {
        let mut offset = 0_u64;
        for chunk in bytes.chunks(ATOMIC_WRITE_CHUNK_BYTES) {
            let step = AtomicCreateStep::WriteChunk {
                offset,
                chunk_len: chunk.len() as u64,
                total_len: bytes.len() as u64,
            };
            atomic_create_checkpoint(control, step, false)?;
            std::io::Write::write_all(&mut file, chunk)
                .map_err(|error| atomic_create_io(step, false, error))?;
            offset = offset.saturating_add(chunk.len() as u64);
        }
        atomic_create_checkpoint(control, AtomicCreateStep::SyncStaging, false)?;
        file.sync_all()
            .map_err(|error| atomic_create_io(AtomicCreateStep::SyncStaging, false, error))
    })();
    drop(file);
    if let Err(error) = staged {
        return Err(cleanup_staging_after_create_failure(&tmp, control, error));
    }
    if let Err(error) = atomic_create_checkpoint(control, AtomicCreateStep::LinkTarget, false) {
        return Err(cleanup_staging_after_create_failure(&tmp, control, error));
    }
    if let Err(error) = std::fs::hard_link(&tmp, path) {
        let primary = atomic_create_io(AtomicCreateStep::LinkTarget, false, error);
        return Err(cleanup_staging_after_create_failure(&tmp, control, primary));
    }
    atomic_create_checkpoint(control, AtomicCreateStep::SyncDirectoryAfterLink, true)?;
    let directory = std::fs::File::open(dir)
        .map_err(|error| atomic_create_io(AtomicCreateStep::SyncDirectoryAfterLink, true, error))?;
    directory
        .sync_all()
        .map_err(|error| atomic_create_io(AtomicCreateStep::SyncDirectoryAfterLink, true, error))?;
    atomic_create_checkpoint(control, AtomicCreateStep::RemoveStaging, true)?;
    std::fs::remove_file(&tmp)
        .map_err(|error| atomic_create_io(AtomicCreateStep::RemoveStaging, true, error))?;
    atomic_create_checkpoint(control, AtomicCreateStep::SyncDirectoryAfterCleanup, true)?;
    directory
        .sync_all()
        .map_err(|error| atomic_create_io(AtomicCreateStep::SyncDirectoryAfterCleanup, true, error))
}

const ATOMIC_WRITE_CHUNK_BYTES: usize = 64 * 1024;

/// The next externally fallible step in an atomic file replacement.
///
/// A controller observes each value immediately before the named operation.
/// `WriteChunk::offset` is the number of bytes already written, so a refusal
/// there can model a full device after an exact prefix without publishing a
/// partial target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AtomicWriteStep {
    CreateStaging,
    WriteChunk {
        offset: u64,
        chunk_len: u64,
        total_len: u64,
    },
    SyncStaging,
    RenameTarget,
    SyncDirectory,
}

impl std::fmt::Display for AtomicWriteStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CreateStaging => f.write_str("create staging file"),
            Self::WriteChunk {
                offset,
                chunk_len,
                total_len,
            } => write!(
                f,
                "write {chunk_len} bytes at offset {offset} of {total_len}"
            ),
            Self::SyncStaging => f.write_str("sync staging file"),
            Self::RenameTarget => f.write_str("replace target"),
            Self::SyncDirectory => f.write_str("sync target directory"),
        }
    }
}

/// Typed failure from [`write_file_atomic_controlled`].
///
/// `target_replaced` is the transaction boundary. If it is false, the target
/// still names the prior complete file. If it is true, the rename succeeded
/// and the new complete file is visible, but the directory sync failed or was
/// refused, so crash durability is not established.
#[derive(Debug)]
pub enum AtomicWriteError<E> {
    Control {
        step: AtomicWriteStep,
        target_replaced: bool,
        source: E,
    },
    Io {
        step: AtomicWriteStep,
        target_replaced: bool,
        source: std::io::Error,
    },
}

impl<E> AtomicWriteError<E> {
    pub const fn step(&self) -> AtomicWriteStep {
        match self {
            Self::Control { step, .. } | Self::Io { step, .. } => *step,
        }
    }

    pub const fn target_replaced(&self) -> bool {
        match self {
            Self::Control {
                target_replaced, ..
            }
            | Self::Io {
                target_replaced, ..
            } => *target_replaced,
        }
    }
}

impl<E: std::fmt::Display> std::fmt::Display for AtomicWriteError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Control {
                step,
                target_replaced,
                source,
            } => write!(
                f,
                "atomic write control refused `{step}` after target replacement={target_replaced}: \
                 {source}"
            ),
            Self::Io {
                step,
                target_replaced,
                source,
            } => write!(
                f,
                "atomic write failed during `{step}` after target replacement={target_replaced}: \
                 {source}"
            ),
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for AtomicWriteError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Control { source, .. } => Some(source),
            Self::Io { source, .. } => Some(source),
        }
    }
}

fn atomic_write_checkpoint<E, C>(
    control: &mut C,
    step: AtomicWriteStep,
    target_replaced: bool,
) -> Result<(), AtomicWriteError<E>>
where
    C: FnMut(AtomicWriteStep) -> Result<(), E> + ?Sized,
{
    control(step).map_err(|source| AtomicWriteError::Control {
        step,
        target_replaced,
        source,
    })
}

/// Atomically replace `path`, consulting `control` immediately before every
/// fallible filesystem step.
///
/// This is the fault-drill and cancellation-capable form of
/// [`write_file_atomic`]. A control refusal is structurally distinct from an
/// operating-system error, and both report whether the rename already
/// linearized. The controller is never called after a successful directory
/// sync.
pub fn write_file_atomic_controlled<E, C>(
    bytes: &[u8],
    path: &std::path::Path,
    control: &mut C,
) -> Result<(), AtomicWriteError<E>>
where
    C: FnMut(AtomicWriteStep) -> Result<(), E> + ?Sized,
{
    let dir = path.parent().unwrap_or_else(|| std::path::Path::new("."));
    let tmp = dir.join(staging_name(path));
    let mut target_replaced = false;
    atomic_write_checkpoint(control, AtomicWriteStep::CreateStaging, target_replaced)?;
    {
        let mut file = std::fs::File::create(&tmp).map_err(|source| AtomicWriteError::Io {
            step: AtomicWriteStep::CreateStaging,
            target_replaced,
            source,
        })?;
        let mut offset = 0u64;
        for chunk in bytes.chunks(ATOMIC_WRITE_CHUNK_BYTES) {
            let step = AtomicWriteStep::WriteChunk {
                offset,
                chunk_len: chunk.len() as u64,
                total_len: bytes.len() as u64,
            };
            atomic_write_checkpoint(control, step, target_replaced)?;
            std::io::Write::write_all(&mut file, chunk).map_err(|source| AtomicWriteError::Io {
                step,
                target_replaced,
                source,
            })?;
            offset = offset.saturating_add(chunk.len() as u64);
        }
        atomic_write_checkpoint(control, AtomicWriteStep::SyncStaging, target_replaced)?;
        file.sync_all().map_err(|source| AtomicWriteError::Io {
            step: AtomicWriteStep::SyncStaging,
            target_replaced,
            source,
        })?;
    }
    atomic_write_checkpoint(control, AtomicWriteStep::RenameTarget, target_replaced)?;
    std::fs::rename(&tmp, path).map_err(|source| AtomicWriteError::Io {
        step: AtomicWriteStep::RenameTarget,
        target_replaced,
        source,
    })?;
    target_replaced = true;
    atomic_write_checkpoint(control, AtomicWriteStep::SyncDirectory, target_replaced)?;
    std::fs::File::open(dir)
        .and_then(|directory| directory.sync_all())
        .map_err(|source| AtomicWriteError::Io {
            step: AtomicWriteStep::SyncDirectory,
            target_replaced,
            source,
        })
}

/// The staging temp path [`write_file_atomic`] uses for `path` in THIS process
/// and THIS thread — exposed so the crash drill can assert "temp present,
/// target absent". Call it from the thread that publishes, or it will name a
/// different file.
pub fn atomic_staging_path(path: &std::path::Path) -> std::path::PathBuf {
    let dir = path.parent().unwrap_or_else(|| std::path::Path::new("."));
    dir.join(staging_name(path))
}
