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

/// Typed region failure. Every variant carries the region offset (bytes from
/// the start of the payload) where the law broke.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegionFault {
    /// Payload shorter than the fixed envelope or a read past its end.
    Truncated { offset: usize, wanted: usize },
    /// Envelope magic differs from the generated contract's.
    BadMagic,
    /// Envelope version outside the contract's accepted set.
    UnsupportedVersion(u8),
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
    let (base_off, base_sz) = header_field("base_addr");
    let base_addr = u64::from_le_bytes(
        file[base_off..base_off + base_sz]
            .try_into()
            .expect("contract-sized field"),
    );
    if !(base_addr as usize).is_multiple_of(rc::REGION_ALIGN) {
        return Err(RegionFault::MisalignedBase { base: base_addr });
    }
    let (data_off, _) = header_field("data");
    Ok(OleanEnvelope {
        version,
        base_addr,
        payload_offset: data_off,
        payload_len: file.len() - data_off,
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
        let alloc = read_i32(buf, offset + 8);
        if limbs == 0 || alloc < mp_size.abs() {
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
    let v = read_u64(buf, field);
    if is_scalar_word(v) {
        return Ok(());
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
    if from != to {
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
            let v = read_u64(buf, field);
            let rel = v.wrapping_sub(from);
            let block = (offset + MPZ_FIXED) as u64..(offset + step.size) as u64;
            if !block.contains(&rel) || !rel.is_multiple_of(8) {
                return Err(RegionFault::MpzIntegrity { offset });
            }
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
                children.push(o.ctor_child(i));
            }
        } else if tag == abi::TAG_ARRAY {
            for i in 0..o.array_view().0 {
                children.push(o.array_child(i));
            }
        } else if tag == abi::TAG_STRING || tag == abi::TAG_MPZ {
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
                    if heap_size < HDR + 8 * n {
                        return Err(RegionFault::BuildShape {
                            reason: "ctor smaller than its slot count",
                        });
                    }
                    emit_header(&mut out, heap_size, h.tag, h.other);
                    for i in 0..n {
                        let c = o.ctor_child(i);
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
                    let (n, _) = o.array_view();
                    emit_header(&mut out, ARRAY_FIXED + 8 * n, h.tag, 0);
                    out.extend_from_slice(&(n as u64).to_le_bytes());
                    out.extend_from_slice(&(n as u64).to_le_bytes());
                    for i in 0..n {
                        let c = o.array_child(i);
                        let w = word_of(&c, &memo);
                        out.extend_from_slice(&w.to_le_bytes());
                    }
                } else if h.tag == abi::TAG_STRING {
                    let (size, _, length, data) = o.string_view();
                    emit_header(&mut out, STRING_FIXED + size, h.tag, 0);
                    out.extend_from_slice(&(size as u64).to_le_bytes());
                    out.extend_from_slice(&(size as u64).to_le_bytes());
                    out.extend_from_slice(&(length as u64).to_le_bytes());
                    out.extend_from_slice(&data);
                } else if h.tag == abi::TAG_MPZ {
                    let (_, mp_size, limbs) = o.mpz_view();
                    emit_header(&mut out, MPZ_FIXED + 8 * limbs.len(), h.tag, 0);
                    out.extend_from_slice(&i32::try_from(limbs.len()).expect("i32").to_le_bytes());
                    out.extend_from_slice(&mp_size.to_le_bytes());
                    let limb_addr = base.wrapping_add(offset + MPZ_FIXED as u64);
                    out.extend_from_slice(&limb_addr.to_le_bytes());
                    for l in &limbs {
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

/// Atomically publish a region file: write to a sibling temp file, fsync it,
/// rename over the target, fsync the directory. A crash at ANY point leaves
/// either the old target or no target — never a half-published region (the
/// fln-wgp staging drill kills the process between temp write and rename and
/// asserts exactly that).
pub fn write_region_file(bytes: &[u8], path: &std::path::Path) -> std::io::Result<()> {
    let dir = path.parent().unwrap_or_else(|| std::path::Path::new("."));
    let tmp = dir.join(format!(
        ".{}.tmp.{}",
        path.file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "region".to_string()),
        std::process::id()
    ));
    {
        let mut f = std::fs::File::create(&tmp)?;
        std::io::Write::write_all(&mut f, bytes)?;
        f.sync_all()?;
    }
    std::fs::rename(&tmp, path)?;
    std::fs::File::open(dir)?.sync_all()
}

/// The staging temp path `write_region_file` uses for `path` in THIS process
/// — exposed so the crash drill can assert "temp present, target absent".
pub fn staging_tmp_path(path: &std::path::Path) -> std::path::PathBuf {
    let dir = path.parent().unwrap_or_else(|| std::path::Path::new("."));
    dir.join(format!(
        ".{}.tmp.{}",
        path.file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "region".to_string()),
        std::process::id()
    ))
}
