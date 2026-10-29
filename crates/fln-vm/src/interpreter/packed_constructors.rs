//! Immutable construction and checked access for the Reference's packed
//! integer fields. Offsets start after the constructor header and include its
//! object slots, matching IR `uproj`/`sproj` and `uset`/`sset`.
//!
//! The certified CompatHeap is 64-bit little-endian. Its existing fallible
//! word reader is sufficient for subword and unaligned accesses: copy the
//! covered initialized words, then select only the requested bytes. No raw
//! pointer, mutable alias, or new unsafe membrane operation is needed.

use super::{
    Obj, ValueKind, VmRefusal, byte_argument, type_mismatch, uint16_argument, uint32_argument,
    uint64_argument, uint64_result, usize_argument, usize_result, value_kind,
};
use fln_comp::flbc::ScalarKind;

pub(super) fn write_scalar(
    bytes: &mut [u8],
    object_fields: usize,
    offset: u16,
    kind: ScalarKind,
    value: &Obj,
    argument: usize,
) -> Result<(), VmRefusal> {
    let offset = usize::from(offset);
    let width = kind.width();
    let bounds = || VmRefusal::ConstructorScalarBounds {
        offset,
        width,
        object_fields,
    };
    let object_bytes = object_fields
        .checked_mul(std::mem::size_of::<usize>())
        .ok_or_else(bounds)?;
    let start = offset.checked_sub(object_bytes).ok_or_else(bounds)?;
    let end = start.checked_add(width).ok_or_else(bounds)?;
    let target = bytes.get_mut(start..end).ok_or_else(bounds)?;
    let operation = "packed constructor initialization";
    let bits = match kind {
        ScalarKind::UInt8 => u64::from(byte_argument(value, operation, argument)?),
        ScalarKind::UInt16 => u64::from(uint16_argument(value, operation, argument)?),
        ScalarKind::UInt32 => u64::from(uint32_argument(value, operation, argument)?),
        ScalarKind::UInt64 => uint64_argument(value, operation, argument)?,
        ScalarKind::USize => usize_argument(value, operation, argument)? as u64,
    };
    target.copy_from_slice(&bits.to_ne_bytes()[..width]);
    Ok(())
}

pub(super) fn project(value: &Obj, offset: u16, kind: ScalarKind) -> Result<Obj, VmRefusal> {
    if !matches!(value_kind(value), ValueKind::Ctor(_)) {
        return Err(type_mismatch(
            "constructor scalar projection",
            0,
            "constructor",
            value,
        ));
    }
    let offset = usize::from(offset);
    let width = kind.width();
    let object_fields = usize::from(value.header().other);
    let bounds = || VmRefusal::ConstructorScalarBounds {
        offset,
        width,
        object_fields,
    };
    let object_bytes = object_fields
        .checked_mul(std::mem::size_of::<usize>())
        .ok_or_else(bounds)?;
    if offset < object_bytes {
        return Err(bounds());
    }
    let mut bytes = [0u8; std::mem::size_of::<u64>()];
    let mut copied = 0;
    while copied < width {
        let current = offset.checked_add(copied).ok_or_else(bounds)?;
        let within = current % bytes.len();
        let aligned = current - within;
        let word = value.try_ctor_scalar_u64(aligned).ok_or_else(bounds)?;
        let count = (width - copied).min(bytes.len() - within);
        bytes[copied..copied + count].copy_from_slice(&word.to_ne_bytes()[within..within + count]);
        copied += count;
    }
    let bits = u64::from_ne_bytes(bytes);
    Ok(match kind {
        ScalarKind::UInt8 | ScalarKind::UInt16 | ScalarKind::UInt32 => Obj::mk_nat(bits as usize),
        ScalarKind::UInt64 => uint64_result(bits).value,
        ScalarKind::USize => usize_result(bits as usize).value,
    })
}
