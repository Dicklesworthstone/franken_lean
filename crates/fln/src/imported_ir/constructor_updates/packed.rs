//! Byte-exact equivalence for immutable updates of packed records.
//!
//! A scalar source is compared by variable identity and its representation,
//! never by numeric equality (which would lose signed zero or NaN payloads).
//! The surviving initialization retains the lowerer's checked carrier reads.
//! Bounds and disjointness of *both* alternatives are checked before either
//! may disappear, and every byte in the fresh result must be initialized.

use super::{IrExpr, IrStmt, IrType, Meter, Result, Shape};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    U8,
    U16,
    U32,
    U64,
    USize,
    F32,
    F64,
}

impl Kind {
    fn from_type(ty: &IrType) -> Option<Self> {
        Some(match ty {
            IrType::UInt8 => Self::U8,
            IrType::UInt16 => Self::U16,
            IrType::UInt32 => Self::U32,
            IrType::UInt64 => Self::U64,
            IrType::USize => Self::USize,
            IrType::Float32 => Self::F32,
            IrType::Float => Self::F64,
            _ => return None,
        })
    }

    const fn width(self) -> u64 {
        match self {
            Self::U8 => 1,
            Self::U16 => 2,
            Self::U32 | Self::F32 => 4,
            Self::U64 | Self::USize | Self::F64 => 8,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Slot {
    offset: u64,
    kind: Kind,
}

fn offset(words: u64, bytes: u64) -> Option<u64> {
    // These are the pinned LP64 artifact's offsets, not host usize arithmetic.
    words.checked_mul(8)?.checked_add(bytes)
}

pub(super) fn projection(ty: &IrType, expr: &IrExpr) -> Option<(u64, Slot)> {
    let kind = Kind::from_type(ty)?;
    let (receiver, offset) = match expr {
        IrExpr::UProj { i, x } if kind == Kind::USize => (*x, offset(*i, 0)?),
        IrExpr::SProj { n, offset: bytes, x } if kind != Kind::USize => {
            (*x, offset(*n, *bytes)?)
        }
        _ => return None,
    };
    Some((receiver, Slot { offset, kind }))
}

pub(super) fn store(stmt: &IrStmt, receiver: u64, shape: Shape) -> Option<(Slot, u64)> {
    let object_end = offset(shape.fields, 0)?;
    let word_end = object_end.checked_add(offset(shape.words, 0)?)?;
    let end = word_end.checked_add(shape.bytes)?;
    let (slot, value, lower, upper) = match stmt {
        IrStmt::USet { x, i, y } if *x == receiver => (
            Slot { offset: offset(*i, 0)?, kind: Kind::USize },
            *y,
            object_end,
            word_end,
        ),
        IrStmt::SSet { x, i, offset: bytes, y, ty } if *x == receiver => {
            let kind = Kind::from_type(ty)?;
            if kind == Kind::USize {
                return None;
            }
            (Slot { offset: offset(*i, *bytes)?, kind }, *y, word_end, end)
        }
        _ => return None,
    };
    (slot.offset >= lower && slot.offset.checked_add(slot.kind.width())? <= upper)
        .then_some((slot, value))
}

#[derive(Default)]
pub(super) struct Writes(BTreeMap<u64, (Slot, u64)>);

impl Writes {
    pub(super) fn insert(&mut self, slot: Slot, value: u64) -> bool {
        let Some(end) = slot.offset.checked_add(slot.kind.width()) else {
            return false;
        };
        if self.0.range(..slot.offset).next_back().is_some_and(|(_, (prior, _))| {
            prior.offset.saturating_add(prior.kind.width()) > slot.offset
        }) || self.0.range(slot.offset..).next().is_some_and(|(next, _)| *next < end) {
            return false;
        }
        self.0.insert(slot.offset, (slot, value));
        true
    }
}

pub(super) fn equivalent(
    shape: Shape,
    receiver: u64,
    writes: &Writes,
    initializers: &Writes,
    projections: &BTreeMap<u64, (u64, Slot)>,
    meter: &mut Meter,
) -> Result<bool> {
    meter.charge(writes.0.len().saturating_add(initializers.0.len()))?;
    let Some(mut position) = offset(shape.fields, 0) else {
        return Ok(false);
    };
    let Some(end) = offset(shape.fields, 0)
        .and_then(|start| start.checked_add(offset(shape.words, shape.bytes)?))
    else {
        return Ok(false);
    };
    let mut matched_writes = 0usize;
    for (slot, value) in initializers.0.values() {
        if slot.offset != position {
            return Ok(false);
        }
        let Some(next) = position.checked_add(slot.kind.width()) else {
            return Ok(false);
        };
        position = next;
        if let Some((written_slot, written_value)) = writes.0.get(&slot.offset) {
            if slot != written_slot || value != written_value {
                return Ok(false);
            }
            matched_writes += 1;
        } else if projections.get(value) != Some(&(receiver, *slot)) {
            return Ok(false);
        }
    }
    // Also reject a write hidden inside a differently sized fresh field, or
    // omitted by an otherwise complete initializer stream.
    Ok(position == end && matched_writes == writes.0.len())
}

#[cfg(test)]
mod tests;
