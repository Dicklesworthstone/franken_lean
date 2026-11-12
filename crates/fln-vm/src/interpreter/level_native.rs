//! Native universe-level primitives used by compiled metaprograms.
//!
//! The extern census owns the call contract. Level equality is structural,
//! including the max/imax order, rather than kernel universe equivalence.
//! Both operands cross the bounded converter membrane before comparison, so
//! cached hashes or pointer identity cannot validate a malformed object.

use std::collections::HashSet;

use super::{
    IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, bool_value, expect_arity, floats,
    macro_native, nat_as_usize,
};
use fln_core::level::{LMVarId, Level, LevelData, LevelView, MAX_LEVEL_DEPTH};
use fln_rt::convert::{Conversion, ConvertError, inject_level};
use fln_rt::native_heap::NativeHeap;

const MAX_LEVEL_PAIRS: usize = 1_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    Beq,
    MkData,
    Succ,
    Max,
    IMax,
    Param,
    MVar,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        match row {
            "extern:Lean.Level.beq" => Some(Self::Beq),
            "extern:Lean.Level.mkData" => Some(Self::MkData),
            "mirror:Lean.Level.succ._override" => Some(Self::Succ),
            "mirror:Lean.Level.max._override" => Some(Self::Max),
            "mirror:Lean.Level.imax._override" => Some(Self::IMax),
            "mirror:Lean.Level.param._override" => Some(Self::Param),
            "mirror:Lean.Level.mvar._override" => Some(Self::MVar),
            _ => None,
        }
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        match self {
            Self::Succ | Self::Max | Self::IMax => {
                let arity = if self == Self::Succ { 1 } else { 2 };
                expect_arity(row, args, arity)?;
                let mut heap = NativeHeap::new();
                let mut conversion = Conversion::new();
                let left = project_level(&mut conversion, &args[0])?;
                let right = if arity == 2 {
                    Some(project_level(&mut conversion, &args[1])?)
                } else {
                    None
                };
                let value = match (self, right) {
                    (Self::Succ, None) => left.succ(),
                    (Self::Max, Some(right)) => Level::max(left, right),
                    (Self::IMax, Some(right)) => Level::imax(left, right),
                    _ => return Err(VmRefusal::InvalidCtorObject.into()),
                }
                .map_err(|error| IntrinsicFailure::MirrorResource {
                    resource: "universe level depth",
                    allowed: u64::from(MAX_LEVEL_DEPTH),
                    observed: u64::from(error.depth),
                })?;
                let handle = heap.alloc(value);
                Ok(IntrinsicResult::raw_object(
                    inject_level(&heap, handle).map_err(conversion_failure)?,
                ))
            }
            Self::Param | Self::MVar => {
                expect_arity(row, args, 1)?;
                let name = macro_native::name(&args[0])?;
                let level = if self == Self::Param {
                    Level::param(name)
                } else {
                    Level::mvar(LMVarId(name))
                };
                let mut heap = NativeHeap::new();
                let handle = heap.alloc(level);
                Ok(IntrinsicResult::raw_object(
                    inject_level(&heap, handle).map_err(conversion_failure)?,
                ))
            }
            Self::Beq => {
                expect_arity(row, args, 2)?;
                let mut conversion = Conversion::new();
                let left = project_level(&mut conversion, &args[0])?;
                let right = project_level(&mut conversion, &args[1])?;
                check_equality_pairs(&left, &right, MAX_LEVEL_PAIRS)?;
                let equal = left == right;
                // These census rows use borrowed arguments and an owned
                // result even when that result is a tagged Boolean.
                Ok(IntrinsicResult::owned(Obj::mk_nat(usize::from(equal))))
            }
            Self::MkData => {
                expect_arity(row, args, 4)?;
                let hash = floats::wide_argument(&args[0], "Lean.Level.mkData", 0)?;
                let depth = nat_as_usize(&args[1], "Lean.Level.mkData", 1)?;
                let has_mvar = bool_value(&args[2], "Lean.Level.mkData", 2)?;
                let has_param = bool_value(&args[3], "Lean.Level.mkData", 3)?;
                let Some(depth) = depth.filter(|depth| *depth <= MAX_LEVEL_DEPTH as usize) else {
                    return Err(IntrinsicFailure::MirrorResource {
                        resource: "universe level depth",
                        allowed: u64::from(MAX_LEVEL_DEPTH),
                        observed: depth.map_or(u64::MAX, |depth| depth as u64),
                    });
                };
                let data = LevelData::pack(hash, depth as u32, has_mvar, has_param)
                    .map_err(|_| VmRefusal::InvalidCtorObject)?;
                Ok(IntrinsicResult::owned(Obj::mk_ctor(
                    0,
                    Vec::new(),
                    &data.0.to_ne_bytes(),
                )))
            }
        }
    }
}

fn project_level(conversion: &mut Conversion, value: &Obj) -> Result<Level, IntrinsicFailure> {
    // Avoid an unaccounted structural comparison during cross-operand
    // interning. Conversion still shares its aggregate node and byte budgets.
    let mut heap = NativeHeap::new();
    let handle = conversion
        .project_level(&mut heap, value)
        .map_err(conversion_failure)?;
    heap.get(handle)
        .cloned()
        .map_err(|_| VmRefusal::InvalidCtorObject.into())
}

pub(super) fn check_equality_pairs(
    left: &Level,
    right: &Level,
    allowed: usize,
) -> Result<usize, IntrinsicFailure> {
    let mut visited = HashSet::new();
    let mut stack = vec![(left, right)];
    while let Some((left, right)) = stack.pop() {
        let pair = (left.allocation_identity(), right.allocation_identity());
        if !visited.insert(pair) {
            continue;
        }
        if visited.len() > allowed {
            return Err(IntrinsicFailure::MirrorResource {
                resource: "universe level comparison pairs",
                allowed: allowed as u64,
                observed: visited.len() as u64,
            });
        }
        if pair.0 == pair.1 || left.data() != right.data() {
            continue;
        }
        match (left.view(), right.view()) {
            (LevelView::Succ(left), LevelView::Succ(right)) => stack.push((left, right)),
            (LevelView::Max(ll, lr), LevelView::Max(rl, rr))
            | (LevelView::IMax(ll, lr), LevelView::IMax(rl, rr)) => {
                stack.push((lr, rr));
                stack.push((ll, rl));
            }
            _ => {}
        }
    }
    Ok(visited.len())
}

fn conversion_failure(error: ConvertError) -> IntrinsicFailure {
    match error {
        ConvertError::NodeBudgetExhausted {
            visited, budget, ..
        } => IntrinsicFailure::MirrorResource {
            resource: "universe level conversion nodes",
            allowed: budget as u64,
            observed: visited as u64,
        },
        ConvertError::ByteBudgetExhausted {
            visited, budget, ..
        } => IntrinsicFailure::MirrorResource {
            resource: "universe level conversion bytes",
            allowed: budget as u64,
            observed: visited as u64,
        },
        _ => VmRefusal::InvalidCtorObject.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_level_equality_bounds_differently_shared_pairs_before_comparison() {
        fn shared(depth: usize) -> Level {
            let mut value = Level::zero();
            for _ in 0..depth {
                value = Level::max(value.clone(), value).unwrap();
            }
            value
        }
        fn separate_prefix(depth: usize, shared_depth: usize) -> Level {
            if depth == 0 {
                shared(shared_depth)
            } else {
                Level::max(
                    separate_prefix(depth - 1, shared_depth),
                    separate_prefix(depth - 1, shared_depth),
                )
                .unwrap()
            }
        }
        let left = separate_prefix(2, 2);
        let mut right = separate_prefix(2, 0);
        for _ in 0..2 {
            right = Level::max(right.clone(), right).unwrap();
        }
        assert_eq!(left, right);
        assert!(matches!(
            check_equality_pairs(&left, &right, 24),
            Err(IntrinsicFailure::MirrorResource {
                resource: "universe level comparison pairs",
                ..
            })
        ));
        assert!(check_equality_pairs(&left, &right, 31).is_ok());
        let mut conversion = Conversion::new();
        let first = project_level(&mut conversion, &Obj::mk_nat(0))
            .unwrap_or_else(|_| panic!("first level"));
        let second = project_level(&mut conversion, &Obj::mk_nat(0))
            .unwrap_or_else(|_| panic!("second level"));
        assert_ne!(first.allocation_identity(), second.allocation_identity());
    }
}
