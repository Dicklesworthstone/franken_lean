//! Native array updates over Marrow handles. Like the existing Array.push
//! adapter, updates copy the object slots instead of mutating a shared array.
//! The checked index must be established before allocating or retaining any
//! output slots; proof-erased bounds violations are typed VM refusals.
use super::{
    IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, array_value, expect_arity, nat_as_usize,
    uint64_argument,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    Pop,
    Set,
    Uset,
    Swap,
    SwapIfInBounds,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        Some(match row {
            "extern:Array.pop" => Self::Pop,
            "extern:Array.set" => Self::Set,
            "extern:Array.uset" => Self::Uset,
            "extern:Array.swap" => Self::Swap,
            "extern:Array.swapIfInBounds" => Self::SwapIfInBounds,
            _ => return None,
        })
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        expect_arity(row, args, if self == Self::Pop { 1 } else { 3 })?;
        let operation = match self {
            Self::Pop => "Array.pop",
            Self::Set => "Array.set",
            Self::Uset => "Array.uset",
            Self::Swap => "Array.swap",
            Self::SwapIfInBounds => "Array.swapIfInBounds",
        };
        let array = &args[0];
        let (size, _) = array_value(array, operation, 0)?;
        if self == Self::Pop {
            return Ok(IntrinsicResult::raw_object(if size == 0 {
                array.clone_ref()
            } else {
                Obj::mk_array(
                    (0..size - 1)
                        .map(|index| array.array_child(index))
                        .collect(),
                )
            }));
        }
        // USize is a full-width boxed scalar in FLBC, not a tagged Nat.
        // Nat indices retain their arbitrary precision: an mpz is never
        // truncated to its low word and accidentally treated as in bounds.
        let first = if self == Self::Uset {
            uint64_argument(&args[1], operation, 1)? as usize
        } else {
            nat_as_usize(&args[1], operation, 1)?.unwrap_or(usize::MAX)
        };
        match self {
            Self::Set | Self::Uset => {
                check_index(first, size)?;
                let updated = (0..size)
                    .map(|index| {
                        if index == first {
                            args[2].clone_ref()
                        } else {
                            array.array_child(index)
                        }
                    })
                    .collect();
                Ok(IntrinsicResult::raw_object(Obj::mk_array(updated)))
            }
            Self::Swap | Self::SwapIfInBounds => {
                let second = nat_as_usize(&args[2], operation, 2)?.unwrap_or(usize::MAX);
                if self == Self::SwapIfInBounds && (first >= size || second >= size) {
                    return Ok(IntrinsicResult::raw_object(array.clone_ref()));
                }
                check_index(first, size)?;
                check_index(second, size)?;
                if first == second {
                    return Ok(IntrinsicResult::raw_object(array.clone_ref()));
                }
                let updated = (0..size)
                    .map(|index| {
                        array.array_child(if index == first {
                            second
                        } else if index == second {
                            first
                        } else {
                            index
                        })
                    })
                    .collect();
                Ok(IntrinsicResult::raw_object(Obj::mk_array(updated)))
            }
            Self::Pop => unreachable!("pop returned before index processing"),
        }
    }
}

fn check_index(index: usize, size: usize) -> Result<(), VmRefusal> {
    if index < size {
        Ok(())
    } else {
        Err(VmRefusal::ArrayIndexOutOfBounds { index, size })
    }
}
