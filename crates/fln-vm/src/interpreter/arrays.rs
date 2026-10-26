//! Native array updates over owned Marrow handles. Exclusive arrays reuse
//! their slots; shared arrays retain independent copy-on-write values.
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
        args: Vec<Obj>,
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        expect_arity(row, &args, if self == Self::Pop { 1 } else { 3 })?;
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
            return Ok(IntrinsicResult::raw_object(
                args.into_iter()
                    .next()
                    .expect("checked pop arity")
                    .try_array_pop()
                    .expect("validated array header"),
            ));
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
                let mut args = args.into_iter();
                let array = args.next().expect("checked set arity");
                let value = args.nth(1).expect("checked set value");
                Ok(IntrinsicResult::raw_object(
                    array
                        .try_array_set(first, value)
                        .expect("validated header and index"),
                ))
            }
            Self::Swap | Self::SwapIfInBounds => {
                let second = nat_as_usize(&args[2], operation, 2)?.unwrap_or(usize::MAX);
                if self == Self::SwapIfInBounds && (first >= size || second >= size) {
                    return Ok(IntrinsicResult::raw_object(
                        args.into_iter().next().expect("checked swap arity"),
                    ));
                }
                check_index(first, size)?;
                check_index(second, size)?;
                Ok(IntrinsicResult::raw_object(
                    args.into_iter()
                        .next()
                        .expect("checked swap arity")
                        .try_array_swap(first, second)
                        .expect("validated header and indices"),
                ))
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

#[cfg(test)]
mod tests {
    use super::super::{IntrinsicImplementation, invoke_intrinsic};
    use super::*;

    #[test]
    fn owned_dispatch_reuses_unique_arrays_and_keeps_shared_snapshots() {
        let push = |array, value| {
            invoke_intrinsic(
                IntrinsicImplementation::ArrayPush,
                "extern:Array.push",
                vec![array, Obj::mk_nat(value)],
                1024,
            )
            .unwrap_or_else(|_| panic!("valid native push"))
            .into_object()
        };
        let array = push(Obj::mk_array(Vec::new()), 7);
        let identity = array.identity_token();
        let array = push(array, 11);
        assert_eq!(
            array.identity_token(),
            identity,
            "the dispatch must not clone owned arguments"
        );
        let snapshot = array.clone_ref();
        let array = push(array, 13);
        assert_eq!(snapshot.array_view().0, 2);
        assert_eq!(snapshot.array_child(1).unbox(), 11);
        assert_ne!(array.identity_token(), snapshot.identity_token());
        let identity = array.identity_token();
        let array = Intrinsic::Set
            .invoke(
                "extern:Array.set",
                vec![array, Obj::mk_nat(0), Obj::mk_nat(42)],
            )
            .unwrap_or_else(|_| panic!("valid native set"))
            .into_object();
        assert_eq!(array.identity_token(), identity);
        assert_eq!(array.array_child(0).unbox(), 42);
        assert_eq!(snapshot.array_child(0).unbox(), 7);
        let array = Intrinsic::Swap
            .invoke(
                "extern:Array.swap",
                vec![array, Obj::mk_nat(0), Obj::mk_nat(2)],
            )
            .unwrap_or_else(|_| panic!("valid native swap"))
            .into_object();
        let array = Intrinsic::Pop
            .invoke("extern:Array.pop", vec![array])
            .unwrap_or_else(|_| panic!("valid native pop"))
            .into_object();
        assert_eq!(array.identity_token(), identity);
        assert_eq!(array.array_view().0, 2);
        assert_eq!(array.array_child(0).unbox(), 13);
    }
}
