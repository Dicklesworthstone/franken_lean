//! List/Array representation bridges and empty-array construction.
//!
//! The List runtime shape is nil = scalar 0, cons = tag 1 with two object
//! fields. Validate the entire spine; a malformed tail must not turn into a
//! successful, truncated array. Both directions are iterative and retain each
//! payload before the input container can be released.

use super::{
    IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, array_value, expect_arity, with_nat_view,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    FromList,
    ToList,
    Empty,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        Some(match row {
            "extern:Array.mk" => Self::FromList,
            "extern:Array.toList" => Self::ToList,
            "extern:Array.emptyWithCapacity" | "extern:Array.mkEmpty" => Self::Empty,
            _ => return None,
        })
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        expect_arity(row, args, 1)?;
        let result = match self {
            Self::FromList => {
                let mut cursor = args[0].clone_ref();
                let mut items = Vec::new();
                loop {
                    if cursor.is_scalar() {
                        if cursor.unbox() == 0 {
                            break;
                        }
                        return Err(VmRefusal::InvalidCtorObject.into());
                    }
                    let header = cursor.header();
                    if header.tag != 1 || header.other != 2 {
                        return Err(VmRefusal::InvalidCtorObject.into());
                    }
                    let head = cursor
                        .try_ctor_child(0)
                        .ok_or(VmRefusal::InvalidCtorObject)?;
                    let tail = cursor
                        .try_ctor_child(1)
                        .ok_or(VmRefusal::InvalidCtorObject)?;
                    items.push(head);
                    cursor = tail;
                }
                Obj::mk_array(items)
            }
            Self::ToList => {
                let (size, _) = array_value(&args[0], "Array.toList", 0)?;
                let mut result = Obj::mk_nat(0);
                for index in (0..size).rev() {
                    result = Obj::mk_ctor(1, vec![args[0].array_child(index), result], &[]);
                }
                result
            }
            Self::Empty => {
                // As with ByteArray.emptyWithCapacity, capacity is a hint,
                // not permission to allocate an arbitrary attacker-sized buffer.
                // The VM's copy-always arrays expose the canonical empty value.
                with_nat_view(&args[0], "Array.emptyWithCapacity", 0, |_| ())?;
                Obj::mk_array(Vec::new())
            }
        };
        Ok(IntrinsicResult::raw_object(result))
    }
}
