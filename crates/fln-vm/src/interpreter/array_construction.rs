//! List/Array representation bridges and empty-array construction.
//!
//! Compiled lists use a fieldless tag-0 constructor for nil and tag 1 with two
//! object fields for cons. The ABI's scalar-0 nil is also accepted on input;
//! output always uses the constructor shape that compiled case analysis reads.
//! Validate the entire spine so a malformed tail cannot publish a truncated
//! array. Both directions retain payloads before releasing their input.

use super::{
    IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, array_value, expect_arity, nat_as_usize,
    with_nat_view,
};

const MAX_REPLICATE_BYTES: usize = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    FromList,
    ToList,
    Empty,
    Replicate,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        Some(match row {
            "extern:Array.mk" => Self::FromList,
            "extern:Array.toList" => Self::ToList,
            "extern:Array.emptyWithCapacity" | "extern:Array.mkEmpty" => Self::Empty,
            "extern:Array.replicate" => Self::Replicate,
            _ => return None,
        })
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        expect_arity(row, args, if self == Self::Replicate { 2 } else { 1 })?;
        let result = match self {
            Self::Replicate => {
                let count = nat_as_usize(&args[0], "Array.replicate", 0)?;
                let requested =
                    count.and_then(|count| count.checked_mul(std::mem::size_of::<Obj>()));
                let limit = || IntrinsicFailure::ArrayResource {
                    allowed: MAX_REPLICATE_BYTES as u64,
                    observed: requested.map_or(u64::MAX, |bytes| bytes as u64),
                };
                let Some((count, bytes)) = count.zip(requested) else {
                    return Err(limit());
                };
                if bytes > MAX_REPLICATE_BYTES {
                    return Err(limit());
                }
                let mut items = Vec::new();
                items.try_reserve_exact(count).map_err(|_| limit())?;
                items.resize_with(count, || args[1].clone_ref());
                Obj::mk_array(items)
            }
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
                    if header.tag == 0 && header.other == 0 {
                        break;
                    }
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
                let mut result = Obj::mk_ctor(0, Vec::new(), &[]);
                for index in (0..size).rev() {
                    result = Obj::mk_ctor(1, vec![args[0].array_child(index), result], &[]);
                }
                result
            }
            Self::Empty => {
                // As with ByteArray.emptyWithCapacity, capacity is a hint,
                // not permission to allocate an arbitrary attacker-sized buffer.
                // Start empty; consuming pushes grow this storage geometrically
                // without turning an untrusted hint into an allocation request.
                with_nat_view(&args[0], "Array.emptyWithCapacity", 0, |_| ())?;
                Obj::mk_array(Vec::new())
            }
        };
        Ok(IntrinsicResult::raw_object(result))
    }
}
