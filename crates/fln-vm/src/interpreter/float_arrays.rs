//! Packed FloatArray primitives over Marrow's checked scalar-array storage.
//!
//! The pin stores FloatArray as eight-byte elements (lean.h:1131-1194 and
//! object.cpp:2608-2645). Observations borrow the live bytes; updates retain
//! shared snapshots. A consuming push uses the existing native COW export,
//! so repeated pushes preserve its geometric capacity growth. All floating
//! payloads are copied as bits, including signed zero and NaN payloads.

use super::{
    IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, array_value, expect_arity, floats, nat_as_usize,
    type_mismatch, usize_argument, with_nat_view,
};

const ELEMENT_BYTES: usize = std::mem::size_of::<f64>();
const MAX_OUTPUT_BYTES: usize = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    FromArray,
    ToArray,
    Empty,
    Push,
    Size,
    USize,
    Get,
    GetBang,
    Uget,
    Set,
    SetBang,
    Uset,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        Some(match row {
            "extern:FloatArray.mk" => Self::FromArray,
            "extern:FloatArray.data" => Self::ToArray,
            "extern:FloatArray.emptyWithCapacity" => Self::Empty,
            "extern:FloatArray.push" => Self::Push,
            "extern:FloatArray.size" => Self::Size,
            "extern:FloatArray.usize" => Self::USize,
            "extern:FloatArray.get" => Self::Get,
            "extern:FloatArray.get!" => Self::GetBang,
            "extern:FloatArray.uget" => Self::Uget,
            "extern:FloatArray.set" => Self::Set,
            "extern:FloatArray.set!" => Self::SetBang,
            "extern:FloatArray.uset" => Self::Uset,
            _ => return None,
        })
    }

    pub(super) fn has_wide_result(self) -> bool {
        matches!(self, Self::Get | Self::GetBang | Self::Uget | Self::USize)
    }

    fn operation(self) -> &'static str {
        match self {
            Self::FromArray => "FloatArray.mk",
            Self::ToArray => "FloatArray.data",
            Self::Empty => "FloatArray.emptyWithCapacity",
            Self::Push => "FloatArray.push",
            Self::Size => "FloatArray.size",
            Self::USize => "FloatArray.usize",
            Self::Get => "FloatArray.get",
            Self::GetBang => "FloatArray.get!",
            Self::Uget => "FloatArray.uget",
            Self::Set => "FloatArray.set",
            Self::SetBang => "FloatArray.set!",
            Self::Uset => "FloatArray.uset",
        }
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: Vec<Obj>,
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        let arity = match self {
            Self::Set | Self::SetBang | Self::Uset => 3,
            Self::Get | Self::GetBang | Self::Uget | Self::Push => 2,
            _ => 1,
        };
        expect_arity(row, &args, arity)?;
        let operation = self.operation();
        if self == Self::Empty {
            // As with the other native array families, capacity is a hint.
            // Validate it as Nat but do not allocate an attacker-sized reserve.
            with_nat_view(&args[0], operation, 0, |_| ())?;
            return Ok(IntrinsicResult::owned(Obj::mk_sarray(8, &[])));
        }
        if self == Self::FromArray {
            let (size, _) = array_value(&args[0], operation, 0)?;
            let requested = output_size(size)?;
            // Validate every boxed Float before reserving an output buffer.
            for index in 0..size {
                floats::wide_argument(&args[0].array_child(index), operation, 0)?;
            }
            let mut bytes = buffer(requested)?;
            for index in 0..size {
                bytes.extend_from_slice(
                    &floats::wide_argument(&args[0].array_child(index), operation, 0)?
                        .to_ne_bytes(),
                );
            }
            return Ok(IntrinsicResult::owned(Obj::mk_sarray(8, &bytes)));
        }

        let bytes = payload(&args[0], operation)?;
        let size = bytes.len() / ELEMENT_BYTES;
        match self {
            Self::Size => Ok(IntrinsicResult::owned(Obj::mk_nat(size))),
            Self::USize => Ok(floats::wide_result(size as u64)),
            Self::ToArray => {
                let requested = output_size(size)?;
                let mut items = Vec::new();
                items
                    .try_reserve_exact(size)
                    .map_err(|_| allocation_limit(requested))?;
                for word in bytes.chunks_exact(ELEMENT_BYTES) {
                    items.push(Obj::mk_ctor(0, Vec::new(), word));
                }
                Ok(IntrinsicResult::owned(Obj::mk_array(items)))
            }
            Self::Push => {
                let bits = floats::wide_argument(&args[1], operation, 1)?;
                output_size(size.checked_add(1).ok_or_else(|| allocation_limit(usize::MAX))?)?;
                let array = args.into_iter().next().expect("checked push arity");
                array
                    .try_float_array_push(f64::from_bits(bits))
                    .map(IntrinsicResult::owned)
                    .map_err(|_| VmRefusal::InvalidArrayObject.into())
            }
            Self::Get | Self::GetBang | Self::Uget => {
                let index = if self == Self::Uget {
                    usize_argument(&args[1], operation, 1)?
                } else {
                    nat_as_usize(&args[1], operation, 1)?.unwrap_or(usize::MAX)
                };
                if index >= size {
                    if self == Self::GetBang {
                        // Unlike Array.get!, the pin returns +0.0 without
                        // reporting a panic for FloatArray's total lookup.
                        return Ok(floats::wide_result(0));
                    }
                    return Err(VmRefusal::ArrayIndexOutOfBounds { index, size }.into());
                }
                let start = index * ELEMENT_BYTES;
                let word = bytes[start..start + ELEMENT_BYTES]
                    .try_into()
                    .expect("the checked element occupies eight bytes");
                Ok(floats::wide_result(u64::from_ne_bytes(word)))
            }
            Self::Set | Self::SetBang | Self::Uset => {
                let index = if self == Self::Uset {
                    usize_argument(&args[1], operation, 1)?
                } else {
                    nat_as_usize(&args[1], operation, 1)?.unwrap_or(usize::MAX)
                };
                let bits = floats::wide_argument(&args[2], operation, 2)?;
                if index >= size {
                    if self == Self::SetBang {
                        return Ok(IntrinsicResult::owned(
                            args.into_iter().next().expect("checked set arity"),
                        ));
                    }
                    return Err(VmRefusal::ArrayIndexOutOfBounds { index, size }.into());
                }
                let mut updated = buffer(output_size(size)?)?;
                updated.extend_from_slice(bytes);
                let start = index * ELEMENT_BYTES;
                updated[start..start + ELEMENT_BYTES].copy_from_slice(&bits.to_ne_bytes());
                Ok(IntrinsicResult::owned(Obj::mk_sarray(8, &updated)))
            }
            Self::FromArray | Self::Empty => unreachable!("construction returned above"),
        }
    }
}

fn payload<'a>(value: &'a Obj, operation: &'static str) -> Result<&'a [u8], VmRefusal> {
    match value.try_borrow_sarray_view() {
        Some((8, _, _, bytes)) => Ok(bytes),
        _ => Err(type_mismatch(operation, 0, "FloatArray", value)),
    }
}

fn allocation_limit(requested: usize) -> IntrinsicFailure {
    IntrinsicFailure::ArrayResource {
        allowed: MAX_OUTPUT_BYTES as u64,
        observed: u64::try_from(requested).unwrap_or(u64::MAX),
    }
}

fn output_size(elements: usize) -> Result<usize, IntrinsicFailure> {
    let bytes = elements
        .checked_mul(ELEMENT_BYTES)
        .ok_or_else(|| allocation_limit(usize::MAX))?;
    if bytes > MAX_OUTPUT_BYTES {
        return Err(allocation_limit(bytes));
    }
    Ok(bytes)
}

fn buffer(bytes: usize) -> Result<Vec<u8>, IntrinsicFailure> {
    let mut result = Vec::new();
    result
        .try_reserve_exact(bytes)
        .map_err(|_| allocation_limit(bytes))?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn float_array_allocation_bounds_count_elements_without_overflow() {
        assert_eq!(
            output_size(MAX_OUTPUT_BYTES / ELEMENT_BYTES)
                .unwrap_or_else(|_| panic!("bounded float array size")),
            MAX_OUTPUT_BYTES
        );
        for elements in [MAX_OUTPUT_BYTES / ELEMENT_BYTES + 1, usize::MAX] {
            assert!(matches!(
                output_size(elements),
                Err(IntrinsicFailure::ArrayResource { .. })
            ));
        }
    }

    #[test]
    fn float_array_observations_borrow_the_checked_eight_byte_storage() {
        let input = Obj::mk_sarray(8, &(-0.0f64).to_ne_bytes());
        let alias = input.clone_ref();
        let raw = input.try_borrow_sarray_view().unwrap().3;
        assert!(std::ptr::eq(raw, payload(&input, "test").unwrap()));
        assert!(std::ptr::eq(raw, payload(&alias, "test").unwrap()));
        for wrong in [
            Obj::mk_sarray(1, &[0; 8]),
            Obj::mk_sarray(4, &[0; 8]),
            Obj::mk_nat(0),
        ] {
            assert!(matches!(
                payload(&wrong, "test"),
                Err(VmRefusal::TypeMismatch { .. })
            ));
        }
    }
}
