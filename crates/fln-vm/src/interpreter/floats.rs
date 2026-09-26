//! Boxed Float/Float32 intrinsics over Marrow objects.
//!
//! The pin's `lean.h` scalar arithmetic and conversion functions take C
//! scalars, while FLBC registers always own `Obj`s. Floating values and
//! 64-bit integer carriers use the pin's zero-field constructor boxes;
//! narrow integer and Boolean results use tagged immediates. This is a
//! per-row adapter, not permission for any scalar intrinsic to return a heap
//! object. Transcendentals and ambient-library formatting remain unsupported.

use super::{IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, expect_arity, type_mismatch};

// object.cpp's public to_bits contract fixes these values rather than using
// the host library's implementation-defined quiet-NaN payload.
const QUIET_NAN64_BITS: u64 = 0x7ff8_0000_0000_0000;
const QUIET_NAN32_BITS: u32 = 0x7fc0_0000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Width {
    Binary64,
    Binary32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Integer {
    U8,
    U16,
    U32,
    U64,
    USize,
    I8,
    I16,
    I32,
    I64,
    ISize,
}

impl Integer {
    fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "UInt8" => Self::U8,
            "UInt16" => Self::U16,
            "UInt32" => Self::U32,
            "UInt64" => Self::U64,
            "USize" => Self::USize,
            "Int8" => Self::I8,
            "Int16" => Self::I16,
            "Int32" => Self::I32,
            "Int64" => Self::I64,
            "ISize" => Self::ISize,
            _ => return None,
        })
    }

    const fn boxed(self) -> bool {
        matches!(self, Self::U64 | Self::USize | Self::I64 | Self::ISize)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Operation {
    Add,
    Sub,
    Mul,
    Div,
    Neg,
    Abs,
    Eq,
    Le,
    Lt,
    IsNaN,
    IsFinite,
    IsInf,
    OfBits,
    ToBits,
    ConvertWidth,
    ToInteger(Integer),
    FromInteger(Integer),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Intrinsic {
    width: Width,
    operation: Operation,
}

// Instantiate at the operand's native precision. In particular, arithmetic
// and integer-to-Float32 conversion never take an intermediate f64 step.
macro_rules! evaluate {
    ($this:ident, $row:ident, $args:ident, $type:ty, $argument:ident, $result:ident,
     $bits_result:path, $converted:ident, $nan_bits:ident) => {{
        let operation = $this.operation;
        if let Operation::FromInteger(integer) = operation {
            let value = &$args[0];
            let label = "integer to float";
            let number: $type = match integer {
                Integer::U8 => super::byte_argument(value, label, 0)? as $type,
                Integer::U16 => super::uint16_argument(value, label, 0)? as $type,
                Integer::U32 => super::uint32_argument(value, label, 0)? as $type,
                Integer::U64 | Integer::USize => wide_argument(value, label, 0)? as $type,
                Integer::I8 => super::int8_argument(value, label, 0)? as $type,
                Integer::I16 => super::int16_argument(value, label, 0)? as $type,
                Integer::I32 => super::int32_argument(value, label, 0)? as $type,
                Integer::I64 | Integer::ISize => wide_argument(value, label, 0)? as i64 as $type,
            };
            return Ok($result(number));
        }
        if operation == Operation::OfBits {
            return Ok(match $this.width {
                Width::Binary64 => {
                    let bits = wide_argument(&$args[0], "Float.ofBits", 0)?;
                    let value = f64::from_bits(bits);
                    binary64_result(if value.is_nan() {
                        f64::from_bits(QUIET_NAN64_BITS)
                    } else {
                        value
                    })
                }
                Width::Binary32 => {
                    let bits = super::uint32_argument(&$args[0], "Float32.ofBits", 0)?;
                    let value = f32::from_bits(bits);
                    binary32_result(if value.is_nan() {
                        f32::from_bits(QUIET_NAN32_BITS)
                    } else {
                        value
                    })
                }
            });
        }
        let value = $argument(&$args[0], 0)?;
        Ok(match operation {
            Operation::Add => $result(value + $argument(&$args[1], 1)?),
            Operation::Sub => $result(value - $argument(&$args[1], 1)?),
            Operation::Mul => $result(value * $argument(&$args[1], 1)?),
            Operation::Div => $result(value / $argument(&$args[1], 1)?),
            Operation::Neg => $result(-value),
            Operation::Abs => $result(value.abs()),
            Operation::Eq => boolean_result(value == $argument(&$args[1], 1)?),
            Operation::Le => boolean_result(value <= $argument(&$args[1], 1)?),
            Operation::Lt => boolean_result(value < $argument(&$args[1], 1)?),
            Operation::IsNaN => boolean_result(value.is_nan()),
            Operation::IsFinite => boolean_result(value.is_finite()),
            Operation::IsInf => boolean_result(value.is_infinite()),
            Operation::ToBits => {
                // object.cpp normalizes the sign, signaling bit, and payload
                // of every NaN at this public observation boundary.
                let bits = if value.is_nan() {
                    $nan_bits
                } else {
                    value.to_bits()
                };
                $bits_result(bits)
            }
            Operation::ConvertWidth => $converted(value),
            Operation::ToInteger(integer) => match integer {
                // Rust float-to-int casts match lean.h's NaN-to-zero,
                // saturation, and truncation rules. Cast at the destination
                // width before taking a signed value's ABI carrier bits.
                Integer::U8 => super::uint8_result(value as u8),
                Integer::U16 => super::uint16_result(value as u16),
                Integer::U32 => super::uint32_result(value as u32),
                Integer::U64 | Integer::USize => wide_result(value as u64),
                Integer::I8 => super::int8_result(value as i8),
                Integer::I16 => super::int16_result(value as i16),
                Integer::I32 => super::int32_result(value as i32),
                Integer::I64 | Integer::ISize => wide_result(value as i64 as u64),
            },
            Operation::OfBits | Operation::FromInteger(_) => {
                return Err(VmRefusal::UnsupportedIntrinsic {
                    row: $row.to_string(),
                }
                .into());
            }
        })
    }};
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        let (family, method) = row.strip_prefix("extern:")?.split_once('.')?;
        let width = match family {
            "Float" => Width::Binary64,
            "Float32" => Width::Binary32,
            _ => {
                let integer = Integer::from_name(family)?;
                let width = match method {
                    "toFloat" => Width::Binary64,
                    "toFloat32" => Width::Binary32,
                    _ => return None,
                };
                return Some(Self {
                    width,
                    operation: Operation::FromInteger(integer),
                });
            }
        };
        let operation = match method {
            "add" => Operation::Add,
            "sub" => Operation::Sub,
            "mul" => Operation::Mul,
            "div" => Operation::Div,
            "neg" => Operation::Neg,
            "abs" => Operation::Abs,
            "beq" => Operation::Eq,
            "decLe" => Operation::Le,
            "decLt" => Operation::Lt,
            "isNaN" => Operation::IsNaN,
            "isFinite" => Operation::IsFinite,
            "isInf" => Operation::IsInf,
            "ofBits" => Operation::OfBits,
            "toBits" => Operation::ToBits,
            "toFloat32" if width == Width::Binary64 => Operation::ConvertWidth,
            "toFloat" if width == Width::Binary32 => Operation::ConvertWidth,
            _ => Operation::ToInteger(Integer::from_name(method.strip_prefix("to")?)?),
        };
        Some(Self { width, operation })
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        let arity = if matches!(
            self.operation,
            Operation::Add
                | Operation::Sub
                | Operation::Mul
                | Operation::Div
                | Operation::Eq
                | Operation::Le
                | Operation::Lt
        ) {
            2
        } else {
            1
        };
        expect_arity(row, args, arity)?;
        match self.width {
            Width::Binary64 => {
                evaluate!(
                    self,
                    row,
                    args,
                    f64,
                    binary64_argument,
                    binary64_result,
                    wide_result,
                    narrow,
                    QUIET_NAN64_BITS
                )
            }
            Width::Binary32 => {
                evaluate!(
                    self,
                    row,
                    args,
                    f32,
                    binary32_argument,
                    binary32_result,
                    super::uint32_result,
                    widen,
                    QUIET_NAN32_BITS
                )
            }
        }
    }

    pub(super) fn result_kind_matches(self, value: &Obj) -> bool {
        let boxed = match self.operation {
            Operation::Eq
            | Operation::Le
            | Operation::Lt
            | Operation::IsNaN
            | Operation::IsFinite
            | Operation::IsInf => false,
            Operation::ToBits => self.width == Width::Binary64,
            Operation::ToInteger(integer) => integer.boxed(),
            _ => true,
        };
        if !boxed {
            return value.is_scalar();
        }
        let wide = match self.operation {
            Operation::ToInteger(_) => true,
            Operation::ConvertWidth => self.width == Width::Binary32,
            _ => self.width == Width::Binary64,
        };
        scalar_box(value)
            && if wide {
                value.try_ctor_scalar_u64(0).is_some()
            } else {
                value.try_ctor_scalar_u32(0).is_some()
            }
    }
}

fn scalar_box(value: &Obj) -> bool {
    !value.is_scalar() && {
        let header = value.header();
        header.tag == 0 && header.other == 0
    }
}

pub(super) fn wide_argument(
    value: &Obj,
    operation: &'static str,
    index: usize,
) -> Result<u64, VmRefusal> {
    if scalar_box(value)
        && let Some(bits) = value.try_ctor_scalar_u64(0)
    {
        return Ok(bits);
    }
    Err(type_mismatch(
        operation,
        index,
        "boxed 64-bit scalar",
        value,
    ))
}

fn binary64_argument(value: &Obj, index: usize) -> Result<f64, VmRefusal> {
    wide_argument(value, "Float", index).map(f64::from_bits)
}

fn binary32_argument(value: &Obj, index: usize) -> Result<f32, VmRefusal> {
    if scalar_box(value)
        && let Some(bits) = value.try_ctor_scalar_u32(0)
    {
        return Ok(f32::from_bits(bits));
    }
    Err(type_mismatch("Float32", index, "boxed Float32", value))
}

pub(super) fn wide_result(bits: u64) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_ctor(0, Vec::new(), &bits.to_ne_bytes()))
}

/// The integer families that already execute in Golem use the same boxed
/// carrier as Float.toBits. Keep their result adaptation explicit so a new
/// unsupported scalar row cannot acquire heap-result permission by accident.
pub(super) fn boxed_integer_result(row: &str) -> bool {
    if row == "extern:mixHash" {
        return true;
    }
    let Some((family, method)) = row
        .strip_prefix("extern:")
        .and_then(|name| name.split_once('.'))
    else {
        return false;
    };
    let Some(integer) = Integer::from_name(family) else {
        return false;
    };
    if let Some(destination) = method.strip_prefix("to").and_then(Integer::from_name) {
        return destination.boxed();
    }
    integer.boxed()
        && matches!(
            method,
            "add"
                | "sub"
                | "mul"
                | "div"
                | "mod"
                | "land"
                | "lor"
                | "xor"
                | "shiftLeft"
                | "shiftRight"
                | "complement"
                | "neg"
                | "abs"
                | "log2"
                | "ofNat"
                | "ofNatLT"
                | "ofBitVec"
                | "ofInt"
        )
}

fn binary64_result(value: f64) -> IntrinsicResult {
    wide_result(value.to_bits())
}

fn binary32_result(value: f32) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_ctor(0, Vec::new(), &value.to_ne_bytes()))
}

fn narrow(value: f64) -> IntrinsicResult {
    binary32_result(value as f32)
}

fn widen(value: f32) -> IntrinsicResult {
    binary64_result(f64::from(value))
}

fn boolean_result(value: bool) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat(usize::from(value)))
}
