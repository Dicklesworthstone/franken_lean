//! Boxed Float/Float32 intrinsics over Marrow objects.
//!
//! The pin's `lean.h` scalar arithmetic and conversion functions take C
//! scalars, while FLBC registers always own `Obj`s. Floating values and
//! 64-bit integer carriers use the pin's zero-field constructor boxes;
//! narrow integer and Boolean results use tagged immediates. This is a
//! per-row adapter, not permission for any scalar intrinsic to return a heap
//! object. The pin's fixed-decimal formatter returns a normal owned String.
//! The unary math rows (`sqrt` through the transcendentals) and the binary
//! `pow`/`atan2` rows execute on `fln-libm`, the owned deterministic numerics
//! plane (§6.8, D21): bit-identical across hosts by construction, never the
//! platform libm the pin's extern symbols name. `frExp` (pair result) and
//! `scaleB` (Int exponent) remain unsupported.

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

/// One-argument float-to-float math executed on the owned `fln-libm` plane.
/// `sqrt`, `ceil`, `floor` and `round` are IEEE-exact; the rest are the
/// deterministic owned transcendentals.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum UnaryMath {
    Sqrt,
    Ceil,
    Floor,
    Round,
    Sin,
    Cos,
    Tan,
    Asin,
    Acos,
    Atan,
    Sinh,
    Cosh,
    Tanh,
    Asinh,
    Acosh,
    Atanh,
    Exp,
    Exp2,
    Log,
    Log2,
    Log10,
    Cbrt,
}

impl UnaryMath {
    fn from_method(method: &str) -> Option<Self> {
        Some(match method {
            "sqrt" => Self::Sqrt,
            "ceil" => Self::Ceil,
            "floor" => Self::Floor,
            "round" => Self::Round,
            "sin" => Self::Sin,
            "cos" => Self::Cos,
            "tan" => Self::Tan,
            "asin" => Self::Asin,
            "acos" => Self::Acos,
            "atan" => Self::Atan,
            "sinh" => Self::Sinh,
            "cosh" => Self::Cosh,
            "tanh" => Self::Tanh,
            "asinh" => Self::Asinh,
            "acosh" => Self::Acosh,
            "atanh" => Self::Atanh,
            "exp" => Self::Exp,
            "exp2" => Self::Exp2,
            "log" => Self::Log,
            "log2" => Self::Log2,
            "log10" => Self::Log10,
            "cbrt" => Self::Cbrt,
            _ => return None,
        })
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
    ToString,
    ConvertWidth,
    ToInteger(Integer),
    FromInteger(Integer),
    Unary(UnaryMath),
    Pow,
    // The pin declares `Float.atan2 (y x : Float)`: the first argument is y.
    Atan2,
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
     $bits_result:path, $converted:ident, $nan_bits:ident, $unary:ident, $pow:ident,
     $atan2:ident) => {{
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
            Operation::ToString => string_result(value),
            Operation::ConvertWidth => $converted(value),
            Operation::Unary(op) => $result($unary(op, value)),
            Operation::Pow => $result($pow(value, $argument(&$args[1], 1)?)),
            // `value` is the pin's first argument, y; the second is x.
            Operation::Atan2 => $result($atan2(value, $argument(&$args[1], 1)?)),
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
            "toString" => Operation::ToString,
            "toFloat32" if width == Width::Binary64 => Operation::ConvertWidth,
            "toFloat" if width == Width::Binary32 => Operation::ConvertWidth,
            "pow" => Operation::Pow,
            "atan2" => Operation::Atan2,
            _ => match UnaryMath::from_method(method) {
                Some(op) => Operation::Unary(op),
                None => Operation::ToInteger(Integer::from_name(method.strip_prefix("to")?)?),
            },
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
                | Operation::Pow
                | Operation::Atan2
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
                    QUIET_NAN64_BITS,
                    unary_math64,
                    pow64,
                    atan2_64
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
                    QUIET_NAN32_BITS,
                    unary_math32,
                    pow32,
                    atan2_32
                )
            }
        }
    }

    pub(super) fn result_kind_matches(self, value: &Obj) -> bool {
        if self.operation == Operation::ToString {
            return super::value_kind(value) == super::ValueKind::String;
        }
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

fn unary_math64(op: UnaryMath, x: f64) -> f64 {
    match op {
        UnaryMath::Sqrt => fln_libm::sqrt(x),
        UnaryMath::Ceil => fln_libm::ceil(x),
        UnaryMath::Floor => fln_libm::floor(x),
        UnaryMath::Round => fln_libm::round(x),
        UnaryMath::Sin => fln_libm::sin(x),
        UnaryMath::Cos => fln_libm::cos(x),
        UnaryMath::Tan => fln_libm::tan(x),
        UnaryMath::Asin => fln_libm::asin(x),
        UnaryMath::Acos => fln_libm::acos(x),
        UnaryMath::Atan => fln_libm::atan(x),
        UnaryMath::Sinh => fln_libm::sinh(x),
        UnaryMath::Cosh => fln_libm::cosh(x),
        UnaryMath::Tanh => fln_libm::tanh(x),
        UnaryMath::Asinh => fln_libm::asinh(x),
        UnaryMath::Acosh => fln_libm::acosh(x),
        UnaryMath::Atanh => fln_libm::atanh(x),
        UnaryMath::Exp => fln_libm::exp(x),
        UnaryMath::Exp2 => fln_libm::exp2(x),
        UnaryMath::Log => fln_libm::log(x),
        UnaryMath::Log2 => fln_libm::log2(x),
        UnaryMath::Log10 => fln_libm::log10(x),
        UnaryMath::Cbrt => fln_libm::cbrt(x),
    }
}

fn unary_math32(op: UnaryMath, x: f32) -> f32 {
    match op {
        UnaryMath::Sqrt => fln_libm::f32::sqrt(x),
        UnaryMath::Ceil => fln_libm::f32::ceil(x),
        UnaryMath::Floor => fln_libm::f32::floor(x),
        UnaryMath::Round => fln_libm::f32::round(x),
        UnaryMath::Sin => fln_libm::f32::sin(x),
        UnaryMath::Cos => fln_libm::f32::cos(x),
        UnaryMath::Tan => fln_libm::f32::tan(x),
        UnaryMath::Asin => fln_libm::f32::asin(x),
        UnaryMath::Acos => fln_libm::f32::acos(x),
        UnaryMath::Atan => fln_libm::f32::atan(x),
        UnaryMath::Sinh => fln_libm::f32::sinh(x),
        UnaryMath::Cosh => fln_libm::f32::cosh(x),
        UnaryMath::Tanh => fln_libm::f32::tanh(x),
        UnaryMath::Asinh => fln_libm::f32::asinh(x),
        UnaryMath::Acosh => fln_libm::f32::acosh(x),
        UnaryMath::Atanh => fln_libm::f32::atanh(x),
        UnaryMath::Exp => fln_libm::f32::exp(x),
        UnaryMath::Exp2 => fln_libm::f32::exp2(x),
        UnaryMath::Log => fln_libm::f32::log(x),
        UnaryMath::Log2 => fln_libm::f32::log2(x),
        UnaryMath::Log10 => fln_libm::f32::log10(x),
        UnaryMath::Cbrt => fln_libm::f32::cbrt(x),
    }
}

fn pow64(x: f64, y: f64) -> f64 {
    fln_libm::pow(x, y)
}

fn pow32(x: f32, y: f32) -> f32 {
    fln_libm::f32::pow(x, y)
}

fn atan2_64(y: f64, x: f64) -> f64 {
    fln_libm::atan2(y, x)
}

fn atan2_32(y: f32, x: f32) -> f32 {
    fln_libm::f32::atan2(y, x)
}

fn boolean_result(value: bool) -> IntrinsicResult {
    IntrinsicResult::scalar(Obj::mk_nat(usize::from(value)))
}

fn string_result(value: impl Into<f64>) -> IntrinsicResult {
    // object.cpp uses std::to_string: fixed notation with six fractional
    // digits. Float32 is promoted to double before formatting. Every NaN
    // prints identically, while -0.0 retains its sign as "-0.000000".
    let value = value.into();
    let text = if value.is_nan() {
        "NaN".to_string()
    } else {
        format!("{value:.6}")
    };
    IntrinsicResult::owned(Obj::mk_string(&text))
}
