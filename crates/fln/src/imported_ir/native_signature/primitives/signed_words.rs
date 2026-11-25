//! Signed machine integers use the pin's unsigned IR storage types. Their
//! native operations still interpret those bits as two's-complement values.
//! In particular Int8/Int16.toInt have tagged results, Int64.toInt has a
//! distinct native symbol, and widening conversions must retain sign extension.
//!
//! These signatures come from Init.Data.SInt.{Basic,Float,Float32}; the parent
//! authenticates each against the complete generated extern contract before
//! either a direct call or a compiler-generated boxed wrapper can use it.

use super::{GeneratedExternRow, IrType, PrimitiveSignature, Review};

pub(super) fn review(row: &GeneratedExternRow) -> Option<Review> {
    let (family, operation) = row.id.strip_prefix("extern:")?.split_once('.')?;
    // Identity casts are inline source definitions, not generated externs.
    if operation.strip_prefix("to") == Some(family) {
        return None;
    }
    macro_rules! family {
        ($family:literal, $c:literal, $ty:ident, $int_result:ident, $to_int:literal) => {{
            macro_rules! review {
                ($operation:literal, $symbol:literal, $parameters:expr, $result:expr, $ownership:literal, $module:literal) => {
                    Some(Review {
                        name: concat!($family, ".", $operation),
                        symbol: concat!($c, "_", $symbol),
                        module: $module,
                        kind: if matches!(operation, "toFloat" | "toFloat32") {
                            "opaque"
                        } else {
                            "defn"
                        },
                        ownership: $ownership,
                        signature: PrimitiveSignature {
                            parameters: $parameters,
                            result: $result,
                            exact_borrowed: None,
                        },
                    })
                };
            }
            macro_rules! binary {
                ($operation:literal, $symbol:literal, $result:ident) => {
                    review!(
                        $operation,
                        $symbol,
                        &[IrType::$ty, IrType::$ty],
                        &IrType::$result,
                        "abi((a1: value, a2: value) -> value)",
                        "Init.Data.SInt.Basic"
                    )
                };
            }
            macro_rules! unary {
                ($operation:literal, $symbol:literal, $result:ident) => {
                    review!(
                        $operation,
                        $symbol,
                        &[IrType::$ty],
                        &IrType::$result,
                        "abi((a: value) -> value)",
                        "Init.Data.SInt.Basic"
                    )
                };
            }
            match operation {
                "add" => binary!("add", "add", $ty),
                "sub" => binary!("sub", "sub", $ty),
                "mul" => binary!("mul", "mul", $ty),
                "div" => binary!("div", "div", $ty),
                "mod" => binary!("mod", "mod", $ty),
                "land" => binary!("land", "land", $ty),
                "lor" => binary!("lor", "lor", $ty),
                "xor" => binary!("xor", "xor", $ty),
                "shiftLeft" => binary!("shiftLeft", "shift_left", $ty),
                "shiftRight" => binary!("shiftRight", "shift_right", $ty),
                "complement" => unary!("complement", "complement", $ty),
                "neg" => unary!("neg", "neg", $ty),
                "abs" => unary!("abs", "abs", $ty),
                "decEq" => binary!("decEq", "dec_eq", UInt8),
                "decLe" => binary!("decLe", "dec_le", UInt8),
                "decLt" => binary!("decLt", "dec_lt", UInt8),
                "ofNat" => review!(
                    "ofNat",
                    "of_nat",
                    &[IrType::TObject],
                    &IrType::$ty,
                    "abi((a: borrowed_arg) -> value)",
                    "Init.Data.SInt.Basic"
                ),
                "ofInt" => review!(
                    "ofInt",
                    "of_int",
                    &[IrType::TObject],
                    &IrType::$ty,
                    "abi((a: borrowed_arg) -> value)",
                    "Init.Data.SInt.Basic"
                ),
                "toInt" => review!(
                    "toInt",
                    $to_int,
                    &[IrType::$ty],
                    &IrType::$int_result,
                    "abi((a: value) -> owned_res)",
                    "Init.Data.SInt.Basic"
                ),
                "toInt8" => unary!("toInt8", "to_int8", UInt8),
                "toInt16" => unary!("toInt16", "to_int16", UInt16),
                "toInt32" => unary!("toInt32", "to_int32", UInt32),
                "toInt64" => unary!("toInt64", "to_int64", UInt64),
                "toISize" => unary!("toISize", "to_isize", USize),
                "toFloat" => review!(
                    "toFloat",
                    "to_float",
                    &[IrType::$ty],
                    &IrType::Float,
                    "abi((a: value) -> value)",
                    "Init.Data.SInt.Float"
                ),
                "toFloat32" => review!(
                    "toFloat32",
                    "to_float32",
                    &[IrType::$ty],
                    &IrType::Float32,
                    "abi((a: value) -> value)",
                    "Init.Data.SInt.Float32"
                ),
                _ => None,
            }
        }};
    }
    match family {
        "Int8" => family!("Int8", "lean_int8", UInt8, Tagged, "to_int"),
        "Int16" => family!("Int16", "lean_int16", UInt16, Tagged, "to_int"),
        "Int32" => family!("Int32", "lean_int32", UInt32, TObject, "to_int"),
        "Int64" => family!("Int64", "lean_int64", UInt64, TObject, "to_int_sint"),
        "ISize" => family!("ISize", "lean_isize", USize, TObject, "to_int"),
        _ => None,
    }
}
