//! The pinned signed-word primitives use unsigned physical IR carriers.
//!
//! Int8 through ISize are erased single-field wrappers in SInt.Basic.
//! Their native operations retain signed semantics; reusing an unsigned
//! implementation merely because its IR carrier agrees would be incorrect.

use super::{GeneratedExternRow, IrType, PrimitiveSignature, Review};

pub(super) fn review(row: &GeneratedExternRow) -> Option<Review> {
    let (family, operation) = row.id.strip_prefix("extern:")?.split_once('.')?;
    // Keep source names, native symbols and carriers independent of input IR.
    // Int64.toInt has a distinct C symbol; only the two small toInt
    // conversions promise a tagged result.
    #[rustfmt::skip]
    macro_rules! family {
        ($family:literal, $c:literal, $ty:ident, $to_int:literal, $int_result:ident) => {{
            macro_rules! entry {
                ($op:literal, $symbol:literal, $parameters:expr, $result:ident, $ownership:literal) => {
                    Some(Review {
                        name: concat!($family, ".", $op),
                        symbol: concat!($c, "_", $symbol),
                        module: "Init.Data.SInt.Basic",
                        kind: "defn",
                        ownership: $ownership,
                        signature: PrimitiveSignature {
                            parameters: $parameters,
                            result: &IrType::$result,
                            exact_borrowed: None,
                        },
                    })
                };
            }
            match operation {
                "add" => entry!("add", "add", &[IrType::$ty, IrType::$ty], $ty,
                    "abi((a1: value, a2: value) -> value)"),
                "sub" => entry!("sub", "sub", &[IrType::$ty, IrType::$ty], $ty,
                    "abi((a1: value, a2: value) -> value)"),
                "mul" => entry!("mul", "mul", &[IrType::$ty, IrType::$ty], $ty,
                    "abi((a1: value, a2: value) -> value)"),
                "div" => entry!("div", "div", &[IrType::$ty, IrType::$ty], $ty,
                    "abi((a1: value, a2: value) -> value)"),
                "mod" => entry!("mod", "mod", &[IrType::$ty, IrType::$ty], $ty,
                    "abi((a1: value, a2: value) -> value)"),
                "land" => entry!("land", "land", &[IrType::$ty, IrType::$ty], $ty,
                    "abi((a1: value, a2: value) -> value)"),
                "lor" => entry!("lor", "lor", &[IrType::$ty, IrType::$ty], $ty,
                    "abi((a1: value, a2: value) -> value)"),
                "xor" => entry!("xor", "xor", &[IrType::$ty, IrType::$ty], $ty,
                    "abi((a1: value, a2: value) -> value)"),
                "shiftLeft" => entry!("shiftLeft", "shift_left", &[IrType::$ty, IrType::$ty], $ty,
                    "abi((a1: value, a2: value) -> value)"),
                "shiftRight" => entry!("shiftRight", "shift_right", &[IrType::$ty, IrType::$ty], $ty,
                    "abi((a1: value, a2: value) -> value)"),
                "complement" => entry!("complement", "complement", &[IrType::$ty], $ty,
                    "abi((a: value) -> value)"),
                "neg" => entry!("neg", "neg", &[IrType::$ty], $ty,
                    "abi((a: value) -> value)"),
                "abs" => entry!("abs", "abs", &[IrType::$ty], $ty,
                    "abi((a: value) -> value)"),
                "decEq" => entry!("decEq", "dec_eq", &[IrType::$ty, IrType::$ty], UInt8,
                    "abi((a1: value, a2: value) -> value)"),
                "decLe" => entry!("decLe", "dec_le", &[IrType::$ty, IrType::$ty], UInt8,
                    "abi((a1: value, a2: value) -> value)"),
                "decLt" => entry!("decLt", "dec_lt", &[IrType::$ty, IrType::$ty], UInt8,
                    "abi((a1: value, a2: value) -> value)"),
                "ofNat" => entry!("ofNat", "of_nat", &[IrType::TObject], $ty,
                    "abi((a: borrowed_arg) -> value)"),
                "ofInt" => entry!("ofInt", "of_int", &[IrType::TObject], $ty,
                    "abi((a: borrowed_arg) -> value)"),
                "toInt" => entry!("toInt", $to_int, &[IrType::$ty], $int_result,
                    "abi((a: value) -> owned_res)"),
                "toInt8" if family != "Int8" => entry!("toInt8", "to_int8", &[IrType::$ty], UInt8,
                    "abi((a: value) -> value)"),
                "toInt16" if family != "Int16" => entry!("toInt16", "to_int16", &[IrType::$ty], UInt16,
                    "abi((a: value) -> value)"),
                "toInt32" if family != "Int32" => entry!("toInt32", "to_int32", &[IrType::$ty], UInt32,
                    "abi((a: value) -> value)"),
                "toInt64" if family != "Int64" => entry!("toInt64", "to_int64", &[IrType::$ty], UInt64,
                    "abi((a: value) -> value)"),
                "toISize" if family != "ISize" => entry!("toISize", "to_isize", &[IrType::$ty], USize,
                    "abi((a: value) -> value)"),
                _ => None,
            }
        }};
    }
    match family {
        "Int8" => family!("Int8", "lean_int8", UInt8, "to_int", Tagged),
        "Int16" => family!("Int16", "lean_int16", UInt16, "to_int", Tagged),
        "Int32" => family!("Int32", "lean_int32", UInt32, "to_int", TObject),
        "Int64" => family!("Int64", "lean_int64", UInt64, "to_int_sint", TObject),
        "ISize" => family!("ISize", "lean_isize", USize, "to_int", TObject),
        _ => None,
    }
}
