//! Exact pin-derived native telescopes for higher-order primitive code.
//! The generated census remains the ABI authority. These reviewed signatures
//! supply the compiler's IR representations; input declarations cannot supply
//! their own arity, ownership, scalar boxing, or implementation.

use super::{GeneratedExternRow, IrExecutionError, IrType, Name, inferred_arity};

#[derive(Clone, Copy)]
pub(super) struct PrimitiveSignature {
    pub(super) parameters: &'static [IrType],
    pub(super) result: &'static IrType,
}

struct Review {
    name: &'static str,
    symbol: &'static str,
    module: &'static str,
    kind: &'static str,
    ownership: &'static str,
    signature: PrimitiveSignature,
}

pub(super) fn signature(
    row: &GeneratedExternRow,
) -> Result<Option<PrimitiveSignature>, IrExecutionError> {
    let Some(review) = natural(row)
        .or_else(|| integer(row))
        .or_else(|| string(row))
        .or_else(|| word(row))
        .or_else(|| floating(row))
    else {
        return Ok(None);
    };
    if row.name != review.name
        || row.symbol != review.symbol
        || row.module != review.module
        || row.kind != review.kind
        || row.ownership != review.ownership
        || row.levels != 0
        || row.arity as usize != review.signature.parameters.len()
        || row.effect != "pure"
        || row.safety != "safe"
        || row.entry_class != "standard"
        || row.entry_scope != "all"
        || row.partition != "toolchain-api"
        || row.mode != "all"
        || row.profile != "faithful,sound"
        || inferred_arity(row)? != review.signature.parameters.len()
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "primitive differs from its reviewed native IR signature".to_owned(),
        });
    }
    Ok(Some(review.signature))
}

/// The pin boxes Float/Float32 closures as constructor objects, including
/// Float32 even though its bit-conversion partner UInt32 boxes as TObject.
/// Keep the bit boundary explicit: ofBits/toBits retain the native public
/// NaN normalization contract rather than acting as unchecked casts.
fn floating(row: &GeneratedExternRow) -> Option<Review> {
    let (family, operation) = row.id.strip_prefix("extern:")?.split_once('.')?;
    // The pinned formatter repeatedly indents nested macro matchers.
    #[rustfmt::skip]
    macro_rules! family {
        ($family:literal, $c:literal, $float:ident, $word:ident) => {{
            macro_rules! review {
                (
                    $operation:literal,
                    $symbol:literal,
                    $parameters:expr,
                    $result:expr,
                    $ownership:literal
                ) => {
                    Some(Review {
                        name: concat!($family, ".", $operation),
                        symbol: concat!($c, "_", $symbol),
                        module: concat!("Init.Data.", $family),
                        kind: "opaque",
                        ownership: $ownership,
                        signature: PrimitiveSignature {
                            parameters: $parameters,
                            result: $result,
                        },
                    })
                };
            }
            match operation {
                "add" => review!(
                    "add",
                    "add",
                    &[IrType::$float, IrType::$float],
                    &IrType::$float,
                    "abi((a: value, b: value) -> value)"
                ),
                "sub" => review!(
                    "sub",
                    "sub",
                    &[IrType::$float, IrType::$float],
                    &IrType::$float,
                    "abi((a: value, b: value) -> value)"
                ),
                "mul" => review!(
                    "mul",
                    "mul",
                    &[IrType::$float, IrType::$float],
                    &IrType::$float,
                    "abi((a: value, b: value) -> value)"
                ),
                "div" => review!(
                    "div",
                    "div",
                    &[IrType::$float, IrType::$float],
                    &IrType::$float,
                    "abi((a: value, b: value) -> value)"
                ),
                "neg" => review!(
                    "neg",
                    "negate",
                    &[IrType::$float],
                    &IrType::$float,
                    "abi((a: value) -> value)"
                ),
                "beq" => review!(
                    "beq",
                    "beq",
                    &[IrType::$float, IrType::$float],
                    &IrType::UInt8,
                    "abi((a: value, b: value) -> value)"
                ),
                "decLe" => review!(
                    "decLe",
                    "decLe",
                    &[IrType::$float, IrType::$float],
                    &IrType::UInt8,
                    "abi((a: value, b: value) -> value)"
                ),
                "decLt" => review!(
                    "decLt",
                    "decLt",
                    &[IrType::$float, IrType::$float],
                    &IrType::UInt8,
                    "abi((a: value, b: value) -> value)"
                ),
                "ofBits" => review!(
                    "ofBits",
                    "of_bits",
                    &[IrType::$word],
                    &IrType::$float,
                    "abi((u: value) -> value)"
                ),
                "toBits" => review!(
                    "toBits",
                    "to_bits",
                    &[IrType::$float],
                    &IrType::$word,
                    "abi((d: value) -> value)"
                ),
                _ => None,
            }
        }};
    }
    match family {
        "Float" => family!("Float", "lean_float", Float, UInt64),
        "Float32" => family!("Float32", "lean_float32", Float32, UInt32),
        _ => None,
    }
}

fn natural(row: &GeneratedExternRow) -> Option<Review> {
    let (name, symbol, comparison, unary) = match row.id {
        "extern:Nat.add" => ("Nat.add", "lean_nat_add", false, false),
        "extern:Nat.sub" => ("Nat.sub", "lean_nat_sub", false, false),
        "extern:Nat.mul" => ("Nat.mul", "lean_nat_mul", false, false),
        "extern:Nat.div" => ("Nat.div", "lean_nat_div", false, false),
        "extern:Nat.mod" => ("Nat.mod", "lean_nat_mod", false, false),
        "extern:Nat.pow" => ("Nat.pow", "lean_nat_pow", false, false),
        "extern:Nat.pred" => ("Nat.pred", "lean_nat_pred", false, true),
        "extern:Nat.beq" => ("Nat.beq", "lean_nat_dec_eq", true, false),
        "extern:Nat.ble" => ("Nat.ble", "lean_nat_dec_le", true, false),
        "extern:Nat.decEq" => ("Nat.decEq", "lean_nat_dec_eq", true, false),
        "extern:Nat.decLe" => ("Nat.decLe", "lean_nat_dec_le", true, false),
        "extern:Nat.decLt" => ("Nat.decLt", "lean_nat_dec_lt", true, false),
        _ => return None,
    };
    Some(Review {
        name,
        symbol,
        module: "Init.Prelude",
        kind: "defn",
        ownership: if unary {
            "abi((n: borrowed_arg) -> owned_res)"
        } else if comparison {
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> value)"
        } else {
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> owned_res)"
        },
        signature: PrimitiveSignature {
            parameters: if unary {
                &[IrType::TObject]
            } else {
                &[IrType::TObject, IrType::TObject]
            },
            result: if comparison {
                &IrType::UInt8
            } else {
                &IrType::TObject
            },
        },
    })
}

fn integer(row: &GeneratedExternRow) -> Option<Review> {
    let (name, symbol, module, kind, ownership, parameters, result): (
        _,
        _,
        _,
        _,
        _,
        &'static [IrType],
        &'static IrType,
    ) = match row.id {
        "extern:Int.add" => (
            "Int.add",
            "lean_int_add",
            "Init.Data.Int.Basic",
            "defn",
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> owned_res)",
            &[IrType::TObject, IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.sub" => (
            "Int.sub",
            "lean_int_sub",
            "Init.Data.Int.Basic",
            "defn",
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> owned_res)",
            &[IrType::TObject, IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.mul" => (
            "Int.mul",
            "lean_int_mul",
            "Init.Data.Int.Basic",
            "defn",
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> owned_res)",
            &[IrType::TObject, IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.ediv" => (
            "Int.ediv",
            "lean_int_ediv",
            "Init.Data.Int.DivMod.Basic",
            "defn",
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> owned_res)",
            &[IrType::TObject, IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.emod" => (
            "Int.emod",
            "lean_int_emod",
            "Init.Data.Int.DivMod.Basic",
            "defn",
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> owned_res)",
            &[IrType::TObject, IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.tdiv" => (
            "Int.tdiv",
            "lean_int_div",
            "Init.Data.Int.DivMod.Basic",
            "defn",
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> owned_res)",
            &[IrType::TObject, IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.tmod" => (
            "Int.tmod",
            "lean_int_mod",
            "Init.Data.Int.DivMod.Basic",
            "defn",
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> owned_res)",
            &[IrType::TObject, IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.neg" => (
            "Int.neg",
            "lean_int_neg",
            "Init.Data.Int.Basic",
            "defn",
            "abi((a: borrowed_arg) -> owned_res)",
            &[IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.natAbs" => (
            "Int.natAbs",
            "lean_nat_abs",
            "Init.Data.Int.Basic",
            "defn",
            "abi((i: borrowed_arg) -> owned_res)",
            &[IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.ofNat" => (
            "Int.ofNat",
            "lean_nat_to_int",
            "Init.Data.Int.Basic",
            "ctor",
            "abi((a: owned_arg) -> owned_res)",
            &[IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.negSucc" => (
            "Int.negSucc",
            "lean_int_neg_succ_of_nat",
            "Init.Data.Int.Basic",
            "ctor",
            "abi((a: owned_arg) -> owned_res)",
            &[IrType::TObject],
            &IrType::TObject,
        ),
        "extern:Int.decEq" => (
            "Int.decEq",
            "lean_int_dec_eq",
            "Init.Data.Int.Basic",
            "defn",
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> value)",
            &[IrType::TObject, IrType::TObject],
            &IrType::UInt8,
        ),
        "extern:Int.decLe" => (
            "Int.decLe",
            "lean_int_dec_le",
            "Init.Data.Int.Basic",
            "defn",
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> value)",
            &[IrType::TObject, IrType::TObject],
            &IrType::UInt8,
        ),
        "extern:Int.decLt" => (
            "Int.decLt",
            "lean_int_dec_lt",
            "Init.Data.Int.Basic",
            "defn",
            "abi((a1: borrowed_arg, a2: borrowed_arg) -> value)",
            &[IrType::TObject, IrType::TObject],
            &IrType::UInt8,
        ),
        "extern:Int.decNonneg" => (
            "Int.decNonneg",
            "lean_int_dec_nonneg",
            "Init.Data.Int.Basic",
            "defn",
            "abi((a: borrowed_arg) -> value)",
            &[IrType::TObject],
            &IrType::UInt8,
        ),
        // divExact has an erased proof in its compiler telescope. Its native
        // closure requires a separate proof-slot bridge; never guess it from
        // the two-argument C ABI.
        _ => return None,
    };
    Some(Review {
        name,
        symbol,
        module,
        kind,
        ownership,
        signature: PrimitiveSignature { parameters, result },
    })
}

fn string(row: &GeneratedExternRow) -> Option<Review> {
    let (name, symbol, module, kind, ownership, parameters, result): (
        _,
        _,
        _,
        _,
        _,
        &'static [IrType],
        &'static IrType,
    ) = match row.id {
        "extern:String.append" => (
            "String.append",
            "lean_string_append",
            "Init.Data.String.Defs",
            "defn",
            "abi((s1: owned_arg, s2: borrowed_arg) -> owned_res)",
            &[IrType::Object, IrType::Object],
            &IrType::Object,
        ),
        "extern:String.push" => (
            "String.push",
            "lean_string_push",
            "Init.Data.String.Bootstrap",
            "defn",
            "abi((s: owned_arg, c: value) -> owned_res)",
            &[IrType::Object, IrType::UInt32],
            &IrType::Object,
        ),
        "extern:String.length" => (
            "String.length",
            "lean_string_length",
            "Init.Data.String.Length",
            "defn",
            "abi((s: borrowed_arg) -> owned_res)",
            &[IrType::Object],
            &IrType::Tagged,
        ),
        "extern:String.utf8ByteSize" => (
            "String.utf8ByteSize",
            "lean_string_utf8_byte_size",
            "Init.Prelude",
            "defn",
            "abi((s: borrowed_arg) -> owned_res)",
            &[IrType::Object],
            &IrType::Tagged,
        ),
        "extern:String.decEq" => (
            "String.decEq",
            "lean_string_dec_eq",
            "Init.Prelude",
            "defn",
            "abi((s1: borrowed_arg, s2: borrowed_arg) -> value)",
            &[IrType::Object, IrType::Object],
            &IrType::UInt8,
        ),
        "extern:String.hash" => (
            "String.hash",
            "lean_string_hash",
            "Init.Prelude",
            "opaque",
            "abi((borrowed_arg) -> value)",
            &[IrType::Object],
            &IrType::UInt64,
        ),
        _ => return None,
    };
    Some(Review {
        name,
        symbol,
        module,
        kind,
        ownership,
        signature: PrimitiveSignature { parameters, result },
    })
}

/// Machine integers already have native scalar operations. Their higher-order
/// entry points retain the exact compiler boxing convention rather than
/// interpreting the Reference's generated `_boxed` bodies. The source anchors
/// are Init.Prelude and Init.Data.UInt.{BasicAux,Basic,Log2}; in particular,
/// `tagged_return` distinguishes the small-word conversions to Nat.
fn word(row: &GeneratedExternRow) -> Option<Review> {
    let (family, operation) = row.id.strip_prefix("extern:")?.split_once('.')?;
    #[rustfmt::skip]
    macro_rules! family {
        ($family:literal, $c:literal, $ty:ident, $add_sub:literal, $order:literal,
         $from_nat:literal, $to_nat:literal, $nat_result:ident, $nat_ownership:literal) => {{
            macro_rules! review {
                (
                    $operation:literal,
                    $symbol:literal,
                    $module:expr,
                    $parameters:expr,
                    $result:expr,
                    $ownership:expr
                ) => {
                    Some(Review {
                        name: concat!($family, ".", $operation),
                        symbol: concat!($c, "_", $symbol),
                        module: $module,
                        kind: "defn",
                        ownership: $ownership,
                        signature: PrimitiveSignature {
                            parameters: $parameters,
                            result: $result,
                        },
                    })
                };
            }
            match operation {
                "add" => review!(
                    "add",
                    "add",
                    $add_sub,
                    &[IrType::$ty, IrType::$ty],
                    &IrType::$ty,
                    "abi((a1: value, a2: value) -> value)"
                ),
                "sub" => review!(
                    "sub",
                    "sub",
                    $add_sub,
                    &[IrType::$ty, IrType::$ty],
                    &IrType::$ty,
                    "abi((a1: value, a2: value) -> value)"
                ),
                "mul" => review!(
                    "mul",
                    "mul",
                    "Init.Data.UInt.Basic",
                    &[IrType::$ty, IrType::$ty],
                    &IrType::$ty,
                    "abi((a1: value, a2: value) -> value)"
                ),
                "div" => review!(
                    "div",
                    "div",
                    "Init.Data.UInt.Basic",
                    &[IrType::$ty, IrType::$ty],
                    &IrType::$ty,
                    "abi((a1: value, a2: value) -> value)"
                ),
                "mod" => review!(
                    "mod",
                    "mod",
                    "Init.Data.UInt.Basic",
                    &[IrType::$ty, IrType::$ty],
                    &IrType::$ty,
                    "abi((a1: value, a2: value) -> value)"
                ),
                "land" => review!(
                    "land",
                    "land",
                    "Init.Data.UInt.Basic",
                    &[IrType::$ty, IrType::$ty],
                    &IrType::$ty,
                    "abi((a: value, b: value) -> value)"
                ),
                "lor" => review!(
                    "lor",
                    "lor",
                    "Init.Data.UInt.Basic",
                    &[IrType::$ty, IrType::$ty],
                    &IrType::$ty,
                    "abi((a: value, b: value) -> value)"
                ),
                "xor" => review!(
                    "xor",
                    "xor",
                    "Init.Data.UInt.Basic",
                    &[IrType::$ty, IrType::$ty],
                    &IrType::$ty,
                    "abi((a: value, b: value) -> value)"
                ),
                "shiftLeft" => review!(
                    "shiftLeft",
                    "shift_left",
                    "Init.Data.UInt.Basic",
                    &[IrType::$ty, IrType::$ty],
                    &IrType::$ty,
                    "abi((a: value, b: value) -> value)"
                ),
                "shiftRight" => review!(
                    "shiftRight",
                    "shift_right",
                    "Init.Data.UInt.Basic",
                    &[IrType::$ty, IrType::$ty],
                    &IrType::$ty,
                    "abi((a: value, b: value) -> value)"
                ),
                "complement" => review!(
                    "complement",
                    "complement",
                    "Init.Data.UInt.Basic",
                    &[IrType::$ty],
                    &IrType::$ty,
                    "abi((a: value) -> value)"
                ),
                "neg" => review!(
                    "neg",
                    "neg",
                    "Init.Data.UInt.Basic",
                    &[IrType::$ty],
                    &IrType::$ty,
                    "abi((a: value) -> value)"
                ),
                "log2" => review!(
                    "log2",
                    "log2",
                    "Init.Data.UInt.Log2",
                    &[IrType::$ty],
                    &IrType::$ty,
                    "abi((a: value) -> value)"
                ),
                "decEq" => review!(
                    "decEq",
                    "dec_eq",
                    "Init.Prelude",
                    &[IrType::$ty, IrType::$ty],
                    &IrType::UInt8,
                    "abi((a1: value, a2: value) -> value)"
                ),
                "decLe" => review!(
                    "decLe",
                    "dec_le",
                    $order,
                    &[IrType::$ty, IrType::$ty],
                    &IrType::UInt8,
                    "abi((a1: value, a2: value) -> value)"
                ),
                "decLt" => review!(
                    "decLt",
                    "dec_lt",
                    $order,
                    &[IrType::$ty, IrType::$ty],
                    &IrType::UInt8,
                    "abi((a1: value, a2: value) -> value)"
                ),
                "ofNat" => review!(
                    "ofNat",
                    "of_nat",
                    $from_nat,
                    &[IrType::TObject],
                    &IrType::$ty,
                    "abi((a: borrowed_arg) -> value)"
                ),
                "toNat" => review!(
                    "toNat",
                    "to_nat",
                    $to_nat,
                    &[IrType::$ty],
                    &IrType::$nat_result,
                    $nat_ownership
                ),
                _ => None,
            }
        }};
    }
    match family {
        "UInt8" => family!(
            "UInt8",
            "lean_uint8",
            UInt8,
            "Init.Data.UInt.Basic",
            "Init.Prelude",
            "Init.Prelude",
            "Init.Data.UInt.BasicAux",
            Tagged,
            "abi((a: value) -> owned_res)"
        ),
        "UInt16" => family!(
            "UInt16",
            "lean_uint16",
            UInt16,
            "Init.Data.UInt.Basic",
            "Init.Data.UInt.Basic",
            "Init.Data.UInt.BasicAux",
            "Init.Data.UInt.BasicAux",
            Tagged,
            "abi((a: value) -> owned_res)"
        ),
        "UInt32" => family!(
            "UInt32",
            "lean_uint32",
            UInt32,
            "Init.Data.UInt.BasicAux",
            "Init.Prelude",
            "Init.Data.UInt.BasicAux",
            "Init.Prelude",
            TObject,
            "abi((a: value) -> owned_res)"
        ),
        "UInt64" => family!(
            "UInt64",
            "lean_uint64",
            UInt64,
            "Init.Data.UInt.Basic",
            "Init.Data.UInt.Basic",
            "Init.Data.UInt.BasicAux",
            "Init.Data.UInt.BasicAux",
            TObject,
            "abi((n: value) -> owned_res)"
        ),
        "USize" => family!(
            "USize",
            "lean_usize",
            USize,
            "Init.Data.UInt.BasicAux",
            "Init.Data.UInt.BasicAux",
            "Init.Data.UInt.BasicAux",
            "Init.Data.UInt.BasicAux",
            TObject,
            "abi((n: value) -> owned_res)"
        ),
        _ => None,
    }
}
