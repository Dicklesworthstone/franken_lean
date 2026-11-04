//! Exact pin-derived native telescopes for higher-order Nat and String code.
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
    let Some(review) = natural(row).or_else(|| string(row)) else {
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
