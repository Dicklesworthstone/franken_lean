//! Pin-specific direct-call bridges for array bounds proofs. These rows have
//! native bounds checks in Golem even when the Reference relies on the proof.
//! Only literal erased operands are discarded; the remaining data is still
//! validated against the generated ABI. Explicit extern telescopes retain
//! their ordinary native-signature validation.

use super::{ErasedOperands, GeneratedExternRow, IrExecutionError, Name, inferred_arity};

pub(super) fn erased_operands(
    row: &GeneratedExternRow,
) -> Result<Option<ErasedOperands>, IrExecutionError> {
    let (name, symbol, module, kind, runtime, ownership, safety, type_prefix) = match row.id {
        "extern:Array.getInternal" => (
            "Array.getInternal",
            "lean_array_fget",
            "Init.Prelude",
            "defn",
            2,
            "abi((a: borrowed_arg, i: borrowed_arg) -> owned_res)",
            "safe",
            true,
        ),
        "extern:Array.getInternalBorrowed" => (
            "Array.getInternalBorrowed",
            "lean_array_fget_borrowed",
            "Init.Prelude",
            "opaque",
            2,
            "abi((a: borrowed_arg, i: borrowed_arg) -> owned_res)",
            "unsafe",
            true,
        ),
        "extern:Array.set" => (
            "Array.set",
            "lean_array_fset",
            "Init.Data.Array.Set",
            "defn",
            3,
            "abi((a: owned_arg, i: borrowed_arg, v: owned_arg) -> raw_object)",
            "safe",
            true,
        ),
        "extern:Array.uget" => (
            "Array.uget",
            "lean_array_uget",
            "Init.Data.Array.Basic",
            "defn",
            2,
            "abi((a: borrowed_arg, i: value) -> raw_object)",
            "safe",
            true,
        ),
        "extern:Array.ugetBorrowed" => (
            "Array.ugetBorrowed",
            "lean_array_uget_borrowed",
            "Init.Data.Array.Basic",
            "opaque",
            2,
            "abi((a: borrowed_arg, i: value) -> borrowed_res)",
            "unsafe",
            true,
        ),
        "extern:Array.uset" => (
            "Array.uset",
            "lean_array_uset",
            "Init.Data.Array.Basic",
            "defn",
            3,
            "abi((a: owned_arg, i: value, v: owned_arg) -> raw_object)",
            "safe",
            true,
        ),
        "extern:ByteArray.get" => (
            "ByteArray.get",
            "lean_byte_array_fget",
            "Init.Data.ByteArray.Basic",
            "defn",
            2,
            "abi((a: borrowed_arg, i: borrowed_arg) -> value)",
            "safe",
            false,
        ),
        "extern:ByteArray.set" => (
            "ByteArray.set",
            "lean_byte_array_fset",
            "Init.Data.ByteArray.Basic",
            "defn",
            3,
            "abi((a: owned_arg, i: borrowed_arg, b: value) -> owned_res)",
            "safe",
            false,
        ),
        "extern:ByteArray.uget" => (
            "ByteArray.uget",
            "lean_byte_array_uget",
            "Init.Data.ByteArray.Basic",
            "defn",
            2,
            "abi((a: borrowed_arg, i: value) -> value)",
            "safe",
            false,
        ),
        "extern:ByteArray.uset" => (
            "ByteArray.uset",
            "lean_byte_array_uset",
            "Init.Data.ByteArray.Basic",
            "defn",
            3,
            "abi((a: owned_arg, i: value, v: value) -> raw_object)",
            "safe",
            false,
        ),
        _ => return Ok(None),
    };
    if row.name != name
        || row.symbol != symbol
        || row.module != module
        || row.kind != kind
        || row.levels != u32::from(type_prefix)
        || row.arity as usize != runtime + usize::from(type_prefix) + 1
        || row.effect != "pure"
        || row.safety != safety
        || row.ownership != ownership
        || row.entry_class != "standard"
        || row.entry_scope != "all"
        || row.partition != "toolchain-api"
        || inferred_arity(row)? != runtime
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "array primitive differs from its reviewed erased proof bridge".to_owned(),
        });
    }
    Ok(Some(ErasedOperands {
        runtime,
        type_prefix,
        proof_suffix: true,
    }))
}
