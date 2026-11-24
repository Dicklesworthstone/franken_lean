//! Native string operations whose Reference IR retains a bounds proof.
//!
//! The proof is a literal erased operand on direct calls and a real arity slot
//! on boxed closures. Neither form supplies proof authority: Golem still checks
//! access to the string buffer. Source borrowing and tagged results are taken
//! from the pinned declarations, separately from the generated C ABI ownership.

use super::{ErasedOperands, GeneratedExternRow, IrExecutionError, IrType, Name, inferred_arity};

pub(super) struct StringProofSignature {
    pub(super) result: &'static IrType,
    pub(super) borrowed: &'static [bool],
}

pub(super) fn signature(
    row: &GeneratedExternRow,
) -> Result<Option<StringProofSignature>, IrExecutionError> {
    let (name, symbol, module, kind, result, borrowed): (
        _,
        _,
        _,
        _,
        &'static IrType,
        &'static [bool],
    ) = match row.id {
        "extern:String.decodeChar" => (
            "String.decodeChar",
            "lean_string_utf8_get_fast",
            "Init.Data.String.Basic",
            "defn",
            &IrType::UInt32,
            &[true, true],
        ),
        "extern:String.Pos.Raw.get'" => (
            "String.Pos.Raw.get'",
            "lean_string_utf8_get_fast",
            "Init.Data.String.Basic",
            "defn",
            &IrType::UInt32,
            &[true, true],
        ),
        "extern:String.get'" => (
            "String.get'",
            "lean_string_utf8_get_fast",
            "Init.Data.String.Basic",
            "defn",
            &IrType::UInt32,
            &[true, true],
        ),
        "extern:String.Internal.getUTF8Byte" => (
            "String.Internal.getUTF8Byte",
            "lean_string_get_byte_fast",
            "Init.Data.String.Bootstrap",
            "opaque",
            &IrType::UInt8,
            &[true, false],
        ),
        "extern:String.getUTF8Byte" => (
            "String.getUTF8Byte",
            "lean_string_get_byte_fast",
            "Init.Data.String.PosRaw",
            "defn",
            &IrType::UInt8,
            &[true, false],
        ),
        "extern:String.getUtf8Byte" => (
            "String.getUtf8Byte",
            "lean_string_get_byte_fast",
            "Init.Data.String.PosRaw",
            "defn",
            &IrType::UInt8,
            &[false, false],
        ),
        // tagged_return is present on these two declarations, but not on
        // the deprecated String.next' alias sharing the same native symbol.
        "extern:String.Pos.Raw.next'" => (
            "String.Pos.Raw.next'",
            "lean_string_utf8_next_fast",
            "Init.Data.String.Basic",
            "defn",
            &IrType::Tagged,
            &[true, true],
        ),
        "extern:String.Pos.next" => (
            "String.Pos.next",
            "lean_string_utf8_next_fast",
            "Init.Data.String.Basic",
            "defn",
            &IrType::Tagged,
            &[true, true],
        ),
        "extern:String.next'" => (
            "String.next'",
            "lean_string_utf8_next_fast",
            "Init.Data.String.Basic",
            "defn",
            &IrType::TObject,
            &[true, true],
        ),
        _ => return Ok(None),
    };
    let ownership = if symbol == "lean_string_utf8_next_fast" {
        "abi((s: borrowed_arg, i: borrowed_arg) -> owned_res)"
    } else {
        "abi((s: borrowed_arg, i: borrowed_arg) -> value)"
    };
    if row.name != name
        || row.symbol != symbol
        || row.module != module
        || row.kind != kind
        || row.levels != 0
        || row.arity != 3
        || row.effect != "pure"
        || row.safety != "safe"
        || row.ownership != ownership
        || row.entry_class != "standard"
        || row.entry_scope != "all"
        || row.partition != "toolchain-api"
        || row.mode != "all"
        || row.profile != "faithful,sound"
        || inferred_arity(row)? != 2
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "string primitive differs from its reviewed erased proof bridge".to_owned(),
        });
    }
    Ok(Some(StringProofSignature { result, borrowed }))
}

pub(super) fn erased_operands(
    row: &GeneratedExternRow,
) -> Result<Option<ErasedOperands>, IrExecutionError> {
    Ok(signature(row)?.map(|_| ErasedOperands {
        runtime: 2,
        type_prefix: false,
        proof_suffix: 1,
    }))
}
