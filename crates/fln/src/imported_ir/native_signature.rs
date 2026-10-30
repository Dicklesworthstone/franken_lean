//! Recover erased executable arities from the generated native ABI contract.
//!
//! The census arity counts source binders, including erased types. A module's
//! IR need not repeat declarations for imported native callees. In that case
//! only the generated ABI or an explicitly reviewed native bridge, never the
//! first observed call site, can supply the runtime arity. Explicit IR extern
//! declarations are checked against the same authority.

use super::{GeneratedExternRow, IrExecutionError, Name, Ownership, extern_row};

pub(super) fn inferred_arity(row: &GeneratedExternRow) -> Result<usize, IrExecutionError> {
    let error = |error: extern_row::ContractError| IrExecutionError::NativeContract {
        declaration: Name::from_components(row.name.split('.')),
        detail: error.to_string(),
    };
    let ownership = Ownership::parse(row.ownership).map_err(error)?;
    let fallback = reviewed_rule_arity(row, &ownership).map_err(error)?;
    executable_arity(&ownership, fallback).map_err(error)
}

/// Reference IR keeps the erased RealWorld argument at a BaseIO call site;
/// Golem's native stream getter receives no runtime operand. Bind the single
/// supported difference to the complete reviewed row, never to input IR.
pub(super) fn ir_arity(row: &GeneratedExternRow) -> Result<usize, IrExecutionError> {
    if row.id != "extern:IO.getStdout" {
        return inferred_arity(row);
    }
    if row.name != "IO.getStdout"
        || row.module != "Init.System.IO"
        || row.kind != "opaque"
        || row.symbol != "lean_get_stdout"
        || row.levels != 0
        || row.arity != 0
        || row.effect != "io"
        || row.safety != "safe"
        || row.ownership != "rule(borrowed-args,owned-result)"
        || inferred_arity(row)? != 0
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "IO.getStdout differs from its reviewed erased-world bridge".to_owned(),
        });
    }
    Ok(1)
}

fn reviewed_rule_arity(
    row: &GeneratedExternRow,
    ownership: &Ownership,
) -> Result<usize, extern_row::ContractError> {
    if row.id != "extern:ST.Prim.Ref.take" {
        return Ok(row.arity as usize);
    }
    // Unlike get/set/swap, take is absent from the pin's lean.h declarations,
    // so its generated ownership row is rule-only. The pinned ST declaration
    // binds erased sigma/alpha before one borrowed reference. Golem's RefTake
    // implementation checks that one handle and returns its owned occupant.
    // This is a row-specific runtime bridge, not a general rule that erases
    // binders by count or accepts an arity supplied by untrusted IR.
    if row.name != "ST.Prim.Ref.take"
        || row.module != "Init.System.ST"
        || row.kind != "opaque"
        || row.symbol != "lean_st_ref_take"
        || row.levels != 0
        || row.arity != 3
        || row.effect != "state"
        || row.safety != "unsafe"
        || !matches!(ownership, Ownership::DefaultRuleOwnedResult)
    {
        return Err(extern_row::ContractError::new(
            "ST.Prim.Ref.take differs from its reviewed erased runtime contract",
        ));
    }
    Ok(1)
}

fn executable_arity(
    ownership: &Ownership,
    source_arity: usize,
) -> Result<usize, extern_row::ContractError> {
    let arity = match ownership {
        Ownership::AbiSignature(signature) => {
            let parameters = signature
                .split_once(" -> ")
                .and_then(|(parameters, _)| parameters.strip_prefix('('))
                .and_then(|parameters| parameters.strip_suffix(')'))
                .ok_or_else(|| {
                    extern_row::ContractError::new("malformed generated ABI parameter list")
                })?;
            if parameters.is_empty() || parameters == "()" {
                0
            } else {
                parameters.split(", ").count()
            }
        }
        // Except for an explicitly reviewed bridge above, a rule-only row
        // has no erased telescope. Preserve its census-arity requirement.
        _ => source_arity,
    };
    // Counting separators does not authorize an ABI. The existing canonical
    // ownership parser must still accept every parameter and the result,
    // including its refusal of raw pointers and unsupported ownership rules.
    ownership.argument_ownership(arity)?;
    ownership.result_ownership()?;
    Ok(arity)
}

#[cfg(test)]
mod tests;
