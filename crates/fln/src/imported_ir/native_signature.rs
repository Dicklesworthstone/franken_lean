//! Recover erased executable arities from the generated native ABI contract.
//!
//! The census arity counts source binders, including erased types. A module's
//! IR need not repeat declarations for imported native callees. In that case
//! only the generated ABI or an explicitly reviewed native bridge, never the
//! first observed call site, can supply the runtime arity. Explicit IR extern
//! declarations are checked against the same authority.

use super::{GeneratedExternRow, IrExecutionError, Name, Ownership, extern_row};
use fln_olean::ir::{IrParam, IrType};

/// The pinned IR retains sigma, alpha and the world around these exact five
/// cell operations. Their native ABI returns the raw value: the surrounding
/// user IR constructs EST.Out.ok itself. Never add an IO-result wrapper here.
pub(super) fn state_runtime_arity(
    row: &GeneratedExternRow,
) -> Result<Option<usize>, IrExecutionError> {
    let (name, symbol, runtime, ownership, safety) = match row.id {
        "extern:ST.Prim.mkRef" => (
            "ST.Prim.mkRef",
            "lean_st_mk_ref",
            1,
            "abi((owned_arg) -> owned_res)",
            "safe",
        ),
        "extern:ST.Prim.Ref.get" => (
            "ST.Prim.Ref.get",
            "lean_st_ref_get",
            1,
            "abi((borrowed_arg) -> owned_res)",
            "safe",
        ),
        "extern:ST.Prim.Ref.set" => (
            "ST.Prim.Ref.set",
            "lean_st_ref_set",
            2,
            "abi((borrowed_arg, owned_arg) -> owned_res)",
            "safe",
        ),
        "extern:ST.Prim.Ref.swap" => (
            "ST.Prim.Ref.swap",
            "lean_st_ref_swap",
            2,
            "abi((borrowed_arg, owned_arg) -> owned_res)",
            "safe",
        ),
        "extern:ST.Prim.Ref.take" => (
            "ST.Prim.Ref.take",
            "lean_st_ref_take",
            1,
            "rule(borrowed-args,owned-result)",
            "unsafe",
        ),
        _ => return Ok(None),
    };
    if row.name != name
        || row.symbol != symbol
        || row.module != "Init.System.ST"
        || row.kind != "opaque"
        || row.levels != 0
        || row.arity as usize != runtime + 2
        || row.effect != "state"
        || row.safety != safety
        || row.ownership != ownership
        || row.entry_class != "standard"
        || row.entry_scope != "all"
        || row.partition != "toolchain-api"
        || inferred_arity(row)? != runtime
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "state primitive differs from its reviewed erased IR bridge".to_owned(),
        });
    }
    Ok(Some(runtime))
}

/// Accept only the native operand form or the pin's explicitly reviewed
/// erased form. The returned arity is the signature after normalization,
/// independently of any call site's operand count.
pub(super) fn validated_ir_arity(
    row: &GeneratedExternRow,
    arity: usize,
) -> Result<usize, IrExecutionError> {
    let expected = ir_arity(row)?;
    if let Some(runtime) = state_runtime_arity(row)? {
        if arity == runtime || arity == runtime + 3 {
            return Ok(runtime);
        }
    } else if arity == expected {
        return Ok(expected);
    }
    Err(IrExecutionError::NativeContract {
        declaration: Name::from_components(row.name.split('.')),
        detail: "extern arity differs from the reviewed Reference IR signature".to_owned(),
    })
}

/// An explicit Reference extern cannot relabel the erased slots as data or
/// change borrowing/result representation. Native-form declarations retain
/// their existing ABI validation; only the newly admitted full telescope is
/// checked against this additional pin-derived shape.
pub(super) fn validate_extern_signature(
    row: &GeneratedExternRow,
    params: &[IrParam],
    result: &IrType,
) -> Result<(), IrExecutionError> {
    let Some(runtime) = state_runtime_arity(row)? else {
        return Ok(());
    };
    if params.len() != runtime + 3 {
        return Ok(());
    }
    let borrowed_ref = row.name != "ST.Prim.mkRef";
    let expected_result = if row.name == "ST.Prim.Ref.set" {
        IrType::Tagged
    } else {
        IrType::TObject
    };
    let valid = params.iter().enumerate().all(|(index, parameter)| {
        let (ty, borrow) = if index < 2 {
            (IrType::Erased, false)
        } else if index == params.len() - 1 {
            (IrType::Void, false)
        } else {
            (IrType::TObject, borrowed_ref && index == 2)
        };
        parameter.ty == ty && parameter.borrow == borrow
    });
    if !valid || result != &expected_result {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "state primitive extern differs from its reviewed erased telescope".to_owned(),
        });
    }
    Ok(())
}

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
