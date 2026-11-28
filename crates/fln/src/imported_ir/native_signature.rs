//! Recover erased executable arities from the generated native ABI contract.
//!
//! The census arity counts source binders, including erased types. A module's
//! IR need not repeat declarations for imported native callees. In that case
//! only the generated ABI or an explicitly reviewed native bridge, never the
//! first observed call site, can supply the runtime arity. Explicit IR extern
//! declarations are checked against the same authority.

use super::{
    GeneratedExternRow, IrExecutionError, IrExecutionLimits, Name, Native, Ownership, extern_row,
    unsupported,
};
use fln_olean::ir::{IrAlt, IrArg, IrDecl, IrExpr, IrModule, IrParam, IrStmt, IrTerminal, IrType};
use std::collections::BTreeMap;

mod array_proofs;
mod base_io_tasks;
mod boxed;
mod primitives;
mod string_proofs;
mod tasks;

pub(super) use boxed::{BoxedNative, boxed_row};

#[derive(Clone, Copy)]
struct ErasedOperands {
    runtime: usize,
    type_prefix: usize,
    proof_suffix: usize,
}

/// The pin retains literal erased types and bounds proofs on reviewed direct
/// calls. Remove those slots only for the exact generated rows, before
/// validating all remaining operands. Never infer a signature from a call.
pub(super) fn erase_type_arguments(
    module: &mut IrModule,
    natives: &BTreeMap<Name, Native>,
    limits: IrExecutionLimits,
) -> Result<(), IrExecutionError> {
    let mut bridges = BTreeMap::new();
    for (name, native) in natives {
        // A boxed wrapper keeps the complete source telescope in its
        // closure ABI. Only its native forwarding body discards these slots.
        if native.boxed.is_some() {
            continue;
        }
        let Some(row) = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.id == native.id)
        else {
            continue;
        };
        let bridge = if let Some(runtime) = erased_type_runtime_arity(row)? {
            Some(ErasedOperands {
                runtime,
                type_prefix: 1,
                proof_suffix: 0,
            })
        } else if let Some(signature) = tasks::signature(row)? {
            Some(ErasedOperands {
                runtime: signature.parameters.len(),
                type_prefix: signature.erased_prefix,
                proof_suffix: 0,
            })
        } else if let Some(signature) = base_io_tasks::signature(row)? {
            Some(ErasedOperands {
                runtime: signature.parameters.len(),
                type_prefix: signature.erased_prefix,
                // The final world is independently inert; waitAny also
                // retains its nonempty-list proof immediately before it.
                proof_suffix: signature.erased_proofs + 1,
            })
        } else {
            array_proofs::erased_operands(row)?
                .or(string_proofs::erased_operands(row)?)
                .or(natural_division_operands(row)?)
        };
        if let Some(bridge) = bridge {
            bridges.insert(
                name.clone(),
                (bridge, native.reference_base_io_task_telescope),
            );
        }
    }
    if bridges.is_empty() {
        return Ok(());
    }
    let mut work = 0u64;
    for declaration in &mut module.decls {
        let IrDecl::Function { name, body, .. } = declaration else {
            continue;
        };
        let mut pending = vec![(body, 1usize)];
        while let Some((body, depth)) = pending.pop() {
            if depth > limits.ir.max_depth.min(128) {
                return Err(IrExecutionError::Limit("native erased-type depth"));
            }
            work = work
                .checked_add(body.stmts.len() as u64)
                .and_then(|work| work.checked_add(1))
                .ok_or(IrExecutionError::Limit("native erased-type adaptation"))?;
            if work > limits.ir.max_work {
                return Err(IrExecutionError::Limit("native erased-type adaptation"));
            }
            for statement in &mut body.stmts {
                match statement {
                    IrStmt::VDecl {
                        expr: IrExpr::Fap { function, args },
                        ..
                    } => {
                        let Some(&(bridge, reference_telescope)) = bridges.get(function) else {
                            continue;
                        };
                        if args.len() == bridge.runtime {
                            if reference_telescope {
                                return Err(unsupported(
                                    name,
                                    "native BaseIO task call omits explicit erased telescope",
                                ));
                            }
                            continue;
                        }
                        let erased = bridge.type_prefix + bridge.proof_suffix;
                        if args.len() != bridge.runtime + erased
                            || args[..bridge.type_prefix]
                                .iter()
                                .any(|argument| argument != &IrArg::Erased)
                            || args[args.len() - bridge.proof_suffix..]
                                .iter()
                                .any(|argument| argument != &IrArg::Erased)
                        {
                            return Err(unsupported(name, "unreviewed native erased operand"));
                        }
                        args.truncate(args.len() - bridge.proof_suffix);
                        args.drain(..bridge.type_prefix).for_each(drop);
                    }
                    IrStmt::VDecl {
                        expr: IrExpr::Pap { function, args },
                        ..
                    } if bridges
                        .get(function)
                        .is_some_and(|(bridge, reference_telescope)| {
                            *reference_telescope
                                || (bridge.type_prefix != 0 && args.first() == Some(&IrArg::Erased))
                                || (bridge.proof_suffix != 0
                                    && (args.len() > bridge.runtime
                                        || args.contains(&IrArg::Erased)))
                        }) =>
                    {
                        return Err(unsupported(name, "first-class erased native primitive"));
                    }
                    IrStmt::JDecl { value, .. } => pending.push((value, depth + 1)),
                    _ => {}
                }
            }
            if let IrTerminal::Case { alts, .. } = body.terminal.as_mut() {
                for alternative in alts {
                    let (IrAlt::Ctor { body, .. } | IrAlt::Default { body }) = alternative;
                    pending.push((body, depth + 1));
                }
            }
        }
    }
    Ok(())
}

pub(super) fn base_io_task_reference_telescope(
    row: &GeneratedExternRow,
    arity: usize,
) -> Result<bool, IrExecutionError> {
    Ok(base_io_tasks::signature(row)?.is_some_and(|signature| {
        arity == signature.erased_prefix + signature.parameters.len() + signature.erased_proofs + 1
    }))
}

/// Nat.divExact retains its divisibility proof in the pin's IR telescope,
/// while lean_nat_div_exact receives only the two naturals. Direct calls may
/// erase only a literal proof placeholder; a boxed closure must keep the slot
/// until saturation. This is runtime erasure, never proof or kernel authority.
fn natural_division_operands(
    row: &GeneratedExternRow,
) -> Result<Option<ErasedOperands>, IrExecutionError> {
    if row.id != "extern:Nat.divExact" {
        return Ok(None);
    }
    if row.name != "Nat.divExact"
        || row.symbol != "lean_nat_div_exact"
        || row.module != "Init.Data.Nat.Div.Basic"
        || row.kind != "defn"
        || row.levels != 0
        || row.arity != 3
        || row.effect != "pure"
        || row.safety != "safe"
        || row.ownership != "abi((a1: borrowed_arg, a2: borrowed_arg) -> owned_res)"
        || row.entry_class != "standard"
        || row.entry_scope != "all"
        || row.partition != "toolchain-api"
        || row.mode != "all"
        || row.profile != "faithful,sound"
        || inferred_arity(row)? != 2
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "Nat.divExact differs from its reviewed erased proof bridge".to_owned(),
        });
    }
    Ok(Some(ErasedOperands {
        runtime: 2,
        type_prefix: 0,
        proof_suffix: 1,
    }))
}

fn erased_type_runtime_arity(row: &GeneratedExternRow) -> Result<Option<usize>, IrExecutionError> {
    let (name, symbol, module, kind, levels, runtime, ownership, safety) = match row.id {
        "extern:Array.mk" => (
            "Array.mk",
            "lean_array_mk",
            "Init.Prelude",
            "ctor",
            1,
            1,
            "abi((l: owned_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.toList" => (
            "Array.toList",
            "lean_array_to_list",
            "Init.Prelude",
            "defn",
            1,
            1,
            "abi((a: owned_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.pop" => (
            "Array.pop",
            "lean_array_pop",
            "Init.Data.Array.Basic",
            "defn",
            1,
            1,
            "abi((a: owned_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.swapIfInBounds" => (
            "Array.swapIfInBounds",
            "lean_array_swap",
            "Init.Data.Array.Basic",
            "defn",
            1,
            3,
            "abi((a: owned_arg, i: borrowed_arg, j: borrowed_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.emptyWithCapacity" => (
            "Array.emptyWithCapacity",
            "lean_mk_empty_array_with_capacity",
            "Init.Prelude",
            "defn",
            1,
            1,
            "abi((capacity: borrowed_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.mkEmpty" => (
            "Array.mkEmpty",
            "lean_mk_empty_array_with_capacity",
            "Init.Prelude",
            "defn",
            1,
            1,
            "abi((capacity: borrowed_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.push" => (
            "Array.push",
            "lean_array_push",
            "Init.Prelude",
            "defn",
            1,
            2,
            "abi((a: owned_arg, v: owned_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.size" => (
            "Array.size",
            "lean_array_get_size",
            "Init.Prelude",
            "defn",
            1,
            1,
            "abi((a: borrowed_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.replicate" => (
            "Array.replicate",
            "lean_mk_array",
            "Init.Data.Array.Basic",
            "defn",
            1,
            2,
            "abi((n: owned_arg, v: owned_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.set!" => (
            "Array.set!",
            "lean_array_set",
            "Init.Data.Array.Set",
            "defn",
            1,
            3,
            "abi((a: owned_arg, i: borrowed_arg, v: owned_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.get!Internal" => (
            "Array.get!Internal",
            "lean_array_get",
            "Init.Prelude",
            "defn",
            1,
            3,
            "abi((def_val: borrowed_arg, a: borrowed_arg, i: borrowed_arg) -> raw_object)",
            "safe",
        ),
        "extern:Array.get!InternalBorrowed" => (
            "Array.get!InternalBorrowed",
            "lean_array_get_borrowed",
            "Init.Prelude",
            "opaque",
            1,
            3,
            "abi((def_val: borrowed_arg, a: borrowed_arg, i: borrowed_arg) -> raw_object)",
            "unsafe",
        ),
        "extern:Array.usize" => (
            "Array.usize",
            "lean_array_size",
            "Init.Data.Array.Basic",
            "defn",
            1,
            1,
            "abi((o: borrowed_arg) -> value)",
            "safe",
        ),
        "extern:Thunk.pure" => (
            "Thunk.pure",
            "lean_thunk_pure",
            "Init.Core",
            "defn",
            1,
            1,
            "abi((v: owned_arg) -> owned_res)",
            "safe",
        ),
        "extern:Thunk.mk" => (
            "Thunk.mk",
            "lean_mk_thunk",
            "Init.Core",
            "ctor",
            1,
            1,
            "abi((c: owned_arg) -> owned_res)",
            "safe",
        ),
        "extern:Thunk.get" => (
            "Thunk.get",
            "lean_thunk_get_own",
            "Init.Core",
            "defn",
            1,
            1,
            "abi((t: borrowed_arg) -> owned_res)",
            "safe",
        ),
        "extern:Void.mk" => (
            "Void.mk",
            "lean_void_mk",
            "Init.System.ST",
            "opaque",
            0,
            1,
            "abi((a: owned_arg) -> owned_res)",
            "safe",
        ),
        _ => return Ok(None),
    };
    if row.name != name
        || row.symbol != symbol
        || row.module != module
        || row.kind != kind
        || row.levels != levels
        || row.arity as usize != runtime + 1
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
            detail: "native primitive differs from its reviewed erased type bridge".to_owned(),
        });
    }
    Ok(Some(runtime))
}

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
    // Output getters have no runtime operands, but the original IR must
    // retain its world until the independently validated erasure pass. Their
    // boxed wrappers also retain that slot until closure saturation.
    if output_getter(row)? {
        if arity == expected {
            return Ok(expected);
        }
    } else if let Some(primitive) = BoxedNative::from_row(row)? {
        let runtime = primitive.runtime_parameters().len();
        if arity == runtime || arity == primitive.arity() {
            return Ok(runtime);
        }
    } else if let Some(runtime) = erased_type_runtime_arity(row)? {
        if arity == runtime || (row.id == "extern:Void.mk" && arity == runtime + 1) {
            return Ok(runtime);
        }
    } else if let Some(runtime) = state_runtime_arity(row)? {
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
    if let Some(primitive) = BoxedNative::from_row(row)?
        && params.len() == primitive.arity()
    {
        return primitive.validate_extern(row, params, result);
    }
    tasks::validate_native_signature(row, params, result)?;
    base_io_tasks::validate_native_signature(row, params, result)?;
    if row.id == "extern:Void.mk" && params.len() == 2 {
        erased_type_runtime_arity(row)?;
        if params[0].ty != IrType::Erased
            || params[0].borrow
            || params[1].ty != IrType::TObject
            || params[1].borrow
            || result != &IrType::Void
        {
            return Err(IrExecutionError::NativeContract {
                declaration: Name::from_components(row.name.split('.')),
                detail: "Void.mk extern differs from its reviewed erased telescope".to_owned(),
            });
        }
        return Ok(());
    }
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
/// Golem's native stream getter receives no runtime operand. Bind this
/// difference to the complete reviewed rows, never to input IR.
pub(super) fn ir_arity(row: &GeneratedExternRow) -> Result<usize, IrExecutionError> {
    if output_getter(row)? {
        Ok(1)
    } else {
        inferred_arity(row)
    }
}

fn output_getter(row: &GeneratedExternRow) -> Result<bool, IrExecutionError> {
    let (name, symbol) = match row.id {
        "extern:IO.getStdout" => ("IO.getStdout", "lean_get_stdout"),
        "extern:IO.getStderr" => ("IO.getStderr", "lean_get_stderr"),
        _ => return Ok(false),
    };
    if row.name != name
        || row.module != "Init.System.IO"
        || row.kind != "opaque"
        || row.symbol != symbol
        || row.levels != 0
        || row.arity != 0
        || row.effect != "io"
        || row.safety != "safe"
        || row.ownership != "rule(borrowed-args,owned-result)"
        || row.entry_class != "standard"
        || row.entry_scope != "all"
        || row.partition != "toolchain-api"
        || row.mode != "all"
        || row.profile != "faithful,sound"
        || inferred_arity(row)? != 0
    {
        return Err(IrExecutionError::NativeContract {
            declaration: Name::from_components(row.name.split('.')),
            detail: "output getter differs from its reviewed erased-world bridge".to_owned(),
        });
    }
    Ok(true)
}

fn reviewed_rule_arity(
    row: &GeneratedExternRow,
    ownership: &Ownership,
) -> Result<usize, extern_row::ContractError> {
    if let Some(signature) = base_io_tasks::signature(row)
        .map_err(|error| extern_row::ContractError::new(error.to_string()))?
    {
        return Ok(signature.parameters.len());
    }
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
