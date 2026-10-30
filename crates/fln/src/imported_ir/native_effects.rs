//! Native effects admitted by the explicit imported-IR executor.
//!
//! The reference-cell primitives operate on Golem-owned cells supplied as
//! ordinary checked values. They require no host I/O capability, process
//! state, imported initializer or Reference runtime. Do not generalize this
//! allowlist to every state-class row: some operate on runtime-global state.
//!
//! `take` is the pin's implementation of public modify/modifyGet. Golem moves
//! the occupant through its checked handle API and refuses a vacant or invalid
//! cell; it never invokes the assertion-based raw ABI entry point. Its erased
//! runtime arity is separately bound in native_signature.

use super::{
    EntryArgument, GeneratedExternRow, IrExecutionError, IrExecutionLimits, Name, Native, fir,
    unsupported,
};
use fln_olean::ir::{
    IrAlt, IrArg, IrBody, IrDecl, IrExpr, IrModule, IrParam, IrStmt, IrTerminal, IrType,
};
use std::collections::{BTreeMap, BTreeSet};

/// Adapt the pin's five cell primitives before arity validation. Only literal
/// Erased sigma/alpha/world operands are removed; every data operand and every
/// instruction remains for the ordinary scope/type validator. This cannot
/// hide a world read, undefined variable, effect or unauthorized callee.
/// Native one/two-operand calls retain their existing meaning and ownership.
pub(super) fn erase_state_arguments(
    module: &mut IrModule,
    natives: &BTreeMap<Name, Native>,
    limits: IrExecutionLimits,
) -> Result<bool, IrExecutionError> {
    let mut state = BTreeMap::new();
    for (name, native) in natives {
        if let Some(arity) = native.state_runtime_arity {
            state.insert(name.clone(), (arity, native.reference_state_telescope));
        }
    }
    if state.is_empty() {
        return Ok(false);
    }
    let mut changed = false;
    let mut work = 0u64;
    for declaration in &mut module.decls {
        let IrDecl::Function { name, body, .. } = declaration else {
            continue;
        };
        let mut pending = vec![(body, 1usize)];
        while let Some((body, depth)) = pending.pop() {
            if depth > limits.ir.max_depth.min(128) {
                return Err(IrExecutionError::Limit("native erased-state depth"));
            }
            work = work
                .checked_add(body.stmts.len() as u64)
                .and_then(|work| work.checked_add(1))
                .ok_or(IrExecutionError::Limit("native erased-state adaptation"))?;
            if work > limits.ir.max_work {
                return Err(IrExecutionError::Limit("native erased-state adaptation"));
            }
            for statement in &mut body.stmts {
                match statement {
                    IrStmt::VDecl {
                        expr: IrExpr::Fap { function, args },
                        ..
                    } => {
                        let Some(&(runtime, reference_telescope)) = state.get(function) else {
                            continue;
                        };
                        if args.len() == runtime {
                            if reference_telescope {
                                return Err(unsupported(
                                    name,
                                    "native state call omits explicit erased telescope",
                                ));
                            }
                            continue;
                        }
                        if args.len() != runtime + 3 {
                            return Err(unsupported(name, "unreviewed native state call arity"));
                        }
                        if args[0] != IrArg::Erased
                            || args[1] != IrArg::Erased
                            || args[runtime + 2] != IrArg::Erased
                        {
                            return Err(unsupported(
                                name,
                                "non-erased native state type or world operand",
                            ));
                        }
                        args.truncate(runtime + 2);
                        args.drain(..2).for_each(drop);
                        changed = true;
                    }
                    IrStmt::VDecl {
                        expr: IrExpr::Pap { function, args },
                        ..
                    } => {
                        if let Some(&(runtime, reference_telescope)) = state.get(function)
                            && (reference_telescope || args.len() > runtime)
                        {
                            return Err(unsupported(
                                name,
                                "first-class erased native state primitive",
                            ));
                        }
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
    Ok(changed)
}

pub(super) fn classify(
    row: &GeneratedExternRow,
    captured_output: bool,
) -> Result<fir::EffectClass, IrExecutionError> {
    match (row.effect, row.id) {
        ("pure", _) => Ok(fir::EffectClass::Pure),
        (
            "state",
            "extern:ST.Prim.mkRef"
            | "extern:ST.Prim.Ref.get"
            | "extern:ST.Prim.Ref.set"
            | "extern:ST.Prim.Ref.swap"
            | "extern:ST.Prim.Ref.take",
        ) => Ok(fir::EffectClass::State),
        ("io", "extern:IO.getStdout") if captured_output => Ok(fir::EffectClass::Io),
        _ => Err(unsupported(
            &Name::from_components(row.name.split('.')),
            "effectful native call",
        )),
    }
}

/// A Reference RealWorld slot has no executable data. Keep Void support
/// confined to unused function parameters and explicit erased entry values;
/// the general lowerer must never give those slots observable object meaning.
pub(super) fn validate_world_parameters(
    name: &Name,
    params: &[IrParam],
    body: &IrBody,
    entry_arguments: Option<&[EntryArgument]>,
) -> Result<(), IrExecutionError> {
    let mut worlds = BTreeSet::new();
    for (index, parameter) in params.iter().enumerate() {
        if parameter.ty != IrType::Void {
            continue;
        }
        if let Some(arguments) = entry_arguments
            && arguments.get(index) != Some(&EntryArgument::Erased)
        {
            return Err(unsupported(name, "non-erased entry world"));
        }
        worlds.insert(parameter.x);
    }
    if worlds.is_empty() {
        return Ok(());
    }
    let reads_arg = |arg: &IrArg| matches!(arg, IrArg::Var(x) if worlds.contains(x));
    let reads_expr = |expr: &IrExpr| match expr {
        IrExpr::Ctor { args, .. } | IrExpr::Fap { args, .. } | IrExpr::Pap { args, .. } => {
            args.iter().any(reads_arg)
        }
        IrExpr::Ap { x, args } | IrExpr::Reuse { x, args, .. } => {
            worlds.contains(x) || args.iter().any(reads_arg)
        }
        IrExpr::Reset { x, .. }
        | IrExpr::Proj { x, .. }
        | IrExpr::UProj { x, .. }
        | IrExpr::SProj { x, .. }
        | IrExpr::Box { x, .. }
        | IrExpr::Unbox { x }
        | IrExpr::IsShared { x } => worlds.contains(x),
        IrExpr::Lit(_) => false,
    };
    for body in body.bodies() {
        let statement_read = body.stmts.iter().any(|stmt| match stmt {
            IrStmt::VDecl { expr, .. } => reads_expr(expr),
            IrStmt::Set { x, y, .. } => worlds.contains(x) || reads_arg(y),
            IrStmt::USet { x, y, .. } | IrStmt::SSet { x, y, .. } => {
                worlds.contains(x) || worlds.contains(y)
            }
            IrStmt::SetTag { x, .. }
            | IrStmt::Inc { x, .. }
            | IrStmt::Dec { x, .. }
            | IrStmt::Del { x } => worlds.contains(x),
            IrStmt::JDecl { .. } => false,
        });
        let terminal_read = match body.terminal.as_ref() {
            IrTerminal::Case { x, .. } => worlds.contains(x),
            IrTerminal::Ret(arg) => reads_arg(arg),
            IrTerminal::Jmp { args, .. } => args.iter().any(reads_arg),
            IrTerminal::Unreachable => false,
        };
        if statement_read || terminal_read {
            return Err(unsupported(name, "access to an erased world parameter"));
        }
    }
    Ok(())
}

/// Remove only the pin's literal erased world from direct native stdout
/// getter calls, after validating the original IR telescope. The rewritten
/// graph is validated again against Golem's zero-argument native signature.
/// A first-class getter or a data-bearing world is outside this narrow bridge.
pub(super) fn erase_world_arguments(
    module: &mut IrModule,
    natives: &BTreeMap<Name, Native>,
    limits: IrExecutionLimits,
) -> Result<bool, IrExecutionError> {
    let stdout = Name::from_components(["IO", "getStdout"]);
    if !natives.contains_key(&stdout) {
        return Ok(false);
    }
    let mut changed = false;
    let mut work = 0u64;
    for declaration in &mut module.decls {
        let IrDecl::Function { name, body, .. } = declaration else {
            continue;
        };
        let mut pending = vec![body];
        while let Some(body) = pending.pop() {
            work = work.saturating_add(body.stmts.len() as u64 + 1);
            if work > limits.ir.max_work {
                return Err(IrExecutionError::Limit("native erased-world adaptation"));
            }
            for statement in &mut body.stmts {
                match statement {
                    IrStmt::VDecl {
                        expr: IrExpr::Fap { function, args },
                        ..
                    } if function == &stdout => {
                        if args.as_slice() != [IrArg::Erased] {
                            return Err(unsupported(name, "non-erased native stdout world"));
                        }
                        args.clear();
                        changed = true;
                    }
                    IrStmt::VDecl {
                        expr: IrExpr::Pap { function, .. },
                        ..
                    } if function == &stdout => {
                        return Err(unsupported(name, "first-class native stdout getter"));
                    }
                    IrStmt::JDecl { value, .. } => pending.push(value),
                    _ => {}
                }
            }
            if let IrTerminal::Case { alts, .. } = body.terminal.as_mut() {
                for alternative in alts {
                    let (IrAlt::Ctor { body, .. } | IrAlt::Default { body }) = alternative;
                    pending.push(body);
                }
            }
        }
    }
    Ok(changed)
}

#[cfg(test)]
mod tests;
