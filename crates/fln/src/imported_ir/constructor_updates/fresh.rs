//! Fold object stores into an allocation that has not yet been read or escaped.
//!
//! The Reference emits constructor allocation and initialization separately.
//! Keep every operand computation in place, but publish one immutable Ctor at
//! the first read. A call, projection, closure capture or join declaration ends
//! the initialization region. Stores after that boundary remain unsupported.

use super::{IrArg, IrBody, IrExpr, IrStmt, IrTerminal, IrType, Meter, Result, Shape};
use super::{rc_only, visit_stmt_reads};
use crate::imported_ir::unsupported;
use fln_core::name::Name;
use fln_olean::ir::IrAlt;
use std::collections::{BTreeMap, BTreeSet};

/// No pending allocation is inherited by a child body. In particular, branch
/// and join control flow cannot grant a mutable view of an enclosing object.
pub(super) fn normalize_body(
    name: &Name,
    body: &mut IrBody,
    meter: &mut Meter,
    depth: usize,
) -> Result<()> {
    meter.depth(depth)?;
    meter.charge(body.stmts.len().saturating_add(1))?;
    let targets: BTreeSet<_> = body
        .stmts
        .iter()
        .filter_map(|stmt| match stmt {
            IrStmt::Set { x, .. } | IrStmt::SetTag { x, .. } => Some(*x),
            _ => None,
        })
        .collect();
    if !targets.is_empty() {
        let mut pending: BTreeMap<u64, IrStmt> = BTreeMap::new();
        let mut allocation_order = Vec::new();
        let mut output = Vec::new();
        for stmt in std::mem::take(&mut body.stmts) {
            match stmt {
                IrStmt::Set { x, i, y } if pending.contains_key(&x) => {
                    if y == IrArg::Var(x) {
                        return Err(unsupported(
                            name,
                            "self-referential constructor initialization",
                        ));
                    }
                    if let IrArg::Var(y) = y {
                        publish(y, &mut pending, &mut output);
                    }
                    let Some(IrStmt::VDecl {
                        expr: IrExpr::Ctor { args, .. },
                        ..
                    }) = pending.get_mut(&x)
                    else {
                        unreachable!("only fresh constructors enter the pending table");
                    };
                    meter.charge(1)?;
                    let slot = usize::try_from(i)
                        .ok()
                        .and_then(|i| args.get_mut(i))
                        .ok_or_else(|| unsupported(name, "fresh constructor field bounds"))?;
                    *slot = y;
                }
                IrStmt::SetTag { x, cidx } if pending.contains_key(&x) => {
                    if cidx > u64::from(fln_rt::abi::TAG_MAX_CTOR_TAG) {
                        return Err(unsupported(name, "fresh constructor tag bounds"));
                    }
                    let Some(IrStmt::VDecl {
                        expr: IrExpr::Ctor { info, .. },
                        ..
                    }) = pending.get_mut(&x)
                    else {
                        unreachable!("only fresh constructors enter the pending table");
                    };
                    // The debug name is not executable authority. The checked
                    // tag and unchanged object layout determine construction.
                    info.cidx = cidx;
                }
                IrStmt::JDecl { .. } => {
                    // Lowering lifts joins with their complete lexical scope.
                    // Their captures must not acquire a later version of a
                    // constructor whose definition preceded the declaration.
                    flush(&mut pending, &mut allocation_order, &mut output, meter)?;
                    output.push(stmt);
                }
                _ => {
                    let mut reads = Vec::new();
                    visit_stmt_reads(&stmt, |x| reads.push(x), meter)?;
                    if rc_only(&stmt) && reads.iter().any(|x| pending.contains_key(x)) {
                        // These annotations already have no executable meaning
                        // in the managed IR path. Keeping one before the moved
                        // allocation would only introduce a false scope error.
                        continue;
                    }
                    for x in reads {
                        publish(x, &mut pending, &mut output);
                    }
                    if let IrStmt::VDecl {
                        x,
                        ty: IrType::Object | IrType::TObject,
                        expr: IrExpr::Ctor { info, .. },
                    } = &stmt
                        && targets.contains(x)
                        && Shape::object_only(info).is_some()
                    {
                        allocation_order.push(*x);
                        pending.insert(*x, stmt);
                        meter.changed = true;
                    } else {
                        output.push(stmt);
                    }
                }
            }
        }
        flush(&mut pending, &mut allocation_order, &mut output, meter)?;
        body.stmts = output;
    }
    // Nested scopes are handled after moving the enclosing allocations, so a
    // recursive refusal cannot leave an unaccounted pending value in a parent.
    for stmt in &mut body.stmts {
        if let IrStmt::JDecl { value, .. } = stmt {
            normalize_body(name, value, meter, depth + 1)?;
        }
    }
    if let IrTerminal::Case { alts, .. } = body.terminal.as_mut() {
        meter.charge(alts.len())?;
        for alt in alts {
            let (IrAlt::Ctor { body, .. } | IrAlt::Default { body }) = alt;
            normalize_body(name, body, meter, depth + 1)?;
        }
    }
    Ok(())
}

fn publish(x: u64, pending: &mut BTreeMap<u64, IrStmt>, output: &mut Vec<IrStmt>) {
    if let Some(allocation) = pending.remove(&x) {
        output.push(allocation);
    }
}

fn flush(
    pending: &mut BTreeMap<u64, IrStmt>,
    order: &mut Vec<u64>,
    output: &mut Vec<IrStmt>,
    meter: &mut Meter,
) -> Result<()> {
    meter.charge(order.len())?;
    for x in order.drain(..) {
        publish(x, pending, output);
    }
    Ok(())
}
