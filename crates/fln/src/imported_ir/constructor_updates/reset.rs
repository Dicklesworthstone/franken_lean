//! Recognize the two-join form produced by the pin's reset/reuse expansion.
//!
//! The reset arms pass either the receiver or an erased allocation token,
//! together with the same sharing bit, to a join. Its common computations run
//! once before a reuse guard. Prove the reuse alternatives equivalent before
//! discarding either guard; never interpret an isShared bit as a constant.

use super::*;

/// The adjacent declaration and guard have exactly one reset-join call site
/// on either path. Moving the join body here therefore preserves its lexical
/// captures, strict common work, and the continuation after allocation.
pub(super) fn normalize(
    body: &mut IrBody,
    scope: &Scope,
    captures: &BTreeSet<u64>,
    meter: &mut Meter,
) -> Result<bool> {
    let Some(shared_index) = equivalent(body, scope, captures, meter)? else {
        return Ok(false);
    };
    body.stmts.pop(); // The original isShared binding is no longer observable.
    let Some(IrStmt::JDecl { mut value, .. }) = body.stmts.pop() else {
        unreachable!("a verified reset region ends in a join and its guard");
    };
    let IrTerminal::Case { alts, .. } = value.terminal.as_mut() else {
        unreachable!("a verified reuse region ends in a sharing guard");
    };
    let replacement = match alts.swap_remove(shared_index) {
        IrAlt::Ctor { body, .. } | IrAlt::Default { body } => body,
    };
    body.stmts.extend(value.stmts);
    body.stmts.extend(replacement.stmts);
    body.terminal = replacement.terminal;
    meter.changed = true;
    Ok(true)
}

fn equivalent(
    body: &IrBody,
    scope: &Scope,
    captures: &BTreeSet<u64>,
    meter: &mut Meter,
) -> Result<Option<usize>> {
    let [
        ..,
        IrStmt::JDecl { j, params, value },
        IrStmt::VDecl {
            x: flag,
            ty: IrType::UInt8,
            expr: IrExpr::IsShared { x: receiver },
        },
    ] = body.stmts.as_slice()
    else {
        return Ok(None);
    };
    // Capturing the input could observe the hot-path update independently of
    // the returned fresh value. The bit itself must not escape either.
    if captures.contains(receiver) || captures.contains(flag) {
        return Ok(None);
    }
    let Some(shape) = scope.shapes.get(receiver).copied() else {
        return Ok(None);
    };
    let [token, sharing] = params.as_slice() else {
        return Ok(None);
    };
    if !matches!(token.ty, IrType::Object | IrType::TObject) || sharing.ty != IrType::UInt8 {
        return Ok(None);
    }
    let IrTerminal::Case {
        x,
        x_type: IrType::UInt8,
        alts,
        ..
    } = body.terminal.as_ref()
    else {
        return Ok(None);
    };
    if x != flag {
        return Ok(None);
    }
    let Some((exclusive, shared)) = boolean_arms(alts) else {
        return Ok(None);
    };
    for (index, allocation) in [(exclusive, IrArg::Var(*receiver)), (shared, IrArg::Erased)] {
        if !reset_arm(
            alt_body(&alts[index]),
            *j,
            [allocation, IrArg::Var(*flag)],
            *receiver,
            shape,
            meter,
        )? {
            return Ok(None);
        }
    }
    let IrTerminal::Case {
        x,
        x_type: IrType::UInt8,
        alts,
        ..
    } = value.terminal.as_ref()
    else {
        return Ok(None);
    };
    if *x != sharing.x {
        return Ok(None);
    }
    // Computations between reset and reuse may be arbitrary admitted calls,
    // but may not consume or inspect either reset parameter. Nested joins are
    // scanned too: an apparently unused capture is not permission to rewrite.
    let forbidden = [*receiver, *flag, token.x, sharing.x];
    if prefix_reads(value, &forbidden, meter)? {
        return Ok(None);
    }
    let mut reuse_scope = meter.scope(scope)?;
    reuse_scope.shapes.insert(token.x, shape);
    // A hot path omits stores that would restore an unchanged original field.
    // Bind those exact projections to the token's known incoming layout.
    for (parent, _) in reuse_scope.projections.values_mut() {
        if *parent == *receiver {
            *parent = token.x;
        }
    }
    equivalent_branches(&token.x, &sharing.x, alts, &reuse_scope, captures, meter)
}

/// The reset-only branches can retain/release references, and the hot branch
/// can read an unused field before releasing it. These reads must be in-bounds
/// projections of the known receiver; a discarded branch may not hide a call
/// or a runtime refusal. Neither branch exports any of these local variables.
fn reset_arm(
    body: &IrBody,
    join: u64,
    operands: [IrArg; 2],
    receiver: u64,
    shape: Shape,
    meter: &mut Meter,
) -> Result<bool> {
    meter.charge(body.stmts.len().saturating_add(1))?;
    for stmt in &body.stmts {
        match stmt {
            IrStmt::VDecl {
                ty: IrType::Object | IrType::TObject,
                expr: IrExpr::Proj { i, x },
                ..
            } if *x == receiver && *i < shape.fields => {}
            _ if rc_only(stmt) => {
                let mut flag_read = false;
                visit_stmt_reads(stmt, |x| flag_read |= IrArg::Var(x) == operands[1], meter)?;
                if flag_read {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(matches!(body.terminal.as_ref(), IrTerminal::Jmp { j, args }
        if *j == join && args.as_slice() == operands))
}

fn prefix_reads(body: &IrBody, forbidden: &[u64], meter: &mut Meter) -> Result<bool> {
    // Only the outer terminal may read the sharing parameter; all nested
    // terminals and statements are ordinary code and are scanned normally.
    let mut pending = vec![(body, 1usize, true)];
    while let Some((body, depth, outer)) = pending.pop() {
        meter.depth(depth)?;
        meter.charge(body.stmts.len().saturating_add(1))?;
        for stmt in &body.stmts {
            let mut found = false;
            visit_stmt_reads(stmt, |x| found |= forbidden.contains(&x), meter)?;
            if found {
                return Ok(true);
            }
            if let IrStmt::JDecl { value, .. } = stmt {
                pending.push((value, depth + 1, false));
            }
        }
        if !outer {
            let mut found = false;
            visit_terminal_reads(&body.terminal, |x| found |= forbidden.contains(&x), meter)?;
            if found {
                return Ok(true);
            }
            if let IrTerminal::Case { alts, .. } = body.terminal.as_ref() {
                meter.charge(alts.len())?;
                for alt in alts {
                    pending.push((alt_body(alt), depth + 1, false));
                }
            }
        }
    }
    Ok(false)
}

#[cfg(test)]
mod tests;
