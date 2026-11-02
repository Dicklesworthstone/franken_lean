//! Recognize the two-join form produced by the pin's reset/reuse expansion.
//!
//! The reset arms pass either the receiver or an erased allocation token,
//! together with the same sharing bit, to a join. Its common computations run
//! once before a reuse guard. Prove the reuse alternatives equivalent before
//! discarding either guard; never interpret an isShared bit as a constant.

use super::*;

enum Choice {
    Immediate(selection::Selection),
    Deferred { token: u64, plan: Deferred },
}

// A plan contains only tree positions and selected alternatives, not cloned
// IR. No mutation is performed until every token/bit use has been checked.
struct Deferred {
    joins: Vec<(usize, Deferred)>,
    terminal: DeferredTerminal,
}

enum DeferredTerminal {
    Leaf,
    Case(Vec<Deferred>),
    Reuse(usize, Box<Deferred>),
}

/// The adjacent declaration and guard have exactly one reset-join call site
/// on either path. Moving the join body here therefore preserves its lexical
/// captures, strict common work, and the continuation after allocation.
pub(super) fn normalize(
    body: &mut IrBody,
    scope: &Scope,
    captures: &BTreeSet<u64>,
    meter: &mut Meter,
    depth: usize,
) -> Result<bool> {
    if let Some(choice) = equivalent(body, scope, captures, meter)? {
        apply(body, choice, meter)?;
        return Ok(true);
    }
    let Some((receiver, info)) = object_candidate(body, scope, meter)? else {
        return Ok(false);
    };
    // The fresh allocation is a candidate, never evidence about the input.
    // Prove the entire reset/reuse region under that conditional layout, then
    // establish it with an executable guard before moving any common work.
    let mut guarded_scope = meter.scope(scope)?;
    guarded_scope.shapes.insert(
        receiver,
        Shape::object_only(&info).expect("candidate is an object-only heap constructor"),
    );
    let Some(choice) = equivalent(body, &guarded_scope, captures, meter)? else {
        return Ok(false);
    };
    meter.depth(depth + 1)?;
    meter.charge(3)?;
    // Keep every original strict prefix statement before the guard. Only the
    // adjacent lexical join and its isShared binding move into the matching
    // arm; neither the discarded reset arm nor common calls run on a mismatch.
    let stmts = body.stmts.split_off(body.stmts.len() - 2);
    let terminal = std::mem::replace(&mut body.terminal, Box::new(IrTerminal::Unreachable));
    let mut matching = IrBody { stmts, terminal };
    apply(&mut matching, choice, meter)?;
    *body.terminal = IrTerminal::Case {
        // This name is diagnostic metadata. The runtime witness comes from
        // the complete CtorInfo layout, lowered to CtorLayoutTest.
        type_name: info.name.clone(),
        x: receiver,
        x_type: IrType::TObject,
        alts: vec![
            IrAlt::Ctor {
                info,
                body: matching,
            },
            IrAlt::Default {
                body: IrBody {
                    stmts: Vec::new(),
                    terminal: Box::new(IrTerminal::Unreachable),
                },
            },
        ],
    };
    Ok(true)
}

fn apply(body: &mut IrBody, choice: Choice, meter: &mut Meter) -> Result<()> {
    body.stmts.pop(); // The original isShared binding is no longer observable.
    let Some(IrStmt::JDecl { mut value, .. }) = body.stmts.pop() else {
        unreachable!("a verified reset region ends in a join and its guard");
    };
    match choice {
        Choice::Immediate(choice) => selection::apply(&mut value, choice, meter)?,
        Choice::Deferred { token, plan } => apply_deferred(&mut value, plan, token, meter)?,
    }
    body.stmts.extend(value.stmts);
    body.terminal = value.terminal;
    meter.changed = true;
    Ok(())
}

/// Infer only a prospective object-only layout from one cold allocation.
/// Packed layouts are excluded: aligned allocation size cannot distinguish a
/// short scalar payload from padding. The existing equivalence checker still
/// verifies all stores, unchanged projections, captures and continuations.
fn object_candidate(
    body: &IrBody,
    scope: &Scope,
    meter: &mut Meter,
) -> Result<Option<(u64, IrCtorInfo)>> {
    let [
        ..,
        IrStmt::JDecl { params, value, .. },
        IrStmt::VDecl {
            ty: IrType::UInt8,
            expr: IrExpr::IsShared { x: receiver },
            ..
        },
    ] = body.stmts.as_slice()
    else {
        return Ok(None);
    };
    if scope.shapes.contains_key(receiver) {
        return Ok(None);
    }
    let [_, sharing] = params.as_slice() else {
        return Ok(None);
    };
    let mut pending = vec![(value, 1usize)];
    while let Some((body, depth)) = pending.pop() {
        meter.depth(depth)?;
        meter.charge(body.stmts.len().saturating_add(1))?;
        if let IrTerminal::Case { x, alts, .. } = body.terminal.as_ref()
            && *x == sharing.x
            && let Some((_, shared)) = boolean_arms(alts)
        {
            for stmt in &alt_body(&alts[shared]).stmts {
                meter.charge(1)?;
                if let IrStmt::VDecl {
                    expr: IrExpr::Ctor { info, .. },
                    ..
                } = stmt
                    && Shape::object_only(info).is_some()
                {
                    return Ok(Some((*receiver, info.clone())));
                }
            }
        }
        for stmt in &body.stmts {
            if let IrStmt::JDecl { value, .. } = stmt {
                pending.push((value, depth + 1));
            }
        }
        if let IrTerminal::Case { alts, .. } = body.terminal.as_ref() {
            meter.charge(alts.len())?;
            pending.extend(alts.iter().map(|alt| (alt_body(alt), depth + 1)));
        }
    }
    Ok(None)
}

fn equivalent(
    body: &IrBody,
    scope: &Scope,
    captures: &BTreeSet<u64>,
    meter: &mut Meter,
) -> Result<Option<Choice>> {
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
    // Computations between reset and reuse may be arbitrary admitted calls,
    // but may not consume or inspect either reset parameter. Nested joins are
    // scanned too: an apparently unused capture is not permission to rewrite.
    let forbidden = [*receiver, *flag, token.x, sharing.x];
    let mut reuse_scope = meter.scope(scope)?;
    reuse_scope.shapes.insert(token.x, shape);
    // A hot path omits stores that would restore an unchanged original field.
    // Bind those exact projections to the token's known incoming layout.
    for (parent, _) in reuse_scope.projections.values_mut() {
        if *parent == *receiver {
            *parent = token.x;
        }
    }
    for (parent, _) in reuse_scope.scalars.values_mut() {
        if *parent == *receiver {
            *parent = token.x;
        }
    }
    if !prefix_reads(value, &forbidden, meter)?
        && let Some(choice) =
            selection::select(value, &token.x, &sharing.x, &reuse_scope, captures, meter)?
    {
        return Ok(Some(Choice::Immediate(choice)));
    }
    let mut joins = BTreeMap::new();
    let mut pending = vec![(value, 1usize)];
    while let Some((body, depth)) = pending.pop() {
        meter.depth(depth)?;
        meter.charge(body.stmts.len().saturating_add(1))?;
        for stmt in &body.stmts {
            if let IrStmt::JDecl { j, value, .. } = stmt {
                joins.insert(*j, value);
                pending.push((value, depth + 1));
            }
        }
        if let IrTerminal::Case { alts, .. } = body.terminal.as_ref() {
            meter.charge(alts.len())?;
            pending.extend(alts.iter().map(|alt| (alt_body(alt), depth + 1)));
        }
    }
    let mut guards = 0;
    let plan = deferred(value, reuse_scope, forbidden, &joins, meter, 1, &mut guards)?;
    Ok(plan.filter(|_| guards > 0).map(|plan| Choice::Deferred {
        token: token.x,
        plan,
    }))
}

/// Only allocation-equivalent guards may observe the token/bit. Captures of
/// these *local join parameters* are checked by walking every nested body,
/// including unused joins. The original receiver's declaration-wide capture
/// prohibition above remains in force. Ordinary calls and terminals cannot
/// receive the token, its sharing bit, or the original reset operands.
fn deferred(
    body: &IrBody,
    mut scope: Scope,
    forbidden: [u64; 4],
    joins: &BTreeMap<u64, &IrBody>,
    meter: &mut Meter,
    depth: usize,
    guards: &mut usize,
) -> Result<Option<Deferred>> {
    meter.depth(depth)?;
    meter.charge(body.stmts.len().saturating_add(1))?;
    let [_, _, token, sharing] = forbidden;
    let mut nested_joins = Vec::new();
    for (index, stmt) in body.stmts.iter().enumerate() {
        let mut invalid = false;
        visit_stmt_reads(
            stmt,
            |x| invalid |= forbidden.contains(&x) && !(x == token && rc_only(stmt)),
            meter,
        )?;
        if invalid {
            return Ok(None);
        }
        match stmt {
            IrStmt::VDecl {
                x,
                expr: IrExpr::Ctor { info, .. },
                ..
            } => {
                if let Some(shape) = Shape::from_info(info) {
                    scope.shapes.insert(*x, shape);
                }
            }
            IrStmt::VDecl {
                x,
                expr: IrExpr::Proj { i, x: receiver },
                ..
            } => {
                scope.projections.insert(*x, (*receiver, *i));
            }
            IrStmt::VDecl { x, ty, expr } => {
                if let Some(projection) = packed::projection(ty, expr) {
                    scope.scalars.insert(*x, projection);
                }
            }
            IrStmt::JDecl { value, .. } => {
                let child_scope = meter.scope(&scope)?;
                let Some(plan) = deferred(
                    value,
                    child_scope,
                    forbidden,
                    joins,
                    meter,
                    depth + 1,
                    guards,
                )?
                else {
                    return Ok(None);
                };
                nested_joins.push((index, plan));
            }
            _ => {}
        }
    }
    let terminal = if let IrTerminal::Case { x, alts, .. } = body.terminal.as_ref()
        && *x == sharing
    {
        // The exhaustive use check replaces only the conservative capture
        // rejection for these two local parameters. Every field, tag, packed
        // slot and outgoing argument still passes the existing proof.
        let Some(selection::Selection::Branch(index)) =
            selection::select(body, &token, &sharing, &scope, &BTreeSet::new(), meter)?
        else {
            return Ok(None);
        };
        if !consumed_once(alt_body(&alts[index]), joins, token, sharing, meter)? {
            return Ok(None);
        }
        let Some(plan) = deferred(
            alt_body(&alts[index]),
            scope,
            forbidden,
            joins,
            meter,
            depth + 1,
            guards,
        )?
        else {
            return Ok(None);
        };
        *guards += 1;
        DeferredTerminal::Reuse(index, Box::new(plan))
    } else {
        let mut invalid = false;
        visit_terminal_reads(&body.terminal, |x| invalid |= forbidden.contains(&x), meter)?;
        if invalid {
            return Ok(None);
        }
        if let IrTerminal::Case {
            x, x_type, alts, ..
        } = body.terminal.as_ref()
        {
            meter.charge(alts.len())?;
            let mut plans = Vec::new();
            for alt in alts {
                let mut child_scope = meter.scope(&scope)?;
                if matches!(x_type, IrType::Object | IrType::TObject)
                    && let IrAlt::Ctor { info, .. } = alt
                    && let Some(shape) = Shape::from_info(info)
                {
                    child_scope.shapes.insert(*x, shape);
                }
                let Some(plan) = deferred(
                    alt_body(alt),
                    child_scope,
                    forbidden,
                    joins,
                    meter,
                    depth + 1,
                    guards,
                )?
                else {
                    return Ok(None);
                };
                plans.push(plan);
            }
            DeferredTerminal::Case(plans)
        } else {
            DeferredTerminal::Leaf
        }
    };
    Ok(Some(Deferred {
        joins: nested_joins,
        terminal,
    }))
}

/// Once a reuse guard consumes its token, no reachable local continuation
/// may observe it or its sharing bit again. Otherwise a later reuse could
/// mutate an earlier returned alias, although each guard looked equivalent
/// in isolation. External joins cannot capture these lexical parameters.
fn consumed_once(
    selected: &IrBody,
    joins: &BTreeMap<u64, &IrBody>,
    token: u64,
    sharing: u64,
    meter: &mut Meter,
) -> Result<bool> {
    let mut targets = Vec::new();
    if let IrTerminal::Jmp { j, .. } = selected.terminal.as_ref() {
        targets.push(*j);
    }
    let mut visited = BTreeSet::new();
    while let Some(target) = targets.pop() {
        meter.charge(1)?;
        if !visited.insert(target) {
            continue;
        }
        let Some(body) = joins.get(&target) else {
            continue;
        };
        let mut pending = vec![(*body, 1usize)];
        while let Some((body, depth)) = pending.pop() {
            meter.depth(depth)?;
            meter.charge(body.stmts.len().saturating_add(1))?;
            let mut invalid = false;
            for stmt in &body.stmts {
                visit_stmt_reads(stmt, |x| invalid |= x == token || x == sharing, meter)?;
                if let IrStmt::JDecl { value, .. } = stmt {
                    pending.push((value, depth + 1));
                }
            }
            visit_terminal_reads(
                &body.terminal,
                |x| invalid |= x == token || x == sharing,
                meter,
            )?;
            if invalid {
                return Ok(false);
            }
            match body.terminal.as_ref() {
                IrTerminal::Jmp { j, .. } => targets.push(*j),
                IrTerminal::Case { alts, .. } => {
                    meter.charge(alts.len())?;
                    pending.extend(alts.iter().map(|alt| (alt_body(alt), depth + 1)));
                }
                _ => {}
            }
        }
    }
    Ok(true)
}

fn apply_deferred(body: &mut IrBody, plan: Deferred, token: u64, meter: &mut Meter) -> Result<()> {
    meter.charge(body.stmts.len().saturating_add(1))?;
    for (index, plan) in plan.joins {
        let IrStmt::JDecl { value, .. } = &mut body.stmts[index] else {
            unreachable!("deferred plan is bound to a checked join");
        };
        apply_deferred(value, plan, token, meter)?;
    }
    // An erased cold-path token is not a runtime value. Its remaining RC-only
    // uses disappear together with the reset join, never becoming free reads.
    body.stmts.retain(|stmt| {
        !matches!(stmt,
        IrStmt::Inc { x, .. } | IrStmt::Dec { x, .. } | IrStmt::Del { x } if *x == token)
    });
    match plan.terminal {
        DeferredTerminal::Leaf => {}
        DeferredTerminal::Case(plans) => {
            let IrTerminal::Case { alts, .. } = body.terminal.as_mut() else {
                unreachable!("deferred plan is bound to a checked case");
            };
            for (alt, plan) in alts.iter_mut().zip(plans) {
                let (IrAlt::Ctor { body, .. } | IrAlt::Default { body }) = alt;
                apply_deferred(body, plan, token, meter)?;
            }
        }
        DeferredTerminal::Reuse(index, plan) => {
            let IrTerminal::Case { alts, .. } = body.terminal.as_mut() else {
                unreachable!("deferred plan is bound to a checked reuse guard");
            };
            let (IrAlt::Ctor {
                body: mut replacement,
                ..
            }
            | IrAlt::Default {
                body: mut replacement,
            }) = alts.swap_remove(index);
            apply_deferred(&mut replacement, *plan, token, meter)?;
            body.stmts.extend(replacement.stmts);
            body.terminal = replacement.terminal;
        }
    }
    Ok(())
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
mod reference;
#[cfg(test)]
mod tests;
