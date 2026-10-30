//! Select an equivalent allocation path even when initialization is factored
//! into a shared continuation. This is not general join inlining: the join
//! must have exactly the two guarded callers, one object parameter, and a
//! nonempty store-only prefix. Its remaining computation is moved once.

use super::*;

pub(super) enum Selection {
    Branch(usize),
    Joined {
        join_index: usize,
        parameter: u64,
        stores: usize,
        fresh: u64,
        initialization: IrBody,
    },
}

pub(super) fn select(
    body: &IrBody,
    receiver: &u64,
    flag: &u64,
    scope: &Scope,
    captures: &BTreeSet<u64>,
    meter: &mut Meter,
) -> Result<Option<Selection>> {
    let IrTerminal::Case { x, x_type: IrType::UInt8, alts, .. } = body.terminal.as_ref() else {
        return Ok(None);
    };
    if x != flag {
        return Ok(None);
    }
    if let Some(index) = equivalent_branches(receiver, flag, alts, scope, captures, meter)? {
        return Ok(Some(Selection::Branch(index)));
    }
    let Some((exclusive, shared)) = boolean_arms(alts) else {
        return Ok(None);
    };
    let hot = alt_body(&alts[exclusive]);
    let cold = alt_body(&alts[shared]);
    if !flat_branch(hot, meter)? || !flat_branch(cold, meter)? {
        return Ok(None);
    }
    let (IrTerminal::Jmp { j, args: hot_args }, IrTerminal::Jmp { j: cold_j, args: cold_args }) =
        (hot.terminal.as_ref(), cold.terminal.as_ref())
    else {
        return Ok(None);
    };
    let ([IrArg::Var(hot_value)], [IrArg::Var(fresh)]) = (hot_args.as_slice(), cold_args.as_slice()) else {
        return Ok(None);
    };
    if hot_value != receiver || j != cold_j || fresh == receiver {
        return Ok(None);
    }
    meter.charge(body.stmts.len())?;
    let Some((join_index, params, continuation)) = body.stmts.iter().enumerate().find_map(|(index, stmt)| {
        match stmt {
            IrStmt::JDecl { j: target, params, value } if target == j => Some((index, params, value)),
            _ => None,
        }
    }) else {
        return Ok(None);
    };
    let [parameter] = params.as_slice() else {
        return Ok(None);
    };
    if !matches!(parameter.ty, IrType::Object | IrType::TObject) {
        return Ok(None);
    }
    let stores = continuation.stmts.iter().take_while(|stmt| store_target(stmt) == Some(parameter.x)).count();
    meter.charge(stores.saturating_mul(2).saturating_add(1))?;
    if stores == 0 || jump_count(body, *j, meter)? != 2 {
        return Ok(None);
    }
    for stmt in &continuation.stmts[..stores] {
        let self_reference = match stmt {
            IrStmt::Set { y, .. } => *y == IrArg::Var(parameter.x),
            IrStmt::USet { y, .. } | IrStmt::SSet { y, .. } => *y == parameter.x,
            _ => false,
        };
        if self_reference {
            return Ok(None);
        }
    }
    // Clone only flat branches and store instructions, never a recursive
    // continuation. The original module has already passed IR validation.
    let mut candidates = alts.to_vec();
    for (index, object) in [(exclusive, *receiver), (shared, *fresh)] {
        let (IrAlt::Ctor { body, .. } | IrAlt::Default { body }) = &mut candidates[index];
        for stmt in &continuation.stmts[..stores] {
            let mut store = stmt.clone();
            replace_stmt_reads(&mut store, parameter.x, object);
            body.stmts.push(store);
        }
        body.terminal = Box::new(IrTerminal::Ret(IrArg::Var(object)));
    }
    let (IrAlt::Ctor { body: initialized, .. } | IrAlt::Default { body: initialized }) = &mut candidates[shared];
    if !fold_object_stores(initialized, *fresh, meter)? {
        return Ok(None);
    }
    if equivalent_branches(receiver, flag, &candidates, scope, captures, meter)? != Some(shared) {
        return Ok(None);
    }
    let initialization = match candidates.swap_remove(shared) {
        IrAlt::Ctor { body, .. } | IrAlt::Default { body } => body,
    };
    Ok(Some(Selection::Joined {
        join_index,
        parameter: parameter.x,
        stores,
        fresh: *fresh,
        initialization,
    }))
}

pub(super) fn apply(body: &mut IrBody, selection: Selection, meter: &mut Meter) -> Result<()> {
    match selection {
        Selection::Branch(index) => {
            let IrTerminal::Case { alts, .. } = body.terminal.as_mut() else {
                unreachable!("selection is bound to a checked case");
            };
            let replacement = match alts.swap_remove(index) {
                IrAlt::Ctor { body, .. } | IrAlt::Default { body } => body,
            };
            body.stmts.extend(replacement.stmts);
            body.terminal = replacement.terminal;
        }
        Selection::Joined { join_index, parameter, stores, fresh, initialization } => {
            let IrStmt::JDecl { mut value, .. } = body.stmts.remove(join_index) else {
                unreachable!("selection is bound to a checked join");
            };
            drop(value.stmts.drain(..stores));
            replace_body_reads(&mut value, parameter, fresh, meter, 1)?;
            body.stmts.extend(initialization.stmts);
            body.stmts.extend(value.stmts);
            body.terminal = value.terminal;
        }
    }
    meter.changed = true;
    Ok(())
}

fn store_target(stmt: &IrStmt) -> Option<u64> {
    match stmt {
        IrStmt::Set { x, .. } | IrStmt::SetTag { x, .. } | IrStmt::USet { x, .. } | IrStmt::SSet { x, .. } => Some(*x),
        _ => None,
    }
}

fn flat_branch(body: &IrBody, meter: &mut Meter) -> Result<bool> {
    meter.charge(body.stmts.len().saturating_add(1))?;
    for stmt in &body.stmts {
        match stmt {
            IrStmt::VDecl { ty: IrType::Object | IrType::TObject, expr: IrExpr::Ctor { args, .. }, .. } => meter.charge(args.len())?,
            IrStmt::Set { .. } | IrStmt::SetTag { .. } | IrStmt::USet { .. } | IrStmt::SSet { .. } => {}
            _ if rc_only(stmt) => {}
            _ => return Ok(false),
        }
    }
    Ok(matches!(body.terminal.as_ref(), IrTerminal::Jmp { args, .. } if args.len() == 1))
}

fn jump_count(body: &IrBody, target: u64, meter: &mut Meter) -> Result<usize> {
    let mut count = 0;
    let mut pending = vec![(body, 1usize)];
    while let Some((body, depth)) = pending.pop() {
        meter.depth(depth)?;
        meter.charge(body.stmts.len().saturating_add(1))?;
        for stmt in &body.stmts {
            if let IrStmt::JDecl { value, .. } = stmt {
                pending.push((value, depth + 1));
            }
        }
        match body.terminal.as_ref() {
            IrTerminal::Jmp { j, .. } if *j == target => {
                count += 1;
                if count > 2 { return Ok(count); }
            }
            IrTerminal::Case { alts, .. } => {
                meter.charge(alts.len())?;
                for alt in alts { pending.push((alt_body(alt), depth + 1)); }
            }
            _ => {}
        }
    }
    Ok(count)
}

fn fold_object_stores(body: &mut IrBody, fresh: u64, meter: &mut Meter) -> Result<bool> {
    meter.charge(body.stmts.len())?;
    let Some(index) = body.stmts.iter().position(|stmt| matches!(stmt,
        IrStmt::VDecl { x, expr: IrExpr::Ctor { .. }, .. } if *x == fresh)) else {
        return Ok(false);
    };
    let mut dropped = BTreeSet::new();
    for i in index + 1..body.stmts.len() {
        let stmt = body.stmts[i].clone();
        let IrStmt::VDecl { expr: IrExpr::Ctor { info, args }, .. } = &mut body.stmts[index] else {
            unreachable!("fresh constructor index");
        };
        match stmt {
            IrStmt::Set { x, i: field, y } if x == fresh && y != IrArg::Var(fresh) => {
                let Some(slot) = usize::try_from(field).ok().and_then(|field| args.get_mut(field)) else { return Ok(false); };
                *slot = y;
                dropped.insert(i);
            }
            IrStmt::SetTag { x, cidx } if x == fresh && cidx <= u64::from(fln_rt::abi::TAG_MAX_CTOR_TAG) => {
                info.cidx = cidx;
                dropped.insert(i);
            }
            IrStmt::Set { .. } | IrStmt::SetTag { .. } => return Ok(false),
            _ => {}
        }
    }
    let mut index = 0usize;
    body.stmts.retain(|_| { let keep = !dropped.contains(&index); index += 1; keep });
    Ok(true)
}

fn replace_arg(arg: &mut IrArg, from: u64, to: u64) {
    if *arg == IrArg::Var(from) { *arg = IrArg::Var(to); }
}
fn replace_var(var: &mut u64, from: u64, to: u64) {
    if *var == from { *var = to; }
}
fn replace_stmt_reads(stmt: &mut IrStmt, from: u64, to: u64) {
    match stmt {
        IrStmt::VDecl { expr, .. } => {
            let args: &mut [IrArg] = match expr {
                IrExpr::Ctor { args, .. } | IrExpr::Fap { args, .. } | IrExpr::Pap { args, .. } => args,
                IrExpr::Reuse { x, args, .. } | IrExpr::Ap { x, args } => { replace_var(x, from, to); args }
                IrExpr::Reset { x, .. } | IrExpr::Proj { x, .. } | IrExpr::UProj { x, .. }
                | IrExpr::SProj { x, .. } | IrExpr::Box { x, .. } | IrExpr::Unbox { x }
                | IrExpr::IsShared { x } => { replace_var(x, from, to); &mut [] }
                IrExpr::Lit(_) => &mut [],
            };
            for arg in args { replace_arg(arg, from, to); }
        }
        IrStmt::Set { x, y, .. } => { replace_var(x, from, to); replace_arg(y, from, to); }
        IrStmt::USet { x, y, .. } | IrStmt::SSet { x, y, .. } => { replace_var(x, from, to); replace_var(y, from, to); }
        IrStmt::SetTag { x, .. } | IrStmt::Inc { x, .. } | IrStmt::Dec { x, .. } | IrStmt::Del { x } => replace_var(x, from, to),
        IrStmt::JDecl { .. } => {}
    }
}
fn replace_body_reads(body: &mut IrBody, from: u64, to: u64, meter: &mut Meter, depth: usize) -> Result<()> {
    meter.depth(depth)?;
    meter.charge(body.stmts.len().saturating_add(1))?;
    for stmt in &mut body.stmts {
        visit_stmt_reads(stmt, |_| {}, meter)?;
        replace_stmt_reads(stmt, from, to);
        if let IrStmt::JDecl { value, .. } = stmt {
            replace_body_reads(value, from, to, meter, depth + 1)?;
        }
    }
    visit_terminal_reads(&body.terminal, |_| {}, meter)?;
    match body.terminal.as_mut() {
        IrTerminal::Ret(arg) => replace_arg(arg, from, to),
        IrTerminal::Jmp { args, .. } => { for arg in args { replace_arg(arg, from, to); } }
        IrTerminal::Case { x, alts, .. } => {
            replace_var(x, from, to);
            meter.charge(alts.len())?;
            for alt in alts {
                let (IrAlt::Ctor { body, .. } | IrAlt::Default { body }) = alt;
                replace_body_reads(body, from, to, meter, depth + 1)?;
            }
        }
        IrTerminal::Unreachable => {}
    }
    Ok(())
}
