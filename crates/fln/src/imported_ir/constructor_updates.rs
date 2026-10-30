//! Eliminate checked allocation-only update branches before FIR lowering.
//!
//! The Reference may implement an immutable constructor update with an
//! `isShared` guard: mutate the exclusive input, or allocate the same result.
//! Golem's managed references do not reproduce Reference RC counts. Never
//! guess that guard's value. Instead, verify that the two alternatives differ
//! only in allocation, then retain the fresh-construction alternative.
//!
//! Fresh object-field initialization is folded before checking branches.
//! This deliberately admits only object-field updates with a known incoming
//! constructor shape. Packed updates, arbitrary mutation, observable sharing
//! flags, and effectful/different alternatives remain unsupported. No mutable
//! runtime handle, native refcount observation, or new execution authority is
//! introduced. The original and rewritten IR both undergo type validation.

use super::{IrExecutionError, IrExecutionLimits};
use fln_olean::ir::{
    IrAlt, IrArg, IrBody, IrCtorInfo, IrDecl, IrExpr, IrModule, IrStmt, IrTerminal, IrType,
};
use std::collections::{BTreeMap, BTreeSet};

mod fresh;
mod reset;

type Result<T> = std::result::Result<T, IrExecutionError>;

#[derive(Clone, Copy)]
struct Shape {
    tag: u64,
    fields: u64,
}

impl Shape {
    fn object_only(info: &IrCtorInfo) -> Option<Self> {
        (info.size > 0 && info.usize == 0 && info.ssize == 0).then_some(Self {
            tag: info.cidx,
            fields: info.size,
        })
    }
}

#[derive(Default)]
struct Scope {
    shapes: BTreeMap<u64, Shape>,
    projections: BTreeMap<u64, (u64, u64)>,
}

struct Meter {
    work: u64,
    max_work: u64,
    max_depth: usize,
    changed: bool,
}

impl Meter {
    fn charge(&mut self, count: usize) -> Result<()> {
        self.work = self
            .work
            .checked_add(count as u64)
            .ok_or(IrExecutionError::Limit("constructor update normalization"))?;
        if self.work > self.max_work {
            return Err(IrExecutionError::Limit("constructor update normalization"));
        }
        Ok(())
    }

    fn scope(&mut self, scope: &Scope) -> Result<Scope> {
        self.charge(scope.shapes.len().saturating_add(scope.projections.len()))?;
        Ok(Scope {
            shapes: scope.shapes.clone(),
            projections: scope.projections.clone(),
        })
    }

    fn depth(&self, depth: usize) -> Result<()> {
        if depth > self.max_depth {
            return Err(IrExecutionError::Limit("constructor update depth"));
        }
        Ok(())
    }
}

/// Called only after the complete selected input has passed IR validation.
/// Work, including scope snapshots and join-capture scans, has its own bound.
pub(super) fn normalize(module: &mut IrModule, limits: IrExecutionLimits) -> Result<bool> {
    let mut meter = Meter {
        work: 0,
        max_work: limits.ir.max_work,
        max_depth: limits.ir.max_depth.min(128),
        changed: false,
    };
    for declaration in &mut module.decls {
        meter.charge(1)?;
        if let IrDecl::Function { name, body, .. } = declaration {
            let (stores, sharing) = update_forms(body, &mut meter)?;
            if stores {
                fresh::normalize_body(name, body, &mut meter, 1)?;
            }
            if sharing {
                let captures = join_captures(body, &mut meter)?;
                normalize_body(body, Scope::default(), &captures, &mut meter, 1)?;
            }
        }
    }
    Ok(meter.changed)
}

// Ordinary immutable functions need neither scope snapshots nor capture scans.
fn update_forms(body: &IrBody, meter: &mut Meter) -> Result<(bool, bool)> {
    let mut stores = false;
    let mut sharing = false;
    let mut pending = vec![(body, 1usize)];
    while let Some((body, depth)) = pending.pop() {
        meter.depth(depth)?;
        meter.charge(body.stmts.len().saturating_add(1))?;
        for stmt in &body.stmts {
            match stmt {
                IrStmt::VDecl {
                    expr: IrExpr::IsShared { .. },
                    ..
                } => sharing = true,
                IrStmt::Set { .. } | IrStmt::SetTag { .. } => stores = true,
                IrStmt::JDecl { value, .. } => pending.push((value, depth + 1)),
                _ => {}
            }
        }
        if stores && sharing {
            return Ok((stores, sharing));
        }
        if let IrTerminal::Case { alts, .. } = body.terminal.as_ref() {
            meter.charge(alts.len())?;
            for alt in alts {
                pending.push((alt_body(alt), depth + 1));
            }
        }
    }
    Ok((stores, sharing))
}

/// A join capturing the updated object could observe an in-place write without
/// receiving that object explicitly. Reject such regions, even when the join
/// appears unused. Declaration-wide unique indices let us subtract locally
/// bound values without comparing names or guessing lexical scope.
fn join_captures(body: &IrBody, meter: &mut Meter) -> Result<BTreeSet<u64>> {
    let mut captures = BTreeSet::new();
    let mut pending = vec![(body, 1usize)];
    while let Some((body, depth)) = pending.pop() {
        meter.depth(depth)?;
        meter.charge(body.stmts.len().saturating_add(1))?;
        for stmt in &body.stmts {
            if let IrStmt::JDecl { params, value, .. } = stmt {
                let mut bound = BTreeSet::new();
                let mut reads = BTreeSet::new();
                for param in params {
                    meter.charge(1)?;
                    bound.insert(param.x);
                }
                let mut nested = vec![(value, depth + 1)];
                while let Some((child, child_depth)) = nested.pop() {
                    meter.depth(child_depth)?;
                    meter.charge(child.stmts.len().saturating_add(1))?;
                    for stmt in &child.stmts {
                        match stmt {
                            IrStmt::VDecl { x, .. } => {
                                bound.insert(*x);
                            }
                            IrStmt::JDecl { params, value, .. } => {
                                for param in params {
                                    meter.charge(1)?;
                                    bound.insert(param.x);
                                }
                                nested.push((value, child_depth + 1));
                            }
                            _ => {}
                        }
                        visit_stmt_reads(
                            stmt,
                            |x| {
                                reads.insert(x);
                            },
                            meter,
                        )?;
                    }
                    visit_terminal_reads(
                        &child.terminal,
                        |x| {
                            reads.insert(x);
                        },
                        meter,
                    )?;
                    if let IrTerminal::Case { alts, .. } = child.terminal.as_ref() {
                        meter.charge(alts.len())?;
                        for alt in alts {
                            nested.push((alt_body(alt), child_depth + 1));
                        }
                    }
                }
                meter.charge(reads.len())?;
                captures.extend(reads.difference(&bound).copied());
                pending.push((value, depth + 1));
            }
        }
        if let IrTerminal::Case { alts, .. } = body.terminal.as_ref() {
            meter.charge(alts.len())?;
            for alt in alts {
                pending.push((alt_body(alt), depth + 1));
            }
        }
    }
    Ok(captures)
}

fn alt_body(alt: &IrAlt) -> &IrBody {
    match alt {
        IrAlt::Ctor { body, .. } | IrAlt::Default { body } => body,
    }
}

fn visit_stmt_reads(stmt: &IrStmt, mut visit: impl FnMut(u64), meter: &mut Meter) -> Result<()> {
    match stmt {
        IrStmt::VDecl { expr, .. } => {
            let args = match expr {
                IrExpr::Ctor { args, .. } | IrExpr::Fap { args, .. } | IrExpr::Pap { args, .. } => {
                    args.as_slice()
                }
                IrExpr::Reuse { x, args, .. } | IrExpr::Ap { x, args } => {
                    meter.charge(1)?;
                    visit(*x);
                    args.as_slice()
                }
                IrExpr::Reset { x, .. }
                | IrExpr::Proj { x, .. }
                | IrExpr::UProj { x, .. }
                | IrExpr::SProj { x, .. }
                | IrExpr::Box { x, .. }
                | IrExpr::Unbox { x }
                | IrExpr::IsShared { x } => {
                    meter.charge(1)?;
                    visit(*x);
                    &[]
                }
                IrExpr::Lit(_) => &[],
            };
            for arg in args {
                meter.charge(1)?;
                if let IrArg::Var(x) = arg {
                    visit(*x);
                }
            }
        }
        IrStmt::Set { x, y, .. } => {
            meter.charge(2)?;
            visit(*x);
            if let IrArg::Var(y) = y {
                visit(*y);
            }
        }
        IrStmt::USet { x, y, .. } | IrStmt::SSet { x, y, .. } => {
            meter.charge(2)?;
            visit(*x);
            visit(*y);
        }
        IrStmt::SetTag { x, .. }
        | IrStmt::Inc { x, .. }
        | IrStmt::Dec { x, .. }
        | IrStmt::Del { x } => {
            meter.charge(1)?;
            visit(*x);
        }
        IrStmt::JDecl { .. } => {}
    }
    Ok(())
}

fn visit_terminal_reads(
    terminal: &IrTerminal,
    mut visit: impl FnMut(u64),
    meter: &mut Meter,
) -> Result<()> {
    match terminal {
        IrTerminal::Case { x, .. } => {
            meter.charge(1)?;
            visit(*x);
        }
        IrTerminal::Ret(IrArg::Var(x)) => {
            meter.charge(1)?;
            visit(*x);
        }
        IrTerminal::Jmp { args, .. } => {
            for arg in args {
                meter.charge(1)?;
                if let IrArg::Var(x) = arg {
                    visit(*x);
                }
            }
        }
        IrTerminal::Ret(IrArg::Erased) | IrTerminal::Unreachable => {}
    }
    Ok(())
}

fn normalize_body(
    body: &mut IrBody,
    mut scope: Scope,
    captures: &BTreeSet<u64>,
    meter: &mut Meter,
    depth: usize,
) -> Result<()> {
    meter.depth(depth)?;
    meter.charge(body.stmts.len().saturating_add(1))?;
    for stmt in &mut body.stmts {
        match stmt {
            IrStmt::VDecl {
                x,
                expr: IrExpr::Ctor { info, .. },
                ..
            } => {
                if let Some(shape) = Shape::object_only(info) {
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
            IrStmt::JDecl { value, .. } => {
                let child_scope = meter.scope(&scope)?;
                normalize_body(value, child_scope, captures, meter, depth + 1)?;
            }
            _ => {}
        }
    }
    if reset::normalize(body, &scope, captures, meter)? {
        return Ok(());
    }
    if let Some(index) = equivalent_update(body, &scope, captures, meter)? {
        let IrTerminal::Case { alts, .. } = body.terminal.as_mut() else {
            unreachable!("a verified update is a case");
        };
        let replacement = match alts.swap_remove(index) {
            IrAlt::Ctor { body, .. } | IrAlt::Default { body } => body,
        };
        body.stmts.pop(); // The flag is used only by the eliminated discriminator.
        body.stmts.extend(replacement.stmts);
        body.terminal = replacement.terminal;
        meter.changed = true;
        return Ok(());
    }
    if let IrTerminal::Case {
        x, x_type, alts, ..
    } = body.terminal.as_mut()
    {
        meter.charge(alts.len())?;
        for alt in alts {
            let mut child_scope = meter.scope(&scope)?;
            let child = match alt {
                IrAlt::Ctor { info, body } => {
                    if matches!(x_type, IrType::Object | IrType::TObject)
                        && let Some(shape) = Shape::object_only(info)
                    {
                        child_scope.shapes.insert(*x, shape);
                    }
                    body
                }
                IrAlt::Default { body } => body,
            };
            normalize_body(child, child_scope, captures, meter, depth + 1)?;
        }
    }
    Ok(())
}

fn rc_only(stmt: &IrStmt) -> bool {
    matches!(
        stmt,
        IrStmt::Inc { .. } | IrStmt::Dec { .. } | IrStmt::Del { .. }
    )
}

/// Return the shared-alternative index only after checking every field, tag,
/// operand and continuation. Not recognizing a pattern never grants support.
fn equivalent_update(
    body: &IrBody,
    scope: &Scope,
    captures: &BTreeSet<u64>,
    meter: &mut Meter,
) -> Result<Option<usize>> {
    let Some(IrStmt::VDecl {
        x: flag,
        ty: IrType::UInt8,
        expr: IrExpr::IsShared { x: receiver },
    }) = body.stmts.last()
    else {
        return Ok(None);
    };
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
    equivalent_branches(receiver, flag, alts, scope, captures, meter)
}

// The caller proves that the discriminator is precisely an isShared bit for
// this receiver (directly or through a checked reset-join parameter).
fn equivalent_branches(
    receiver: &u64,
    flag: &u64,
    alts: &[IrAlt],
    scope: &Scope,
    captures: &BTreeSet<u64>,
    meter: &mut Meter,
) -> Result<Option<usize>> {
    if captures.contains(receiver) || captures.contains(flag) {
        return Ok(None);
    }
    let Some(shape) = scope.shapes.get(receiver) else {
        return Ok(None);
    };
    let Some((exclusive_index, shared_index)) = boolean_arms(alts) else {
        return Ok(None);
    };
    let exclusive = alt_body(&alts[exclusive_index]);
    let shared = alt_body(&alts[shared_index]);
    meter.charge(exclusive.stmts.len().saturating_add(shared.stmts.len()))?;
    let mut writes = BTreeMap::new();
    let mut tag = shape.tag;
    let mut changed_tag = false;
    for stmt in &exclusive.stmts {
        match stmt {
            IrStmt::Set { x, i, y } if x == receiver && *i < shape.fields => {
                if *y == IrArg::Var(*receiver)
                    || *y == IrArg::Var(*flag)
                    || writes.insert(*i, *y).is_some()
                {
                    return Ok(None);
                }
            }
            IrStmt::SetTag { x, cidx } if x == receiver && !changed_tag => {
                tag = *cidx;
                changed_tag = true;
            }
            _ if rc_only(stmt) => {
                let mut flag_read = false;
                visit_stmt_reads(stmt, |x| flag_read |= x == *flag, meter)?;
                if flag_read {
                    return Ok(None);
                }
            }
            _ => return Ok(None),
        }
    }
    let mut allocation = None;
    for stmt in &shared.stmts {
        match stmt {
            IrStmt::VDecl {
                x,
                ty,
                expr: IrExpr::Ctor { info, args },
            } if matches!(ty, IrType::Object | IrType::TObject) && allocation.is_none() => {
                allocation = Some((*x, info, args));
            }
            _ if rc_only(stmt) => {
                let mut flag_read = false;
                visit_stmt_reads(stmt, |x| flag_read |= x == *flag, meter)?;
                if flag_read {
                    return Ok(None);
                }
            }
            _ => return Ok(None),
        }
    }
    let Some((fresh, info, args)) = allocation else {
        return Ok(None);
    };
    let Some(new_shape) = Shape::object_only(info) else {
        return Ok(None);
    };
    if new_shape.fields != shape.fields || new_shape.tag != tag || args.len() as u64 != shape.fields
    {
        return Ok(None);
    }
    meter.charge(args.len())?;
    for (index, actual) in args.iter().enumerate() {
        if *actual == IrArg::Var(*receiver) || *actual == IrArg::Var(*flag) {
            return Ok(None);
        }
        if let Some(expected) = writes.get(&(index as u64)) {
            if actual != expected {
                return Ok(None);
            }
        } else {
            let IrArg::Var(projected) = actual else {
                return Ok(None);
            };
            if scope.projections.get(projected) != Some(&(*receiver, index as u64)) {
                return Ok(None);
            }
        }
    }
    let same_result = match (exclusive.terminal.as_ref(), shared.terminal.as_ref()) {
        (IrTerminal::Ret(a), IrTerminal::Ret(b)) => {
            *a == IrArg::Var(*receiver) && *b == IrArg::Var(fresh)
        }
        (IrTerminal::Jmp { j: a, args: xs }, IrTerminal::Jmp { j: b, args: ys })
            if a == b && xs.len() == ys.len() =>
        {
            meter.charge(xs.len())?;
            let mut returned = false;
            let mut equal = true;
            for (x, y) in xs.iter().zip(ys) {
                if *x == IrArg::Var(*receiver) {
                    returned = true;
                    equal &= *y == IrArg::Var(fresh);
                } else {
                    equal &= x == y && *x != IrArg::Var(*flag);
                }
            }
            returned && equal
        }
        _ => false,
    };
    Ok(same_result.then_some(shared_index))
}

/// A single default denotes exactly the missing bit, never an arbitrary tag.
fn boolean_arms(alts: &[IrAlt]) -> Option<(usize, usize)> {
    if alts.len() != 2 {
        return None;
    }
    let mut exclusive = None;
    let mut shared = None;
    let mut fallback = None;
    for (index, alt) in alts.iter().enumerate() {
        match alt {
            IrAlt::Ctor { info, .. } if info.size == 0 && info.usize == 0 && info.ssize == 0 => {
                match info.cidx {
                    0 if exclusive.is_none() => exclusive = Some(index),
                    1 if shared.is_none() => shared = Some(index),
                    _ => return None,
                }
            }
            IrAlt::Default { .. } if fallback.is_none() => fallback = Some(index),
            _ => return None,
        }
    }
    match (exclusive, shared, fallback) {
        (Some(exclusive), Some(shared), None)
        | (Some(exclusive), None, Some(shared))
        | (None, Some(shared), Some(exclusive)) => Some((exclusive, shared)),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
