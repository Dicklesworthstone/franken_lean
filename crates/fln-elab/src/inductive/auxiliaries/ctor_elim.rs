//! Native `ctorElimType`, `ctorElim`, and `<ctor>.elim` candidates
//! (fln-derived-declaration-frontier-cj7s).
//!
//! Algorithm: the pin's `Lean/Meta/Constructions/CtorElim.lean` (`mkCtorElim`,
//! `mkCtorElimType`, `mkIndCtorElim`, `mkConstructorElim`) and
//! `Lean/Meta/NatTable.lean::mkNatLookupTable`.
//!
//! Candidate generation confers no admission or attribute authority: every
//! produced definition must pass both checking seats through the caller's
//! ordinary admission path.

use super::ctor_idx::{
    CtorIdxConstMeta, bounded_telescope, instantiate_forall, is_prop_former, scan_const_meta,
};
use super::*;
use fln_core::expr::{Literal, NatLit};
use fln_core::level::LevelView;
use fln_env::constants::{ConstantInfo, ConstructorVal};
use std::collections::HashMap;

/// Generated `<T>.ctorElimType`, `<T>.ctorElim`, and per-constructor
/// `<ctor>.elim` definitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtorElimCandidates {
    pub ctor_elim_type: DefinitionVal,
    pub ctor_elim: DefinitionVal,
    pub constructor_elims: Vec<DefinitionVal>,
}

/// Right-associates top-level `Level::Max` nodes (`CtorElim.lean::reassocMax`).
fn reassoc_max(work: &mut Builder, level: Level) -> Result<Level, AuxiliaryError> {
    let mut leaves = Vec::new();
    let mut stack = vec![level];
    while let Some(cur) = stack.pop() {
        work.tick()?;
        match cur.view() {
            LevelView::Max(l1, l2) => {
                stack.push(l2.clone());
                stack.push(l1.clone());
            }
            _ => leaves.push(cur),
        }
    }
    let Some(mut acc) = leaves.pop() else {
        return Err(AuxiliaryError::InvalidTelescope);
    };
    while let Some(lhs) = leaves.pop() {
        work.tick()?;
        acc = Level::max(lhs, acc).map_err(|_| AuxiliaryError::ResourceLimit)?;
    }
    Ok(acc)
}

fn max_levels(work: &mut Builder, levels: &[Level]) -> Result<Level, AuxiliaryError> {
    let Some(first) = levels.first() else {
        return Err(AuxiliaryError::InvalidTelescope);
    };
    let mut acc = first.clone();
    for lvl in &levels[1..] {
        work.tick()?;
        acc = Level::try_smart_max(acc, lvl.clone()).map_err(|_| AuxiliaryError::ResourceLimit)?;
    }
    reassoc_max(work, acc.normalize())
}

/// Binary-search lookup table over `Nat` (`Lean/Meta/NatTable.lean::mkNatLookupTable`).
fn mk_nat_lookup_table(
    work: &mut Builder,
    index: &Expr,
    table_type: &Expr,
    table_type_level: &Level,
    entries: &[Expr],
) -> Result<Expr, AuxiliaryError> {
    if entries.is_empty() {
        return Err(AuxiliaryError::InvalidTelescope);
    }
    fn go(
        work: &mut Builder,
        index: &Expr,
        table_type: &Expr,
        table_type_level: &Level,
        entries: &[Expr],
        start: usize,
        stop: usize,
    ) -> Result<Expr, AuxiliaryError> {
        work.tick()?;
        if start + 1 == stop {
            return Ok(entries[start].clone());
        }
        let mid = start + (stop - start) / 2;
        let low = go(
            work,
            index,
            table_type,
            table_type_level,
            entries,
            start,
            mid,
        )?;
        let high = go(
            work,
            index,
            table_type,
            table_type_level,
            entries,
            mid,
            stop,
        )?;
        let ble = app(
            Expr::const_(Name::from_components(["Nat", "ble"]), Vec::new()),
            [
                index.clone(),
                Expr::lit(Literal::Nat(NatLit::from_u64((mid - 1) as u64))),
            ],
        );
        Ok(app(
            Expr::const_(
                Name::from_components(["cond"]),
                vec![table_type_level.clone()],
            ),
            [table_type.clone(), ble, low, high],
        ))
    }
    go(
        work,
        index,
        table_type,
        table_type_level,
        entries,
        0,
        entries.len(),
    )
}

enum NameAtom {
    Str(String),
    Num(u64),
}

fn name_atoms(name: &Name) -> Vec<NameAtom> {
    let mut rev = Vec::new();
    let mut cur = name.clone();
    while !cur.is_anonymous() {
        match cur.leaf_view() {
            LeafView::Str(s) => rev.push(NameAtom::Str(s.to_owned())),
            LeafView::Num(n) => rev.push(NameAtom::Num(n)),
            LeafView::Anonymous => break,
        }
        cur = cur.parent();
    }
    rev.reverse();
    rev
}

fn build_name(atoms: &[NameAtom]) -> Name {
    let mut acc = Name::anonymous();
    for atom in atoms {
        acc = match atom {
            NameAtom::Str(s) => Name::str(acc, s.clone()),
            NameAtom::Num(n) => Name::num(acc, *n),
        };
    }
    acc
}

/// Split a Lean private name `_private.<mod>.<idx>.<user>` into `(prefix, user)`.
fn split_private_name(name: &Name) -> (Option<Vec<NameAtom>>, Vec<NameAtom>) {
    let atoms = name_atoms(name);
    if matches!(atoms.first(), Some(NameAtom::Str(s)) if s == "_private")
        && let Some(num_pos) = atoms
            .iter()
            .enumerate()
            .skip(1)
            .find_map(|(idx, atom)| matches!(atom, NameAtom::Num(_)).then_some(idx))
    {
        let prefix = atoms[..=num_pos]
            .iter()
            .map(|a| match a {
                NameAtom::Str(s) => NameAtom::Str(s.clone()),
                NameAtom::Num(n) => NameAtom::Num(*n),
            })
            .collect();
        let rest = atoms[num_pos + 1..]
            .iter()
            .map(|a| match a {
                NameAtom::Str(s) => NameAtom::Str(s.clone()),
                NameAtom::Num(n) => NameAtom::Num(*n),
            })
            .collect();
        return (Some(prefix), rest);
    }
    (None, atoms)
}

/// `CtorElim.lean::asPrivateAs`: apply `owner`'s private prefix (if any) to `target`.
pub(super) fn as_private_as(target: &Name, owner: &Name) -> Name {
    let (_, target_user) = split_private_name(target);
    let (owner_prefix, _) = split_private_name(owner);
    match owner_prefix {
        Some(mut prefix) => {
            prefix.extend(target_user);
            build_name(&prefix)
        }
        None => build_name(&target_user),
    }
}

/// Iterative, DAG-memoized level-parameter substitution inside a `Level`.
fn subst_level_params(
    work: &mut Builder,
    level: &Level,
    params: &[Name],
    levels: &[Level],
) -> Result<Level, AuxiliaryError> {
    if params.len() != levels.len() {
        return Err(AuxiliaryError::InconsistentFamily);
    }
    if params.is_empty() || !level.has_param() {
        return Ok(level.clone());
    }
    let map: HashMap<&Name, &Level> = params.iter().zip(levels).collect();
    let mut done: HashMap<*const Level, Level> = HashMap::new();
    let mut pending = vec![(level, false)];
    while let Some((cur, exit)) = pending.pop() {
        work.tick()?;
        let id = std::ptr::from_ref(cur);
        if done.contains_key(&id) {
            continue;
        }
        if !cur.has_param() {
            done.insert(id, cur.clone());
            continue;
        }
        if !exit {
            pending.push((cur, true));
            match cur.view() {
                LevelView::Succ(inner) => pending.push((inner, false)),
                LevelView::Max(l, r) | LevelView::IMax(l, r) => {
                    pending.push((r, false));
                    pending.push((l, false));
                }
                _ => {}
            }
            continue;
        }
        let val = match cur.view() {
            LevelView::Param(n) => Ok(map.get(n).map_or_else(|| cur.clone(), |l| (*l).clone())),
            LevelView::Succ(inner) => done[&std::ptr::from_ref(inner)].clone().succ(),
            LevelView::Max(l, r) => Level::try_smart_max(
                done[&std::ptr::from_ref(l)].clone(),
                done[&std::ptr::from_ref(r)].clone(),
            ),
            LevelView::IMax(l, r) => Level::try_smart_imax(
                done[&std::ptr::from_ref(l)].clone(),
                done[&std::ptr::from_ref(r)].clone(),
            ),
            _ => Ok(cur.clone()),
        }
        .map_err(|_| AuxiliaryError::ResourceLimit)?;
        done.insert(id, val);
    }
    Ok(done[&std::ptr::from_ref(level)].clone())
}

/// Iterative, DAG-memoized level-parameter substitution inside an `Expr`.
pub(super) fn subst_expr_level_params(
    work: &mut Builder,
    expr: &Expr,
    params: &[Name],
    levels: &[Level],
) -> Result<Expr, AuxiliaryError> {
    if params.len() != levels.len() {
        return Err(AuxiliaryError::InconsistentFamily);
    }
    if params.is_empty() || !expr.has_level_param() {
        return Ok(expr.clone());
    }
    let mut done: HashMap<usize, Expr> = HashMap::new();
    let mut stack = vec![(expr, false)];
    while let Some((cur, exit)) = stack.pop() {
        work.tick()?;
        let id = cur.allocation_identity();
        if done.contains_key(&id) {
            continue;
        }
        if !cur.has_level_param() {
            done.insert(id, cur.clone());
            continue;
        }
        if !exit {
            stack.push((cur, true));
            match cur.node() {
                ExprNode::App { f, a } => {
                    stack.push((a, false));
                    stack.push((f, false));
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    stack.push((body, false));
                    stack.push((binder_type, false));
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    stack.push((body, false));
                    stack.push((value, false));
                    stack.push((type_, false));
                }
                ExprNode::MData { expr: inner, .. } | ExprNode::Proj { expr: inner, .. } => {
                    stack.push((inner, false));
                }
                _ => {}
            }
            continue;
        }
        let get = |e: &Expr| done[&e.allocation_identity()].clone();
        let rebuilt = match cur.node() {
            ExprNode::Sort { level } => {
                Expr::sort(subst_level_params(work, level, params, levels)?)
            }
            ExprNode::Const {
                name,
                levels: clevels,
            } => {
                let mut next = Vec::with_capacity(clevels.len());
                for lvl in clevels {
                    next.push(subst_level_params(work, lvl, params, levels)?);
                }
                Expr::const_(name.clone(), next)
            }
            ExprNode::App { f, a } => Expr::app(get(f), get(a)),
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::lam(
                binder_name.clone(),
                get(binder_type),
                get(body),
                *binder_info,
            ),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::forall_e(
                binder_name.clone(),
                get(binder_type),
                get(body),
                *binder_info,
            ),
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => Expr::let_e(
                decl_name.clone(),
                get(type_),
                get(value),
                get(body),
                *non_dep,
            ),
            ExprNode::MData { data, expr: inner } => Expr::mdata(data.clone(), get(inner)),
            ExprNode::Proj {
                struct_name,
                idx,
                expr: inner,
            } => Expr::proj(struct_name.clone(), *idx, get(inner)),
            _ => cur.clone(),
        };
        done.insert(id, rebuilt);
    }
    Ok(done[&expr.allocation_identity()].clone())
}

/// Bounded lightweight WHNF (beta, zeta, delta on definitions, mdata unwrap,
/// struct projection on constructor apps) sufficient to infer universe sort levels
/// of inductive minor-premise types directly from a constant lookup closure.
pub(super) fn whnf_for_sort<'a, F>(
    work: &mut Builder,
    mut expr: Expr,
    lookup_const: &F,
) -> Result<Expr, AuxiliaryError>
where
    F: Fn(&Name) -> Option<&'a ConstantInfo>,
{
    loop {
        work.tick()?;
        match expr.node() {
            ExprNode::MData { expr: inner, .. } => {
                expr = inner.clone();
            }
            ExprNode::LetE { value, body, .. } => {
                expr = body
                    .subst_loose(0, std::slice::from_ref(value))
                    .map_err(|_| AuxiliaryError::InvalidTelescope)?;
            }
            ExprNode::App { .. } | ExprNode::Const { .. } => {
                let mut head = expr.clone();
                let mut rev_args = Vec::new();
                while let ExprNode::App { f, a } = head.node() {
                    work.tick()?;
                    rev_args.push(a.clone());
                    head = f.clone();
                }
                rev_args.reverse();
                match head.node() {
                    ExprNode::MData { expr: inner, .. } => {
                        expr = app(inner.clone(), rev_args);
                    }
                    ExprNode::Lam { body, .. } if !rev_args.is_empty() => {
                        let reduced = body
                            .subst_loose(0, &rev_args[..1])
                            .map_err(|_| AuxiliaryError::InvalidTelescope)?;
                        expr = app(reduced, rev_args.into_iter().skip(1));
                    }
                    ExprNode::LetE { value, body, .. } => {
                        let reduced = body
                            .subst_loose(0, std::slice::from_ref(value))
                            .map_err(|_| AuxiliaryError::InvalidTelescope)?;
                        expr = app(reduced, rev_args);
                    }
                    ExprNode::Const { name, levels } => {
                        if let Some(ConstantInfo::Defn(def)) = lookup_const(name)
                            && def.base.level_params.len() == levels.len()
                        {
                            let body = subst_expr_level_params(
                                work,
                                &def.value,
                                &def.base.level_params,
                                levels,
                            )?;
                            expr = app(body, rev_args);
                            continue;
                        }
                        return Ok(expr);
                    }
                    _ => return Ok(expr),
                }
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr: inner,
            } => {
                let reduced = whnf_for_sort(work, inner.clone(), lookup_const)?;
                let mut head = reduced;
                let mut rev_args = Vec::new();
                while let ExprNode::App { f, a } = head.node() {
                    work.tick()?;
                    rev_args.push(a.clone());
                    head = f.clone();
                }
                rev_args.reverse();
                if let ExprNode::Const {
                    name: ctor_name, ..
                } = head.node()
                    && let Some(ConstantInfo::Ctor(ctor)) = lookup_const(ctor_name)
                    && &ctor.induct == struct_name
                {
                    let field_pos = (ctor.num_params as usize) + (*idx as usize);
                    if let Some(field_val) = rev_args.get(field_pos) {
                        expr = field_val.clone();
                        continue;
                    }
                }
                return Ok(expr);
            }
            _ => return Ok(expr),
        }
    }
}

/// Infer the type of `expr` under `locals` using `lookup_const`, sufficient for
/// computing `getLevel` on every `casesOn` minor premise type.
pub(super) fn infer_type_bounded<'a, F>(
    build: &mut Build,
    locals: &[LocalDecl],
    expr: &Expr,
    lookup_const: &F,
) -> Result<Expr, AuxiliaryError>
where
    F: Fn(&Name) -> Option<&'a ConstantInfo>,
{
    build.work.tick()?;
    match expr.node() {
        ExprNode::MData { expr: inner, .. } => {
            infer_type_bounded(build, locals, inner, lookup_const)
        }
        ExprNode::FVar { id } => locals
            .iter()
            .rev()
            .find(|decl| decl.id == *id)
            .map(|decl| decl.type_.clone())
            .ok_or(AuxiliaryError::InvalidTelescope),
        ExprNode::Sort { level } => {
            let next = level
                .clone()
                .succ()
                .map_err(|_| AuxiliaryError::ResourceLimit)?;
            Ok(Expr::sort(next))
        }
        ExprNode::Lit { literal } => match literal {
            Literal::Nat(_) => Ok(Expr::const_(Name::from_components(["Nat"]), Vec::new())),
            Literal::Str(_) => Ok(Expr::const_(Name::from_components(["String"]), Vec::new())),
        },
        ExprNode::Const { name, levels } => {
            let info = lookup_const(name).ok_or(AuxiliaryError::InconsistentFamily)?;
            let base = info.constant_val();
            if base.level_params.len() != levels.len() {
                return Err(AuxiliaryError::InconsistentFamily);
            }
            subst_expr_level_params(&mut build.work, &base.type_, &base.level_params, levels)
        }
        ExprNode::ForallE { .. } => {
            // Mirror `Lean.Meta.inferForallType` (`InferType.lean:176-183`):
            // open the entire leading forall telescope, fold `mkLevelIMax'`
            // right-to-left over domain levels, and call `Level::normalize` once.
            let mut next_locals = locals.to_vec();
            let mut dom_levels = Vec::new();
            let mut cursor = expr.clone();
            while let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = cursor.node()
            {
                let dom_level = infer_sort_level(build, &next_locals, binder_type, lookup_const)?;
                dom_levels.push(dom_level);
                let local = build.local(binder_name.clone(), binder_type.clone(), *binder_info)?;
                let opened = body
                    .subst_loose(0, &[fv(&local)])
                    .map_err(|_| AuxiliaryError::InvalidTelescope)?;
                next_locals.push(local);
                cursor = opened;
            }
            let mut result_level = infer_sort_level(build, &next_locals, &cursor, lookup_const)?;
            for dom_level in dom_levels.into_iter().rev() {
                result_level = Level::try_smart_imax(dom_level, result_level)
                    .map_err(|_| AuxiliaryError::ResourceLimit)?;
            }
            Ok(Expr::sort(result_level.normalize()))
        }
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let local = build.local(binder_name.clone(), binder_type.clone(), *binder_info)?;
            let opened = body
                .subst_loose(0, &[fv(&local)])
                .map_err(|_| AuxiliaryError::InvalidTelescope)?;
            let mut next_locals = locals.to_vec();
            next_locals.push(local.clone());
            let body_ty = infer_type_bounded(build, &next_locals, &opened, lookup_const)?;
            build.close(&[local], body_ty, false)
        }
        ExprNode::LetE { value, body, .. } => {
            let reduced = body
                .subst_loose(0, std::slice::from_ref(value))
                .map_err(|_| AuxiliaryError::InvalidTelescope)?;
            infer_type_bounded(build, locals, &reduced, lookup_const)
        }
        ExprNode::App { f, a } => {
            let f_ty = infer_type_bounded(build, locals, f, lookup_const)?;
            let f_ty_whnf = whnf_for_sort(&mut build.work, f_ty, lookup_const)?;
            let ExprNode::ForallE { body, .. } = f_ty_whnf.node() else {
                return Err(AuxiliaryError::InvalidTelescope);
            };
            body.subst_loose(0, std::slice::from_ref(a))
                .map_err(|_| AuxiliaryError::InvalidTelescope)
        }
        ExprNode::Proj {
            struct_name,
            idx,
            expr: inner,
        } => {
            let inner_ty = infer_type_bounded(build, locals, inner, lookup_const)?;
            let inner_ty_whnf = whnf_for_sort(&mut build.work, inner_ty, lookup_const)?;
            let mut head = inner_ty_whnf;
            let mut rev_args = Vec::new();
            while let ExprNode::App { f, a } = head.node() {
                build.work.tick()?;
                rev_args.push(a.clone());
                head = f.clone();
            }
            rev_args.reverse();
            let ExprNode::Const {
                name: head_name,
                levels,
            } = head.node()
            else {
                return Err(AuxiliaryError::InvalidTelescope);
            };
            if head_name != struct_name {
                return Err(AuxiliaryError::InvalidTelescope);
            }
            let Some(ConstantInfo::Induct(ind)) = lookup_const(struct_name) else {
                return Err(AuxiliaryError::InconsistentFamily);
            };
            let Some(ctor_name) = ind.ctors.first() else {
                return Err(AuxiliaryError::InconsistentFamily);
            };
            let Some(ConstantInfo::Ctor(ctor)) = lookup_const(ctor_name) else {
                return Err(AuxiliaryError::InconsistentFamily);
            };
            if ctor.base.level_params.len() != levels.len()
                || rev_args.len() < ctor.num_params as usize
            {
                return Err(AuxiliaryError::InconsistentFamily);
            }
            let mut cur = subst_expr_level_params(
                &mut build.work,
                &ctor.base.type_,
                &ctor.base.level_params,
                levels,
            )?;
            cur = instantiate_forall(&mut build.work, &cur, &rev_args[..ctor.num_params as usize])?;
            for field_i in 0..=(*idx as usize) {
                cur = whnf_for_sort(&mut build.work, cur, lookup_const)?;
                let ExprNode::ForallE {
                    binder_type, body, ..
                } = cur.node()
                else {
                    return Err(AuxiliaryError::InvalidTelescope);
                };
                if field_i == *idx as usize {
                    return Ok(binder_type.clone());
                }
                let proj_i = Expr::proj(struct_name.clone(), field_i as u64, inner.clone());
                cur = body
                    .subst_loose(0, &[proj_i])
                    .map_err(|_| AuxiliaryError::InvalidTelescope)?;
            }
            Err(AuxiliaryError::InvalidTelescope)
        }
        ExprNode::BVar { .. } | ExprNode::MVar { .. } => Err(AuxiliaryError::InvalidTelescope),
    }
}

pub(super) fn infer_sort_level<'a, F>(
    build: &mut Build,
    locals: &[LocalDecl],
    type_: &Expr,
    lookup_const: &F,
) -> Result<Level, AuxiliaryError>
where
    F: Fn(&Name) -> Option<&'a ConstantInfo>,
{
    let ty_of_ty = infer_type_bounded(build, locals, type_, lookup_const)?;
    let whnf = whnf_for_sort(&mut build.work, ty_of_ty, lookup_const)?;
    match whnf.node() {
        ExprNode::Sort { level } => Ok(level.clone()),
        _ => Err(AuxiliaryError::InvalidTelescope),
    }
}

/// Construct `<T>.ctorElimType`, `<T>.ctorElim`, and `<ctor_i>.elim` from the
/// admitted inductive family, its ordered constructors, its `casesOn`
/// definition, and a constant lookup closure (`CtorElim.lean::mkCtorElim`).
///
/// Returns `Ok(None)` when the pin's own guard skips generation:
/// - `num_ctors <= 1`
/// - Prop-former family
/// - `casesOn` does not eliminate into `Type` (no extra motive universe param)
pub fn ctor_elim_declarations<'a, F>(
    inductive: &InductiveVal,
    constructors: &[ConstructorVal],
    cases_on: &DefinitionVal,
    budget: RecordBudget,
    lookup_const: F,
) -> Result<Option<CtorElimCandidates>, AuxiliaryError>
where
    F: Fn(&Name) -> Option<&'a ConstantInfo>,
{
    let family = &inductive.base.name;
    let expected_cases_on = Name::str(family.clone(), "casesOn");
    if family.is_anonymous() || cases_on.base.name != expected_cases_on {
        return Err(AuxiliaryError::InconsistentFamily);
    }
    if constructors.len() != inductive.ctors.len() {
        return Err(AuxiliaryError::InconsistentFamily);
    }
    for (expected_name, ctor) in inductive.ctors.iter().zip(constructors) {
        if &ctor.base.name != expected_name
            || &ctor.induct != family
            || ctor.num_params != inductive.num_params
        {
            return Err(AuxiliaryError::InconsistentFamily);
        }
    }
    if constructors.len() <= 1 {
        return Ok(None);
    }
    if cases_on.base.level_params.len() <= inductive.base.level_params.len() {
        return Ok(None);
    }
    let expected_binders = (inductive.num_params as usize)
        .checked_add(1)
        .and_then(|n| n.checked_add(inductive.num_indices as usize))
        .and_then(|n| n.checked_add(1))
        .and_then(|n| n.checked_add(constructors.len()))
        .ok_or(AuxiliaryError::ResourceLimit)?;
    if expected_binders > budget.max_binders
        || cases_on.base.level_params.len() > budget.max_binders
    {
        return Err(AuxiliaryError::ResourceLimit);
    }

    let mut work = Builder {
        remaining: budget.max_nodes,
    };
    work.scan(&inductive.base.type_, &HashSet::new(), &Name::anonymous())?;
    work.scan(&cases_on.base.type_, &HashSet::new(), &Name::anonymous())?;
    for ctor in constructors {
        work.scan(&ctor.base.type_, &HashSet::new(), &Name::anonymous())?;
    }

    if is_prop_former(&mut work, &inductive.base.type_)? {
        return Ok(None);
    }

    let mut build = Build {
        work,
        remaining_binders: budget.max_binders,
        next: 0,
    };

    let (xs, _) = bounded_telescope(&mut build, &cases_on.base.type_, expected_binders)?;
    let num_params = inductive.num_params as usize;
    let num_indices = inductive.num_indices as usize;
    let params = &xs[..num_params];
    let motive = &xs[num_params];
    let indices = &xs[num_params + 1..num_params + 1 + num_indices];
    let major_arg = &xs[num_params + 1 + num_indices];
    let alts = &xs[num_params + 1 + num_indices + 1..];

    let v_and_us: Vec<Level> = cases_on
        .base
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let us: Vec<Level> = v_and_us[1..].to_vec();

    let mut param_motive_locals = Vec::with_capacity(num_params + 1);
    param_motive_locals.extend_from_slice(params);
    param_motive_locals.push(motive.clone());

    let mut alt_levels = Vec::with_capacity(alts.len());
    for alt in alts {
        let lvl = infer_sort_level(&mut build, &param_motive_locals, &alt.type_, &lookup_const)?;
        alt_levels.push(lvl);
    }
    let u = max_levels(&mut build.work, &alt_levels)?;
    let u_prime = reassoc_max(
        &mut build.work,
        Level::try_smart_max(u.clone(), Level::one())
            .map_err(|_| AuxiliaryError::ResourceLimit)?
            .normalize(),
    )?;
    let u_prime_succ = u_prime
        .clone()
        .succ()
        .map_err(|_| AuxiliaryError::ResourceLimit)?;

    let nat_type = Expr::const_(Name::from_components(["Nat"]), Vec::new());
    let eq_const = Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]);
    let ctor_idx_name = Name::str(family.clone(), "ctorIdx");
    let ctor_elim_type_name = Name::str(family.clone(), "ctorElimType");
    let ctor_elim_name = Name::str(family.clone(), "ctorElim");
    let const_meta = |n: &Name| lookup_const(n).map(CtorIdxConstMeta::from_constant);

    let mut ism = Vec::with_capacity(num_indices + 1);
    ism.extend_from_slice(indices);
    ism.push(major_arg.clone());
    let param_fvars: Vec<Expr> = params.iter().map(fv).collect();
    let ism_fvars: Vec<Expr> = ism.iter().map(fv).collect();
    let motive_ism = app(fv(motive), ism_fvars.iter().cloned());

    // 1. `<T>.ctorElimType`
    let ctor_idx_var_ty = build.local(
        Name::from_components(["ctorIdx"]),
        nat_type.clone(),
        BinderInfo::Default,
    )?;
    let lifted_alts: Vec<Expr> = alts
        .iter()
        .zip(&alt_levels)
        .map(|(alt, s_i)| {
            app(
                Expr::const_(
                    Name::from_components(["PULift"]),
                    vec![u.clone(), s_i.clone()],
                ),
                [alt.type_.clone()],
            )
        })
        .collect();
    let lookup_body = mk_nat_lookup_table(
        &mut build.work,
        &fv(&ctor_idx_var_ty),
        &Expr::sort(u_prime.clone()),
        &u_prime_succ,
        &lifted_alts,
    )?;
    let mut cet_locals = param_motive_locals.clone();
    cet_locals.push(ctor_idx_var_ty);
    let cet_value = build.close(&cet_locals, lookup_body, true)?;
    let cet_type = build.close(&cet_locals, Expr::sort(u_prime.clone()), false)?;
    let (_, cet_unsafe) = scan_const_meta(&mut build.work, &[&cet_type, &cet_value], &const_meta)?;
    let cet_safety = if inductive.is_unsafe || cet_unsafe {
        DefinitionSafety::Unsafe
    } else {
        DefinitionSafety::Safe
    };
    let ctor_elim_type = DefinitionVal {
        base: ConstantVal {
            name: ctor_elim_type_name.clone(),
            level_params: cases_on.base.level_params.clone(),
            type_: cet_type,
        },
        value: cet_value,
        hints: ReducibilityHints::Abbrev,
        safety: cet_safety,
        all: vec![ctor_elim_type_name.clone()],
    };

    // 2. `<T>.ctorElim`
    let ctor_idx_var = build.local(
        Name::from_components(["ctorIdx"]),
        nat_type.clone(),
        BinderInfo::Default,
    )?;
    let k_type_f = app(
        Expr::const_(ctor_elim_type_name, v_and_us.clone()),
        param_fvars
            .iter()
            .cloned()
            .chain(std::iter::once(fv(motive))),
    );
    let k_type = app(k_type_f.clone(), [fv(&ctor_idx_var)]);
    let ctor_app = app(
        Expr::const_(ctor_idx_name, us),
        param_fvars.iter().cloned().chain(ism_fvars.iter().cloned()),
    );
    let h_type_elim = app(
        eq_const.clone(),
        [nat_type.clone(), fv(&ctor_idx_var), ctor_app.clone()],
    );
    let h_elim_local = build.local(
        Name::from_components(["h"]),
        h_type_elim.clone(),
        BinderInfo::Default,
    )?;
    let k_local = build.local(Name::from_components(["k"]), k_type, BinderInfo::Default)?;

    let motive_prime_arrow = Expr::forall_e(
        Name::from_components(["h"]),
        h_type_elim,
        motive_ism.clone(),
        BinderInfo::Default,
    );
    let motive_prime = build.close(&ism, motive_prime_arrow, true)?;

    let mut cases_args = Vec::with_capacity(num_params + 1 + ism.len() + constructors.len());
    cases_args.extend(param_fvars.iter().cloned());
    cases_args.push(motive_prime);
    cases_args.extend(ism_fvars.iter().cloned());

    for (i, ctor) in constructors.iter().enumerate() {
        let ctor_type = instantiate_forall(&mut build.work, &ctor.base.type_, &param_fvars)?;
        let (zs, _) = bounded_telescope(&mut build, &ctor_type, ctor.num_fields as usize)?;
        let nat_i = Expr::lit(Literal::Nat(NatLit::from_u64(i as u64)));
        let heq = app(
            eq_const.clone(),
            [nat_type.clone(), fv(&ctor_idx_var), nat_i.clone()],
        );
        let h_alt = build.local(Name::from_components(["h"]), heq, BinderInfo::Default)?;
        let eq_ndrec = app(
            Expr::const_(
                Name::from_components(["Eq", "ndrec"]),
                vec![u_prime.clone(), Level::one()],
            ),
            [
                nat_type.clone(),
                fv(&ctor_idx_var),
                k_type_f.clone(),
                fv(&k_local),
                nat_i,
                fv(&h_alt),
            ],
        );
        let pulift_down = app(
            Expr::const_(
                Name::from_components(["PULift", "down"]),
                vec![u.clone(), alt_levels[i].clone()],
            ),
            [alts[i].type_.clone(), eq_ndrec],
        );
        let alt_body = app(pulift_down, zs.iter().map(fv));
        let mut alt_binders = zs;
        alt_binders.push(h_alt);
        cases_args.push(build.close(&alt_binders, alt_body, true)?);
    }

    let cases_app = app(
        Expr::const_(expected_cases_on, v_and_us.clone()),
        cases_args,
    );
    let elim_body = app(cases_app, [fv(&h_elim_local)]);
    let mut elim_locals = Vec::with_capacity(num_params + 4 + ism.len());
    elim_locals.extend_from_slice(params);
    elim_locals.push(motive.clone());
    elim_locals.push(ctor_idx_var);
    elim_locals.extend(ism.iter().cloned());
    elim_locals.push(h_elim_local);
    elim_locals.push(k_local);

    let ce_value = build.close(&elim_locals, elim_body, true)?;
    let ce_type = build.close(&elim_locals, motive_ism.clone(), false)?;
    let (_, ce_unsafe) = scan_const_meta(&mut build.work, &[&ce_type, &ce_value], &const_meta)?;
    let ce_safety = if inductive.is_unsafe || ce_unsafe {
        DefinitionSafety::Unsafe
    } else {
        DefinitionSafety::Safe
    };
    let ctor_elim = DefinitionVal {
        base: ConstantVal {
            name: ctor_elim_name.clone(),
            level_params: cases_on.base.level_params.clone(),
            type_: ce_type,
        },
        value: ce_value,
        hints: ReducibilityHints::Abbrev,
        safety: ce_safety,
        all: vec![ctor_elim_name.clone()],
    };

    // 3. Per-constructor `<ctor_i>.elim`
    let mut constructor_elims = Vec::with_capacity(constructors.len());
    for (i, ctor) in constructors.iter().enumerate() {
        let decl_name = as_private_as(&Name::str(ctor.base.name.clone(), "elim"), family);
        let nat_i = Expr::lit(Literal::Nat(NatLit::from_u64(i as u64)));
        let h_type_c = app(
            eq_const.clone(),
            [nat_type.clone(), ctor_app.clone(), nat_i.clone()],
        );
        let h_c = build.local(Name::from_components(["h"]), h_type_c, BinderInfo::Default)?;
        let alt_local = alts[i].clone();

        let symm = app(
            Expr::const_(Name::from_components(["Eq", "symm"]), vec![Level::one()]),
            [nat_type.clone(), ctor_app.clone(), nat_i.clone(), fv(&h_c)],
        );
        let up = app(
            Expr::const_(
                Name::from_components(["PULift", "up"]),
                vec![u.clone(), alt_levels[i].clone()],
            ),
            [alt_local.type_.clone(), fv(&alt_local)],
        );
        let mut call_args = Vec::with_capacity(num_params + 4 + ism.len());
        call_args.extend(param_fvars.iter().cloned());
        call_args.push(fv(motive));
        call_args.push(nat_i);
        call_args.extend(ism_fvars.iter().cloned());
        call_args.push(symm);
        call_args.push(up);
        let c_body = app(
            Expr::const_(ctor_elim_name.clone(), v_and_us.clone()),
            call_args,
        );

        let mut c_locals = Vec::with_capacity(num_params + 3 + ism.len());
        c_locals.extend_from_slice(params);
        c_locals.push(motive.clone());
        c_locals.extend(ism.iter().cloned());
        c_locals.push(h_c);
        c_locals.push(alt_local);

        let c_value = build.close(&c_locals, c_body, true)?;
        let c_type = build.close(&c_locals, motive_ism.clone(), false)?;
        let (_, c_unsafe) = scan_const_meta(&mut build.work, &[&c_type, &c_value], &const_meta)?;
        let c_safety = if inductive.is_unsafe || c_unsafe {
            DefinitionSafety::Unsafe
        } else {
            DefinitionSafety::Safe
        };
        constructor_elims.push(DefinitionVal {
            base: ConstantVal {
                name: decl_name.clone(),
                level_params: cases_on.base.level_params.clone(),
                type_: c_type,
            },
            value: c_value,
            hints: ReducibilityHints::Abbrev,
            safety: c_safety,
            all: vec![decl_name],
        });
    }

    Ok(Some(CtorElimCandidates {
        ctor_elim_type,
        ctor_elim,
        constructor_elims,
    }))
}
