//! Native `noConfusionType` and `noConfusion` candidates
//! (fln-derived-declaration-frontier-cj7s).
//!
//! Algorithm: the pin's `Lean/Meta/Constructions/NoConfusion.lean`
//! (`mkNoConfusion`, `mkNoConfusionEnum`, `mkNoConfusionCore`,
//! `mkNoConfusionType`, `mkNoConfusionCoreImp`, `mkNoConfusionCtorArg`,
//! `mkEqNDRecTelescope`).
//!
//! Candidate generation confers no admission or attribute authority: every
//! produced definition must pass both checking seats through the caller's
//! ordinary admission path.

use super::ctor_elim::{
    as_private_as, infer_sort_level, infer_type_bounded, subst_expr_level_params, whnf_for_sort,
};
use super::ctor_idx::{
    CtorIdxConstMeta, bounded_telescope, instantiate_forall, is_enum_type, is_prop_former,
    scan_const_meta,
};
use super::*;
use fln_core::expr::{Literal, NatLit};
use fln_env::constants::{ConstantInfo, ConstructorVal};
use std::collections::{HashMap, HashSet};

/// Generated `<T>.noConfusionType` and `<T>.noConfusion` definitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoConfusionCandidates {
    pub no_confusion_type: DefinitionVal,
    pub no_confusion: DefinitionVal,
    /// `true` when constructed via `mkNoConfusionEnum` (whose first universe
    /// parameter is a fresh hygienic `v` in Lean 4).
    pub is_enum_construction: bool,
}

fn fresh_enum_universe(existing: &[Name]) -> Name {
    let base = Name::from_components(["v"]);
    if !existing.contains(&base) {
        return base;
    }
    for idx in 1u64.. {
        let cand = Name::str(Name::anonymous(), format!("v_{idx}"));
        if !existing.contains(&cand) {
            return cand;
        }
    }
    unreachable!()
}

/// Structural alpha-equality on `Expr` (ignoring binder names).
fn expr_alpha_eq(work: &mut Builder, left: &Expr, right: &Expr) -> Result<bool, AuxiliaryError> {
    let mut stack = vec![(left, right)];
    let mut seen = HashSet::new();
    while let Some((a, b)) = stack.pop() {
        work.tick()?;
        if a == b {
            continue;
        }
        if !seen.insert((a.allocation_identity(), b.allocation_identity())) {
            continue;
        }
        match (a.node(), b.node()) {
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                stack.push((aa, ba));
                stack.push((af, bf));
            }
            (
                ExprNode::Lam {
                    binder_type: at,
                    body: ab,
                    binder_info: ai,
                    ..
                },
                ExprNode::Lam {
                    binder_type: bt,
                    body: bb,
                    binder_info: bi,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: at,
                    body: ab,
                    binder_info: ai,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: bt,
                    body: bb,
                    binder_info: bi,
                    ..
                },
            ) => {
                if ai != bi {
                    return Ok(false);
                }
                stack.push((ab, bb));
                stack.push((at, bt));
            }
            (
                ExprNode::LetE {
                    type_: at,
                    value: av,
                    body: ab,
                    non_dep: an,
                    ..
                },
                ExprNode::LetE {
                    type_: bt,
                    value: bv,
                    body: bb,
                    non_dep: bn,
                    ..
                },
            ) => {
                if an != bn {
                    return Ok(false);
                }
                stack.push((ab, bb));
                stack.push((av, bv));
                stack.push((at, bt));
            }
            (
                ExprNode::Proj {
                    struct_name: at,
                    idx: ai,
                    expr: ae,
                },
                ExprNode::Proj {
                    struct_name: bt,
                    idx: bi,
                    expr: be,
                },
            ) => {
                if at != bt || ai != bi {
                    return Ok(false);
                }
                stack.push((ae, be));
            }
            (ExprNode::MData { expr: ae, .. }, _) => {
                stack.push((ae, b));
            }
            (_, ExprNode::MData { expr: be, .. }) => {
                stack.push((a, be));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// Bounded definitional equality sufficient to decide `Eq` vs `HEq` between
/// abstract constructor field types in `mkNoConfusionCtorArg` and
/// `withEqTelescope`.
fn is_def_eq_types<'a, F>(
    build: &mut Build,
    left: &Expr,
    right: &Expr,
    lookup_const: &F,
) -> Result<bool, AuxiliaryError>
where
    F: Fn(&Name) -> Option<&'a ConstantInfo>,
{
    build.work.tick()?;
    if expr_alpha_eq(&mut build.work, left, right)? {
        return Ok(true);
    }
    let a = whnf_for_sort(&mut build.work, left.clone(), lookup_const)?;
    let b = whnf_for_sort(&mut build.work, right.clone(), lookup_const)?;
    if expr_alpha_eq(&mut build.work, &a, &b)? {
        return Ok(true);
    }
    match (a.node(), b.node()) {
        (ExprNode::Sort { level: l1 }, ExprNode::Sort { level: l2 }) => {
            Ok(l1.normalize() == l2.normalize())
        }
        (
            ExprNode::Const {
                name: n1,
                levels: ls1,
            },
            ExprNode::Const {
                name: n2,
                levels: ls2,
            },
        ) => Ok(n1 == n2
            && ls1.len() == ls2.len()
            && ls1
                .iter()
                .zip(ls2)
                .all(|(x, y)| x.normalize() == y.normalize())),
        (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
            Ok(is_def_eq_types(build, af, bf, lookup_const)?
                && is_def_eq_types(build, aa, ba, lookup_const)?)
        }
        (
            ExprNode::ForallE {
                binder_name,
                binder_type: at,
                body: ab,
                binder_info: ai,
            },
            ExprNode::ForallE {
                binder_type: bt,
                body: bb,
                ..
            },
        )
        | (
            ExprNode::Lam {
                binder_name,
                binder_type: at,
                body: ab,
                binder_info: ai,
            },
            ExprNode::Lam {
                binder_type: bt,
                body: bb,
                ..
            },
        ) => {
            if !is_def_eq_types(build, at, bt, lookup_const)? {
                return Ok(false);
            }
            let local = build.local(binder_name.clone(), at.clone(), *ai)?;
            let var = fv(&local);
            let ab_open = ab
                .subst_loose(0, std::slice::from_ref(&var))
                .map_err(|_| AuxiliaryError::InvalidTelescope)?;
            let bb_open = bb
                .subst_loose(0, std::slice::from_ref(&var))
                .map_err(|_| AuxiliaryError::InvalidTelescope)?;
            is_def_eq_types(build, &ab_open, &bb_open, lookup_const)
        }
        (
            ExprNode::Proj {
                struct_name: s1,
                idx: i1,
                expr: e1,
            },
            ExprNode::Proj {
                struct_name: s2,
                idx: i2,
                expr: e2,
            },
        ) => Ok(s1 == s2 && i1 == i2 && is_def_eq_types(build, e1, e2, lookup_const)?),
        _ => Ok(false),
    }
}

/// Open every leading `ForallE` (without delta-unfolding).
fn forall_telescope_plain(
    build: &mut Build,
    type_: &Expr,
) -> Result<(Vec<LocalDecl>, Expr), AuxiliaryError> {
    let mut current = type_.clone();
    let mut locals = Vec::new();
    loop {
        build.work.tick()?;
        match current.node() {
            ExprNode::MData { expr, .. } => current = expr.clone(),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let local = build.local(binder_name.clone(), binder_type.clone(), *binder_info)?;
                current = body
                    .subst_loose(0, &[fv(&local)])
                    .map_err(|_| AuxiliaryError::InvalidTelescope)?;
                locals.push(local);
            }
            _ => return Ok((locals, current)),
        }
    }
}

/// Open every leading `ForallE` reducing through WHNF (`forallTelescopeReducing`).
fn forall_telescope_reducing<'a, F>(
    build: &mut Build,
    type_: &Expr,
    lookup_const: &F,
) -> Result<(Vec<LocalDecl>, Expr), AuxiliaryError>
where
    F: Fn(&Name) -> Option<&'a ConstantInfo>,
{
    let mut current = type_.clone();
    let mut locals = Vec::new();
    loop {
        build.work.tick()?;
        let reduced = whnf_for_sort(&mut build.work, current.clone(), lookup_const)?;
        match reduced.node() {
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let local = build.local(binder_name.clone(), binder_type.clone(), *binder_info)?;
                current = body
                    .subst_loose(0, &[fv(&local)])
                    .map_err(|_| AuxiliaryError::InvalidTelescope)?;
                locals.push(local);
            }
            _ => return Ok((locals, current)),
        }
    }
}

/// Extract `count` consecutive `ForallE` domains (`arrowDomainsN`).
fn arrow_domains_n(
    work: &mut Builder,
    count: usize,
    type_: &Expr,
) -> Result<Vec<Expr>, AuxiliaryError> {
    let mut current = type_;
    let mut domains = Vec::with_capacity(count);
    for _ in 0..count {
        loop {
            work.tick()?;
            match current.node() {
                ExprNode::MData { expr, .. } => current = expr,
                ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    domains.push(binder_type.clone());
                    current = body;
                    break;
                }
                _ => return Err(AuxiliaryError::InvalidTelescope),
            }
        }
    }
    Ok(domains)
}

/// Substitute a map of FVars inside an `Expr` (DAG-memoized, iterative).
fn subst_fvars(
    work: &mut Builder,
    expr: &Expr,
    replacements: &HashMap<FVarId, Expr>,
) -> Result<Expr, AuxiliaryError> {
    if replacements.is_empty() || !expr.has_fvar() {
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
        if !cur.has_fvar() {
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
            ExprNode::FVar { id: fvar } => replacements
                .get(fvar)
                .cloned()
                .unwrap_or_else(|| cur.clone()),
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

fn contains_any_fvar(
    work: &mut Builder,
    expr: &Expr,
    targets: &HashSet<FVarId>,
) -> Result<bool, AuxiliaryError> {
    if targets.is_empty() || !expr.has_fvar() {
        return Ok(false);
    }
    let mut stack = vec![expr];
    let mut seen = HashSet::new();
    while let Some(cur) = stack.pop() {
        work.tick()?;
        if !cur.has_fvar() || !seen.insert(cur.allocation_identity()) {
            continue;
        }
        match cur.node() {
            ExprNode::FVar { id } => {
                if targets.contains(id) {
                    return Ok(true);
                }
            }
            ExprNode::App { f, a } => {
                stack.push(a);
                stack.push(f);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(body);
                stack.push(binder_type);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(body);
                stack.push(value);
                stack.push(type_);
            }
            ExprNode::MData { expr: inner, .. } | ExprNode::Proj { expr: inner, .. } => {
                stack.push(inner);
            }
            _ => {}
        }
    }
    Ok(false)
}

/// Build `Eq` or `HEq` between `lhs` and `rhs` (`Lean.Meta.mkEqHEq`).
/// Returns `(eq_expr, is_heq)`.
fn mk_eq_heq<'a, F>(
    build: &mut Build,
    locals: &[LocalDecl],
    lhs: &Expr,
    rhs: &Expr,
    lookup_const: &F,
) -> Result<(Expr, bool), AuxiliaryError>
where
    F: Fn(&Name) -> Option<&'a ConstantInfo>,
{
    let ty1 = infer_type_bounded(build, locals, lhs, lookup_const)?;
    let ty2 = infer_type_bounded(build, locals, rhs, lookup_const)?;
    let u1 = infer_sort_level(build, locals, &ty1, lookup_const)?;
    if is_def_eq_types(build, &ty1, &ty2, lookup_const)? {
        let eq = app(
            Expr::const_(Name::from_components(["Eq"]), vec![u1]),
            [ty1, lhs.clone(), rhs.clone()],
        );
        Ok((eq, false))
    } else {
        let heq = app(
            Expr::const_(Name::from_components(["HEq"]), vec![u1]),
            [ty1, lhs.clone(), ty2, rhs.clone()],
        );
        Ok((heq, true))
    }
}

/// The field equalities of `mkNoConfusionCtorArg`, before applying either
/// constructor telescope. Both generated declarations reuse these same
/// abstract equality decisions. In particular, identifying the two concrete
/// parameter lists later must not turn an abstract `HEq` into an `Eq`.
struct CtorEqualityTemplate {
    parameters: [Vec<LocalDecl>; 2],
    fields: [Vec<LocalDecl>; 2],
    equalities: Vec<(Name, Expr)>,
}

impl CtorEqualityTemplate {
    fn instantiate(
        &self,
        work: &mut Builder,
        p_expr: &Expr,
        xs1: &[LocalDecl],
        zs1: &[LocalDecl],
        xs2: &[LocalDecl],
        zs2: &[LocalDecl],
    ) -> Result<Expr, AuxiliaryError> {
        let groups = [
            (self.parameters[0].as_slice(), xs1),
            (self.fields[0].as_slice(), zs1),
            (self.parameters[1].as_slice(), xs2),
            (self.fields[1].as_slice(), zs2),
        ];
        let mut replacements = HashMap::new();
        for (abstract_locals, concrete_locals) in groups {
            if abstract_locals.len() != concrete_locals.len() {
                return Err(AuxiliaryError::InvalidTelescope);
            }
            // Proof fields remain in this map even though they introduce no
            // equality: later dependent field types may still refer to them.
            for (abstract_local, concrete_local) in abstract_locals.iter().zip(concrete_locals) {
                work.tick()?;
                replacements.insert(abstract_local.id.clone(), fv(concrete_local));
            }
        }
        let mut result = p_expr.clone();
        for (name, domain) in self.equalities.iter().rev() {
            work.tick()?;
            result = Expr::forall_e(name.clone(), domain.clone(), result, BinderInfo::Default);
        }
        subst_fvars(work, &result, &replacements)
    }
}

/// Open the two abstract constructor telescopes once per constructor, instead
/// of repeating this work for `noConfusionType` and `noConfusion`. Equality
/// domains depend on these checked constructor types and universe arguments,
/// not on the eventual concrete fields or the return proposition `P`.
fn ctor_equality_template<'a, F>(
    build: &mut Build,
    ctor: &ConstructorVal,
    us: &[Level],
    lookup_const: &F,
) -> Result<CtorEqualityTemplate, AuxiliaryError>
where
    F: Fn(&Name) -> Option<&'a ConstantInfo>,
{
    let ctor_ty = subst_expr_level_params(
        &mut build.work,
        &ctor.base.type_,
        &ctor.base.level_params,
        us,
    )?;
    let (xs1_abs, t1) = bounded_telescope(build, &ctor_ty, ctor.num_params as usize)?;
    let (fields1_abs, _) = forall_telescope_reducing(build, &t1, lookup_const)?;
    let (xs2_abs, t2) = bounded_telescope(build, &ctor_ty, ctor.num_params as usize)?;
    let (fields2_abs, _) = forall_telescope_reducing(build, &t2, lookup_const)?;

    let mut abs_locals = Vec::new();
    abs_locals.extend(xs1_abs.iter().cloned());
    abs_locals.extend(fields1_abs.iter().cloned());
    abs_locals.extend(xs2_abs.iter().cloned());
    abs_locals.extend(fields2_abs.iter().cloned());

    let mut equalities = Vec::new();
    for (f1, f2) in fields1_abs.iter().rev().zip(fields2_abs.iter().rev()) {
        build.work.tick()?;
        let field_sort = infer_sort_level(build, &abs_locals, &f1.type_, lookup_const)?;
        if field_sort.normalize().is_zero() {
            continue;
        }
        let (eq_ty, _) = mk_eq_heq(build, &abs_locals, &fv(f1), &fv(f2), lookup_const)?;
        let eq_name = Name::str(
            Name::anonymous(),
            format!("{}_eq", f1.user_name.to_display_string()),
        );
        equalities.push((eq_name, eq_ty));
    }
    equalities.reverse();
    Ok(CtorEqualityTemplate {
        parameters: [xs1_abs, xs2_abs],
        fields: [fields1_abs, fields2_abs],
        equalities,
    })
}

/// Build the constant motive `fun ys => p_type` matching `motive_binder_domain`.
fn build_const_motive<'a, F>(
    build: &mut Build,
    t: &Expr,
    p_type: &Expr,
    lookup_const: &F,
) -> Result<(Expr, Expr), AuxiliaryError>
where
    F: Fn(&Name) -> Option<&'a ConstantInfo>,
{
    let t_whnf = whnf_for_sort(&mut build.work, t.clone(), lookup_const)?;
    let ExprNode::ForallE { binder_type, .. } = t_whnf.node() else {
        return Err(AuxiliaryError::InvalidTelescope);
    };
    let (ys, _) = forall_telescope_plain(build, binder_type)?;
    let motive = build.close(&ys, p_type.clone(), true)?;
    let instantiated = instantiate_forall(&mut build.work, t, std::slice::from_ref(&motive))?;
    Ok((motive, instantiated))
}

fn decompose_eq_or_heq(expr: &Expr) -> Option<(&'static str, Vec<Level>, Vec<Expr>)> {
    let mut head = expr;
    let mut args = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        head = f;
    }
    args.reverse();
    let ExprNode::Const { name, levels } = head.node() else {
        return None;
    };
    if *name == Name::from_components(["Eq"]) && args.len() == 3 && levels.len() == 1 {
        Some(("Eq", levels.clone(), args))
    } else if *name == Name::from_components(["HEq"]) && args.len() == 4 && levels.len() == 1 {
        Some(("HEq", levels.clone(), args))
    } else {
        None
    }
}

#[derive(Clone)]
enum ActiveLocal {
    Y(usize, LocalDecl),
    Eq(usize, LocalDecl, bool),
}

impl ActiveLocal {
    fn decl(&self) -> &LocalDecl {
        match self {
            Self::Y(_, d) | Self::Eq(_, d, _) => d,
        }
    }

    fn with_decl(&self, decl: LocalDecl) -> Self {
        match self {
            Self::Y(i, _) => Self::Y(*i, decl),
            Self::Eq(i, _, is_heq) => Self::Eq(*i, decl, *is_heq),
        }
    }
}

/// Pure, tactic-free implementation of `NoConfusion.lean::mkEqNDRecTelescope`,
/// matching `Meta.substEq`'s exact local-context reversion and re-introduction
/// order (`mvarId.revert` + `clear` + `introNP`).
#[allow(clippy::too_many_arguments)]
fn mk_eq_ndrec_step<'a, F>(
    build: &mut Build,
    base_locals: &[LocalDecl],
    xs1: &[LocalDecl],
    active_lctx: &[ActiveLocal],
    cur_target: &Expr,
    base_proof: &Expr,
    idx: usize,
    lookup_const: &F,
) -> Result<Expr, AuxiliaryError>
where
    F: Fn(&Name) -> Option<&'a ConstantInfo>,
{
    build.work.tick()?;
    if idx >= xs1.len() {
        return Ok(base_proof.clone());
    }
    let x = &xs1[idx];
    let y = active_lctx
        .iter()
        .find_map(|slot| match slot {
            ActiveLocal::Y(i, d) if *i == idx => Some(d.clone()),
            _ => None,
        })
        .ok_or(AuxiliaryError::InvalidTelescope)?;
    let (eq_var, is_heq) = active_lctx
        .iter()
        .find_map(|slot| match slot {
            ActiveLocal::Eq(i, d, h) if *i == idx => Some((d.clone(), *h)),
            _ => None,
        })
        .ok_or(AuxiliaryError::InvalidTelescope)?;

    // Collect every remaining local whose type transitively mentions `y.id`,
    // preserving exact current local-context order (mirroring `mvarId.revert`).
    let mut dep_ids = HashSet::new();
    dep_ids.insert(y.id.clone());

    let mut stay_slots = Vec::with_capacity(active_lctx.len());
    let mut dep_slots = Vec::new();
    for slot in active_lctx {
        match slot {
            ActiveLocal::Y(i, _) | ActiveLocal::Eq(i, _, _) if *i == idx => continue,
            _ => {}
        }
        if contains_any_fvar(&mut build.work, &slot.decl().type_, &dep_ids)? {
            dep_ids.insert(slot.decl().id.clone());
            dep_slots.push(slot.clone());
        } else {
            stay_slots.push(slot.clone());
        }
    }

    let dep_vars: Vec<LocalDecl> = dep_slots.iter().map(|s| s.decl().clone()).collect();

    // Build `motive_i = fun {y : T_i} => ∀ dep_vars, cur_target`.
    let reverted_type = build.close(&dep_vars, cur_target.clone(), false)?;
    let motive_i = build.close(std::slice::from_ref(&y), reverted_type.clone(), true)?;

    // Compute universe levels for `Eq.ndrec.{motive_level, t_i_level}`.
    let mut locals_for_step = base_locals.to_vec();
    locals_for_step.extend(active_lctx.iter().map(|s| s.decl().clone()));
    let motive_level = infer_sort_level(build, &locals_for_step, &reverted_type, lookup_const)?;
    let t_i = &x.type_;
    let t_i_level = infer_sort_level(build, &locals_for_step, t_i, lookup_const)?;

    // Substitute `y := x` and allocate fresh locals for reverted `dep_vars` in
    // the inner `Eq.ndrec` minor premise `body_i`, appending them at the end
    // of the local context (mirroring `mvarId.introNP`).
    let mut repl = HashMap::new();
    repl.insert(y.id.clone(), fv(x));

    let mut dep_vars_sub = Vec::with_capacity(dep_slots.len());
    let mut dep_slots_sub = Vec::with_capacity(dep_slots.len());
    for slot in &dep_slots {
        let decl = slot.decl();
        let sub_ty = subst_fvars(&mut build.work, &decl.type_, &repl)?;
        let fresh = build.local(decl.user_name.clone(), sub_ty, decl.binder_info)?;
        repl.insert(decl.id.clone(), fv(&fresh));
        dep_vars_sub.push(fresh.clone());
        dep_slots_sub.push(slot.with_decl(fresh));
    }
    let next_target = subst_fvars(&mut build.work, cur_target, &repl)?;

    let mut next_lctx = stay_slots;
    next_lctx.extend(dep_slots_sub);

    let inner = mk_eq_ndrec_step(
        build,
        base_locals,
        xs1,
        &next_lctx,
        &next_target,
        base_proof,
        idx + 1,
        lookup_const,
    )?;
    let body_i = build.close(&dep_vars_sub, inner, true)?;

    let eq_proof = if is_heq {
        app(
            Expr::const_(
                Name::from_components(["eq_of_heq"]),
                vec![t_i_level.clone()],
            ),
            [t_i.clone(), fv(x), fv(&y), fv(&eq_var)],
        )
    } else {
        fv(&eq_var)
    };
    let mut step = app(
        Expr::const_(
            Name::from_components(["Eq", "ndrec"]),
            vec![motive_level, t_i_level],
        ),
        [t_i.clone(), fv(x), motive_i, body_i, fv(&y), eq_proof],
    );
    for dep in &dep_vars {
        step = Expr::app(step, fv(dep));
    }
    Ok(step)
}

/// Construct `<T>.noConfusionType` and `<T>.noConfusion` for an inductive type
/// (`Lean/Meta/Constructions/NoConfusion.lean::mkNoConfusion`).
///
/// `use_enum_helper` mirrors `(← getEnv).contains ``noConfusionEnum` at the
/// point `T` was declared: when `true` and `T` is an enumeration type, uses
/// `mkNoConfusionEnum`; otherwise uses `mkNoConfusionCore`.
///
/// Returns `Ok(None)` when the pin's own guard skips generation (Prop-former
/// families or families whose `casesOn` does not eliminate into `Type`).
pub fn no_confusion_declarations<'a, F>(
    inductive: &InductiveVal,
    constructors: &[ConstructorVal],
    cases_on: &DefinitionVal,
    use_enum_helper: bool,
    budget: RecordBudget,
    lookup_const: F,
) -> Result<Option<NoConfusionCandidates>, AuxiliaryError>
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

    let mut work = Builder {
        remaining: budget.max_nodes,
    };
    work.scan(&inductive.base.type_, &HashSet::new(), &Name::anonymous())?;
    work.scan(&cases_on.base.type_, &HashSet::new(), &Name::anonymous())?;
    for ctor in constructors {
        work.scan(&ctor.base.type_, &HashSet::new(), &Name::anonymous())?;
    }

    let prop_former = is_prop_former(&mut work, &inductive.base.type_)?;
    if prop_former || cases_on.base.level_params.len() <= inductive.base.level_params.len() {
        return Ok(None);
    }

    let mut build = Build {
        work,
        remaining_binders: budget.max_binders,
        next: 0,
    };

    let nct_name = Name::str(family.clone(), "noConfusionType");
    let nc_name = Name::str(family.clone(), "noConfusion");

    // 1. Enumeration fast path (`NoConfusion.lean::mkNoConfusionEnum`).
    if is_enum_type(inductive, constructors, prop_former) && use_enum_helper {
        let us: Vec<Level> = inductive
            .base
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let v_name = fresh_enum_universe(&inductive.base.level_params);
        let v = Level::param(v_name.clone());
        let mut level_params = Vec::with_capacity(inductive.base.level_params.len() + 1);
        level_params.push(v_name);
        level_params.extend(inductive.base.level_params.iter().cloned());

        let enum_ty = Expr::const_(family.clone(), us.clone());
        let enum_level = infer_sort_level(&mut build, &[], &enum_ty, &lookup_const)?;
        let sort_v = Expr::sort(v.clone());

        let p_nct = build.local(
            Name::from_components(["P"]),
            sort_v.clone(),
            BinderInfo::Default,
        )?;
        let x_nct = build.local(
            Name::from_components(["x"]),
            enum_ty.clone(),
            BinderInfo::Default,
        )?;
        let y_nct = build.local(
            Name::from_components(["y"]),
            enum_ty.clone(),
            BinderInfo::Default,
        )?;
        let nct_binders = [p_nct.clone(), x_nct.clone(), y_nct.clone()];
        let nct_type = build.close(&nct_binders, sort_v.clone(), false)?;
        let nct_body = if constructors.len() == 1 {
            Expr::forall_e(
                Name::anonymous(),
                fv(&p_nct),
                fv(&p_nct),
                BinderInfo::Default,
            )
        } else {
            let ctor_idx = Expr::const_(Name::str(family.clone(), "ctorIdx"), us.clone());
            app(
                Expr::const_(
                    Name::from_components(["noConfusionTypeEnum"]),
                    vec![enum_level.clone(), Level::one(), v.clone()],
                ),
                [
                    enum_ty.clone(),
                    Expr::const_(Name::from_components(["Nat"]), Vec::new()),
                    Expr::const_(Name::from_components(["instDecidableEqNat"]), Vec::new()),
                    ctor_idx,
                    fv(&p_nct),
                    fv(&x_nct),
                    fv(&y_nct),
                ],
            )
        };
        let nct_value = build.close(&nct_binders, nct_body, true)?;
        let no_confusion_type = DefinitionVal {
            base: ConstantVal {
                name: nct_name.clone(),
                level_params: level_params.clone(),
                type_: nct_type,
            },
            value: nct_value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![nct_name.clone()],
        };

        let p_nc = build.local(Name::from_components(["P"]), sort_v, BinderInfo::Implicit)?;
        let x_nc = build.local(
            Name::from_components(["x"]),
            enum_ty.clone(),
            BinderInfo::Implicit,
        )?;
        let y_nc = build.local(
            Name::from_components(["y"]),
            enum_ty.clone(),
            BinderInfo::Implicit,
        )?;
        let eq_ty = app(
            Expr::const_(Name::from_components(["Eq"]), vec![enum_level.clone()]),
            [enum_ty.clone(), fv(&x_nc), fv(&y_nc)],
        );
        let h_nc = build.local(Name::from_components(["h"]), eq_ty, BinderInfo::Default)?;
        let mut nct_levels = Vec::with_capacity(us.len() + 1);
        nct_levels.push(v.clone());
        nct_levels.extend(us.iter().cloned());
        let nc_ret = app(
            Expr::const_(nct_name, nct_levels),
            [fv(&p_nc), fv(&x_nc), fv(&y_nc)],
        );
        let nc_binders = [p_nc.clone(), x_nc.clone(), y_nc.clone(), h_nc.clone()];
        let nc_type = build.close(&nc_binders, nc_ret, false)?;
        let nc_body = if constructors.len() == 1 {
            let p_val =
                build.local(Name::from_components(["p"]), fv(&p_nc), BinderInfo::Default)?;
            build.close(std::slice::from_ref(&p_val), fv(&p_val), true)?
        } else {
            let ctor_idx = Expr::const_(Name::str(family.clone(), "ctorIdx"), us);
            app(
                Expr::const_(
                    Name::from_components(["noConfusionEnum"]),
                    vec![enum_level, Level::one(), v],
                ),
                [
                    enum_ty,
                    Expr::const_(Name::from_components(["Nat"]), Vec::new()),
                    Expr::const_(Name::from_components(["instDecidableEqNat"]), Vec::new()),
                    ctor_idx,
                    fv(&p_nc),
                    fv(&x_nc),
                    fv(&y_nc),
                    fv(&h_nc),
                ],
            )
        };
        let nc_value = build.close(&nc_binders, nc_body, true)?;
        let no_confusion = DefinitionVal {
            base: ConstantVal {
                name: nc_name.clone(),
                level_params,
                type_: nc_type,
            },
            value: nc_value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![nc_name],
        };
        return Ok(Some(NoConfusionCandidates {
            no_confusion_type,
            no_confusion,
            is_enum_construction: true,
        }));
    }

    // 2. General path (`NoConfusion.lean::mkNoConfusionCore`).
    let level_params = cases_on.base.level_params.clone();
    let v = Level::param(level_params[0].clone());
    let v_succ = v
        .clone()
        .succ()
        .map_err(|_| AuxiliaryError::ResourceLimit)?;
    let us: Vec<Level> = level_params[1..]
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let mut cases_succ_levels = Vec::with_capacity(level_params.len());
    cases_succ_levels.push(v_succ.clone());
    cases_succ_levels.extend(us.iter().cloned());
    let mut cases_v_levels = Vec::with_capacity(level_params.len());
    cases_v_levels.push(v.clone());
    cases_v_levels.extend(us.iter().cloned());
    let ctor_equalities: Vec<_> = constructors
        .iter()
        .map(|ctor| ctor_equality_template(&mut build, ctor, &us, &lookup_const))
        .collect::<Result<_, _>>()?;

    let use_linear = constructors.len() > 2
        && lookup_const(&Name::str(family.clone(), "ctorElim")).is_some()
        && lookup_const(&Name::from_components(["dite"])).is_some()
        && lookup_const(&Name::from_components(["Nat", "decEq"])).is_some()
        && lookup_const(&Name::from_components(["Not"])).is_some();

    let num_params = inductive.num_params as usize;
    let num_indices = inductive.num_indices as usize;
    let num_ctors = constructors.len();
    let cases_const_succ = Expr::const_(expected_cases_on.clone(), cases_succ_levels.clone());
    let cases_succ_ty = subst_expr_level_params(
        &mut build.work,
        &cases_on.base.type_,
        &cases_on.base.level_params,
        &cases_succ_levels,
    )?;
    let p_type = Expr::sort(v.clone());

    // 2a. `<T>.noConfusionType`
    let p_local = build.local(
        Name::from_components(["P"]),
        p_type.clone(),
        BinderInfo::Default,
    )?;
    let (xs1, t1) = bounded_telescope(&mut build, &cases_succ_ty, num_params)?;
    let (xs2, t2) = bounded_telescope(&mut build, &cases_succ_ty, num_params)?;
    let (motive1, t1) = build_const_motive(&mut build, &t1, &p_type, &lookup_const)?;
    let (motive2, t2) = build_const_motive(&mut build, &t2, &p_type, &lookup_const)?;
    let (ysx1, t1) = bounded_telescope(&mut build, &t1, num_indices + 1)?;
    let (ysx2, _) = bounded_telescope(&mut build, &t2, num_indices + 1)?;

    let mut nct_outer_locals = Vec::with_capacity(1 + 2 * (num_params + num_indices + 1));
    nct_outer_locals.push(p_local.clone());
    nct_outer_locals.extend(xs1.iter().cloned());
    nct_outer_locals.extend(ysx1.iter().cloned());
    nct_outer_locals.extend(xs2.iter().cloned());
    nct_outer_locals.extend(ysx2.iter().cloned());

    let alt_types1 = arrow_domains_n(&mut build.work, num_ctors, &t1)?;
    let mut alts1 = Vec::with_capacity(num_ctors);
    let nat_ty = Expr::const_(Name::from_components(["Nat"]), Vec::new());

    for (i, alt_type1) in alt_types1.iter().enumerate() {
        let (zs1, _) = forall_telescope_plain(&mut build, alt_type1)?;
        let mut branch_locals = nct_outer_locals.clone();
        branch_locals.extend(zs1.iter().cloned());
        let alt_body = if use_linear {
            let mut idx_args: Vec<Expr> = xs2.iter().map(fv).collect();
            idx_args.extend(ysx2.iter().map(fv));
            let ctor_idx_app = app(
                Expr::const_(Name::str(family.clone(), "ctorIdx"), us.clone()),
                idx_args,
            );
            let lit_i = Expr::lit(Literal::Nat(NatLit::from_u64(i as u64)));
            let heq = app(
                Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]),
                [nat_ty.clone(), ctor_idx_app.clone(), lit_i.clone()],
            );
            let dec = app(
                Expr::const_(Name::from_components(["Nat", "decEq"]), Vec::new()),
                [ctor_idx_app, lit_i],
            );
            let h_then = build.local(
                Name::from_components(["h"]),
                heq.clone(),
                BinderInfo::Default,
            )?;
            let with_name = as_private_as(
                &Name::str(constructors[i].base.name.clone(), "elim"),
                family,
            );
            let mut with_args: Vec<Expr> = xs2.iter().map(fv).collect();
            with_args.push(motive2.clone());
            with_args.extend(ysx2.iter().map(fv));
            with_args.push(fv(&h_then));
            let with_app = app(
                Expr::const_(with_name, cases_succ_levels.clone()),
                with_args,
            );
            let mut then_locals = branch_locals.clone();
            then_locals.push(h_then.clone());
            let with_ty = infer_type_bounded(&mut build, &then_locals, &with_app, &lookup_const)?;
            let with_ty_whnf = whnf_for_sort(&mut build.work, with_ty, &lookup_const)?;
            let ExprNode::ForallE {
                binder_type: alt2_dom,
                ..
            } = with_ty_whnf.node()
            else {
                return Err(AuxiliaryError::InvalidTelescope);
            };
            let (zs2, _) = forall_telescope_reducing(&mut build, alt2_dom, &lookup_const)?;
            let k = ctor_equalities[i].instantiate(
                &mut build.work,
                &fv(&p_local),
                &xs1,
                &zs1,
                &xs2,
                &zs2,
            )?;
            let k_arrow_p = Expr::forall_e(Name::anonymous(), k, fv(&p_local), BinderInfo::Default);
            let inner_alt = build.close(&zs2, k_arrow_p, true)?;
            let then_body = Expr::app(with_app, inner_alt);
            let then_lam = build.close(&[h_then], then_body, true)?;

            let not_heq = Expr::app(
                Expr::const_(Name::from_components(["Not"]), Vec::new()),
                heq.clone(),
            );
            let h_else = build.local(Name::from_components(["h"]), not_heq, BinderInfo::Default)?;
            let else_lam = build.close(&[h_else], fv(&p_local), true)?;

            app(
                Expr::const_(Name::from_components(["dite"]), vec![v_succ.clone()]),
                [p_type.clone(), heq, dec, then_lam, else_lam],
            )
        } else {
            let mut inner_args: Vec<Expr> = xs2.iter().map(fv).collect();
            inner_args.push(motive2.clone());
            inner_args.extend(ysx2.iter().map(fv));
            let alt2_head = app(cases_const_succ.clone(), inner_args);
            let alt2_head_ty =
                infer_type_bounded(&mut build, &branch_locals, &alt2_head, &lookup_const)?;
            let alt_types2 = arrow_domains_n(&mut build.work, num_ctors, &alt2_head_ty)?;
            let mut alts2 = Vec::with_capacity(num_ctors);
            for (j, alt_type2) in alt_types2.iter().enumerate() {
                let (zs2, _) = forall_telescope_plain(&mut build, alt_type2)?;
                let body2 = if i == j {
                    let k = ctor_equalities[i].instantiate(
                        &mut build.work,
                        &fv(&p_local),
                        &xs1,
                        &zs1,
                        &xs2,
                        &zs2,
                    )?;
                    Expr::forall_e(Name::anonymous(), k, fv(&p_local), BinderInfo::Default)
                } else {
                    fv(&p_local)
                };
                alts2.push(build.close(&zs2, body2, true)?);
            }
            app(alt2_head, alts2)
        };
        alts1.push(build.close(&zs1, alt_body, true)?);
    }

    let mut outer_args: Vec<Expr> = xs1.iter().map(fv).collect();
    outer_args.push(motive1);
    outer_args.extend(ysx1.iter().map(fv));
    outer_args.extend(alts1);
    let nct_body = app(cases_const_succ, outer_args);
    let nct_value = build.close(&nct_outer_locals, nct_body, true)?;
    // `Lean.Meta.inferType` beta-reduces `(motive1 ysx1)` = `(fun _ => Sort v) ysx1` to `Sort v`.
    let nct_type = build.close(&nct_outer_locals, p_type, false)?;

    build
        .work
        .scan(&nct_type, &HashSet::new(), &Name::anonymous())?;
    build
        .work
        .scan(&nct_value, &HashSet::new(), &Name::anonymous())?;

    let (_, nct_val_unsafe) = scan_const_meta(&mut build.work, &[&nct_value], &|n| {
        lookup_const(n).map(CtorIdxConstMeta::from_constant)
    })?;
    let (_, nct_ty_unsafe) = scan_const_meta(&mut build.work, &[&nct_type], &|n| {
        lookup_const(n).map(CtorIdxConstMeta::from_constant)
    })?;
    let nct_safety = if inductive.is_unsafe || nct_val_unsafe || nct_ty_unsafe {
        DefinitionSafety::Unsafe
    } else {
        DefinitionSafety::Safe
    };
    let no_confusion_type = DefinitionVal {
        base: ConstantVal {
            name: nct_name.clone(),
            level_params: level_params.clone(),
            type_: nct_type.clone(),
        },
        value: nct_value,
        hints: ReducibilityHints::Abbrev,
        safety: nct_safety,
        all: vec![nct_name.clone()],
    };
    let nct_info = ConstantInfo::Defn(no_confusion_type.clone());
    let lookup_with_nct = |n: &Name| {
        if n == &nct_name {
            Some(&nct_info)
        } else {
            lookup_const(n)
        }
    };

    // 2b. `<T>.noConfusion` (`NoConfusion.lean::mkNoConfusionCoreImp`)
    let nct_ty_v =
        subst_expr_level_params(&mut build.work, &nct_type, &level_params, &cases_v_levels)?;
    let (mut p_vec, t_after_p) = bounded_telescope(&mut build, &nct_ty_v, 1)?;
    let (mut nc_xs1, t_after_xs1) =
        bounded_telescope(&mut build, &t_after_p, num_params + num_indices + 1)?;
    let (mut nc_xs2, _) =
        bounded_telescope(&mut build, &t_after_xs1, num_params + num_indices + 1)?;
    p_vec[0].binder_info = BinderInfo::Implicit;
    for l in &mut nc_xs1 {
        l.binder_info = BinderInfo::Implicit;
    }
    for l in &mut nc_xs2 {
        l.binder_info = BinderInfo::Implicit;
    }
    let p_nc = p_vec.pop().unwrap();
    let params1 = &nc_xs1[..num_params];
    let ysx1_nc = &nc_xs1[num_params..];

    let mut nc_base_locals = Vec::with_capacity(1 + 2 * nc_xs1.len());
    nc_base_locals.push(p_nc.clone());
    nc_base_locals.extend(nc_xs1.iter().cloned());
    nc_base_locals.extend(nc_xs2.iter().cloned());

    let nct_const_v = Expr::const_(nct_name.clone(), cases_v_levels.clone());
    let mut target1_args = Vec::with_capacity(1 + 2 * nc_xs1.len());
    target1_args.push(fv(&p_nc));
    target1_args.extend(nc_xs1.iter().map(fv));
    target1_args.extend(nc_xs1.iter().map(fv));
    let target1 = app(nct_const_v.clone(), target1_args);
    let nc_motive1 = build.close(ysx1_nc, target1, true)?;

    let params1_fvs: Vec<Expr> = params1.iter().map(fv).collect();
    let mut nc_alts = Vec::with_capacity(num_ctors);
    for (ctor, equalities) in constructors.iter().zip(&ctor_equalities) {
        let ctor_ty_u = subst_expr_level_params(
            &mut build.work,
            &ctor.base.type_,
            &ctor.base.level_params,
            &us,
        )?;
        let ctor_ty_inst = instantiate_forall(&mut build.work, &ctor_ty_u, &params1_fvs)?;
        let (fs1, _) = forall_telescope_reducing(&mut build, &ctor_ty_inst, &lookup_with_nct)?;
        let k_type =
            equalities.instantiate(&mut build.work, &fv(&p_nc), params1, &fs1, params1, &fs1)?;
        let k_local = build.local(
            Name::from_components(["k"]),
            k_type.clone(),
            BinderInfo::Default,
        )?;
        let mut e = fv(&k_local);
        let mut cursor = &k_type;
        loop {
            build.work.tick()?;
            match cursor.node() {
                ExprNode::MData { expr, .. } => cursor = expr,
                ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    let Some((kind, lvls, args)) = decompose_eq_or_heq(binder_type) else {
                        return Err(AuxiliaryError::InvalidTelescope);
                    };
                    let refl = if kind == "Eq" {
                        app(
                            Expr::const_(Name::from_components(["Eq", "refl"]), lvls),
                            [args[0].clone(), args[1].clone()],
                        )
                    } else {
                        app(
                            Expr::const_(Name::from_components(["HEq", "refl"]), lvls),
                            [args[0].clone(), args[1].clone()],
                        )
                    };
                    e = Expr::app(e, refl);
                    cursor = body;
                }
                _ => break,
            }
        }
        let mut alt_binders = fs1;
        alt_binders.push(k_local);
        nc_alts.push(build.close(&alt_binders, e, true)?);
    }

    let mut base_proof_args: Vec<Expr> = params1.iter().map(fv).collect();
    base_proof_args.push(nc_motive1);
    base_proof_args.extend(ysx1_nc.iter().map(fv));
    base_proof_args.extend(nc_alts);
    let base_proof = app(
        Expr::const_(expected_cases_on, cases_v_levels),
        base_proof_args,
    );

    // Build `withEqTelescope xs1 xs2` and `mkEqNDRecTelescope`.
    let mut eq_locals = Vec::with_capacity(nc_xs1.len());
    for (i, (x, y)) in nc_xs1.iter().zip(&nc_xs2).enumerate() {
        let (eq_ty, is_heq) = mk_eq_heq(
            &mut build,
            &nc_base_locals,
            &fv(x),
            &fv(y),
            &lookup_with_nct,
        )?;
        let eq_name = if nc_xs1.len() > 1 {
            Name::str(Name::anonymous(), format!("eq_{}", i + 1))
        } else {
            Name::from_components(["eq"])
        };
        let eq_local = build.local(eq_name, eq_ty, BinderInfo::Default)?;
        eq_locals.push((eq_local, is_heq));
    }

    let mut target2_args = Vec::with_capacity(1 + 2 * nc_xs1.len());
    target2_args.push(fv(&p_nc));
    target2_args.extend(nc_xs1.iter().map(fv));
    target2_args.extend(nc_xs2.iter().map(fv));
    let target2 = app(nct_const_v, target2_args);

    let mut step_base_locals = Vec::with_capacity(1 + nc_xs1.len());
    step_base_locals.push(p_nc.clone());
    step_base_locals.extend(nc_xs1.iter().cloned());

    let mut initial_lctx = Vec::with_capacity(2 * nc_xs1.len());
    for (j, y) in nc_xs2.iter().enumerate() {
        initial_lctx.push(ActiveLocal::Y(j, y.clone()));
    }
    for (j, (eq_d, is_heq)) in eq_locals.iter().enumerate() {
        initial_lctx.push(ActiveLocal::Eq(j, eq_d.clone(), *is_heq));
    }

    let nc_body = mk_eq_ndrec_step(
        &mut build,
        &step_base_locals,
        &nc_xs1,
        &initial_lctx,
        &target2,
        &base_proof,
        0,
        &lookup_with_nct,
    )?;

    let mut nc_binders = Vec::with_capacity(1 + 3 * nc_xs1.len());
    nc_binders.push(p_nc);
    nc_binders.extend(nc_xs1);
    nc_binders.extend(nc_xs2);
    nc_binders.extend(eq_locals.into_iter().map(|(d, _)| d));
    let nc_value = build.close(&nc_binders, nc_body, true)?;
    // `Lean.Meta.inferType` returns `∀ {P} {xs1} {xs2} (eqs...), T.noConfusionType P xs1 xs2`.
    let nc_type = build.close(&nc_binders, target2, false)?;

    build
        .work
        .scan(&nc_type, &HashSet::new(), &Name::anonymous())?;
    build
        .work
        .scan(&nc_value, &HashSet::new(), &Name::anonymous())?;

    let (_, nc_val_unsafe) = scan_const_meta(&mut build.work, &[&nc_value], &|n| {
        lookup_with_nct(n).map(CtorIdxConstMeta::from_constant)
    })?;
    let (_, nc_ty_unsafe) = scan_const_meta(&mut build.work, &[&nc_type], &|n| {
        lookup_with_nct(n).map(CtorIdxConstMeta::from_constant)
    })?;
    let nc_safety = if inductive.is_unsafe || nc_val_unsafe || nc_ty_unsafe {
        DefinitionSafety::Unsafe
    } else {
        DefinitionSafety::Safe
    };
    let no_confusion = DefinitionVal {
        base: ConstantVal {
            name: nc_name.clone(),
            level_params,
            type_: nc_type,
        },
        value: nc_value,
        hints: ReducibilityHints::Abbrev,
        safety: nc_safety,
        all: vec![nc_name],
    };

    Ok(Some(NoConfusionCandidates {
        no_confusion_type,
        no_confusion,
        is_enum_construction: false,
    }))
}
