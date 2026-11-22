//! Native `ctorIdx` and enum `toCtorIdx` candidates (fln-derived-declaration-frontier-cj7s).
//!
//! Algorithm: the pin's `Lean/Meta/Constructions/CtorIdx.lean::mkCtorIdx` and
//! `Lean/MonadEnv.lean::isEnumType`.
//!
//! Like `recOn`, `casesOn`, `below`, and `brecOn`, these generators confer no
//! admission or attribute authority: every produced candidate must pass both
//! checking seats through the caller's ordinary admission path.

use super::*;
use fln_core::expr::{Literal, NatLit};
use fln_env::constants::{ConstantInfo, ConstructorVal};

/// Ambient constant metadata needed to compute `getMaxHeight` and
/// `mkDefinitionValInferringUnsafe` without coupling `fln-elab` to a single
/// environment container (callers may query an `Environment` or a decoded
/// `.olean` constant map).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CtorIdxConstMeta {
    /// Definition height when `ConstantInfo::Defn(d)` carries
    /// `ReducibilityHints::Regular(h)` (or an active `defHeightOverrideExt`
    /// height override).
    pub regular_height: Option<u32>,
    /// Whether the constant itself is unsafe (`Induct`/`Ctor`/`Rec`/`Axiom`
    /// `is_unsafe`, `Defn` `DefinitionSafety::Unsafe`, or `Opaque` `is_unsafe`).
    pub is_unsafe: bool,
}

impl CtorIdxConstMeta {
    /// Extract `CtorIdxConstMeta` from any decoded or admitted [`ConstantInfo`].
    pub fn from_constant(info: &ConstantInfo) -> Self {
        match info {
            ConstantInfo::Axiom(a) => Self {
                regular_height: None,
                is_unsafe: a.is_unsafe,
            },
            ConstantInfo::Defn(d) => Self {
                regular_height: match d.hints {
                    ReducibilityHints::Regular(h) => Some(h),
                    ReducibilityHints::Opaque | ReducibilityHints::Abbrev => None,
                },
                is_unsafe: d.safety == DefinitionSafety::Unsafe,
            },
            ConstantInfo::Thm(_) | ConstantInfo::Quot(_) => Self {
                regular_height: None,
                is_unsafe: false,
            },
            ConstantInfo::Opaque(o) => Self {
                regular_height: None,
                is_unsafe: o.is_unsafe,
            },
            ConstantInfo::Induct(i) => Self {
                regular_height: None,
                is_unsafe: i.is_unsafe,
            },
            ConstantInfo::Ctor(c) => Self {
                regular_height: None,
                is_unsafe: c.is_unsafe,
            },
            ConstantInfo::Rec(r) => Self {
                regular_height: None,
                is_unsafe: r.is_unsafe,
            },
        }
    }
}

/// Generated `<T>.ctorIdx` and optional enumeration alias `<T>.toCtorIdx`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtorIdxCandidates {
    pub ctor_idx: DefinitionVal,
    pub to_ctor_idx: Option<DefinitionVal>,
}

fn is_prop_former(work: &mut Builder, type_: &Expr) -> Result<bool, AuxiliaryError> {
    let mut current = type_;
    loop {
        work.tick()?;
        match current.node() {
            ExprNode::ForallE { body, .. } => current = body,
            ExprNode::MData { expr, .. } => current = expr,
            ExprNode::Sort { level } => return Ok(level.is_zero()),
            _ => return Err(AuxiliaryError::InvalidTelescope),
        }
    }
}

fn bounded_telescope(
    build: &mut Build,
    type_: &Expr,
    count: usize,
) -> Result<(Vec<LocalDecl>, Expr), AuxiliaryError> {
    let mut current = type_.clone();
    let mut locals = Vec::with_capacity(count);
    for _ in 0..count {
        loop {
            build.work.tick()?;
            match current.node() {
                ExprNode::MData { expr, .. } => current = expr.clone(),
                _ => break,
            }
        }
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = current.node()
        else {
            return Err(AuxiliaryError::InvalidTelescope);
        };
        let local = build.local(binder_name.clone(), binder_type.clone(), *binder_info)?;
        current = body
            .subst_loose(0, &[fv(&local)])
            .map_err(|_| AuxiliaryError::InvalidTelescope)?;
        locals.push(local);
    }
    Ok((locals, current))
}

fn instantiate_forall(
    work: &mut Builder,
    type_: &Expr,
    args: &[Expr],
) -> Result<Expr, AuxiliaryError> {
    let mut current = type_.clone();
    for arg in args {
        loop {
            work.tick()?;
            match current.node() {
                ExprNode::MData { expr, .. } => current = expr.clone(),
                _ => break,
            }
        }
        let ExprNode::ForallE { body, .. } = current.node() else {
            return Err(AuxiliaryError::InvalidTelescope);
        };
        current = body
            .subst_loose(0, std::slice::from_ref(arg))
            .map_err(|_| AuxiliaryError::InvalidTelescope)?;
    }
    Ok(current)
}

/// Iterative walk collecting maximum regular definition height and whether any
/// referenced constant is unsafe (`Environment.getMaxHeight` + `hasUnsafe`).
fn scan_const_meta<F>(
    work: &mut Builder,
    roots: &[&Expr],
    lookup: &F,
) -> Result<(u32, bool), AuxiliaryError>
where
    F: Fn(&Name) -> Option<CtorIdxConstMeta>,
{
    let mut stack: Vec<&Expr> = roots.to_vec();
    let mut seen = HashSet::new();
    let mut max_height = 0_u32;
    let mut has_unsafe = false;
    while let Some(expr) = stack.pop() {
        work.tick()?;
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        match expr.node() {
            ExprNode::Const { name, .. } => {
                if let Some(meta) = lookup(name) {
                    if let Some(h) = meta.regular_height {
                        max_height = max_height.max(h);
                    }
                    if meta.is_unsafe {
                        has_unsafe = true;
                    }
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
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                stack.push(expr);
            }
            _ => {}
        }
    }
    Ok((max_height, has_unsafe))
}

/// `Lean.isEnumType` (`Lean/MonadEnv.lean:198-208`).
fn is_enum_type(
    inductive: &InductiveVal,
    constructors: &[ConstructorVal],
    prop_former: bool,
) -> bool {
    !prop_former
        && inductive.all.len() == 1
        && inductive.num_nested == 0
        && inductive.num_indices == 0
        && inductive.num_params == 0
        && !inductive.ctors.is_empty()
        && !inductive.is_rec
        && !inductive.is_unsafe
        && constructors.iter().all(|ctor| ctor.num_fields == 0)
}

/// Construct `<T>.ctorIdx` (and `<T>.toCtorIdx` for enumeration types) from the
/// admitted inductive family, its ordered constructors, and its `casesOn`
/// definition (`Lean/Meta/Constructions/CtorIdx.lean::mkCtorIdx`).
///
/// Returns `Ok(None)` when the pin's own guard skips generation (Prop-former
/// families or families whose `casesOn` does not eliminate into `Type`).
pub fn ctor_idx_declarations<F>(
    inductive: &InductiveVal,
    constructors: &[ConstructorVal],
    cases_on: &DefinitionVal,
    budget: RecordBudget,
    const_meta: F,
) -> Result<Option<CtorIdxCandidates>, AuxiliaryError>
where
    F: Fn(&Name) -> Option<CtorIdxConstMeta>,
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
    let total_xs = (inductive.num_params as usize)
        .checked_add(inductive.num_indices as usize)
        .ok_or(AuxiliaryError::ResourceLimit)?;
    if total_xs >= budget.max_binders || inductive.base.level_params.len() > budget.max_binders {
        return Err(AuxiliaryError::ResourceLimit);
    }

    let mut work = Builder {
        remaining: budget.max_nodes,
    };
    work.scan(&inductive.base.type_, &HashSet::new(), &Name::anonymous())?;
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

    let (mut xs, _) = bounded_telescope(&mut build, &inductive.base.type_, total_xs)?;
    // `withImplicitBinderInfos xs`: every parameter and index binder becomes implicit.
    for local in &mut xs {
        local.binder_info = BinderInfo::Implicit;
    }
    let num_params = inductive.num_params as usize;
    let params = &xs[..num_params];
    let indices = &xs[num_params..];

    let us: Vec<Level> = inductive
        .base
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let ind_type = app(Expr::const_(family.clone(), us.clone()), xs.iter().map(fv));
    let nat_type = Expr::const_(Name::from_components(["Nat"]), Vec::new());

    // `mkArrow indType natType` followed by `mkForallFVars xs`.
    let arrow = Expr::forall_e(
        Name::from_components(["x"]),
        ind_type.clone(),
        nat_type.clone(),
        BinderInfo::Default,
    );
    let decl_type = build.close(&xs, arrow, false)?;

    // `withLocalDeclD `x indType fun x => ...`
    let x_local = build.local(Name::from_components(["x"]), ind_type, BinderInfo::Default)?;
    let body = if constructors.len() == 1 {
        Expr::lit(Literal::Nat(NatLit::from_u64(0)))
    } else {
        let mut motive_locals = indices.to_vec();
        motive_locals.push(x_local.clone());
        let motive = build.close(&motive_locals, nat_type, true)?;

        let mut cases_levels = Vec::with_capacity(us.len() + 1);
        cases_levels.push(Level::one());
        cases_levels.extend(us.iter().cloned());

        let mut value_args: Vec<Expr> = params.iter().map(fv).collect();
        value_args.push(motive);
        value_args.extend(indices.iter().map(fv));
        value_args.push(fv(&x_local));

        let param_fvars: Vec<Expr> = params.iter().map(fv).collect();
        for ctor in constructors {
            let ctor_type = instantiate_forall(&mut build.work, &ctor.base.type_, &param_fvars)?;
            let (ys, _) = bounded_telescope(&mut build, &ctor_type, ctor.num_fields as usize)?;
            let lit = Expr::lit(Literal::Nat(NatLit::from_u64(u64::from(ctor.cidx))));
            let alt = build.close(&ys, lit, true)?;
            value_args.push(alt);
        }
        app(Expr::const_(expected_cases_on, cases_levels), value_args)
    };

    let mut value_locals = xs;
    value_locals.push(x_local);
    let decl_value = build.close(&value_locals, body, true)?;

    build
        .work
        .scan(&decl_type, &HashSet::new(), &Name::anonymous())?;
    build
        .work
        .scan(&decl_value, &HashSet::new(), &Name::anonymous())?;

    let (max_height, value_unsafe) = scan_const_meta(&mut build.work, &[&decl_value], &const_meta)?;
    let (_, type_unsafe) = scan_const_meta(&mut build.work, &[&decl_type], &const_meta)?;
    let safety = if inductive.is_unsafe || type_unsafe || value_unsafe {
        DefinitionSafety::Unsafe
    } else {
        DefinitionSafety::Safe
    };
    let hints = ReducibilityHints::Regular(max_height.saturating_add(1));

    let decl_name = Name::str(family.clone(), "ctorIdx");
    let ctor_idx = DefinitionVal {
        base: ConstantVal {
            name: decl_name.clone(),
            level_params: inductive.base.level_params.clone(),
            type_: decl_type.clone(),
        },
        value: decl_value,
        hints,
        safety,
        all: vec![decl_name.clone()],
    };

    let to_ctor_idx = if is_enum_type(inductive, constructors, prop_former) {
        let alias_name = Name::str(family.clone(), "toCtorIdx");
        Some(DefinitionVal {
            base: ConstantVal {
                name: alias_name.clone(),
                level_params: inductive.base.level_params.clone(),
                type_: decl_type,
            },
            value: Expr::const_(decl_name, us),
            hints: ReducibilityHints::Abbrev,
            safety,
            all: vec![alias_name],
        })
    } else {
        None
    };

    Ok(Some(CtorIdxCandidates {
        ctor_idx,
        to_ctor_idx,
    }))
}
