//! Course-of-values recursion candidates, derived from the checked recursor.
//!
//! This is the native construction in the pin's
//! `Lean/Meta/Constructions/BRecOn.lean`: `below` stores the motive result and
//! recursive history of each recursive field; `brecOn.go` computes that pair;
//! `brecOn` projects its first component. Function-valued children retain their
//! complete dependent telescope. Mutual motives and nested recursors retain
//! their original order and names.
//!
//! These functions confer no admission or attribute authority. In particular,
//! the separate `brecOn.eq` theorem is not manufactured by these generators.

use super::*;
use fln_core::level::LevelView;
use std::collections::HashMap;

struct Layout {
    locals: Vec<LocalDecl>,
    result: Expr,
    minor_start: usize,
    suffix: usize,
    main: usize,
    levels: Vec<Level>,
    result_level: Level,
    below_name: Name,
    brec_name: Name,
}

impl Layout {
    fn new(
        build: &mut Build,
        recursor: &RecursorVal,
        families: &[InductiveVal],
    ) -> Result<Self, AuxiliaryError> {
        let expected = argument_count(recursor)?;
        let (locals, result) = build.telescope(&recursor.base.type_)?;
        if locals.len() != expected || recursor.num_motives == 0 {
            return Err(AuxiliaryError::InvalidTelescope);
        }
        let owner = recursor.base.name.parent();
        let suffix = match recursor.base.name.leaf_view() {
            LeafView::Str("rec") => String::new(),
            LeafView::Str(s) => {
                let Some(index) = s.strip_prefix("rec_").and_then(|s| s.parse::<u32>().ok()) else {
                    return Err(AuxiliaryError::InvalidRecursorName);
                };
                let owner_info = find_family(build, families, &owner)?;
                if index == 0
                    || index > owner_info.num_nested
                    || recursor.all.first() != Some(&owner)
                {
                    return Err(AuxiliaryError::InconsistentFamily);
                }
                format!("_{index}")
            }
            _ => return Err(AuxiliaryError::InvalidRecursorName),
        };
        let owner_info = find_family(build, families, &owner)?;
        if !owner_info.is_rec
            || owner_info.is_unsafe != recursor.is_unsafe
            || owner_info.num_params != recursor.num_params
            || recursor.all.is_empty()
            || recursor.all.len() > recursor.num_motives as usize
        {
            return Err(AuxiliaryError::InconsistentFamily);
        }
        let minor_start = recursor.num_params as usize + recursor.num_motives as usize;
        let tail = minor_start + recursor.num_minors as usize;
        let level = major_level(build, families, &locals.last().unwrap().type_)?;
        // `mkBelow` and `mkBRecOn` exclude proposition-valued families. An
        // arbitrary Sort parameter may become Prop, but is not a Prop former.
        if level.is_zero()
            || recursor.base.level_params.len() != owner_info.base.level_params.len() + 1
        {
            return Err(AuxiliaryError::InconsistentFamily);
        }
        let levels: Vec<_> = recursor
            .base
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let result_level =
            Level::max(level, levels[0].clone()).map_err(|_| AuxiliaryError::ResourceLimit)?;
        let (result_head, _) = spine(build, &result)?;
        let main = locals[recursor.num_params as usize..minor_start]
            .iter()
            .position(|motive| result_head == fv(motive))
            .ok_or(AuxiliaryError::InvalidTelescope)?;
        Ok(Self {
            locals,
            result,
            minor_start,
            suffix: tail,
            main,
            levels,
            result_level,
            below_name: Name::str(owner.clone(), format!("below{suffix}")),
            brec_name: Name::str(owner, format!("brecOn{suffix}")),
        })
    }

    fn motives(&self, recursor: &RecursorVal) -> &[LocalDecl] {
        &self.locals[recursor.num_params as usize..self.minor_start]
    }

    fn parameters(&self) -> Vec<LocalDecl> {
        self.locals[..self.minor_start]
            .iter()
            .chain(&self.locals[self.suffix..])
            .cloned()
            .collect()
    }
}

fn find_family<'a>(
    build: &mut Build,
    families: &'a [InductiveVal],
    name: &Name,
) -> Result<&'a InductiveVal, AuxiliaryError> {
    let mut found = None;
    for family in families {
        build.work.tick()?;
        if family.base.name == *name {
            if found.is_some() {
                return Err(AuxiliaryError::InconsistentFamily);
            }
            found = Some(family);
        }
    }
    found.ok_or(AuxiliaryError::InconsistentFamily)
}

/// `inferType` of a saturated family application, retaining the pin's exact
/// smart level-parameter substitution. In particular, nested containers can
/// instantiate `max u v` with the same level for both parameters.
fn major_level(
    build: &mut Build,
    families: &[InductiveVal],
    major_type: &Expr,
) -> Result<Level, AuxiliaryError> {
    let (head, arguments) = spine(build, major_type)?;
    let ExprNode::Const { name, levels } = head.node() else {
        return Err(AuxiliaryError::InvalidTelescope);
    };
    let family = find_family(build, families, name)?;
    let arity = (family.num_params as usize)
        .checked_add(family.num_indices as usize)
        .ok_or(AuxiliaryError::ResourceLimit)?;
    if arguments.len() != arity || family.base.level_params.len() != levels.len() {
        return Err(AuxiliaryError::InconsistentFamily);
    }
    let mut type_former = &family.base.type_;
    while let ExprNode::ForallE { body, .. } = type_former.node() {
        build.work.tick()?;
        type_former = body;
    }
    let ExprNode::Sort { level } = type_former.node() else {
        return Err(AuxiliaryError::InvalidTelescope);
    };
    if type_former.has_level_mvar() {
        return Err(AuxiliaryError::InvalidTelescope);
    }
    let mut substitutions = HashMap::new();
    for (name, level) in family.base.level_params.iter().zip(levels) {
        build.work.tick()?;
        if substitutions.insert(name, level).is_some() {
            return Err(AuxiliaryError::InconsistentFamily);
        }
    }
    let mut done = HashMap::new();
    let mut pending = vec![(level, false)];
    while let Some((current, exit)) = pending.pop() {
        build.work.tick()?;
        let id = std::ptr::from_ref(current);
        if done.contains_key(&id) {
            continue;
        }
        if !current.has_param() {
            done.insert(id, current.clone());
            continue;
        }
        if !exit {
            pending.push((current, true));
            match current.view() {
                LevelView::Succ(inner) => pending.push((inner, false)),
                LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                    pending.push((right, false));
                    pending.push((left, false));
                }
                _ => {}
            }
            continue;
        }
        let child = |level: &Level| done[&std::ptr::from_ref(level)].clone();
        let value = match current.view() {
            LevelView::Param(name) => Ok(substitutions
                .get(name)
                .map_or_else(|| current.clone(), |level| (*level).clone())),
            LevelView::Succ(inner) => child(inner).succ(),
            LevelView::Max(left, right) => Level::try_smart_max(child(left), child(right)),
            LevelView::IMax(left, right) => Level::try_smart_imax(child(left), child(right)),
            _ => Ok(current.clone()),
        }
        .map_err(|_| AuxiliaryError::ResourceLimit)?;
        done.insert(id, value);
    }
    Ok(done[&std::ptr::from_ref(level)].clone())
}

/// `MetavarContext.mkBinding` calls `headBeta` on each local's type before
/// abstracting it. This is deliberately local to the Meta-based construction;
/// the C++ `casesOn` construction preserves its binder domains verbatim.
fn meta_locals(build: &mut Build, locals: &[LocalDecl]) -> Result<Vec<LocalDecl>, AuxiliaryError> {
    let mut result = Vec::with_capacity(locals.len());
    for local in locals {
        build.work.tick()?;
        let mut local = local.clone();
        local.type_ = head_beta(build, &local.type_)?;
        result.push(local);
    }
    Ok(result)
}

fn head_beta(build: &mut Build, term: &Expr) -> Result<Expr, AuxiliaryError> {
    let (head, arguments) = spine(build, term)?;
    if arguments.is_empty() {
        return Ok(term.clone());
    }
    let mut body = &head;
    while let ExprNode::MData { expr, .. } = body.node() {
        build.work.tick()?;
        body = expr;
    }
    if !matches!(body.node(), ExprNode::Lam { .. }) {
        return Ok(term.clone());
    }
    let mut consumed = 0;
    while consumed < arguments.len() {
        build.work.tick()?;
        match body.node() {
            ExprNode::Lam { body: next, .. } => {
                body = next;
                consumed += 1;
            }
            ExprNode::MData { expr, .. } => body = expr,
            _ => break,
        }
    }
    // Like `Expr.betaRev`, substitute the initially exposed lambdas together;
    // do not recursively normalize a redex exposed by that substitution.
    let result = body
        .subst_loose(0, &arguments[..consumed])
        .map_err(|_| AuxiliaryError::InvalidTelescope)?;
    Ok(app(result, arguments[consumed..].iter().cloned()))
}

fn meta_close(
    build: &mut Build,
    locals: &[LocalDecl],
    body: Expr,
    lambda: bool,
) -> Result<Expr, AuxiliaryError> {
    let locals = meta_locals(build, locals)?;
    build.close(&locals, body, lambda)
}

fn meta_finish(
    build: &mut Build,
    recursor: &RecursorVal,
    name: Name,
    locals: &[LocalDecl],
    type_: Expr,
    value: Expr,
) -> Result<DefinitionVal, AuxiliaryError> {
    let locals = meta_locals(build, locals)?;
    build.finish(recursor, name, &locals, type_, value)
}

fn spine(build: &mut Build, term: &Expr) -> Result<(Expr, Vec<Expr>), AuxiliaryError> {
    let mut head = term;
    let mut arguments = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        build.work.tick()?;
        arguments.push(a.clone());
        head = f;
    }
    arguments.reverse();
    Ok((head.clone(), arguments))
}

fn product(left_level: &Level, right_level: &Level, left: Expr, right: Expr) -> Expr {
    app(
        Expr::const_(
            Name::from_components(["PProd"]),
            vec![left_level.clone(), right_level.clone()],
        ),
        [left, right],
    )
}

fn product_level(left: &Level, right: &Level) -> Result<Level, AuxiliaryError> {
    let first = Level::try_smart_max(Level::one(), left.clone())
        .map_err(|_| AuxiliaryError::ResourceLimit)?;
    Level::try_smart_max(first, right.clone()).map_err(|_| AuxiliaryError::ResourceLimit)
}

fn history_level(motive: &Level, history: &Level, function: bool) -> Result<Level, AuxiliaryError> {
    let level = product_level(motive, history)?;
    // The pin's inferForallType normalizes its result. Every recursive-field
    // domain belongs to the family universe already included in `history`.
    // A direct PProd application instead retains the smart-instantiated level.
    Ok(if function { level.normalize() } else { level })
}

fn pair(
    left_level: &Level,
    right_level: &Level,
    left_type: Expr,
    right_type: Expr,
    left: Expr,
    right: Expr,
) -> Expr {
    app(
        Expr::const_(
            Name::from_components(["PProd", "mk"]),
            vec![left_level.clone(), right_level.clone()],
        ),
        [left_type, right_type, left, right],
    )
}

fn unit(level: &Level, value: bool) -> Expr {
    Expr::const_(
        Name::from_components(if value {
            vec!["PUnit", "unit"]
        } else {
            vec!["PUnit"]
        }),
        vec![level.clone()],
    )
}

/// The pin packs one child without an extra product and an empty collection
/// using PUnit. This shape is observable when users project recursive history.
fn pack_types(
    build: &mut Build,
    level: &Level,
    mut types: Vec<(Expr, Level)>,
) -> Result<Expr, AuxiliaryError> {
    let Some((mut result, mut result_level)) = types.pop() else {
        return Ok(unit(level, false));
    };
    while let Some((type_, left_level)) = types.pop() {
        build.work.tick()?;
        result = product(&left_level, &result_level, type_, result);
        result_level = product_level(&left_level, &result_level)?;
    }
    Ok(result)
}

fn pack_values(
    build: &mut Build,
    level: &Level,
    mut values: Vec<(Expr, Expr, Level)>,
) -> Result<(Expr, Expr, Level), AuxiliaryError> {
    let Some((mut type_, mut value, mut result_level)) = values.pop() else {
        return Ok((unit(level, false), unit(level, true), level.clone()));
    };
    while let Some((left_type, left, left_level)) = values.pop() {
        build.work.tick()?;
        value = pair(
            &left_level,
            &result_level,
            left_type.clone(),
            type_.clone(),
            left,
            value,
        );
        type_ = product(&left_level, &result_level, left_type, type_);
        result_level = product_level(&left_level, &result_level)?;
    }
    Ok((type_, value, result_level))
}

/// Construct a `below` candidate, including auxiliary nested recursors such as
/// `Tree.rec_1`. `families` must contain the owning family and the inductive
/// type at the major premise's head (which may be an imported nested family).
pub fn below_declaration(
    recursor: &RecursorVal,
    families: &[InductiveVal],
    budget: RecordBudget,
) -> Result<DefinitionVal, AuxiliaryError> {
    if argument_count(recursor)? > budget.max_binders {
        return Err(AuxiliaryError::ResourceLimit);
    }
    let mut build = Build::new(budget, recursor)?;
    let layout = Layout::new(&mut build, recursor, families)?;
    let motives = layout.motives(recursor);
    let mut levels = layout.levels.clone();
    levels[0] = layout
        .result_level
        .clone()
        .succ()
        .map_err(|_| AuxiliaryError::ResourceLimit)?;
    let mut arguments: Vec<_> = layout.locals[..recursor.num_params as usize]
        .iter()
        .map(fv)
        .collect();
    for motive in motives {
        let (params, _) = build.telescope(&motive.type_)?;
        arguments.push(meta_close(
            &mut build,
            &params,
            Expr::sort(layout.result_level.clone()),
            true,
        )?);
    }
    for minor in &layout.locals[layout.minor_start..layout.suffix] {
        let (fields, _) = build.telescope(&minor.type_)?;
        let mut params = Vec::new();
        let mut history = Vec::new();
        for field in fields {
            let (field_args, field_result) = build.telescope(&field.type_)?;
            let (head, _) = spine(&mut build, &field_result)?;
            if motives.iter().any(|motive| head == fv(motive)) {
                let type_ = meta_close(
                    &mut build,
                    &field_args,
                    Expr::sort(layout.result_level.clone()),
                    false,
                )?;
                let replacement = build.local(field.user_name, type_, BinderInfo::Default)?;
                let child = product(
                    &layout.levels[0],
                    &layout.result_level,
                    field_result,
                    app(fv(&replacement), field_args.iter().map(fv)),
                );
                let level = history_level(
                    &layout.levels[0],
                    &layout.result_level,
                    !field_args.is_empty(),
                )?;
                history.push((meta_close(&mut build, &field_args, child, false)?, level));
                params.push(replacement);
            } else {
                params.push(field);
            }
        }
        let history = pack_types(&mut build, &layout.result_level, history)?;
        arguments.push(meta_close(&mut build, &params, history, true)?);
    }
    arguments.extend(layout.locals[layout.suffix..].iter().map(fv));
    let value = app(Expr::const_(recursor.base.name.clone(), levels), arguments);
    meta_finish(
        &mut build,
        recursor,
        layout.below_name.clone(),
        &layout.parameters(),
        Expr::sort(layout.result_level),
        value,
    )
}

/// Construct `brecOn.go` and `brecOn`, in dependency order. Before admitting
/// them, the caller must have admitted every mutual/nested family's `below`.
/// Both definitions are reducible/protected; only `brecOn` is an auxiliary
/// recursor. The returned definitions themselves install none of those tags.
pub fn brec_on_declarations(
    recursor: &RecursorVal,
    families: &[InductiveVal],
    budget: RecordBudget,
) -> Result<[DefinitionVal; 2], AuxiliaryError> {
    if argument_count(recursor)? > budget.max_binders {
        return Err(AuxiliaryError::ResourceLimit);
    }
    let mut build = Build::new(budget, recursor)?;
    let layout = Layout::new(&mut build, recursor, families)?;
    let motives = layout.motives(recursor);
    let prefix: Vec<_> = layout.locals[..layout.minor_start].iter().map(fv).collect();
    let mut belows = Vec::new();
    let mut below_levels = Vec::new();
    let mut functionals = Vec::new();
    for (index, motive) in motives.iter().enumerate() {
        build.work.tick()?;
        let below_name = if let Some(name) = recursor.all.get(index) {
            Name::str(name.clone(), "below")
        } else {
            Name::str(
                recursor.all[0].clone(),
                format!("below_{}", index - recursor.all.len() + 1),
            )
        };
        let below = app(
            Expr::const_(below_name, layout.levels.clone()),
            prefix.iter().cloned(),
        );
        let (mut params, _) = build.telescope(&motive.type_)?;
        let major_type = &params.last().ok_or(AuxiliaryError::InvalidTelescope)?.type_;
        let family_level = major_level(&mut build, families, major_type)?;
        below_levels.push(
            Level::max(family_level, layout.levels[0].clone())
                .map_err(|_| AuxiliaryError::ResourceLimit)?,
        );
        let motive_app = app(fv(motive), params.iter().map(fv));
        let below_app = app(below.clone(), params.iter().map(fv));
        let history = build.local(Name::from_components(["f"]), below_app, BinderInfo::Default)?;
        params.push(history);
        let type_ = meta_close(&mut build, &params, motive_app, false)?;
        functionals.push(build.local(
            Name::str(Name::anonymous(), format!("F_{}", index + 1)),
            type_,
            BinderInfo::Default,
        )?);
        belows.push(below);
    }
    let mut arguments: Vec<_> = layout.locals[..recursor.num_params as usize]
        .iter()
        .map(fv)
        .collect();
    for ((motive, below), below_level) in motives.iter().zip(&belows).zip(&below_levels) {
        let (params, _) = build.telescope(&motive.type_)?;
        let pair_type = product(
            &layout.levels[0],
            below_level,
            app(fv(motive), params.iter().map(fv)),
            app(below.clone(), params.iter().map(fv)),
        );
        arguments.push(meta_close(&mut build, &params, pair_type, true)?);
    }
    for minor in &layout.locals[layout.minor_start..layout.suffix] {
        let (fields, minor_result) = build.telescope(&minor.type_)?;
        let mut params = Vec::new();
        let mut history = Vec::new();
        for field in fields {
            let (field_args, field_result) = build.telescope(&field.type_)?;
            let (head, result_args) = spine(&mut build, &field_result)?;
            if let Some(index) = motives.iter().position(|motive| head == fv(motive)) {
                let pair_type = product(
                    &layout.levels[0],
                    &below_levels[index],
                    field_result,
                    app(belows[index].clone(), result_args),
                );
                let type_ = meta_close(&mut build, &field_args, pair_type, false)?;
                let replacement =
                    build.local(field.user_name, type_.clone(), BinderInfo::Default)?;
                let level = history_level(
                    &layout.levels[0],
                    &below_levels[index],
                    !field_args.is_empty(),
                )?;
                history.push((type_, fv(&replacement), level));
                params.push(replacement);
            } else {
                params.push(field);
            }
        }
        let (head, mut result_args) = spine(&mut build, &minor_result)?;
        let index = motives
            .iter()
            .position(|motive| head == fv(motive))
            .ok_or(AuxiliaryError::InvalidTelescope)?;
        let (history_type, history_value, history_level) =
            pack_values(&mut build, &layout.result_level, history)?;
        result_args.push(history_value.clone());
        let body = pair(
            &layout.levels[0],
            &history_level,
            minor_result,
            history_type,
            app(fv(&functionals[index]), result_args),
            history_value,
        );
        arguments.push(meta_close(&mut build, &params, body, true)?);
    }
    arguments.extend(layout.locals[layout.suffix..].iter().map(fv));
    let mut rec_levels = layout.levels.clone();
    rec_levels[0] = layout.result_level.clone();
    let go_value = app(
        Expr::const_(recursor.base.name.clone(), rec_levels),
        arguments,
    );
    let mut params = layout.parameters();
    params.extend(functionals);
    let main_below = app(
        belows[layout.main].clone(),
        layout.locals[layout.suffix..].iter().map(fv),
    );
    let go_type = product(
        &layout.levels[0],
        &below_levels[layout.main],
        layout.result.clone(),
        main_below,
    );
    let go_name = Name::str(layout.brec_name.clone(), "go");
    let go = meta_finish(
        &mut build,
        recursor,
        go_name.clone(),
        &params,
        go_type,
        go_value,
    )?;
    let go_app = app(Expr::const_(go_name, layout.levels), params.iter().map(fv));
    let value = Expr::proj(Name::from_components(["PProd"]), 0, go_app);
    let result = meta_finish(
        &mut build,
        recursor,
        layout.brec_name,
        &params,
        layout.result,
        value,
    )?;
    Ok([go, result])
}
