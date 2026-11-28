//! Forward simp theorem preprocessing produces ordinary, untrusted theorem
//! candidates. The caller admits every new candidate before registering it.
//! Logical propositions, including conjunctions with their own telescopes,
//! become the equality proofs consumed by the pin's persistent simp entries.
use super::{Meter, SimpSetError, keys};
use crate::lctx::LocalContext;
use fln_core::expr::{Expr, ExprNode, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, ConstantVal, DefinitionSafety, TheoremVal};
use fln_env::environment::Environment;
use fln_kernel::Declaration;
use std::collections::{HashMap, HashSet};

/// An existing proof is selected through its source registration and complete
/// type, never just through an auxiliary-looking declaration name.
pub struct Auxiliary {
    pub declaration: Declaration,
    pub existing: bool,
}

fn unsupported() -> SimpSetError {
    SimpSetError::UnsupportedDeclaration(Name::anonymous())
}

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn constant(value: &str) -> Expr {
    Expr::const_(name(value), Vec::new())
}

fn app(function: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(function, Expr::app)
}

fn equality(level: Level, type_: Expr, lhs: Expr, rhs: Expr) -> Expr {
    app(Expr::const_(name("Eq"), vec![level]), [type_, lhs, rhs])
}

fn prop_equality(lhs: Expr, rhs: Expr) -> Expr {
    equality(Level::one(), Expr::sort(Level::zero()), lhs, rhs)
}

fn scan(expression: &Expr, meter: &mut Meter) -> Result<(), SimpSetError> {
    let mut pending = vec![expression];
    let mut seen = HashSet::new();
    while let Some(expression) = pending.pop() {
        meter.work(1)?;
        if !seen.insert(expression.allocation_identity()) {
            continue;
        }
        match expression.node() {
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::ForallE {
                binder_type, body, ..
            }
            | ExprNode::Lam {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    Ok(())
}

fn application(expression: &Expr, meter: &mut Meter) -> Result<(Expr, Vec<Expr>), SimpSetError> {
    let mut head = expression;
    let mut arguments = Vec::new();
    loop {
        meter.work(1)?;
        match head.node() {
            ExprNode::App { f, a } => {
                arguments.push(a.clone());
                head = f;
            }
            ExprNode::MData { expr, .. } => head = expr,
            _ => break,
        }
    }
    arguments.reverse();
    Ok((head.clone(), arguments))
}

fn is_constant(expression: &Expr, expected: &str, levels: usize) -> bool {
    matches!(expression.node(), ExprNode::Const { name: actual, levels: actual_levels }
        if *actual == name(expected) && actual_levels.len() == levels)
}

fn helper(env: &Environment, label: &str) -> Result<Expr, SimpSetError> {
    match env.find(&name(label)) {
        Some(ConstantInfo::Thm(_)) => Ok(constant(label)),
        Some(ConstantInfo::Axiom(value)) if !value.is_unsafe => Ok(constant(label)),
        Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Safe => {
            Ok(constant(label))
        }
        _ => Err(unsupported()),
    }
}

fn negative(
    env: &Environment,
    proposition: Expr,
    proof: Expr,
    meter: &mut Meter,
) -> Result<(Expr, Expr), SimpSetError> {
    let (head, arguments) = application(&proposition, meter)?;
    if is_constant(&head, "Eq", 1)
        && let [_, lhs, rhs] = arguments.as_slice()
    {
        let opposite = if is_constant(rhs, "Bool.true", 0) {
            Some(("Bool.false", "Bool.of_not_eq_true"))
        } else if is_constant(rhs, "Bool.false", 0) {
            Some(("Bool.true", "Bool.of_not_eq_false"))
        } else {
            None
        };
        if let Some((result, conversion)) = opposite {
            return Ok((
                equality(
                    Level::one(),
                    constant("Bool"),
                    lhs.clone(),
                    constant(result),
                ),
                app(helper(env, conversion)?, [lhs.clone(), proof]),
            ));
        }
    }
    Ok((
        prop_equality(proposition.clone(), constant("False")),
        app(helper(env, "eq_false")?, [proposition, proof]),
    ))
}

fn close(
    mut type_: Expr,
    mut value: Expr,
    locals: &LocalContext,
    meter: &mut Meter,
) -> Result<(Expr, Expr), SimpSetError> {
    for local in locals.decls().iter().rev() {
        scan(&type_, meter)?;
        scan(&value, meter)?;
        type_ = type_
            .abstract_fvar(&local.id, 0)
            .map_err(|_| SimpSetError::Limit)?;
        value = value
            .abstract_fvar(&local.id, 0)
            .map_err(|_| SimpSetError::Limit)?;
        type_ = Expr::forall_e(
            local.user_name.clone(),
            local.type_.clone(),
            type_,
            local.binder_info,
        );
        value = Expr::lam(
            local.user_name.clone(),
            local.type_.clone(),
            value,
            local.binder_info,
        );
    }
    if [&type_, &value].into_iter().any(|expression| {
        expression.has_fvar()
            || expression.has_expr_mvar()
            || expression.has_level_mvar()
            || expression.has_loose_bvars()
    }) {
        return Err(SimpSetError::Malformed);
    }
    Ok((type_, value))
}

struct Pending {
    type_: Expr,
    value: Expr,
    locals: LocalContext,
    auxiliary_required: bool,
}

fn leaves(
    env: &Environment,
    base: &ConstantVal,
    meter: &mut Meter,
) -> Result<Vec<(Expr, Expr)>, SimpSetError> {
    let levels = base
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let mut pending = vec![Pending {
        type_: base.type_.clone(),
        value: Expr::const_(base.name.clone(), levels),
        locals: LocalContext::new(),
        auxiliary_required: false,
    }];
    let mut result = Vec::new();
    while let Some(mut current) = pending.pop() {
        loop {
            meter.work(1)?;
            current.type_ = keys::reduce_type(env, &current.type_, &current.locals, meter)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = current.type_.node()
            else {
                break;
            };
            if current.locals.len() >= 4096 {
                return Err(SimpSetError::Limit);
            }
            let id = FVarId(Name::num(
                name("_fln_simp_preprocess"),
                current.locals.len() as u64,
            ));
            let variable = Expr::fvar(id.clone());
            current
                .locals
                .add_param(id, binder_name.clone(), binder_type.clone(), *binder_info);
            scan(body, meter)?;
            current.type_ = body
                .subst_loose(0, std::slice::from_ref(&variable))
                .map_err(|_| SimpSetError::Limit)?;
            current.value = Expr::app(current.value, variable);
        }
        let (head, arguments) = application(&current.type_, meter)?;
        if is_constant(&head, "And", 0)
            && let [left, right] = arguments.as_slice()
        {
            // A stack visits the left leaf first, as the pin's list append.
            pending.push(Pending {
                type_: right.clone(),
                value: Expr::proj(name("And"), 1, current.value.clone()),
                locals: current.locals.clone(),
                auxiliary_required: true,
            });
            pending.push(Pending {
                type_: left.clone(),
                value: Expr::proj(name("And"), 0, current.value),
                locals: current.locals,
                auxiliary_required: true,
            });
            continue;
        }
        let (type_, value) = if is_constant(&head, "Eq", 1) && arguments.len() == 3 {
            if !current.auxiliary_required {
                return Ok(Vec::new());
            }
            (current.type_, current.value)
        } else if is_constant(&head, "Iff", 0) && arguments.len() == 2 {
            (
                prop_equality(arguments[0].clone(), arguments[1].clone()),
                app(
                    helper(env, "propext")?,
                    [arguments[0].clone(), arguments[1].clone(), current.value],
                ),
            )
        } else if is_constant(&head, "Ne", 1) && arguments.len() == 3 {
            let ExprNode::Const { levels, .. } = head.node() else {
                unreachable!()
            };
            let proposition = equality(
                levels[0].clone(),
                arguments[0].clone(),
                arguments[1].clone(),
                arguments[2].clone(),
            );
            negative(env, proposition, current.value, meter)?
        } else if is_constant(&head, "Not", 0) && arguments.len() == 1 {
            negative(env, arguments[0].clone(), current.value, meter)?
        } else {
            (
                prop_equality(current.type_.clone(), constant("True")),
                app(helper(env, "eq_true")?, [current.type_, current.value]),
            )
        };
        if result.len() >= 4096 {
            return Err(SimpSetError::Limit);
        }
        result.push(close(type_, value, &current.locals, meter)?);
    }
    Ok(result)
}

fn owned_cache(
    env: &Environment,
    base: &ConstantVal,
    meter: &mut Meter,
) -> Result<HashMap<Expr, TheoremVal>, SimpSetError> {
    use super::super::{JournalEntry, PROOF_SNAPSHOT_MAGIC, decode_entry, descriptor};
    let mut cache = HashMap::new();
    let Some(state) = env.extension(&descriptor().name) else {
        return Ok(cache);
    };
    if state.descriptor != descriptor() {
        return Err(SimpSetError::Malformed);
    }
    for (index, row) in state.entries().enumerate() {
        meter.work(1)?;
        if !row.payload.starts_with(PROOF_SNAPSHOT_MAGIC) {
            continue;
        }
        meter.work(row.payload.len())?;
        let JournalEntry::Add { entry, .. } = decode_entry(&row.payload, index)? else {
            return Err(SimpSetError::Malformed);
        };
        if entry.declaration != base.name {
            continue;
        }
        let proof = entry.proof.ok_or(SimpSetError::Malformed)?;
        let Some(ConstantInfo::Thm(theorem)) = env.find(&proof) else {
            continue;
        };
        if theorem.base.level_params == base.level_params {
            scan(&theorem.base.type_, meter)?;
            cache
                .entry(theorem.base.type_.clone())
                .or_insert_with(|| theorem.clone());
        }
    }
    Ok(cache)
}

/// Preprocess forward logical simp rules. Unsupported proof infrastructure
/// preserves the existing source simplifier and its explicit export refusal.
/// No candidate is published here, including when a later leaf exhausts fuel.
pub fn prepare_auxiliaries(
    env: &Environment,
    declaration: &Name,
) -> Result<Vec<Auxiliary>, SimpSetError> {
    let info = env
        .find(declaration)
        .ok_or_else(|| SimpSetError::UnknownDeclaration(declaration.clone()))?;
    match info {
        ConstantInfo::Thm(_) => {}
        ConstantInfo::Axiom(value) if !value.is_unsafe => {}
        ConstantInfo::Defn(value) if value.safety == DefinitionSafety::Safe => {}
        _ => return Ok(Vec::new()),
    }
    let base = info.constant_val();
    let mut meter = Meter {
        remaining: 1 << 20,
        bytes: 0,
    };
    let prepared = (|| {
        if !keys::is_proposition(env, &base.type_, &mut meter)? {
            return Ok(Vec::new());
        }
        let leaves = leaves(env, base, &mut meter)?;
        if leaves.is_empty() {
            return Ok(Vec::new());
        }
        let mut cache = owned_cache(env, base, &mut meter)?;
        let mut next_index = 1u64;
        let mut result = Vec::new();
        for (type_, value) in leaves {
            meter.work(1)?;
            if let Some(theorem) = cache.get(&type_) {
                result.push(Auxiliary {
                    declaration: Declaration::Thm(theorem.clone()),
                    existing: true,
                });
                continue;
            }
            let auxiliary = loop {
                meter.work(1)?;
                let candidate = Name::str(declaration.clone(), format!("_simp_{next_index}"));
                next_index = next_index.checked_add(1).ok_or(SimpSetError::Limit)?;
                if !env.contains(&candidate) {
                    break candidate;
                }
            };
            let theorem = TheoremVal {
                base: ConstantVal {
                    name: auxiliary.clone(),
                    level_params: base.level_params.clone(),
                    type_: type_.clone(),
                },
                value,
                all: vec![auxiliary],
            };
            cache.insert(type_, theorem.clone());
            result.push(Auxiliary {
                declaration: Declaration::Thm(theorem),
                existing: false,
            });
        }
        Ok(result)
    })();
    match prepared {
        Err(SimpSetError::UnsupportedDeclaration(_)) => Ok(Vec::new()),
        result => result,
    }
}
