//! Source-side counterpart of the runtime's checked WF compiler equations.
//! This changes dependency selection only. Both checking seats still receive
//! the original declaration, and runtime authority is checked independently.
use super::*;
use fln_env::constants::{ConstantVal, DefinitionSafety};
use fln_env::environment::Environment;

#[cfg(test)]
mod tests;

const EQUATIONS: [(&str, &str, &str); 5] = [
    (
        "WellFounded.fix",
        "WellFounded.fixC",
        "WellFounded.fix_eq_fixC",
    ),
    ("Acc.rec", "Acc.recC", "Acc.rec_eq_recC"),
    ("Acc.ndrec", "Acc.ndrecC", "Acc.ndrec_eq_ndrecC"),
    ("Acc.ndrecOn", "Acc.ndrecOnC", "Acc.ndrecOn_eq_ndrecOnC"),
    (
        "WellFounded.fixF",
        "WellFounded.fixFC",
        "WellFounded.fixF_eq_fixFC",
    ),
];

#[derive(Clone, Default)]
pub(super) struct Cache {
    // None: unqueried. Some(false): absent. Some(true): fully validated.
    // Fixed-size staging allocates no new cache table and cannot grow with
    // unrelated source constants. Each Dependencies owns its immutable env.
    equations: [Option<bool>; EQUATIONS.len()],
    equality_checked: bool,
}

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn equation_index(source: &Name) -> Option<usize> {
    static SOURCES: std::sync::OnceLock<[Name; EQUATIONS.len()]> = std::sync::OnceLock::new();
    SOURCES
        .get_or_init(|| EQUATIONS.map(|(from, _, _)| n(from)))
        .iter()
        .position(|candidate| source == candidate)
}

pub(super) fn recognizes(source: &Name) -> bool {
    equation_index(source).is_some()
}

fn invalid(theorem: &Name, reason: &'static str) -> NatDefinitionElabError {
    failure(SourceInferenceError::NoncomputableJournal(
        crate::noncomputable::NoncomputableError::CompilerEquation {
            theorem: theorem.clone(),
            reason,
        },
    ))
}

fn capacity<T>(values: &mut Vec<T>, additional: usize) -> Result<(), NatDefinitionElabError> {
    values
        .try_reserve(additional)
        .map_err(|_| failure(SourceInferenceError::ResourceLimit))
}

impl Cache {
    /// Stage successful lookups. The caller commits this copy only after the
    /// terminal dependency passes its ordinary noncomputability check too.
    pub(super) fn resolve(
        &self,
        context: &mut Context,
        environment: &Environment,
        implementations: &ImplementedByTable,
        externs: &ExternTable,
        requested: &Name,
    ) -> Result<(Name, Self), NatDefinitionElabError> {
        let mut staged = self.clone();
        let mut current = requested.clone();
        let mut seen = HashSet::new();
        loop {
            context.tick()?;
            // Explicit implementations retain priority at every stage. Their
            // complete attribute chains have already been validated and metered.
            if let Some(terminal) = implementations.implementation(&current) {
                current = terminal.clone();
            }
            seen.try_reserve(1)
                .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
            if !seen.insert(current.clone()) {
                return Err(invalid(&current, "cyclic executable replacement chain"));
            }
            let Some(index) = equation_index(&current) else {
                break;
            };
            // Even malformed companion linkage must reach the ordinary checks,
            // rather than escaping through an otherwise valid library equation.
            if externs.get(&current).is_some()
                || environment.contains(&Name::str(current.clone(), "_unsafe_rec"))
            {
                break;
            }
            let (_, target, theorem) = EQUATIONS[index];
            let target = n(target);
            let theorem = n(theorem);
            let available = match staged.equations[index] {
                Some(available) => available,
                None => {
                    let available = if let Some(info) = environment.find(&theorem) {
                        let ConstantInfo::Thm(proof) = info else {
                            return Err(invalid(&theorem, "expected an admitted equality theorem"));
                        };
                        validate_equation(context, environment, &current, &target, &proof.base)?;
                        if !staged.equality_checked {
                            if !canonical_equality(context, environment)? {
                                return Err(invalid(&theorem, "canonical equality is unavailable"));
                            }
                            staged.equality_checked = true;
                        }
                        true
                    } else {
                        false
                    };
                    context.tick()?;
                    staged.equations[index] = Some(available);
                    available
                }
            };
            if !available {
                break;
            }
            current = target;
        }
        Ok((current, staged))
    }
}

fn validate_equation(
    context: &mut Context,
    environment: &Environment,
    source: &Name,
    target: &Name,
    theorem: &ConstantVal,
) -> Result<(), NatDefinitionElabError> {
    let mut arguments = Vec::new();
    let mut head = &theorem.type_;
    while let ExprNode::App { f, a } = head.node() {
        context.tick()?;
        if arguments.len() == 3 {
            return Err(invalid(&theorem.name, "expected a constant equality"));
        }
        capacity(&mut arguments, 1)?;
        arguments.push(a);
        head = f;
    }
    context.tick()?;
    if !matches!(head.node(), ExprNode::Const { name, levels }
        if name == &n("Eq") && levels.len() == 1)
        || arguments.len() != 3
    {
        return Err(invalid(&theorem.name, "expected a constant equality"));
    }
    arguments.reverse();
    let (
        ExprNode::Const { name: from, levels },
        ExprNode::Const {
            name: to,
            levels: other,
        },
    ) = (arguments[1].node(), arguments[2].node())
    else {
        return Err(invalid(&theorem.name, "the endpoints are not constants"));
    };
    if from != source
        || to != target
        || levels != other
        || levels.len() != theorem.level_params.len()
    {
        return Err(invalid(&theorem.name, "different endpoints or universes"));
    }
    let mut parameters = HashSet::new();
    for parameter in &theorem.level_params {
        context.tick()?;
        parameters
            .try_reserve(1)
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        if !parameters.insert(Level::param(parameter.clone())) {
            return Err(invalid(&theorem.name, "a universe parameter is repeated"));
        }
    }
    for level in levels {
        context.tick()?;
        if !parameters.remove(level) {
            return Err(invalid(
                &theorem.name,
                "universes are not a parameter bijection",
            ));
        }
    }
    for endpoint in [source, target] {
        context.tick()?;
        let Some(info) = environment.find(endpoint) else {
            return Err(invalid(&theorem.name, "an endpoint is absent"));
        };
        let safe = match info {
            ConstantInfo::Defn(definition) => definition.safety == DefinitionSafety::Safe,
            ConstantInfo::Rec(recursor) => {
                endpoint == source && source == &n("Acc.rec") && !recursor.is_unsafe
            }
            _ => false,
        };
        let base = info.constant_val();
        if !safe || base.level_params.len() != levels.len() {
            return Err(invalid(
                &theorem.name,
                "unsupported endpoint safety or universe arity",
            ));
        }
        let signature = crate::universe::parameters::instantiate(
            || context.tick(),
            || invalid(&theorem.name, "endpoint universe substitution failed"),
            &base.type_,
            &base.level_params,
            levels,
        )?;
        if !same_expression(context, &signature, arguments[0])? {
            return Err(invalid(&theorem.name, "endpoint interface mismatch"));
        }
    }
    Ok(())
}

/// Compare the checked de Bruijn interfaces without reducing definitions or
/// erasing domains. Binder labels/info and transparent metadata are irrelevant.
fn same_expression(
    context: &mut Context,
    actual: &Expr,
    expected: &Expr,
) -> Result<bool, NatDefinitionElabError> {
    let mut pending = vec![(actual, expected)];
    let mut seen = HashSet::new();
    while let Some((a, b)) = pending.pop() {
        context.tick()?;
        let key = (a.allocation_identity(), b.allocation_identity());
        if key.0 == key.1 || seen.contains(&key) {
            continue;
        }
        seen.try_reserve(1)
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        seen.insert(key);
        capacity(&mut pending, 2)?;
        match (a.node(), b.node()) {
            (ExprNode::MData { expr, .. }, _) => pending.push((expr, b)),
            (_, ExprNode::MData { expr, .. }) => pending.push((a, expr)),
            (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
            (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) if a == b => {}
            (
                ExprNode::Const {
                    name: a,
                    levels: al,
                },
                ExprNode::Const {
                    name: b,
                    levels: bl,
                },
            ) if a == b && al == bl => {}
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                pending.push((aa, ba));
                pending.push((af, bf));
            }
            (
                ExprNode::ForallE {
                    binder_type: at,
                    body: ab,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: bt,
                    body: bb,
                    ..
                },
            )
            | (
                ExprNode::Lam {
                    binder_type: at,
                    body: ab,
                    ..
                },
                ExprNode::Lam {
                    binder_type: bt,
                    body: bb,
                    ..
                },
            ) => {
                pending.push((ab, bb));
                pending.push((at, bt));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn same_base(
    context: &mut Context,
    actual: &ConstantVal,
    expected: &ConstantVal,
) -> Result<bool, NatDefinitionElabError> {
    context.tick()?;
    Ok(actual.name == expected.name
        && actual.level_params == expected.level_params
        && same_expression(context, &actual.type_, &expected.type_)?)
}

/// Authenticate the same complete Eq/Eq.refl/Eq.rec model as runtime selection.
/// A different inductive spelled Eq must not authorize executable replacement.
fn canonical_equality(
    context: &mut Context,
    environment: &Environment,
) -> Result<bool, NatDefinitionElabError> {
    let Declaration::Inductive(model) = crate::seed::eq_seed_declaration() else {
        unreachable!("the equality seed is a fixed inductive block");
    };
    for expected in &model.types {
        context.tick()?;
        let Some(ConstantInfo::Induct(actual)) = environment.find(&expected.base.name) else {
            return Ok(false);
        };
        if actual.num_params != expected.num_params
            || actual.num_indices != expected.num_indices
            || actual.all != expected.all
            || actual.ctors != expected.ctors
            || actual.num_nested != expected.num_nested
            || actual.is_rec != expected.is_rec
            || actual.is_unsafe != expected.is_unsafe
            || actual.is_reflexive != expected.is_reflexive
            || !same_base(context, &actual.base, &expected.base)?
        {
            return Ok(false);
        }
    }
    for expected in &model.ctors {
        context.tick()?;
        let Some(ConstantInfo::Ctor(actual)) = environment.find(&expected.base.name) else {
            return Ok(false);
        };
        if actual.induct != expected.induct
            || actual.cidx != expected.cidx
            || actual.num_params != expected.num_params
            || actual.num_fields != expected.num_fields
            || actual.is_unsafe != expected.is_unsafe
            || !same_base(context, &actual.base, &expected.base)?
        {
            return Ok(false);
        }
    }
    for expected in &model.recursors {
        context.tick()?;
        let Some(ConstantInfo::Rec(actual)) = environment.find(&expected.base.name) else {
            return Ok(false);
        };
        if actual.all != expected.all
            || actual.num_params != expected.num_params
            || actual.num_indices != expected.num_indices
            || actual.num_motives != expected.num_motives
            || actual.num_minors != expected.num_minors
            || actual.k != expected.k
            || actual.is_unsafe != expected.is_unsafe
            || actual.rules.len() != expected.rules.len()
            || !same_base(context, &actual.base, &expected.base)?
        {
            return Ok(false);
        }
        for (a, b) in actual.rules.iter().zip(&expected.rules) {
            context.tick()?;
            if a.ctor != b.ctor
                || a.nfields != b.nfields
                || !same_expression(context, &a.rhs, &b.rhs)?
            {
                return Ok(false);
            }
        }
    }
    Ok(true)
}
