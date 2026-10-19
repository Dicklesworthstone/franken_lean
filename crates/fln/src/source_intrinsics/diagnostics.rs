//! Native diagnostics require both their checked logical meaning and the
//! exact selected extern. A familiar name or a logical default alone never
//! authorizes reporting a message. Reducibility hints and binder labels are
//! not execution semantics; types, bodies and the admitted data family are.
use super::*;
use fln_core::level::Level;

fn c(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_components(label.split('.')), levels)
}
fn b(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed diagnostic contract binder")
}
fn bind(domain: Expr, body: Expr, info: BinderInfo, lambda: bool) -> Expr {
    if lambda {
        Expr::lam(Name::anonymous(), domain, body, info)
    } else {
        Expr::forall_e(Name::anonymous(), domain, body, info)
    }
}

/// Definitions may have different inlining/reducibility heights after native
/// source checking. Those do not alter these closed terms. This comparison
/// does not unfold a user definition or accept a different implementation.
/// `fun {α} … => body` respelled `fun α … => body`; every other node is unchanged.
fn with_explicit_outer_binder(value: &Expr) -> Expr {
    match value.node() {
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            ..
        } => Expr::lam(
            binder_name.clone(),
            binder_type.clone(),
            body.clone(),
            BinderInfo::Default,
        ),
        _ => value.clone(),
    }
}

fn definition_matches(
    comparison: &mut Comparison<'_>,
    actual: &DefinitionVal,
    type_: &Expr,
    value: &Expr,
) -> Result<bool, IngressError> {
    Ok(actual.safety == DefinitionSafety::Safe
        && actual.all == [actual.base.name.clone()]
        && comparison.expression(&actual.base.type_, type_)?
        && comparison.expression(&actual.value, value)?)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PanicDefault {
    Projection,
    SeedAlias,
}

impl PanicDefault {
    fn label(self) -> &'static str {
        match self {
            Self::Projection => "Inhabited.default",
            Self::SeedAlias => "default",
        }
    }

    fn dependencies(self) -> &'static [&'static str] {
        match self {
            Self::Projection => &["Inhabited.default"],
            Self::SeedAlias => &["Inhabited.default", "default"],
        }
    }
}

/// The pin exports `default` as an alias, not a declaration: its panic body
/// names `Inhabited.default` directly. The source seed also has a checked
/// forwarding definition called `default`. Recognize exactly those two bodies
/// and validate only the helper chain actually selected by the body. In
/// particular, an unrelated declaration named `default` cannot authorize or
/// prevent execution of the imported projection form.
fn panic_default(
    comparison: &mut Comparison<'_>,
    actual: &DefinitionVal,
) -> Result<Option<PanicDefault>, IngressError> {
    let [universe] = actual.base.level_params.as_slice() else {
        return Ok(None);
    };
    let u = Level::param(universe.clone());
    let telescope = |result, lambda| {
        bind(
            Expr::sort(u.clone()),
            bind(
                Expr::app(c("Inhabited", vec![u.clone()]), b(0)),
                bind(c("String", vec![]), result, BinderInfo::Default, lambda),
                BinderInfo::InstImplicit,
                lambda,
            ),
            BinderInfo::Implicit,
            lambda,
        )
    };
    let type_ = telescope(b(2), false);
    for model in [PanicDefault::Projection, PanicDefault::SeedAlias] {
        let value = Expr::app(Expr::app(c(model.label(), vec![u.clone()]), b(2)), b(1));
        if definition_matches(comparison, actual, &type_, &telescope(value, true))? {
            return Ok(Some(model));
        }
    }
    Ok(None)
}

pub(crate) fn panic_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let requested = Name::from_components(["panicCore"]);
    if !extern_attribute_matches(environment, &requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    let unsupported = || IngressError::UnsupportedNode {
        kind: "native panicCore differs from its checked logical contract",
    };
    let Some(ConstantInfo::Defn(actual)) = environment.find(&requested) else {
        return Err(unsupported());
    };
    let mut comparison = Comparison { visited, limits };
    let Some(model) = panic_default(&mut comparison, actual)? else {
        return Err(unsupported());
    };
    if !comparison.declaration(
        environment,
        fln_elab::seed::inhabited::inhabited_seed_declaration(),
    )? {
        return Err(unsupported());
    }
    for &label in model.dependencies() {
        let Declaration::Defn(expected) =
            fln_elab::seed::inhabited::default_seed_declaration(label == "Inhabited.default")
        else {
            unreachable!("fixed default model")
        };
        let Some(ConstantInfo::Defn(actual)) = environment.find(&expected.base.name) else {
            return Err(unsupported());
        };
        if actual.base.level_params != expected.base.level_params {
            return Err(unsupported());
        }
        let seed_form = definition_matches(
            &mut comparison,
            actual,
            &expected.base.type_,
            &expected.value,
        )?;
        // The pin's structure projection (`Init.Prelude`'s `Inhabited.default`) binds its
        // parameter `α` with default binder info in the value while the type keeps it
        // implicit; the seed's value marks it implicit. Binder info is not logical content,
        // so both spellings of the same projection satisfy the contract
        // (fln-panic-contract-seed-regression-q8iy).
        if !seed_form
            && !(label == "Inhabited.default"
                && definition_matches(
                    &mut comparison,
                    actual,
                    &expected.base.type_,
                    &with_explicit_outer_binder(&expected.value),
                )?)
        {
            return Err(unsupported());
        }
    }
    for &label in model.dependencies() {
        check_selected_extern_attribute(
            environment,
            &Name::from_components(label.split('.')),
            externs,
            visited,
            limits,
        )?;
    }
    Ok(true)
}

/// A trace is effectful only for the exact checked logical continuation and
/// selected native extern. Unit's concrete runtime shape is checked at ingress.
pub(crate) fn trace_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<Option<Expr>, IngressError> {
    let requested = Name::from_components(["dbgTrace"]);
    if !extern_attribute_matches(environment, &requested, true, externs, visited, limits)? {
        return Ok(None);
    }
    let unsupported = || IngressError::UnsupportedNode {
        kind: "native dbgTrace differs from its checked logical contract",
    };
    let Some(ConstantInfo::Defn(actual)) = environment.find(&requested) else {
        return Err(unsupported());
    };
    let [universe] = actual.base.level_params.as_slice() else {
        return Err(unsupported());
    };
    let u = Level::param(universe.clone());
    let alpha_sort = Expr::sort(Level::succ(u).map_err(|_| unsupported())?);
    let unit_types = [c("Unit", vec![]), c("PUnit", vec![Level::one()])];
    let unit_values = [("Unit.unit", vec![]), ("PUnit.unit", vec![Level::one()])];
    let mut selected = None;
    {
        let mut comparison = Comparison { visited, limits };
        for unit in unit_types {
            let telescope = |result, lambda| {
                bind(
                    alpha_sort.clone(),
                    bind(
                        c("String", vec![]),
                        bind(
                            Expr::forall_e(
                                Name::anonymous(),
                                unit.clone(),
                                b(2),
                                BinderInfo::Default,
                            ),
                            result,
                            BinderInfo::Default,
                            lambda,
                        ),
                        BinderInfo::Default,
                        lambda,
                    ),
                    BinderInfo::Implicit,
                    lambda,
                )
            };
            for (label, levels) in &unit_values {
                let constructor = Name::from_components(label.split('.'));
                let dependencies = match environment.find(&constructor) {
                    Some(ConstantInfo::Ctor(_)) => vec![constructor.clone()],
                    Some(ConstantInfo::Defn(alias)) if *label == "Unit.unit" => {
                        let target = Name::from_components(["PUnit", "unit"]);
                        if !alias.base.level_params.is_empty()
                            || !matches!(environment.find(&target), Some(ConstantInfo::Ctor(_)))
                            || !definition_matches(
                                &mut comparison,
                                alias,
                                &unit,
                                &c("PUnit.unit", vec![Level::one()]),
                            )?
                        {
                            continue;
                        }
                        vec![constructor.clone(), target]
                    }
                    _ => continue,
                };
                let value = Expr::app(b(0), c(label, levels.clone()));
                if definition_matches(
                    &mut comparison,
                    actual,
                    &telescope(b(2), false),
                    &telescope(value, true),
                )? {
                    selected = Some((unit.clone(), dependencies));
                    break;
                }
            }
            if selected.is_some() {
                break;
            }
        }
    }
    let (unit, dependencies) = selected.ok_or_else(unsupported)?;
    for dependency in dependencies {
        check_selected_extern_attribute(environment, &dependency, externs, visited, limits)?;
    }
    Ok(Some(unit))
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_env::constants::{ConstantVal, ReducibilityHints};

    fn candidate(target: &str) -> DefinitionVal {
        let name = Name::from_components(["panicCore"]);
        let universe = Name::from_components(["u"]);
        let u = Level::param(universe.clone());
        let telescope = |body, lambda| {
            bind(
                Expr::sort(u.clone()),
                bind(
                    Expr::app(c("Inhabited", vec![u.clone()]), b(0)),
                    bind(c("String", vec![]), body, BinderInfo::Default, lambda),
                    BinderInfo::InstImplicit,
                    lambda,
                ),
                BinderInfo::Implicit,
                lambda,
            )
        };
        DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: vec![universe],
                type_: telescope(b(2), false),
            },
            value: telescope(
                Expr::app(Expr::app(c(target, vec![u.clone()]), b(2)), b(1)),
                true,
            ),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name],
        }
    }

    fn recognize(candidate: &DefinitionVal) -> Option<PanicDefault> {
        panic_default(
            &mut Comparison {
                visited: &mut 0,
                limits: IngressLimits::default(),
            },
            candidate,
        )
        .unwrap()
    }

    #[test]
    fn imported_projection_does_not_require_a_seed_only_alias() {
        let model = recognize(&candidate("Inhabited.default")).unwrap();
        assert_eq!(model, PanicDefault::Projection);
        assert_eq!(model.dependencies(), &["Inhabited.default"]);
    }

    #[test]
    fn seed_forwarder_still_requires_both_checked_helpers() {
        let model = recognize(&candidate("default")).unwrap();
        assert_eq!(model, PanicDefault::SeedAlias);
        assert_eq!(model.dependencies(), &["Inhabited.default", "default"]);
    }

    #[test]
    fn names_safety_universe_arity_and_bodies_remain_checked() {
        assert_eq!(recognize(&candidate("User.default")), None);
        assert_eq!(recognize(&candidate("User.Inhabited.default")), None);
        let original = candidate("Inhabited.default");
        let mut changed = original.clone();
        changed.safety = DefinitionSafety::Unsafe;
        assert_eq!(recognize(&changed), None);
        let mut changed = original.clone();
        changed.all.clear();
        assert_eq!(recognize(&changed), None);
        let mut changed = original.clone();
        changed.base.level_params.push(Name::from_components(["v"]));
        assert_eq!(recognize(&changed), None);
        let mut changed = original.clone();
        changed.base.type_ = c("Nat", vec![]);
        assert_eq!(recognize(&changed), None);
        let mut changed = original;
        changed.value = c("Inhabited.default", vec![Level::one()]);
        assert_eq!(recognize(&changed), None);
    }

    #[test]
    fn recognizing_either_body_is_metered() {
        for label in ["Inhabited.default", "default"] {
            let limits = IngressLimits {
                max_nodes: 0,
                ..IngressLimits::default()
            };
            assert!(
                panic_default(
                    &mut Comparison {
                        visited: &mut 0,
                        limits,
                    },
                    &candidate(label),
                )
                .is_err()
            );
        }
    }
}
