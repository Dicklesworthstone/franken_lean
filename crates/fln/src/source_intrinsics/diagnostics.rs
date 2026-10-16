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
    let [universe] = actual.base.level_params.as_slice() else {
        return Err(unsupported());
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
    let value = Expr::app(Expr::app(c("default", vec![u.clone()]), b(2)), b(1));
    let mut comparison = Comparison { visited, limits };
    if !definition_matches(
        &mut comparison,
        actual,
        &telescope(b(2), false),
        &telescope(value, true),
    )? || !comparison.declaration(
        environment,
        fln_elab::seed::inhabited::inhabited_seed_declaration(),
    )? {
        return Err(unsupported());
    }
    for qualified in [false, true] {
        let Declaration::Defn(expected) =
            fln_elab::seed::inhabited::default_seed_declaration(qualified)
        else {
            unreachable!("fixed default model")
        };
        let Some(ConstantInfo::Defn(actual)) = environment.find(&expected.base.name) else {
            return Err(unsupported());
        };
        if actual.base.level_params != expected.base.level_params
            || !definition_matches(
                &mut comparison,
                actual,
                &expected.base.type_,
                &expected.value,
            )?
        {
            return Err(unsupported());
        }
    }
    for label in ["Inhabited.default", "default"] {
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
