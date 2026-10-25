//! Fixed de Bruijn models from Init.Core and Init.Prelude at the pinned epoch.
//! Universe labels come from each checked telescope; their positions, kinds,
//! constructors, rule bodies and dependencies are all compared explicitly.
use super::*;
use fln_core::level::Level;
use fln_env::constants::{RecursorRule, RecursorVal};

pub(super) fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn c(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(label), levels)
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed Thunk model binder")
}

fn app(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn pi(domain: Expr, body: Expr, info: BinderInfo) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, info)
}

fn lam(domain: Expr, body: Expr, info: BinderInfo) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, info)
}

fn explicit(domain: Expr, body: Expr) -> Expr {
    pi(domain, body, BinderInfo::Default)
}

fn unit() -> Expr {
    c("Unit", vec![])
}

fn family_type(u: &Level, alpha: Expr) -> Expr {
    Expr::app(c("Thunk", vec![u.clone()]), alpha)
}

fn callback(alpha: Expr) -> Expr {
    explicit(unit(), alpha)
}

fn base(label: &str, universes: &[Name], type_: Expr) -> ConstantVal {
    ConstantVal {
        name: name(label),
        level_params: universes.to_vec(),
        type_,
    }
}

pub(super) fn family(environment: &Environment) -> Option<Vec<ConstantInfo>> {
    let family = environment.find(&name("Thunk"))?.constant_val();
    let [parameter] = family.level_params.as_slice() else {
        return None;
    };
    let u = Level::param(parameter.clone());
    let sort = Expr::sort(u.clone().succ().ok()?);
    let rec = environment.find(&name("Thunk.rec"))?.constant_val();
    let [result, parameter] = rec.level_params.as_slice() else {
        return None;
    };
    let ru = Level::param(parameter.clone());
    let rv = Level::param(result.clone());
    let rsort = Expr::sort(ru.clone().succ().ok()?);
    let motive = explicit(family_type(&ru, b(0)), Expr::sort(rv));
    let minor = explicit(
        callback(b(2)),
        Expr::app(b(1), app(c("Thunk.mk", vec![ru.clone()]), [b(2), b(0)])),
    );
    let rec_type = pi(
        rsort.clone(),
        pi(
            motive.clone(),
            explicit(
                minor.clone(),
                explicit(family_type(&ru, b(2)), Expr::app(b(2), b(0))),
            ),
            BinderInfo::Implicit,
        ),
        BinderInfo::Implicit,
    );
    let rule = lam(
        rsort,
        lam(
            motive,
            lam(
                minor,
                lam(callback(b(3)), Expr::app(b(1), b(0)), BinderInfo::Default),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    Some(vec![
        ConstantInfo::Induct(InductiveVal {
            base: base(
                "Thunk",
                &family.level_params,
                explicit(sort.clone(), sort.clone()),
            ),
            num_params: 1,
            num_indices: 0,
            all: vec![name("Thunk")],
            ctors: vec![name("Thunk.mk")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
        ConstantInfo::Ctor(ConstructorVal {
            base: base(
                "Thunk.mk",
                &family.level_params,
                pi(
                    sort,
                    explicit(callback(b(1)), family_type(&u, b(1))),
                    BinderInfo::Implicit,
                ),
            ),
            induct: name("Thunk"),
            cidx: 0,
            num_params: 1,
            num_fields: 1,
            is_unsafe: false,
        }),
        ConstantInfo::Rec(RecursorVal {
            base: base("Thunk.rec", &rec.level_params, rec_type),
            all: vec![name("Thunk")],
            num_params: 1,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: name("Thunk.mk"),
                nfields: 1,
                rhs: rule,
            }],
            k: false,
            is_unsafe: false,
        }),
    ])
}

fn definition_matches(
    comparison: &mut Comparison<'_>,
    actual: &DefinitionVal,
    type_: &Expr,
    value: &Expr,
) -> Result<bool, IngressError> {
    // Reducibility heights and binder labels do not grant runtime behavior.
    // Every other logical node, safety bit and member name still must match.
    Ok(actual.safety == DefinitionSafety::Safe
        && actual.all == [actual.base.name.clone()]
        && comparison.expression(&actual.base.type_, type_)?
        && comparison.expression(&actual.value, value)?)
}

pub(super) fn unit_matches(
    environment: &Environment,
    comparison: &mut Comparison<'_>,
) -> Result<bool, IngressError> {
    let Some(ConstantInfo::Induct(family)) = environment.find(&name("PUnit")) else {
        return Ok(false);
    };
    let [parameter] = family.base.level_params.as_slice() else {
        return Ok(false);
    };
    let u = Level::param(parameter.clone());
    let expected = ConstantInfo::Induct(InductiveVal {
        base: base("PUnit", &family.base.level_params, Expr::sort(u.clone())),
        num_params: 0,
        num_indices: 0,
        all: vec![name("PUnit")],
        ctors: vec![name("PUnit.unit")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    });
    if !comparison.constant(environment, expected)?
        || !comparison.constant(
            environment,
            ConstantInfo::Ctor(ConstructorVal {
                base: base("PUnit.unit", &family.base.level_params, c("PUnit", vec![u])),
                induct: name("PUnit"),
                cidx: 0,
                num_params: 0,
                num_fields: 0,
                is_unsafe: false,
            }),
        )?
    {
        return Ok(false);
    }
    for (label, type_, value) in [
        (
            "Unit",
            Expr::sort(Level::one()),
            c("PUnit", vec![Level::one()]),
        ),
        ("Unit.unit", unit(), c("PUnit.unit", vec![Level::one()])),
    ] {
        let Some(ConstantInfo::Defn(actual)) = environment.find(&name(label)) else {
            return Ok(false);
        };
        if !actual.base.level_params.is_empty()
            || !definition_matches(comparison, actual, &type_, &value)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn projection_matches(
    environment: &Environment,
    comparison: &mut Comparison<'_>,
) -> Result<bool, IngressError> {
    let Some(ConstantInfo::Defn(actual)) = environment.find(&name("Thunk.fn")) else {
        return Ok(false);
    };
    let [parameter] = actual.base.level_params.as_slice() else {
        return Ok(false);
    };
    let u = Level::param(parameter.clone());
    let sort = Expr::sort(u.clone().succ().map_err(|_| unsupported())?);
    let type_ = pi(
        sort.clone(),
        explicit(family_type(&u, b(0)), callback(b(2))),
        BinderInfo::Implicit,
    );
    for info in [BinderInfo::Default, BinderInfo::Implicit] {
        let value = lam(
            sort.clone(),
            lam(
                family_type(&u, b(0)),
                Expr::proj(name("Thunk"), 0, b(0)),
                BinderInfo::Default,
            ),
            info,
        );
        if definition_matches(comparison, actual, &type_, &value)? {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(super) fn operation_matches(
    environment: &Environment,
    operation: Operation,
    comparison: &mut Comparison<'_>,
) -> Result<bool, IngressError> {
    let Some(ConstantInfo::Defn(actual)) = environment.find(&name(operation.label())) else {
        return Ok(false);
    };
    let [parameter] = actual.base.level_params.as_slice() else {
        return Ok(false);
    };
    let u = Level::param(parameter.clone());
    let sort = Expr::sort(u.clone().succ().map_err(|_| unsupported())?);
    let (domain, result, body) = match operation {
        Operation::Pure => (
            b(0),
            family_type(&u, b(1)),
            app(
                c("Thunk.mk", vec![u]),
                [b(1), lam(unit(), b(1), BinderInfo::Default)],
            ),
        ),
        Operation::Get => (
            family_type(&u, b(0)),
            b(1),
            app(c("Thunk.fn", vec![u]), [b(1), b(0), c("Unit.unit", vec![])]),
        ),
        Operation::New => return Ok(false),
    };
    let type_ = pi(
        sort.clone(),
        explicit(domain.clone(), result),
        BinderInfo::Implicit,
    );
    let value = lam(
        sort,
        lam(domain, body, BinderInfo::Default),
        BinderInfo::Implicit,
    );
    if !definition_matches(comparison, actual, &type_, &value)? {
        return Ok(false);
    }
    if operation == Operation::Get {
        return projection_matches(environment, comparison);
    }
    Ok(true)
}
