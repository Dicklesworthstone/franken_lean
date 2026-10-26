//! Complete de Bruijn models of the pinned Task family and selected operations.
//! Universe parameter labels are taken from the admitted telescopes; the model
//! fixes their positions and every logical field and elimination rule.

use super::*;
use fln_env::constants::{RecursorRule, RecursorVal};

pub(super) fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn c(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(label), levels)
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed Task model binder")
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

fn family_type(u: &Level, alpha: Expr) -> Expr {
    Expr::app(c("Task", vec![u.clone()]), alpha)
}

fn base(label: &str, universes: &[Name], type_: Expr) -> ConstantVal {
    ConstantVal {
        name: name(label),
        level_params: universes.to_vec(),
        type_,
    }
}

pub(super) fn family(environment: &Environment) -> Option<Vec<ConstantInfo>> {
    let family = environment.find(&name("Task"))?.constant_val();
    let [parameter] = family.level_params.as_slice() else {
        return None;
    };
    let u = Level::param(parameter.clone());
    let sort = Expr::sort(u.clone().succ().ok()?);
    let rec = environment.find(&name("Task.rec"))?.constant_val();
    let [result, parameter] = rec.level_params.as_slice() else {
        return None;
    };
    let ru = Level::param(parameter.clone());
    let rv = Level::param(result.clone());
    let rsort = Expr::sort(ru.clone().succ().ok()?);
    let motive = explicit(family_type(&ru, b(0)), Expr::sort(rv));
    let minor = explicit(
        b(1),
        Expr::app(b(1), app(c("Task.pure", vec![ru.clone()]), [b(2), b(0)])),
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
                lam(b(2), Expr::app(b(1), b(0)), BinderInfo::Default),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    Some(vec![
        ConstantInfo::Induct(InductiveVal {
            base: base(
                "Task",
                &family.level_params,
                explicit(sort.clone(), sort.clone()),
            ),
            num_params: 1,
            num_indices: 0,
            all: vec![name("Task")],
            ctors: vec![name("Task.pure")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
        ConstantInfo::Ctor(ConstructorVal {
            base: base(
                "Task.pure",
                &family.level_params,
                pi(
                    sort,
                    explicit(b(0), family_type(&u, b(1))),
                    BinderInfo::Implicit,
                ),
            ),
            induct: name("Task"),
            cidx: 0,
            num_params: 1,
            num_fields: 1,
            is_unsafe: false,
        }),
        ConstantInfo::Rec(RecursorVal {
            base: base("Task.rec", &rec.level_params, rec_type),
            all: vec![name("Task")],
            num_params: 1,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: name("Task.pure"),
                nfields: 1,
                rhs: rule,
            }],
            k: false,
            is_unsafe: false,
        }),
    ])
}

fn getter_matches(
    environment: &Environment,
    comparison: &mut Comparison<'_>,
) -> Result<bool, IngressError> {
    let Some(ConstantInfo::Defn(actual)) = environment.find(&name("Task.get")) else {
        return Ok(false);
    };
    let [parameter] = actual.base.level_params.as_slice() else {
        return Ok(false);
    };
    let u = Level::param(parameter.clone());
    let sort = Expr::sort(u.clone().succ().map_err(|_| unsupported())?);
    let type_ = pi(
        sort.clone(),
        explicit(family_type(&u, b(0)), b(1)),
        BinderInfo::Implicit,
    );
    let value = lam(
        sort,
        lam(
            family_type(&u, b(0)),
            Expr::proj(name("Task"), 0, b(0)),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    Ok(actual.safety == DefinitionSafety::Safe
        && actual.all == [name("Task.get")]
        && comparison.expression(&actual.base.type_, &type_)?
        && comparison.expression(&actual.value, &value)?)
}

fn base_io(alpha: Expr) -> Expr {
    Expr::app(c("BaseIO", vec![]), alpha)
}

fn applicative() -> Expr {
    app(
        c("Monad.toApplicative", vec![Level::zero(); 2]),
        [c("BaseIO", vec![]), c("instMonadBaseIO", vec![])],
    )
}

fn priority() -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: base("Task.Priority", &[], Expr::sort(Level::one())),
        value: c("Nat", vec![]),
        hints: fln_env::constants::ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("Task.Priority")],
    })
}

fn opaque(operation: Operation) -> ConstantInfo {
    let sort = Expr::sort(Level::one());
    let (type_, value) = match operation {
        Operation::AsTask => {
            let priority = c("Task.Priority", vec![]);
            let domain = app(
                c("optParam", vec![Level::one()]),
                [priority.clone(), c("Task.Priority.default", vec![])],
            );
            let type_ = pi(
                sort.clone(),
                explicit(
                    base_io(b(0)),
                    explicit(domain, base_io(family_type(&Level::zero(), b(2)))),
                ),
                BinderInfo::Implicit,
            );
            let functor = app(
                c("Applicative.toFunctor", vec![Level::zero(); 2]),
                [c("BaseIO", vec![]), applicative()],
            );
            let value = app(
                c("Functor.map", vec![Level::zero(); 2]),
                [
                    c("BaseIO", vec![]),
                    functor,
                    b(2),
                    family_type(&Level::zero(), b(2)),
                    Expr::app(c("Task.pure", vec![Level::zero()]), b(2)),
                    b(1),
                ],
            );
            let value = lam(
                sort,
                lam(
                    base_io(b(0)),
                    lam(priority, value, BinderInfo::Default),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            );
            (type_, value)
        }
        Operation::Wait => {
            let type_ = pi(
                sort.clone(),
                explicit(family_type(&Level::zero(), b(0)), base_io(b(1))),
                BinderInfo::Implicit,
            );
            let pure = app(
                c("Applicative.toPure", vec![Level::zero(); 2]),
                [c("BaseIO", vec![]), applicative()],
            );
            let value = app(
                c("Pure.pure", vec![Level::zero(); 2]),
                [
                    c("BaseIO", vec![]),
                    pure,
                    b(1),
                    app(c("Task.get", vec![Level::zero()]), [b(1), b(0)]),
                ],
            );
            let value = lam(
                sort,
                lam(
                    family_type(&Level::zero(), b(0)),
                    value,
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            );
            (type_, value)
        }
        Operation::Pure | Operation::Get | Operation::MapTask | Operation::BindTask => {
            unreachable!("monomorphic opaque Task operation")
        }
    };
    ConstantInfo::Opaque(OpaqueVal {
        base: base(operation.label(), &[], type_),
        value,
        is_unsafe: false,
        all: vec![name(operation.label())],
    })
}

fn composition(environment: &Environment, operation: Operation) -> Option<ConstantInfo> {
    let actual = environment.find(&name(operation.label()))?.constant_val();
    let [parameter] = actual.level_params.as_slice() else {
        return None;
    };
    let u = Level::param(parameter.clone());
    let alpha_sort = Expr::sort(u.clone().succ().ok()?);
    let beta_sort = Expr::sort(Level::one());
    let priority = c("Task.Priority", vec![]);
    let bool_ = c("Bool", vec![]);
    let priority_domain = app(
        c("optParam", vec![Level::one()]),
        [priority.clone(), c("Task.Priority.default", vec![])],
    );
    let sync_domain = app(
        c("optParam", vec![Level::one()]),
        [bool_.clone(), c("Bool.false", vec![])],
    );
    let (first, second) = match operation {
        Operation::MapTask => (explicit(b(1), base_io(b(1))), family_type(&u, b(2))),
        Operation::BindTask => (
            family_type(&u, b(1)),
            explicit(b(2), base_io(family_type(&Level::zero(), b(2)))),
        ),
        _ => unreachable!("Task composition operation"),
    };
    let type_ = pi(
        alpha_sort.clone(),
        pi(
            beta_sort.clone(),
            explicit(
                first.clone(),
                explicit(
                    second.clone(),
                    explicit(
                        priority_domain,
                        explicit(sync_domain, base_io(family_type(&Level::zero(), b(4)))),
                    ),
                ),
            ),
            BinderInfo::Implicit,
        ),
        BinderInfo::Implicit,
    );
    let value = match operation {
        Operation::MapTask => {
            let functor = app(
                c("Applicative.toFunctor", vec![Level::zero(); 2]),
                [c("BaseIO", vec![]), applicative()],
            );
            app(
                c("Functor.map", vec![Level::zero(); 2]),
                [
                    c("BaseIO", vec![]),
                    functor,
                    b(4),
                    family_type(&Level::zero(), b(4)),
                    Expr::app(c("Task.pure", vec![Level::zero()]), b(4)),
                    Expr::app(b(3), app(c("Task.get", vec![u.clone()]), [b(5), b(2)])),
                ],
            )
        }
        Operation::BindTask => Expr::app(b(2), app(c("Task.get", vec![u]), [b(5), b(3)])),
        _ => unreachable!("Task composition operation"),
    };
    let value = lam(
        alpha_sort,
        lam(
            beta_sort,
            lam(
                first,
                lam(
                    second,
                    lam(
                        priority,
                        lam(bool_, value, BinderInfo::Default),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        ),
        BinderInfo::Implicit,
    );
    Some(ConstantInfo::Opaque(OpaqueVal {
        base: base(operation.label(), &actual.level_params, type_),
        value,
        is_unsafe: false,
        all: vec![name(operation.label())],
    }))
}

pub(super) fn operation_matches(
    environment: &Environment,
    operation: Operation,
    comparison: &mut Comparison<'_>,
) -> Result<bool, IngressError> {
    match operation {
        Operation::Pure => Ok(true),
        Operation::Get => getter_matches(environment, comparison),
        Operation::AsTask => Ok(comparison.constant(environment, priority())?
            && comparison.constant(environment, opaque(operation))?),
        Operation::Wait => Ok(getter_matches(environment, comparison)?
            && comparison.constant(environment, opaque(operation))?),
        Operation::MapTask | Operation::BindTask => {
            let Some(expected) = composition(environment, operation) else {
                return Ok(false);
            };
            Ok(getter_matches(environment, comparison)?
                && comparison.constant(environment, priority())?
                && comparison.constant(environment, expected)?)
        }
    }
}
