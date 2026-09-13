//! Hand-built recursor fixtures; neither source nor primary inductive generator.
#![forbid(unsafe_code)]
use super::*;
use fln_checker::admit::{InductiveRejection, InductiveVerdict};
use fln_core::expr::FVarId;
#[derive(Clone)]
struct B {
    id: FVarId,
    ty: Expr,
}
impl B {
    fn new(label: &str, ty: Expr) -> Self {
        Self {
            id: FVarId(primary_name(label)),
            ty,
        }
    }
    fn e(&self) -> Expr {
        Expr::fvar(self.id.clone())
    }
}
fn close(bs: &[B], mut body: Expr, lambda: bool) -> Expr {
    for b in bs.iter().rev() {
        body = body.abstract_fvar(&b.id, 0).unwrap();
        body = if lambda {
            Expr::lam(b.id.0.clone(), b.ty.clone(), body, BinderInfo::Default)
        } else {
            Expr::forall_e(b.id.0.clone(), b.ty.clone(), body, BinderInfo::Default)
        };
    }
    body
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn constant(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_components(name.split('.')), levels)
}
#[derive(Clone, Copy)]
enum Mutation {
    None,
    SwapChildrenArguments,
    MissingLambda,
    FalseReflexive,
    FalseRecursive,
    WrongMinor,
    WrongUniverse,
    Negative,
}
fn fixture(mutation: Mutation) -> Vec<ConstantEntry> {
    let a = B::new("A", Expr::sort(Level::one()));
    let family = app(constant("Higher", vec![]), [a.e()]);
    let leaf_value = B::new("value", a.e());
    let first = B::new(
        "x",
        if matches!(mutation, Mutation::Negative) {
            family.clone()
        } else {
            a.e()
        },
    );
    let second = B::new("y", a.e());
    let seed = B::new("seed", a.e());
    let children = B::new(
        "children",
        close(&[first.clone(), second.clone()], family.clone(), false),
    );
    let major = B::new("major", family.clone());
    let motive = B::new(
        "motive",
        close(
            std::slice::from_ref(&major),
            Expr::sort(Level::param(primary_name("u"))),
            false,
        ),
    );
    let leaf = app(constant("Higher.leaf", vec![]), [a.e(), leaf_value.e()]);
    let fork = app(
        constant("Higher.fork", vec![]),
        [a.e(), seed.e(), children.e()],
    );
    let child = app(children.e(), [first.e(), second.e()]);
    let ih = B::new(
        "ih",
        close(
            &[first.clone(), second.clone()],
            app(motive.e(), [child.clone()]),
            false,
        ),
    );
    let m0 = B::new(
        "leaf",
        close(
            std::slice::from_ref(&leaf_value),
            app(motive.e(), [leaf]),
            false,
        ),
    );
    let m1 = B::new(
        "fork",
        close(
            &[seed.clone(), children.clone(), ih.clone()],
            app(motive.e(), [fork]),
            false,
        ),
    );
    let binders = [a.clone(), motive.clone(), m0.clone(), m1.clone()];
    let mut sig = binders.to_vec();
    sig.push(major.clone());
    let rec_type = close(&sig, app(motive.e(), [major.e()]), false);
    let mut leaf_binders = binders.to_vec();
    leaf_binders.push(leaf_value.clone());
    let mut fork_binders = binders.to_vec();
    fork_binders.extend([seed.clone(), children.clone()]);
    let child_call = app(
        children.e(),
        if matches!(mutation, Mutation::SwapChildrenArguments) {
            [second.e(), first.e()]
        } else {
            [first.e(), second.e()]
        },
    );
    let recursive = app(
        constant(
            "Higher.rec",
            vec![if matches!(mutation, Mutation::WrongUniverse) {
                Level::one()
            } else {
                Level::param(primary_name("u"))
            }],
        ),
        [a.e(), motive.e(), m0.e(), m1.e(), child_call],
    );
    let ih_value = if matches!(mutation, Mutation::MissingLambda) {
        recursive
    } else {
        close(&[first, second], recursive, true)
    };
    let rhs = if matches!(mutation, Mutation::WrongMinor) {
        app(m0.e(), [seed.e()])
    } else {
        app(m1.e(), [seed.e(), children.e(), ih_value])
    };
    vec![
        ConstantEntry::new(
            checker_name("Higher"),
            ConstantDeclaration::inductive(
                vec![],
                decoded(&close(
                    std::slice::from_ref(&a),
                    Expr::sort(Level::one()),
                    false,
                )),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    1,
                    0,
                    vec![checker_name("Higher")],
                    vec![
                        checker_qualified(&["Higher", "leaf"]),
                        checker_qualified(&["Higher", "fork"]),
                    ],
                    0,
                    !matches!(mutation, Mutation::FalseRecursive),
                    !matches!(mutation, Mutation::FalseReflexive),
                ),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Higher", "leaf"]),
            ConstantDeclaration::constructor(
                vec![],
                decoded(&close(
                    &[a.clone(), leaf_value.clone()],
                    family.clone(),
                    false,
                )),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("Higher"), 0, 1, 1),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Higher", "fork"]),
            ConstantDeclaration::constructor(
                vec![],
                decoded(&close(&[a, seed, children], family, false)),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("Higher"), 1, 1, 2),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Higher", "rec"]),
            ConstantDeclaration::recursor(
                vec![checker_name("u")],
                decoded(&rec_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![checker_name("Higher")],
                    1,
                    0,
                    1,
                    2,
                    vec![
                        RecursorRule::new(
                            checker_qualified(&["Higher", "leaf"]),
                            1,
                            decoded(&close(&leaf_binders, app(m0.e(), [leaf_value.e()]), true)),
                        ),
                        RecursorRule::new(
                            checker_qualified(&["Higher", "fork"]),
                            2,
                            decoded(&close(&fork_binders, rhs, true)),
                        ),
                    ],
                    false,
                ),
            ),
        ),
    ]
}
fn verdict(mutation: Mutation) -> InductiveVerdict {
    admit_inductive(
        &ConstantEnvironment::empty(),
        &fixture(mutation),
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    )
}
#[test]
fn function_child_recursor_is_reconstructed_from_its_constructor() {
    let result = verdict(Mutation::None);
    assert!(result.is_admitted(), "{result:?}");
}
#[test]
fn well_typed_but_wrong_recursive_arguments_are_rejected() {
    for mutation in [
        Mutation::SwapChildrenArguments,
        Mutation::WrongMinor,
        Mutation::WrongUniverse,
    ] {
        let result = verdict(mutation);
        assert!(
            matches!(
                result,
                InductiveVerdict::Rejected(InductiveRejection::RecursorShape { .. })
            ),
            "{result:?}"
        );
    }
}
#[test]
fn missing_function_binders_cannot_publish_a_recursor() {
    let result = verdict(Mutation::MissingLambda);
    assert!(!result.is_admitted(), "{result:?}");
}
#[test]
fn recursivity_flags_are_derived_not_trusted() {
    for mutation in [Mutation::FalseReflexive, Mutation::FalseRecursive] {
        let result = verdict(mutation);
        assert!(
            matches!(
                result,
                InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { .. })
            ),
            "{result:?}"
        );
    }
}
#[test]
fn negative_function_domains_are_rejected_even_with_plausible_recursor_metadata() {
    let result = verdict(Mutation::Negative);
    assert!(
        matches!(
            result,
            InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { .. })
        ),
        "{result:?}"
    );
}
#[test]
fn higher_order_admission_resource_and_cancellation_stops_are_recoverable() {
    let rows = fixture(Mutation::None);
    let env = ConstantEnvironment::empty();
    let before = env.clone();
    let stopped = admit_inductive_with(
        &env,
        &rows,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
        || true,
    );
    assert!(
        matches!(stopped, InductiveVerdict::Inconclusive(_)),
        "{stopped:?}"
    );
    let mut budget = AdmissionBudget::unlimited();
    budget.conversion.quick.max_comparisons = 1;
    let stopped = admit_inductive(&env, &rows, budget, EnvironmentBudget::unlimited());
    assert!(
        matches!(stopped, InductiveVerdict::Inconclusive(_)),
        "{stopped:?}"
    );
    assert_eq!(env, before);
    assert!(verdict(Mutation::None).is_admitted());
}
