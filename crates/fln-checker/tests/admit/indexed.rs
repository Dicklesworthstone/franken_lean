//! Indexed recursor reconstruction uses constructor-derived index expressions.
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
    fn new(text: &str, ty: Expr) -> Self {
        Self {
            id: FVarId(primary_name(text)),
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
fn call(name: &[&str], levels: &[Level], args: &[Expr]) -> Expr {
    args.iter().cloned().fold(
        Expr::const_(Name::from_components(name.iter().copied()), levels.to_vec()),
        Expr::app,
    )
}
fn apply(head: Expr, args: &[Expr]) -> Expr {
    args.iter().cloned().fold(head, Expr::app)
}
fn nat() -> Expr {
    call(&["Nat"], &[], &[])
}
fn zero() -> Expr {
    call(&["Nat", "zero"], &[], &[])
}
fn succ(n: Expr) -> Expr {
    call(&["Nat", "succ"], &[], &[n])
}

#[derive(Clone, Copy)]
enum Mutation {
    None,
    WrongRecursiveIndex,
    WrongResultIndex,
    WrongMinorIndex,
    WrongMetadata,
    NonUniform,
    NestedIndex,
}

fn vector(mutation: Mutation) -> Vec<ConstantEntry> {
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let levels = [v.clone()];
    let rec_levels = [u.clone(), v.clone()];
    let a = B::new("A", Expr::sort(v.clone().succ().unwrap()));
    let n = B::new("n", nat());
    let value = B::new("value", a.e());
    let child_index = if matches!(mutation, Mutation::NestedIndex) {
        // An index that mentions the family is forbidden even when it sits in
        // an argument to a function that will ignore it.
        Expr::app(
            Expr::lam(
                primary_name("ignored"),
                Expr::sort(v.clone().succ().unwrap()),
                zero(),
                BinderInfo::Default,
            ),
            call(&["Vector"], &levels, &[a.e(), n.e()]),
        )
    } else {
        n.e()
    };
    let tail = B::new(
        "tail",
        call(
            &["Vector"],
            &levels,
            &[
                if matches!(mutation, Mutation::NonUniform) {
                    nat()
                } else {
                    a.e()
                },
                child_index,
            ],
        ),
    );
    let major = B::new("major", call(&["Vector"], &levels, &[a.e(), n.e()]));
    let motive = B::new(
        "motive",
        close(&[n.clone(), major.clone()], Expr::sort(u), false),
    );
    let nil = call(&["Vector", "nil"], &levels, &[a.e()]);
    let cons = call(
        &["Vector", "cons"],
        &levels,
        &[a.e(), n.e(), value.e(), tail.e()],
    );
    let nil_minor = B::new("nil_case", apply(motive.e(), &[zero(), nil]));
    let ih = B::new(
        "ih",
        apply(
            motive.e(),
            &[
                if matches!(mutation, Mutation::WrongMinorIndex) {
                    succ(n.e())
                } else {
                    n.e()
                },
                tail.e(),
            ],
        ),
    );
    let result_index = if matches!(mutation, Mutation::WrongResultIndex) {
        n.e()
    } else {
        succ(n.e())
    };
    let fields = [n.clone(), value.clone(), tail.clone()];
    let cons_minor = B::new(
        "cons_case",
        close(
            &fields,
            close(&[ih], apply(motive.e(), &[result_index, cons]), false),
            false,
        ),
    );
    let prefix = [
        a.clone(),
        motive.clone(),
        nil_minor.clone(),
        cons_minor.clone(),
    ];
    let rec_type = close(
        &prefix,
        close(
            &[n.clone(), major.clone()],
            apply(motive.e(), &[n.e(), major.e()]),
            false,
        ),
        false,
    );
    let recurse = call(
        &["Vector", "rec"],
        &rec_levels,
        &[
            a.e(),
            motive.e(),
            nil_minor.e(),
            cons_minor.e(),
            if matches!(mutation, Mutation::WrongRecursiveIndex) {
                succ(n.e())
            } else {
                n.e()
            },
            tail.e(),
        ],
    );
    let rule = close(
        &prefix,
        close(
            &fields,
            apply(cons_minor.e(), &[n.e(), value.e(), tail.e(), recurse]),
            true,
        ),
        true,
    );
    let family_name = checker_name("Vector");
    let nil_name = checker_qualified(&["Vector", "nil"]);
    let cons_name = checker_qualified(&["Vector", "cons"]);
    let safe = ConstantSafety::Safe;
    vec![
        ConstantEntry::new(
            family_name.clone(),
            ConstantDeclaration::inductive(
                vec![checker_name("v")],
                decoded(&close(
                    &[a.clone(), n.clone()],
                    Expr::sort(v.succ().unwrap()),
                    false,
                )),
                safe,
                InductiveDeclaration::new(
                    1,
                    1,
                    vec![family_name.clone()],
                    vec![nil_name.clone(), cons_name.clone()],
                    0,
                    true,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            nil_name.clone(),
            ConstantDeclaration::constructor(
                vec![checker_name("v")],
                decoded(&close(
                    std::slice::from_ref(&a),
                    call(&["Vector"], &levels, &[a.e(), zero()]),
                    false,
                )),
                safe,
                ConstructorDeclaration::new(family_name.clone(), 0, 1, 0),
            ),
        ),
        ConstantEntry::new(
            cons_name.clone(),
            ConstantDeclaration::constructor(
                vec![checker_name("v")],
                decoded(&close(
                    std::slice::from_ref(&a),
                    close(
                        &fields,
                        call(&["Vector"], &levels, &[a.e(), succ(n.e())]),
                        false,
                    ),
                    false,
                )),
                safe,
                ConstructorDeclaration::new(family_name.clone(), 1, 1, 3),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Vector", "rec"]),
            ConstantDeclaration::recursor(
                vec![checker_name("u"), checker_name("v")],
                decoded(&rec_type),
                safe,
                RecursorDeclaration::new(
                    vec![family_name],
                    1,
                    if matches!(mutation, Mutation::WrongMetadata) {
                        0
                    } else {
                        1
                    },
                    1,
                    2,
                    vec![
                        RecursorRule::new(
                            nil_name,
                            0,
                            decoded(&close(&prefix, nil_minor.e(), true)),
                        ),
                        RecursorRule::new(cons_name, 3, decoded(&rule)),
                    ],
                    false,
                ),
            ),
        ),
    ]
}
fn base() -> ConstantEnvironment {
    let rows = nat_entries();
    assert!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &rows,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited()
        )
        .is_admitted()
    );
    environment_of(rows)
}
#[test]
fn indexed_vectors_are_admitted_from_their_constructor_telescopes() {
    let env = base();
    let before = env.clone();
    let verdict = admit_inductive(
        &env,
        &vector(Mutation::None),
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "{verdict:?}");
    assert_eq!(env, before);
}
#[test]
fn indexed_recursor_claims_cannot_change_a_child_index_or_branch_result() {
    for mutation in [
        Mutation::WrongRecursiveIndex,
        Mutation::WrongResultIndex,
        Mutation::WrongMinorIndex,
        Mutation::WrongMetadata,
    ] {
        let verdict = admit_inductive(
            &base(),
            &vector(mutation),
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        );
        assert!(
            matches!(
                verdict,
                InductiveVerdict::Rejected(InductiveRejection::RecursorShape { .. })
            ),
            "{verdict:?}"
        );
    }
}
#[test]
fn indexed_recursive_arguments_still_require_uniform_parameters() {
    let verdict = admit_inductive(
        &base(),
        &vector(Mutation::NonUniform),
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(!verdict.is_admitted(), "{verdict:?}");
}
#[test]
fn indexed_cancellation_and_materialization_stops_are_atomic_nonanswers() {
    let env = base();
    let rows = vector(Mutation::None);
    assert!(matches!(
        admit_inductive_with(
            &env,
            &rows,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
            || true
        ),
        InductiveVerdict::Inconclusive(_)
    ));
    let mut budget = AdmissionBudget::unlimited();
    budget.inference.materialization.max_arena_nodes = 0;
    assert!(matches!(
        admit_inductive(&env, &rows, budget, EnvironmentBudget::unlimited()),
        InductiveVerdict::Inconclusive(_)
    ));
    assert!(
        admit_inductive(
            &env,
            &rows,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited()
        )
        .is_admitted()
    );
}
#[test]
fn an_index_must_not_contain_an_occurrence_of_the_family() {
    let verdict = admit_inductive(
        &base(),
        &vector(Mutation::NestedIndex),
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(!verdict.is_admitted(), "{verdict:?}");
}
