//! Indexed recursor reconstruction uses constructor-derived index expressions.
#![forbid(unsafe_code)]
use super::*;
use fln_checker::admit::{InductiveRejection, InductiveStop, InductiveVerdict};
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

/// `W.{v} (α : Type v) : Type v := α`.
fn w_entry() -> ConstantEntry {
    let v = Level::param(primary_name("v"));
    let alpha = B::new("α", Expr::sort(v.succ().unwrap()));
    ConstantEntry::new(
        checker_name("W"),
        ConstantDeclaration::definition(
            vec![checker_name("v")],
            decoded(&close(
                std::slice::from_ref(&alpha),
                alpha.ty.clone(),
                false,
            )),
            ConstantSafety::Safe,
            DefinitionBody::new(
                decoded(&close(std::slice::from_ref(&alpha), alpha.e(), true)),
                ReducibilityHint::Regular(1),
                DefinitionSafety::Safe,
                Vec::new(),
            ),
        ),
    )
}
/// `KR.{v} : (α : Type v) → (a : W α) → α → Prop`, two parameters and one
/// index, with `KR.refl : (α : Type v) → (a : α) → KR α a a`. The family binds
/// its second parameter at `W α` and the constructor at `α`, as Mathlib's
/// `Cat.FreeReflRel` binds a promoted index at `Paths V` and at `V`.
fn promoted_parameter_family() -> Vec<ConstantEntry> {
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let levels = [v.clone()];
    let alpha = B::new("α", Expr::sort(v.clone().succ().unwrap()));
    let a_family = B::new("a", call(&["W"], &levels, &[alpha.e()]));
    let a_constructor = B::new("a", alpha.e());
    let b = B::new("b", alpha.e());
    let family = |a: &B, b: Expr| call(&["KR"], &levels, &[alpha.e(), a.e(), b]);
    let major = B::new("h", family(&a_family, b.e()));
    let motive = B::new(
        "motive",
        close(&[b.clone(), major.clone()], Expr::sort(u.clone()), false),
    );
    let refl = |a: &B| call(&["KR", "refl"], &levels, &[alpha.e(), a.e()]);
    let minor = B::new(
        "refl_case",
        apply(motive.e(), &[a_family.e(), refl(&a_family)]),
    );
    let prefix = [
        alpha.clone(),
        a_family.clone(),
        motive.clone(),
        minor.clone(),
    ];
    let rec_type = close(
        &prefix,
        close(
            &[b.clone(), major.clone()],
            apply(motive.e(), &[b.e(), major.e()]),
            false,
        ),
        false,
    );
    let family_name = checker_name("KR");
    let refl_name = checker_qualified(&["KR", "refl"]);
    let safe = ConstantSafety::Safe;
    vec![
        ConstantEntry::new(
            family_name.clone(),
            ConstantDeclaration::inductive(
                vec![checker_name("v")],
                decoded(&close(
                    &[alpha.clone(), a_family.clone(), b.clone()],
                    Expr::sort(Level::zero()),
                    false,
                )),
                safe,
                InductiveDeclaration::new(
                    2,
                    1,
                    vec![family_name.clone()],
                    vec![refl_name.clone()],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            refl_name.clone(),
            ConstantDeclaration::constructor(
                vec![checker_name("v")],
                decoded(&close(
                    &[alpha.clone(), a_constructor.clone()],
                    family(&a_constructor, a_constructor.e()),
                    false,
                )),
                safe,
                ConstructorDeclaration::new(family_name.clone(), 0, 2, 0),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["KR", "rec"]),
            ConstantDeclaration::recursor(
                vec![checker_name("u"), checker_name("v")],
                decoded(&rec_type),
                safe,
                RecursorDeclaration::new(
                    vec![family_name],
                    2,
                    1,
                    1,
                    1,
                    vec![RecursorRule::new(
                        refl_name,
                        0,
                        decoded(&close(&prefix, minor.e(), true)),
                    )],
                    true,
                ),
            ),
        ),
    ]
}
/// The pin converts each constructor parameter's domain with the family's
/// (`is_def_eq`, vendored `inductive.cpp:430`); comparing them as written
/// rejected `Cat.FreeReflRel`, whose constructor binds `X : V` where the
/// family has `X : Paths V`, though K1 and the pin accept it (S23,
/// `Mathlib.CategoryTheory.Category.ReflQuiv`).
#[test]
fn a_constructor_parameter_domain_that_converts_with_the_familys_is_admitted() {
    let verdict = admit_inductive(
        &environment_of(vec![w_entry()]),
        &promoted_parameter_family(),
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "{verdict:?}");
}
/// That conversion runs on the admission's conversion budget, and a stop there
/// is a typed non-answer for that parameter, never a rejection. The quick
/// budget stays whole: the structural comparisons before it spend that one.
#[test]
fn a_starved_parameter_domain_conversion_is_inconclusive() {
    let unlimited = InferenceBudget::unlimited().defeq;
    let budget = AdmissionBudget::new(
        InferenceBudget::unlimited(),
        WhnfBudget::unlimited(),
        DefEqBudget::new(
            unlimited.quick,
            0,
            0,
            u64::MAX,
            u64::MAX,
            WhnfBudget::new(0, 0, TermBudget::unlimited()),
        ),
    );
    let verdict = admit_inductive(
        &environment_of(vec![w_entry()]),
        &promoted_parameter_family(),
        budget,
        EnvironmentBudget::unlimited(),
    );
    assert!(
        matches!(
            verdict,
            InductiveVerdict::Inconclusive(InductiveStop::ParameterConversion { parameter: 1, .. })
        ),
        "{verdict:?}"
    );
}

/// `KU.{v1 … vn} : (α1 : Sort v1) → … → (αn : Sort vn) → Prop`, one parameter
/// per universe, with `KU.mk : (α1 …) → KU α1 …` and its K-like recursor
/// `KU.rec.{u, v1 … vn} : (α1 …) → (motive : KU α1 … → Sort u) →
/// motive (KU.mk α1 …) → (t : KU α1 …) → motive t`.
fn universe_parameter_family(count: usize) -> Vec<ConstantEntry> {
    let u = Level::param(primary_name("u"));
    let names: Vec<String> = (1..=count).map(|i| format!("v{i}")).collect();
    let levels: Vec<Level> = names
        .iter()
        .map(|name| Level::param(primary_name(name.as_str())))
        .collect();
    let level_names: Vec<WireName> = names
        .iter()
        .map(|name| checker_name(name.as_str()))
        .collect();
    let parameters: Vec<B> = levels
        .iter()
        .enumerate()
        .map(|(index, level)| B::new(&format!("α{index}"), Expr::sort(level.clone())))
        .collect();
    let arguments: Vec<Expr> = parameters.iter().map(B::e).collect();
    let family = call(&["KU"], &levels, &arguments);
    let major = B::new("t", family.clone());
    let motive = B::new(
        "motive",
        close(std::slice::from_ref(&major), Expr::sort(u.clone()), false),
    );
    let minor = B::new(
        "mk_case",
        apply(motive.e(), &[call(&["KU", "mk"], &levels, &arguments)]),
    );
    let mut prefix = parameters.clone();
    prefix.extend([motive.clone(), minor.clone()]);
    let rec_type = close(
        &prefix,
        close(
            std::slice::from_ref(&major),
            apply(motive.e(), &[major.e()]),
            false,
        ),
        false,
    );
    let family_name = checker_name("KU");
    let mk_name = checker_qualified(&["KU", "mk"]);
    let safe = ConstantSafety::Safe;
    let mut rec_levels = vec![checker_name("u")];
    rec_levels.extend(level_names.iter().cloned());
    let parameter_count = u32::try_from(count).expect("small family");
    vec![
        ConstantEntry::new(
            family_name.clone(),
            ConstantDeclaration::inductive(
                level_names.clone(),
                decoded(&close(&parameters, Expr::sort(Level::zero()), false)),
                safe,
                InductiveDeclaration::new(
                    parameter_count,
                    0,
                    vec![family_name.clone()],
                    vec![mk_name.clone()],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            mk_name.clone(),
            ConstantDeclaration::constructor(
                level_names,
                decoded(&close(&parameters, family, false)),
                safe,
                ConstructorDeclaration::new(family_name.clone(), 0, parameter_count, 0),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["KU", "rec"]),
            ConstantDeclaration::recursor(
                rec_levels,
                decoded(&rec_type),
                safe,
                RecursorDeclaration::new(
                    vec![family_name],
                    parameter_count,
                    0,
                    1,
                    1,
                    vec![RecursorRule::new(
                        mk_name,
                        0,
                        decoded(&close(&prefix, minor.e(), true)),
                    )],
                    true,
                ),
            ),
        ),
    ]
}
/// The pin keeps an inductive's universe parameters as a list with no bound
/// (`m_lparams`, vendored `inductive.cpp:163`); it refuses only a duplicate
/// (`check_duplicated_univ_params`, `:779`). The constructor-derived route
/// deferred any family with more than eight, which in S23 left
/// `Limits.PreservesColimit₂` (ten) and two siblings without an answer.
#[test]
fn a_family_with_more_than_eight_universe_parameters_is_admitted() {
    for count in [1, 8, 9, 12] {
        let verdict = admit_inductive(
            &ConstantEnvironment::empty(),
            &universe_parameter_family(count),
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        );
        assert!(
            verdict.is_admitted(),
            "{count} universe parameters: {verdict:?}"
        );
    }
}
