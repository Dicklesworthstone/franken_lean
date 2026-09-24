//! KR-312 function eta at typed conversion sites, with independently authored
//! wire fixtures. A lambda is convertible with a non-lambda `s` when it is
//! convertible with `s`'s eta expansion through `s`'s Π-type (the pin's
//! `try_eta_expansion_core`). Found by the whole-Init council frontier:
//! `WellFounded.fix_eq_fixC` and `WellFounded.extrinsicFix₂_eq_fix` were
//! K1-accepted and checker-deferred.
#![forbid(unsafe_code)]
use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(primary_name(label), vec![])
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(primary_name("x"), domain, body, BinderInfo::Default)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(primary_name("x"), domain, body, BinderInfo::Default)
}
fn bvar(index: u32) -> Expr {
    Expr::bvar(index).expect("small bound index")
}
fn axiom(label: &str, ty: Expr) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(label),
        header(
            vec![],
            decoded(&ty),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    )
}
fn unary() -> Expr {
    pi(c("A"), c("A"))
}
fn ty() -> Expr {
    Expr::sort(Level::one())
}
/// `U`, a one-constructor, zero-field structure: its values are all
/// definitionally equal (KR-315), which only a typed rule can see.
fn unit_like() -> Vec<ConstantEntry> {
    vec![
        ConstantEntry::new(
            checker_name("U"),
            ConstantDeclaration::inductive(
                vec![],
                decoded(&ty()),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    0,
                    0,
                    vec![checker_name("U")],
                    vec![checker_qualified(&["U", "mk"])],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["U", "mk"]),
            ConstantDeclaration::constructor(
                vec![],
                decoded(&c("U")),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("U"), 0, 0, 0),
            ),
        ),
    ]
}
/// `B`, with two constructors: its values are NOT all equal, so eta must
/// still compare the bodies it exposes rather than accept on shape.
fn two_valued() -> Vec<ConstantEntry> {
    let ctor = |leaf: &str, index: u32| {
        ConstantEntry::new(
            checker_qualified(&["B", leaf]),
            ConstantDeclaration::constructor(
                vec![],
                decoded(&c("B")),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("B"), index, 0, 0),
            ),
        )
    };
    vec![
        ConstantEntry::new(
            checker_name("B"),
            ConstantDeclaration::inductive(
                vec![],
                decoded(&ty()),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    0,
                    0,
                    vec![checker_name("B")],
                    vec![
                        checker_qualified(&["B", "t"]),
                        checker_qualified(&["B", "f"]),
                    ],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ctor("t", 0),
        ctor("f", 1),
    ]
}
fn to_u() -> Expr {
    pi(c("A"), c("U"))
}
fn to_b() -> Expr {
    pi(c("A"), c("B"))
}
/// `fun _ : A => u`, whose body is not an application at all, so the untyped
/// exact contraction has nothing to contract. Converting it with `v : A → U`
/// needs `v` eta-expanded through its type and then `u ≟ v x`, which holds by
/// unit-like eta.
fn constant_function() -> Expr {
    lam(c("A"), c("u"))
}
fn environment() -> ConstantEnvironment {
    let mut rows = vec![axiom("A", ty())];
    rows.extend(unit_like());
    rows.extend(two_valued());
    rows.extend([
        axiom("u", c("U")),
        axiom("v", to_u()),
        axiom("f", unary()),
        axiom("T", pi(to_u(), ty())),
        axiom("w_v", app(c("T"), [c("v")])),
        axiom("w_const", app(c("T"), [constant_function()])),
        axiom("b1", c("B")),
        axiom("vb", to_b()),
        axiom("TB", pi(to_b(), ty())),
        axiom("w_vb", app(c("TB"), [c("vb")])),
        axiom("w_constant_b", app(c("TB"), [lam(c("A"), c("b1"))])),
        axiom("T1", pi(unary(), ty())),
        axiom("w_f", app(c("T1"), [c("f")])),
        // Beneath a binder the checker meets a free local against the lambda:
        // `(h : A → U) → T h` against `(h : A → U) → T (fun _ => u)`.
        axiom("w_h", pi(to_u(), app(c("T"), [bvar(0)]))),
    ]);
    environment_of(rows)
}

#[test]
fn a_function_converts_with_its_eta_expansion_in_both_orientations() {
    let env = environment();
    let under_binder = pi(to_u(), app(c("T"), [constant_function()]));
    for (label, declared, value) in [
        (
            "expansion_declared",
            app(c("T"), [constant_function()]),
            c("w_v"),
        ),
        ("expansion_value", app(c("T"), [c("v")]), c("w_const")),
        ("under_binder", under_binder, c("w_h")),
    ] {
        let candidate = definition(label, decoded(&declared), decoded(&value));
        let outcome = admit(&env, &candidate, AdmissionBudget::unlimited());
        assert!(
            matches!(outcome, Verdict::Admitted(_)),
            "{label}: {outcome:?}"
        );
    }
}

#[test]
fn eta_never_equates_a_function_with_a_different_one() {
    let env = environment();
    // `fun x => f (f x)` is not an eta expansion of `f`.
    let twice = lam(c("A"), app(c("f"), [app(c("f"), [bvar(0)])]));
    let candidate = definition("twice", decoded(&app(c("T1"), [twice])), decoded(&c("w_f")));
    let outcome = admit(&env, &candidate, AdmissionBudget::unlimited());
    assert!(
        !matches!(outcome, Verdict::Admitted(_)),
        "a non-expansion must not convert: {outcome:?}"
    );
    // `fun _ => b1` against `vb : A → B` reaches the eta rule (the lambda body is
    // not an application), and the exposed `b1 ≟ vb x` is false for a
    // two-valued type: eta must stay a comparison, never an acceptance.
    for (label, declared, value) in [
        (
            "constant_b_declared",
            app(c("TB"), [lam(c("A"), c("b1"))]),
            c("w_vb"),
        ),
        (
            "constant_b_value",
            app(c("TB"), [c("vb")]),
            c("w_constant_b"),
        ),
    ] {
        let candidate = definition(label, decoded(&declared), decoded(&value));
        let outcome = admit(&env, &candidate, AdmissionBudget::unlimited());
        assert!(
            !matches!(outcome, Verdict::Admitted(_)),
            "{label}: eta exposed a false body obligation and must not convert: {outcome:?}"
        );
    }
}
