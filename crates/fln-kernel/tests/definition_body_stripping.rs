//! The `franken_lean-d17i` discriminator, made executable.
//!
//! d17i's 13 `DefinitionTypeMismatch` corpus rows were classified as decode
//! artifacts rather than kernel incompleteness on the strength of one claim
//! about this crate: that a definition which reaches the kernel with its TYPE
//! intact but its VALUE stripped — a `ConstantInfo::Axiom` where the pin has a
//! `defnInfo` — cannot be delta-unfolded, so `def_eq` fails and admission of
//! any declaration that needed the unfolding is rejected as
//! `DefinitionTypeMismatch`.
//!
//! That claim was established by READING the chain (`unfold_definition`
//! requires `ConstantInfo::Defn`; `definition_height` returns `None` for every
//! other kind; `lazy_delta`'s `(None, None)` arm is immediately `Stuck`; the
//! `KR-974` body check turns a false `def_eq_public` into
//! `RejectClass::DefinitionTypeMismatch`). Reading is how the classification
//! was reached and it is not wrong, but it leaves the load-bearing fact of a
//! P0 classification with no test behind it: nothing in the suite fails if the
//! chain is later changed at either end.
//!
//! These three cases pin it, pin-independently — no Reference toolchain, no
//! corpus, no olean. They are deliberately the same shape as the sharpest of
//! the five rows, `Lean.Arrow`, where `Lean.Arrow a b` is definitionally
//! `(a -> b)` and admission needs exactly one delta step:
//!
//!   1. definition present WITH its value  -> Accepted
//!   2. same definition stripped to an axiom -> Rejected DefinitionTypeMismatch
//!   3. same definition absent entirely      -> Rejected UnknownConstant
//!
//! Case 1 is what makes case 2 a finding rather than a limitation: the kernel
//! admits this shape when it is handed a body, so the rejection in case 2 is
//! attributable to the stripped value and to nothing else. Case 3 separates
//! the two decode symptoms d17i had to tell apart — a constant that is missing
//! outright is reported by a different rule and carries a different class, so
//! case 2's class cannot be produced by mere absence.
//!
//! This guards the classification, not the decoder. Whether `fln-olean` still
//! strips bodies is `franken_lean-timy`'s question and is not asked here.

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, RejectClass, Verdict};
use fln_kernel::{Declaration, check};

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn sort1() -> Expr {
    Expr::sort(Level::one())
}

fn axiom_val(name: &str, type_: Expr) -> AxiomVal {
    AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        is_unsafe: false,
    }
}

fn defn_val(name: &str, type_: Expr, value: Expr) -> DefinitionVal {
    DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    }
}

/// Add a constant the way a decoded environment would present it, through the
/// kernel's own door: admitted first, then recorded. Nothing here smuggles in a
/// declaration the kernel would refuse.
fn admit(env: &Environment, decl: &Declaration, info: ConstantInfo) -> Environment {
    let verdict = check(env, decl, Budget::DEFAULT);
    assert!(
        matches!(verdict, Outcome::Complete(Verdict::Accepted { .. })),
        "setup declaration must be admissible, got {verdict:?}"
    );
    env.add_decl(info).expect("kernel-accepted decl adds")
}

/// `T`, an opaque carrier. Present identically in all three cases.
fn env_with_carrier() -> Environment {
    let env = Environment::new();
    let t = axiom_val("T", sort1());
    admit(&env, &Declaration::Axiom(t.clone()), ConstantInfo::Axiom(t))
}

fn t_const() -> Expr {
    Expr::const_(n("T"), vec![])
}

/// `Arrow : Sort 1 := T -> T` — the pin's `Lean.Arrow` shape reduced to its
/// essentials: a definition whose value is the very Pi that the dependent
/// declaration's body will be inferred to have.
fn arrow_value() -> Expr {
    Expr::forall_e(n("x"), t_const(), t_const(), BinderInfo::Default)
}

/// `def ap : Arrow := fun (x : T) => x`.
///
/// The body's inferred type is the Pi `T -> T`; the declared type is the
/// constant `Arrow`. Admission therefore REQUIRES delta-unfolding `Arrow`, and
/// requires nothing else — no equation-compiler auxiliary, no recursor, no
/// projection. That isolation is the point: it is the only reason a verdict
/// here can be attributed to the presence or absence of `Arrow`'s value.
fn dependent_declaration() -> Declaration {
    Declaration::Defn(defn_val(
        "ap",
        Expr::const_(n("Arrow"), vec![]),
        Expr::lam(
            n("x"),
            t_const(),
            Expr::bvar(0).expect("a single binder is in range"),
            BinderInfo::Default,
        ),
    ))
}

fn reject_class(verdict: &Outcome<Verdict>) -> Option<RejectClass> {
    match verdict {
        Outcome::Complete(Verdict::Rejected { class, .. }) => Some(*class),
        _ => None,
    }
}

#[test]
fn a_definition_with_its_value_admits_the_declaration_that_needs_one_delta_step() {
    let env = env_with_carrier();
    let arrow = defn_val("Arrow", sort1(), arrow_value());
    let env = admit(
        &env,
        &Declaration::Defn(arrow.clone()),
        ConstantInfo::Defn(arrow),
    );

    let verdict = check(&env, &dependent_declaration(), Budget::DEFAULT);
    assert!(
        matches!(verdict, Outcome::Complete(Verdict::Accepted { .. })),
        "the kernel closes `Arrow` = `T -> T` in one delta step when it is \
         handed the body; if this ever fails, d17i's five rows are genuine \
         defeq incompleteness after all and the classification must be \
         reopened. Got {verdict:?}"
    );
}

#[test]
fn the_same_definition_stripped_to_an_axiom_is_rejected_as_definition_type_mismatch() {
    let env = env_with_carrier();
    // Exactly what our decoder produced for `Lean.Arrow`, `Option.choice`,
    // `WellFounded.fixFC`, `Array.insertIdxIfInBounds` and
    // `Std.PRange.UpwardEnumerable.least`: the type survives, the value is
    // gone, the kind has changed. Same name, same type, same everything else
    // as the accepted case above.
    let arrow = axiom_val("Arrow", sort1());
    let env = admit(
        &env,
        &Declaration::Axiom(arrow.clone()),
        ConstantInfo::Axiom(arrow),
    );

    let verdict = check(&env, &dependent_declaration(), Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::DefinitionTypeMismatch),
        "a stripped body must surface as DefinitionTypeMismatch — the class \
         d17i's 13 corpus rows carried. Got {verdict:?}"
    );
}

#[test]
fn the_same_definition_absent_entirely_is_rejected_as_unknown_constant() {
    // The discriminating control. If absence produced DefinitionTypeMismatch
    // too, the previous test would prove nothing about STRIPPING — it would be
    // satisfied by any environment that could not resolve the name, and the
    // two decode symptoms d17i separated (24 UnknownConstant rows against 13
    // DefinitionTypeMismatch rows) would not be separable by class at all.
    let env = env_with_carrier();

    let verdict = check(&env, &dependent_declaration(), Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::UnknownConstant),
        "an absent constant is a different rule with a different class. Got {verdict:?}"
    );
}
