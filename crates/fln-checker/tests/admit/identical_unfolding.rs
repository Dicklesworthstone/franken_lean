//! Identical terms are equal before lazy delta unfolds them (bead
//! `fln-checker-exhaustion-roots-1mr1`).
//!
//! The pin's `lazy_delta_reduction_step` asks `quick_is_def_eq` of the pair each
//! step leaves (vendored type_checker.cpp:954-958), and that first asks its
//! equivalence manager, which falls back to structural equality
//! (type_checker.cpp:759-761, equiv_manager.cpp:56-115). Two identical terms
//! under a shared head that is not regular, so that the same-head argument
//! comparison (type_checker.cpp:936-948) does not apply, are therefore equal
//! at once. The checker used to unfold them in lockstep instead, one delta step
//! per side at a time, through every layer of both copies.
//!
//! Minimized from `Equiv.isDomain` (Mathlib.Algebra.Ring.TransferInstance),
//! where an instance diamond puts identical copies of `Equiv.mul e …`,
//! `HMul.hMul …` and the `Semiring` parent projections on both sides of one
//! application-argument conversion: 14,168,443 comparisons and the whole
//! materialization budget, where K1 took 12,309 steps. Here the identical
//! subterm is `d40 Prop`, where `d0 x := x` and `dₖ x := dₖ₋₁ (dₖ₋₁ x)` are
//! abbreviations: unfolding it to a weak head normal form takes 2^40 steps.
#![forbid(unsafe_code)]
use super::*;
use fln_checker::defeq::{DefEqOutcome, def_eq};
use fln_checker::whnf::WhnfContext;

/// The doubling chain's length: `d40 Prop` is `Prop` only after 2^40 head
/// steps, so a lockstep unfolding of two copies cannot finish in any budget.
const DEPTH: u32 = 40;

/// Comparisons plus WHNF steps the conversion may take. Measured with the
/// identity check (debug build of d9269bef plus this change): 28 slow
/// comparisons, 33 WHNF steps, 1 delta unfold. Without it, as at d9269bef, the
/// same conversion had not finished after 86 minutes of a debug build at a cap
/// of 20,000,000 and was stopped; it fails this bound at once.
const CONVERSION_BOUND: u64 = 1_000;

/// The budget the declarations below are checked within, in every dimension.
const ADMISSION_CAP: u64 = 10_000;

fn c(label: &str) -> Expr {
    Expr::const_(primary_name(label), vec![])
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn bv(index: u32) -> Expr {
    Expr::bvar(index).expect("small bound index")
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(primary_name("x"), domain, body, BinderInfo::Default)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(primary_name("x"), domain, body, BinderInfo::Default)
}
fn prop() -> Expr {
    Expr::sort(Level::zero())
}
fn ty() -> Expr {
    Expr::sort(Level::one())
}
/// `Sort (u+1)` for the chain's own universe parameter `u`.
fn successor_sort() -> Expr {
    Expr::sort(Level::succ(Level::param(primary_name("u"))).expect("universe successor packs"))
}
fn axiom_of(label: &str, type_: Expr) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(label),
        header(
            vec![],
            decoded(&type_),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    )
}
fn definition_entry(
    label: &str,
    level_parameters: Vec<WireName>,
    type_: Expr,
    value: Expr,
    hint: ReducibilityHint,
) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(label),
        ConstantDeclaration::definition(
            level_parameters,
            decoded(&type_),
            ConstantSafety::Safe,
            DefinitionBody::new(decoded(&value), hint, DefinitionSafety::Safe, Vec::new()),
        ),
    )
}
fn chain_name(index: u32) -> String {
    format!("d{index}")
}
/// `dₖ.{level} argument`.
fn chain(index: u32, level: Level, argument: Expr) -> Expr {
    app(
        Expr::const_(primary_name(chain_name(index)), vec![level]),
        [argument],
    )
}
/// `d0.{u} : Sort (u+1) → Sort (u+1) := fun x => x` and
/// `dₖ.{u} := fun x => dₖ₋₁.{u} (dₖ₋₁.{u} x)`, all abbreviations, so the
/// same-head argument comparison never applies to them.
fn chain_entries() -> Vec<ConstantEntry> {
    let u = || Level::param(primary_name("u"));
    let mut rows = vec![definition_entry(
        &chain_name(0),
        vec![checker_name("u")],
        pi(successor_sort(), successor_sort()),
        lam(successor_sort(), bv(0)),
        ReducibilityHint::Abbrev,
    )];
    for index in 1..=DEPTH {
        let inner = chain(index - 1, u(), bv(0));
        rows.push(definition_entry(
            &chain_name(index),
            vec![checker_name("u")],
            pi(successor_sort(), successor_sort()),
            lam(successor_sort(), chain(index - 1, u(), inner)),
            ReducibilityHint::Abbrev,
        ));
    }
    rows
}
fn environment() -> ConstantEnvironment {
    let mut rows = chain_entries();
    rows.push(definition_entry(
        "idR",
        vec![],
        pi(ty(), ty()),
        lam(ty(), bv(0)),
        ReducibilityHint::Regular(1),
    ));
    rows.extend([
        axiom_of("T", pi(ty(), pi(ty(), ty()))),
        axiom_of("b", ty()),
        axiom_of("w", app(c("T"), [deep(), c("b")])),
        axiom_of("q", chain(4, Level::one(), Expr::sort(Level::one()))),
    ]);
    environment_of(rows)
}
/// `d40.{0} Prop`: `Prop`, but only after 2^40 head steps.
fn deep() -> Expr {
    chain(DEPTH, Level::zero(), prop())
}
/// `T (d40 Prop) b`, the type of `w`.
fn inferred() -> Expr {
    app(c("T"), [deep(), c("b")])
}
/// `T (d40 Prop) (idR b)`: not identical to `inferred`, so the conversion is
/// not decided by a structural comparison at its root, and the `d40 Prop`
/// pair is reached on its own.
fn declared() -> Expr {
    app(c("T"), [deep(), app(c("idR"), [c("b")])])
}
fn capped() -> AdmissionBudget {
    let inference = InferenceBudget::new(
        ADMISSION_CAP,
        ADMISSION_CAP,
        TermBudget::unlimited(),
        TermBudget::unlimited(),
    );
    AdmissionBudget::new(
        inference,
        WhnfBudget::new(ADMISSION_CAP, ADMISSION_CAP, TermBudget::unlimited()),
        inference.defeq,
    )
}

/// The conversion of the two types within a bounded number of comparisons:
/// the identical `d40 Prop` pair is equal at once, as the pin's
/// `quick_is_def_eq` finds, instead of being unfolded side by side.
#[test]
fn identical_abbreviation_applications_convert_within_a_bounded_count() {
    let context = WhnfContext::new(Vec::new(), Vec::new(), environment());
    let budget = InferenceBudget::new(
        CONVERSION_BOUND,
        CONVERSION_BOUND,
        TermBudget::unlimited(),
        TermBudget::unlimited(),
    )
    .defeq;
    let outcome = def_eq(
        &decoded(&inferred()),
        &decoded(&declared()),
        &context,
        budget,
    );
    let DefEqOutcome::Equal(progress) = outcome else {
        panic!(
            "identical terms must convert within {CONVERSION_BOUND} comparisons, as the pin's \
             quick_is_def_eq decides them: {outcome:?}"
        );
    };
    assert!(
        progress.slow_comparisons + progress.whnf_steps <= CONVERSION_BOUND,
        "{progress:?}"
    );
    assert_eq!(
        progress.delta_unfolds, 1,
        "only `idR` unfolds; the identical `d40 Prop` pair is never unfolded: {progress:?}"
    );
}

/// The minimized declaration: `w : T (d40 Prop) b` admitted at
/// `T (d40 Prop) (idR b)` within a capped budget.
#[test]
fn the_minimized_declaration_is_admitted_within_a_capped_budget() {
    let candidate = definition("isDomain_shape", decoded(&declared()), decoded(&c("w")));
    let outcome = admit(&environment(), &candidate, capped());
    assert!(matches!(outcome, Verdict::Admitted(_)), "{outcome:?}");
}

/// Negative control: `d4.{1} Type` against `d4.{0} Prop` share every node but
/// their universe levels, so the identity check must not equate them; they
/// unfold to `Type` and `Prop`, and `q : d4.{1} Type` is rejected as a value of
/// `d4.{0} Prop` by a decisive sort mismatch.
#[test]
fn applications_differing_only_in_levels_are_still_rejected() {
    let candidate = definition(
        "isDomain_shape_wrong_level",
        decoded(&chain(4, Level::zero(), prop())),
        decoded(&c("q")),
    );
    let outcome = admit(&environment(), &candidate, capped());
    assert!(
        matches!(
            outcome,
            Verdict::Rejected(AdmissionRejection::BodyTypeMismatch { .. })
        ),
        "{outcome:?}"
    );
}
