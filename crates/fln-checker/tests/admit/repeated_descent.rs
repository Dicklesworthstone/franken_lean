//! The typed lane opens a binder pair again after a failed congruence attempt
//! gave it back (bead `fln-kiq3`). In `MvPolynomial.degrees_def` 42% of the
//! lane's descents repeated one already made; each opened a fresh local, so every
//! pair below it was new to the lane's caches and the check never ended.
//!
//! The family below makes every level do that. `L i r` is
//! `fun y => M (L (i - 1) r) (k y x_r)` with `x_p = a`, `x_q = b`, over
//! `L 0 r = fun y => h y r`, and `M l x := G l c0` ignores `x`. Comparing
//! `L i p` with `L i q` opens `y` and compares `M (L (i - 1) p) (k y a)` with
//! `M (L (i - 1) q) (k y b)`. Congruence on `M` first establishes
//! `L (i - 1) p ≟ L (i - 1) q`, then fails on `a ≟ b`, and gives that back;
//! unfolding `M` leaves `G (L (i - 1) p) c0 ≟ G (L (i - 1) q) c0`, whose
//! congruence opens the same pair again. At the bottom, `h y p ≟ h y q` holds
//! only by proof irrelevance, so the untyped converter defers every level to
//! the lane. Opened at a fresh local each time, the work doubles per level
//! (measured, unbounded: 37 s at depth 16, 600 s at depth 20); opened again at
//! the same local, the second descent meets pairs the lane has already settled
//! (105 ms and 185 ms).
#![forbid(unsafe_code)]
use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(primary_name(label), vec![])
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn bv(index: u32) -> Expr {
    Expr::bvar(index).expect("small bound index")
}
/// A non-dependent arrow `domain → body`.
fn arrow(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(primary_name("x"), domain, body, BinderInfo::Default)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(primary_name("y"), domain, body, BinderInfo::Default)
}
fn ty() -> Expr {
    Expr::sort(Level::one())
}
fn prop() -> Expr {
    Expr::sort(Level::zero())
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
fn t() -> Expr {
    c("T")
}
fn t_to_t() -> Expr {
    arrow(t(), t())
}

/// `L depth r` above, for `r = proof` and `x_r = x`; `bottom` gives `L 0`'s
/// body at the bound `y`.
fn family(depth: usize, proof: &str, x: &str, bottom: &dyn Fn(&str) -> Expr) -> Expr {
    let mut term = lam(t(), bottom(proof));
    for _ in 0..depth {
        term = lam(t(), app(c("M"), [term, app(c("k"), [bv(0), c(x)])]));
    }
    term
}
fn h_y(proof: &str) -> Expr {
    app(c("h"), [bv(0), c(proof)])
}

fn environment(qa_type: Expr) -> ConstantEnvironment {
    let m_body = lam(t_to_t(), lam(t(), app(c("G"), [bv(1), c("c0")])));
    environment_of(vec![
        axiom("T", ty()),
        axiom("c0", t()),
        axiom("a", t()),
        axiom("b", t()),
        axiom("Pp", prop()),
        axiom("p", c("Pp")),
        axiom("q", c("Pp")),
        axiom("h", arrow(t(), arrow(c("Pp"), t()))),
        axiom("k", arrow(t(), arrow(t(), t()))),
        axiom("G", arrow(t_to_t(), arrow(t(), t()))),
        ConstantEntry::new(
            checker_name("M"),
            ConstantDeclaration::definition(
                vec![],
                decoded(&arrow(t_to_t(), arrow(t(), t()))),
                ConstantSafety::Safe,
                DefinitionBody::new(
                    decoded(&m_body),
                    ReducibilityHint::Regular(1),
                    DefinitionSafety::Safe,
                    Vec::new(),
                ),
            ),
        ),
        axiom("Q", arrow(t_to_t(), prop())),
        axiom("qa", app(c("Q"), [qa_type])),
    ])
}

/// The lane's own step bound. At `DEPTH` the lane needs under 20,000 steps
/// when a repeated descent reopens its pair at the same local, and between 2
/// and 5 million when every descent opens a fresh one (measured at both).
const LANE_STEPS: u64 = 100_000;
const DEPTH: usize = 16;

/// `qa : Q (L DEPTH p)` checked at `Q (L DEPTH q)`, with `L 0 q`'s body given
/// by `bottom`, under `LANE_STEPS`.
fn admit_family(bottom: &dyn Fn(&str) -> Expr) -> Verdict {
    let env = environment(family(DEPTH, "p", "a", &h_y));
    let candidate = definition(
        "descent",
        decoded(&app(c("Q"), [family(DEPTH, "q", "b", bottom)])),
        decoded(&c("qa")),
    );
    let budget = AdmissionBudget::new(
        InferenceBudget::new(
            LANE_STEPS,
            u64::MAX,
            TermBudget::unlimited(),
            TermBudget::unlimited(),
        ),
        WhnfBudget::unlimited(),
        InferenceBudget::unlimited().defeq,
    );
    admit(&env, &candidate, budget)
}

#[test]
fn a_binder_pair_opened_again_after_a_failed_attempt_settles_within_a_small_budget() {
    let outcome = admit_family(&h_y);
    assert!(matches!(outcome, Verdict::Admitted(_)), "{outcome:?}");
}

/// The control: with `L 0 q`'s body `h c0 q`, the bottom pair `h y p ≟ h c0 q`
/// differs at a value, and reopening pairs at the same locals must not hide it.
/// The lane is sufficient only, so a pair it cannot equate defers the body's
/// conversion; it decides that within the same budget instead of exhausting it.
#[test]
fn a_family_differing_at_a_value_below_the_repeated_descents_is_not_admitted() {
    let outcome = admit_family(&|proof| app(c("h"), [c("c0"), c(proof)]));
    assert!(
        matches!(
            outcome,
            Verdict::Deferred(AdmissionDeferred::BodyConversion { .. })
        ),
        "{outcome:?}"
    );
}
