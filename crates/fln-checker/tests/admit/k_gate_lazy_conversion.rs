//! KR-317's gate decides by lazy conversion before it walks eagerly (bead
//! `fln-checker-exhaustion-roots-1mr1`).
//!
//! The pin fires K on a stuck major only when the major's type is `is_def_eq`
//! to the nullary constructor's (vendored inductive.h:48), and `is_def_eq` is
//! lazy: at two applications of one regular definition it compares the
//! arguments before unfolding (vendored type_checker.cpp:936-948). The checker
//! used to try its own eager walk first, which normalizes both index terms with
//! full delta and splits the weak heads it reaches. Over a structural recursion
//! on a large literal that walk peels one successor per layer, every layer
//! cheap, and reaches the arguments that actually differ only after as many
//! layers as the literal's value.
//!
//! Minimized from `Char.toUpper_eq_of_isLower` (Batteries.Data.Char.AsciiCasing):
//! a cast along `h : c.val + ('A'.val - 'a'.val) = c.val + 4294967264`, whose
//! gate the walk could not finish in 100,000,000 steps while K1 admitted the
//! declaration in 12,967. Here `h : addR (idN x) N = addR x N` with `addR` a
//! recursion on its second argument and `idN` the identity: equal by unfolding
//! `idN` alone, as the same-head comparison finds, and `N` far beyond any walk.
//! `addR` builds a value of its own type `L` (`L.cons` per successor), so each
//! layer the walk peels is an ordinary constructor application, as the
//! `UInt32`/`BitVec` layers were, and no other bound ends the walk.
#![forbid(unsafe_code)]
use super::*;
use fln_checker::whnf::{WhnfContext, WhnfOutcome, whnf};
use fln_checker::wire::ExprNode;

/// The recursion's literal: far more layers than any budget can peel.
const LITERAL: u64 = 1 << 40;

/// Steps the cast's reduction may take, gate included. Measured with the lazy
/// conversion first (debug build of d9269bef plus this change): 197 steps, 4
/// reductions. With the eager walk first, as at d9269bef, the same reduction
/// is a non-answer at a cap of 20,000,000 steps (it had spent all of them and
/// 1,199,998 reductions peeling `addR`), so this bound fails on a regression
/// back to the walk-first order by any margin.
const REDUCTION_STEP_BOUND: u64 = 2_000;

/// The budget the declarations below are checked within, in every dimension.
/// Measured with the lazy conversion first: the two positive declarations are
/// admitted and the sort-shaped negative rejected at a cap of 500. With the
/// walk first all three are inconclusive at this cap.
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
fn nat() -> Expr {
    c("Nat")
}
fn ty() -> Expr {
    Expr::sort(Level::one())
}
fn literal(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
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
fn regular(label: &str, type_: Expr, value: Expr) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(label),
        ConstantDeclaration::definition(
            vec![],
            decoded(&type_),
            ConstantSafety::Safe,
            DefinitionBody::new(
                decoded(&value),
                ReducibilityHint::Regular(1),
                DefinitionSafety::Safe,
                Vec::new(),
            ),
        ),
    )
}
fn l() -> Expr {
    c("L")
}
fn add_r(left: Expr, right: Expr) -> Expr {
    app(c("addR"), [left, right])
}
fn id_n(value: Expr) -> Expr {
    app(c("idN"), [value])
}
/// `@Eq.{1} L a b`.
fn eq_l(a: Expr, b: Expr) -> Expr {
    app(
        Expr::const_(primary_name("Eq"), vec![Level::one()]),
        [l(), a, b],
    )
}
/// `@Eq.rec.{u, 1} L a (fun b _ => motive) minor b major : motive`, which
/// reduces to `minor` only by K, and only when `a` and `b` are definitionally
/// equal. `u` is the universe of `motive`'s type.
fn cast_into(u: Level, motive: Expr, minor: Expr, a: Expr, b: Expr, major: &str) -> Expr {
    app(
        Expr::const_(Name::from_components(["Eq", "rec"]), vec![u, Level::one()]),
        [
            l(),
            a.clone(),
            lam(l(), lam(eq_l(a, bv(0)), motive)),
            minor,
            b,
            c(major),
        ],
    )
}
/// The cast at motive `C`: `w` by K.
fn cast(a: Expr, b: Expr, major: &str) -> Expr {
    cast_into(Level::one(), c("C"), c("w"), a, b, major)
}
/// The cast whose gate the walk cannot finish.
fn deep_cast() -> Expr {
    cast(
        add_r(id_n(c("x")), literal(LITERAL)),
        add_r(c("x"), literal(LITERAL)),
        "h",
    )
}
/// The same gate at motive `Type`: a type that is `Prop` by K.
fn deep_sort_cast() -> Expr {
    cast_into(
        Level::succ(Level::one()).expect("universe successor packs"),
        ty(),
        Expr::sort(Level::zero()),
        add_r(id_n(c("x")), literal(LITERAL)),
        add_r(c("x"), literal(LITERAL)),
        "h",
    )
}
/// A cast whose gate genuinely fails: `addR (idN y) 3 ≠ addR x 3` for
/// distinct axioms `x` and `y`, so K must not fire.
fn unequal_cast() -> Expr {
    cast(
        add_r(id_n(c("y")), literal(3)),
        add_r(c("x"), literal(3)),
        "h_unequal",
    )
}
fn environment() -> ConstantEnvironment {
    let mut rows = nat_entries();
    rows.extend(init_eq_entries());
    // `L : Type` with `L.base : Nat → L` and `L.cons : L → L`.
    rows.extend([
        ConstantEntry::new(
            checker_name("L"),
            ConstantDeclaration::inductive(
                vec![],
                decoded(&ty()),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    0,
                    0,
                    vec![checker_name("L")],
                    vec![
                        checker_qualified(&["L", "base"]),
                        checker_qualified(&["L", "cons"]),
                    ],
                    0,
                    true,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["L", "base"]),
            ConstantDeclaration::constructor(
                vec![],
                decoded(&pi(nat(), l())),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("L"), 0, 0, 1),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["L", "cons"]),
            ConstantDeclaration::constructor(
                vec![],
                decoded(&pi(l(), l())),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("L"), 1, 0, 1),
            ),
        ),
    ]);
    // `addR n m := Nat.rec (motive := fun _ => L) (L.base n) (fun _ ih => L.cons ih) m`
    let successor = lam(
        nat(),
        lam(
            l(),
            app(
                Expr::const_(Name::from_components(["L", "cons"]), vec![]),
                [bv(0)],
            ),
        ),
    );
    let base = app(
        Expr::const_(Name::from_components(["L", "base"]), vec![]),
        [bv(1)],
    );
    rows.push(regular(
        "addR",
        pi(nat(), pi(nat(), l())),
        lam(
            nat(),
            lam(
                nat(),
                app(
                    Expr::const_(Name::from_components(["Nat", "rec"]), vec![Level::one()]),
                    [lam(nat(), l()), base, successor, bv(0)],
                ),
            ),
        ),
    ));
    rows.push(regular("idN", pi(nat(), nat()), lam(nat(), bv(0))));
    rows.extend([
        axiom_of("x", nat()),
        axiom_of("y", nat()),
        axiom_of("C", ty()),
        axiom_of("w", c("C")),
        axiom_of("Q", Expr::sort(Level::zero())),
        axiom_of("F", pi(c("C"), ty())),
        axiom_of("wF", app(c("F"), [c("w")])),
        axiom_of(
            "h",
            eq_l(
                add_r(id_n(c("x")), literal(LITERAL)),
                add_r(c("x"), literal(LITERAL)),
            ),
        ),
        axiom_of(
            "h_unequal",
            eq_l(add_r(id_n(c("y")), literal(3)), add_r(c("x"), literal(3))),
        ),
    ]);
    environment_of(rows)
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

/// The cast reduces to `w` within a bounded number of steps: the gate passes
/// by the lazy conversion, which compares `idN x` with `x` at the shared head
/// `addR` instead of walking `addR`'s recursion over 2^40.
#[test]
fn a_k_gate_over_a_deep_literal_recursion_passes_within_a_bounded_step_count() {
    let context = WhnfContext::new(Vec::new(), Vec::new(), environment());
    let outcome = whnf(
        &decoded(&deep_cast()),
        &context,
        WhnfBudget::new(
            REDUCTION_STEP_BOUND,
            REDUCTION_STEP_BOUND,
            TermBudget::unlimited(),
        ),
    );
    let WhnfOutcome::Complete(result) = outcome else {
        panic!(
            "the K gate must pass within {REDUCTION_STEP_BOUND} steps, as the pin's lazy \
             is_def_eq passes it: {outcome:?}"
        );
    };
    assert!(
        result.steps <= REDUCTION_STEP_BOUND,
        "{} steps",
        result.steps
    );
    assert_eq!(
        result.term.node(result.term.root()),
        Some(&ExprNode::Constant {
            name: checker_name("w"),
            levels: Vec::new(),
        }),
        "the cast reduces to its minor premise by K"
    );
}

/// The minimized declaration: `wF : F w` admitted at `F (cast … h)`, within a
/// capped budget. A walk-first gate leaves it inconclusive, which is how the
/// council halted Batteries.Data.Char.AsciiCasing.
#[test]
fn the_minimized_declaration_is_admitted_within_a_capped_budget() {
    let candidate = definition(
        "toUpper_shape",
        decoded(&app(c("F"), [deep_cast()])),
        decoded(&c("wF")),
    );
    let outcome = admit(&environment(), &candidate, capped());
    assert!(matches!(outcome, Verdict::Admitted(_)), "{outcome:?}");
}

/// The same gate, where what the cast reduces to is a sort: `Q : Prop` is a
/// value of the cast, which is `Prop` by K.
#[test]
fn a_proposition_is_a_value_of_the_cast_that_is_prop_by_k() {
    let candidate = definition(
        "toUpper_shape_sort",
        decoded(&deep_sort_cast()),
        decoded(&c("Q")),
    );
    let outcome = admit(&environment(), &candidate, capped());
    assert!(matches!(outcome, Verdict::Admitted(_)), "{outcome:?}");
}

/// Negative control: the gate passes and the cast is `Prop`, so `Nat : Type`
/// is not a value of it. Rejected, by a decisive sort mismatch, not merely
/// left unadmitted.
#[test]
fn a_type_is_still_rejected_as_a_value_of_the_cast_that_is_prop_by_k() {
    let candidate = definition(
        "toUpper_shape_sort_wrong",
        decoded(&deep_sort_cast()),
        decoded(&nat()),
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

/// Negative control: the major's indices differ (`idN y` against `x`), so the
/// gate must fail, the cast stays stuck, and `wF : F w` must not be admitted
/// at `F (cast …)`. The checker's untyped conversion leaves that pair
/// deferred (measured: `Deferred` at this cap with this change);
/// the claim tested is only that it is never admitted.
#[test]
fn a_cast_whose_indices_differ_is_not_reduced() {
    let candidate = definition(
        "toUpper_shape_unequal",
        decoded(&app(c("F"), [unequal_cast()])),
        decoded(&c("wF")),
    );
    let outcome = admit(&environment(), &candidate, capped());
    assert!(
        !matches!(outcome, Verdict::Admitted(_)),
        "a cast whose indices differ must not reduce: {outcome:?}"
    );
}
