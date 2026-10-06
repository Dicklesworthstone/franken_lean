//! KR-317's gate in WHNF settles by proof irrelevance what the untyped
//! conversion defers (bead `fln-narm`).
//!
//! The pin fires K on a stuck major only when the major's type is `is_def_eq`
//! to the nullary constructor's (vendored inductive.h:48), and `is_def_eq`
//! decides two proofs of one proposition equal (`is_def_eq_proof_irrel`,
//! vendored type_checker.cpp:1117). The checker's WHNF gate compared the two
//! types by its untyped conversion only, which cannot know that two distinct
//! constants are proofs and so defers; the gate then missed, and the cast
//! stayed stuck.
//!
//! Minimized from `SSet.horn₃₁.desc.multicofork._proof_8`
//! (Mathlib.AlgebraicTopology.SimplicialSet.HornColimits): `decide` over two
//! `Fin` values reaches an `Eq.rec` cast whose gate compares `Fin` values built
//! with different proofs of their bounds. Here the cast runs along
//! `h : f p1 = f p2` with `p1 p2 : P` two proofs of a proposition, so
//! `f p1` and `f p2` are equal only by proof irrelevance.
#![forbid(unsafe_code)]
use super::*;
use fln_checker::defeq::{DefEqOutcome, def_eq};
use fln_checker::whnf::{WhnfContext, WhnfOutcome, whnf};
use fln_checker::wire::ExprNode;

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
fn axiom_of(label: &str, levels: Vec<WireName>, type_: Expr) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(label),
        header(
            levels,
            decoded(&type_),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    )
}
/// `@Eq.{1} Nat a b`.
fn eq_nat(a: Expr, b: Expr) -> Expr {
    app(
        Expr::const_(primary_name("Eq"), vec![Level::one()]),
        [nat(), a, b],
    )
}
/// `@Eq.rec.{1, 1} Nat a (fun b _ => C) w b major : C`, which reduces to `w`
/// only by K, and only when `a` and `b` are definitionally equal.
fn cast(a: Expr, b: Expr, major: Expr) -> Expr {
    app(
        Expr::const_(
            Name::from_components(["Eq", "rec"]),
            vec![Level::one(), Level::one()],
        ),
        [
            nat(),
            a.clone(),
            lam(nat(), lam(eq_nat(a, bv(0)), c("C"))),
            c("w"),
            b,
            major,
        ],
    )
}
/// `fU.{v} qN.{v}`: `f` and its proofs' proposition `PU.{v}` at a universe
/// parameter, so typing either proof meets `v`.
fn f_at_v(proof: &str) -> Expr {
    let v = || vec![Level::param(primary_name("v"))];
    app(
        Expr::const_(primary_name("fU"), v()),
        [Expr::const_(primary_name(proof), v())],
    )
}
fn at_u(label: &str) -> Expr {
    Expr::const_(primary_name(label), vec![Level::param(primary_name("u"))])
}
fn environment() -> ConstantEnvironment {
    let mut rows = nat_entries();
    rows.extend(init_eq_entries());
    let f_of = |proof: &str| app(c("f"), [c(proof)]);
    let g_of = |value: &str| app(c("g"), [c(value)]);
    rows.extend([
        axiom_of("P", vec![], Expr::sort(Level::zero())),
        axiom_of("p1", vec![], c("P")),
        axiom_of("p2", vec![], c("P")),
        axiom_of("f", vec![], pi(c("P"), nat())),
        axiom_of("PU", vec![checker_name("u")], Expr::sort(Level::zero())),
        axiom_of("q1", vec![checker_name("u")], at_u("PU")),
        axiom_of("q2", vec![checker_name("u")], at_u("PU")),
        axiom_of("fU", vec![checker_name("u")], pi(at_u("PU"), nat())),
        axiom_of("g", vec![], pi(nat(), nat())),
        axiom_of("n1", vec![], nat()),
        axiom_of("n2", vec![], nat()),
        axiom_of("C", vec![], ty()),
        axiom_of("w", vec![], c("C")),
        axiom_of("h", vec![], eq_nat(f_of("p1"), f_of("p2"))),
        axiom_of(
            "hU",
            vec![checker_name("v")],
            eq_nat(f_at_v("q1"), f_at_v("q2")),
        ),
        axiom_of("h_data", vec![], eq_nat(g_of("n1"), g_of("n2"))),
        // `hx : ∀ x : P, f p1 = f x`.
        axiom_of(
            "hx",
            vec![],
            pi(c("P"), eq_nat(f_of("p1"), app(c("f"), [bv(0)]))),
        ),
    ]);
    environment_of(rows)
}
fn reduce(term: &Expr) -> WhnfOutcome {
    let context = WhnfContext::new(Vec::new(), Vec::new(), environment());
    whnf(
        &decoded(term),
        &context,
        WhnfBudget::new(1_000_000, 1_000_000, TermBudget::unlimited()),
    )
}
/// The head constant of `term`'s application spine.
fn head_is(term: &WireExpr, name: &WireName) -> bool {
    let mut head = term.root();
    while let Some(ExprNode::Apply { function, .. }) = term.node(head) {
        head = *function;
    }
    matches!(term.node(head), Some(ExprNode::Constant { name: found, .. }) if found == name)
}
fn reduced_to_w(outcome: &WhnfOutcome) -> bool {
    matches!(outcome, WhnfOutcome::Complete(result) if result.term.node(result.term.root())
        == Some(&ExprNode::Constant { name: checker_name("w"), levels: Vec::new() }))
}

/// The cast reduces to `w` by K: the gate's sides `f p1 = f p2` and
/// `f p1 = f p1` are equal because `p1` and `p2` prove one proposition.
#[test]
fn a_k_gate_whose_sides_differ_only_by_a_proof_passes() {
    let outcome = reduce(&cast(
        app(c("f"), [c("p1")]),
        app(c("f"), [c("p2")]),
        c("h"),
    ));
    assert!(
        reduced_to_w(&outcome),
        "the cast must reduce to its minor premise by K, as the pin's typed is_def_eq \
         passes its gate by proof irrelevance: {outcome:?}"
    );
}

/// The same gate where the proofs live at a universe parameter `v`, which no
/// context here declares: `q1.{v}` and `q2.{v}` must still be typed and found
/// to prove one proposition.
#[test]
fn a_k_gate_whose_sides_mention_a_universe_parameter_passes() {
    let h_u = Expr::const_(primary_name("hU"), vec![Level::param(primary_name("v"))]);
    let outcome = reduce(&cast(f_at_v("q1"), f_at_v("q2"), h_u));
    assert!(
        reduced_to_w(&outcome),
        "the cast must reduce by K under a universe parameter: {outcome:?}"
    );
}

/// Negative control: the sides differ in data (`g n1` against `g n2` for
/// distinct axioms `n1 n2 : Nat`), which no proof irrelevance equates, so the
/// gate must miss and the reduction complete with the cast still stuck at its
/// recursor.
#[test]
fn a_k_gate_whose_sides_differ_in_data_does_not_pass() {
    let outcome = reduce(&cast(
        app(c("g"), [c("n1")]),
        app(c("g"), [c("n2")]),
        c("h_data"),
    ));
    assert!(
        matches!(&outcome, WhnfOutcome::Complete(result)
            if head_is(&result.term, &checker_qualified(&["Eq", "rec"]))),
        "the cast must stay stuck at Eq.rec: {outcome:?}"
    );
}

/// Under a binder the untyped conversion keeps the bound variable loose, so a
/// gate side can be open: here `f p1 = f #0` inside `fun x : P => …`. The typed
/// conversion has no local to type `#0` with and is not run on such a side;
/// the gate misses as it did before the typed fallback, and the comparison is
/// left to conversion with types. Typing the open side would fault on the
/// loose variable instead.
#[test]
fn a_k_gate_whose_sides_have_a_loose_bound_variable_is_not_typed() {
    let body = cast(
        app(c("f"), [c("p1")]),
        app(c("f"), [bv(0)]),
        app(c("hx"), [bv(0)]),
    );
    let context = WhnfContext::new(Vec::new(), Vec::new(), environment());
    let outcome = def_eq(
        &decoded(&lam(c("P"), body)),
        &decoded(&lam(c("P"), c("w"))),
        &context,
        DefEqBudget::unlimited(),
    );
    assert!(
        matches!(outcome, DefEqOutcome::Deferred { .. }),
        "the open gate must miss and the pair defer, not fault: {outcome:?}"
    );
}
