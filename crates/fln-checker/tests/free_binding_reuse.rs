#![forbid(unsafe_code)]

//! Regressions for fln-checker-free-binding-cycle-false-reject-u1vk.
//! These are synthetic checker tests, not a replay of the pinned Mathlib module.

use fln_checker::environment::{ConstantEnvironment, DefinitionSafety};
use fln_checker::infer::{
    InferenceBudget, InferenceContext, InferenceMode, InferenceOutcome, infer,
};
use fln_checker::term::TermBudget;
use fln_checker::whnf::{
    FreeBinding, ProjectionRule, WhnfBudget, WhnfContext, WhnfOutcome, WhnfRefusal, WhnfResult,
    whnf, whnf_with,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::canon::Canonical;

fn name(text: impl Into<String>) -> Name {
    Name::str(Name::anonymous(), text)
}

fn wire_name(text: &str) -> WireName {
    match decode_name(&name(text).to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("name did not decode: {other:?}"),
    }
}

fn decoded(term: &Expr) -> WireExpr {
    match decode_expr(&term.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("expression did not decode: {other:?}"),
    }
}

fn free(text: &str) -> Expr {
    Expr::fvar(FVarId(name(text)))
}

fn atom(text: &str) -> Expr {
    Expr::const_(name(text), Vec::new())
}

fn bound(index: u32) -> Expr {
    Expr::bvar(index).expect("test bound variable packs")
}

fn lambda(body: Expr) -> Expr {
    Expr::lam(
        name("x"),
        Expr::sort(Level::zero()),
        body,
        BinderInfo::Default,
    )
}

fn identity() -> Expr {
    lambda(bound(0))
}

fn context(bindings: Vec<(&str, Expr)>) -> WhnfContext {
    WhnfContext::new(
        bindings
            .into_iter()
            .map(|(name, value)| FreeBinding::new(wire_name(name), decoded(&value)))
            .collect(),
        Vec::new(),
        ConstantEnvironment::empty(),
    )
}

fn repeated(head: Expr, argument: Expr) -> Expr {
    Expr::app(head.clone(), Expr::app(head, argument))
}

fn complete(outcome: WhnfOutcome) -> WhnfResult {
    match outcome {
        WhnfOutcome::Complete(result) => result,
        other => panic!("expected completed reduction, got {other:?}"),
    }
}

fn assert_atom(term: &Expr, context: &WhnfContext, expected: &Expr) {
    let result = complete(whnf(&decoded(term), context, WhnfBudget::unlimited()));
    let expected = decoded(expected);
    assert_eq!(
        result.term.node(result.term.root()),
        expected.node(expected.root()),
    );
}

/// A genuine cycle is refused within a few steps. The budget is bounded so that
/// a regression in cycle detection fails here, as an inconclusive outcome,
/// instead of reducing `f := f` forever and hanging the suite.
fn assert_cycle(term: &Expr, context: &WhnfContext) {
    let outcome = whnf(
        &decoded(term),
        context,
        WhnfBudget::new(100_000, 100_000, TermBudget::unlimited()),
    );
    assert!(
        matches!(
            outcome,
            WhnfOutcome::Refused(WhnfRefusal::FreeBindingCycle { .. })
        ),
        "expected a free-binding cycle refusal, got {outcome:?}"
    );
}

#[test]
fn identity_may_be_unfolded_again_after_beta() {
    let context = context(vec![("f", identity())]);
    assert_atom(&repeated(free("f"), atom("a")), &context, &atom("a"));
}

#[test]
fn aliases_may_be_reused_after_beta() {
    let context = context(vec![("f", free("g")), ("g", identity())]);
    assert_atom(&repeated(free("f"), atom("a")), &context, &atom("a"));
}

#[test]
fn shared_dependency_diamonds_are_not_cycles() {
    let context = context(vec![
        (
            "f",
            lambda(Expr::app(free("g"), Expr::app(free("h"), bound(0)))),
        ),
        ("g", free("base")),
        ("h", free("base")),
        ("base", identity()),
    ]);
    assert_atom(&repeated(free("f"), atom("a")), &context, &atom("a"));
}

#[test]
fn zeta_may_return_an_already_used_binding() {
    let context = context(vec![("f", identity())]);
    let inner = Expr::let_e(
        name("saved"),
        Expr::sort(Level::zero()),
        free("f"),
        Expr::app(bound(0), atom("a")),
        false,
    );
    assert_atom(&Expr::app(free("f"), inner), &context, &atom("a"));
}

#[test]
fn projection_may_select_an_already_used_binding() {
    let context = WhnfContext::new(
        vec![
            FreeBinding::new(
                wire_name("record"),
                decoded(&Expr::app(atom("Mk"), free("f"))),
            ),
            FreeBinding::new(wire_name("f"), decoded(&identity())),
        ],
        vec![ProjectionRule::new(wire_name("S"), wire_name("Mk"), 0)],
        ConstantEnvironment::empty(),
    );
    let projection = Expr::proj(name("S"), 0, free("record"));
    assert_atom(&repeated(projection, atom("a")), &context, &atom("a"));
}

#[test]
fn unbound_free_variables_stay_stuck_after_binding_reuse() {
    let context = context(vec![("f", identity())]);
    assert_atom(&repeated(free("f"), free("a")), &context, &free("a"));
}

#[test]
fn direct_binding_cycles_are_still_refused() {
    assert_cycle(&free("f"), &context(vec![("f", free("f"))]));
}

#[test]
fn mutual_binding_cycles_are_still_refused() {
    assert_cycle(
        &free("f"),
        &context(vec![("f", free("g")), ("g", free("f"))]),
    );
}

#[test]
fn beta_cannot_hide_a_genuine_binding_cycle() {
    let context = context(vec![("f", lambda(Expr::app(free("f"), bound(0))))]);
    assert_cycle(&Expr::app(free("f"), atom("a")), &context);
}

#[test]
fn a_shared_acyclic_sibling_does_not_hide_a_cycle() {
    let context = context(vec![
        (
            "f",
            lambda(Expr::app(free("base"), Expr::app(free("g"), bound(0)))),
        ),
        ("g", free("f")),
        ("base", identity()),
    ]);
    assert_cycle(&Expr::app(free("f"), atom("a")), &context);
}

#[test]
fn an_unrelated_unused_cycle_does_not_poison_acyclic_reuse() {
    let context = context(vec![("f", identity()), ("unused", free("unused"))]);
    assert_atom(&repeated(free("f"), atom("a")), &context, &atom("a"));
}

/// A closed typing regression, not just a supplied untyped WHNF context:
/// let F : Type -> Type := fun A => A;
/// fun (f : F (F (Prop -> Prop))) (p : Prop) => f p
/// The application must normalize its function type through the same scoped
/// let binding twice. The invalid variant supplies Type where Prop is required.
fn scoped_application(valid: bool) -> Expr {
    let prop = Expr::sort(Level::zero());
    let type_ = Expr::sort(Level::one());
    let endomorphism = Expr::forall_e(name("p"), prop.clone(), prop.clone(), BinderInfo::Default);
    let function_type = repeated(bound(0), endomorphism);
    let argument = if valid { bound(0) } else { type_.clone() };
    let body = Expr::lam(
        name("f"),
        function_type,
        Expr::lam(
            name("p"),
            prop,
            Expr::app(bound(1), argument),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    Expr::let_e(
        name("F"),
        Expr::forall_e(name("A"), type_.clone(), type_.clone(), BinderInfo::Default),
        Expr::lam(name("A"), type_, bound(0), BinderInfo::Default),
        body,
        false,
    )
}

#[test]
fn checking_a_closed_application_can_reuse_a_scoped_let() {
    let context = InferenceContext::new(Vec::new(), Vec::new(), ConstantEnvironment::empty())
        .expect("empty inference context");
    let outcome = infer(
        &decoded(&scoped_application(true)),
        &context,
        InferenceMode::Checking {
            declaration_safety: DefinitionSafety::Safe,
        },
        InferenceBudget::unlimited(),
    );
    assert!(
        matches!(outcome, InferenceOutcome::Complete(_)),
        "{outcome:?}"
    );
}

#[test]
fn fixing_scoped_let_reuse_does_not_admit_an_ill_typed_argument() {
    let context = InferenceContext::new(Vec::new(), Vec::new(), ConstantEnvironment::empty())
        .expect("empty inference context");
    let outcome = infer(
        &decoded(&scoped_application(false)),
        &context,
        InferenceMode::Checking {
            declaration_safety: DefinitionSafety::Safe,
        },
        InferenceBudget::unlimited(),
    );
    assert!(
        matches!(outcome, InferenceOutcome::Refused { .. }),
        "{outcome:?}"
    );
}

#[test]
fn every_step_and_reduction_cutoff_remains_inconclusive() {
    let context = context(vec![("f", free("g")), ("g", identity())]);
    let input = decoded(&repeated(free("f"), atom("a")));
    let result = complete(whnf(&input, &context, WhnfBudget::unlimited()));
    for limit in 0..result.steps {
        let outcome = whnf(
            &input,
            &context,
            WhnfBudget::new(limit, u64::MAX, TermBudget::unlimited()),
        );
        assert!(
            matches!(outcome, WhnfOutcome::Inconclusive(_)),
            "step limit {limit}: {outcome:?}"
        );
    }
    for limit in 0..result.reductions {
        let outcome = whnf(
            &input,
            &context,
            WhnfBudget::new(u64::MAX, limit, TermBudget::unlimited()),
        );
        assert!(
            matches!(outcome, WhnfOutcome::Inconclusive(_)),
            "reduction limit {limit}: {outcome:?}"
        );
    }
    assert_atom(&repeated(free("f"), atom("a")), &context, &atom("a"));
}

#[test]
fn cancellation_at_every_poll_never_publishes_a_success() {
    let context = context(vec![("f", free("g")), ("g", identity())]);
    let input = decoded(&repeated(free("f"), atom("a")));
    let mut total_polls = 0usize;
    complete(whnf_with(&input, &context, WhnfBudget::unlimited(), || {
        total_polls += 1;
        false
    }));
    assert!(total_polls > 0);
    for stop_at in 1..=total_polls {
        let mut polls = 0usize;
        let outcome = whnf_with(&input, &context, WhnfBudget::unlimited(), || {
            polls += 1;
            polls == stop_at
        });
        assert!(
            matches!(outcome, WhnfOutcome::Inconclusive(_)),
            "poll {stop_at}: {outcome:?}"
        );
    }
    assert_atom(&repeated(free("f"), atom("a")), &context, &atom("a"));
}

#[test]
fn deep_dependency_checks_use_the_heap_not_the_host_stack() {
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(|| {
            let depth = 4096;
            let bindings = (0..depth)
                .map(|index| {
                    let value = if index + 1 == depth {
                        identity()
                    } else {
                        free(&format!("f{}", index + 1))
                    };
                    FreeBinding::new(wire_name(&format!("f{index}")), decoded(&value))
                })
                .collect();
            let context = WhnfContext::new(bindings, Vec::new(), ConstantEnvironment::empty());
            assert_atom(&repeated(free("f0"), atom("a")), &context, &atom("a"));
        })
        .expect("start small-stack regression")
        .join()
        .expect("acyclic dependency walk must not overflow the host stack");
}
