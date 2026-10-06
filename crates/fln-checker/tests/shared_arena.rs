#![forbid(unsafe_code)]

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use fln_checker::term::{TermBudget, TermOutcome, raise_external_bounds};
use fln_checker::whnf::{WhnfBudget, WhnfContext, WhnfOutcome, whnf, whnf_with};
use fln_checker::wire::{DecodeBudget, DecodeOutcome, WireExpr, decode_expr};
use fln_core::expr::{BinderInfo, Expr, Literal};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::canon::Canonical;

fn decoded(expression: &Expr) -> WireExpr {
    match decode_expr(&expression.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(term)) => term,
        other => panic!("fixture failed to decode: {other:?}"),
    }
}

fn fixture() -> WireExpr {
    decoded(&Expr::app(
        Expr::bvar(0).expect("bounded index"),
        Expr::sort(Level::one()),
    ))
}

fn hash(term: &WireExpr) -> u64 {
    let mut hasher = DefaultHasher::new();
    term.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn clones_share_expression_and_level_storage() {
    let term = fixture();
    assert!(!term.nodes().is_empty());
    assert!(!term.levels().is_empty());
    let clones: Vec<_> = (0..64).map(|_| term.clone()).collect();
    for cloned in &clones {
        assert!(std::ptr::eq(term.nodes(), cloned.nodes()));
        assert!(std::ptr::eq(term.levels(), cloned.levels()));
        assert_eq!(cloned.root(), term.root());
        assert_eq!(cloned, &term);
    }
}

#[test]
fn independently_decoded_arenas_keep_content_equality_and_hashing() {
    let first = fixture();
    let second = fixture();
    assert!(!std::ptr::eq(first.nodes(), second.nodes()));
    assert!(!std::ptr::eq(first.levels(), second.levels()));
    assert_eq!(first, second);
    assert_eq!(hash(&first), hash(&second));
    assert_eq!(hash(&first), hash(&first.clone()));
    let different = decoded(&Expr::sort(Level::zero()));
    assert_ne!(first, different);
}

#[test]
fn rewriting_a_shared_arena_leaves_every_alias_unchanged() {
    let original = fixture();
    let alias = original.clone();
    let before_hash = hash(&original);
    let changed = match raise_external_bounds(&alias, 3, 0, TermBudget::unlimited()) {
        TermOutcome::Complete(term) => term,
        other => panic!("rewrite failed: {other:?}"),
    };
    let expected = decoded(&Expr::app(
        Expr::bvar(3).expect("bounded index"),
        Expr::sort(Level::one()),
    ));
    assert_eq!(changed, expected);
    assert_ne!(changed, original);
    assert_eq!(original, fixture());
    assert_eq!(alias, original);
    assert_eq!(hash(&original), before_hash);
    assert!(std::ptr::eq(original.nodes(), alias.nodes()));
}

#[test]
fn the_last_alias_retains_large_node_payloads() {
    let payload = "shared checker payload ".repeat(16_384);
    let surviving = {
        let original = decoded(&Expr::lit(Literal::Str(payload.clone())));
        let alias = original.clone();
        assert!(std::ptr::eq(original.nodes(), alias.nodes()));
        alias
    };
    assert_eq!(surviving, decoded(&Expr::lit(Literal::Str(payload))));
}

fn redex() -> WireExpr {
    decoded(&Expr::app(
        Expr::lam(
            Name::anonymous(),
            Expr::sort(Level::one()),
            Expr::bvar(0).expect("bounded index"),
            BinderInfo::Default,
        ),
        Expr::sort(Level::zero()),
    ))
}

#[test]
fn independent_threads_can_reduce_shared_inputs() {
    let original = redex();
    let before = original.clone();
    std::thread::scope(|scope| {
        for _ in 0..4 {
            let input = original.clone();
            scope.spawn(move || {
                let result = whnf(&input, &WhnfContext::default(), WhnfBudget::unlimited());
                let WhnfOutcome::Complete(result) = result else {
                    panic!("reduction failed: {result:?}");
                };
                assert_eq!(result.term, decoded(&Expr::sort(Level::zero())));
            });
        }
    });
    assert_eq!(original, before);
    assert!(std::ptr::eq(original.nodes(), before.nodes()));
}

#[test]
fn sharing_preserves_reduction_progress_and_nonanswers() {
    let original = redex();
    let alias = original.clone();
    let context = WhnfContext::default();
    assert_eq!(
        whnf(&original, &context, WhnfBudget::unlimited()),
        whnf(&alias, &WhnfContext::default(), WhnfBudget::unlimited()),
    );
    let exhausted = WhnfBudget::new(0, 0, TermBudget::unlimited());
    let left = whnf(&original, &context, exhausted);
    let right = whnf(&alias, &context, exhausted);
    assert!(matches!(left, WhnfOutcome::Inconclusive(_)));
    assert_eq!(left, right);
    let left = whnf_with(&original, &context, WhnfBudget::unlimited(), || true);
    let right = whnf_with(&alias, &context, WhnfBudget::unlimited(), || true);
    assert!(matches!(left, WhnfOutcome::Inconclusive(_)));
    assert_eq!(left, right);
}

#[test]
fn shared_inputs_still_pay_materialization_limits() {
    let term = redex();
    let alias = term.clone();
    for materialization in [
        TermBudget::new(0, u64::MAX),
        TermBudget::new(u64::MAX, 0),
        TermBudget::unlimited().with_max_arena_nodes(0),
    ] {
        let budget = WhnfBudget::new(10_000, 10_000, materialization);
        let original = whnf(&term, &WhnfContext::default(), budget);
        let shared = whnf(&alias, &WhnfContext::default(), budget);
        assert!(matches!(original, WhnfOutcome::Inconclusive(_)));
        assert_eq!(original, shared);
    }
}
