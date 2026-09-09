#![forbid(unsafe_code)]
use fln_checker::defeq::{DefEqBudget, DefEqOutcome, QuickDefEqBudget, def_eq, def_eq_with};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety, DefinitionBody,
    DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
};
use fln_checker::whnf::{ProjectionRule, WhnfBudget, WhnfContext};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::canon::Canonical;
fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn constant(s: &str) -> Expr {
    Expr::const_(name(s), Vec::new())
}
fn nat_literal(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn decoded(expr: &Expr) -> WireExpr {
    match decode_expr(&expr.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("wire input must decode: {other:?}"),
    }
}
fn checker_name(s: &str) -> WireName {
    match decode_name(&name(s).to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("wire name must decode: {other:?}"),
    }
}
fn identity() -> Expr {
    Expr::lam(
        name("x"),
        Expr::sort(Level::zero()),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    )
}
fn definition_entry(
    n: &str,
    value: WireExpr,
    hint: ReducibilityHint,
    safety: DefinitionSafety,
) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(n),
        ConstantDeclaration::definition(
            Vec::new(),
            decoded(&Expr::sort(Level::zero())),
            if safety == DefinitionSafety::Unsafe {
                ConstantSafety::Unsafe
            } else {
                ConstantSafety::Safe
            },
            DefinitionBody::new(value, hint, safety, Vec::new()),
        ),
    )
}
fn definition_context(entries: Vec<ConstantEntry>) -> WhnfContext {
    let EnvironmentOutcome::Complete { environment, .. } =
        ConstantEnvironment::build(entries, EnvironmentBudget::unlimited())
    else {
        panic!("environment");
    };
    WhnfContext::new(Vec::new(), Vec::new(), environment)
}
fn slow_equal(
    left: &WireExpr,
    right: &WireExpr,
    context: &WhnfContext,
) -> fln_checker::defeq::DefEqProgress {
    match def_eq(left, right, context, DefEqBudget::unlimited()) {
        DefEqOutcome::Equal(progress) => progress,
        other => panic!("expected conversion, got {other:?}"),
    }
}

fn defined_projection_context(safety: DefinitionSafety) -> WhnfContext {
    let env = definition_context(vec![
        definition_entry(
            "dictionary",
            decoded(&Expr::app(constant("MkS"), identity())),
            ReducibilityHint::Regular(3),
            safety,
        ),
        definition_entry(
            "dictionaryAlias",
            decoded(&constant("dictionary")),
            ReducibilityHint::Regular(4),
            DefinitionSafety::Safe,
        ),
    ]);
    WhnfContext::new(
        Vec::new(),
        vec![ProjectionRule::new(
            checker_name("S"),
            checker_name("MkS"),
            0,
        )],
        env.constants().clone(),
    )
}

#[test]
fn projection_conversion_unfolds_its_defined_major_and_retains_outer_arguments() {
    let context = defined_projection_context(DefinitionSafety::Safe);
    let projected = Expr::proj(name("S"), 0, constant("dictionaryAlias"));
    let result = slow_equal(&decoded(&projected), &decoded(&identity()), &context);
    assert!(result.delta_unfolds >= 2);
    let applied = Expr::app(projected, nat_literal(19));
    slow_equal(&decoded(&applied), &decoded(&nat_literal(19)), &context);
    slow_equal(&decoded(&nat_literal(19)), &decoded(&applied), &context);
}

#[test]
fn projection_delta_does_not_bypass_constructor_field_or_safety_checks() {
    for (structure, field, safety) in [
        ("OtherStructure", 0, DefinitionSafety::Safe),
        ("S", 1, DefinitionSafety::Safe),
        ("S", 0, DefinitionSafety::Unsafe),
    ] {
        let context = defined_projection_context(safety);
        let projected = decoded(&Expr::proj(
            name(structure),
            field,
            constant("dictionaryAlias"),
        ));
        assert!(!matches!(
            def_eq(
                &projected,
                &decoded(&identity()),
                &context,
                DefEqBudget::unlimited()
            ),
            DefEqOutcome::Equal(_)
        ));
    }
}

#[test]
fn projection_delta_budget_stop_and_cancellation_do_not_become_conversion() {
    let context = defined_projection_context(DefinitionSafety::Safe);
    let projected = decoded(&Expr::proj(name("S"), 0, constant("dictionaryAlias")));
    let rhs = decoded(&identity());
    let budget = DefEqBudget::new(
        QuickDefEqBudget::unlimited(),
        u64::MAX,
        2,
        u64::MAX,
        u64::MAX,
        WhnfBudget::unlimited(),
    );
    assert!(matches!(
        def_eq(&projected, &rhs, &context, budget),
        DefEqOutcome::Inconclusive(_)
    ));
    assert!(matches!(
        def_eq_with(&projected, &rhs, &context, DefEqBudget::unlimited(), || {
            true
        }),
        DefEqOutcome::Inconclusive(_)
    ));
    slow_equal(&projected, &rhs, &context);
}
