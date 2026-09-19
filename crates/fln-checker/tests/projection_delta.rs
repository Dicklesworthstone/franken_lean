#![forbid(unsafe_code)]
use fln_checker::defeq::{DefEqBudget, DefEqOutcome, QuickDefEqBudget, def_eq, def_eq_with};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety,
    ConstructorDeclaration, DefinitionBody, DefinitionSafety, EnvironmentBudget,
    EnvironmentOutcome, InductiveDeclaration, ReducibilityHint,
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
fn projection_application_head_reduces_before_application_congruence() {
    let context = defined_projection_context(DefinitionSafety::Safe);
    let proj1 = Expr::proj(name("S"), 0, constant("dictionaryAlias"));
    let proj2 = Expr::proj(name("S"), 0, constant("dictionary"));
    let applied1 = Expr::app(proj1, Expr::app(identity(), nat_literal(19)));
    let applied2 = Expr::app(proj2, nat_literal(19));
    slow_equal(&decoded(&applied1), &decoded(&applied2), &context);
    slow_equal(&decoded(&applied2), &decoded(&applied1), &context);
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

fn structure_context(
    struct_name: &str,
    ctor_name: &str,
    num_params: u32,
    num_fields: u32,
) -> WhnfContext {
    let struct_wire = checker_name(struct_name);
    let ctor_wire = checker_name(ctor_name);
    let induct_meta = InductiveDeclaration::new(
        num_params,
        0,
        Vec::new(),
        vec![ctor_wire.clone()],
        0,
        false,
        false,
    );
    let ctor_meta = ConstructorDeclaration::new(struct_wire.clone(), 0, num_params, num_fields);
    let entries = vec![
        ConstantEntry::new(
            struct_wire,
            ConstantDeclaration::inductive(
                Vec::new(),
                decoded(&Expr::sort(Level::param(name("u")))),
                ConstantSafety::Safe,
                induct_meta,
            ),
        ),
        ConstantEntry::new(
            ctor_wire,
            ConstantDeclaration::constructor(
                Vec::new(),
                decoded(&Expr::sort(Level::param(name("u")))),
                ConstantSafety::Safe,
                ctor_meta,
            ),
        ),
    ];
    let EnvironmentOutcome::Complete { environment, .. } =
        ConstantEnvironment::build(entries, EnvironmentBudget::unlimited())
    else {
        panic!("environment build failed");
    };
    WhnfContext::new(Vec::new(), Vec::new(), environment)
}

#[test]
fn structure_eta_single_field_converts_symmetrically() {
    let context = structure_context("PLift", "PLift.up", 1, 1);
    let alpha = constant("A");
    let b = Expr::bvar(0).unwrap();
    let proj = Expr::proj(name("PLift"), 0, b.clone());
    let eta_term = Expr::app(Expr::app(constant("PLift.up"), alpha), proj);

    let lhs = decoded(&eta_term);
    let rhs = decoded(&b);
    assert!(matches!(
        def_eq(&lhs, &rhs, &context, DefEqBudget::unlimited()),
        DefEqOutcome::Equal(_)
    ));
    assert!(matches!(
        def_eq(&rhs, &lhs, &context, DefEqBudget::unlimited()),
        DefEqOutcome::Equal(_)
    ));
}

#[test]
fn structure_eta_multi_field_converts_symmetrically() {
    let context = structure_context("Pair", "Pair.mk", 2, 2);
    let alpha = constant("A");
    let beta = constant("B");
    let p = Expr::bvar(0).unwrap();
    let proj0 = Expr::proj(name("Pair"), 0, p.clone());
    let proj1 = Expr::proj(name("Pair"), 1, p.clone());
    let eta_term = Expr::app(
        Expr::app(
            Expr::app(Expr::app(constant("Pair.mk"), alpha), beta),
            proj0,
        ),
        proj1,
    );

    let lhs = decoded(&eta_term);
    let rhs = decoded(&p);
    assert!(matches!(
        def_eq(&lhs, &rhs, &context, DefEqBudget::unlimited()),
        DefEqOutcome::Equal(_)
    ));
    assert!(matches!(
        def_eq(&rhs, &lhs, &context, DefEqBudget::unlimited()),
        DefEqOutcome::Equal(_)
    ));
}

#[test]
fn structure_eta_rejects_swapped_fields_or_wrong_structure() {
    let context = structure_context("Pair", "Pair.mk", 2, 2);
    let alpha = constant("A");
    let beta = constant("B");
    let p = Expr::bvar(0).unwrap();
    // Swapped fields: Proj(Pair, 1, p) in field 0, Proj(Pair, 0, p) in field 1
    let proj0 = Expr::proj(name("Pair"), 0, p.clone());
    let proj1 = Expr::proj(name("Pair"), 1, p.clone());
    let swapped = Expr::app(
        Expr::app(
            Expr::app(Expr::app(constant("Pair.mk"), alpha), beta),
            proj1,
        ),
        proj0,
    );

    let lhs = decoded(&swapped);
    let rhs = decoded(&p);
    assert!(!matches!(
        def_eq(&lhs, &rhs, &context, DefEqBudget::unlimited()),
        DefEqOutcome::Equal(_)
    ));
}
