#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::term::{
    TermBudget, TermFacts, TermLimit, TermOutcome, TermStop, abstract_free, inspect, inspect_with,
    raise_external_bounds, raise_external_bounds_with, substitute_bound, substitute_free,
    substitute_free_with,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, ExprId, ExprNode, LevelNode, NamePart, WireExpr, WireName,
    decode_expr, decode_name,
};
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap, SyntaxHandle};
use fln_hash::canon::{CanonWriter, Canonical, SCHEMA_EXPR};

fn decoded(expression: &Expr) -> WireExpr {
    match decode_expr(&expression.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced expression did not decode: {other:?}"),
    }
}

fn checker_name(value: &str) -> WireName {
    let primary = Name::str(Name::anonymous(), value);
    match decode_name(&primary.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced name did not decode: {other:?}"),
    }
}

fn complete<T>(outcome: TermOutcome<T>) -> T {
    match outcome {
        TermOutcome::Complete(value) => value,
        TermOutcome::Inconclusive(stop) => panic!("unexpected non-answer: {stop:?}"),
        TermOutcome::InternalFault(fault) => panic!("unexpected internal fault: {fault:?}"),
    }
}

fn generated_primary_terms() -> Vec<Expr> {
    let x = Name::str(Name::anonymous(), "x");
    let u = Name::str(Name::anonymous(), "u");
    let m = Name::str(Name::anonymous(), "m");
    let parameter = Level::param(u.clone());
    let universe_meta = Level::mvar(LMVarId(m.clone()));
    let mut terms = vec![
        Expr::bvar(0).expect("bounded"),
        Expr::bvar(3).expect("bounded"),
        Expr::fvar(FVarId(x.clone())),
        Expr::mvar(MVarId(m)),
        Expr::sort(parameter.clone()),
        Expr::sort(universe_meta.clone()),
        Expr::const_(
            Name::str(Name::anonymous(), "C"),
            vec![parameter, universe_meta],
        ),
        Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![3, 5]))),
        Expr::lit(Literal::Str("term-facts".to_owned())),
    ];

    for round in 0..3 {
        let sample: Vec<_> = terms.iter().take(18 + round * 4).cloned().collect();
        for (index, term) in sample.iter().enumerate() {
            let other = sample[(index * 5 + 3) % sample.len()].clone();
            let type_ = Expr::sort(Level::zero());
            terms.push(Expr::app(term.clone(), other.clone()));
            terms.push(Expr::lam(
                Name::anonymous(),
                type_.clone(),
                term.clone(),
                BinderInfo::Default,
            ));
            terms.push(Expr::forall_e(
                Name::anonymous(),
                type_.clone(),
                term.clone(),
                BinderInfo::Implicit,
            ));
            terms.push(Expr::let_e(
                Name::anonymous(),
                type_,
                other,
                term.clone(),
                index % 2 == 0,
            ));
            terms.push(Expr::mdata(KVMap::new(), term.clone()));
            terms.push(Expr::proj(
                Name::str(Name::anonymous(), "S"),
                (index % 3) as u64,
                term.clone(),
            ));
        }
    }
    terms
}

#[test]
fn facts_match_primary_packed_answers_over_generated_terms() {
    let terms = generated_primary_terms();
    assert!(
        terms.len() > 200,
        "the generated corpus must stay nontrivial"
    );
    for (index, expression) in terms.iter().enumerate() {
        let facts = complete(inspect(&decoded(expression), TermBudget::unlimited()));
        assert_eq!(
            facts,
            TermFacts {
                external_bound_span: expression.loose_bvar_range(),
                contains_free: expression.has_fvar(),
                contains_expression_meta: expression.has_expr_mvar(),
                contains_universe_meta: expression.has_level_mvar(),
                contains_universe_parameter: expression.has_level_param(),
                approximate_depth: expression.approx_depth(),
            },
            "fact drift at generated expression {index}: {expression:?}"
        );
    }
}

#[test]
fn binders_adjust_only_body_scope_and_every_leaf_flag_is_live() {
    let free = Expr::fvar(FVarId(Name::str(Name::anonymous(), "free")));
    let meta = Expr::mvar(MVarId(Name::str(Name::anonymous(), "meta")));
    let universe = Level::max(
        Level::param(Name::str(Name::anonymous(), "u")),
        Level::mvar(LMVarId(Name::str(Name::anonymous(), "v"))),
    )
    .expect("shallow level");
    let flags = Expr::app(
        Expr::app(free, meta),
        Expr::const_(Name::str(Name::anonymous(), "C"), vec![universe]),
    );
    let body = Expr::app(
        Expr::bvar(0).expect("bound"),
        Expr::app(Expr::bvar(3).expect("bound"), flags),
    );
    let expression = Expr::lam(
        Name::anonymous(),
        Expr::bvar(2).expect("bound"),
        body,
        BinderInfo::Default,
    );
    let facts = complete(inspect(&decoded(&expression), TermBudget::unlimited()));

    assert_eq!(facts.external_bound_span, 3);
    assert!(facts.contains_free);
    assert!(facts.contains_expression_meta);
    assert!(facts.contains_universe_meta);
    assert!(facts.contains_universe_parameter);
    assert_eq!(facts.approximate_depth, expression.approx_depth());
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Model {
    Bound(u32),
    Free(String),
    Meta(String),
    Sort,
    Constant(String),
    Apply(Box<Model>, Box<Model>),
    Lambda(Box<Model>, Box<Model>),
    Forall(Box<Model>, Box<Model>),
    Let {
        type_: Box<Model>,
        value: Box<Model>,
        body: Box<Model>,
        non_dependent: bool,
    },
    Nat(Vec<u64>),
    String(String),
    Metadata(Box<Model>),
    Projection(u64, Box<Model>),
}

fn model_name(name: &WireName) -> String {
    match name.parts().last() {
        Some(NamePart::Text(value)) => value.clone(),
        Some(NamePart::Numeric { value, overflowed }) => {
            format!("{value}:overflow={overflowed}")
        }
        None => String::new(),
    }
}

fn wire_model(term: &WireExpr, id: ExprId) -> Model {
    match term.node(id).expect("valid expression id") {
        ExprNode::Bound { index } => Model::Bound(*index),
        ExprNode::Free { name } => Model::Free(model_name(name)),
        ExprNode::Meta { name } => Model::Meta(model_name(name)),
        ExprNode::Sort { .. } => Model::Sort,
        ExprNode::Constant { name, .. } => Model::Constant(model_name(name)),
        ExprNode::Apply { function, argument } => Model::Apply(
            Box::new(wire_model(term, *function)),
            Box::new(wire_model(term, *argument)),
        ),
        ExprNode::Lambda {
            binder_type, body, ..
        } => Model::Lambda(
            Box::new(wire_model(term, *binder_type)),
            Box::new(wire_model(term, *body)),
        ),
        ExprNode::Forall {
            binder_type, body, ..
        } => Model::Forall(
            Box::new(wire_model(term, *binder_type)),
            Box::new(wire_model(term, *body)),
        ),
        ExprNode::Let {
            type_,
            value,
            body,
            non_dependent,
            ..
        } => Model::Let {
            type_: Box::new(wire_model(term, *type_)),
            value: Box::new(wire_model(term, *value)),
            body: Box::new(wire_model(term, *body)),
            non_dependent: *non_dependent,
        },
        ExprNode::NatLiteral { limbs_le } => Model::Nat(limbs_le.clone()),
        ExprNode::StringLiteral(value) => Model::String(value.clone()),
        ExprNode::Metadata { expression, .. } => {
            Model::Metadata(Box::new(wire_model(term, *expression)))
        }
        ExprNode::Projection {
            index, expression, ..
        } => Model::Projection(*index, Box::new(wire_model(term, *expression))),
    }
}

fn model_expr(model: &Model) -> Expr {
    match model {
        Model::Bound(index) => Expr::bvar(*index).expect("model bound packs"),
        Model::Free(name) => Expr::fvar(FVarId(Name::str(Name::anonymous(), name))),
        Model::Meta(name) => Expr::mvar(MVarId(Name::str(Name::anonymous(), name))),
        Model::Sort => Expr::sort(Level::zero()),
        Model::Constant(name) => Expr::const_(Name::str(Name::anonymous(), name), Vec::new()),
        Model::Apply(function, argument) => Expr::app(model_expr(function), model_expr(argument)),
        Model::Lambda(type_, body) => Expr::lam(
            Name::anonymous(),
            model_expr(type_),
            model_expr(body),
            BinderInfo::Default,
        ),
        Model::Forall(type_, body) => Expr::forall_e(
            Name::anonymous(),
            model_expr(type_),
            model_expr(body),
            BinderInfo::Implicit,
        ),
        Model::Let {
            type_,
            value,
            body,
            non_dependent,
        } => Expr::let_e(
            Name::anonymous(),
            model_expr(type_),
            model_expr(value),
            model_expr(body),
            *non_dependent,
        ),
        Model::Nat(limbs) => Expr::lit(Literal::Nat(NatLit::from_limbs_le(limbs.clone()))),
        Model::String(value) => Expr::lit(Literal::Str(value.clone())),
        Model::Metadata(expression) => Expr::mdata(KVMap::new(), model_expr(expression)),
        Model::Projection(index, expression) => Expr::proj(
            Name::str(Name::anonymous(), "S"),
            *index,
            model_expr(expression),
        ),
    }
}

fn map_nonbinding(
    model: &Model,
    recur: &mut impl FnMut(&Model, u32) -> Model,
    scope: u32,
) -> Model {
    match model {
        Model::Bound(index) => Model::Bound(*index),
        Model::Free(name) => Model::Free(name.clone()),
        Model::Meta(name) => Model::Meta(name.clone()),
        Model::Sort => Model::Sort,
        Model::Constant(name) => Model::Constant(name.clone()),
        Model::Apply(function, argument) => Model::Apply(
            Box::new(recur(function, scope)),
            Box::new(recur(argument, scope)),
        ),
        Model::Lambda(type_, body) => Model::Lambda(
            Box::new(recur(type_, scope)),
            Box::new(recur(body, scope + 1)),
        ),
        Model::Forall(type_, body) => Model::Forall(
            Box::new(recur(type_, scope)),
            Box::new(recur(body, scope + 1)),
        ),
        Model::Let {
            type_,
            value,
            body,
            non_dependent,
        } => Model::Let {
            type_: Box::new(recur(type_, scope)),
            value: Box::new(recur(value, scope)),
            body: Box::new(recur(body, scope + 1)),
            non_dependent: *non_dependent,
        },
        Model::Nat(limbs) => Model::Nat(limbs.clone()),
        Model::String(value) => Model::String(value.clone()),
        Model::Metadata(expression) => Model::Metadata(Box::new(recur(expression, scope))),
        Model::Projection(index, expression) => {
            Model::Projection(*index, Box::new(recur(expression, scope)))
        }
    }
}

fn model_raise(model: &Model, amount: u32, cutoff: u32, scope: u32) -> Model {
    if let Model::Bound(index) = model {
        let threshold = cutoff + scope;
        return Model::Bound(if *index >= threshold {
            index + amount
        } else {
            *index
        });
    }
    map_nonbinding(
        model,
        &mut |child, child_scope| model_raise(child, amount, cutoff, child_scope),
        scope,
    )
}

fn model_substitute_bound(model: &Model, target: u32, replacement: &Model, scope: u32) -> Model {
    if let Model::Bound(index) = model {
        let sought = target + scope;
        return if *index == sought {
            model_raise(replacement, scope, 0, 0)
        } else if *index > sought {
            Model::Bound(index - 1)
        } else {
            Model::Bound(*index)
        };
    }
    map_nonbinding(
        model,
        &mut |child, child_scope| model_substitute_bound(child, target, replacement, child_scope),
        scope,
    )
}

fn model_abstract_free(model: &Model, target: &str, scope: u32) -> Model {
    match model {
        Model::Bound(index) => {
            return Model::Bound(if *index >= scope { index + 1 } else { *index });
        }
        Model::Free(name) if name == target => return Model::Bound(scope),
        _ => {}
    }
    map_nonbinding(
        model,
        &mut |child, child_scope| model_abstract_free(child, target, child_scope),
        scope,
    )
}

fn model_substitute_free(model: &Model, target: &str, replacement: &Model, scope: u32) -> Model {
    if matches!(model, Model::Free(name) if name == target) {
        return model_raise(replacement, scope, 0, 0);
    }
    map_nonbinding(
        model,
        &mut |child, child_scope| model_substitute_free(child, target, replacement, child_scope),
        scope,
    )
}

fn generated_models() -> Vec<Model> {
    let mut models = vec![
        Model::Bound(0),
        Model::Bound(1),
        Model::Bound(3),
        Model::Free("x".to_owned()),
        Model::Free("y".to_owned()),
        Model::Meta("m".to_owned()),
        Model::Sort,
        Model::Constant("C".to_owned()),
        Model::Nat(vec![7, 9]),
        Model::String("s".to_owned()),
    ];
    for round in 0..3 {
        let sample: Vec<_> = models.iter().take(20 + round * 5).cloned().collect();
        for (index, model) in sample.iter().enumerate() {
            let other = sample[(index * 7 + 1) % sample.len()].clone();
            models.push(Model::Apply(
                Box::new(model.clone()),
                Box::new(other.clone()),
            ));
            models.push(Model::Lambda(
                Box::new(Model::Sort),
                Box::new(model.clone()),
            ));
            models.push(Model::Forall(
                Box::new(Model::Sort),
                Box::new(model.clone()),
            ));
            models.push(Model::Let {
                type_: Box::new(Model::Sort),
                value: Box::new(other),
                body: Box::new(model.clone()),
                non_dependent: index % 2 == 0,
            });
            models.push(Model::Metadata(Box::new(model.clone())));
            models.push(Model::Projection(
                (index % 3) as u64,
                Box::new(model.clone()),
            ));
        }
    }
    models
}

#[test]
fn generated_transform_model_matches_checker() {
    let models = generated_models();
    assert!(models.len() > 300);
    let replacement = Model::Apply(
        Box::new(Model::Bound(0)),
        Box::new(Model::Free("z".to_owned())),
    );
    let replacement_wire = decoded(&model_expr(&replacement));
    let x = checker_name("x");

    for (index, model) in models.iter().enumerate() {
        let term = decoded(&model_expr(model));
        let raised = complete(raise_external_bounds(&term, 2, 1, TermBudget::unlimited()));
        assert_eq!(
            wire_model(&raised, raised.root()),
            model_raise(model, 2, 1, 0),
            "raise drift at model {index}"
        );

        let opened = complete(substitute_bound(
            &term,
            0,
            &replacement_wire,
            TermBudget::unlimited(),
        ));
        assert_eq!(
            wire_model(&opened, opened.root()),
            model_substitute_bound(model, 0, &replacement, 0),
            "bound substitution drift at model {index}"
        );

        let closed = complete(abstract_free(&term, &x, TermBudget::unlimited()));
        assert_eq!(
            wire_model(&closed, closed.root()),
            model_abstract_free(model, "x", 0),
            "free abstraction drift at model {index}"
        );

        let replaced = complete(substitute_free(
            &term,
            &x,
            &replacement_wire,
            TermBudget::unlimited(),
        ));
        assert_eq!(
            wire_model(&replaced, replaced.root()),
            model_substitute_free(model, "x", &replacement, 0),
            "free substitution drift at model {index}"
        );
    }
}

#[test]
fn bound_substitution_is_capture_avoiding_and_decrements_only_looser_indices() {
    let subject = Model::Apply(
        Box::new(Model::Bound(0)),
        Box::new(Model::Apply(
            Box::new(Model::Bound(1)),
            Box::new(Model::Lambda(
                Box::new(Model::Sort),
                Box::new(Model::Apply(
                    Box::new(Model::Bound(1)),
                    Box::new(Model::Bound(2)),
                )),
            )),
        )),
    );
    let replacement = Model::Bound(0);
    let subject_wire = decoded(&model_expr(&subject));
    let replacement_wire = decoded(&model_expr(&replacement));
    let actual = complete(substitute_bound(
        &subject_wire,
        0,
        &replacement_wire,
        TermBudget::unlimited(),
    ));
    assert_eq!(
        wire_model(&actual, actual.root()),
        model_substitute_bound(&subject, 0, &replacement, 0)
    );
    assert_eq!(
        wire_model(&actual, actual.root()),
        Model::Apply(
            Box::new(Model::Bound(0)),
            Box::new(Model::Apply(
                Box::new(Model::Bound(0)),
                Box::new(Model::Lambda(
                    Box::new(Model::Sort),
                    Box::new(Model::Apply(
                        Box::new(Model::Bound(1)),
                        Box::new(Model::Bound(1)),
                    )),
                )),
            )),
        )
    );
}

#[test]
fn free_abstraction_shifts_external_bounds_and_respects_nested_binders() {
    let subject = Model::Apply(
        Box::new(Model::Bound(0)),
        Box::new(Model::Lambda(
            Box::new(Model::Sort),
            Box::new(Model::Apply(
                Box::new(Model::Free("x".to_owned())),
                Box::new(Model::Bound(1)),
            )),
        )),
    );
    let term = decoded(&model_expr(&subject));
    let x = checker_name("x");
    let actual = complete(abstract_free(&term, &x, TermBudget::unlimited()));
    assert_eq!(
        wire_model(&actual, actual.root()),
        Model::Apply(
            Box::new(Model::Bound(1)),
            Box::new(Model::Lambda(
                Box::new(Model::Sort),
                Box::new(Model::Apply(
                    Box::new(Model::Bound(1)),
                    Box::new(Model::Bound(2)),
                )),
            )),
        )
    );
}

#[test]
fn free_substitution_raises_replacement_under_binders() {
    let subject = Model::Lambda(
        Box::new(Model::Sort),
        Box::new(Model::Apply(
            Box::new(Model::Free("x".to_owned())),
            Box::new(Model::Bound(0)),
        )),
    );
    let replacement = Model::Bound(0);
    let term = decoded(&model_expr(&subject));
    let replacement_wire = decoded(&model_expr(&replacement));
    let actual = complete(substitute_free(
        &term,
        &checker_name("x"),
        &replacement_wire,
        TermBudget::unlimited(),
    ));
    assert_eq!(
        wire_model(&actual, actual.root()),
        Model::Lambda(
            Box::new(Model::Sort),
            Box::new(Model::Apply(
                Box::new(Model::Bound(1)),
                Box::new(Model::Bound(0)),
            )),
        )
    );

    let universe_replacement = decoded(&Expr::sort(
        Level::max(
            Level::param(Name::str(Name::anonymous(), "u")),
            Level::mvar(LMVarId(Name::str(Name::anonymous(), "v"))),
        )
        .expect("shallow replacement universe"),
    ));
    let two_occurrences = decoded(&Expr::lam(
        Name::anonymous(),
        Expr::sort(Level::zero()),
        Expr::app(
            Expr::fvar(FVarId(Name::str(Name::anonymous(), "x"))),
            Expr::fvar(FVarId(Name::str(Name::anonymous(), "x"))),
        ),
        BinderInfo::Default,
    ));
    let with_universes = complete(substitute_free(
        &two_occurrences,
        &checker_name("x"),
        &universe_replacement,
        TermBudget::unlimited(),
    ));
    let facts = complete(inspect(&with_universes, TermBudget::unlimited()));
    assert!(facts.contains_universe_meta);
    assert!(facts.contains_universe_parameter);
    assert!(!facts.contains_free);

    let absent = complete(substitute_free(
        &two_occurrences,
        &checker_name("absent"),
        &universe_replacement,
        TermBudget::unlimited(),
    ));
    assert_eq!(
        absent, two_occurrences,
        "an unused replacement must not add unreachable arena levels"
    );
}

fn all_variants_expression() -> Expr {
    let name = Name::str(Name::anonymous(), "n");
    let type_ = Expr::sort(Level::one());
    let locals = Expr::app(
        Expr::app(
            Expr::bvar(0).expect("bound"),
            Expr::fvar(FVarId(Name::str(Name::anonymous(), "free"))),
        ),
        Expr::mvar(MVarId(Name::str(Name::anonymous(), "meta"))),
    );
    let constants = Expr::app(
        Expr::const_(
            name.clone(),
            vec![
                Level::param(Name::str(Name::anonymous(), "u")),
                Level::mvar(LMVarId(Name::str(Name::anonymous(), "v"))),
            ],
        ),
        Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![4, 8]))),
    );
    let body = Expr::app(
        Expr::app(constants, locals),
        Expr::lit(Literal::Str("all-variants".to_owned())),
    );
    let lambda = Expr::lam(
        name.clone(),
        type_.clone(),
        body,
        BinderInfo::StrictImplicit,
    );
    let forall = Expr::forall_e(
        name.clone(),
        type_.clone(),
        lambda,
        BinderInfo::InstImplicit,
    );
    let let_expr = Expr::let_e(
        name.clone(),
        type_,
        Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![1]))),
        forall,
        true,
    );
    let metadata = KVMap::from_entries(vec![
        (
            Name::str(Name::anonymous(), "text"),
            DataValue::OfString("metadata".to_owned()),
        ),
        (name.clone(), DataValue::OfBool(true)),
        (
            Name::str(Name::anonymous(), "name"),
            DataValue::OfName(name.clone()),
        ),
        (Name::str(Name::anonymous(), "nat"), DataValue::OfNat(42)),
        (Name::str(Name::anonymous(), "int"), DataValue::OfInt(-7)),
        (
            Name::str(Name::anonymous(), "syntax"),
            DataValue::OfSyntax(SyntaxHandle(9)),
        ),
    ]);
    Expr::mdata(metadata, Expr::proj(name, 2, let_expr))
}

#[test]
fn metadata_projection_and_all_expression_variants_survive_every_transform() {
    let original = decoded(&all_variants_expression());
    let identity = complete(raise_external_bounds(
        &original,
        0,
        0,
        TermBudget::unlimited(),
    ));
    assert_eq!(identity, original);

    let nested = Expr::mdata(
        KVMap::new(),
        Expr::proj(
            Name::str(Name::anonymous(), "S"),
            1,
            Expr::bvar(0).expect("bound"),
        ),
    );
    let raised = complete(raise_external_bounds(
        &decoded(&nested),
        1,
        0,
        TermBudget::unlimited(),
    ));
    let root = raised.node(raised.root()).expect("metadata root");
    let ExprNode::Metadata { expression, .. } = root else {
        panic!("metadata wrapper was skipped: {root:?}");
    };
    let ExprNode::Projection { expression, .. } = raised.node(*expression).expect("projection")
    else {
        panic!("projection wrapper was skipped");
    };
    assert!(matches!(
        raised.node(*expression),
        Some(ExprNode::Bound { index: 1 })
    ));
}

#[test]
fn resource_and_cancellation_are_typed_nonanswers_with_exact_recovery() {
    let term = decoded(&model_expr(&Model::Apply(
        Box::new(Model::Free("x".to_owned())),
        Box::new(Model::Bound(0)),
    )));
    let replacement = decoded(&model_expr(&Model::Bound(0)));
    let pristine = term.clone();

    assert!(matches!(
        inspect(&term, TermBudget::new(0, u64::MAX)),
        TermOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::Steps,
            ..
        })
    ));
    assert!(matches!(
        inspect_with(&term, TermBudget::unlimited(), || true),
        TermOutcome::Inconclusive(TermStop::Cancelled { .. })
    ));
    assert!(matches!(
        substitute_free(
            &term,
            &checker_name("x"),
            &replacement,
            TermBudget::new(u64::MAX, 0),
        ),
        TermOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::OutputUnits,
            ..
        })
    ));
    assert!(matches!(
        substitute_free(
            &term,
            &checker_name("x"),
            &replacement,
            TermBudget::unlimited().with_max_arena_nodes(1),
        ),
        TermOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::ArenaNodes,
            allowed: 1,
            observed: 2,
            ..
        })
    ));

    let mut polls = 0;
    assert!(matches!(
        substitute_free_with(
            &term,
            &checker_name("x"),
            &replacement,
            TermBudget::unlimited(),
            || {
                polls += 1;
                polls == 3
            },
        ),
        TermOutcome::Inconclusive(TermStop::Cancelled { .. })
    ));
    assert_eq!(term, pristine, "a stopped rewrite mutated its input");

    let recovered = complete(substitute_free(
        &term,
        &checker_name("x"),
        &replacement,
        TermBudget::unlimited(),
    ));
    assert_eq!(
        wire_model(&recovered, recovered.root()),
        Model::Apply(Box::new(Model::Bound(0)), Box::new(Model::Bound(0)))
    );
}

#[test]
fn large_owned_payloads_are_charged_before_retention() {
    let payload = "payload".repeat(16 * 1024);
    let payload_units = payload.len() as u64 + 2;
    let expression = Expr::mvar(MVarId(Name::str(Name::anonymous(), payload)));
    let term = decoded(&expression);

    assert!(matches!(
        raise_external_bounds(
            &term,
            0,
            0,
            TermBudget::new(u64::MAX, payload_units - 1),
        ),
        TermOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::OutputUnits,
            allowed,
            observed,
            completed_steps: 1,
            ..
        }) if allowed == payload_units - 1 && observed == payload_units
    ));

    let mut polls = 0;
    assert!(matches!(
        raise_external_bounds_with(&term, 0, 0, TermBudget::unlimited(), || {
            polls += 1;
            polls == 2
        }),
        TermOutcome::Inconclusive(TermStop::Cancelled {
            polls: 2,
            completed_steps: 1,
            ..
        })
    ));

    let retained = complete(raise_external_bounds(
        &term,
        0,
        0,
        TermBudget::new(u64::MAX, payload_units),
    ));
    assert_eq!(retained, term);
}

#[test]
fn bound_index_overflow_is_a_typed_resource_stop() {
    const MAX_INDEX: u32 = (1 << 20) - 2;
    let term = decoded(&Expr::bvar(MAX_INDEX).expect("schema maximum packs"));
    assert!(matches!(
        raise_external_bounds(&term, 1, 0, TermBudget::unlimited()),
        TermOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::BoundIndex,
            allowed,
            observed,
            ..
        }) if allowed == u64::from(MAX_INDEX) && observed == u64::from(MAX_INDEX) + 1
    ));
}

#[test]
fn production_arenas_preserve_backward_reference_invariants() {
    let term = decoded(&all_variants_expression());
    assert!(term.root().index() < term.nodes().len());
    for (parent, node) in term.nodes().iter().enumerate() {
        let children: Vec<ExprId> = match node {
            ExprNode::Apply { function, argument } => vec![*function, *argument],
            ExprNode::Lambda {
                binder_type, body, ..
            }
            | ExprNode::Forall {
                binder_type, body, ..
            } => vec![*binder_type, *body],
            ExprNode::Let {
                type_, value, body, ..
            } => vec![*type_, *value, *body],
            ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                vec![*expression]
            }
            ExprNode::Bound { .. }
            | ExprNode::Free { .. }
            | ExprNode::Meta { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Constant { .. }
            | ExprNode::NatLiteral { .. }
            | ExprNode::StringLiteral(_) => Vec::new(),
        };
        assert!(
            children.iter().all(|child| child.index() < parent),
            "expression parent {parent} has a non-backward child: {children:?}"
        );
    }
    for (parent, node) in term.levels().iter().enumerate() {
        let children = match node {
            LevelNode::Succ(child) => vec![*child],
            LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                vec![*left, *right]
            }
            LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => Vec::new(),
        };
        assert!(
            children.iter().all(|child| child.index() < parent),
            "level parent {parent} has a non-backward child: {children:?}"
        );
    }
}

fn deep_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_EXPR);
    for _ in 0..DEPTH {
        writer.u8(11);
        writer.u64(0);
    }
    writer.u8(0);
    writer.u32(0);
    let term = match decode_expr(&writer.into_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => {
            return Err(format!(
                "deep primary-shaped bytes did not decode: {other:?}"
            ));
        }
    };
    let facts = match inspect(&term, TermBudget::unlimited()) {
        TermOutcome::Complete(value) => value,
        other => return Err(format!("deep facts walk failed: {other:?}")),
    };
    if facts.external_bound_span != 1 || facts.approximate_depth != 255 {
        return Err(format!("deep facts drifted: {facts:?}"));
    }
    let raised = match raise_external_bounds(&term, 1, 0, TermBudget::unlimited()) {
        TermOutcome::Complete(value) => value,
        other => return Err(format!("deep rewrite failed: {other:?}")),
    };
    if raised.nodes().len() != DEPTH + 1 {
        return Err(format!(
            "deep output node count drifted: {}",
            raised.nodes().len()
        ));
    }
    let raised_facts = match inspect(&raised, TermBudget::unlimited()) {
        TermOutcome::Complete(value) => value,
        other => return Err(format!("deep output facts failed: {other:?}")),
    };
    if raised_facts.external_bound_span != 2 {
        return Err(format!("deep output bound span drifted: {raised_facts:?}"));
    }
    Ok(())
}

#[test]
fn deep_term_walks_and_transforms_fit_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_TERM_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-term-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_child)
            .expect("spawn bounded-stack child thread")
            .join()
            .expect("bounded-stack child thread did not panic");
        result.expect("bounded-stack term work");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "deep_term_walks_and_transforms_fit_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack child process");
    assert!(
        output.status.success(),
        "bounded-stack child failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn term_production_code_has_no_primary_semantic_path() {
    let source = include_str!("../src/term.rs");
    for forbidden in [
        "fln_core::",
        ".loose_bvar_range(",
        ".has_fvar(",
        ".has_expr_mvar(",
        ".has_level_mvar(",
        ".has_level_param(",
        ".approx_depth(",
    ] {
        assert!(
            !source.contains(forbidden),
            "checker term source shares forbidden semantic path `{forbidden}`"
        );
    }
}
