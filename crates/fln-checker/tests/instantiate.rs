#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::instantiate::{
    InstantiationOutcome, InstantiationRefusal, instantiate_level_parameters,
    instantiate_level_parameters_with, instantiate_term_parameters,
};
use fln_checker::term::{TermBudget, TermLimit, TermStop};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, ExprId, ExprNode, LevelId, LevelNode, NamePart, WireExpr,
    WireLevel, WireName, decode_expr, decode_level, decode_name,
};
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap, SyntaxHandle};
use fln_hash::canon::{CanonWriter, Canonical, SCHEMA_LEVEL};

fn decoded_level(level: &Level) -> WireLevel {
    match decode_level(&level.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced level did not decode: {other:?}"),
    }
}

fn decoded_expr(expression: &Expr) -> WireExpr {
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

fn complete<T>(outcome: InstantiationOutcome<T>) -> T {
    match outcome {
        InstantiationOutcome::Complete(value) => value,
        InstantiationOutcome::Refused(refusal) => {
            panic!("unexpected instantiation refusal: {refusal:?}")
        }
        InstantiationOutcome::Inconclusive(stop) => {
            panic!("unexpected instantiation non-answer: {stop:?}")
        }
        InstantiationOutcome::InternalFault(fault) => {
            panic!("unexpected instantiation fault: {fault:?}")
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Model {
    Zero,
    Succ(Box<Model>),
    Max(Box<Model>, Box<Model>),
    IMax(Box<Model>, Box<Model>),
    Parameter(String),
    Meta(String),
}

fn primary_name(value: &str) -> Name {
    Name::str(Name::anonymous(), value)
}

fn primary(model: &Model) -> Level {
    match model {
        Model::Zero => Level::zero(),
        Model::Succ(child) => primary(child).succ().expect("generated level is shallow"),
        Model::Max(left, right) => {
            Level::max(primary(left), primary(right)).expect("generated level is shallow")
        }
        Model::IMax(left, right) => {
            Level::imax(primary(left), primary(right)).expect("generated level is shallow")
        }
        Model::Parameter(name) => Level::param(primary_name(name)),
        Model::Meta(name) => Level::mvar(LMVarId(primary_name(name))),
    }
}

fn model_name(name: &WireName) -> String {
    match name.parts().last() {
        Some(NamePart::Text(value)) => value.clone(),
        Some(NamePart::Numeric { value, .. }) => value.to_string(),
        None => String::new(),
    }
}

fn wire_model(level: &WireLevel, id: LevelId) -> Model {
    match level.node(id).expect("model level id exists") {
        LevelNode::Zero => Model::Zero,
        LevelNode::Succ(child) => Model::Succ(Box::new(wire_model(level, *child))),
        LevelNode::Max(left, right) => Model::Max(
            Box::new(wire_model(level, *left)),
            Box::new(wire_model(level, *right)),
        ),
        LevelNode::IMax(left, right) => Model::IMax(
            Box::new(wire_model(level, *left)),
            Box::new(wire_model(level, *right)),
        ),
        LevelNode::Parameter(name) => Model::Parameter(model_name(name)),
        LevelNode::Meta(name) => Model::Meta(model_name(name)),
    }
}

fn term_level_model(term: &WireExpr, id: LevelId) -> Model {
    match term.level(id).expect("term level id exists") {
        LevelNode::Zero => Model::Zero,
        LevelNode::Succ(child) => Model::Succ(Box::new(term_level_model(term, *child))),
        LevelNode::Max(left, right) => Model::Max(
            Box::new(term_level_model(term, *left)),
            Box::new(term_level_model(term, *right)),
        ),
        LevelNode::IMax(left, right) => Model::IMax(
            Box::new(term_level_model(term, *left)),
            Box::new(term_level_model(term, *right)),
        ),
        LevelNode::Parameter(name) => Model::Parameter(model_name(name)),
        LevelNode::Meta(name) => Model::Meta(model_name(name)),
    }
}

fn model_offset(mut model: &Model) -> (&Model, usize) {
    let mut offset = 0;
    while let Model::Succ(child) = model {
        model = child;
        offset += 1;
    }
    (model, offset)
}

fn model_nonzero(model: &Model) -> bool {
    match model {
        Model::Succ(_) => true,
        Model::Max(left, right) => model_nonzero(left) || model_nonzero(right),
        Model::IMax(_, right) => model_nonzero(right),
        Model::Zero | Model::Parameter(_) | Model::Meta(_) => false,
    }
}

fn model_max(left: Model, right: Model) -> Model {
    let (left_base, left_offset) = model_offset(&left);
    let (right_base, right_offset) = model_offset(&right);
    if left_base == &Model::Zero && right_base == &Model::Zero {
        return if left_offset >= right_offset {
            left
        } else {
            right
        };
    }
    if left == right || right == Model::Zero {
        return left;
    }
    if left == Model::Zero {
        return right;
    }
    if matches!(&right, Model::Max(a, b) if a.as_ref() == &left || b.as_ref() == &left) {
        return right;
    }
    if matches!(&left, Model::Max(a, b) if a.as_ref() == &right || b.as_ref() == &right) {
        return left;
    }
    if left_base == right_base {
        return if left_offset > right_offset {
            left
        } else {
            right
        };
    }
    Model::Max(Box::new(left), Box::new(right))
}

fn model_imax(left: Model, right: Model) -> Model {
    if model_nonzero(&right) {
        model_max(left, right)
    } else if right == Model::Zero
        || left == Model::Zero
        || left == Model::Succ(Box::new(Model::Zero))
    {
        right
    } else if left == right {
        left
    } else {
        Model::IMax(Box::new(left), Box::new(right))
    }
}

// The frozen model originally copied every rebuilt Max/IMax literally. That
// contradicted the pin's update_max, so the changed-ancestor rule now models
// its smart constructors; no-op subjects and replacement values remain raw.
fn frozen_substitute_changed(
    model: &Model,
    parameters: &[String],
    values: &[Model],
) -> (Model, bool) {
    match model {
        Model::Zero => (Model::Zero, false),
        Model::Succ(child) => {
            let (child, changed) = frozen_substitute_changed(child, parameters, values);
            (Model::Succ(Box::new(child)), changed)
        }
        Model::Max(left, right) | Model::IMax(left, right) => {
            let (left, changed_left) = frozen_substitute_changed(left, parameters, values);
            let (right, changed_right) = frozen_substitute_changed(right, parameters, values);
            let changed = changed_left || changed_right;
            let output = match (model, changed) {
                (Model::Max(..), true) => model_max(left, right),
                (Model::IMax(..), true) => model_imax(left, right),
                (Model::Max(..), false) => Model::Max(Box::new(left), Box::new(right)),
                _ => Model::IMax(Box::new(left), Box::new(right)),
            };
            (output, changed)
        }
        Model::Parameter(name) => parameters
            .iter()
            .position(|parameter| parameter == name)
            .and_then(|index| values.get(index))
            .cloned()
            .map(|value| (value, true))
            .unwrap_or_else(|| (Model::Parameter(name.clone()), false)),
        Model::Meta(name) => (Model::Meta(name.clone()), false),
    }
}

fn frozen_substitute(model: &Model, parameters: &[String], values: &[Model]) -> Model {
    frozen_substitute_changed(model, parameters, values).0
}

fn generated_models() -> Vec<Model> {
    let mut models = vec![
        Model::Zero,
        Model::Parameter("u".to_owned()),
        Model::Parameter("v".to_owned()),
        Model::Parameter("w".to_owned()),
        Model::Meta("m".to_owned()),
        Model::Meta("n".to_owned()),
    ];
    for round in 0..3 {
        let sample: Vec<_> = models.iter().take(8 + round * 32).cloned().collect();
        for (index, model) in sample.iter().enumerate() {
            let other = sample[(index * 7 + 3) % sample.len()].clone();
            models.push(Model::Succ(Box::new(model.clone())));
            models.push(Model::Max(Box::new(model.clone()), Box::new(other.clone())));
            models.push(Model::IMax(Box::new(other), Box::new(model.clone())));
        }
    }
    models
}

#[test]
fn changed_universe_nodes_use_pinned_smart_constructors() {
    // The pin rebuilds changed ancestors through update_max -> mk_max/mk_imax
    // (vendor/lean4-src/src/kernel/level.cpp:81-123, 290-324). These expectations
    // are literal results of those rules, not the generated model below.
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let w = Level::param(primary_name("w"));
    let max = |a, b| Level::max(a, b).expect("shallow maximum");
    let imax = |a, b| Level::imax(a, b).expect("shallow dependent maximum");
    let succ = |a: &Level| a.clone().succ().expect("shallow successor");
    let two = succ(&Level::one());
    let three = succ(&two);
    let cases = [
        (
            "explicit maximum",
            max(u.clone(), two),
            three.clone(),
            three,
        ),
        (
            "left zero",
            max(u.clone(), v.clone()),
            Level::zero(),
            v.clone(),
        ),
        (
            "right zero",
            max(v.clone(), u.clone()),
            Level::zero(),
            v.clone(),
        ),
        (
            "structurally equal operands",
            max(u.clone(), v.clone()),
            v.clone(),
            v.clone(),
        ),
        (
            "right maximum absorbs its left operand",
            max(u.clone(), max(v.clone(), w.clone())),
            v.clone(),
            max(v.clone(), w.clone()),
        ),
        (
            "left maximum absorbs its right operand",
            max(max(v.clone(), w.clone()), u.clone()),
            w.clone(),
            max(v.clone(), w.clone()),
        ),
        (
            "larger successor offset of the same base",
            max(succ(&u), succ(&succ(&v))),
            v.clone(),
            succ(&succ(&v)),
        ),
        (
            "imax right zero",
            imax(v.clone(), u.clone()),
            Level::zero(),
            Level::zero(),
        ),
        (
            "imax left zero",
            imax(u.clone(), v.clone()),
            Level::zero(),
            v.clone(),
        ),
        (
            "imax left one",
            imax(u.clone(), v.clone()),
            Level::one(),
            v.clone(),
        ),
        (
            "imax equal operands",
            imax(u.clone(), v.clone()),
            v.clone(),
            v.clone(),
        ),
        (
            "imax positive right operand",
            imax(v.clone(), u.clone()),
            succ(&w),
            max(v.clone(), succ(&w)),
        ),
        (
            "imax positivity traverses a raw replacement",
            imax(v.clone(), u.clone()),
            imax(w.clone(), Level::one()),
            max(v.clone(), imax(w.clone(), Level::one())),
        ),
        (
            "positive left operand does not establish right positivity",
            imax(u.clone(), v.clone()),
            succ(&w),
            imax(succ(&w), v.clone()),
        ),
        (
            "semantic equivalence does not replace structural equality",
            max(u.clone(), max(v.clone(), w.clone())),
            max(w.clone(), v.clone()),
            max(max(w.clone(), v.clone()), max(v, w)),
        ),
    ];
    for (label, subject, replacement, expected) in cases {
        let output = complete(instantiate_level_parameters(
            &decoded_level(&subject),
            &[checker_name("u")],
            &[decoded_level(&replacement)],
            TermBudget::unlimited(),
        ));
        let expected = decoded_level(&expected);
        assert_eq!(
            wire_model(&output, output.root()),
            wire_model(&expected, expected.root()),
            "pinned constructor rule: {label}"
        );
    }
}

#[test]
fn universe_instantiation_preserves_untouched_and_replacement_shapes() {
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let w = Level::param(primary_name("w"));
    let raw = Level::imax(v, Level::zero()).expect("shallow raw dependent maximum");
    let mixed = Level::max(u.clone(), raw.clone()).expect("shallow mixed subject");
    let expected_mixed = Level::max(w.clone(), raw.clone()).expect("shallow mixed result");
    for (subject, replacement, expected) in [
        (raw.clone(), w.clone(), raw.clone()),
        (u, raw.clone(), raw),
        (mixed, w, expected_mixed),
    ] {
        let output = complete(instantiate_level_parameters(
            &decoded_level(&subject),
            &[checker_name("u")],
            &[decoded_level(&replacement)],
            TermBudget::unlimited(),
        ));
        let expected = decoded_level(&expected);
        assert_eq!(
            wire_model(&output, output.root()),
            wire_model(&expected, expected.root()),
            "only ancestors of a substituted parameter are rebuilt"
        );
    }
}

#[test]
fn universe_rebuilding_preserves_budget_and_cancellation_nonanswers() {
    let subject = decoded_level(
        &Level::imax(
            Level::param(primary_name("v")),
            Level::param(primary_name("u")),
        )
        .expect("shallow subject"),
    );
    let pristine = subject.clone();
    let parameters = [checker_name("u")];
    let replacements = [decoded_level(&Level::zero())];
    for budget in [
        TermBudget::new(0, u64::MAX),
        TermBudget::new(u64::MAX, 0),
        TermBudget::unlimited().with_max_arena_nodes(1),
    ] {
        assert!(matches!(
            instantiate_level_parameters(&subject, &parameters, &replacements, budget),
            InstantiationOutcome::Inconclusive(TermStop::Resource { .. })
        ));
    }
    let mut polls = 0;
    assert!(matches!(
        instantiate_level_parameters_with(
            &subject,
            &parameters,
            &replacements,
            TermBudget::unlimited(),
            || {
                polls += 1;
                polls == 4
            },
        ),
        InstantiationOutcome::Inconclusive(TermStop::Cancelled { .. })
    ));
    assert_eq!(subject, pristine);
}

#[test]
fn delta_instantiation_exposes_prop_without_collapsing_unknown_universes() {
    use fln_checker::environment::{
        ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety, DefinitionBody,
        DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
    };
    use fln_checker::whnf::{WhnfBudget, WhnfContext, WhnfOutcome, whnf};

    // Exercise the actual delta consumer, which instantiates from roots in a
    // shared expression arena rather than from standalone replacement levels.
    let universe = Level::imax(
        Level::param(primary_name("u")),
        Level::param(primary_name("v")),
    )
    .expect("shallow universe");
    let entry = ConstantEntry::new(
        checker_name("PolySort"),
        ConstantDeclaration::definition(
            vec![checker_name("u"), checker_name("v")],
            decoded_expr(&Expr::sort(universe.clone().succ().expect("shallow type"))),
            ConstantSafety::Safe,
            DefinitionBody::new(
                decoded_expr(&Expr::sort(universe)),
                ReducibilityHint::Abbrev,
                DefinitionSafety::Safe,
                Vec::new(),
            ),
        ),
    );
    let environment = match ConstantEnvironment::build(vec![entry], EnvironmentBudget::unlimited())
    {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("polymorphic definition environment: {other:?}"),
    };
    let context = WhnfContext::new(Vec::new(), Vec::new(), environment);
    let left = Level::param(primary_name("w"))
        .succ()
        .expect("shallow left universe");
    for (right, expected) in [
        (Level::zero(), Model::Zero),
        (
            Level::param(primary_name("x")),
            Model::IMax(
                Box::new(Model::Succ(Box::new(Model::Parameter("w".to_owned())))),
                Box::new(Model::Parameter("x".to_owned())),
            ),
        ),
    ] {
        let input = decoded_expr(&Expr::const_(
            primary_name("PolySort"),
            vec![left.clone(), right],
        ));
        let result = match whnf(&input, &context, WhnfBudget::unlimited()) {
            WhnfOutcome::Complete(result) => result,
            other => panic!("polymorphic delta reduction: {other:?}"),
        };
        let Some(ExprNode::Sort { level }) = result.term.node(result.term.root()) else {
            panic!("polymorphic delta reduction must expose a sort");
        };
        assert_eq!(term_level_model(&result.term, *level), expected);
    }
}

#[test]
fn generated_instantiation_matches_the_frozen_model() {
    let models = generated_models();
    assert!(
        models.len() > 300,
        "the generated instantiation corpus must stay nontrivial"
    );
    let parameter_models = vec!["u".to_owned(), "v".to_owned()];
    let parameters = vec![checker_name("u"), checker_name("v")];
    let value_models = vec![
        Model::Succ(Box::new(Model::Parameter("v".to_owned()))),
        Model::IMax(
            Box::new(Model::Meta("replacement-meta".to_owned())),
            Box::new(Model::Succ(Box::new(Model::Zero))),
        ),
    ];
    let values: Vec<_> = value_models
        .iter()
        .map(|value| decoded_level(&primary(value)))
        .collect();

    for (index, model) in models.iter().enumerate() {
        let subject = decoded_level(&primary(model));
        let output = complete(instantiate_level_parameters(
            &subject,
            &parameters,
            &values,
            TermBudget::unlimited(),
        ));
        assert_eq!(
            wire_model(&output, output.root()),
            frozen_substitute(model, &parameter_models, &value_models),
            "generated substitution drift at case {index}: {model:?}"
        );
    }
}

#[test]
fn arity_and_duplicate_parameter_maps_are_refused_separately() {
    let subject = decoded_level(&Level::zero());
    let u = checker_name("u");
    let zero = decoded_level(&Level::zero());
    let one = decoded_level(&Level::one());

    assert_eq!(
        instantiate_level_parameters(
            &subject,
            std::slice::from_ref(&u),
            &[],
            TermBudget::unlimited(),
        ),
        InstantiationOutcome::Refused(InstantiationRefusal::ArityMismatch {
            parameters: 1,
            values: 0,
        })
    );
    assert_eq!(
        instantiate_level_parameters(
            &subject,
            &[u.clone(), u],
            &[zero, one],
            TermBudget::unlimited(),
        ),
        InstantiationOutcome::Refused(InstantiationRefusal::DuplicateParameter {
            first: 0,
            second: 1,
        })
    );
}

#[test]
fn simultaneous_substitution_does_not_cascade_into_replacements() {
    let u = checker_name("u");
    let v = checker_name("v");
    let values = [
        decoded_level(&Level::param(primary_name("v"))),
        decoded_level(&Level::zero()),
    ];

    let u_subject = decoded_level(&Level::param(primary_name("u")));
    let u_result = complete(instantiate_level_parameters(
        &u_subject,
        &[u.clone(), v.clone()],
        &values,
        TermBudget::unlimited(),
    ));
    assert_eq!(
        wire_model(&u_result, u_result.root()),
        Model::Parameter("v".to_owned()),
        "the v inside u's replacement must not be rewritten by the sibling map entry"
    );

    let v_subject = decoded_level(&Level::param(primary_name("v")));
    let v_result = complete(instantiate_level_parameters(
        &v_subject,
        &[u, v],
        &values,
        TermBudget::unlimited(),
    ));
    assert_eq!(wire_model(&v_result, v_result.root()), Model::Zero);

    let w_subject = decoded_level(&Level::param(primary_name("w")));
    let w_result = complete(instantiate_level_parameters(
        &w_subject,
        &[],
        &[],
        TermBudget::unlimited(),
    ));
    assert_eq!(
        wire_model(&w_result, w_result.root()),
        Model::Parameter("w".to_owned())
    );
}

#[test]
fn repeated_occurrences_share_one_copied_replacement_arena() {
    let u = Level::param(primary_name("u"));
    let expression = Expr::app(
        Expr::sort(u.clone()),
        Expr::const_(primary_name("C"), vec![u]),
    );
    let subject = decoded_expr(&expression);
    let replacement = decoded_level(
        &Level::max(Level::zero(), Level::param(primary_name("replacement")))
            .expect("shallow replacement"),
    );
    let output = complete(instantiate_term_parameters(
        &subject,
        &[checker_name("u")],
        std::slice::from_ref(&replacement),
        TermBudget::unlimited(),
    ));

    let sort_level = output.nodes().iter().find_map(|node| match node {
        ExprNode::Sort { level } => Some(*level),
        _ => None,
    });
    let constant_level = output.nodes().iter().find_map(|node| match node {
        ExprNode::Constant { levels, .. } => levels.first().copied(),
        _ => None,
    });
    assert_eq!(sort_level, constant_level);
    assert_eq!(
        output.levels().len(),
        replacement.nodes().len(),
        "the replacement arena must be copied once and shared by both occurrences"
    );
}

fn all_variants_expression() -> Expr {
    let name = primary_name("n");
    let type_ = Expr::sort(Level::param(primary_name("u")));
    let locals = Expr::app(
        Expr::app(
            Expr::bvar(0).expect("bound"),
            Expr::fvar(FVarId(primary_name("free"))),
        ),
        Expr::mvar(MVarId(primary_name("meta"))),
    );
    let constants = Expr::app(
        Expr::const_(
            name.clone(),
            vec![
                Level::param(primary_name("u")),
                Level::mvar(LMVarId(primary_name("v"))),
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
            primary_name("text"),
            DataValue::OfString("metadata".to_owned()),
        ),
        (name.clone(), DataValue::OfBool(true)),
        (primary_name("name"), DataValue::OfName(name.clone())),
        (primary_name("nat"), DataValue::OfNat(42)),
        (primary_name("int"), DataValue::OfInt(-7)),
        (primary_name("syntax"), DataValue::OfSyntax(SyntaxHandle(9))),
    ]);
    Expr::mdata(metadata, Expr::proj(name, 2, let_expr))
}

#[test]
fn sort_and_constant_levels_are_both_remapped() {
    let subject = decoded_expr(&all_variants_expression());
    let replacement_model = Model::Max(
        Box::new(Model::Succ(Box::new(Model::Zero))),
        Box::new(Model::Parameter("replacement".to_owned())),
    );
    let replacement = decoded_level(&primary(&replacement_model));
    let output = complete(instantiate_term_parameters(
        &subject,
        &[checker_name("u")],
        &[replacement],
        TermBudget::unlimited(),
    ));

    assert_eq!(subject.nodes().len(), output.nodes().len());
    for (index, (before, after)) in subject.nodes().iter().zip(output.nodes()).enumerate() {
        match (before, after) {
            (ExprNode::Sort { level: before }, ExprNode::Sort { level: after }) => {
                let expected = frozen_substitute(
                    &term_level_model(&subject, *before),
                    &["u".to_owned()],
                    std::slice::from_ref(&replacement_model),
                );
                assert_eq!(term_level_model(&output, *after), expected);
            }
            (
                ExprNode::Constant {
                    name: before_name,
                    levels: before_levels,
                },
                ExprNode::Constant {
                    name: after_name,
                    levels: after_levels,
                },
            ) => {
                assert_eq!(before_name, after_name);
                assert_eq!(before_levels.len(), after_levels.len());
                for (before, after) in before_levels.iter().zip(after_levels) {
                    let expected = frozen_substitute(
                        &term_level_model(&subject, *before),
                        &["u".to_owned()],
                        std::slice::from_ref(&replacement_model),
                    );
                    assert_eq!(term_level_model(&output, *after), expected);
                }
            }
            _ => assert_eq!(before, after, "payload drift at expression node {index}"),
        }
    }
}

#[test]
fn resource_and_cancellation_are_typed_nonanswers_with_exact_recovery() {
    let subject = decoded_level(&Level::param(primary_name("payload")));
    let pristine = subject.clone();

    assert!(matches!(
        instantiate_level_parameters(&subject, &[], &[], TermBudget::new(0, u64::MAX)),
        InstantiationOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::Steps,
            allowed: 0,
            observed: 1,
            completed_steps: 0,
            ..
        })
    ));
    assert!(matches!(
        instantiate_level_parameters(&subject, &[], &[], TermBudget::new(u64::MAX, 0)),
        InstantiationOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::OutputUnits,
            allowed: 0,
            completed_steps: 1,
            ..
        })
    ));
    assert!(matches!(
        instantiate_level_parameters(
            &decoded_level(&Level::one()),
            &[],
            &[],
            TermBudget::unlimited().with_max_arena_nodes(1),
        ),
        InstantiationOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::ArenaNodes,
            allowed: 1,
            observed: 2,
            ..
        })
    ));

    let mut polls = 0;
    assert!(matches!(
        instantiate_level_parameters_with(&subject, &[], &[], TermBudget::unlimited(), || {
            polls += 1;
            polls == 2
        },),
        InstantiationOutcome::Inconclusive(TermStop::Cancelled {
            polls: 2,
            completed_steps: 1,
            ..
        })
    ));
    assert_eq!(subject, pristine);

    let recovered = complete(instantiate_level_parameters(
        &subject,
        &[],
        &[],
        TermBudget::unlimited(),
    ));
    assert_eq!(recovered, subject);
}

#[test]
fn large_owned_payloads_are_charged_before_copy() {
    let payload = "payload".repeat(16 * 1024);
    let output_units = payload.len() as u64 + 2;
    let subject = decoded_level(&Level::param(Name::str(Name::anonymous(), payload)));

    assert!(matches!(
        instantiate_level_parameters(
            &subject,
            &[],
            &[],
            TermBudget::new(u64::MAX, output_units - 1),
        ),
        InstantiationOutcome::Inconclusive(TermStop::Resource {
            limit: TermLimit::OutputUnits,
            allowed,
            observed,
            completed_steps: 1,
            ..
        }) if allowed == output_units - 1 && observed == output_units
    ));
    let copied = complete(instantiate_level_parameters(
        &subject,
        &[],
        &[],
        TermBudget::new(u64::MAX, output_units),
    ));
    assert_eq!(copied, subject);
}

#[test]
fn output_arenas_preserve_backward_reference_invariants() {
    let subject = decoded_expr(&all_variants_expression());
    let replacement = decoded_level(
        &Level::imax(Level::param(primary_name("x")), Level::one()).expect("shallow replacement"),
    );
    let output = complete(instantiate_term_parameters(
        &subject,
        &[checker_name("u")],
        &[replacement],
        TermBudget::unlimited(),
    ));

    assert!(output.root().index() < output.nodes().len());
    for (parent, node) in output.nodes().iter().enumerate() {
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
        assert!(children.iter().all(|child| child.index() < parent));
    }
    for (parent, node) in output.levels().iter().enumerate() {
        let children = match node {
            LevelNode::Succ(child) => vec![*child],
            LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                vec![*left, *right]
            }
            LevelNode::Zero | LevelNode::Parameter(_) | LevelNode::Meta(_) => Vec::new(),
        };
        assert!(children.iter().all(|child| child.index() < parent));
    }
}

fn deep_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_LEVEL);
    for _ in 0..DEPTH {
        writer.u8(1);
    }
    writer.u8(0);
    let replacement = match decode_level(
        &writer.into_bytes(),
        DecodeBudget::new(u64::MAX, DEPTH as u64 + 1),
    ) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => return Err(format!("deep replacement did not decode: {other:?}")),
    };
    let subject = decoded_level(&Level::param(primary_name("u")));
    let output = match instantiate_level_parameters(
        &subject,
        &[checker_name("u")],
        &[replacement],
        TermBudget::unlimited(),
    ) {
        InstantiationOutcome::Complete(value) => value,
        other => return Err(format!("deep instantiation failed: {other:?}")),
    };
    if output.nodes().len() != DEPTH + 1 {
        return Err(format!(
            "deep output node count drifted: {}",
            output.nodes().len()
        ));
    }
    if output.root().index() != DEPTH {
        return Err(format!(
            "deep output root drifted: {}",
            output.root().index()
        ));
    }
    Ok(())
}

#[test]
fn deep_universe_instantiation_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_INSTANTIATE_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-instantiate-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_child)
            .expect("spawn bounded-stack child thread")
            .join()
            .expect("bounded-stack child thread did not panic");
        result.expect("bounded-stack instantiation");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "deep_universe_instantiation_fits_a_64k_stack",
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
fn instantiation_production_code_has_no_primary_semantic_path() {
    let source = include_str!("../src/instantiate.rs");
    for forbidden in [
        "fln_core::",
        "TypeChecker",
        "instantiate_lparams",
        "substitute_level",
    ] {
        assert!(
            !source.contains(forbidden),
            "checker instantiation source shares forbidden semantic path `{forbidden}`"
        );
    }
}
