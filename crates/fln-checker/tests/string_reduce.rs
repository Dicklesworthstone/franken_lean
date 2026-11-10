#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::defeq::{DefEqBudget, DefEqMismatch, DefEqOutcome, DefEqStop, def_eq};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety,
    ConstructorDeclaration, DefinitionBody, DefinitionSafety, EnvironmentBudget,
    EnvironmentOutcome, InductiveDeclaration, RecursorDeclaration, RecursorRule, ReducibilityHint,
};
use fln_checker::string_reduce::{
    StringExpansionBudget, StringExpansionLimit, StringExpansionOutcome, StringExpansionStop,
    expand_string_literal, expand_string_literal_with,
};
use fln_checker::whnf::{
    ProjectionRule, WhnfBudget, WhnfContext, WhnfOutcome, WhnfStop, whnf, whnf_with,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, ExprId, ExprNode, NamePart, WireExpr, WireName, decode_expr,
    decode_name,
};
use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::canon::Canonical;

fn top(name: &str) -> Name {
    Name::str(Name::anonymous(), name)
}

fn qualified(namespace: &str, leaf: &str) -> Name {
    Name::str(top(namespace), leaf)
}

fn decoded(expression: &Expr) -> WireExpr {
    match decode_expr(&expression.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("schema fixture did not decode: {other:?}"),
    }
}

fn checker_name(name: &Name) -> WireName {
    match decode_name(&name.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("schema name did not decode: {other:?}"),
    }
}

fn string_literal(value: &str) -> Expr {
    Expr::lit(Literal::Str(value.to_owned()))
}

fn nat_literal(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn char_list(codes: &[u64]) -> Expr {
    let char_constant = Expr::const_(top("Char"), Vec::new());
    let cons = Expr::app(
        Expr::const_(qualified("List", "cons"), vec![Level::zero()]),
        char_constant.clone(),
    );
    let mut spine = Expr::app(
        Expr::const_(qualified("List", "nil"), vec![Level::zero()]),
        char_constant,
    );
    let char_of_nat = Expr::const_(qualified("Char", "ofNat"), Vec::new());
    for code in codes.iter().rev() {
        let character = Expr::app(char_of_nat.clone(), nat_literal(*code));
        spine = Expr::app(Expr::app(cons.clone(), character), spine);
    }
    spine
}

fn of_list(codes: &[u64]) -> Expr {
    Expr::app(
        Expr::const_(qualified("String", "ofList"), Vec::new()),
        char_list(codes),
    )
}

fn exact_name(name: &WireName, expected: &[&str]) -> bool {
    name.parts().len() == expected.len()
        && name
            .parts()
            .iter()
            .zip(expected)
            .all(|(part, expected)| matches!(part, NamePart::Text(value) if value == expected))
}

fn app_spine(term: &WireExpr, mut root: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    loop {
        match term.node(root).expect("well-formed output arena") {
            ExprNode::Apply { function, argument } => {
                assert!(function.index() < root.index());
                assert!(argument.index() < root.index());
                arguments.push(*argument);
                root = *function;
            }
            _ => {
                arguments.reverse();
                return (root, arguments);
            }
        }
    }
}

fn expect_constant(term: &WireExpr, root: ExprId, name: &[&str], level_count: usize) {
    match term.node(root).expect("constant root exists") {
        ExprNode::Constant {
            name: actual,
            levels,
        } => {
            assert!(exact_name(actual, name), "unexpected name {actual:?}");
            assert_eq!(levels.len(), level_count);
        }
        other => panic!("expected constant {name:?}, got {other:?}"),
    }
}

fn list_codes(term: &WireExpr, mut root: ExprId) -> Vec<u64> {
    let mut codes = Vec::new();
    loop {
        let (head, arguments) = app_spine(term, root);
        let ExprNode::Constant { name, levels } = term.node(head).expect("list head exists") else {
            panic!("list spine has a nonconstant head");
        };
        assert_eq!(levels.len(), 1, "List constructors use universe zero");
        if exact_name(name, &["List", "nil"]) {
            assert_eq!(arguments.len(), 1);
            expect_constant(term, arguments[0], &["Char"], 0);
            return codes;
        }
        assert!(exact_name(name, &["List", "cons"]));
        assert_eq!(arguments.len(), 3);
        expect_constant(term, arguments[0], &["Char"], 0);
        let (char_head, char_arguments) = app_spine(term, arguments[1]);
        expect_constant(term, char_head, &["Char", "ofNat"], 0);
        assert_eq!(char_arguments.len(), 1);
        let code = match term
            .node(char_arguments[0])
            .expect("character code literal exists")
        {
            ExprNode::NatLiteral { limbs_le } => match limbs_le.as_slice() {
                [] => 0,
                [value] => *value,
                other => panic!("Unicode scalar escaped one limb: {other:?}"),
            },
            other => panic!("Char.ofNat argument is not a Nat literal: {other:?}"),
        };
        codes.push(code);
        root = arguments[2];
    }
}

fn expansion_codes(term: &WireExpr) -> Vec<u64> {
    let (head, arguments) = app_spine(term, term.root());
    expect_constant(term, head, &["String", "ofList"], 0);
    assert_eq!(arguments.len(), 1);
    list_codes(term, arguments[0])
}

fn string_context() -> WhnfContext {
    let value = Expr::lam(
        top("data"),
        Expr::sort(Level::zero()),
        Expr::app(
            Expr::const_(qualified("String", "mk"), Vec::new()),
            Expr::bvar(0).expect("one binder"),
        ),
        BinderInfo::Default,
    );
    let entry = ConstantEntry::new(
        checker_name(&qualified("String", "ofList")),
        ConstantDeclaration::definition(
            Vec::new(),
            decoded(&Expr::sort(Level::zero())),
            ConstantSafety::Safe,
            DefinitionBody::new(
                decoded(&value),
                ReducibilityHint::Regular(1),
                DefinitionSafety::Safe,
                Vec::new(),
            ),
        ),
    );
    let environment = match ConstantEnvironment::build(vec![entry], EnvironmentBudget::unlimited())
    {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("String constant environment did not build: {other:?}"),
    };
    WhnfContext::new(
        Vec::new(),
        vec![ProjectionRule::new(
            checker_name(&top("String")),
            checker_name(&qualified("String", "mk")),
            0,
        )],
        environment,
    )
}

/// A reduction fixture with a constructor field containing the character list.
/// As in `string_context`, this isolates KR-314 from the pin's UTF-8 encoder:
/// the owned literal expansion must pass through the environment's `ofList`
/// definition before the recursor can find its constructor rule.
fn string_recursor_context(include_of_list: bool, constructor: Name) -> WhnfContext {
    let string = Expr::const_(top("String"), Vec::new());
    let chars = Expr::app(
        Expr::const_(top("List"), vec![Level::zero()]),
        Expr::const_(top("Char"), Vec::new()),
    );
    let pi = |domain, body| Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default);
    let lam = |domain, body| Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default);
    let bound = |index| Expr::bvar(index).unwrap();
    let motive = pi(string.clone(), Expr::sort(Level::param(top("u"))));
    let minor = pi(
        chars.clone(),
        Expr::app(
            bound(1),
            Expr::app(Expr::const_(constructor.clone(), Vec::new()), bound(0)),
        ),
    );
    let type_ = pi(
        motive.clone(),
        pi(
            minor.clone(),
            pi(string.clone(), Expr::app(bound(2), bound(0))),
        ),
    );
    let rhs = lam(
        motive,
        lam(minor, lam(chars.clone(), Expr::app(bound(1), bound(0)))),
    );
    let recursor = ConstantEntry::new(
        checker_name(&qualified("String", "rec")),
        ConstantDeclaration::recursor(
            vec![checker_name(&top("u"))],
            decoded(&type_),
            ConstantSafety::Safe,
            RecursorDeclaration::new(
                vec![checker_name(&top("String"))],
                0,
                0,
                1,
                1,
                vec![RecursorRule::new(
                    checker_name(&constructor),
                    1,
                    decoded(&rhs),
                )],
                false,
            ),
        ),
    );
    let mut environment = if include_of_list {
        string_context().constants().clone()
    } else {
        ConstantEnvironment::empty()
    };
    // Include the whole structure shape: otherwise early structure eta would
    // be unavailable and could not mask missing literal expansion in this test.
    for entry in [
        ConstantEntry::new(
            checker_name(&top("String")),
            ConstantDeclaration::inductive(
                Vec::new(),
                decoded(&Expr::sort(Level::one())),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    0,
                    0,
                    vec![checker_name(&top("String"))],
                    vec![checker_name(&qualified("String", "mk"))],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            checker_name(&qualified("String", "mk")),
            ConstantDeclaration::constructor(
                Vec::new(),
                decoded(&pi(chars, string)),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name(&top("String")), 0, 0, 1),
            ),
        ),
        recursor,
    ] {
        environment = match environment.extend(entry, EnvironmentBudget::unlimited()) {
            EnvironmentOutcome::Complete { environment, .. } => environment,
            other => panic!("String recursor environment did not build: {other:?}"),
        };
    }
    WhnfContext::new(
        Vec::new(),
        vec![ProjectionRule::new(
            checker_name(&top("String")),
            checker_name(&qualified("String", "mk")),
            0,
        )],
        environment,
    )
}

fn string_recursor(major: Expr, minor: Expr) -> Expr {
    let motive = Expr::lam(
        Name::anonymous(),
        Expr::const_(top("String"), Vec::new()),
        Expr::app(
            Expr::const_(top("List"), vec![Level::zero()]),
            Expr::const_(top("Char"), Vec::new()),
        ),
        BinderInfo::Default,
    );
    [motive, minor, major].into_iter().fold(
        Expr::const_(qualified("String", "rec"), vec![Level::one()]),
        Expr::app,
    )
}

#[test]
fn string_recursor_expands_majors_and_preserves_the_minor_and_trailing_arguments() {
    let context = string_recursor_context(true, qualified("String", "mk"));
    for text in ["", "aλ🦀\0"] {
        // A neutral minor keeps its field unevaluated. The returned field must
        // nevertheless be the expansion's actual list, not a projection of
        // the original literal manufactured by structure eta.
        let minor = Expr::const_(top("observe"), Vec::new());
        for major in [
            string_literal(text),
            Expr::let_e(
                top("s"),
                Expr::const_(top("String"), Vec::new()),
                string_literal(text),
                Expr::bvar(0).unwrap(),
                false,
            ),
            Expr::app(
                Expr::lam(
                    top("s"),
                    Expr::const_(top("String"), Vec::new()),
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                string_literal(text),
            ),
        ] {
            let application = Expr::app(string_recursor(major, minor.clone()), nat_literal(7));
            let result = match whnf(&decoded(&application), &context, WhnfBudget::unlimited()) {
                WhnfOutcome::Complete(result) => result,
                other => panic!("String recursor did not normalize: {other:?}"),
            };
            let (head, arguments) = app_spine(&result.term, result.term.root());
            expect_constant(&result.term, head, &["observe"], 0);
            assert_eq!(arguments.len(), 2);
            let expected: Vec<_> = text.chars().map(|c| u64::from(u32::from(c))).collect();
            assert_eq!(list_codes(&result.term, arguments[0]), expected);
            assert!(
                matches!(result.term.node(arguments[1]), Some(ExprNode::NatLiteral { limbs_le }) if limbs_le.as_slice() == [7])
            );
            assert_eq!(result.string_progress.code_points, expected.len() as u64);
            assert_eq!(result.string_progress.generated_arenas, 1);
            assert!(result.delta_reductions >= 1);
        }
    }
}

#[test]
fn string_recursor_requires_the_expansion_to_reach_its_own_constructor() {
    let application = decoded(&string_recursor(
        string_literal("a"),
        Expr::const_(top("observe"), Vec::new()),
    ));
    for context in [
        string_recursor_context(false, qualified("String", "mk")),
        string_recursor_context(true, qualified("Other", "mk")),
    ] {
        let result = match whnf(&application, &context, WhnfBudget::unlimited()) {
            WhnfOutcome::Complete(result) => result,
            other => panic!("unsupported String recursor context must stay stuck: {other:?}"),
        };
        let (head, arguments) = app_spine(&result.term, result.term.root());
        expect_constant(&result.term, head, &["String", "rec"], 1);
        assert_eq!(arguments.len(), 3);
        assert!(
            matches!(result.term.node(arguments[2]), Some(ExprNode::StringLiteral(value)) if value == "a")
        );
        assert_eq!(result.reductions, 0, "failed major work is not progress");
        assert_eq!(result.string_progress.generated_arenas, 1);
    }
}

#[test]
fn string_recursor_still_uses_structure_eta_for_a_neutral_major() {
    let context = string_recursor_context(true, qualified("String", "mk"));
    let application = decoded(&string_recursor(
        Expr::const_(top("neutralString"), Vec::new()),
        Expr::const_(top("observe"), Vec::new()),
    ));
    let result = match whnf(&application, &context, WhnfBudget::unlimited()) {
        WhnfOutcome::Complete(result) => result,
        other => panic!("neutral String major did not eta-reduce: {other:?}"),
    };
    let (head, arguments) = app_spine(&result.term, result.term.root());
    expect_constant(&result.term, head, &["observe"], 0);
    assert_eq!(arguments.len(), 1);
    let ExprNode::Projection {
        structure_name,
        index,
        expression,
    } = result
        .term
        .node(arguments[0])
        .expect("field projection exists")
    else {
        panic!("neutral major must produce a projection");
    };
    assert!(exact_name(structure_name, &["String"]));
    assert_eq!(*index, 0);
    expect_constant(&result.term, *expression, &["neutralString"], 0);
    assert_eq!(result.string_progress.generated_arenas, 0);
}

#[test]
fn string_recursor_limits_and_cancellation_are_recoverable_nonanswers() {
    let context = string_recursor_context(true, qualified("String", "mk"));
    let application = decoded(&string_recursor(
        string_literal("aλ"),
        Expr::const_(top("observe"), Vec::new()),
    ));
    let budget = WhnfBudget::unlimited().with_string(StringExpansionBudget::new(
        u64::MAX,
        1,
        u64::MAX,
        u64::MAX,
    ));
    assert!(matches!(
        whnf(&application, &context, budget),
        WhnfOutcome::Inconclusive(WhnfStop::StringExpansion {
            stop: StringExpansionStop::Resource {
                limit: StringExpansionLimit::CodePoints,
                allowed: 1,
                observed: 2,
                ..
            },
            ..
        })
    ));
    assert!(matches!(
        whnf_with(&application, &context, WhnfBudget::unlimited(), || true),
        WhnfOutcome::Inconclusive(_)
    ));
    let result = match whnf(&application, &context, WhnfBudget::unlimited()) {
        WhnfOutcome::Complete(result) => result,
        other => panic!("String recursor did not recover: {other:?}"),
    };
    let (head, arguments) = app_spine(&result.term, result.term.root());
    expect_constant(&result.term, head, &["observe"], 0);
    assert_eq!(list_codes(&result.term, arguments[0]), [97, 955]);
}

#[test]
fn expansion_is_exact_unicode_scalar_shape_not_utf8_bytes() {
    let result = match expand_string_literal("aλ🦀\0", StringExpansionBudget::unlimited()) {
        StringExpansionOutcome::Expanded(result) => result,
        other => panic!("String literal did not expand: {other:?}"),
    };
    assert_eq!(expansion_codes(&result.term), [97, 955, 129_408, 0]);
    assert_eq!(result.progress.code_points, 4);
    assert_eq!(result.progress.steps, 29);
    assert_eq!(result.progress.generated_arenas, 1);
    assert_eq!(result.progress.arena_nodes, 25);
    assert_eq!(result.progress.owned_units, 79);

    let empty = match expand_string_literal("", StringExpansionBudget::unlimited()) {
        StringExpansionOutcome::Expanded(result) => result,
        other => panic!("empty String literal did not expand: {other:?}"),
    };
    assert!(expansion_codes(&empty.term).is_empty());
    assert_eq!(empty.progress.steps, 9);
    assert_eq!(empty.progress.arena_nodes, 9);
    assert_eq!(empty.progress.owned_units, 60);
}

#[test]
fn every_expansion_limit_has_an_exact_and_one_less_boundary() {
    let exact = StringExpansionBudget::new(29, 4, 25, 79);
    assert!(matches!(
        expand_string_literal("aλ🦀\0", exact),
        StringExpansionOutcome::Expanded(_)
    ));

    for (budget, expected_limit, allowed, observed) in [
        (
            StringExpansionBudget::new(28, 4, 25, 79),
            StringExpansionLimit::Steps,
            28,
            29,
        ),
        (
            StringExpansionBudget::new(29, 3, 25, 79),
            StringExpansionLimit::CodePoints,
            3,
            4,
        ),
        (
            StringExpansionBudget::new(29, 4, 24, 79),
            StringExpansionLimit::ArenaNodes,
            24,
            25,
        ),
        (
            StringExpansionBudget::new(29, 4, 25, 78),
            StringExpansionLimit::OwnedUnits,
            78,
            79,
        ),
    ] {
        assert!(matches!(
            expand_string_literal("aλ🦀\0", budget),
            StringExpansionOutcome::Inconclusive(StringExpansionStop::Resource {
                limit,
                allowed: actual_allowed,
                observed: actual_observed,
                ..
            }) if limit == expected_limit
                && actual_allowed == allowed
                && actual_observed == observed
        ));
    }
}

#[test]
fn cancellation_is_typed_and_a_clean_rerun_recovers_exactly() {
    let mut polls = 0_u64;
    let stopped = expand_string_literal_with("abcdef", StringExpansionBudget::unlimited(), || {
        polls += 1;
        polls == 7
    });
    assert!(matches!(
        stopped,
        StringExpansionOutcome::Inconclusive(StringExpansionStop::Cancelled { polls: 7, .. })
    ));
    let recovered = match expand_string_literal("abcdef", StringExpansionBudget::unlimited()) {
        StringExpansionOutcome::Expanded(result) => result,
        other => panic!("recovery did not complete: {other:?}"),
    };
    assert_eq!(
        expansion_codes(&recovered.term),
        [97, 98, 99, 100, 101, 102]
    );
}

#[test]
fn conversion_gate_is_exact_symmetric_and_decisive_once_matched() {
    let literal = decoded(&string_literal("aλ"));
    let exact = decoded(&of_list(&[97, 955]));
    for (left, right) in [(&literal, &exact), (&exact, &literal)] {
        assert!(matches!(
            def_eq(
                left,
                right,
                &WhnfContext::default(),
                DefEqBudget::unlimited(),
            ),
            DefEqOutcome::Equal(_)
        ));
    }

    let wrong_value = decoded(&of_list(&[97, 956]));
    assert!(matches!(
        def_eq(
            &literal,
            &wrong_value,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::NotEqual { .. }
    ));
    let reversed = decoded(&of_list(&[955, 97]));
    assert!(matches!(
        def_eq(
            &literal,
            &reversed,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::NotEqual { .. }
    ));

    let unknown_argument = decoded(&Expr::app(
        Expr::const_(qualified("String", "ofList"), Vec::new()),
        Expr::const_(top("unknown"), Vec::new()),
    ));
    assert!(matches!(
        def_eq(
            &literal,
            &unknown_argument,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::NotEqual {
            mismatch: DefEqMismatch::StringExpansion { .. },
            ..
        }
    ));
}

#[test]
fn wrong_head_levels_and_arity_do_not_enter_the_string_rule() {
    let literal = decoded(&string_literal("a"));
    let argument = char_list(&[97]);
    let cases = [
        Expr::app(
            Expr::const_(qualified("Other", "ofList"), Vec::new()),
            argument.clone(),
        ),
        Expr::app(
            Expr::const_(qualified("String", "ofList"), vec![Level::zero()]),
            argument.clone(),
        ),
        Expr::app(
            Expr::app(
                Expr::const_(qualified("String", "ofList"), Vec::new()),
                argument,
            ),
            Expr::const_(top("extra"), Vec::new()),
        ),
    ];
    for case in cases {
        let outcome = def_eq(
            &literal,
            &decoded(&case),
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        );
        assert!(
            matches!(outcome, DefEqOutcome::Deferred { .. }),
            "inexact String gate answered instead of deferring: {outcome:?}"
        );
    }
}

#[test]
fn projection_expands_then_forces_the_oflist_definition_to_constructor_whnf() {
    let context = string_context();
    let projection = decoded(&Expr::proj(top("String"), 0, string_literal("aλ")));
    let result = match whnf(&projection, &context, WhnfBudget::unlimited()) {
        WhnfOutcome::Complete(result) => result,
        other => panic!("String projection did not normalize: {other:?}"),
    };
    assert_eq!(list_codes(&result.term, result.term.root()), [97, 955]);
    assert_eq!(result.string_progress.code_points, 2);
    assert_eq!(result.string_progress.generated_arenas, 1);
    assert!(result.delta_reductions >= 1);

    assert!(matches!(
        def_eq(
            &projection,
            &decoded(&char_list(&[97, 955])),
            &context,
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Equal(_)
    ));
}

#[test]
fn projection_string_budget_stops_are_typed_and_recoverable() {
    let context = string_context();
    let projection = decoded(&Expr::proj(top("String"), 0, string_literal("a")));
    let budget = WhnfBudget::unlimited().with_string(StringExpansionBudget::new(
        13,
        u64::MAX,
        u64::MAX,
        u64::MAX,
    ));
    assert!(matches!(
        whnf(&projection, &context, budget),
        WhnfOutcome::Inconclusive(WhnfStop::StringExpansion {
            stop: StringExpansionStop::Resource {
                limit: StringExpansionLimit::Steps,
                allowed: 13,
                observed: 14,
                ..
            },
            ..
        })
    ));
    let result = match whnf(&projection, &context, WhnfBudget::unlimited()) {
        WhnfOutcome::Complete(result) => result,
        other => panic!("projection recovery failed: {other:?}"),
    };
    assert_eq!(list_codes(&result.term, result.term.root()), [97]);

    let defeq_budget = DefEqBudget::unlimited().with_string(StringExpansionBudget::new(
        13,
        u64::MAX,
        u64::MAX,
        u64::MAX,
    ));
    assert!(matches!(
        def_eq(
            &decoded(&string_literal("a")),
            &decoded(&of_list(&[97])),
            &WhnfContext::default(),
            defeq_budget,
        ),
        DefEqOutcome::Inconclusive(DefEqStop::StringExpansion {
            stop: StringExpansionStop::Resource {
                limit: StringExpansionLimit::Steps,
                allowed: 13,
                observed: 14,
                ..
            },
            ..
        })
    ));
}

#[test]
fn absent_or_wrong_projection_context_stays_nondecisive() {
    let projection = decoded(&Expr::proj(top("String"), 0, string_literal("a")));
    let absent = match whnf(
        &projection,
        &WhnfContext::default(),
        WhnfBudget::unlimited(),
    ) {
        WhnfOutcome::Complete(result) => result,
        other => panic!("missing String context was not a typed stuck result: {other:?}"),
    };
    assert!(matches!(
        absent.term.node(absent.term.root()),
        Some(ExprNode::Projection { .. })
    ));
    assert_eq!(absent.string_progress.generated_arenas, 1);

    let wrong_structure = decoded(&Expr::proj(top("NotString"), 0, string_literal("a")));
    let wrong = match whnf(&wrong_structure, &string_context(), WhnfBudget::unlimited()) {
        WhnfOutcome::Complete(result) => result,
        other => panic!("wrong structure was not left stuck: {other:?}"),
    };
    assert!(matches!(
        wrong.term.node(wrong.term.root()),
        Some(ExprNode::Projection { .. })
    ));
    assert_eq!(wrong.string_progress.generated_arenas, 0);
}

#[test]
fn fifty_thousand_code_points_fit_a_64k_stack() {
    const CODE_POINTS: usize = 50_000;
    let child = std::thread::Builder::new()
        .name("checker-string-expansion-stack".to_owned())
        .stack_size(64 * 1024)
        .spawn(|| {
            let input = "a".repeat(CODE_POINTS);
            let result = expand_string_literal(&input, StringExpansionBudget::unlimited());
            match result {
                StringExpansionOutcome::Expanded(result) => {
                    if result.progress.code_points != CODE_POINTS as u64 {
                        return Err(format!(
                            "expanded {} code points",
                            result.progress.code_points
                        ));
                    }
                    if result.progress.arena_nodes != 200_009 {
                        return Err(format!(
                            "materialized {} arena nodes",
                            result.progress.arena_nodes
                        ));
                    }
                    Ok(())
                }
                other => Err(format!("deep expansion did not complete: {other:?}")),
            }
        })
        .expect("spawn bounded-stack String expansion child");
    match child.join() {
        Ok(Ok(())) => {}
        Ok(Err(error)) => panic!("{error}"),
        Err(_) => panic!("bounded-stack String expansion child panicked"),
    }
}

#[test]
fn production_expansion_has_no_primary_semantic_path() {
    // Resolve the invoking tree at run time. A shared target directory may
    // otherwise reuse a test binary whose compile-time path names another
    // checkout and silently inspect the wrong production source (k60n).
    let root = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(std::path::PathBuf::from)
        .expect("cargo identifies the invoking checker crate");
    let source = std::fs::read_to_string(root.join("src/string_reduce.rs"))
        .expect("read production String reducer");
    for forbidden in [
        "fln_kernel",
        "fln_bignum",
        "fln_core::expr",
        "string_lit_to_constructor(",
    ] {
        assert!(
            !source.contains(forbidden),
            "production String reducer reached forbidden semantic path {forbidden}"
        );
    }

    let output = Command::new("cargo")
        .args(["tree", "-p", "fln-checker", "--prefix", "none"])
        .output()
        .expect("query checker dependency tree");
    assert!(output.status.success());
    let tree = String::from_utf8(output.stdout).expect("dependency tree is UTF-8");
    assert!(!tree.lines().any(|line| line.trim() == "fln-kernel"));
    assert!(!tree.lines().any(|line| line.trim() == "fln-bignum"));
}

#[test]
fn a_remembered_projection_is_replayed_only_within_its_string_budget() {
    let projection = decoded(&Expr::proj(top("String"), 0, string_literal("aλ")));
    let context = string_context();
    let full = match whnf(&projection, &context, WhnfBudget::unlimited()) {
        WhnfOutcome::Complete(result) => result,
        other => panic!("String projection did not normalize: {other:?}"),
    };
    let used = full.string_progress;
    let unlimited = [u64::MAX; 4];
    for (dimension, spent) in [
        used.steps,
        used.code_points,
        used.arena_nodes,
        used.owned_units,
    ]
    .into_iter()
    .enumerate()
    {
        for (allowed, completes) in [(spent, true), (spent - 1, false)] {
            let mut limits = unlimited;
            limits[dimension] = allowed;
            let budget = WhnfBudget::unlimited().with_string(StringExpansionBudget::new(
                limits[0], limits[1], limits[2], limits[3],
            ));
            // The context that remembers the result answers exactly as a fresh
            // context that must expand the literal again.
            let remembered = whnf(&projection, &context, budget);
            let recomputed = whnf(&projection, &string_context(), budget);
            assert_eq!(remembered, recomputed, "dimension {dimension}, {allowed}");
            assert_eq!(
                matches!(recomputed, WhnfOutcome::Complete(_)),
                completes,
                "dimension {dimension}, {allowed}: {recomputed:?}"
            );
        }
    }
}
