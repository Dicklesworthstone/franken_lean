#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::defeq::{DefEqBudget, DefEqMismatch, DefEqOutcome, DefEqStop, def_eq};
use fln_checker::environment::{
    Definition, DefinitionEntry, DefinitionEnvironment, DefinitionSafety, EnvironmentBudget,
    EnvironmentOutcome, ReducibilityHint,
};
use fln_checker::string_reduce::{
    StringExpansionBudget, StringExpansionLimit, StringExpansionOutcome, StringExpansionStop,
    expand_string_literal, expand_string_literal_with,
};
use fln_checker::whnf::{ProjectionRule, WhnfBudget, WhnfContext, WhnfOutcome, WhnfStop, whnf};
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
    let entry = DefinitionEntry::new(
        checker_name(&qualified("String", "ofList")),
        Definition::new(
            Vec::new(),
            decoded(&Expr::sort(Level::zero())),
            decoded(&value),
            ReducibilityHint::Regular(1),
            DefinitionSafety::Safe,
            Vec::new(),
        ),
    );
    let environment =
        match DefinitionEnvironment::build(vec![entry], EnvironmentBudget::unlimited()) {
            EnvironmentOutcome::Complete { environment, .. } => environment,
            other => panic!("String definition environment did not build: {other:?}"),
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
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
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
