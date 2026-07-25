//! Frozen structural comparison against the pinned Reference parser (bead
//! `franken_lean-c24a`; plan §9 and §18).
//!
//! This suite closes one specific hole in Vellum's evidence composition. The existing
//! precedence model compares grouped expressions indirectly through values printed by the
//! Reference, while the lexer goldens and metamorphic suites compare Vellum with itself. The
//! Reference can expose its actual `Syntax` tree without an instrumented build:
//!
//! ```lean
//! import Lean.Elab.Command
//! open Lean in
//! run_cmd do
//!   let stx ← `(term| 1 + 2 * 3)
//!   Lean.logInfo (toString stx)
//! ```
//!
//! With the toolchain pinned by `SUITE.lock`, that prints:
//!
//! ```text
//! («term_+_» (num "1") "+" («term_*_» (num "2") "*" (num "3")))
//! ```
//!
//! ## Frozen fixture, not a runtime oracle
//!
//! [`CASES`] records output captured from `leanprover/lean4:v4.32.0` at commit
//! `8c9756b28d64dab099da31a4c09229a9e6a2ef35`. Normal tests never locate or execute the
//! Reference. There is deliberately no update mode: changing a row requires rerunning the
//! snippet above, reviewing the structural difference, and editing the row by hand.
//!
//! ## Exact comparison boundary
//!
//! The comparison is exact over node-kind sequence, child order, atom spelling, and grouping.
//! The tree on our side is produced by the actual [`fln_parse::pratt::pratt_parser`] over real
//! `fln-syntax` lexer tokens and attached leaves. This slice deliberately excludes SourceInfo
//! spans/trivia, hygiene scopes, preresolved identifiers, and recovered nodes. Reference syntax
//! quotations containing identifiers carry volatile `_stdin.<digest>._hygCtx._hyg.<ordinal>`
//! identities; those constructs need a narrow, separately tested normalizer rather than a broad
//! string scrubber. Keeping them out is an explicit evidence boundary, not an implied pass.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::build::Leaves;
use fln_parse::pratt::{Grammar, Lookup, pratt_parser, result_of};
use fln_parse::state::{MAX_PREC, ParseError, ParserState, Prec, Production};
use fln_syntax::literal::LiteralKind;
use fln_syntax::run::{Event, lex_run};
use fln_syntax::source::{BytePos, SourceText};
use fln_syntax::token::{LexedToken, TokenKind, TokenTable};
use fln_syntax::tree::Syntax;
use std::collections::BTreeSet;
use std::sync::{Arc, Weak};

const REFERENCE_TAG: &str = "v4.32.0";
const REFERENCE_COMMIT: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";
const SUITE_LOCK: &str = include_str!("../../../SUITE.lock");

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Associativity {
    Left,
    Right,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Operator {
    symbol: &'static str,
    precedence: Prec,
    associativity: Associativity,
}

const OPERATORS: &[Operator] = &[
    Operator {
        symbol: "^",
        precedence: 80,
        associativity: Associativity::Right,
    },
    Operator {
        symbol: "*",
        precedence: 70,
        associativity: Associativity::Left,
    },
    Operator {
        symbol: "+",
        precedence: 65,
        associativity: Associativity::Left,
    },
    Operator {
        symbol: "-",
        precedence: 65,
        associativity: Associativity::Left,
    },
];

/// A planted, uniformly wrong table: `+` binds more tightly than `*`.
///
/// A self-differential built from this table would remain perfectly green. The frozen Reference
/// tree must kill it.
const REVERSED_PRECEDENCE_MUTANT: &[Operator] = &[
    Operator {
        symbol: "^",
        precedence: 80,
        associativity: Associativity::Right,
    },
    Operator {
        symbol: "+",
        precedence: 75,
        associativity: Associativity::Left,
    },
    Operator {
        symbol: "*",
        precedence: 70,
        associativity: Associativity::Left,
    },
    Operator {
        symbol: "-",
        precedence: 65,
        associativity: Associativity::Left,
    },
];

#[derive(Debug, Clone, Copy)]
struct ReferenceCase {
    label: &'static str,
    source: &'static str,
    reference_tree: &'static str,
}

/// Exact `toString Syntax` rows captured from the pinned Reference.
///
/// The rows avoid identifier-bearing quotations in this first slice because their hygiene
/// identities are intentionally not stable across generator files. Numeric, scientific, char,
/// string, and raw-string literal nodes contain no such ambient identity and can be frozen
/// exactly.
const CASES: &[ReferenceCase] = &[
    ReferenceCase {
        label: "add_mul",
        source: "1 + 2 * 3",
        reference_tree: "(«term_+_» (num \"1\") \"+\" («term_*_» (num \"2\") \"*\" (num \"3\")))",
    },
    ReferenceCase {
        label: "mul_add",
        source: "1 * 2 + 3",
        reference_tree: "(«term_+_» («term_*_» (num \"1\") \"*\" (num \"2\")) \"+\" (num \"3\"))",
    },
    ReferenceCase {
        label: "right_pow",
        source: "2 ^ 3 ^ 4",
        reference_tree: "(«term_^_» (num \"2\") \"^\" («term_^_» (num \"3\") \"^\" (num \"4\")))",
    },
    ReferenceCase {
        label: "left_sub",
        source: "10 - 3 - 4",
        reference_tree: "(«term_-_» («term_-_» (num \"10\") \"-\" (num \"3\")) \"-\" (num \"4\"))",
    },
    ReferenceCase {
        label: "plus_then_minus",
        source: "10 + 3 - 4",
        reference_tree: "(«term_-_» («term_+_» (num \"10\") \"+\" (num \"3\")) \"-\" (num \"4\"))",
    },
    ReferenceCase {
        label: "minus_then_plus",
        source: "10 - 3 + 4",
        reference_tree: "(«term_+_» («term_-_» (num \"10\") \"-\" (num \"3\")) \"+\" (num \"4\"))",
    },
    ReferenceCase {
        label: "deep_mix",
        source: "1 + 2 * 3 ^ 4",
        reference_tree: "(«term_+_» (num \"1\") \"+\" («term_*_» (num \"2\") \"*\" («term_^_» (num \"3\") \"^\" (num \"4\"))))",
    },
    ReferenceCase {
        label: "hex_nat",
        source: "0x1F",
        reference_tree: "(num \"0x1F\")",
    },
    ReferenceCase {
        label: "binary_nat",
        source: "0b1010",
        reference_tree: "(num \"0b1010\")",
    },
    ReferenceCase {
        label: "separated_nat",
        source: "1_000",
        reference_tree: "(num \"1_000\")",
    },
    ReferenceCase {
        label: "scientific",
        source: "1.5e-3",
        reference_tree: "(scientific \"1.5e-3\")",
    },
    ReferenceCase {
        label: "char",
        source: "'x'",
        reference_tree: "(char \"'x'\")",
    },
    ReferenceCase {
        label: "raw_string",
        source: "r#\"raw\"#",
        reference_tree: "(str \"r#\\\"raw\\\"#\")",
    },
    ReferenceCase {
        label: "string",
        source: "\"a\\nb\"",
        reference_tree: "(str \"\\\"a\\\\nb\\\"\")",
    },
];

struct IndexedProduction {
    token_index: usize,
    production: Production,
}

/// The smallest concrete grammar that can drive the real Pratt engine over this frozen corpus.
///
/// It is test apparatus, not a second parser: tokenization, attachment, candidate scoring,
/// precedence checks, trailing-loop refusal, and tree construction all use the production
/// implementation. The apparatus supplies only the category's registered productions, which is
/// precisely what Vellum's dynamic grammar layer supplies in the product.
struct FixtureGrammar {
    source: SourceText,
    tokens: Vec<LexedToken>,
    leading: Vec<IndexedProduction>,
    trailing: Vec<IndexedProduction>,
}

impl FixtureGrammar {
    fn build(source: &str, operators: &'static [Operator]) -> Result<Arc<FixtureGrammar>, String> {
        let text = SourceText::from_utf8(source.as_bytes())
            .map_err(|error| format!("source was not valid UTF-8: {error:?}"))?;
        let table = TokenTable::from_tokens(operators.iter().map(|operator| operator.symbol));
        let run = lex_run(&text, &table);
        if !run.accepted() {
            return Err(format!("lexer refused {source:?}: {:?}", run.diagnostics()));
        }
        let tokens: Vec<LexedToken> = run
            .events
            .iter()
            .filter_map(|event| match event {
                Event::Token(token) => Some(token.clone()),
                Event::Trivia(_) => None,
                Event::Refused { .. } => None,
            })
            .collect();
        let leaves = Leaves::build(&text, &tokens)
            .map_err(|error| format!("token attachment refused {source:?}: {error:?}"))?;

        Ok(Arc::new_cyclic(move |grammar| {
            let mut leading = Vec::new();
            let mut trailing = Vec::new();

            for (token_index, token) in tokens.iter().enumerate() {
                let leaf = leaves.leaf(token_index).unwrap_or_else(|_| Syntax::Missing);
                if let TokenKind::Literal(literal_kind) = token.kind {
                    leading.push(IndexedProduction {
                        token_index,
                        production: literal_production(
                            literal_kind,
                            leaf.clone(),
                            token.extent.end(),
                        ),
                    });
                }

                if let TokenKind::Symbol(symbol) = &token.kind
                    && let Some(operator) = operators
                        .iter()
                        .copied()
                        .find(|operator| operator.symbol == symbol)
                {
                    trailing.push(IndexedProduction {
                        token_index,
                        production: operator_production(
                            grammar.clone(),
                            operator,
                            leaf,
                            token.extent.end(),
                        ),
                    });
                }
            }

            FixtureGrammar {
                source: text,
                tokens,
                leading,
                trailing,
            }
        }))
    }

    fn next_token_index(&self, from: BytePos) -> Option<usize> {
        self.tokens
            .iter()
            .position(|token| token.extent.start().0 >= from.0)
    }

    fn production_at<'a>(
        &'a self,
        indexed: &'a [IndexedProduction],
        state: &ParserState,
    ) -> Lookup<'a> {
        let Some(token_index) = self.next_token_index(state.pos()) else {
            return Lookup::TokenError(ParseError::new("unexpected end of input", state.pos()));
        };
        let productions = indexed
            .iter()
            .filter(|entry| entry.token_index == token_index)
            .map(|entry| &entry.production)
            .collect();
        Lookup::Productions(productions)
    }
}

impl Grammar for FixtureGrammar {
    fn kind(&self) -> Name {
        name("term")
    }

    fn leading_at(&self, state: &ParserState) -> Lookup<'_> {
        self.production_at(&self.leading, state)
    }

    fn trailing_at(&self, state: &ParserState) -> Lookup<'_> {
        self.production_at(&self.trailing, state)
    }

    fn consume_token(&self, state: &mut ParserState) -> Result<String, ParseError> {
        let Some(token_index) = self.next_token_index(state.pos()) else {
            return Err(ParseError::new("unexpected end of input", state.pos()));
        };
        let token = &self.tokens[token_index];
        state.set_pos(token.extent.end());
        Ok(self
            .source
            .as_str()
            .get(token.extent.start().0..token.extent.end().0)
            .unwrap_or_default()
            .to_string())
    }
}

fn literal_production(kind: LiteralKind, leaf: Syntax, end: BytePos) -> Production {
    let node_kind = match kind {
        LiteralKind::Nat => "num",
        LiteralKind::Scientific => "scientific",
        LiteralKind::Str => "str",
        LiteralKind::Char => "char",
        LiteralKind::Name => "name",
    };
    Production::new(name(node_kind), 0, move |state| {
        state.set_pos(end);
        state.set_lhs_prec(MAX_PREC);
        state.push(Syntax::node(name(node_kind), vec![leaf.clone()]));
    })
}

fn operator_production(
    grammar: Weak<FixtureGrammar>,
    operator: Operator,
    operator_leaf: Syntax,
    operator_end: BytePos,
) -> Production {
    let (left_requirement, right_requirement) = match operator.associativity {
        Associativity::Left => (operator.precedence, operator.precedence + 1),
        Associativity::Right => (operator.precedence + 1, operator.precedence),
    };
    let kind = name(&format!("term_{}_", operator.symbol));
    let production_kind = kind.clone();

    Production::new(production_kind, 0, move |state| {
        if !state.check_lhs_prec(left_requirement) || !state.check_prec(operator.precedence) {
            return;
        }
        let Some(left) = state.pop() else {
            state.set_error(ParseError::new(
                "operator production has no left operand",
                state.pos(),
            ));
            return;
        };

        state.set_pos(operator_end);
        let outer_precedence = state.prec();
        state.set_prec(right_requirement);
        let Some(grammar) = grammar.upgrade() else {
            state.set_error(ParseError::new(
                "fixture grammar expired during a parse",
                state.pos(),
            ));
            return;
        };
        pratt_parser(grammar.as_ref(), state);
        state.set_prec(outer_precedence);
        if state.has_error() {
            return;
        }

        let Some(right) = state.pop() else {
            state.set_error(ParseError::new(
                "operator production has no right operand",
                state.pos(),
            ));
            return;
        };
        state.push(Syntax::node(
            kind.clone(),
            vec![left, operator_leaf.clone(), right],
        ));
        state.set_lhs_prec(operator.precedence);
    })
}

fn name(component: &str) -> Name {
    Name::str(Name::anonymous(), component)
}

fn parse(source: &str, operators: &'static [Operator]) -> Result<Syntax, String> {
    let grammar = FixtureGrammar::build(source, operators)?;
    let mut state = ParserState::new(0);
    pratt_parser(grammar.as_ref(), &mut state);
    if let Some(error) = state.error() {
        return Err(format!(
            "parser refused {source:?} at byte {}: {}",
            error.at.0, error.message
        ));
    }
    if let Some(token_index) = grammar.next_token_index(state.pos()) {
        let token = &grammar.tokens[token_index];
        return Err(format!(
            "parser left token {:?} at byte {} in {source:?}",
            token.kind,
            token.extent.start().0
        ));
    }
    result_of(&state)
        .cloned()
        .ok_or_else(|| format!("parser produced no tree for {source:?}"))
}

/// Render the comparison subset in the Reference's `Syntax.toString` vocabulary.
///
/// This is intentionally total only over the declared subset. Encountering an identifier,
/// missing/recovered node, or an unexpected kind is a typed test failure; it is never erased by a
/// wildcard normalizer.
fn render_reference_shape(syntax: &Syntax) -> Result<String, String> {
    match syntax {
        Syntax::Missing => Err("comparison subset does not admit Syntax::Missing".to_string()),
        Syntax::Ident { .. } => {
            Err("comparison subset does not normalize identifier hygiene".to_string())
        }
        Syntax::Atom { val, .. } => Ok(format!("{val:?}")),
        Syntax::Node { kind, args, .. } => {
            let display = kind.to_display_string();
            let rendered_kind = if display.starts_with("term_") {
                format!("«{display}»")
            } else if matches!(
                display.as_str(),
                "num" | "scientific" | "str" | "char" | "name"
            ) {
                display
            } else {
                return Err(format!(
                    "comparison subset has no rule for node kind {display:?}"
                ));
            };
            let rendered_args = args
                .iter()
                .map(render_reference_shape)
                .collect::<Result<Vec<_>, _>>()?;
            if rendered_args.is_empty() {
                Ok(format!("({rendered_kind})"))
            } else {
                Ok(format!("({rendered_kind} {})", rendered_args.join(" ")))
            }
        }
    }
}

#[test]
fn actual_pratt_trees_match_every_frozen_reference_tree() {
    assert_eq!(
        CASES.len(),
        14,
        "the first frozen slice has an explicit anti-shrink floor"
    );
    for case in CASES {
        let syntax =
            parse(case.source, OPERATORS).unwrap_or_else(|error| panic!("{}: {error}", case.label));
        let actual = render_reference_shape(&syntax)
            .unwrap_or_else(|error| panic!("{}: {error}", case.label));
        assert_eq!(
            actual, case.reference_tree,
            "{}: Vellum's node kinds or grouping diverged from the pinned Reference for {:?}",
            case.label, case.source
        );
    }
}

#[test]
fn frozen_rows_are_unique_and_bound_to_the_suite_pin() {
    let expected_pin =
        "reference leanprover/lean4 tag=v4.32.0 commit=8c9756b28d64dab099da31a4c09229a9e6a2ef35";
    assert!(
        SUITE_LOCK.contains(expected_pin),
        "the frozen parse trees belong to {REFERENCE_TAG} at {REFERENCE_COMMIT}; a pin move \
         requires a reviewed fixture ceremony"
    );

    let mut labels = BTreeSet::new();
    let mut sources = BTreeSet::new();
    let mut shapes = BTreeSet::new();
    for case in CASES {
        assert!(
            labels.insert(case.label),
            "duplicate label {:?}",
            case.label
        );
        assert!(
            sources.insert(case.source),
            "duplicate source {:?}",
            case.source
        );
        assert!(
            shapes.insert(case.reference_tree),
            "duplicate Reference tree {:?}",
            case.reference_tree
        );
        assert!(
            case.reference_tree.starts_with('(') && case.reference_tree.ends_with(')'),
            "{}: fixture must be a structural Syntax rendering",
            case.label
        );
    }
}

#[test]
fn reversed_precedence_mutant_is_killed_by_the_reference_tree() {
    let case = CASES
        .iter()
        .find(|case| case.label == "add_mul")
        .expect("the discriminating add/mul row exists");
    let mutant = parse(case.source, REVERSED_PRECEDENCE_MUTANT)
        .and_then(|syntax| render_reference_shape(&syntax))
        .expect("the planted mutant still parses");
    assert_eq!(
        mutant, "(«term_*_» («term_+_» (num \"1\") \"+\" (num \"2\")) \"*\" (num \"3\"))",
        "the planted table must produce the intended wrong grouping"
    );
    assert_ne!(
        mutant, case.reference_tree,
        "the frozen Reference tree must kill a uniform precedence error"
    );
}
