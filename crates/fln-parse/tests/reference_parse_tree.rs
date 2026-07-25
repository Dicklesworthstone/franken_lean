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
//! spans, preresolved identifiers, and recovered nodes. Reference quotations attach the volatile
//! authority `_@._stdin.<decimal>._hygCtx._hyg.<decimal>` to identifiers. The comparator replaces
//! only that exact suffix; a lookalike authority is a typed fixture error, not text silently
//! scrubbed until the trees agree.
//!
//! The term rows drive the real Pratt engine. The one command row is deliberately separate:
//! Vellum's category-independent lexer/attachment layer supplies its leaves, while a small
//! command-slice adapter constructs exactly the nodes the registered command productions must
//! mint. This is evidence for that named slice, not a claim that the full command grammar exists.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::build::Leaves;
use fln_parse::pratt::{Grammar, Lookup, leading_parser, pratt_parser, result_of};
use fln_parse::state::{MAX_PREC, ParseError, ParserState, Prec, Production, null_kind};
use fln_syntax::literal::LiteralKind;
use fln_syntax::run::{Event, lex_run};
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo, SourceText};
use fln_syntax::token::{LexedToken, TokenKind, TokenTable};
use fln_syntax::tree::Syntax;
use std::collections::BTreeSet;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Weak};

const REFERENCE_TAG: &str = "v4.32.0";
const REFERENCE_COMMIT: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";
const SUITE_LOCK: &str = include_str!("../../../SUITE.lock");

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Associativity {
    Left,
    Right,
    Non,
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
    Operator {
        symbol: "=",
        precedence: 50,
        associativity: Associativity::Non,
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
    Operator {
        symbol: "=",
        precedence: 50,
        associativity: Associativity::Non,
    },
];

const FIXED_SYMBOLS: &[&str] = &["(", ")", "fun", "=>", "∀", ":", ","];

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
        label: "nonassoc_eq",
        source: "1 = 2",
        reference_tree: r#"(«term_=_» (num "1") "=" (num "2"))"#,
    },
    ReferenceCase {
        label: "parenthesized",
        source: "(1 + 2) * 3",
        reference_tree: r#"(«term_*_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `_@._stdin.3953391374._hygCtx._hyg.8)) («term_+_» (num "1") "+" (num "2")) ")") "*" (num "3"))"#,
    },
    ReferenceCase {
        label: "application",
        source: "f x y",
        reference_tree: r#"(Term.app `f._@._stdin.3953391374._hygCtx._hyg.8 [`x._@._stdin.3953391374._hygCtx._hyg.8 `y._@._stdin.3953391374._hygCtx._hyg.8])"#,
    },
    ReferenceCase {
        label: "dotted_ident",
        source: "Nat.succ",
        reference_tree: r#"`Nat.succ._@._stdin.3953391374._hygCtx._hyg.8"#,
    },
    ReferenceCase {
        label: "escaped_ident",
        source: "«odd name»",
        reference_tree: r#"`odd name._@._stdin.3953391374._hygCtx._hyg.8"#,
    },
    ReferenceCase {
        label: "lambda",
        source: "fun x => x",
        reference_tree: r#"(Term.fun "fun" (Term.basicFun [`x._@._stdin.3953391374._hygCtx._hyg.8] [] "=>" `x._@._stdin.3953391374._hygCtx._hyg.8))"#,
    },
    ReferenceCase {
        label: "typed_lambda",
        source: "fun (x : Nat) => x",
        reference_tree: r#"(Term.fun "fun" (Term.basicFun [(Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `_@._stdin.3953391374._hygCtx._hyg.8)) `x._@._stdin.3953391374._hygCtx._hyg.8 ":" [`Nat._@._stdin.3953391374._hygCtx._hyg.8] ")")] [] "=>" `x._@._stdin.3953391374._hygCtx._hyg.8))"#,
    },
    ReferenceCase {
        label: "forall",
        source: "∀ x : Nat, x = x",
        reference_tree: r#"(Term.forall "∀" [`x._@._stdin.3953391374._hygCtx._hyg.8] [(Term.typeSpec ":" `Nat._@._stdin.3953391374._hygCtx._hyg.8)] "," («term_=_» `x._@._stdin.3953391374._hygCtx._hyg.8 "=" `x._@._stdin.3953391374._hygCtx._hyg.8))"#,
    },
    ReferenceCase {
        label: "nested_block_trivia",
        source: "1 /- outer /- inner -/ tail -/ + 2",
        reference_tree: r#"(«term_+_» (num "1") "+" (num "2"))"#,
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
        label: "octal_nat",
        source: "0o755",
        reference_tree: r#"(num "0o755")"#,
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
    ReferenceCase {
        label: "name_literal",
        source: "`Nat.succ",
        reference_tree: r#"(Term.quotedName (name "`Nat.succ"))"#,
    },
];

const DOC_COMMAND_SOURCE: &str = "/-- frozen doc -/ def x := 1";
const DOC_COMMAND_REFERENCE_TREE: &str = r#"(Command.declaration (Command.declModifiers [(Command.docComment "/--" "frozen doc -/")] [] [] [] [] [] []) (Command.definition "def" (Command.declId `x._@._stdin.3158774818._hygCtx._hyg.8 []) (Command.optDeclSig [] []) (Command.declValSimple ":=" (num "1") (Termination.suffix [] []) []) []))"#;

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
    leaves: Leaves,
    leading: Vec<IndexedProduction>,
    trailing: Vec<IndexedProduction>,
}

impl FixtureGrammar {
    fn build(source: &str, operators: &'static [Operator]) -> Result<Arc<FixtureGrammar>, String> {
        let text = SourceText::from_utf8(source.as_bytes())
            .map_err(|error| format!("source was not valid UTF-8: {error:?}"))?;
        let table = TokenTable::from_tokens(
            operators
                .iter()
                .map(|operator| operator.symbol)
                .chain(FIXED_SYMBOLS.iter().copied()),
        );
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

                if matches!(token.kind, TokenKind::Ident(_)) {
                    leading.push(IndexedProduction {
                        token_index,
                        production: identifier_production(leaf.clone(), token.extent.end()),
                    });
                }

                if let TokenKind::Symbol(symbol) = &token.kind {
                    match symbol.as_str() {
                        "(" => leading.push(IndexedProduction {
                            token_index,
                            production: parenthesized_production(
                                grammar.clone(),
                                leaf.clone(),
                                token.extent.end(),
                            ),
                        }),
                        "fun" => leading.push(IndexedProduction {
                            token_index,
                            production: lambda_production(
                                grammar.clone(),
                                leaf.clone(),
                                token.extent.end(),
                            ),
                        }),
                        "∀" => leading.push(IndexedProduction {
                            token_index,
                            production: forall_production(
                                grammar.clone(),
                                leaf.clone(),
                                token.extent.end(),
                            ),
                        }),
                        _ => {}
                    }

                    if let Some(operator) = operators
                        .iter()
                        .copied()
                        .find(|operator| operator.symbol == symbol)
                    {
                        trailing.push(IndexedProduction {
                            token_index,
                            production: operator_production(
                                grammar.clone(),
                                operator,
                                leaf.clone(),
                                token.extent.end(),
                            ),
                        });
                    }
                }

                if matches!(token.kind, TokenKind::Ident(_) | TokenKind::Literal(_))
                    || matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == "(")
                {
                    trailing.push(IndexedProduction {
                        token_index,
                        production: application_production(grammar.clone()),
                    });
                }
            }

            FixtureGrammar {
                source: text,
                tokens,
                leaves,
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

    fn take_symbol(&self, state: &mut ParserState, expected: &str) -> Result<Syntax, ParseError> {
        let at = state.pos();
        let Some(index) = self.next_token_index(at) else {
            return Err(ParseError::consuming(
                format!("expected {expected:?}, found end of input"),
                at,
            ));
        };
        let token = &self.tokens[index];
        if !matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == expected) {
            return Err(ParseError::consuming(format!("expected {expected:?}"), at));
        }
        state.set_pos(token.extent.end());
        self.leaves
            .leaf(index)
            .map_err(|error| ParseError::consuming(format!("missing leaf: {error:?}"), at))
    }

    fn take_ident(&self, state: &mut ParserState) -> Result<Syntax, ParseError> {
        let at = state.pos();
        let Some(index) = self.next_token_index(at) else {
            return Err(ParseError::consuming(
                "expected identifier, found end of input",
                at,
            ));
        };
        let token = &self.tokens[index];
        if !matches!(token.kind, TokenKind::Ident(_)) {
            return Err(ParseError::consuming("expected identifier", at));
        }
        state.set_pos(token.extent.end());
        self.leaves
            .leaf(index)
            .map_err(|error| ParseError::consuming(format!("missing leaf: {error:?}"), at))
    }

    fn starts_application_argument(&self, state: &ParserState) -> bool {
        self.next_token_index(state.pos()).is_some_and(|index| {
            matches!(
                self.tokens[index].kind,
                TokenKind::Ident(_) | TokenKind::Literal(_)
            ) || matches!(&self.tokens[index].kind, TokenKind::Symbol(symbol) if symbol == "(")
        })
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
        let literal = Syntax::node(name(node_kind), vec![leaf.clone()]);
        if kind == LiteralKind::Name {
            state.push(Syntax::node(
                parser_kind(&["Term", "quotedName"]),
                vec![literal],
            ));
        } else {
            state.push(literal);
        }
    })
}

fn identifier_production(leaf: Syntax, end: BytePos) -> Production {
    Production::new(name("ident"), 0, move |state| {
        state.set_pos(end);
        state.set_lhs_prec(MAX_PREC);
        state.push(leaf.clone());
    })
}

fn parenthesized_production(
    grammar: Weak<FixtureGrammar>,
    lparen: Syntax,
    lparen_end: BytePos,
) -> Production {
    Production::new(parser_kind(&["Term", "paren"]), 0, move |state| {
        state.set_pos(lparen_end);
        let Some(grammar) = grammar.upgrade() else {
            state.set_error(ParseError::consuming(
                "fixture grammar expired during parenthesized parse",
                state.pos(),
            ));
            return;
        };
        let Some(inner) = parse_subterm(grammar.as_ref(), state) else {
            return;
        };
        let rparen = match grammar.take_symbol(state, ")") {
            Ok(rparen) => rparen,
            Err(error) => {
                state.set_error(error);
                return;
            }
        };
        state.push(Syntax::node(
            parser_kind(&["Term", "paren"]),
            vec![hygienic_lparen(lparen.clone()), inner, rparen],
        ));
        state.set_lhs_prec(MAX_PREC);
    })
}

fn application_production(grammar: Weak<FixtureGrammar>) -> Production {
    Production::new(parser_kind(&["Term", "app"]), 0, move |state| {
        let Some(left) = state.pop() else {
            state.set_error(ParseError::new(
                "application production has no function",
                state.pos(),
            ));
            return;
        };
        let Some(grammar) = grammar.upgrade() else {
            state.set_error(ParseError::consuming(
                "fixture grammar expired during application",
                state.pos(),
            ));
            return;
        };
        let mut arguments = Vec::new();
        while grammar.starts_application_argument(state) {
            leading_parser(grammar.as_ref(), state);
            if state.has_error() {
                return;
            }
            let Some(argument) = state.pop() else {
                state.set_error(ParseError::consuming(
                    "application argument produced no tree",
                    state.pos(),
                ));
                return;
            };
            arguments.push(argument);
        }
        if arguments.is_empty() {
            state.set_error(ParseError::new(
                "application production had no argument",
                state.pos(),
            ));
            return;
        }
        state.push(Syntax::node(
            parser_kind(&["Term", "app"]),
            vec![left, null_node(arguments)],
        ));
        state.set_lhs_prec(MAX_PREC);
    })
}

fn lambda_production(
    grammar: Weak<FixtureGrammar>,
    fun_leaf: Syntax,
    fun_end: BytePos,
) -> Production {
    Production::new(parser_kind(&["Term", "fun"]), 0, move |state| {
        state.set_pos(fun_end);
        let Some(grammar) = grammar.upgrade() else {
            state.set_error(ParseError::consuming(
                "fixture grammar expired during lambda",
                state.pos(),
            ));
            return;
        };

        let mut binders = Vec::new();
        let starts_typed = grammar
            .next_token_index(state.pos())
            .is_some_and(|index| {
                matches!(&grammar.tokens[index].kind, TokenKind::Symbol(symbol) if symbol == "(")
            });
        if starts_typed {
            let lparen = match grammar.take_symbol(state, "(") {
                Ok(leaf) => leaf,
                Err(error) => {
                    state.set_error(error);
                    return;
                }
            };
            let ident = match grammar.take_ident(state) {
                Ok(ident) => ident,
                Err(error) => {
                    state.set_error(error);
                    return;
                }
            };
            let colon = match grammar.take_symbol(state, ":") {
                Ok(colon) => colon,
                Err(error) => {
                    state.set_error(error);
                    return;
                }
            };
            let Some(ty) = parse_subterm(grammar.as_ref(), state) else {
                return;
            };
            let rparen = match grammar.take_symbol(state, ")") {
                Ok(rparen) => rparen,
                Err(error) => {
                    state.set_error(error);
                    return;
                }
            };
            binders.push(Syntax::node(
                parser_kind(&["Term", "typeAscription"]),
                vec![
                    hygienic_lparen(lparen),
                    ident,
                    colon,
                    null_node(vec![ty]),
                    rparen,
                ],
            ));
        } else {
            while grammar
                .next_token_index(state.pos())
                .is_some_and(|index| matches!(grammar.tokens[index].kind, TokenKind::Ident(_)))
            {
                match grammar.take_ident(state) {
                    Ok(ident) => binders.push(ident),
                    Err(error) => {
                        state.set_error(error);
                        return;
                    }
                }
            }
        }
        if binders.is_empty() {
            state.set_error(ParseError::consuming(
                "lambda requires at least one binder",
                state.pos(),
            ));
            return;
        }
        let arrow = match grammar.take_symbol(state, "=>") {
            Ok(arrow) => arrow,
            Err(error) => {
                state.set_error(error);
                return;
            }
        };
        let Some(body) = parse_subterm(grammar.as_ref(), state) else {
            return;
        };
        let basic = Syntax::node(
            parser_kind(&["Term", "basicFun"]),
            vec![null_node(binders), null_node(Vec::new()), arrow, body],
        );
        state.push(Syntax::node(
            parser_kind(&["Term", "fun"]),
            vec![fun_leaf.clone(), basic],
        ));
        state.set_lhs_prec(MAX_PREC);
    })
}

fn forall_production(
    grammar: Weak<FixtureGrammar>,
    forall_leaf: Syntax,
    forall_end: BytePos,
) -> Production {
    Production::new(parser_kind(&["Term", "forall"]), 0, move |state| {
        state.set_pos(forall_end);
        let Some(grammar) = grammar.upgrade() else {
            state.set_error(ParseError::consuming(
                "fixture grammar expired during forall",
                state.pos(),
            ));
            return;
        };
        let mut binders = Vec::new();
        while grammar
            .next_token_index(state.pos())
            .is_some_and(|index| matches!(grammar.tokens[index].kind, TokenKind::Ident(_)))
        {
            match grammar.take_ident(state) {
                Ok(ident) => binders.push(ident),
                Err(error) => {
                    state.set_error(error);
                    return;
                }
            }
        }
        if binders.is_empty() {
            state.set_error(ParseError::consuming(
                "forall requires at least one binder",
                state.pos(),
            ));
            return;
        }
        let colon = match grammar.take_symbol(state, ":") {
            Ok(colon) => colon,
            Err(error) => {
                state.set_error(error);
                return;
            }
        };
        let Some(ty) = parse_subterm(grammar.as_ref(), state) else {
            return;
        };
        let comma = match grammar.take_symbol(state, ",") {
            Ok(comma) => comma,
            Err(error) => {
                state.set_error(error);
                return;
            }
        };
        let Some(body) = parse_subterm(grammar.as_ref(), state) else {
            return;
        };
        let type_spec = Syntax::node(parser_kind(&["Term", "typeSpec"]), vec![colon, ty]);
        state.push(Syntax::node(
            parser_kind(&["Term", "forall"]),
            vec![
                forall_leaf.clone(),
                null_node(binders),
                null_node(vec![type_spec]),
                comma,
                body,
            ],
        ));
        state.set_lhs_prec(MAX_PREC);
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
        Associativity::Non => (operator.precedence + 1, operator.precedence + 1),
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

fn qualified_name(components: &[&str]) -> Name {
    components
        .iter()
        .fold(Name::anonymous(), |prefix, component| {
            Name::str(prefix, *component)
        })
}

fn parser_kind(components: &[&str]) -> Name {
    let mut full = vec!["Lean", "Parser"];
    full.extend_from_slice(components);
    qualified_name(&full)
}

fn null_node(args: Vec<Syntax>) -> Syntax {
    Syntax::node(null_kind(), args)
}

fn hygiene_ident() -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::empty_at(BytePos(0)),
        val: Name::anonymous(),
        preresolved: Vec::new(),
    }
}

fn hygienic_lparen(lparen: Syntax) -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "hygienicLParen"]),
        vec![
            lparen,
            Syntax::node(name("hygieneInfo"), vec![hygiene_ident()]),
        ],
    )
}

fn parse_subterm(grammar: &FixtureGrammar, state: &mut ParserState) -> Option<Syntax> {
    let outer_precedence = state.prec();
    state.set_prec(0);
    pratt_parser(grammar, state);
    state.set_prec(outer_precedence);
    if state.has_error() {
        return None;
    }
    let Some(term) = state.pop() else {
        state.set_error(ParseError::consuming(
            "subterm parser produced no tree",
            state.pos(),
        ));
        return None;
    };
    Some(term)
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

fn parse_doc_definition(source: &str) -> Result<Syntax, String> {
    let text = SourceText::from_utf8(source.as_bytes())
        .map_err(|error| format!("doc command was not valid UTF-8: {error:?}"))?;
    let table = TokenTable::from_tokens(["/--", "-/", "def", ":="]);
    let run = lex_run(&text, &table);
    if !run.accepted() {
        return Err(format!(
            "doc command lexer refused: {:?}",
            run.diagnostics()
        ));
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
    let signature = tokens
        .iter()
        .map(|token| match &token.kind {
            TokenKind::Symbol(symbol) => format!("symbol:{symbol}"),
            TokenKind::Ident(ident) => format!("ident:{}", ident.to_display_string()),
            TokenKind::Literal(kind) => format!("literal:{kind:?}"),
        })
        .collect::<Vec<_>>()
        .join("|");
    let expected =
        "symbol:/--|ident:frozen|ident:doc|symbol:-/|symbol:def|ident:x|symbol::=|literal:Nat";
    if signature != expected {
        return Err(format!(
            "doc command token sequence diverged: expected {expected:?}, got {signature:?}"
        ));
    }
    let leaves = Leaves::build(&text, &tokens)
        .map_err(|error| format!("doc command attachment refused: {error:?}"))?;
    let leaf = |index| {
        leaves
            .leaf(index)
            .map_err(|error| format!("doc command leaf {index} missing: {error:?}"))
    };
    let body = text
        .as_str()
        .get(tokens[1].extent.start().0..tokens[3].extent.end().0)
        .ok_or_else(|| "doc comment body span was not a UTF-8 boundary".to_string())?;

    let doc_comment = Syntax::node(
        parser_kind(&["Command", "docComment"]),
        vec![leaf(0)?, Syntax::atom(SourceInfo::None, body)],
    );
    let modifiers = Syntax::node(
        parser_kind(&["Command", "declModifiers"]),
        vec![
            null_node(vec![doc_comment]),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
        ],
    );
    let decl_id = Syntax::node(
        parser_kind(&["Command", "declId"]),
        vec![leaf(5)?, null_node(Vec::new())],
    );
    let opt_decl_sig = Syntax::node(
        parser_kind(&["Command", "optDeclSig"]),
        vec![null_node(Vec::new()), null_node(Vec::new())],
    );
    let numeral = Syntax::node(name("num"), vec![leaf(7)?]);
    let termination = Syntax::node(
        parser_kind(&["Termination", "suffix"]),
        vec![null_node(Vec::new()), null_node(Vec::new())],
    );
    let decl_value = Syntax::node(
        parser_kind(&["Command", "declValSimple"]),
        vec![leaf(6)?, numeral, termination, null_node(Vec::new())],
    );
    let definition = Syntax::node(
        parser_kind(&["Command", "definition"]),
        vec![
            leaf(4)?,
            decl_id,
            opt_decl_sig,
            decl_value,
            null_node(Vec::new()),
        ],
    );
    Ok(Syntax::node(
        parser_kind(&["Command", "declaration"]),
        vec![modifiers, definition],
    ))
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum HygieneAuthorityError {
    UnsupportedAuthority { at: usize },
    MissingModuleDigest { at: usize },
    MissingHygieneOrdinal { at: usize },
    ContinuedAuthority { at: usize },
}

impl fmt::Display for HygieneAuthorityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HygieneAuthorityError::UnsupportedAuthority { at } => {
                write!(formatter, "unsupported hygiene authority at byte {at}")
            }
            HygieneAuthorityError::MissingModuleDigest { at } => {
                write!(
                    formatter,
                    "hygiene authority has no decimal module digest at byte {at}"
                )
            }
            HygieneAuthorityError::MissingHygieneOrdinal { at } => {
                write!(
                    formatter,
                    "hygiene authority has no decimal ordinal at byte {at}"
                )
            }
            HygieneAuthorityError::ContinuedAuthority { at } => {
                write!(
                    formatter,
                    "hygiene authority continues past its ordinal at byte {at}"
                )
            }
        }
    }
}

/// Replace exactly the authority syntax quotations add to an identifier.
///
/// This is not a general text scrubber. Seeing `_@.` commits the fixture to the one authority the
/// pinned probe emits; malformed, non-decimal, or extended variants refuse instead of surviving
/// unexamined or being normalized into a false match.
fn normalize_reference_hygiene(raw: &str) -> Result<String, HygieneAuthorityError> {
    const PREFIX: &str = "_@._stdin.";
    const MIDDLE: &str = "._hygCtx._hyg.";
    const MARKER: &str = "_@.<hygiene>";

    let mut out = String::with_capacity(raw.len());
    let mut cursor = 0usize;
    while let Some(relative) = raw[cursor..].find("_@.") {
        let at = cursor + relative;
        out.push_str(&raw[cursor..at]);
        let authority = &raw[at..];
        let Some(after_prefix) = authority.strip_prefix(PREFIX) else {
            return Err(HygieneAuthorityError::UnsupportedAuthority { at });
        };
        let digest_len = after_prefix.bytes().take_while(u8::is_ascii_digit).count();
        if digest_len == 0 {
            return Err(HygieneAuthorityError::MissingModuleDigest { at });
        }
        let after_digest = &after_prefix[digest_len..];
        let Some(after_middle) = after_digest.strip_prefix(MIDDLE) else {
            return Err(HygieneAuthorityError::UnsupportedAuthority { at });
        };
        let ordinal_len = after_middle.bytes().take_while(u8::is_ascii_digit).count();
        if ordinal_len == 0 {
            return Err(HygieneAuthorityError::MissingHygieneOrdinal { at });
        }
        let consumed = PREFIX.len() + digest_len + MIDDLE.len() + ordinal_len;
        if authority[consumed..].starts_with('.') {
            return Err(HygieneAuthorityError::ContinuedAuthority { at: at + consumed });
        }
        out.push_str(MARKER);
        cursor = at + consumed;
    }
    out.push_str(&raw[cursor..]);
    Ok(out)
}

/// Render the comparison subset in the Reference's `Syntax.toString` vocabulary.
///
/// This is intentionally total only over the declared subset. Encountering a missing/recovered
/// node or an unexpected kind is a typed test failure; it is never erased by a wildcard
/// normalizer.
fn render_reference_shape(syntax: &Syntax) -> Result<String, String> {
    match syntax {
        Syntax::Missing => Err("comparison subset does not admit Syntax::Missing".to_string()),
        Syntax::Ident { val, .. } => {
            if val.is_anonymous() {
                Ok("`_@.<hygiene>".to_string())
            } else {
                Ok(format!("`{}._@.<hygiene>", val.to_display_string()))
            }
        }
        Syntax::Atom { val, .. } => Ok(format!("{val:?}")),
        Syntax::Node { kind, args, .. } => {
            let display = kind.to_display_string();
            let rendered_args = args
                .iter()
                .map(render_reference_shape)
                .collect::<Result<Vec<_>, _>>()?;
            if display == "null" {
                return Ok(format!("[{}]", rendered_args.join(" ")));
            }

            const EXACT_KINDS: &[&str] = &[
                "num",
                "scientific",
                "str",
                "char",
                "name",
                "hygieneInfo",
                "Lean.Parser.Term.paren",
                "Lean.Parser.Term.hygienicLParen",
                "Lean.Parser.Term.app",
                "Lean.Parser.Term.fun",
                "Lean.Parser.Term.basicFun",
                "Lean.Parser.Term.typeAscription",
                "Lean.Parser.Term.forall",
                "Lean.Parser.Term.typeSpec",
                "Lean.Parser.Term.quotedName",
                "Lean.Parser.Command.declaration",
                "Lean.Parser.Command.declModifiers",
                "Lean.Parser.Command.docComment",
                "Lean.Parser.Command.definition",
                "Lean.Parser.Command.declId",
                "Lean.Parser.Command.optDeclSig",
                "Lean.Parser.Command.declValSimple",
                "Lean.Parser.Termination.suffix",
            ];
            let rendered_kind = if display.starts_with("term_") {
                format!("«{display}»")
            } else if EXACT_KINDS.contains(&display.as_str()) {
                display
                    .strip_prefix("Lean.Parser.")
                    .unwrap_or(&display)
                    .to_string()
            } else {
                return Err(format!(
                    "comparison subset has no rule for node kind {display:?}"
                ));
            };
            if rendered_args.is_empty() {
                Ok(format!("({rendered_kind})"))
            } else {
                Ok(format!("({rendered_kind} {})", rendered_args.join(" ")))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum DifferentialFailure {
    Parse {
        label: &'static str,
        reason: String,
    },
    ReferenceFixture {
        label: &'static str,
        reason: String,
    },
    Render {
        label: &'static str,
        reason: String,
    },
    TreeMismatch {
        label: &'static str,
        source: &'static str,
        expected: String,
        actual: String,
    },
}

impl fmt::Display for DifferentialFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DifferentialFailure::Parse { label, reason } => {
                write!(formatter, "{label}: Vellum parse refused: {reason}")
            }
            DifferentialFailure::ReferenceFixture { label, reason } => {
                write!(formatter, "{label}: Reference fixture refused: {reason}")
            }
            DifferentialFailure::Render { label, reason } => {
                write!(
                    formatter,
                    "{label}: Vellum tree could not be compared: {reason}"
                )
            }
            DifferentialFailure::TreeMismatch {
                label,
                source,
                expected,
                actual,
            } => write!(
                formatter,
                "{label}: tree_mismatch for {source:?}; expected {expected:?}, actual {actual:?}"
            ),
        }
    }
}

fn compare_case(
    case: &ReferenceCase,
    operators: &'static [Operator],
) -> Result<(), DifferentialFailure> {
    let syntax = parse(case.source, operators).map_err(|reason| DifferentialFailure::Parse {
        label: case.label,
        reason,
    })?;
    let actual = render_reference_shape(&syntax).map_err(|reason| DifferentialFailure::Render {
        label: case.label,
        reason,
    })?;
    let expected = normalize_reference_hygiene(case.reference_tree).map_err(|error| {
        DifferentialFailure::ReferenceFixture {
            label: case.label,
            reason: error.to_string(),
        }
    })?;
    if actual == expected {
        Ok(())
    } else {
        Err(DifferentialFailure::TreeMismatch {
            label: case.label,
            source: case.source,
            expected,
            actual,
        })
    }
}

#[test]
fn actual_pratt_trees_match_every_frozen_reference_tree() {
    assert_eq!(
        CASES.len(),
        25,
        "the frozen term slice has an explicit anti-shrink floor"
    );
    for case in CASES {
        compare_case(case, OPERATORS).unwrap_or_else(|failure| panic!("{failure}"));
    }
}

#[test]
fn doc_comment_command_matches_the_frozen_reference_tree() {
    let syntax = parse_doc_definition(DOC_COMMAND_SOURCE)
        .unwrap_or_else(|error| panic!("doc_comment_command: {error}"));
    let actual = render_reference_shape(&syntax)
        .unwrap_or_else(|error| panic!("doc_comment_command: {error}"));
    let expected = normalize_reference_hygiene(DOC_COMMAND_REFERENCE_TREE)
        .unwrap_or_else(|error| panic!("doc_comment_command fixture: {error}"));
    assert_eq!(
        actual, expected,
        "doc_comment_command: tree_mismatch for {DOC_COMMAND_SOURCE:?}"
    );
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
            (case.reference_tree.starts_with('(') && case.reference_tree.ends_with(')'))
                || case.reference_tree.starts_with('`'),
            "{}: fixture must be a structural Syntax rendering",
            case.label
        );
        normalize_reference_hygiene(case.reference_tree)
            .unwrap_or_else(|error| panic!("{}: malformed fixture authority: {error}", case.label));
    }
    normalize_reference_hygiene(DOC_COMMAND_REFERENCE_TREE).unwrap_or_else(|error| {
        panic!("doc_comment_command: malformed fixture authority: {error}")
    });
}

#[test]
fn reversed_precedence_mutant_is_killed_by_the_reference_tree() {
    let case = CASES
        .iter()
        .find(|case| case.label == "add_mul")
        .expect("the discriminating add/mul row exists");
    let failure = compare_case(case, REVERSED_PRECEDENCE_MUTANT)
        .expect_err("the frozen Reference tree must kill a uniform precedence error");
    let DifferentialFailure::TreeMismatch { label, actual, .. } = failure else {
        panic!("the planted divergence must be named tree_mismatch, got {failure}");
    };
    assert_eq!(label, "add_mul", "the mismatch names its fixture");
    assert_eq!(
        actual, "(«term_*_» («term_+_» (num \"1\") \"+\" (num \"2\")) \"*\" (num \"3\"))",
        "the planted table must produce the intended wrong grouping"
    );
}

#[test]
fn nonassociative_equality_refuses_the_reference_chain() {
    let refusal = parse("1 = 2 = 3", OPERATORS)
        .expect_err("the Reference refuses a second non-associative equality");
    assert!(
        refusal.contains("left token Symbol(\"=\") at byte 6"),
        "the second equality must remain at the pin's refusal point: {refusal}"
    );
}

#[test]
fn hygiene_normalization_is_narrow_and_preserves_structure() {
    let raw = r#"(Term.app `f._@._stdin.3953391374._hygCtx._hyg.8 [`x._@._stdin.3953391374._hygCtx._hyg.8])"#;
    assert_eq!(
        normalize_reference_hygiene(raw).as_deref(),
        Ok(r#"(Term.app `f._@.<hygiene> [`x._@.<hygiene>])"#),
        "only the volatile decimal authority changes"
    );
    assert_eq!(
        normalize_reference_hygiene(r#"`x._@._stdin.not_decimal._hygCtx._hyg.8"#),
        Err(HygieneAuthorityError::MissingModuleDigest { at: 3 }),
        "a lookalike authority refuses instead of surviving or being scrubbed"
    );
    assert_eq!(
        normalize_reference_hygiene(r#"`x._@._stdin.1._hygCtx._hyg.8.extra"#),
        Err(HygieneAuthorityError::ContinuedAuthority { at: 29 }),
        "an extended authority cannot be collapsed onto the supported one"
    );
}

fn pinned_reference_binary() -> Result<PathBuf, &'static str> {
    let home = std::env::var_os("HOME").ok_or("HOME is not set")?;
    let binary = Path::new(&home).join(".elan/toolchains/leanprover--lean4---v4.32.0/bin/lean");
    binary
        .is_file()
        .then_some(binary)
        .ok_or("the pinned Reference toolchain is not installed")
}

#[test]
fn installed_reference_identity_matches_the_frozen_provenance_or_skips_typed() {
    let binary = match pinned_reference_binary() {
        Ok(binary) => binary,
        Err(reason) => {
            println!("SKIP reference_parse_tree: {reason}; frozen fixtures still run");
            return;
        }
    };
    let output = Command::new(binary)
        .arg("--githash")
        .output()
        .expect("the installed Reference binary must answer --githash");
    assert!(
        output.status.success(),
        "the installed Reference --githash probe failed: {:?}",
        output.status.code()
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        REFERENCE_COMMIT,
        "an installed but different Reference cannot validate these fixtures"
    );
}
