//! **fln-parse** — Vellum's engine — the extensible Pratt parser preserving
//! parse/elaborate interleaving, byte-exact positions, and error recovery that
//! never changes acceptance (plan §9).
//!
//! The general Pratt/category machinery lives in the modules below. The
//! [`parse_nat_definition`] entry point is deliberately much smaller: it is the
//! first production command seam for `fln-elab` (bead `fln-5720`) and accepts
//! optional explicit `Nat` parameters followed by a natural literal, identifier,
//! or saturated identifier-headed application of those atom forms. It uses the
//! same source view, lexer, attachment, and canonical `Syntax` shape as the
//! general engine. Being outside this seed grammar is a typed refusal, not a
//! claim that the source is invalid Lean.

#![forbid(unsafe_code)]

pub mod build;
pub mod category;
pub mod macro_expand;
pub mod macro_txn;
pub mod pratt;
pub mod recovery;
pub mod registry;
pub mod state;

use build::{BuildError, Leaves};
use fln_core::name::Name;
use fln_syntax::literal::LiteralKind;
use fln_syntax::run::{Event, lex_run};
use fln_syntax::source::{BytePos, ByteSpan, SourceError, SourceText};
use fln_syntax::token::{LexedToken, TokenKind, TokenTable};
use fln_syntax::tree::Syntax;
use fln_syntax::view::SourceView;

/// One lexical refusal, mapped back from the parser's normalized view to the
/// original source bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseDiagnostic {
    pub message: &'static str,
    pub at: BytePos,
}

/// The next form required by the first command grammar slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatDefinitionExpectation {
    DefinitionKeyword,
    DeclarationIdentifier,
    ParameterIdentifier,
    ParameterTypeAscription,
    NaturalType,
    ClosingParenthesis,
    Assignment,
    NaturalValue,
    EndOfCommand,
}

/// Why the bounded natural-definition command parser refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatDefinitionParseError {
    Source(SourceError),
    /// The seed token table could not classify some bytes. This is a diagnostic
    /// from this bounded driver, not a proof that a complete Lean grammar would
    /// reject those bytes.
    Lexical {
        diagnostics: Vec<ParseDiagnostic>,
    },
    /// The bytes may be valid Lean; they are simply outside this first command
    /// grammar. No source-level rejection can be inferred from this variant.
    OutsideSeedGrammar {
        at: BytePos,
        expected: NatDefinitionExpectation,
    },
    Build(BuildError),
}

impl From<BuildError> for NatDefinitionParseError {
    fn from(error: BuildError) -> Self {
        NatDefinitionParseError::Build(error)
    }
}

/// A command tree together with the normalized source coordinate system its
/// leaves name. Keeping the view makes both the byte-exact original and the
/// parser-visible text recoverable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedNatDefinition {
    source_view: SourceView,
    syntax: Syntax,
    epilogue: ByteSpan,
}

impl ParsedNatDefinition {
    pub fn syntax(&self) -> &Syntax {
        &self.syntax
    }

    pub fn source_view(&self) -> &SourceView {
        &self.source_view
    }

    pub const fn epilogue(&self) -> ByteSpan {
        self.epilogue
    }

    pub fn reconstruct_normalized(&self) -> Option<Vec<u8>> {
        self.syntax
            .reconstruct(self.source_view.normalized(), self.epilogue)
    }

    pub fn reconstruct_original(&self) -> Vec<u8> {
        self.source_view.reconstruct_original()
    }
}

fn parser_kind(components: &[&str]) -> Name {
    let mut name = Name::from_components(["Lean", "Parser"]);
    for component in components {
        name = Name::str(name, *component);
    }
    name
}

fn null_node(args: Vec<Syntax>) -> Syntax {
    Syntax::node(state::null_kind(), args)
}

fn original_position(view: &SourceView, tokens: &[LexedToken], index: usize) -> BytePos {
    let in_view = tokens
        .get(index)
        .map_or(BytePos(view.normalized().len_bytes()), |token| {
            token.extent.start()
        });
    view.to_original(in_view)
}

/// Parse the first production command subset:
///
/// ```text
/// def <identifier> (<identifier> : Nat)* := <natural-literal-or-identifier>
/// def <identifier> (<identifier> : Nat)* := <identifier> <natural-literal-or-identifier>+
/// ```
///
pub fn parse_nat_definition(source: &[u8]) -> Result<ParsedNatDefinition, NatDefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let table = TokenTable::from_tokens(["def", "(", ")", ":", ":="]);
    let run = lex_run(view.normalized(), &table);
    let diagnostics = run
        .diagnostics()
        .into_iter()
        .map(|(message, at)| ParseDiagnostic {
            message,
            at: view.to_original(at),
        })
        .collect::<Vec<_>>();
    if !diagnostics.is_empty() {
        return Err(NatDefinitionParseError::Lexical { diagnostics });
    }

    let tokens = run
        .events
        .into_iter()
        .filter_map(|event| match event {
            Event::Token(token) => Some(token),
            Event::Trivia(_) | Event::Refused { .. } => None,
        })
        .collect::<Vec<_>>();

    if !matches!(
        tokens.first().map(|token| &token.kind),
        Some(TokenKind::Symbol(symbol)) if symbol == "def"
    ) {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(&view, &tokens, 0),
            expected: NatDefinitionExpectation::DefinitionKeyword,
        });
    }
    if !matches!(
        tokens.get(1).map(|token| &token.kind),
        Some(TokenKind::Ident(_))
    ) {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(&view, &tokens, 1),
            expected: NatDefinitionExpectation::DeclarationIdentifier,
        });
    }
    let mut parameter_starts = Vec::new();
    let mut cursor = 2;
    while matches!(
        tokens.get(cursor).map(|token| &token.kind),
        Some(TokenKind::Symbol(symbol)) if symbol == "("
    ) {
        parameter_starts.push(cursor);
        if !matches!(
            tokens.get(cursor + 1).map(|token| &token.kind),
            Some(TokenKind::Ident(_))
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, cursor + 1),
                expected: NatDefinitionExpectation::ParameterIdentifier,
            });
        }
        if !matches!(
            tokens.get(cursor + 2).map(|token| &token.kind),
            Some(TokenKind::Symbol(symbol)) if symbol == ":"
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, cursor + 2),
                expected: NatDefinitionExpectation::ParameterTypeAscription,
            });
        }
        if !matches!(
            tokens.get(cursor + 3).map(|token| &token.kind),
            Some(TokenKind::Ident(name)) if name == &Name::from_components(["Nat"])
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, cursor + 3),
                expected: NatDefinitionExpectation::NaturalType,
            });
        }
        if !matches!(
            tokens.get(cursor + 4).map(|token| &token.kind),
            Some(TokenKind::Symbol(symbol)) if symbol == ")"
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, cursor + 4),
                expected: NatDefinitionExpectation::ClosingParenthesis,
            });
        }
        cursor += 5;
    }
    let assignment_index = cursor;
    if !matches!(
        tokens.get(assignment_index).map(|token| &token.kind),
        Some(TokenKind::Symbol(symbol)) if symbol == ":="
    ) {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(&view, &tokens, assignment_index),
            expected: NatDefinitionExpectation::Assignment,
        });
    }
    let value_index = assignment_index + 1;
    if !matches!(
        tokens.get(value_index).map(|token| &token.kind),
        Some(TokenKind::Literal(LiteralKind::Nat) | TokenKind::Ident(_))
    ) {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(&view, &tokens, value_index),
            expected: NatDefinitionExpectation::NaturalValue,
        });
    }
    if tokens.len() > value_index + 1
        && !matches!(
            tokens.get(value_index).map(|token| &token.kind),
            Some(TokenKind::Ident(_))
        )
    {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(&view, &tokens, value_index + 1),
            expected: NatDefinitionExpectation::EndOfCommand,
        });
    }
    for index in value_index + 1..tokens.len() {
        if !matches!(
            tokens.get(index).map(|token| &token.kind),
            Some(TokenKind::Literal(LiteralKind::Nat) | TokenKind::Ident(_))
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, index),
                expected: NatDefinitionExpectation::NaturalValue,
            });
        }
    }

    let leaves = Leaves::build(view.normalized(), &tokens)?;
    let epilogue = leaves.attachment().epilogue();
    let definition_keyword = leaves.leaf(0)?;
    let declaration_name = leaves.leaf(1)?;
    let assignment = leaves.leaf(assignment_index)?;

    let modifiers = Syntax::node(
        parser_kind(&["Command", "declModifiers"]),
        vec![
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
        ],
    );
    let declaration_id = Syntax::node(
        parser_kind(&["Command", "declId"]),
        vec![declaration_name, null_node(Vec::new())],
    );
    let mut parameters = Vec::new();
    for start in parameter_starts {
        parameters.push(Syntax::node(
            parser_kind(&["Term", "explicitBinder"]),
            vec![
                leaves.leaf(start)?,
                null_node(vec![leaves.leaf(start + 1)?]),
                null_node(vec![leaves.leaf(start + 2)?, leaves.leaf(start + 3)?]),
                null_node(Vec::new()),
                leaves.leaf(start + 4)?,
            ],
        ));
    }
    let optional_signature = Syntax::node(
        parser_kind(&["Command", "optDeclSig"]),
        vec![null_node(parameters), null_node(Vec::new())],
    );
    let term_leaf = |index: usize| -> Result<Syntax, NatDefinitionParseError> {
        let leaf = leaves.leaf(index)?;
        match tokens.get(index).map(|token| &token.kind) {
            Some(TokenKind::Literal(LiteralKind::Nat)) => Ok(Syntax::node(
                Name::str(Name::anonymous(), "num"),
                vec![leaf],
            )),
            Some(TokenKind::Ident(_)) => Ok(leaf),
            _ => Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, index),
                expected: NatDefinitionExpectation::NaturalValue,
            }),
        }
    };
    let head = term_leaf(value_index)?;
    let value = if tokens.len() == value_index + 1 {
        head
    } else {
        let mut arguments = Vec::new();
        for index in value_index + 1..tokens.len() {
            arguments.push(term_leaf(index)?);
        }
        Syntax::node(
            parser_kind(&["Term", "app"]),
            vec![head, null_node(arguments)],
        )
    };
    let termination = Syntax::node(
        parser_kind(&["Termination", "suffix"]),
        vec![null_node(Vec::new()), null_node(Vec::new())],
    );
    let declaration_value = Syntax::node(
        parser_kind(&["Command", "declValSimple"]),
        vec![assignment, value, termination, null_node(Vec::new())],
    );
    let definition = Syntax::node(
        parser_kind(&["Command", "definition"]),
        vec![
            definition_keyword,
            declaration_id,
            optional_signature,
            declaration_value,
            null_node(Vec::new()),
        ],
    );
    let syntax = Syntax::node(
        parser_kind(&["Command", "declaration"]),
        vec![modifiers, definition],
    );

    Ok(ParsedNatDefinition {
        source_view: view,
        syntax,
        epilogue,
    })
}

#[cfg(test)]
mod nat_definition_tests {
    use super::*;

    #[test]
    fn command_slice_builds_the_canonical_tree_and_retains_both_source_views() {
        let source = b"def answer := 18446744073709551616\r\n";
        let parsed = parse_nat_definition(source).expect("the seed command parses");

        assert_eq!(
            parsed
                .syntax()
                .kind()
                .map(Name::to_display_string)
                .as_deref(),
            Some("Lean.Parser.Command.declaration")
        );
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(b"def answer := 18446744073709551616\n".as_slice())
        );
        assert_eq!(parsed.reconstruct_original(), source);
        assert_eq!(parsed.source_view().removed_count(), 1);
    }

    #[test]
    fn command_slice_retains_an_identifier_value_as_the_canonical_leaf() {
        let source = b"def copy := answer";
        let parsed = parse_nat_definition(source).expect("the seed Nat reference parses");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );

        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node { args: value, .. } = &definition[3] else {
            panic!("the definition value must use declValSimple");
        };
        assert!(matches!(
            &value[1],
            Syntax::Ident { val, .. } if val.to_display_string() == "answer"
        ));
    }

    #[test]
    fn command_slice_builds_the_reference_application_shape_without_losing_source() {
        let source = b"def selected := first 17 29";
        let parsed = parse_nat_definition(source).expect("the bounded Nat application parses");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );

        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node { args: value, .. } = &definition[3] else {
            panic!("the definition value must use declValSimple");
        };
        let Syntax::Node {
            kind,
            args: application,
            ..
        } = &value[1]
        else {
            panic!("the source application must be a term node");
        };
        assert_eq!(kind, &parser_kind(&["Term", "app"]));
        assert!(matches!(
            &application[0],
            Syntax::Ident { val, .. } if val.to_display_string() == "first"
        ));
        let Syntax::Node {
            kind,
            args: arguments,
            ..
        } = &application[1]
        else {
            panic!("the application arguments must use the Reference null array shape");
        };
        assert_eq!(kind, &state::null_kind());
        assert_eq!(arguments.len(), 2);
        assert!(arguments.iter().all(|argument| matches!(
            argument,
            Syntax::Node { kind, args, .. }
                if kind == &Name::str(Name::anonymous(), "num") && args.len() == 1
        )));
    }

    #[test]
    fn command_slice_builds_the_reference_explicit_nat_binder_shape() {
        let source = b"def first (x : Nat) (y : Nat) := x";
        let parsed = parse_nat_definition(source).expect("explicit Nat parameters parse");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );

        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node {
            kind,
            args: signature,
            ..
        } = &definition[2]
        else {
            panic!("the definition must carry an optional signature node");
        };
        assert_eq!(kind, &parser_kind(&["Command", "optDeclSig"]));
        let Syntax::Node {
            kind,
            args: binders,
            ..
        } = &signature[0]
        else {
            panic!("the signature binders must use the Reference null array shape");
        };
        assert_eq!(kind, &state::null_kind());
        assert_eq!(binders.len(), 2);
        for (binder, expected_name) in binders.iter().zip(["x", "y"]) {
            let Syntax::Node { kind, args, .. } = binder else {
                panic!("each parameter must be an explicit binder node");
            };
            assert_eq!(kind, &parser_kind(&["Term", "explicitBinder"]));
            assert_eq!(args.len(), 5);
            assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "("));
            assert!(matches!(
                &args[1],
                Syntax::Node { kind, args, .. }
                    if kind == &state::null_kind()
                        && matches!(&args[..], [Syntax::Ident { val, .. }]
                            if val.to_display_string() == expected_name)
            ));
            assert!(matches!(
                &args[2],
                Syntax::Node { kind, args, .. }
                    if kind == &state::null_kind()
                        && matches!(&args[..],
                            [Syntax::Atom { val: colon, .. }, Syntax::Ident { val: ty, .. }]
                            if colon == ":" && ty.to_display_string() == "Nat")
            ));
            assert!(matches!(
                &args[3],
                Syntax::Node { kind, args, .. }
                    if kind == &state::null_kind() && args.is_empty()
            ));
            assert!(matches!(&args[4], Syntax::Atom { val, .. } if val == ")"));
        }
    }

    #[test]
    fn source_and_seed_grammar_refusals_remain_typed() {
        assert!(matches!(
            parse_nat_definition(&[0xff]),
            Err(NatDefinitionParseError::Source(SourceError::NotUtf8 {
                at: BytePos(0)
            }))
        ));
        assert!(matches!(
            parse_nat_definition(b"theorem answer := 42"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::DefinitionKeyword,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer := 42 extra"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::EndOfCommand,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer := identity \"not a Nat\""),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalValue,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer (x : String) := x"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalType,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer (x : Nat := x"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::ClosingParenthesis,
                ..
            })
        ));
    }
}
