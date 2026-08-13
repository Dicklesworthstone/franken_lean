//! Quotation, antiquotation, splice, nesting, and source-map production laws.

#![forbid(unsafe_code)]

use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::domain::Digest;
use fln_parse::macro_expand::{
    GeneratedName, HygienePolicy, MacroExpansion, MacroExpansionBudget, MacroExpansionCoordinates,
    MacroExpansionError, MacroExpansionInput, QuotationContext, QuotationTemplate, QuotedSyntax,
    expand_quotation,
};
use fln_parse::registry::GrammarEpoch;
use fln_parse::state::null_kind;
use fln_syntax::hygiene::{
    ExpansionOrigin, ExpansionPath, OriginKind, SyntaxPath, extract_macro_scopes,
};
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};
use fln_syntax::tree::{Preresolved, Syntax};

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(BytePos(start), BytePos(end)).expect("forward span")
}

fn original(start: usize, end: usize) -> SourceInfo {
    SourceInfo::Original {
        leading: ByteSpan::empty_at(BytePos(start)),
        pos: BytePos(start),
        trailing: ByteSpan::empty_at(BytePos(end)),
        end_pos: BytePos(end),
    }
}

fn coordinates(mode: Mode, revision: u64) -> MacroExpansionCoordinates {
    MacroExpansionCoordinates {
        grammar_epoch: GrammarEpoch::from_parts(revision, Digest([revision as u8; 32])),
        mode,
        expansion_path: ExpansionPath::root(
            ExpansionOrigin::new(Name::from_components(["Main", "Quotation"]), 5),
            2,
        ),
    }
}

fn quotation() -> QuotationContext {
    QuotationContext {
        name: Name::from_components(["Main", "quotation", "_hygCtx"]),
        macro_scope: 17,
        call_site: Some(span(100, 120)),
        canonical: true,
        hygiene: HygienePolicy::Enabled,
    }
}

fn ident(text: &str, start: usize, preresolved: Vec<Preresolved>) -> Syntax {
    Syntax::Ident {
        info: original(start, start + text.len()),
        raw_val: span(start, start + text.len()),
        val: Name::from_components([text]),
        preresolved,
    }
}

fn complete(input: MacroExpansionInput) -> MacroExpansion {
    match expand_quotation(input, MacroExpansionBudget::generous(), None) {
        Outcome::Complete(Ok(expansion)) => expansion,
        other => panic!("expected a completed expansion, got {other:?}"),
    }
}

fn full_template() -> QuotationTemplate {
    QuotationTemplate::Node {
        definition_info: original(0, 30),
        kind: null_kind(),
        args: vec![
            QuotationTemplate::Literal(ident(
                "captured",
                1,
                vec![Preresolved::Decl {
                    name: Name::from_components(["Known", "captured"]),
                    fields: vec!["field".to_string()],
                }],
            )),
            QuotationTemplate::Antiquotation {
                hole_info: original(4, 8),
                value: QuotedSyntax::from_source(ident("caller", 40, Vec::new())),
            },
            QuotationTemplate::Splice {
                hole_info: original(9, 15),
                values: vec![
                    QuotedSyntax::from_source(Syntax::atom(original(50, 51), "a")),
                    QuotedSyntax::from_source(Syntax::atom(original(52, 53), "b")),
                ],
            },
            QuotationTemplate::GeneratedIdent {
                definition_info: original(16, 17),
                raw_val: span(16, 17),
                base: Name::from_components(["g"]),
                preresolved: Vec::new(),
                local_ordinal: 0,
            },
            QuotationTemplate::Nested {
                definition_info: original(18, 25),
                quotation_ordinal: 7,
                body: Box::new(QuotationTemplate::GeneratedIdent {
                    definition_info: original(20, 21),
                    raw_val: span(20, 21),
                    base: Name::from_components(["g"]),
                    preresolved: Vec::new(),
                    local_ordinal: 0,
                }),
            },
        ],
    }
}

#[test]
fn quotation_scopes_literals_preserves_antiquotations_flattens_splices_and_maps_every_node() {
    let expansion = complete(MacroExpansionInput {
        coordinates: coordinates(Mode::Faithful, 7),
        quotation: quotation(),
        template: full_template(),
    });
    let Syntax::Node { args, info, .. } = expansion.syntax() else {
        panic!("expected a quotation node");
    };
    assert_eq!(args.len(), 6, "the two-value splice must flatten");
    assert_eq!(
        *info,
        SourceInfo::Synthetic {
            pos: BytePos(100),
            end_pos: BytePos(120),
            canonical: true,
        }
    );

    let Syntax::Ident {
        val: literal_name,
        preresolved,
        ..
    } = &args[0]
    else {
        panic!("literal identifier");
    };
    let literal_view = extract_macro_scopes(literal_name).expect("well-formed scoped literal");
    assert_eq!(literal_view.name, Name::from_components(["captured"]));
    assert_eq!(literal_view.scopes, vec![17]);
    assert_eq!(preresolved.len(), 1, "pre-resolution survives quotation");

    let Syntax::Ident {
        val: caller_name, ..
    } = &args[1]
    else {
        panic!("antiquoted identifier");
    };
    assert_eq!(caller_name, &Name::from_components(["caller"]));
    assert!(
        !caller_name.has_macro_scopes(),
        "antiquotation is inserted as-is"
    );

    assert_eq!(
        expansion.source_map().len(),
        expansion.stats().output_nodes as usize,
        "the authoritative map is exact over every output node"
    );
    let caller_origins = expansion
        .source_map()
        .origins(&SyntaxPath::root().child(1))
        .expect("caller origin");
    assert!(
        caller_origins
            .iter()
            .any(|origin| origin.kind == OriginKind::Literal)
    );
    assert!(
        caller_origins
            .iter()
            .any(|origin| origin.kind == OriginKind::Antiquotation)
    );
    assert_eq!(caller_origins.primary_span(), Some(span(40, 46)));

    assert_eq!(expansion.generated_names().len(), 2);
    assert_ne!(
        expansion.generated_names()[0].stable,
        expansion.generated_names()[1].stable,
        "the nested quotation path is part of generated-name identity"
    );
    assert_eq!(expansion.generated_names()[1].path.quotations(), &[7]);
}

#[test]
fn an_expansion_reinserted_by_antiquotation_round_trips_without_recapture() {
    let first = complete(MacroExpansionInput {
        coordinates: coordinates(Mode::Sound, 4),
        quotation: quotation(),
        template: full_template(),
    });
    let expected_syntax = first.syntax().clone();
    let expected_names = first.generated_names().to_vec();
    let second = complete(MacroExpansionInput {
        coordinates: coordinates(Mode::Sound, 5),
        quotation: QuotationContext {
            name: Name::from_components(["Other", "context", "_hygCtx"]),
            macro_scope: 99,
            ..quotation()
        },
        template: QuotationTemplate::Antiquotation {
            hole_info: original(70, 75),
            value: first.into_quoted(),
        },
    });

    assert_eq!(second.syntax(), &expected_syntax);
    let Syntax::Node { args, .. } = second.syntax() else {
        panic!("expected node");
    };
    let Syntax::Ident { val, .. } = &args[0] else {
        panic!("expected identifier");
    };
    assert_eq!(
        extract_macro_scopes(val).expect("well formed").context,
        Name::from_components(["Main", "quotation", "_hygCtx"]),
        "the outer quotation must not re-scope antiquoted syntax"
    );
    assert_eq!(expected_names.len(), 2);
}

fn coordinate_invariant_template() -> QuotationTemplate {
    QuotationTemplate::Node {
        definition_info: original(0, 5),
        kind: null_kind(),
        args: vec![
            QuotationTemplate::Literal(Syntax::atom(original(1, 2), "x")),
            QuotationTemplate::GeneratedIdent {
                definition_info: original(2, 3),
                raw_val: span(2, 3),
                base: Name::from_components(["g"]),
                preresolved: Vec::new(),
                local_ordinal: 3,
            },
        ],
    }
}

#[test]
fn mode_and_grammar_epoch_are_bound_coordinates_but_not_timing_inputs_to_names() {
    let mut outputs = Vec::new();
    for (mode, revision) in [(Mode::Faithful, 1), (Mode::Sound, 7), (Mode::Frontier, 99)] {
        outputs.push(complete(MacroExpansionInput {
            coordinates: coordinates(mode, revision),
            quotation: quotation(),
            template: coordinate_invariant_template(),
        }));
    }

    for output in &outputs[1..] {
        assert_eq!(output.syntax(), outputs[0].syntax());
        assert_eq!(output.generated_names(), outputs[0].generated_names());
        assert_eq!(output.source_map(), outputs[0].source_map());
        assert_ne!(
            output.coordinates(),
            outputs[0].coordinates(),
            "mode/epoch remain explicit admission coordinates"
        );
    }
}

#[test]
fn malformed_forms_have_exact_typed_diagnostics_and_publish_no_syntax() {
    let unexpected = expand_quotation(
        MacroExpansionInput {
            coordinates: coordinates(Mode::Faithful, 1),
            quotation: quotation(),
            template: QuotationTemplate::Node {
                definition_info: original(0, 3),
                kind: Name::from_components(["Lean", "Parser", "Term"]),
                args: vec![QuotationTemplate::Splice {
                    hole_info: original(1, 2),
                    values: vec![QuotedSyntax::from_source(Syntax::atom(
                        original(10, 11),
                        "x",
                    ))],
                }],
            },
        },
        MacroExpansionBudget::generous(),
        None,
    );
    let path = match unexpected {
        Outcome::Complete(Err(error @ MacroExpansionError::UnexpectedSplice { .. })) => {
            assert_eq!(error.message(), "unexpected antiquotation splice");
            let MacroExpansionError::UnexpectedSplice { path } = error else {
                unreachable!("matched above");
            };
            path
        }
        other => panic!("root splice refusal must keep its class, got {other:?}"),
    };
    assert_eq!(path, SyntaxPath::root());

    let nested_unexpected = expand_quotation(
        MacroExpansionInput {
            coordinates: coordinates(Mode::Faithful, 1),
            quotation: quotation(),
            template: QuotationTemplate::Node {
                definition_info: original(0, 8),
                kind: Name::from_components(["Lean", "Parser", "Term"]),
                args: vec![
                    QuotationTemplate::Literal(Syntax::atom(original(1, 2), "head")),
                    QuotationTemplate::Node {
                        definition_info: original(3, 7),
                        kind: Name::from_components(["Lean", "Parser", "Term"]),
                        args: vec![QuotationTemplate::Splice {
                            hole_info: original(4, 6),
                            values: vec![QuotedSyntax::from_source(Syntax::atom(
                                original(10, 11),
                                "x",
                            ))],
                        }],
                    },
                ],
            },
        },
        MacroExpansionBudget::generous(),
        None,
    );
    let Outcome::Complete(Err(MacroExpansionError::UnexpectedSplice { path })) = nested_unexpected
    else {
        panic!("nested splice refusal must name the offending node, got {nested_unexpected:?}");
    };
    assert_eq!(path, SyntaxPath::root().child(1));

    let missing = expand_quotation(
        MacroExpansionInput {
            coordinates: coordinates(Mode::Faithful, 1),
            quotation: quotation(),
            template: QuotationTemplate::Literal(Syntax::Missing),
        },
        MacroExpansionBudget::generous(),
        None,
    );
    assert!(matches!(
        missing,
        Outcome::Complete(Err(MacroExpansionError::UnsupportedMissing { .. }))
    ));
}

#[test]
fn duplicate_generated_paths_are_refused_before_publication() {
    let generated = || QuotationTemplate::GeneratedIdent {
        definition_info: original(1, 2),
        raw_val: span(1, 2),
        base: Name::from_components(["x"]),
        preresolved: Vec::new(),
        local_ordinal: 0,
    };
    let outcome = expand_quotation(
        MacroExpansionInput {
            coordinates: coordinates(Mode::Sound, 1),
            quotation: quotation(),
            template: QuotationTemplate::Node {
                definition_info: original(0, 3),
                kind: null_kind(),
                args: vec![generated(), generated()],
            },
        },
        MacroExpansionBudget::generous(),
        None,
    );
    assert!(matches!(
        outcome,
        Outcome::Complete(Err(MacroExpansionError::DuplicateGeneratedPath { .. }))
    ));
}

#[test]
fn generated_name_shape_is_retained_in_the_output_identifier() {
    let expansion = complete(MacroExpansionInput {
        coordinates: coordinates(Mode::Sound, 1),
        quotation: quotation(),
        template: coordinate_invariant_template(),
    });
    let generated: &GeneratedName = &expansion.generated_names()[0];
    let Syntax::Node { args, .. } = expansion.syntax() else {
        panic!("node");
    };
    let Syntax::Ident { val, .. } = &args[1] else {
        panic!("generated identifier");
    };
    assert_eq!(val, &generated.hygienic);
    assert_eq!(
        extract_macro_scopes(val).expect("well formed").name,
        generated.stable
    );
}
