//! Real public-API no-mock macro-hygiene evidence driver.

#![forbid(unsafe_code)]

use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::{CacheAdmission, Outcome};
use fln_hash::domain::{Digest, Domain, hash};
use fln_parse::macro_expand::{
    HygienePolicy, MacroExpansion, MacroExpansionBudget, MacroExpansionCheckpoint,
    MacroExpansionCoordinates, MacroExpansionError, MacroExpansionInput, QuotationContext,
    QuotationTemplate, QuotedSyntax, expand_quotation,
};
use fln_parse::registry::GrammarEpoch;
use fln_parse::state::null_kind;
use fln_syntax::hygiene::{ExpansionOrigin, ExpansionPath, add_macro_scope, extract_macro_scopes};
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};
use fln_syntax::tree::Syntax;
use std::fmt::Write as _;
use std::path::Path;

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(BytePos(start), BytePos(end)).expect("forward span")
}

fn info(start: usize, end: usize) -> SourceInfo {
    SourceInfo::Synthetic {
        pos: BytePos(start),
        end_pos: BytePos(end),
        canonical: true,
    }
}

fn coordinates() -> MacroExpansionCoordinates {
    MacroExpansionCoordinates {
        grammar_epoch: GrammarEpoch::from_parts(12, Digest([0x12; 32])),
        mode: Mode::Faithful,
        expansion_path: ExpansionPath::root(
            ExpansionOrigin::new(Name::from_components(["Main", "NoMock"]), 4),
            3,
        ),
    }
}

fn quotation() -> QuotationContext {
    QuotationContext {
        name: Name::from_components(["Main", "noMock", "_hygCtx"]),
        macro_scope: 23,
        call_site: Some(span(200, 220)),
        canonical: true,
        hygiene: HygienePolicy::Enabled,
    }
}

fn positive_template() -> QuotationTemplate {
    QuotationTemplate::Node {
        definition_info: info(0, 30),
        kind: null_kind(),
        args: vec![
            QuotationTemplate::Literal(Syntax::Ident {
                info: info(1, 2),
                raw_val: span(1, 2),
                val: Name::from_components(["literal"]),
                preresolved: Vec::new(),
            }),
            QuotationTemplate::Antiquotation {
                hole_info: info(3, 4),
                value: QuotedSyntax::from_source(Syntax::Ident {
                    info: info(80, 86),
                    raw_val: span(80, 86),
                    val: Name::from_components(["caller"]),
                    preresolved: Vec::new(),
                }),
            },
            QuotationTemplate::Splice {
                hole_info: info(5, 8),
                values: vec![
                    QuotedSyntax::from_source(Syntax::atom(info(90, 91), "a")),
                    QuotedSyntax::from_source(Syntax::atom(info(92, 93), "b")),
                ],
            },
            QuotationTemplate::GeneratedIdent {
                definition_info: info(10, 11),
                raw_val: span(10, 11),
                base: Name::from_components(["generated"]),
                preresolved: Vec::new(),
                local_ordinal: 0,
            },
            QuotationTemplate::Nested {
                definition_info: info(12, 18),
                quotation_ordinal: 9,
                body: Box::new(QuotationTemplate::GeneratedIdent {
                    definition_info: info(14, 15),
                    raw_val: span(14, 15),
                    base: Name::from_components(["generated"]),
                    preresolved: Vec::new(),
                    local_ordinal: 0,
                }),
            },
        ],
    }
}

fn positive_input() -> MacroExpansionInput {
    MacroExpansionInput {
        coordinates: coordinates(),
        quotation: quotation(),
        template: positive_template(),
    }
}

fn complete(input: MacroExpansionInput) -> MacroExpansion {
    match expand_quotation(input, MacroExpansionBudget::generous(), None) {
        Outcome::Complete(Ok(expansion)) => expansion,
        other => panic!("expected completed production expansion, got {other:?}"),
    }
}

fn expansion_root(expansion: &MacroExpansion) -> String {
    let mut canonical = format!("{:?};", expansion.syntax());
    canonical.push_str(&expansion.source_map().canonical());
    for generated in expansion.generated_names() {
        canonical.push_str(&generated.path.canonical());
        canonical.push_str(&generated.stable.to_display_string());
        canonical.push(';');
        canonical.push_str(&generated.hygienic.to_display_string());
        canonical.push(';');
    }
    write!(
        canonical,
        "visited={};output={};",
        expansion.stats().visited_nodes,
        expansion.stats().output_nodes
    )
    .expect("writing into a String cannot fail");
    hash(Domain::Fixture, canonical.as_bytes()).to_hex()
}

fn scope_overlap() -> String {
    let plain = Name::from_components(["x"]);
    let first_context = Name::from_components(["Main", "command17", "_hygCtx"]);
    let second_context = Name::from_components(["Imported", "command4", "_hygCtx"]);
    let first = add_macro_scope(&first_context, &plain, 1).expect("first scope");
    let second = add_macro_scope(&first_context, &first, 8).expect("second scope");
    add_macro_scope(&second_context, &second, 3)
        .expect("context transition")
        .to_display_string()
}

fn json_text(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for scalar in value.chars() {
        match scalar {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            scalar if scalar.is_control() => {
                write!(out, "\\u{:04x}", scalar as u32).expect("writing into a String cannot fail");
            }
            scalar => out.push(scalar),
        }
    }
    out.push('"');
    out
}

fn write_evidence(artifact_dir: &Path, semantic_rows: &[String], run_id: &str, thread_root: &str) {
    let mut semantic = semantic_rows.join("\n");
    semantic.push('\n');
    std::fs::write(artifact_dir.join("semantic.ndjson"), semantic)
        .expect("semantic evidence path is writable");

    let telemetry = format!(
        concat!(
            "{{\"schema\":\"fln.e2e.hygiene-telemetry/1\",",
            "\"run_id\":{},\"thread_counts\":[1,8,32],",
            "\"productive_expansions\":41,\"thread_root\":{}}}\n"
        ),
        json_text(run_id),
        json_text(thread_root),
    );
    std::fs::write(artifact_dir.join("telemetry.ndjson"), telemetry)
        .expect("telemetry evidence path is writable");
}

#[test]
fn hygiene_no_mock_e2e() {
    let positive = complete(positive_input());
    let positive_root = expansion_root(&positive);
    let Syntax::Node { args, .. } = positive.syntax() else {
        panic!("positive expansion must be a node");
    };
    let Syntax::Ident {
        val: literal_name, ..
    } = &args[0]
    else {
        panic!("literal identifier");
    };
    let literal_view = extract_macro_scopes(literal_name).expect("literal scope is well formed");
    assert_eq!(literal_view.name, Name::from_components(["literal"]));
    let Syntax::Ident {
        val: caller_name, ..
    } = &args[1]
    else {
        panic!("caller identifier");
    };
    assert_eq!(caller_name, &Name::from_components(["caller"]));

    let failure = expand_quotation(
        MacroExpansionInput {
            coordinates: coordinates(),
            quotation: quotation(),
            template: QuotationTemplate::Node {
                definition_info: info(0, 4),
                kind: Name::from_components(["Lean", "Parser", "Term"]),
                args: vec![QuotationTemplate::Splice {
                    hole_info: info(1, 2),
                    values: vec![QuotedSyntax::from_source(Syntax::atom(info(50, 51), "x"))],
                }],
            },
        },
        MacroExpansionBudget::generous(),
        None,
    );
    let failure_message = match failure {
        Outcome::Complete(Err(error @ MacroExpansionError::UnexpectedSplice { .. })) => {
            error.message()
        }
        other => panic!("unexpected-splice path was not a typed refusal: {other:?}"),
    };

    let recovery = complete(MacroExpansionInput {
        coordinates: coordinates(),
        quotation: quotation(),
        template: QuotationTemplate::Node {
            definition_info: info(0, 4),
            kind: null_kind(),
            args: vec![QuotationTemplate::Splice {
                hole_info: info(1, 2),
                values: vec![QuotedSyntax::from_source(Syntax::atom(info(50, 51), "x"))],
            }],
        },
    });
    let recovery_root = expansion_root(&recovery);

    let cancelled = expand_quotation(
        positive_input(),
        MacroExpansionBudget::generous(),
        Some(&|checkpoint| {
            matches!(
                checkpoint,
                MacroExpansionCheckpoint::BeforePublication { .. }
            )
        }),
    );
    assert!(matches!(cancelled, Outcome::Inconclusive(_)));
    assert!(matches!(
        cancelled.cache_admission(),
        CacheAdmission::Refused { .. }
    ));

    let resource = expand_quotation(
        positive_input(),
        MacroExpansionBudget {
            max_output_nodes: 1,
            ..MacroExpansionBudget::generous()
        },
        None,
    );
    assert!(matches!(resource, Outcome::Inconclusive(_)));
    assert!(matches!(
        resource.cache_admission(),
        CacheAdmission::Refused { .. }
    ));

    let mut thread_roots = Vec::new();
    for worker_count in [1usize, 8, 32] {
        let handles = (0..worker_count)
            .map(|_| std::thread::spawn(|| expansion_root(&complete(positive_input()))))
            .collect::<Vec<_>>();
        let roots = handles
            .into_iter()
            .map(|handle| handle.join().expect("worker completes"))
            .collect::<Vec<_>>();
        assert!(!roots.is_empty());
        assert!(roots.iter().all(|root| root == &roots[0]));
        thread_roots.push(roots[0].clone());
    }
    assert!(thread_roots.iter().all(|root| root == &thread_roots[0]));
    let thread_root = thread_roots[0].clone();

    let semantic_rows = vec![
        format!(
            concat!(
                "{{\"schema\":\"fln.e2e.hygiene-semantic/1\",\"sequence\":0,",
                "\"scenario\":\"positive\",\"status\":\"accepted\",",
                "\"semantic_root\":{},\"scope_overlap\":{},",
                "\"generated_names\":2,\"output_nodes\":7,\"published\":true}}"
            ),
            json_text(&positive_root),
            json_text(&scope_overlap()),
        ),
        format!(
            concat!(
                "{{\"schema\":\"fln.e2e.hygiene-semantic/1\",\"sequence\":1,",
                "\"scenario\":\"failure\",\"status\":\"rejected\",",
                "\"diagnostic\":{},\"published\":false}}"
            ),
            json_text(failure_message),
        ),
        format!(
            concat!(
                "{{\"schema\":\"fln.e2e.hygiene-semantic/1\",\"sequence\":2,",
                "\"scenario\":\"recovery\",\"status\":\"accepted\",",
                "\"semantic_root\":{},\"published\":true}}"
            ),
            json_text(&recovery_root),
        ),
        concat!(
            "{\"schema\":\"fln.e2e.hygiene-semantic/1\",\"sequence\":3,",
            "\"scenario\":\"cancellation\",\"status\":\"inconclusive\",",
            "\"published\":false}"
        )
        .to_string(),
        concat!(
            "{\"schema\":\"fln.e2e.hygiene-semantic/1\",\"sequence\":4,",
            "\"scenario\":\"resource\",\"status\":\"inconclusive\",",
            "\"published\":false}"
        )
        .to_string(),
        format!(
            concat!(
                "{{\"schema\":\"fln.e2e.hygiene-semantic/1\",\"sequence\":5,",
                "\"scenario\":\"thread_matrix\",\"status\":\"accepted\",",
                "\"thread_counts\":[1,8,32],\"productive_expansions\":41,",
                "\"semantic_root\":{},\"published\":true}}"
            ),
            json_text(&thread_root),
        ),
    ];

    if let Some(artifact_dir) = std::env::var_os("FLN_HYGIENE_E2E_ART_DIR") {
        let artifact_dir = Path::new(&artifact_dir);
        assert!(
            artifact_dir.is_dir(),
            "artifact directory must already exist"
        );
        let run_id =
            std::env::var("FLN_HYGIENE_E2E_RUN_ID").expect("run id accompanies artifact path");
        write_evidence(artifact_dir, &semantic_rows, &run_id, &thread_root);
    }

    println!(
        "hygiene-no-mock status=pass semantic_root={} thread_root={} scope_overlap={}",
        positive_root,
        thread_root,
        scope_overlap()
    );
}
