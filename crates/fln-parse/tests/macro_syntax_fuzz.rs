//! Deterministic grammar-adjacent fuzzing for the production quotation expander.

#![forbid(unsafe_code)]

use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::domain::Digest;
use fln_parse::macro_expand::{
    HygienePolicy, MacroExpansionBudget, MacroExpansionCheckpoint, MacroExpansionCoordinates,
    MacroExpansionInput, QuotationContext, QuotationTemplate, QuotedSyntax, expand_quotation,
};
use fln_parse::registry::GrammarEpoch;
use fln_parse::state::null_kind;
use fln_syntax::hygiene::{ExpansionOrigin, ExpansionPath, extract_macro_scopes};
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};
use fln_syntax::tree::Syntax;
use std::process::Command;

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(BytePos(start), BytePos(end)).expect("forward span")
}

fn info(seed: u64) -> SourceInfo {
    let start = (seed as usize) % 400;
    SourceInfo::Synthetic {
        pos: BytePos(start),
        end_pos: BytePos(start + 1),
        canonical: seed.is_multiple_of(2),
    }
}

fn input(seed: u64) -> MacroExpansionInput {
    let mut args = Vec::new();
    for index in 0..(seed % 7 + 1) {
        let point = seed.wrapping_mul(17).wrapping_add(index);
        match point % 5 {
            0 => args.push(QuotationTemplate::Literal(Syntax::atom(
                info(point),
                format!("a{point}"),
            ))),
            1 => args.push(QuotationTemplate::Literal(Syntax::Ident {
                info: info(point),
                raw_val: span((point % 400) as usize, (point % 400) as usize + 1),
                val: Name::from_components([format!("i{point}").as_str()]),
                preresolved: Vec::new(),
            })),
            2 => args.push(QuotationTemplate::Antiquotation {
                hole_info: info(point),
                value: QuotedSyntax::from_source(Syntax::atom(info(point + 1), "anti")),
            }),
            3 => args.push(QuotationTemplate::Splice {
                hole_info: info(point),
                values: (0..point % 3)
                    .map(|ordinal| {
                        QuotedSyntax::from_source(Syntax::atom(
                            info(point + ordinal),
                            format!("s{point}_{ordinal}"),
                        ))
                    })
                    .collect(),
            }),
            _ => args.push(QuotationTemplate::GeneratedIdent {
                definition_info: info(point),
                raw_val: span((point % 400) as usize, (point % 400) as usize + 1),
                base: Name::from_components(["g"]),
                preresolved: Vec::new(),
                local_ordinal: index,
            }),
        }
    }
    args.push(QuotationTemplate::Nested {
        definition_info: info(seed + 900),
        quotation_ordinal: seed % 11,
        body: Box::new(QuotationTemplate::GeneratedIdent {
            definition_info: info(seed + 901),
            raw_val: span(0, 0),
            base: Name::from_components(["nested"]),
            preresolved: Vec::new(),
            local_ordinal: 1_000 + seed,
        }),
    });

    MacroExpansionInput {
        coordinates: MacroExpansionCoordinates {
            grammar_epoch: GrammarEpoch::from_parts(seed, Digest([seed as u8; 32])),
            mode: match seed % 3 {
                0 => Mode::Faithful,
                1 => Mode::Sound,
                _ => Mode::Frontier,
            },
            expansion_path: ExpansionPath::root(
                ExpansionOrigin::new(Name::from_components(["Fuzz", "Macro"]), seed / 9),
                seed % 9,
            ),
        },
        quotation: QuotationContext {
            name: Name::from_components(["Fuzz", "context", "_hygCtx"]),
            macro_scope: seed + 1,
            call_site: Some(span(500, 510)),
            canonical: true,
            hygiene: if seed.is_multiple_of(4) {
                HygienePolicy::Disabled
            } else {
                HygienePolicy::Enabled
            },
        },
        template: QuotationTemplate::Node {
            definition_info: info(seed),
            kind: null_kind(),
            args,
        },
    }
}

#[test]
fn generated_macro_syntax_corpus_is_total_productive_and_source_map_complete() {
    let mut completed = 0usize;
    let mut generated = 0usize;
    for seed in 0..512 {
        let outcome = expand_quotation(input(seed), MacroExpansionBudget::generous(), None);
        let expansion = match outcome {
            Outcome::Complete(Ok(expansion)) => expansion,
            other => panic!("seed {seed} did not complete: {other:?}"),
        };
        completed += 1;
        generated += expansion.generated_names().len();
        assert_eq!(
            expansion.source_map().len(),
            expansion.stats().output_nodes as usize,
            "seed {seed} produced a partial source map"
        );
        for generated_name in expansion.generated_names() {
            if seed.is_multiple_of(4) {
                assert_eq!(generated_name.hygienic, generated_name.stable);
            } else {
                assert_eq!(
                    extract_macro_scopes(&generated_name.hygienic)
                        .expect("generated scope is well formed")
                        .name,
                    generated_name.stable
                );
            }
        }
    }
    assert_eq!(completed, 512);
    assert!(generated > 0, "the generated-name lane must be productive");
}

#[test]
fn an_exact_budget_is_invisible_and_each_one_less_boundary_is_inconclusive() {
    let baseline = match expand_quotation(input(73), MacroExpansionBudget::generous(), None) {
        Outcome::Complete(Ok(expansion)) => expansion,
        other => panic!("baseline failed: {other:?}"),
    };
    let exact_budget = MacroExpansionBudget {
        max_visited_nodes: baseline.stats().visited_nodes,
        max_output_nodes: baseline.stats().output_nodes,
        max_generated_names: baseline.generated_names().len() as u64,
    };
    let exact = expand_quotation(input(73), exact_budget, None);
    let exact = match exact {
        Outcome::Complete(Ok(expansion)) => expansion,
        other => panic!("exact boundary must complete: {other:?}"),
    };
    assert_eq!(exact.syntax(), baseline.syntax());
    assert_eq!(exact.generated_names(), baseline.generated_names());
    assert_eq!(exact.source_map(), baseline.source_map());

    for budget in [
        MacroExpansionBudget {
            max_visited_nodes: exact_budget.max_visited_nodes - 1,
            ..exact_budget
        },
        MacroExpansionBudget {
            max_output_nodes: exact_budget.max_output_nodes - 1,
            ..exact_budget
        },
        MacroExpansionBudget {
            max_generated_names: exact_budget.max_generated_names - 1,
            ..exact_budget
        },
    ] {
        assert!(matches!(
            expand_quotation(input(73), budget, None),
            Outcome::Inconclusive(_)
        ));
    }
}

#[test]
fn cancellation_at_every_observed_visit_and_before_publication_is_nonpublication() {
    let baseline = match expand_quotation(input(29), MacroExpansionBudget::generous(), None) {
        Outcome::Complete(Ok(expansion)) => expansion,
        other => panic!("baseline failed: {other:?}"),
    };
    for stop_at in 0..baseline.stats().visited_nodes {
        let outcome = expand_quotation(
            input(29),
            MacroExpansionBudget::generous(),
            Some(&|checkpoint| match checkpoint {
                MacroExpansionCheckpoint::BeforeTemplateNode { visited }
                | MacroExpansionCheckpoint::BeforeSyntaxNode { visited } => visited == stop_at,
                MacroExpansionCheckpoint::BeforePublication { .. } => false,
            }),
        );
        assert!(
            matches!(outcome, Outcome::Inconclusive(_)),
            "visit cancellation {stop_at} published or rejected"
        );
    }
    let final_stop = expand_quotation(
        input(29),
        MacroExpansionBudget::generous(),
        Some(&|checkpoint| {
            matches!(
                checkpoint,
                MacroExpansionCheckpoint::BeforePublication { .. }
            )
        }),
    );
    assert!(matches!(final_stop, Outcome::Inconclusive(_)));
}

#[test]
fn malformed_splice_then_exact_repair_recovers_without_residue() {
    let bad = expand_quotation(
        MacroExpansionInput {
            template: QuotationTemplate::Node {
                definition_info: info(1),
                kind: Name::from_components(["Lean", "Parser", "Term"]),
                args: vec![QuotationTemplate::Splice {
                    hole_info: info(2),
                    values: vec![QuotedSyntax::from_source(Syntax::atom(info(3), "x"))],
                }],
            },
            ..input(1)
        },
        MacroExpansionBudget::generous(),
        None,
    );
    assert!(matches!(bad, Outcome::Complete(Err(_))));

    let repaired = expand_quotation(
        MacroExpansionInput {
            template: QuotationTemplate::Node {
                definition_info: info(1),
                kind: null_kind(),
                args: vec![QuotationTemplate::Splice {
                    hole_info: info(2),
                    values: vec![QuotedSyntax::from_source(Syntax::atom(info(3), "x"))],
                }],
            },
            ..input(1)
        },
        MacroExpansionBudget::generous(),
        None,
    );
    let Outcome::Complete(Ok(repaired)) = repaired else {
        panic!("the exact repair must complete");
    };
    assert_eq!(
        repaired.source_map().len(),
        repaired.stats().output_nodes as usize
    );
}

#[test]
fn arbitrary_hygiene_like_name_shapes_always_return_a_typed_answer() {
    for seed in 0..2_000u64 {
        let mut candidate = Name::from_components(["x"]);
        for step in 0..seed % 9 {
            candidate = match (seed + step) % 4 {
                0 => Name::str(candidate, "_@"),
                1 => Name::str(candidate, "_hyg"),
                2 => Name::num(candidate, seed ^ step),
                _ => Name::str(candidate, format!("c{step}")),
            };
        }
        let _typed_answer = extract_macro_scopes(&candidate);
    }
}

#[test]
fn deep_cancelled_quotation_cleanup_fits_on_a_small_thread_stack() {
    const CHILD: &str = "FLN_MACRO_DEEP_CANCEL_CHILD";
    if std::env::var_os(CHILD).is_some() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut template =
                    QuotationTemplate::Literal(Syntax::atom(SourceInfo::None, "leaf"));
                for ordinal in 0..50_000 {
                    template = QuotationTemplate::Nested {
                        definition_info: SourceInfo::None,
                        quotation_ordinal: ordinal,
                        body: Box::new(template),
                    };
                }
                let outcome = expand_quotation(
                    MacroExpansionInput {
                        template,
                        ..input(1)
                    },
                    MacroExpansionBudget::generous(),
                    Some(&|checkpoint| {
                        matches!(
                            checkpoint,
                            MacroExpansionCheckpoint::BeforeTemplateNode { visited: 0 }
                        )
                    }),
                );
                assert!(matches!(outcome, Outcome::Inconclusive(_)));
            })
            .expect("small-stack thread starts")
            .join()
            .expect("deep cancelled quotation cleans up iteratively");
        return;
    }

    let result = Command::new(std::env::current_exe().expect("current test binary"))
        .arg("--exact")
        .arg("deep_cancelled_quotation_cleanup_fits_on_a_small_thread_stack")
        .arg("--nocapture")
        .env(CHILD, "1")
        .status()
        .expect("child test process runs");
    assert!(result.success(), "small-stack child failed: {result}");
}
