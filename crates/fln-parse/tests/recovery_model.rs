#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_parse::category::LeadingIdentBehavior;
use fln_parse::recovery::{
    IncrementalRecoveryRequest, IncrementalRestartReason, NormalizedRecoveryEdit,
    PublicationRefusal, RecoveryBudget, RecoveryCatalog, RecoveryCatalogError, RecoveryCheckpoint,
    RecoveryError, RecoveryMode, RecoverySession, RecoverySpec, RecoverySpecError,
    ResynchronizationToken, SpeculativeObservation, VerifiedIncrementalRecovery, command_category,
    nat_definition_recovery_spec, parse_nat_definition_recovering, pinned_parser_categories,
    reparse_nat_definition_incremental,
};
use fln_parse::registry::Registry;
use fln_parse::{NatDefinitionExpectation, NatDefinitionParseError, parse_nat_definition};
use fln_syntax::run::LexBudget;
use fln_syntax::source::{BytePos, ByteSpan, SourceError};

fn completed(
    outcome: Outcome<Result<RecoverySession, RecoveryError>>,
) -> Result<RecoverySession, RecoveryError> {
    match outcome {
        Outcome::Complete(result) => result,
        Outcome::Inconclusive(stop) => panic!("unexpected inconclusive outcome: {stop:?}"),
        Outcome::InternalFault(fault) => panic!("unexpected internal fault: {fault:?}"),
    }
}

fn session(source: &[u8], mode: RecoveryMode) -> RecoverySession {
    completed(parse_nat_definition_recovering(
        source,
        7,
        &Registry::new(),
        &nat_definition_recovery_spec(),
        mode,
        RecoveryBudget::generous(),
        None,
    ))
    .expect("the command recovery category matches")
}

fn incremental_completed(
    outcome: Outcome<Result<VerifiedIncrementalRecovery, RecoveryError>>,
) -> Result<VerifiedIncrementalRecovery, RecoveryError> {
    match outcome {
        Outcome::Complete(result) => result,
        Outcome::Inconclusive(stop) => panic!("unexpected inconclusive outcome: {stop:?}"),
        Outcome::InternalFault(fault) => panic!("unexpected internal fault: {fault:?}"),
    }
}

fn incremental_request<'a>(
    edit: NormalizedRecoveryEdit,
    registry: &'a Registry,
    spec: &'a RecoverySpec,
) -> IncrementalRecoveryRequest<'a> {
    IncrementalRecoveryRequest {
        edit,
        registry,
        spec,
        mode: RecoveryMode::Enabled,
        budget: RecoveryBudget::generous(),
        cancellation: None,
    }
}

#[test]
fn recovery_mode_cannot_change_the_authoritative_acceptance_result() {
    for source in [
        b"def answer := 42".as_slice(),
        b"def broken :=".as_slice(),
        b"theorem answer := 42".as_slice(),
        b"def one := 1\ndef two := 2".as_slice(),
        &[0xff],
    ] {
        let disabled = session(source, RecoveryMode::Disabled);
        let enabled = session(source, RecoveryMode::Enabled);
        assert_eq!(
            disabled.authoritative().result(),
            enabled.authoritative().result()
        );
        assert_eq!(
            enabled.authoritative().result(),
            &parse_nat_definition(source)
        );
    }
}

#[test]
fn malformed_commands_are_marked_and_both_boundary_products_are_journaled() {
    let source = b"def broken :=\ndef good := 2";
    let recovered = session(source, RecoveryMode::Enabled);

    assert!(!recovered.authoritative().accepted());
    assert!(recovered.authoritative().boundaries().is_empty());
    let speculative = recovered.speculative().expect("recovery was enabled");
    assert_eq!(speculative.boundaries().len(), 2);
    assert!(matches!(
        speculative.boundaries()[0].observation(),
        SpeculativeObservation::RejectedCommandShape(_)
    ));
    assert_eq!(
        speculative.boundaries()[1].observation(),
        &SpeculativeObservation::AcceptedCommandShape
    );
    assert_eq!(recovered.recovered().len(), 1);
    assert!(recovered.recovered()[0].is_epoch_bound());
    assert_eq!(
        recovered.recovered()[0].marker().category(),
        &command_category()
    );

    let entry = recovered.journal().first().expect("disagreement recorded");
    assert!(entry.authoritative().is_empty());
    assert_eq!(entry.speculative(), speculative.boundaries());
    assert_eq!(
        entry.disagreement_span(),
        ByteSpan::new(BytePos(0), BytePos(source.len())).expect("ordered")
    );
    assert_eq!(
        entry.markers(),
        &[recovered.recovered()[0].marker().clone()]
    );
}

#[test]
fn later_command_refusals_name_file_bytes_not_the_slice() {
    // First command is well-formed. A slice-local diagnostic for the second
    // command sits around byte 12 and would land inside `def good := 2`.
    let source = b"def good := 2\ndef broken : String := 1";
    let recovered = session(source, RecoveryMode::Enabled);
    let speculative = recovered.speculative().expect("recovery was enabled");
    assert_eq!(speculative.boundaries().len(), 2);
    assert_eq!(
        speculative.boundaries()[0].observation(),
        &SpeculativeObservation::AcceptedCommandShape
    );
    let SpeculativeObservation::RejectedCommandShape(NatDefinitionParseError::OutsideSeedGrammar {
        at,
        expected: NatDefinitionExpectation::NaturalType,
    }) = speculative.boundaries()[1].observation()
    else {
        panic!(
            "the second command must be a type-ascription refusal, got {:?}",
            speculative.boundaries()[1].observation()
        );
    };
    assert_eq!(*at, BytePos(27));
    assert!(source[at.0..].starts_with(b"String"));

    let crlf = b"def good := 2\r\ndef broken : String := 1";
    let recovered = session(crlf, RecoveryMode::Enabled);
    let speculative = recovered.speculative().expect("recovery was enabled");
    let SpeculativeObservation::RejectedCommandShape(NatDefinitionParseError::OutsideSeedGrammar {
        at,
        ..
    }) = speculative.boundaries()[1].observation()
    else {
        panic!("CRLF later-command refusal must keep its parse class");
    };
    assert_eq!(*at, BytePos(28));
    assert_eq!(crlf[at.0], b'S');
}

#[test]
fn invalid_utf8_is_authoritatively_rejected_and_never_repaired() {
    let recovered = session(&[0xff], RecoveryMode::Enabled);
    assert!(matches!(
        recovered.authoritative().result(),
        Err(NatDefinitionParseError::Source(SourceError::NotUtf8 {
            at: BytePos(0)
        }))
    ));
    assert!(recovered.source_view().is_none());
    assert!(recovered.lexical_run().is_none());
    assert!(recovered.speculative().is_none());
    assert!(recovered.recovered().is_empty());
    assert!(recovered.journal().is_empty());
}

#[test]
fn every_recovery_category_requires_an_explicit_nonempty_unique_specification() {
    assert_eq!(
        RecoverySpec::new(
            Name::anonymous(),
            Name::from_components(["marker"]),
            vec![ResynchronizationToken::Symbol("def".to_string())],
        ),
        Err(RecoverySpecError::AnonymousCategory)
    );
    assert_eq!(
        RecoverySpec::new(
            command_category(),
            Name::from_components(["marker"]),
            Vec::new(),
        ),
        Err(RecoverySpecError::EmptyResynchronizationSet)
    );
    let duplicate = ResynchronizationToken::Symbol("def".to_string());
    assert_eq!(
        RecoverySpec::new(
            command_category(),
            Name::from_components(["marker"]),
            vec![duplicate.clone(), duplicate.clone()],
        ),
        Err(RecoverySpecError::DuplicateResynchronizationToken(
            duplicate
        ))
    );

    let term = RecoverySpec::new(
        Name::from_components(["Lean", "Parser", "Term"]),
        Name::from_components(["Lean", "Parser", "Term", "recovered"]),
        vec![ResynchronizationToken::Identifier(Name::from_components([
            "fun",
        ]))],
    )
    .expect("a term-specific contract is structurally valid");
    assert!(matches!(
        completed(parse_nat_definition_recovering(
            b"def answer := 42",
            1,
            &Registry::new(),
            &term,
            RecoveryMode::Enabled,
            RecoveryBudget::generous(),
            None,
        )),
        Err(RecoveryError::CategoryMismatch { .. })
    ));
}

#[test]
fn the_recovery_catalog_is_exact_over_the_generated_pinned_category_inventory() {
    let categories = pinned_parser_categories().expect("the governed inventory is well formed");
    assert_eq!(
        categories.len(),
        35,
        "anti-shrink floor for the pinned epoch"
    );
    assert!(categories.contains(&command_category()));
    let specification_for = |category: &Name| {
        RecoverySpec::new(
            category.clone(),
            Name::str(
                Name::from_components(["Lean", "Parser", "Recovery"]),
                category.to_display_string(),
            ),
            vec![ResynchronizationToken::Symbol(";".to_string())],
        )
        .expect("inventory categories and marker kinds are named")
    };
    let specifications = categories.iter().map(specification_for).collect::<Vec<_>>();
    let catalog = RecoveryCatalog::for_pinned_categories(specifications.clone())
        .expect("one explicit policy per inventory category");
    assert_eq!(catalog.len(), categories.len());
    assert_eq!(catalog.categories().count(), categories.len());
    assert!(catalog.get(&command_category()).is_some());
    assert!(
        catalog
            .get(&Name::from_components(["not", "a", "category"]))
            .is_none(),
        "there is no fallback recovery policy"
    );

    let mut missing = specifications.clone();
    let omitted = missing
        .pop()
        .expect("inventory is nonempty")
        .category()
        .clone();
    assert_eq!(
        RecoveryCatalog::for_pinned_categories(missing),
        Err(RecoveryCatalogError::MissingSpecifications(vec![omitted]))
    );

    let mut duplicate = specifications.clone();
    duplicate.push(specifications[0].clone());
    assert!(matches!(
        RecoveryCatalog::for_pinned_categories(duplicate),
        Err(RecoveryCatalogError::DuplicateSpecification(_))
    ));

    let mut unexpected = specifications;
    unexpected.push(
        RecoverySpec::new(
            Name::from_components(["not", "a", "category"]),
            Name::from_components(["Lean", "Parser", "Recovery", "unexpected"]),
            vec![ResynchronizationToken::Symbol(";".to_string())],
        )
        .expect("named synthetic policy"),
    );
    assert!(matches!(
        RecoveryCatalog::for_pinned_categories(unexpected),
        Err(RecoveryCatalogError::UnexpectedSpecifications(_))
    ));
}

#[test]
fn only_a_current_exact_accepted_product_yields_a_publication_capability() {
    let mut registry = Registry::new();
    let exact_epoch = registry.epoch();
    let accepted = completed(parse_nat_definition_recovering(
        b"def answer := 42",
        11,
        &registry,
        &nat_definition_recovery_spec(),
        RecoveryMode::Enabled,
        RecoveryBudget::generous(),
        None,
    ))
    .expect("matching category");

    let candidate = accepted
        .publication_candidate(11, exact_epoch)
        .expect("exact accepted product is publishable");
    assert_eq!(candidate.generation(), 11);
    assert_eq!(candidate.epoch(), exact_epoch);
    assert_eq!(
        candidate.parsed().reconstruct_original(),
        b"def answer := 42"
    );
    assert!(matches!(
        accepted.publication_candidate(12, exact_epoch),
        Err(PublicationRefusal::StaleGeneration {
            session: 11,
            expected: 12
        })
    ));

    registry
        .declare_category(
            Name::from_components(["Later"]),
            LeadingIdentBehavior::Default,
        )
        .expect("new category advances the grammar");
    assert!(matches!(
        accepted.publication_candidate(11, registry.epoch()),
        Err(PublicationRefusal::EpochMismatch { .. })
    ));

    let rejected = session(b"def broken :=", RecoveryMode::Enabled);
    assert!(matches!(
        rejected.publication_candidate(7, Registry::new().epoch()),
        Err(PublicationRefusal::AuthoritativeRejected)
    ));
}

#[test]
fn cancellation_and_resource_exhaustion_are_non_answers_with_no_session() {
    let cancelled_at_publication =
        |checkpoint| matches!(checkpoint, RecoveryCheckpoint::BeforePublication { .. });
    assert!(matches!(
        parse_nat_definition_recovering(
            b"def answer := 42",
            1,
            &Registry::new(),
            &nat_definition_recovery_spec(),
            RecoveryMode::Enabled,
            RecoveryBudget::generous(),
            Some(&cancelled_at_publication),
        ),
        Outcome::Inconclusive(_)
    ));

    let budget = RecoveryBudget {
        lex: LexBudget {
            max_input_bytes: 0,
            max_events: 100,
        },
        ..RecoveryBudget::generous()
    };
    assert!(matches!(
        parse_nat_definition_recovering(
            b"def answer := 42",
            1,
            &Registry::new(),
            &nat_definition_recovery_spec(),
            RecoveryMode::Enabled,
            budget,
            None,
        ),
        Outcome::Inconclusive(_)
    ));
}

#[test]
fn crlf_normalization_keeps_recovery_spans_in_the_declared_view_coordinates() {
    let source = b"def broken :=\r\ndef good := 2";
    let recovered = session(source, RecoveryMode::Enabled);
    let view = recovered.source_view().expect("valid source");
    assert_eq!(view.removed_count(), 1);
    assert_eq!(
        recovered.journal()[0].disagreement_span().end(),
        BytePos(view.normalized().len_bytes())
    );
    assert_eq!(
        recovered
            .recovered()
            .first()
            .expect("one repaired command")
            .marker()
            .epoch(),
        recovered.speculative().expect("enabled").boundaries()[0].epoch()
    );
}

#[test]
fn recovery_products_are_schedule_independent_across_the_thread_matrix() {
    let source = b"def broken :=\ndef good := 2".to_vec();
    let mut products = Vec::new();
    for threads in [1usize, 8, 32] {
        let mut handles = Vec::new();
        for _ in 0..threads {
            let source = source.clone();
            handles.push(std::thread::spawn(move || {
                session(&source, RecoveryMode::Enabled)
            }));
        }
        products.push(
            handles
                .into_iter()
                .map(|handle| handle.join().expect("worker did not panic"))
                .collect::<Vec<_>>(),
        );
    }
    let expected = &products[0][0];
    assert!(products.iter().flatten().all(|product| product == expected));
}

#[test]
fn an_incremental_edit_matches_full_recovery_and_reuses_the_untouched_prefix() {
    let registry = Registry::new();
    let spec = nat_definition_recovery_spec();
    let old_source = b"def one := 1\ndef two := 2";
    let new_source = b"def one := 1\ndef two := 20";
    let previous = completed(parse_nat_definition_recovering(
        old_source,
        20,
        &registry,
        &spec,
        RecoveryMode::Enabled,
        RecoveryBudget::generous(),
        None,
    ))
    .expect("matching category");
    let numeral = old_source.len() - 1;
    let edit = NormalizedRecoveryEdit {
        base_generation: 20,
        next_generation: 21,
        base_registry_epoch: registry.epoch(),
        replaced: ByteSpan::new(BytePos(numeral), BytePos(numeral + 1)).expect("ordered"),
        inserted_len: 2,
    };

    let incremental = incremental_completed(reparse_nat_definition_incremental(
        &previous,
        new_source,
        incremental_request(edit, &registry, &spec),
    ))
    .expect("exact edit");
    let full = completed(parse_nat_definition_recovering(
        new_source,
        21,
        &registry,
        &spec,
        RecoveryMode::Enabled,
        RecoveryBudget::generous(),
        None,
    ))
    .expect("matching category");

    assert_eq!(incremental.session(), &full);
    assert!(incremental.lexical_damage().reused_anything());
    assert_eq!(incremental.boundary_damage().reused_prefix, 1);
    assert_eq!(incremental.boundary_damage().reparsed, 1);
    assert_eq!(incremental.boundary_damage().total_boundaries(), 2);
}

#[test]
fn repairing_a_malformed_command_changes_only_the_exact_parsers_own_verdict() {
    let registry = Registry::new();
    let spec = nat_definition_recovery_spec();
    let old_source = b"def answer :=";
    let new_source = b"def answer := 42";
    let previous = completed(parse_nat_definition_recovering(
        old_source,
        30,
        &registry,
        &spec,
        RecoveryMode::Enabled,
        RecoveryBudget::generous(),
        None,
    ))
    .expect("matching category");
    assert!(!previous.authoritative().accepted());

    let incremental = incremental_completed(reparse_nat_definition_incremental(
        &previous,
        new_source,
        incremental_request(
            NormalizedRecoveryEdit {
                base_generation: 30,
                next_generation: 31,
                base_registry_epoch: registry.epoch(),
                replaced: ByteSpan::empty_at(BytePos(old_source.len())),
                inserted_len: 3,
            },
            &registry,
            &spec,
        ),
    ))
    .expect("exact insertion");

    assert!(incremental.session().authoritative().accepted());
    assert!(incremental.session().recovered().is_empty());
    assert!(
        incremental
            .session()
            .publication_candidate(31, registry.epoch())
            .is_ok()
    );
}

#[test]
fn stale_generation_epoch_and_inexact_edit_metadata_are_refused_before_publication() {
    let mut original_registry = Registry::new();
    original_registry
        .declare_category(
            Name::from_components(["Original"]),
            LeadingIdentBehavior::Default,
        )
        .expect("advance original grammar");
    let spec = nat_definition_recovery_spec();
    let source = b"def answer := 42";
    let previous = completed(parse_nat_definition_recovering(
        source,
        40,
        &original_registry,
        &spec,
        RecoveryMode::Enabled,
        RecoveryBudget::generous(),
        None,
    ))
    .expect("matching category");
    let unchanged = NormalizedRecoveryEdit {
        base_generation: 40,
        next_generation: 41,
        base_registry_epoch: original_registry.epoch(),
        replaced: ByteSpan::empty_at(BytePos(source.len())),
        inserted_len: 0,
    };

    assert!(matches!(
        incremental_completed(reparse_nat_definition_incremental(
            &previous,
            source,
            incremental_request(
                NormalizedRecoveryEdit {
                    base_generation: 39,
                    ..unchanged
                },
                &original_registry,
                &spec,
            ),
        )),
        Err(RecoveryError::StaleBaseGeneration { .. })
    ));
    assert!(matches!(
        incremental_completed(reparse_nat_definition_incremental(
            &previous,
            source,
            incremental_request(
                NormalizedRecoveryEdit {
                    next_generation: 40,
                    ..unchanged
                },
                &original_registry,
                &spec,
            ),
        )),
        Err(RecoveryError::NonMonotonicGeneration { .. })
    ));
    assert!(matches!(
        incremental_completed(reparse_nat_definition_incremental(
            &previous,
            source,
            incremental_request(
                NormalizedRecoveryEdit {
                    base_registry_epoch: Registry::new().epoch(),
                    ..unchanged
                },
                &original_registry,
                &spec,
            ),
        )),
        Err(RecoveryError::StaleGrammarEpoch { .. })
    ));

    let mut foreign_registry = Registry::new();
    foreign_registry
        .declare_category(
            Name::from_components(["Foreign"]),
            LeadingIdentBehavior::Default,
        )
        .expect("advance a different grammar");
    assert!(matches!(
        incremental_completed(reparse_nat_definition_incremental(
            &previous,
            source,
            incremental_request(unchanged, &foreign_registry, &spec),
        )),
        Err(RecoveryError::ForeignGrammarEpoch { .. })
    ));

    assert!(matches!(
        incremental_completed(reparse_nat_definition_incremental(
            &previous,
            b"def changed := 42",
            incremental_request(unchanged, &original_registry, &spec),
        )),
        Err(RecoveryError::InvalidNormalizedEdit { .. })
    ));
}

#[test]
fn invalid_utf8_requires_a_full_restart_instead_of_an_incremental_repair() {
    let registry = Registry::new();
    let spec = nat_definition_recovery_spec();
    let source = b"def answer := 42";
    let previous = completed(parse_nat_definition_recovering(
        source,
        50,
        &registry,
        &spec,
        RecoveryMode::Enabled,
        RecoveryBudget::generous(),
        None,
    ))
    .expect("matching category");
    assert!(matches!(
        incremental_completed(reparse_nat_definition_incremental(
            &previous,
            &[0xff],
            incremental_request(
                NormalizedRecoveryEdit {
                    base_generation: 50,
                    next_generation: 51,
                    base_registry_epoch: registry.epoch(),
                    replaced: ByteSpan::new(BytePos(0), BytePos(source.len())).expect("ordered"),
                    inserted_len: 1,
                },
                &registry,
                &spec,
            ),
        )),
        Err(RecoveryError::IncrementalRestartRequired(
            IncrementalRestartReason::NewSourceIsNotUtf8
        ))
    ));
}

#[test]
fn accepted_speculative_suffixes_never_become_publishable_declarations() {
    let recovered = session(b"def one := 1\ndef two := 2", RecoveryMode::Enabled);
    let speculative = recovered.speculative().expect("enabled");
    assert_eq!(speculative.boundaries().len(), 2);
    assert!(speculative.boundaries().iter().all(|boundary| {
        boundary.observation() == &SpeculativeObservation::AcceptedCommandShape
    }));
    assert!(
        recovered.recovered().is_empty(),
        "a boundary disagreement must not invent a repaired syntax node"
    );
    assert!(matches!(
        recovered.publication_candidate(7, Registry::new().epoch()),
        Err(PublicationRefusal::AuthoritativeRejected)
    ));
}

#[test]
fn every_small_ascii_edit_is_incrementally_equivalent_to_a_full_session() {
    let registry = Registry::new();
    let spec = nat_definition_recovery_spec();
    let seeds = [
        b"def a := 1".as_slice(),
        b"def broken :=".as_slice(),
        b"theorem a := 1".as_slice(),
        b"def one := 1\ndef two := 2".as_slice(),
    ];

    for mode in [RecoveryMode::Disabled, RecoveryMode::Enabled] {
        for seed in seeds {
            let previous = completed(parse_nat_definition_recovering(
                seed,
                100,
                &registry,
                &spec,
                mode,
                RecoveryBudget::generous(),
                None,
            ))
            .expect("matching category");
            for at in 0..=seed.len() {
                let mut replacements = vec![
                    (0usize, b"x".as_slice()),
                    (0usize, b"def".as_slice()),
                    (0usize, b"\n".as_slice()),
                ];
                if at < seed.len() {
                    replacements.push((1, b"".as_slice()));
                    replacements.push((1, b"2".as_slice()));
                }
                for (removed, inserted) in replacements {
                    let mut edited = Vec::with_capacity(seed.len() - removed + inserted.len());
                    edited.extend_from_slice(&seed[..at]);
                    edited.extend_from_slice(inserted);
                    edited.extend_from_slice(&seed[at + removed..]);
                    let edit = NormalizedRecoveryEdit {
                        base_generation: 100,
                        next_generation: 101,
                        base_registry_epoch: registry.epoch(),
                        replaced: ByteSpan::new(BytePos(at), BytePos(at + removed))
                            .expect("ordered edit"),
                        inserted_len: inserted.len(),
                    };
                    let incremental = incremental_completed(reparse_nat_definition_incremental(
                        &previous,
                        &edited,
                        IncrementalRecoveryRequest {
                            edit,
                            registry: &registry,
                            spec: &spec,
                            mode,
                            budget: RecoveryBudget::generous(),
                            cancellation: None,
                        },
                    ))
                    .expect("the generated edit metadata is exact");
                    let full = completed(parse_nat_definition_recovering(
                        &edited,
                        101,
                        &registry,
                        &spec,
                        mode,
                        RecoveryBudget::generous(),
                        None,
                    ))
                    .expect("matching category");
                    assert_eq!(
                        incremental.session(),
                        &full,
                        "mode={mode:?}, seed={seed:?}, at={at}, removed={removed}, \
                         inserted={inserted:?}"
                    );
                    assert_eq!(
                        incremental.lexical_damage().total_events(),
                        incremental
                            .session()
                            .lexical_run()
                            .expect("ASCII input has a run")
                            .events
                            .len()
                    );
                    let boundary_count = incremental
                        .session()
                        .speculative()
                        .map_or(0, |map| map.boundaries().len());
                    assert_eq!(
                        incremental.boundary_damage().total_boundaries(),
                        boundary_count
                    );
                }
            }
        }
    }
}
