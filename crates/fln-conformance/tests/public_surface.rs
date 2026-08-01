//! Independent consumer and model checks for `PublicSurfaceContractV1`.

#![forbid(unsafe_code)]

use fln_conformance::public_surface::{
    CONTRACT_DOCUMENT, CONTRACT_SCHEMA, CONTRACT_TEXT, EvidenceBundle, ProcessOutcome,
    PublicSurfaceContract, PublicationDisposition, PublicationPhase, PublicationState,
    SemanticDisposition, SemanticRecord, TelemetryRecord, classify_outcome,
    publish_with_interruption, recover_publication, reduce_productively,
};

fn fnv(bytes: &[u8]) -> String {
    let mut value = 0xcbf29ce484222325_u64;
    for byte in bytes {
        value ^= u64::from(*byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{value:016x}")
}

fn framed_hash<'a>(domain: &'a str, fields: impl IntoIterator<Item = &'a str>) -> String {
    let mut payload = Vec::new();
    for field in std::iter::once(domain).chain(fields) {
        payload.extend_from_slice(&(field.len() as u64).to_le_bytes());
        payload.extend_from_slice(field.as_bytes());
    }
    fnv(&payload)
}

fn reseal(text: &str) -> String {
    let mut lines = text.lines().map(str::to_string).collect::<Vec<_>>();
    let root_index = lines
        .iter()
        .position(|line| line.starts_with("contract-root "))
        .expect("contract root row");
    assert_eq!(root_index + 1, lines.len(), "root remains the final row");
    let root = framed_hash(
        CONTRACT_SCHEMA,
        lines[..root_index].iter().map(String::as_str),
    );
    lines[root_index] = format!("contract-root {root}");
    lines.join("\n") + "\n"
}

fn replace_once(text: &str, before: &str, after: &str) -> String {
    assert_eq!(
        text.matches(before).count(),
        1,
        "test replacement must select one cell"
    );
    text.replacen(before, after, 1)
}

fn semantic_record(disposition: SemanticDisposition) -> SemanticRecord {
    let inconclusive = matches!(
        disposition,
        SemanticDisposition::Inconclusive | SemanticDisposition::InternalFault
    );
    SemanticRecord {
        run_id: "public-surface-test-run".to_string(),
        sequence: 0,
        domain: "option".to_string(),
        row: "Lean.Parser.maxRecDepth".to_string(),
        epoch: "v4.32.0@8c9756b28d64dab099da31a4c09229a9e6a2ef35".to_string(),
        platform: "linux-x86_64".to_string(),
        client: "lean".to_string(),
        profile: "faithful,sound".to_string(),
        mode: "all".to_string(),
        fixture: "option-census-no-mock".to_string(),
        comparison: "exact".to_string(),
        authority: "pinned-reference-binary".to_string(),
        input_root: "fnv1a64:1ca89a9168d51641".to_string(),
        output_root: if inconclusive {
            "none".to_string()
        } else {
            "fnv1a64:3075944236a50690".to_string()
        },
        expected: "ok".to_string(),
        actual: "ok λ".to_string(),
        resource_class: "bounded-process".to_string(),
        resource_used: 1,
        disposition,
        decision: if inconclusive {
            "no-promotion".to_string()
        } else {
            "record".to_string()
        },
        cleanup: "complete".to_string(),
        final_state: "reaped".to_string(),
    }
}

fn telemetry_record() -> TelemetryRecord {
    TelemetryRecord {
        run_id: "public-surface-test-run".to_string(),
        sequence: 0,
        host: "test-host".to_string(),
        pid: 7,
        worker: 0,
        elapsed_micros: 11,
        path: "/pinned/lean".to_string(),
        cache: "cold".to_string(),
        detail: "test-only operational detail".to_string(),
    }
}

#[test]
fn public_surface_schema_join() {
    let contract =
        PublicSurfaceContract::load_embedded().expect("the canonical joined contract is valid");
    assert_eq!(contract.domains.len(), 3);
    assert_eq!(contract.surfaces.len(), 1_010);
    assert_eq!(contract.fixtures.len(), 40);
    assert_eq!(
        contract
            .domains
            .iter()
            .map(|domain| (domain.name.as_str(), domain.row_count))
            .collect::<Vec<_>>(),
        [("cli-lake", 291), ("lsp", 59), ("option", 660)]
    );
    assert_eq!(
        contract
            .fixtures
            .iter()
            .filter(|fixture| fixture.domain == "cli-lake")
            .count(),
        25
    );
    assert_eq!(
        contract
            .fixtures
            .iter()
            .filter(|fixture| fixture.domain == "lsp")
            .count(),
        8
    );
    assert_eq!(
        contract
            .fixtures
            .iter()
            .filter(|fixture| fixture.domain == "option")
            .count(),
        7
    );
    assert!(contract.surface("cli-lake", "command:lake:build").is_some());
    assert!(
        contract
            .surface("lsp", "request:textDocument/hover")
            .is_some()
    );
    assert!(
        contract
            .surface("option", "builtin_option:maxRecDepth")
            .is_some()
    );
    assert!(
        contract
            .surfaces
            .iter()
            .all(|row| row.epoch == "v4.32.0@8c9756b28d64dab099da31a4c09229a9e6a2ef35")
    );

    let one = reduce_productively(&contract, 1).expect("one-worker reduction");
    let eight = reduce_productively(&contract, 8).expect("eight-worker reduction");
    let thirty_two = reduce_productively(&contract, 32).expect("thirty-two-worker reduction");
    let thirty_one = reduce_productively(&contract, 31).expect("non-divisor worker reduction");
    assert_eq!(one.semantic_root, eight.semantic_root);
    assert_eq!(one.semantic_root, thirty_two.semantic_root);
    assert_eq!(one.semantic_root, thirty_one.semantic_root);
    for evidence in [&one, &eight, &thirty_one, &thirty_two] {
        assert_eq!(evidence.completed_per_worker.len(), evidence.workers);
        assert_eq!(
            evidence.completed_per_worker.iter().sum::<usize>(),
            contract.surfaces.len()
        );
        assert!(
            evidence
                .completed_per_worker
                .iter()
                .all(|completed| *completed > 0)
        );
    }
    reduce_productively(&contract, 0).expect_err("a zero-worker label is not productive");
    reduce_productively(&contract, contract.surfaces.len() + 1)
        .expect_err("more workers than rows necessarily admits an idle worker");
}

#[test]
fn generated_consumer_compile() {
    let contract = PublicSurfaceContract::parse(CONTRACT_TEXT)
        .expect("canonical text parses")
        .validate_generated_projection()
        .expect("generated Rust and Markdown bind every canonical population");
    assert_eq!(
        CONTRACT_DOCUMENT.matches(&contract.contract_root).count(),
        1
    );
    assert_eq!(
        contract
            .projections
            .iter()
            .map(|projection| projection.kind.as_str())
            .collect::<Vec<_>>(),
        ["markdown", "rust"]
    );

    let changed_source = reseal(&replace_once(
        CONTRACT_TEXT,
        "source=vendor/lean4-src/src/lake/Lake/CLI/Main.lean:1260",
        "source=vendor/lean4-src/src/lake/Lake/CLI/Main.lean:1261",
    ));
    PublicSurfaceContract::parse(&changed_source)
        .expect("the independently resealed text remains structurally valid")
        .validate_generated_projection()
        .expect_err("generated consumers cannot silently retain an older contract root");
}

#[test]
fn public_surface_drift_model() {
    let corrupted_root = replace_once(
        CONTRACT_TEXT,
        "contract-root fnv1a64:90a8cf467a6d7718",
        "contract-root fnv1a64:0000000000000000",
    );
    PublicSurfaceContract::parse(&corrupted_root).expect_err("root drift must be refused");

    let policy_folded_into_facts = reseal(&replace_once(
        CONTRACT_TEXT,
        "raw-policy-separation required",
        "raw-policy-separation merged",
    ));
    PublicSurfaceContract::parse(&policy_folded_into_facts)
        .expect_err("raw facts and reviewed policy must remain distinct");

    let changed_authority = reseal(&CONTRACT_TEXT.replacen(
        "authority=native-target support=required effect=channel:n/a%3Bprecedence:first-positional",
        "authority=inherited support=required effect=channel:n/a%3Bprecedence:first-positional",
        1,
    ));
    PublicSurfaceContract::parse(&changed_authority)
        .expect("the independently resealed policy-shaped row parses")
        .validate_domain_inputs()
        .expect_err("the join must be reconstructed from the canonical domain inputs");

    let first_surface = CONTRACT_TEXT
        .lines()
        .find(|line| line.starts_with("surface "))
        .expect("first surface");
    let omitted = CONTRACT_TEXT
        .lines()
        .filter(|line| *line != first_surface)
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    let omitted = reseal(&omitted.replace("surface-count 1010", "surface-count 1009"));
    PublicSurfaceContract::parse(&omitted)
        .expect_err("the anti-vacuity population rejects a shortened census");

    let second_surface = CONTRACT_TEXT
        .lines()
        .filter(|line| line.starts_with("surface "))
        .nth(1)
        .expect("second surface");
    let duplicated = reseal(&replace_once(CONTRACT_TEXT, second_surface, first_surface));
    PublicSurfaceContract::parse(&duplicated)
        .expect_err("the joined census rejects a duplicate domain-row identity");

    let first_fixture = CONTRACT_TEXT
        .lines()
        .find(|line| line.starts_with("fixture "))
        .expect("first fixture");
    let fixture_omitted = CONTRACT_TEXT
        .lines()
        .filter(|line| *line != first_fixture)
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    let fixture_omitted = reseal(&fixture_omitted.replace("fixture-count 40", "fixture-count 39"));
    PublicSurfaceContract::parse(&fixture_omitted)
        .expect_err("the anti-vacuity population rejects a missing fixture binding");

    let noncanonical_escape = reseal(&replace_once(
        CONTRACT_TEXT,
        "platform=portable-schema%2Blinux-x86_64-oracle",
        "platform=portable-schema%2blinux-x86_64-oracle",
    ));
    PublicSurfaceContract::parse(&noncanonical_escape)
        .expect_err("alternate percent-escape spelling is not a canonical contract");
}

#[test]
fn atomic_contract_publication() {
    let old = PublicationState::complete("fnv1a64:1111111111111111");
    let candidate = "fnv1a64:c46e47f4b7a8bb4c";
    for phase in [
        PublicationPhase::CandidatesValidated,
        PublicationPhase::RustProjection,
        PublicationPhase::MarkdownProjection,
        PublicationPhase::CanonicalContract,
    ] {
        let (interrupted, disposition) = publish_with_interruption(&old, candidate, Some(phase));
        assert_eq!(
            disposition,
            PublicationDisposition::Inconclusive {
                interrupted_after: phase
            }
        );
        match phase {
            PublicationPhase::CandidatesValidated => {
                assert_eq!(interrupted.authoritative_root(), old.authoritative_root());
            }
            PublicationPhase::RustProjection | PublicationPhase::MarkdownProjection => {
                assert_eq!(
                    interrupted.authoritative_root(),
                    None,
                    "a mixed projection set has no authoritative root"
                );
            }
            PublicationPhase::CanonicalContract => {
                assert_eq!(interrupted.authoritative_root(), Some(candidate));
            }
        }
        assert_eq!(
            recover_publication(&interrupted, candidate).expect("reachable prefix recovers"),
            PublicationState::complete(candidate)
        );
    }
    let (published, disposition) = publish_with_interruption(&old, candidate, None);
    assert_eq!(disposition, PublicationDisposition::Complete);
    assert_eq!(published.authoritative_root(), Some(candidate));
    assert_eq!(
        recover_publication(&published, candidate).expect("complete candidate is idempotent"),
        published
    );

    let three_roots = PublicationState {
        canonical_root: "fnv1a64:1111111111111111".to_string(),
        rust_projection_root: candidate.to_string(),
        markdown_projection_root: "fnv1a64:2222222222222222".to_string(),
    };
    recover_publication(&three_roots, candidate)
        .expect_err("recovery refuses a state containing two unrelated prior roots");
    let reversed = PublicationState {
        canonical_root: candidate.to_string(),
        rust_projection_root: "fnv1a64:1111111111111111".to_string(),
        markdown_projection_root: "fnv1a64:1111111111111111".to_string(),
    };
    recover_publication(&reversed, candidate)
        .expect_err("recovery refuses a state outside the projections-first prefix order");
    recover_publication(&old, "not-a-root")
        .expect_err("recovery refuses an unsealed candidate root");
}

#[test]
fn cross_domain_epoch_platform_model() {
    let mixed_epoch = reseal(&CONTRACT_TEXT.replacen(
        "epoch=v4.32.0%408c9756b28d64dab099da31a4c09229a9e6a2ef35",
        "epoch=v4.31.0%408c9756b28d64dab099da31a4c09229a9e6a2ef35",
        1,
    ));
    PublicSurfaceContract::parse(&mixed_epoch)
        .expect_err("one domain row cannot carry a different Reference epoch");

    let mixed_platform = reseal(&replace_once(
        CONTRACT_TEXT,
        "platform=portable-schema%2Blinux-x86_64-oracle",
        "platform=darwin-aarch64",
    ));
    PublicSurfaceContract::parse(&mixed_platform)
        .expect_err("an unreviewed domain platform cannot enter the join");

    let moved_reference = CONTRACT_TEXT
        .replace("tag=v4.32.0 commit=", "tag=v4.32.1 commit=")
        .replace("epoch=v4.32.0%40", "epoch=v4.32.1%40");
    PublicSurfaceContract::parse(&reseal(&moved_reference))
        .expect("a coherently shaped but different epoch remains parseable")
        .validate_domain_inputs()
        .expect_err("domain inputs remain pinned to the suite Reference identity");

    let moved_domain_version = reseal(&replace_once(
        CONTRACT_TEXT,
        "schema=fln-cli-lake-inventory/1",
        "schema=fln-cli-lake-inventory/2",
    ));
    PublicSurfaceContract::parse(&moved_domain_version)
        .expect("a structurally valid domain-version change remains parseable")
        .validate_domain_inputs()
        .expect_err("the domain schema version remains bound to its canonical producer");
}

#[test]
fn semantic_evidence_is_strict_and_telemetry_is_separate() {
    assert_eq!(
        classify_outcome(ProcessOutcome::Observed),
        SemanticDisposition::Accepted
    );
    assert_eq!(
        classify_outcome(ProcessOutcome::Mismatch),
        SemanticDisposition::Rejected
    );
    for outcome in [
        ProcessOutcome::Cancelled,
        ProcessOutcome::TimedOut,
        ProcessOutcome::OutputBudgetExceeded,
    ] {
        assert_eq!(classify_outcome(outcome), SemanticDisposition::Inconclusive);
    }
    assert_eq!(
        classify_outcome(ProcessOutcome::InternalFault),
        SemanticDisposition::InternalFault
    );

    let bundle = EvidenceBundle::new(
        vec![semantic_record(SemanticDisposition::Accepted)],
        vec![telemetry_record()],
    )
    .expect("semantic and operational streams are valid separately");
    let semantic = bundle.semantic_ndjson();
    let telemetry = bundle.telemetry_ndjson();
    assert!(!semantic.contains("\"host\":"));
    assert!(!semantic.contains("\"elapsed_micros\":"));
    assert!(!telemetry.contains("\"decision\":"));
    assert_ne!(bundle.semantic_root(), bundle.telemetry_root());
    let round_trip =
        EvidenceBundle::from_ndjson(&semantic, &telemetry).expect("strict NDJSON round trip");
    assert_eq!(round_trip.semantic_root(), bundle.semantic_root());
    assert_eq!(round_trip.telemetry_root(), bundle.telemetry_root());

    let extra_field = semantic.replacen("}\n", ",\"unreviewed_semantic_field\":\"value\"}\n", 1);
    EvidenceBundle::from_ndjson(&extra_field, &telemetry)
        .expect_err("unknown semantic fields must fail closed");

    let reordered = semantic.replacen(
        "{\"schema\":\"fln.public-surface.semantic/1\",\"run_id\":\"public-surface-test-run\"",
        "{\"run_id\":\"public-surface-test-run\",\"schema\":\"fln.public-surface.semantic/1\"",
        1,
    );
    EvidenceBundle::from_ndjson(&reordered, &telemetry)
        .expect_err("parse-equivalent field reordering is not canonical evidence");
    let leading_zero = semantic.replacen("\"sequence\":0", "\"sequence\":00", 1);
    EvidenceBundle::from_ndjson(&leading_zero, &telemetry)
        .expect_err("parse-equivalent integer spelling is not canonical evidence");
    let escaped_unicode = semantic.replacen('λ', "\\u03bb", 1);
    EvidenceBundle::from_ndjson(&escaped_unicode, &telemetry)
        .expect_err("parse-equivalent Unicode escaping is not canonical evidence");

    let mut missing_telemetry = telemetry_record();
    missing_telemetry.host.clear();
    EvidenceBundle::new(
        vec![semantic_record(SemanticDisposition::Accepted)],
        vec![missing_telemetry],
    )
    .expect_err("telemetry rows require every structural string field");

    let mut authorityless = semantic_record(SemanticDisposition::Accepted);
    authorityless.authority.clear();
    EvidenceBundle::new(vec![authorityless], vec![telemetry_record()])
        .expect_err("semantic rows require every structural string field");
    let mut rootless = semantic_record(SemanticDisposition::Accepted);
    rootless.output_root = "none".to_string();
    EvidenceBundle::new(vec![rootless], vec![telemetry_record()])
        .expect_err("conclusive evidence requires a sealed output root");

    let mut semantic_with_schema_words = semantic_record(SemanticDisposition::Accepted);
    semantic_with_schema_words.actual =
        "diagnostic mentions normalized \"path\" and \"host\" field names".to_string();
    EvidenceBundle::new(vec![semantic_with_schema_words], vec![telemetry_record()])
        .expect("semantic text may mention words that are telemetry only when top-level fields");

    let second_semantic = SemanticRecord {
        sequence: 1,
        ..semantic_record(SemanticDisposition::Accepted)
    };
    EvidenceBundle::new(
        vec![
            semantic_record(SemanticDisposition::Accepted),
            second_semantic,
        ],
        vec![telemetry_record()],
    )
    .expect_err("stream linkage requires one telemetry sequence for each semantic sequence");

    let inconclusive = EvidenceBundle::new(
        vec![semantic_record(SemanticDisposition::Inconclusive)],
        vec![telemetry_record()],
    )
    .expect("typed inconclusive evidence remains recordable");
    assert!(
        inconclusive
            .semantic_ndjson()
            .contains("\"decision\":\"no-promotion\"")
    );
}
