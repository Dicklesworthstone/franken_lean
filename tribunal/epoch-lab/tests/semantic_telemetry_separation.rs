//! Suite `semantic_telemetry_separation` (bead `fln-euo`, the epic's ninth
//! named suite; the eighth, `reference_reference_no_mock_e2e`, is its sibling
//! remainder).
//!
//! # The law under test
//!
//! Canonical semantic evidence excludes timestamps, durations, process ids,
//! absolute paths, scheduler/allocator/performance facts — those live in
//! BOUNDED telemetry LINKED to the semantic root and never inside it. Fixed
//! semantic inputs run productively at 1/8/32 where safely parallel, with
//! nonempty partitions and deterministic reduction; intrinsically serial
//! steps stay ordered and are not relabeled parallel.
//!
//! # The two failure directions, both priced
//!
//! Every telemetry class has a REFUSAL cell (the leak direction — the fact
//! reaches the root and roots stop being comparable across hosts) AND an
//! ADMISSION cell for its nearest legitimate neighbour (the wall direction —
//! a detector so eager it refuses honest semantic facts, which is how a
//! separation law gets deleted as friction a month later). A suite that
//! priced only one direction would be the thing it tests for.

#![forbid(unsafe_code)]

use fln_epoch_lab::telemetry::{
    ExecutionClaim, MAX_TELEMETRY_ENTRIES, SemanticEvidence, SeparationError, StepKind, Telemetry,
    TelemetryClass, reduction_root, validate_execution,
};

fn admitted(pairs: &[(&str, &str)]) -> SemanticEvidence {
    let mut e = SemanticEvidence::new();
    for (k, v) in pairs {
        e.admit(k, v)
            .unwrap_or_else(|err| panic!("{k:?}={v:?} must admit: {err}"));
    }
    e
}

fn inputs(names: &[&str]) -> Vec<String> {
    names.iter().map(|s| s.to_string()).collect()
}

// ---------------------------------------------------------------------------
// Admission: the leak direction and the wall direction, class by class
// ---------------------------------------------------------------------------

#[test]
fn a_clean_semantic_record_admits_and_its_root_is_stable() {
    let e = admitted(&[
        ("module", "Init.Prelude"),
        ("verdict", "accepted"),
        ("decl_count", "1755"),
        ("fixture", "tribunal/fixtures/c3/Init.olean"),
        (
            "digest",
            "4e33c82df2e20d84213aa60211b48ad2d5c28c6522d259714f84bb90127243a6",
        ),
    ]);
    let first = e.semantic_root().expect("nonempty evidence has a root");
    let second = e.semantic_root().expect("still has a root");
    assert_eq!(first, second, "the root is a function of the facts");
    assert_eq!(first.len(), 64, "the root is a full digest");
}

#[test]
fn every_telemetry_class_is_refused_from_semantic_evidence_naming_its_class() {
    // The semantic/telemetry MIXING mutant, one cell per class, each required
    // to fail FOR THE INTENDED REASON — the named class — not merely to fail.
    let cells: &[(&str, &str, TelemetryClass)] = &[
        // Key-announced classes.
        ("started_at", "run-a", TelemetryClass::Timestamp),
        ("wall_ms", "300", TelemetryClass::Duration),
        ("pid", "41272", TelemetryClass::ProcessId),
        ("cpu_affinity", "0-3", TelemetryClass::Scheduler),
        ("heap_bytes", "1048576", TelemetryClass::Allocator),
        ("throughput", "high", TelemetryClass::Performance),
        // Value-shape classes.
        (
            "note",
            "compared at 2026-07-28T23:59:00Z exactly",
            TelemetryClass::Timestamp,
        ),
        ("note", "1785270000", TelemetryClass::Timestamp),
        ("note", "took 300ms overall", TelemetryClass::Duration),
        (
            "source",
            "/home/ubuntu/.elan/toolchains/lean4",
            TelemetryClass::AbsolutePath,
        ),
    ];
    for (key, value, want) in cells {
        let mut e = SemanticEvidence::new();
        match e.admit(key, value) {
            Err(SeparationError::TelemetryKeyInSemantic { class, .. })
            | Err(SeparationError::TelemetryValueInSemantic { class, .. }) => {
                assert_eq!(
                    class, *want,
                    "{key:?}={value:?} refused under the wrong class"
                );
            }
            other => panic!("{key:?}={value:?} must be refused as {want:?}, got {other:?}"),
        }
        assert!(e.is_empty(), "a refused fact must not be admitted anyway");
    }
}

#[test]
fn the_nearest_legitimate_neighbour_of_each_detector_still_admits() {
    // The WALL direction. Each value here sits as close to a detector as an
    // honest semantic fact gets; a detector that eats one of these is refusing
    // correct practice and must be narrowed, not obeyed.
    admitted(&[
        // Repo-relative path: the host-independence doctrine's own good case.
        ("fixture", "tribunal/fixtures/c3/Init.olean"),
        // 64-hex digest: long, digit-rich, not a timestamp (not all digits).
        (
            "digest",
            "878d10592357efc15a939258154bbeb89d9d5d0c5691bd8793450fa8ce691e92",
        ),
        // Nine digits: the largest all-digit width the timestamp detector
        // deliberately leaves alone.
        ("object_count", "956240600"[..9].as_ref()),
        // Digit-led token with a non-unit suffix.
        ("codec", "sha256s"),
        // A lone slash is division, not a host path.
        ("ratio", "1744 / 1755"),
        // Version-shaped, dash-separated, no 'T' boundary.
        ("pin", "leanprover/lean4:v4.32.0"),
    ]);
}

#[test]
fn an_empty_record_has_no_root() {
    // A constant root over nothing would read as cross-run agreement about
    // nothing — the vacuous-green shape, refused at the type's own door.
    let e = SemanticEvidence::new();
    match e.semantic_root() {
        Err(SeparationError::EmptySemanticEvidence) => {}
        other => panic!("an empty record must have no root, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Telemetry: linked, bounded, and inert with respect to the root
// ---------------------------------------------------------------------------

#[test]
fn telemetry_never_moves_the_semantic_root() {
    // The observable form of the whole law: identical semantics under wildly
    // different host circumstances produce byte-identical roots.
    let quiet = admitted(&[("module", "Init.Prelude"), ("verdict", "accepted")]);
    let loud = admitted(&[("module", "Init.Prelude"), ("verdict", "accepted")]);

    let no_telemetry = Telemetry::attach(&quiet, vec![]).expect("empty envelope attaches");
    let heavy = Telemetry::attach(
        &loud,
        vec![
            (
                TelemetryClass::Timestamp,
                "started_at".into(),
                "2026-07-28T23:59:00Z".into(),
            ),
            (TelemetryClass::Duration, "wall_ms".into(), "1926656".into()),
            (TelemetryClass::ProcessId, "pid".into(), "41272".into()),
            (
                TelemetryClass::AbsolutePath,
                "target".into(),
                "/data/tmp/x".into(),
            ),
            (TelemetryClass::Allocator, "rss".into(), "1073741824".into()),
        ],
    )
    .expect("a bounded envelope attaches");

    assert_eq!(
        no_telemetry.semantic_root(),
        heavy.semantic_root(),
        "telemetry moved the semantic root; the separation is broken"
    );
}

#[test]
fn telemetry_is_linked_by_construction_and_bounded_by_refusal() {
    let e = admitted(&[("module", "Init.Prelude"), ("verdict", "accepted")]);
    let root = e.semantic_root().expect("root");

    let t = Telemetry::attach(
        &e,
        vec![(TelemetryClass::Duration, "wall_ms".into(), "3".into())],
    )
    .expect("attaches");
    assert_eq!(t.semantic_root(), root, "the link carries the exact root");

    // Over budget by entry count: refused, never truncated.
    let too_many: Vec<_> = (0..=MAX_TELEMETRY_ENTRIES)
        .map(|i| {
            (
                TelemetryClass::Performance,
                format!("k{i}"),
                "v".to_string(),
            )
        })
        .collect();
    match Telemetry::attach(&e, too_many) {
        Err(SeparationError::TelemetryOverBudget {
            entries,
            max_entries,
            ..
        }) => {
            assert!(entries > max_entries);
        }
        other => panic!("an over-budget envelope must refuse, got {other:?}"),
    }

    // Over budget by bytes: same refusal, the other bound.
    let huge = vec![(
        TelemetryClass::Performance,
        "k".to_string(),
        "v".repeat(70_000),
    )];
    assert!(matches!(
        Telemetry::attach(&e, huge),
        Err(SeparationError::TelemetryOverBudget { .. })
    ));

    // And telemetry on evidence with no root is unrepresentable.
    let empty = SemanticEvidence::new();
    assert!(matches!(
        Telemetry::attach(&empty, vec![]),
        Err(SeparationError::EmptySemanticEvidence)
    ));
}

// ---------------------------------------------------------------------------
// Execution claims: productive widths, deterministic reduction, no fake labels
// ---------------------------------------------------------------------------

#[test]
fn partitions_at_1_8_and_32_reduce_to_the_same_root() {
    // Deterministic reduction as a digest property: any partitioning of the
    // same fixed inputs, at any width, reduces identically — including widths
    // partitioned differently on purpose.
    let names: Vec<String> = (0..64).map(|i| format!("decl{i:02}")).collect();

    let mut roots = Vec::new();
    for width in [1usize, 8, 32] {
        // Round-robin partitioning...
        let mut parts: Vec<Vec<String>> = vec![Vec::new(); width];
        for (i, n) in names.iter().enumerate() {
            parts[i % width].push(n.clone());
        }
        let claim = ExecutionClaim::Parallel {
            width: width as u32,
            partitions: parts,
        };
        validate_execution("replay", StepKind::SafelyParallel, &claim, &names)
            .expect("a productive partition validates");
        roots.push(reduction_root(&claim));

        // ...and contiguous-chunk partitioning of the same inputs.
        let chunk = names.len().div_ceil(width);
        let parts2: Vec<Vec<String>> = names.chunks(chunk).map(<[String]>::to_vec).collect();
        if parts2.len() == width {
            let claim2 = ExecutionClaim::Parallel {
                width: width as u32,
                partitions: parts2,
            };
            validate_execution("replay", StepKind::SafelyParallel, &claim2, &names)
                .expect("chunked partition validates");
            roots.push(reduction_root(&claim2));
        }
    }
    assert!(
        roots.windows(2).all(|w| w[0] == w[1]),
        "reduction is schedule-dependent: {roots:?}"
    );
}

#[test]
fn a_fake_thread_label_is_refused() {
    // Width 8 claimed, one worker did everything, seven did nothing: the
    // "parallel" label is decoration. Both fake shapes — empty partitions and
    // a partition count that is not the width — must fail as FakeThreadLabel.
    let names = inputs(&["a", "b", "c"]);

    let mut padded: Vec<Vec<String>> = vec![names.clone()];
    padded.extend(std::iter::repeat_n(Vec::new(), 7));
    match validate_execution(
        "replay",
        StepKind::SafelyParallel,
        &ExecutionClaim::Parallel {
            width: 8,
            partitions: padded,
        },
        &names,
    ) {
        Err(SeparationError::FakeThreadLabel {
            width: 8,
            empty_partitions: 7,
            ..
        }) => {}
        other => panic!("empty partitions must be a fake label, got {other:?}"),
    }

    match validate_execution(
        "replay",
        StepKind::SafelyParallel,
        &ExecutionClaim::Parallel {
            width: 8,
            partitions: vec![names.clone()],
        },
        &names,
    ) {
        Err(SeparationError::FakeThreadLabel {
            width: 8,
            partitions: 1,
            ..
        }) => {}
        other => panic!("wrong partition count must be a fake label, got {other:?}"),
    }
}

#[test]
fn a_partition_that_is_not_a_partition_is_refused() {
    let names = inputs(&["a", "b", "c", "d"]);
    // Missing an input.
    let missing = ExecutionClaim::Parallel {
        width: 2,
        partitions: vec![inputs(&["a"]), inputs(&["b", "c"])],
    };
    match validate_execution("replay", StepKind::SafelyParallel, &missing, &names) {
        Err(SeparationError::PartitionMismatch { missing: 1, .. }) => {}
        other => panic!("a dropped input must refuse, got {other:?}"),
    }
    // Duplicating an input across workers.
    let duplicated = ExecutionClaim::Parallel {
        width: 2,
        partitions: vec![inputs(&["a", "b", "c"]), inputs(&["c", "d"])],
    };
    match validate_execution("replay", StepKind::SafelyParallel, &duplicated, &names) {
        Err(SeparationError::PartitionMismatch { duplicated: 1, .. }) => {}
        other => panic!("a doubly-charged input must refuse, got {other:?}"),
    }
}

#[test]
fn an_intrinsically_serial_step_is_not_relabeled_parallel() {
    // The relabel mutant: perfect partitions, honest width — and still
    // refused, because order IS this step's semantics and no partitioning
    // makes that safe.
    let names = inputs(&["s1", "s2"]);
    match validate_execution(
        "publish-chain",
        StepKind::IntrinsicallySerial,
        &ExecutionClaim::Parallel {
            width: 2,
            partitions: vec![inputs(&["s1"]), inputs(&["s2"])],
        },
        &names,
    ) {
        Err(SeparationError::SerialStepRelabeled { step }) => assert_eq!(step, "publish-chain"),
        other => panic!("a relabeled serial step must refuse, got {other:?}"),
    }
    // The same step claimed serially validates — the refusal above is about
    // the label, not the step.
    validate_execution(
        "publish-chain",
        StepKind::IntrinsicallySerial,
        &ExecutionClaim::Serial {
            steps: names.clone(),
        },
        &names,
    )
    .expect("the serial claim of a serial step validates");
}

#[test]
fn serial_order_is_bound_into_the_root_and_parallel_order_is_not() {
    // The two halves of "stay ordered": a serial reordering is a DIFFERENT
    // claim (root moves), while a parallel repartitioning is the SAME claim
    // (root holds). A rig that got these backwards would either launder a
    // reorder or manufacture schedule-dependence.
    let forward = ExecutionClaim::Serial {
        steps: inputs(&["s1", "s2", "s3"]),
    };
    let reversed = ExecutionClaim::Serial {
        steps: inputs(&["s3", "s2", "s1"]),
    };
    assert_ne!(
        reduction_root(&forward),
        reduction_root(&reversed),
        "a serial reorder must change the root"
    );

    let names = inputs(&["s1", "s2", "s3"]);
    let one = ExecutionClaim::Parallel {
        width: 1,
        partitions: vec![names.clone()],
    };
    let three = ExecutionClaim::Parallel {
        width: 3,
        partitions: vec![inputs(&["s3"]), inputs(&["s1"]), inputs(&["s2"])],
    };
    assert_eq!(
        reduction_root(&one),
        reduction_root(&three),
        "parallel reduction must be a function of the set"
    );
    // And the serial root is not the parallel root even over identical
    // members: an ordered claim never silently equals an unordered one.
    assert_ne!(reduction_root(&forward), reduction_root(&one));
}
