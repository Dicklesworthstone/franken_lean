//! Per-epoch diagnostic projection conformance (bead `franken_lean-wlan`).
//!
//! The five named suites in the bead live here so every frontend is compared against
//! one fixture vocabulary. The Reference appears only as a separately spawned
//! Tribunal oracle in `diagnostic_projection_no_mock_e2e`; the FrankenLean half is a
//! separately spawned copy of this test process exercising the production adapters.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use fln_conformance::normalize::{ComparisonClass, Normalizer, NormalizerId, compare};
use fln_conformance::pin;
use fln_core::diag::{
    Diagnostic, DiagnosticChannel, DiagnosticColorPolicy, DiagnosticEpoch, DiagnosticFormat,
    DiagnosticFrontend, DiagnosticOrderPolicy, DiagnosticPathPolicy, DiagnosticReport, ErrorValue,
    ExitClass, ProjectionDecodeError, ProjectionRequest, ProjectionSnapshot, RelatedSpan,
    ResourceReason, Severity,
};
use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::{BoundedText, Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_core::pos::Position;

fn workspace_root() -> &'static Path {
    static ROOT: std::sync::OnceLock<std::path::PathBuf> = std::sync::OnceLock::new();
    ROOT.get_or_init(|| fln_conformance::checked_workspace_root!())
        .as_path()
}

fn parse_frame(line: &str) -> Option<Diagnostic> {
    let mut parts = line.splitn(5, ':');
    let file_name = parts.next()?.to_string();
    let line_no: usize = parts.next()?.parse().ok()?;
    let col_no: usize = parts.next()?.parse().ok()?;
    let label = parts.next()?;
    let message = parts.next()?.strip_prefix(' ')?.to_string();
    let label = label.strip_prefix(' ')?;
    let (severity, name_part) = match label.strip_prefix("error") {
        Some(rest) => (Severity::Error, rest),
        None => (Severity::Warning, label.strip_prefix("warning")?),
    };
    let error_name = if name_part.is_empty() {
        None
    } else {
        let inner = name_part.strip_prefix('(')?.strip_suffix(')')?;
        Some(Name::from_components(inner.split('.')))
    };
    Some(Diagnostic {
        file_name,
        pos: Position {
            line: line_no,
            column: col_no,
        },
        end_pos: None,
        severity,
        error_name,
        caption: String::new(),
        value: ErrorValue::SyntaxFailure { message },
    })
}

fn epoch_lab_dir() -> String {
    std::env::var("FLN_EPOCH_LAB_DIR").unwrap_or_else(|_| "tribunal/epochs/v4.32.0".to_string())
}

fn request(
    frontend: DiagnosticFrontend,
    format: DiagnosticFormat,
    channel: DiagnosticChannel,
    mode: Mode,
) -> ProjectionRequest {
    ProjectionRequest {
        epoch: DiagnosticEpoch::V4_32_0,
        mode,
        frontend,
        format,
        channel,
        color: DiagnosticColorPolicy::Never,
        path: DiagnosticPathPolicy::Preserve,
        ordering: DiagnosticOrderPolicy::SourcePositionV1,
    }
}

fn cli_request(mode: Mode) -> ProjectionRequest {
    request(
        DiagnosticFrontend::Cli,
        DiagnosticFormat::Human,
        DiagnosticChannel::Stdout,
        mode,
    )
}

fn json_request(mode: Mode) -> ProjectionRequest {
    request(
        DiagnosticFrontend::Json,
        DiagnosticFormat::Ndjson,
        DiagnosticChannel::Stdout,
        mode,
    )
}

fn lsp_request(mode: Mode) -> ProjectionRequest {
    request(
        DiagnosticFrontend::Lsp,
        DiagnosticFormat::Lsp,
        DiagnosticChannel::Protocol,
        mode,
    )
}

fn library_request(mode: Mode) -> ProjectionRequest {
    request(
        DiagnosticFrontend::Library,
        DiagnosticFormat::Typed,
        DiagnosticChannel::ReturnValue,
        mode,
    )
}

fn report(value: ErrorValue, file: &str, line: usize, column: usize) -> DiagnosticReport {
    DiagnosticReport::new(Diagnostic {
        file_name: file.to_string(),
        pos: Position { line, column },
        end_pos: None,
        severity: Severity::Error,
        error_name: None,
        caption: String::new(),
        value,
    })
    .expect("authoritative user diagnostic")
}

fn snapshot(outcome: Outcome<Vec<DiagnosticReport>>) -> ProjectionSnapshot {
    ProjectionSnapshot::from_outcome(&outcome, DiagnosticOrderPolicy::SourcePositionV1)
}

fn reportable_error_values() -> Vec<ErrorValue> {
    let decl = Name::from_components(["Demo", "decl"]);
    vec![
        ErrorValue::SyntaxFailure {
            message: "syntax".to_string(),
        },
        ErrorValue::MacroFailure {
            macro_name: Name::from_components(["Demo", "macro"]),
            message: "macro".to_string(),
        },
        ErrorValue::ElaborationFailure {
            message: "elaboration".to_string(),
        },
        ErrorValue::KernelRejection {
            decl: decl.clone(),
            stable_error_class: "type_mismatch".to_string(),
            message: "kernel rejection".to_string(),
        },
        ErrorValue::ArtifactCorrupt {
            path: "Demo.olean".to_string(),
            detail: "checksum".to_string(),
        },
        ErrorValue::ArtifactEpochMismatch {
            path: "Demo.olean".to_string(),
            expected_epoch: "v4.32.0".to_string(),
            found_epoch: "v4.31.0".to_string(),
        },
        ErrorValue::AbiViolation {
            symbol: "lean_demo".to_string(),
            detail: "layout".to_string(),
        },
        ErrorValue::CapabilityDenied {
            capability: "network".to_string(),
            detail: "sealed build".to_string(),
        },
        ErrorValue::PluginCrashed {
            plugin: "demo".to_string(),
            detail: "signal".to_string(),
        },
        ErrorValue::BuildFailure {
            job: "Demo".to_string(),
            detail: "compiler".to_string(),
        },
        ErrorValue::ProtocolFailure {
            detail: "bad request".to_string(),
        },
        ErrorValue::ReplayDivergence {
            detail: "root mismatch".to_string(),
        },
    ]
}

fn golden_frames() -> (usize, Vec<String>) {
    let root = workspace_root();
    let lab = epoch_lab_dir();
    let manifest = std::fs::read_to_string(root.join(format!("{lab}/MANIFEST.txt")))
        .expect("epoch lab published");
    let d1_files = manifest
        .lines()
        .filter(|line| line.starts_with("d1 ") || line.starts_with("d1-quirk "))
        .map(|line| line.split_whitespace().nth(1).expect("d1 row has a file"))
        .collect::<Vec<_>>();
    assert!(!d1_files.is_empty(), "the D1 corpus exists");

    let mut count = 0;
    let mut failures = Vec::new();
    for file in d1_files {
        let transcript =
            std::fs::read_to_string(root.join(format!("{lab}/transcripts/{file}.stdout")))
                .expect("transcript exists");
        let lines = transcript.lines().collect::<Vec<_>>();
        for (index, line) in lines.iter().enumerate() {
            let Some(diagnostic) = parse_frame(line) else {
                continue;
            };
            let next_is_boundary = lines
                .get(index + 1)
                .is_none_or(|next| parse_frame(next).is_some());
            if !next_is_boundary {
                continue;
            }
            count += 1;
            let projected = snapshot(Outcome::complete(vec![
                DiagnosticReport::new(diagnostic).expect("oracle user diagnostic"),
            ]));
            let rendered = fln_cli::project(cli_request(Mode::Faithful), &projected)
                .expect("faithful CLI tuple is supported")
                .stdout;
            let expected = format!("{line}\n");
            if compare(ComparisonClass::Exact, &rendered, &expected, None)
                .expect("exact comparison cannot fail")
                .is_some()
            {
                failures.push(format!(
                    "{file}: ours `{}` vs oracle `{}`",
                    rendered.trim_end(),
                    expected.trim_end()
                ));
            }
        }
    }
    (count, failures)
}

/// Suite: diagnostic_projection_golden.
///
/// Real epoch frames are byte-exact, every current typed cause survives the robot
/// projection, and semantic comparison can remove only declared path/line-ending
/// differences.
#[test]
fn diagnostic_projection_golden() {
    let (goldens, failures) = golden_frames();
    assert!(
        goldens >= 6,
        "expected at least 6 golden frames across the D1 corpus, found {goldens}"
    );
    assert!(
        failures.is_empty(),
        "{} frame mismatch(es) against the pinned binary:\n{}",
        failures.len(),
        failures.join("\n")
    );

    let reports = reportable_error_values()
        .into_iter()
        .enumerate()
        .map(|(index, value)| report(value, "All.lean", index + 1, 0))
        .collect::<Vec<_>>();
    let semantic = fln_cli::project(
        json_request(Mode::Faithful),
        &snapshot(Outcome::complete(reports)),
    )
    .expect("robot tuple")
    .stdout;
    let reportable_classes = ErrorValue::CLASS_NAMES
        .iter()
        .copied()
        .filter(|class| !matches!(*class, "KernelInconclusive" | "InternalInvariantViolation"))
        .collect::<BTreeSet<_>>();
    let observed = reportable_classes
        .iter()
        .copied()
        .filter(|class| semantic.contains(&format!("\"causeClass\":\"{class}\"")))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        observed, reportable_classes,
        "catch-all swallowing or cause loss changes the reportable population"
    );

    for value in [
        ErrorValue::KernelInconclusive {
            decl: Name::from_components(["Demo", "slow"]),
            resource: ResourceReason::Heartbeats {
                consumed: 11,
                limit: 10,
            },
        },
        ErrorValue::InternalInvariantViolation {
            invariant: "FL-INV-07".to_string(),
            detail: "authority mismatch".to_string(),
        },
    ] {
        let rejected = DiagnosticReport::new(Diagnostic {
            file_name: "Authority.lean".to_string(),
            pos: Position { line: 1, column: 0 },
            end_pos: None,
            severity: Severity::Error,
            error_name: None,
            caption: String::new(),
            value,
        });
        assert!(
            rejected.is_err(),
            "non-authoritative cause cannot enter a complete report"
        );
    }

    let normalizer = Normalizer::paths_v1(vec!["/data/projects/franken_lean".to_string()]);
    let class = ComparisonClass::Semantic {
        normalizer: NormalizerId::PathsV1,
    };
    let ours = "<PATH>/A.lean:1:0: error: body\n";
    let oracle = "/data/projects/franken_lean/A.lean:1:0: error: body\r\n";
    assert!(
        compare(class, ours, oracle, Some(&normalizer))
            .expect("semantic comparison")
            .is_none()
    );
    let changed_body = oracle.replace("body", "different");
    assert!(
        compare(class, ours, &changed_body, Some(&normalizer))
            .expect("semantic comparison")
            .is_some(),
        "a normalizer may not downgrade a body divergence"
    );
}

/// Suite: diagnostic_ordering_model.
///
/// Every arrival permutation produces the same ordered bytes. Related spans and
/// evidence links are independently canonicalized, so arrival timing cannot choose
/// a transcript.
#[test]
fn diagnostic_ordering_model() {
    let make = || {
        vec![
            report(
                ErrorValue::SyntaxFailure {
                    message: "z-body".to_string(),
                },
                "B.lean",
                2,
                0,
            )
            .with_evidence("receipt-z")
            .with_evidence("receipt-a"),
            report(
                ErrorValue::SyntaxFailure {
                    message: "b-body".to_string(),
                },
                "A.lean",
                1,
                0,
            )
            .with_related(RelatedSpan::new(
                "Z.lean",
                Position { line: 3, column: 0 },
                Position { line: 3, column: 1 },
                "z",
            ))
            .with_related(RelatedSpan::new(
                "A.lean",
                Position { line: 2, column: 0 },
                Position { line: 2, column: 1 },
                "a",
            )),
            report(
                ErrorValue::SyntaxFailure {
                    message: "a-body".to_string(),
                },
                "A.lean",
                1,
                0,
            ),
        ]
    };
    let base = make();
    let permutations = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    let mut expected = None;
    for permutation in permutations {
        let reports = permutation
            .into_iter()
            .map(|index| base[index].clone())
            .collect();
        let rendered = fln_cli::project(
            json_request(Mode::Faithful),
            &snapshot(Outcome::complete(reports)),
        )
        .expect("robot tuple")
        .stdout;
        match &expected {
            Some(expected) => assert_eq!(&rendered, expected),
            None => expected = Some(rendered),
        }
    }
    let expected = expected.expect("one permutation");
    let first = expected.find("a-body").expect("first tied body retained");
    let second = expected.find("b-body").expect("second tied body retained");
    let third = expected.find("z-body").expect("later source retained");
    assert!(first < second && second < third);
    assert!(
        expected.find("receipt-a").expect("evidence a")
            < expected.find("receipt-z").expect("evidence z")
    );
    assert!(
        expected.find("\"file\":\"A.lean\"").expect("related a")
            < expected.find("\"file\":\"Z.lean\"").expect("related z")
    );
}

fn warning_snapshot() -> ProjectionSnapshot {
    let mut diagnostic = Diagnostic {
        file_name: "Warn.lean".to_string(),
        pos: Position { line: 1, column: 0 },
        end_pos: None,
        severity: Severity::Warning,
        error_name: None,
        caption: String::new(),
        value: ErrorValue::SyntaxFailure {
            message: "warning".to_string(),
        },
    };
    let report = DiagnosticReport::new(diagnostic.clone()).expect("warning diagnostic");
    diagnostic.severity = Severity::Error;
    let _error_control = DiagnosticReport::new(diagnostic).expect("error diagnostic");
    snapshot(Outcome::complete(vec![report]))
}

fn supported_tuple(request: ProjectionRequest) -> bool {
    match request.frontend {
        DiagnosticFrontend::Cli => {
            request.format == DiagnosticFormat::Human
                && matches!(
                    request.channel,
                    DiagnosticChannel::Stdout | DiagnosticChannel::Stderr
                )
        }
        DiagnosticFrontend::Json => {
            matches!(
                request.format,
                DiagnosticFormat::Json | DiagnosticFormat::Ndjson
            ) && matches!(
                request.channel,
                DiagnosticChannel::Stdout | DiagnosticChannel::Stderr
            ) && request.color == DiagnosticColorPolicy::Never
        }
        DiagnosticFrontend::Lsp => {
            request.format == DiagnosticFormat::Lsp
                && request.channel == DiagnosticChannel::Protocol
                && request.color == DiagnosticColorPolicy::Never
        }
        DiagnosticFrontend::Library => {
            request.format == DiagnosticFormat::Typed
                && request.channel == DiagnosticChannel::ReturnValue
                && request.color == DiagnosticColorPolicy::Never
        }
    }
}

const ADAPTER_OWNERS: &[(DiagnosticFrontend, &str, &str)] = &[
    (DiagnosticFrontend::Cli, "fln-cli", "franken_lean-wlan"),
    (DiagnosticFrontend::Json, "fln-cli", "franken_lean-wlan"),
    (DiagnosticFrontend::Lsp, "fln-server", "franken_lean-wlan"),
    (DiagnosticFrontend::Library, "fln", "franken_lean-wlan"),
];

fn adapter_attempt(
    request: ProjectionRequest,
    snapshot: &ProjectionSnapshot,
) -> Result<ExitClass, fln_core::diag::ProjectionRefusal> {
    match request.frontend {
        DiagnosticFrontend::Cli | DiagnosticFrontend::Json => {
            let projected = fln_cli::project(request, snapshot)?;
            let empty_human_success = request.frontend == DiagnosticFrontend::Cli
                && matches!(
                    snapshot,
                    ProjectionSnapshot::Complete { diagnostics } if diagnostics.is_empty()
                );
            if request.channel == DiagnosticChannel::Stdout {
                assert!(projected.stderr.is_empty());
                assert!(empty_human_success || !projected.stdout.is_empty());
            } else {
                assert!(projected.stdout.is_empty());
                assert!(empty_human_success || !projected.stderr.is_empty());
            }
            Ok(projected.exit)
        }
        DiagnosticFrontend::Lsp => {
            let projected = fln_server::project(request, snapshot)?;
            assert!(!projected.messages.is_empty());
            Ok(projected.disposition)
        }
        DiagnosticFrontend::Library => {
            let projected = fln::project_diagnostics(request, snapshot)?;
            Ok(projected.disposition)
        }
    }
}

/// Suite: frontend_exit_channel_matrix.
///
/// The Cartesian product is closed: exactly the registered tuples succeed, every
/// other tuple fails typed, and all three outcome arms retain disjoint exit classes.
#[test]
fn frontend_exit_channel_matrix() {
    let registered = ADAPTER_OWNERS
        .iter()
        .map(|(frontend, crate_name, bead)| {
            assert!(!crate_name.is_empty() && !bead.is_empty());
            *frontend
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        registered,
        DiagnosticFrontend::ALL.into_iter().collect(),
        "a new frontend cannot exist without an owning crate and gate bead"
    );
    assert_eq!(
        DiagnosticFormat::from_tag(Some(99)),
        Err(ProjectionDecodeError::Unknown {
            axis: fln_core::diag::ProjectionAxis::Format,
            tag: 99
        })
    );
    assert_eq!(
        DiagnosticFrontend::from_tag(None),
        Err(ProjectionDecodeError::Missing {
            axis: fln_core::diag::ProjectionAxis::Frontend
        })
    );

    let complete_ok = snapshot(Outcome::complete(Vec::new()));
    let complete_warning = warning_snapshot();
    let complete_error = snapshot(Outcome::complete(vec![report(
        ErrorValue::SyntaxFailure {
            message: "bad input".to_string(),
        },
        "Bad.lean",
        1,
        0,
    )]));
    let inconclusive = snapshot(Outcome::Inconclusive(
        Inconclusive::cancelled("declaration Demo").with_progress("Demo"),
    ));
    let internal_fault = snapshot(Outcome::InternalFault(
        InternalFault::new("FL-INV-07", "authority bit disagreed").with_evidence("receipt:demo"),
    ));
    let outcomes = [
        (&complete_ok, ExitClass::Success),
        (&complete_warning, ExitClass::Success),
        (&complete_error, ExitClass::UserError),
        (&inconclusive, ExitClass::Inconclusive),
        (&internal_fault, ExitClass::InternalFault),
    ];

    let mut supported = 0;
    for epoch in DiagnosticEpoch::ALL {
        for mode in [Mode::Faithful, Mode::Sound, Mode::Frontier] {
            for frontend in DiagnosticFrontend::ALL {
                for format in DiagnosticFormat::ALL {
                    for channel in DiagnosticChannel::ALL {
                        for color in DiagnosticColorPolicy::ALL {
                            for path in DiagnosticPathPolicy::ALL {
                                let request = ProjectionRequest {
                                    epoch,
                                    mode,
                                    frontend,
                                    format,
                                    channel,
                                    color,
                                    path,
                                    ordering: DiagnosticOrderPolicy::SourcePositionV1,
                                };
                                let expected_support = supported_tuple(request);
                                for (snapshot, exit) in outcomes {
                                    let actual = adapter_attempt(request, snapshot);
                                    assert_eq!(
                                        actual.is_ok(),
                                        expected_support,
                                        "tuple {request:?}"
                                    );
                                    if let Ok(actual_exit) = actual {
                                        assert_eq!(actual_exit, exit);
                                        assert_ne!(
                                            (snapshot.outcome_class(), actual_exit),
                                            ("inconclusive", ExitClass::UserError)
                                        );
                                        assert_ne!(
                                            (snapshot.outcome_class(), actual_exit),
                                            ("internal_fault", ExitClass::UserError)
                                        );
                                    }
                                }
                                supported += usize::from(expected_support);
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(supported, 60, "the registered tuple population changed");
}

/// Suite: mode_projection_isolation.
///
/// Sound/frontier detail never leaks into faithful bytes, and bounded loss retains
/// its cause/evidence links in every structured projection.
#[test]
fn mode_projection_isolation() {
    assert_eq!(
        cli_request(Mode::Faithful).validated_product_class(),
        Ok(fln_core::mode::ValidatedProductClass::ReferenceParity)
    );
    assert_eq!(
        cli_request(Mode::Sound).validated_product_class(),
        Ok(fln_core::mode::ValidatedProductClass::SoundDivergence {
            behavior_note: fln_core::diag::DIAGNOSTIC_SOUND_BEHAVIOR_NOTE,
        })
    );
    let oversized = "x".repeat(BoundedText::LIMIT + 31);
    let diagnostic = DiagnosticReport::new(Diagnostic {
        file_name: "/workspace/Foo.lean".to_string(),
        pos: Position { line: 2, column: 0 },
        end_pos: Some(Position { line: 2, column: 7 }),
        severity: Severity::Error,
        error_name: Some(Name::from_components(["lean", "demo"])),
        caption: String::new(),
        value: ErrorValue::SyntaxFailure {
            message: oversized.clone(),
        },
    })
    .expect("authoritative user diagnostic")
    .with_evidence(format!("receipt:{oversized}"))
    .with_related(RelatedSpan::new(
        "/workspace/Origin.lean",
        Position { line: 1, column: 0 },
        Position { line: 1, column: 3 },
        oversized,
    ));
    let projected = snapshot(Outcome::complete(vec![diagnostic]));
    let faithful = fln_cli::project(cli_request(Mode::Faithful), &projected)
        .expect("faithful")
        .stdout;
    let sound = fln_cli::project(cli_request(Mode::Sound), &projected)
        .expect("sound")
        .stdout;
    let frontier = fln_cli::project(cli_request(Mode::Frontier), &projected)
        .expect("frontier")
        .stdout;
    assert!(!faithful.contains("[typed cause:"));
    assert!(!faithful.contains("BN-02"));
    assert!(sound.contains("[behavior note: BN-02]"));
    assert!(sound.contains("[typed cause: SyntaxFailure]"));
    assert!(frontier.contains("[behavior note: BN-02]"));
    assert!(frontier.contains("[typed cause: SyntaxFailure]"));
    assert!(faithful.starts_with("/workspace/Foo.lean:2:0-2:7: error(lean.demo):"));
    assert!(faithful.contains("diagnostic body truncated"));
    assert_eq!(projected.exit_class(), ExitClass::UserError);

    let json = fln_cli::project(json_request(Mode::Faithful), &projected)
        .expect("json")
        .stdout;
    let sound_json = fln_cli::project(json_request(Mode::Sound), &projected)
        .expect("sound json")
        .stdout;
    assert!(json.contains("\"causeClass\":\"SyntaxFailure\""));
    assert!(json.contains("\"behaviorNote\":null"));
    assert!(sound_json.contains("\"behaviorNote\":\"BN-02\""));
    assert!(json.contains("\"endPosition\":{\"line\":2,\"column\":7}"));
    assert!(json.contains("\"severity\":\"error\""));
    assert!(json.contains("\"truncated\":true"));
    assert!(json.contains("receipt:"));
    assert!(!json.contains("\"host\""));
    assert!(!json.contains("\"pid\""));
    assert!(!json.contains("\"timestamp\""));

    let faithful_lsp =
        fln_server::project(lsp_request(Mode::Faithful), &projected).expect("faithful lsp");
    let sound_lsp = fln_server::project(lsp_request(Mode::Sound), &projected).expect("sound lsp");
    assert!(!faithful_lsp.messages.join("").contains("[typed cause:"));
    assert!(!faithful_lsp.messages.join("").contains("BN-02"));
    assert!(faithful_lsp.messages.join("").contains(
        "\"range\":{\"start\":{\"line\":1,\"character\":0},\"end\":{\"line\":1,\"character\":7}}"
    ));
    assert!(faithful_lsp.messages.join("").contains("\"severity\":1"));
    assert!(
        sound_lsp
            .messages
            .join("")
            .contains("[typed cause: SyntaxFailure]")
    );
    assert!(
        sound_lsp
            .messages
            .join("")
            .contains("[behavior note: BN-02]")
    );

    let library =
        fln::project_diagnostics(library_request(Mode::Faithful), &projected).expect("library");
    assert_eq!(library.semantic, projected);
    let ProjectionSnapshot::Complete { diagnostics } = library.semantic else {
        panic!("library retains complete snapshot");
    };
    assert!(diagnostics[0].body.truncated());
    assert!(diagnostics[0].evidence[0].truncated());
    assert_eq!(diagnostics[0].cause_class, "SyntaxFailure");

    assert_eq!(
        DiagnosticEpoch::from_tag(Some(99)),
        Err(ProjectionDecodeError::Unknown {
            axis: fln_core::diag::ProjectionAxis::Epoch,
            tag: 99
        })
    );
}

const CHILD_OUTPUT_ENV: &str = "FLN_DIAGNOSTIC_CHILD_OUTPUT";
const CHILD_INPUT_ENV: &str = "FLN_DIAGNOSTIC_CHILD_INPUT";
const CHILD_SCENARIO_ENV: &str = "FLN_DIAGNOSTIC_CHILD_SCENARIO";
const CHILD_EPOCH_ENV: &str = "FLN_DIAGNOSTIC_CHILD_EPOCH";
const CHILD_ORIGIN_ENV: &str = "FLN_DIAGNOSTIC_CHILD_ORIGIN";
const EVIDENCE_DIR_ENV: &str = "FLN_DIAGNOSTIC_EVIDENCE_DIR";
const EVIDENCE_RUN_ID_ENV: &str = "FLN_DIAGNOSTIC_RUN_ID";

fn write_new(path: &Path, contents: &str) {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .expect("child output is write-once");
    file.write_all(contents.as_bytes())
        .expect("child output complete");
    file.sync_all().expect("child output durable");
}

fn resource_snapshot() -> ProjectionSnapshot {
    let usage = ResourceUsage {
        reason: ResourceReason::Heartbeats {
            consumed: 11,
            limit: 10,
        },
        allowed: 10,
        observed: 11,
    };
    snapshot(Outcome::Inconclusive(
        Inconclusive::resource(usage)
            .with_diagnostic(ErrorValue::KernelInconclusive {
                decl: Name::from_components(["Demo", "slow"]),
                resource: ResourceReason::Heartbeats {
                    consumed: 11,
                    limit: 10,
                },
            })
            .with_progress("Demo.slow"),
    ))
}

/// The production-adapter side of the no-mock process boundary. In an ordinary test
/// run it executes a non-vacuous smoke cell; the parent E2E sets a write-once output
/// path and this process terminates with the projected C-family exit code.
#[test]
fn diagnostic_projection_child_process() {
    let Ok(output_path) = std::env::var(CHILD_OUTPUT_ENV) else {
        let smoke = snapshot(Outcome::complete(Vec::new()));
        let rendered = fln_cli::project(json_request(Mode::Faithful), &smoke)
            .expect("child smoke")
            .stdout;
        assert!(rendered.contains("\"outcome\":\"complete\""));
        return;
    };
    assert_eq!(
        std::env::var(CHILD_ORIGIN_ENV).as_deref(),
        Ok("tribunal-process"),
        "mock substitution is refused"
    );
    let epoch_tag = std::env::var(CHILD_EPOCH_ENV)
        .unwrap_or_else(|_| DiagnosticEpoch::V4_32_0.tag().to_string())
        .parse::<u16>()
        .expect("numeric epoch tag");
    let epoch = DiagnosticEpoch::from_tag(Some(epoch_tag)).expect("known diagnostic epoch");
    let scenario = std::env::var(CHILD_SCENARIO_ENV).unwrap_or_else(|_| "reference".to_string());
    let (snapshot, mut request) = match scenario.as_str() {
        "reference" => {
            let input_path = std::env::var(CHILD_INPUT_ENV).expect("reference input path");
            let input = std::fs::read_to_string(input_path).expect("reference input");
            let nonempty = input.lines().filter(|line| !line.is_empty()).count();
            let reports = input
                .lines()
                .filter(|line| !line.is_empty())
                .filter_map(parse_frame)
                .map(DiagnosticReport::new)
                .collect::<Result<Vec<_>, _>>()
                .expect("Reference transcript contains user diagnostics");
            assert_eq!(
                reports.len(),
                nonempty,
                "malformed transcript line cannot disappear"
            );
            assert!(!reports.is_empty(), "transcript must carry a diagnostic");
            (
                snapshot(Outcome::complete(reports)),
                cli_request(Mode::Faithful),
            )
        }
        "resource" => (resource_snapshot(), json_request(Mode::Faithful)),
        "cancelled" => (
            snapshot(Outcome::Inconclusive(
                Inconclusive::cancelled("Demo.cancelled").with_progress("Demo"),
            )),
            json_request(Mode::Faithful),
        ),
        "internal-fault" => (
            snapshot(Outcome::InternalFault(
                InternalFault::new("FL-INV-07", "projection invariant")
                    .with_evidence("receipt:projection"),
            )),
            json_request(Mode::Faithful),
        ),
        other => panic!("unknown child scenario {other}"),
    };
    request.epoch = epoch;
    let projection = fln_cli::project(request, &snapshot).expect("registered child tuple");
    write_new(Path::new(&output_path), &projection.stdout);
    std::process::exit(projection.exit.c_family_code().into());
}

fn scratch_dir() -> std::path::PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after epoch")
        .as_nanos();
    let path = workspace_root().join(format!(
        "target/diagnostic-projection-no-mock-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&path).expect("retained scratch directory");
    path
}

fn run_child(
    output: &Path,
    scenario: &str,
    input: Option<&Path>,
    epoch: u16,
    real_origin: bool,
) -> ExitStatus {
    let mut command = Command::new(std::env::current_exe().expect("current test executable"));
    command
        .arg("--exact")
        .arg("diagnostic_projection_child_process")
        .arg("--nocapture")
        .env(CHILD_OUTPUT_ENV, output)
        .env(CHILD_SCENARIO_ENV, scenario)
        .env(CHILD_EPOCH_ENV, epoch.to_string());
    if let Some(input) = input {
        command.env(CHILD_INPUT_ENV, input);
    }
    if real_origin {
        command.env(CHILD_ORIGIN_ENV, "tribunal-process");
    } else {
        command.env_remove(CHILD_ORIGIN_ENV);
    }
    command.stdout(Stdio::null()).stderr(Stdio::null());
    command
        .status()
        .expect("spawn FrankenLean projection process")
}

fn semantic_root(text: &str) -> String {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in text.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{hash:016x}")
}

fn publish_semantic_and_telemetry(
    scratch: &Path,
    started: Instant,
    oracle_root: &str,
    corrupt_root: &str,
    nonanswer_roots: &[(&str, String)],
    raw_statuses: &[(&str, Option<i32>)],
) {
    let Ok(directory) = std::env::var(EVIDENCE_DIR_ENV) else {
        return;
    };
    let directory = Path::new(&directory);
    std::fs::create_dir_all(directory).expect("diagnostic evidence directory");
    let root_for = |name: &str| {
        nonanswer_roots
            .iter()
            .find_map(|(candidate, root)| (*candidate == name).then_some(root.as_str()))
            .expect("non-answer root exists")
    };
    let cases = [
        format!(
            "{{\"actual\":\"equal\",\"actualExit\":\"user_error\",\"actualRoot\":\"{oracle_root}\",\"authority\":true,\"case\":\"reference\",\"channel\":\"stdout\",\"comparisonClass\":\"exact\",\"epoch\":\"v4.32.0\",\"expected\":\"equal\",\"expectedExit\":\"user_error\",\"expectedRoot\":\"{oracle_root}\",\"format\":\"human\",\"frontend\":\"cli\",\"mode\":\"faithful\",\"schema\":\"fln.diagnostic-projection.semantic/1\",\"sequence\":0}}"
        ),
        format!(
            "{{\"actual\":\"divergent\",\"actualExit\":\"user_error\",\"actualRoot\":\"{corrupt_root}\",\"authority\":true,\"case\":\"corrupt\",\"channel\":\"stdout\",\"comparisonClass\":\"exact\",\"epoch\":\"v4.32.0\",\"expected\":\"divergent\",\"expectedExit\":\"user_error\",\"expectedRoot\":\"{oracle_root}\",\"format\":\"human\",\"frontend\":\"cli\",\"mode\":\"faithful\",\"schema\":\"fln.diagnostic-projection.semantic/1\",\"sequence\":1}}"
        ),
        "{\"actual\":\"typed_refusal\",\"actualExit\":\"refused\",\"actualRoot\":\"none\",\"authority\":false,\"case\":\"malformed\",\"expected\":\"typed_refusal\",\"schema\":\"fln.diagnostic-projection.semantic/1\",\"sequence\":2}".to_string(),
        "{\"actual\":\"typed_refusal\",\"actualExit\":\"refused\",\"actualRoot\":\"none\",\"authority\":false,\"case\":\"aged_epoch\",\"expected\":\"typed_refusal\",\"schema\":\"fln.diagnostic-projection.semantic/1\",\"sequence\":3}".to_string(),
        "{\"actual\":\"typed_refusal\",\"actualExit\":\"refused\",\"actualRoot\":\"none\",\"authority\":false,\"case\":\"mock_substitution\",\"expected\":\"typed_refusal\",\"schema\":\"fln.diagnostic-projection.semantic/1\",\"sequence\":4}".to_string(),
        format!(
            "{{\"actual\":\"inconclusive\",\"actualExit\":\"inconclusive\",\"actualRoot\":\"{}\",\"authority\":false,\"case\":\"resource\",\"expected\":\"inconclusive\",\"schema\":\"fln.diagnostic-projection.semantic/1\",\"sequence\":5}}",
            root_for("resource")
        ),
        format!(
            "{{\"actual\":\"inconclusive\",\"actualExit\":\"inconclusive\",\"actualRoot\":\"{}\",\"authority\":false,\"case\":\"cancelled\",\"expected\":\"inconclusive\",\"schema\":\"fln.diagnostic-projection.semantic/1\",\"sequence\":6}}",
            root_for("cancelled")
        ),
        format!(
            "{{\"actual\":\"internal_fault\",\"actualExit\":\"internal_fault\",\"actualRoot\":\"{}\",\"authority\":false,\"case\":\"internal_fault\",\"expected\":\"internal_fault\",\"schema\":\"fln.diagnostic-projection.semantic/1\",\"sequence\":7}}",
            root_for("internal-fault")
        ),
        format!(
            "{{\"actual\":\"equal\",\"actualExit\":\"user_error\",\"actualRoot\":\"{oracle_root}\",\"authority\":true,\"case\":\"recovery\",\"channel\":\"stdout\",\"comparisonClass\":\"exact\",\"epoch\":\"v4.32.0\",\"expected\":\"equal\",\"expectedExit\":\"user_error\",\"expectedRoot\":\"{oracle_root}\",\"format\":\"human\",\"frontend\":\"cli\",\"mode\":\"faithful\",\"schema\":\"fln.diagnostic-projection.semantic/1\",\"sequence\":8}}"
        ),
    ];
    write_new(
        &directory.join("semantic.ndjson"),
        &(cases.join("\n") + "\n"),
    );

    let mut raw_statuses = raw_statuses.to_vec();
    raw_statuses.sort_unstable_by_key(|(name, _)| *name);
    let statuses = raw_statuses
        .iter()
        .map(|(name, code)| {
            format!(
                "\"{name}\":{}",
                code.map_or_else(|| "null".to_string(), |code| code.to_string())
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let run_id = std::env::var(EVIDENCE_RUN_ID_ENV)
        .unwrap_or_else(|_| "unregistered-local-run".to_string())
        .replace('\\', "\\\\")
        .replace('"', "\\\"");
    let scratch = scratch
        .display()
        .to_string()
        .replace('\\', "\\\\")
        .replace('"', "\\\"");
    let telemetry = format!(
        "{{\"durationNs\":{},\"pid\":{},\"rawProcessExits\":{{{statuses}}},\"runId\":\"{run_id}\",\"schema\":\"fln.diagnostic-projection.telemetry/1\",\"scratch\":\"{scratch}\"}}\n",
        started.elapsed().as_nanos(),
        std::process::id()
    );
    write_new(&directory.join("telemetry.ndjson"), &telemetry);
}

/// Suite: diagnostic_projection_no_mock_e2e.
///
/// Runs the pinned Reference and the production adapters in separate processes,
/// exercises corrupt/aged/malformed/resource/cancellation/internal-fault branches,
/// and proves a same-input retry returns to the original exact root.
#[test]
fn diagnostic_projection_no_mock_e2e() {
    let started = Instant::now();
    let rig = pin::RigRun::new(pin::PinRig::DiagnosticProjectionNoMockE2e);
    let Some(reference) = fln_conformance::pin::pinned_lean() else {
        eprintln!("{}", rig.typed_skip().expect("record typed pin skip"));
        return;
    };
    let root = workspace_root();
    let fixture = Path::new("vendor/lean4-src/tests/elab_fail/1707.lean");
    let oracle = Command::new(reference)
        .current_dir(root)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SYSROOT")
        .env("LC_ALL", "C")
        .env("TZ", "UTC")
        .arg(fixture)
        .output()
        .expect("spawn pinned Reference process");
    let oracle_exit = oracle.status.code();
    assert_eq!(oracle_exit, Some(1));
    assert!(oracle.stderr.is_empty());
    let oracle_stdout = String::from_utf8(oracle.stdout).expect("Reference stdout is UTF-8");
    assert!(!oracle_stdout.is_empty());

    let scratch = scratch_dir();
    let input = scratch.join("reference.stdout");
    write_new(&input, &oracle_stdout);
    let projected_path = scratch.join("frankenlean.stdout");
    let reference_status = run_child(
        &projected_path,
        "reference",
        Some(&input),
        DiagnosticEpoch::V4_32_0.tag(),
        true,
    );
    assert_eq!(
        reference_status.code(),
        Some(ExitClass::UserError.c_family_code().into())
    );
    let projected = std::fs::read_to_string(&projected_path).expect("projected transcript");
    assert_eq!(
        compare(ComparisonClass::Exact, &projected, &oracle_stdout, None)
            .expect("exact comparator"),
        None
    );
    let authoritative_root = semantic_root(&projected);

    let corrupt_input = scratch.join("corrupt.stdout");
    write_new(
        &corrupt_input,
        &oracle_stdout.replace("Unknown identifier", "Different identifier"),
    );
    let corrupt_output = scratch.join("corrupt.projected");
    let corrupt_status = run_child(
        &corrupt_output,
        "reference",
        Some(&corrupt_input),
        DiagnosticEpoch::V4_32_0.tag(),
        true,
    );
    assert_eq!(corrupt_status.code(), Some(1));
    let corrupt = std::fs::read_to_string(&corrupt_output).expect("corrupt projection");
    let corrupt_root = semantic_root(&corrupt);
    assert!(
        compare(ComparisonClass::Exact, &corrupt, &oracle_stdout, None)
            .expect("exact comparator")
            .is_some(),
        "corrupt body must not compare clean"
    );

    let malformed_input = scratch.join("malformed.stdout");
    write_new(&malformed_input, "not a diagnostic frame\n");
    let malformed_output = scratch.join("malformed.projected");
    let malformed_status = run_child(
        &malformed_output,
        "reference",
        Some(&malformed_input),
        DiagnosticEpoch::V4_32_0.tag(),
        true,
    );
    assert!(!malformed_status.success());
    assert!(!malformed_output.exists());

    let aged_output = scratch.join("aged.projected");
    let aged_status = run_child(&aged_output, "resource", None, 99, true);
    assert!(!aged_status.success(), "unknown epoch cannot default");
    assert!(!aged_output.exists());

    let mock_output = scratch.join("mock.projected");
    let mock_status = run_child(
        &mock_output,
        "reference",
        Some(&input),
        DiagnosticEpoch::V4_32_0.tag(),
        false,
    );
    assert!(
        !mock_status.success(),
        "mock substitution must fail before publication"
    );
    assert!(!mock_output.exists());

    let mut nonanswer_roots = Vec::new();
    let mut nonanswer_statuses = Vec::new();
    for (scenario, exit, required) in [
        (
            "resource",
            ExitClass::Inconclusive,
            "\"outcome\":\"inconclusive\"",
        ),
        (
            "cancelled",
            ExitClass::Inconclusive,
            "\"causeClass\":\"cancelled\"",
        ),
        (
            "internal-fault",
            ExitClass::InternalFault,
            "\"outcome\":\"internal_fault\"",
        ),
    ] {
        let output = scratch.join(format!("{scenario}.projected"));
        let status = run_child(
            &output,
            scenario,
            None,
            DiagnosticEpoch::V4_32_0.tag(),
            true,
        );
        assert_eq!(status.code(), Some(exit.c_family_code().into()));
        let text = std::fs::read_to_string(output).expect("typed non-answer output");
        assert!(text.contains(required));
        assert!(!text.contains("\"exitClass\":\"user_error\""));
        assert!(text.contains("\"authority\":false"));
        nonanswer_roots.push((scenario, semantic_root(&text)));
        nonanswer_statuses.push((scenario, status.code()));
    }

    let recovered_path = scratch.join("recovered.stdout");
    let recovery_status = run_child(
        &recovered_path,
        "reference",
        Some(&input),
        DiagnosticEpoch::V4_32_0.tag(),
        true,
    );
    assert_eq!(recovery_status.code(), Some(1));
    let recovered = std::fs::read_to_string(recovered_path).expect("recovery transcript");
    assert_eq!(recovered, oracle_stdout);
    assert_eq!(semantic_root(&recovered), authoritative_root);
    let mut raw_statuses = vec![
        ("reference_oracle", oracle_exit),
        ("reference_projection", reference_status.code()),
        ("corrupt", corrupt_status.code()),
        ("malformed", malformed_status.code()),
        ("aged_epoch", aged_status.code()),
        ("mock_substitution", mock_status.code()),
        ("recovery", recovery_status.code()),
    ];
    raw_statuses.extend(nonanswer_statuses);
    publish_semantic_and_telemetry(
        &scratch,
        started,
        &authoritative_root,
        &corrupt_root,
        &nonanswer_roots,
        &raw_statuses,
    );
    rig.executed().expect("record executed projection rig");
}

#[test]
fn the_frame_parser_itself_is_exercised_by_the_labeled_form() {
    let diagnostic =
        parse_frame("vendor/x.lean:1:9: error(lean.unknownIdentifier): Unknown identifier `c`")
            .expect("labeled frame parses");
    assert_eq!(
        diagnostic.error_name.as_ref().map(Name::to_display_string),
        Some("lean.unknownIdentifier".to_string())
    );
    let projected = snapshot(Outcome::complete(vec![
        DiagnosticReport::new(diagnostic).expect("ordinary diagnostic"),
    ]));
    assert_eq!(
        fln_cli::project(cli_request(Mode::Faithful), &projected)
            .expect("faithful")
            .stdout,
        "vendor/x.lean:1:9: error(lean.unknownIdentifier): Unknown identifier `c`\n"
    );
    assert!(parse_frame("  expected ':='").is_none());
}
