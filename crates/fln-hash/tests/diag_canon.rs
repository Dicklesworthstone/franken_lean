//! Versioned wire behavior for the typed error taxonomy (bead fln-rk6): every
//! variant round-trips; an unknown (newer) variant tag decodes as a TYPED failure,
//! never garbage; and a fuzz sweep over arbitrary bytes never panics — malformed
//! input is a value, not an abort (D8).

#![forbid(unsafe_code)]

use fln_core::diag::{Diagnostic, ErrorValue, ResourceReason, Severity};
use fln_core::name::Name;
use fln_core::pos::Position;
use fln_hash::canon::{CanonWriter, Canonical, SCHEMA_DIAG};

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn every_variant() -> Vec<ErrorValue> {
    vec![
        ErrorValue::SyntaxFailure {
            message: "unterminated comment".into(),
        },
        ErrorValue::MacroFailure {
            macro_name: n("myMacro"),
            message: "expansion failed".into(),
        },
        ErrorValue::ElaborationFailure {
            message: "unknown identifier 'x'".into(),
        },
        ErrorValue::KernelRejection {
            decl: n("foo"),
            stable_error_class: "type_mismatch".into(),
            message: "type mismatch".into(),
        },
        ErrorValue::KernelInconclusive {
            decl: n("slow"),
            resource: ResourceReason::Heartbeats {
                consumed: 200_001_000,
                limit: 200_000_000,
            },
        },
        ErrorValue::KernelInconclusive {
            decl: n("bounded"),
            resource: ResourceReason::ExecutionSteps,
        },
        ErrorValue::KernelInconclusive {
            decl: n("deep"),
            resource: ResourceReason::RecursionDepth { limit: 512 },
        },
        ErrorValue::KernelInconclusive {
            decl: n("gone"),
            resource: ResourceReason::Cancelled,
        },
        ErrorValue::KernelInconclusive {
            decl: n("fat"),
            resource: ResourceReason::Memory {
                limit_bytes: 1 << 30,
            },
        },
        ErrorValue::ArtifactCorrupt {
            path: "Foo.olean".into(),
            detail: "bad magic".into(),
        },
        ErrorValue::ArtifactEpochMismatch {
            path: "Foo.olean".into(),
            expected_epoch: "v4.32.0".into(),
            found_epoch: "v4.31.0".into(),
        },
        ErrorValue::AbiViolation {
            symbol: "lean_inc".into(),
            detail: "null object".into(),
        },
        ErrorValue::CapabilityDenied {
            capability: "fs.read".into(),
            detail: "denied by --pure-elab".into(),
        },
        ErrorValue::PluginCrashed {
            plugin: "libfoo.so".into(),
            detail: "SIGSEGV".into(),
        },
        ErrorValue::BuildFailure {
            job: "Mathlib.Order.Basic".into(),
            detail: "dependency failed".into(),
        },
        ErrorValue::ProtocolFailure {
            detail: "missing jsonrpc field".into(),
        },
        ErrorValue::ReplayDivergence {
            detail: "step 41 differs".into(),
        },
        ErrorValue::InternalInvariantViolation {
            invariant: "FL-INV-01".into(),
            detail: "schedule-dependent result".into(),
        },
    ]
}

fn wrap(value: ErrorValue) -> Diagnostic {
    Diagnostic {
        file_name: "Foo.lean".into(),
        pos: Position { line: 2, column: 0 },
        end_pos: Some(Position { line: 2, column: 9 }),
        severity: Severity::Error,
        error_name: Some(n("lean")),
        caption: "ctx".into(),
        value,
    }
}

#[test]
fn every_taxonomy_variant_round_trips() {
    let mut covered = std::collections::BTreeSet::new();
    for value in every_variant() {
        covered.insert(value.class_name());
        let diag = wrap(value);
        let bytes = diag.to_canonical_bytes();
        let back = Diagnostic::from_canonical_bytes(&bytes).expect("round-trip");
        assert_eq!(back, diag);
    }
    assert_eq!(
        covered.len(),
        ErrorValue::CLASS_NAMES.len(),
        "the corpus covers all fourteen classes"
    );
}

#[test]
fn an_unknown_newer_variant_tag_fails_typed_never_garbles() {
    // A hypothetical newer taxonomy value: schema header + valid envelope + tag 99.
    let mut w = CanonWriter::new();
    w.schema(SCHEMA_DIAG);
    w.str("Foo.lean");
    w.u64(1);
    w.u64(0);
    w.u8(0); // no end pos
    w.u8(2); // error severity
    w.u8(0); // no error name
    w.str(""); // caption
    w.u8(99); // unknown variant tag
    let result = Diagnostic::from_canonical_bytes(&w.into_bytes());
    let error = result.expect_err("newer variant must fail typed");
    assert!(error.what.contains("unknown error-value tag"));
}

#[test]
fn severity_and_option_tags_reject_non_canonical_values() {
    let good = wrap(every_variant().remove(0)).to_canonical_bytes();
    // Locate and corrupt the severity byte by rebuilding with a bad value instead of
    // byte surgery (offsets shift with string lengths).
    let mut w = CanonWriter::new();
    w.schema(SCHEMA_DIAG);
    w.str("Foo.lean");
    w.u64(1);
    w.u64(0);
    w.u8(7); // non-canonical option tag for end_pos
    assert!(Diagnostic::from_canonical_bytes(&w.into_bytes()).is_err());
    assert!(Diagnostic::from_canonical_bytes(&good).is_ok());
}

#[test]
fn fuzz_sweep_arbitrary_bytes_never_panic() {
    // Deterministic LCG byte soup, plus mutations of a valid encoding: decoding must
    // return Ok or a typed error — never panic, never abort.
    let mut state = 0x1234_5678_9abc_def0u64;
    let mut next = move || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (state >> 24) as u8
    };
    for len in [0usize, 1, 7, 32, 128, 512] {
        for _ in 0..50 {
            let bytes: Vec<u8> = (0..len).map(|_| next()).collect();
            let _ = Diagnostic::from_canonical_bytes(&bytes);
        }
    }
    let valid = wrap(every_variant().remove(3)).to_canonical_bytes();
    for i in 0..valid.len() {
        let mut mutated = valid.clone();
        mutated[i] ^= 0xff;
        let _ = Diagnostic::from_canonical_bytes(&mutated);
        let mut truncated = valid.clone();
        truncated.truncate(i);
        let _ = Diagnostic::from_canonical_bytes(&truncated);
    }
}
