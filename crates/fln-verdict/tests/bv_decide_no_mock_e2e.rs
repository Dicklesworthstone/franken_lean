//! Real in-process Verdict-to-Crucible publication, refusal, and recovery.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::sync::atomic::AtomicBool;
use std::thread;

use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::mode::{Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_kernel::verdict::RejectClass;
use fln_verdict::{
    BoolExpr, BvDecideInconclusive, BvDecideInternalFault, BvDecideLimits, BvDecideOutcome,
    BvDecidePublication, BvDecideRefusal, BvDecideRequest, BvDecideTelemetry, ProofCheckLimits,
    ProofCheckOutcome, ProofCheckReceipt, ReflectedTheoremRefusal, SolverStatistics, bv_decide,
    bv_decide_with_cancel, check_unsat_streams,
};

const SEMANTIC_SCHEMA: &str = "fln.e2e.bv-decide-semantic/1";
const TELEMETRY_SCHEMA: &str = "fln.e2e.bv-decide-telemetry/1";

fn name(text: &str) -> Name {
    Name::str(Name::anonymous(), text)
}

fn sort_zero() -> Expr {
    Expr::sort(Level::zero())
}

fn identity_type() -> Expr {
    Expr::forall_e(
        name("p"),
        sort_zero(),
        Expr::forall_e(
            name("h"),
            Expr::bvar(0).expect("test bound variable is in range"),
            Expr::bvar(1).expect("test bound variable is in range"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    )
}

fn identity_proof() -> Expr {
    Expr::lam(
        name("p"),
        sort_zero(),
        Expr::lam(
            name("h"),
            Expr::bvar(0).expect("test bound variable is in range"),
            Expr::bvar(0).expect("test bound variable is in range"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    )
}

fn request(theorem: &str) -> BvDecideRequest {
    BvDecideRequest::new(
        BoolExpr::Constant(true),
        name(theorem),
        vec![],
        identity_type(),
        identity_proof(),
        Mode::Sound,
        ReproducibilityProfile::Standard,
    )
}

fn invalid_request(theorem: &str) -> BvDecideRequest {
    BvDecideRequest::new(
        BoolExpr::Constant(true),
        name(theorem),
        vec![],
        Expr::sort(Level::one()),
        sort_zero(),
        Mode::Sound,
        ReproducibilityProfile::Standard,
    )
}

fn hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        encoded.push(char::from_digit(u32::from(byte >> 4), 16).expect("nibble is hexadecimal"));
        encoded.push(char::from_digit(u32::from(byte & 0x0f), 16).expect("nibble is hexadecimal"));
    }
    encoded
}

fn unhex(encoded: &str) -> Result<Vec<u8>, String> {
    let (pairs, remainder) = encoded.as_bytes().as_chunks::<2>();
    if !remainder.is_empty() {
        return Err("hex value has odd length".to_owned());
    }
    if encoded
        .bytes()
        .any(|byte| !matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
    {
        return Err("hex value is not canonical lowercase".to_owned());
    }
    pairs
        .iter()
        .map(|pair| {
            let high = char::from(pair[0])
                .to_digit(16)
                .ok_or_else(|| "hex value has a non-hex high nibble".to_owned())?;
            let low = char::from(pair[1])
                .to_digit(16)
                .ok_or_else(|| "hex value has a non-hex low nibble".to_owned())?;
            u8::try_from((high << 4) | low).map_err(|_| "hex byte overflow".to_owned())
        })
        .collect()
}

fn semantic_ndjson(theorem: &str, publication: &BvDecidePublication) -> String {
    let reflection = publication.reflection();
    format!(
        "{{\"bead\":\"fln-zti3\",\"cleanup\":\"none-required\",\
         \"cnf_hex\":\"{}\",\"declaration_digest\":\"{}\",\
         \"final_state\":\"published-environment-len-1\",\"mode\":\"sound\",\
         \"policy\":\"{}\",\"proof_hex\":\"{}\",\"reproducibility\":\"standard\",\
         \"scenario\":\"bv_decide_no_mock_e2e\",\"schema\":\"{SEMANTIC_SCHEMA}\",\
         \"status\":\"published\",\"theorem\":\"{theorem}\"}}\n",
        hex(reflection.cnf_bytes()),
        reflection.publication.digest,
        fln_verdict::BV_DECIDE_POLICY_ID,
        hex(reflection.proof_bytes()),
    )
}

fn telemetry_ndjson(telemetry: BvDecideTelemetry) -> String {
    format!(
        "{{\"bitblast_ast_nodes\":{},\"bitblast_work_units\":{},\
         \"checker_work_units\":{},\"schema\":\"{TELEMETRY_SCHEMA}\",\
         \"solver_conflicts\":{},\"solver_work_units\":{}}}\n",
        telemetry.bitblast.ast_nodes,
        telemetry.bitblast.work_units,
        telemetry.proof_checker_work_units.unwrap_or(0),
        telemetry.solver.conflicts,
        telemetry.solver.work_units,
    )
}

fn parse_flat_canonical_object(line: &str) -> Result<BTreeMap<String, String>, String> {
    let body = line
        .strip_suffix('\n')
        .ok_or_else(|| "NDJSON record must end with one newline".to_owned())?
        .strip_prefix('{')
        .and_then(|value| value.strip_suffix('}'))
        .ok_or_else(|| "record is not one JSON object".to_owned())?;
    let mut fields = BTreeMap::new();
    let mut previous = None::<String>;
    for field in body.split(',') {
        let (raw_key, raw_value) = field
            .split_once(':')
            .ok_or_else(|| "field has no value separator".to_owned())?;
        let key = raw_key
            .strip_prefix('"')
            .and_then(|value| value.strip_suffix('"'))
            .ok_or_else(|| "field key is not a JSON string".to_owned())?
            .to_owned();
        if previous.as_ref().is_some_and(|prior| prior >= &key) {
            return Err("field keys are not strictly canonical".to_owned());
        }
        previous = Some(key.clone());
        let value = raw_value
            .strip_prefix('"')
            .and_then(|inner| inner.strip_suffix('"'))
            .unwrap_or(raw_value)
            .to_owned();
        if fields.insert(key, value).is_some() {
            return Err("record repeats a field".to_owned());
        }
    }
    Ok(fields)
}

fn validate_semantic_ndjson(line: &str) -> Result<ProofCheckReceipt, String> {
    let fields = parse_flat_canonical_object(line)?;
    let expected = [
        ("bead", "fln-zti3"),
        ("cleanup", "none-required"),
        ("final_state", "published-environment-len-1"),
        ("mode", "sound"),
        ("policy", fln_verdict::BV_DECIDE_POLICY_ID),
        ("reproducibility", "standard"),
        ("scenario", "bv_decide_no_mock_e2e"),
        ("schema", SEMANTIC_SCHEMA),
        ("status", "published"),
    ];
    for (key, value) in expected {
        if fields.get(key).map(String::as_str) != Some(value) {
            return Err(format!("semantic field {key} is not the expected value"));
        }
    }
    let digest = unhex(
        fields
            .get("declaration_digest")
            .ok_or_else(|| "semantic record has no declaration digest".to_owned())?,
    )?;
    if digest.len() != 32 {
        return Err("declaration digest is not 32-byte lowercase hex".to_owned());
    }
    let cnf = unhex(
        fields
            .get("cnf_hex")
            .ok_or_else(|| "semantic record has no CNF".to_owned())?,
    )?;
    let proof = unhex(
        fields
            .get("proof_hex")
            .ok_or_else(|| "semantic record has no proof".to_owned())?,
    )?;
    match check_unsat_streams(
        cnf.as_slice(),
        proof.as_slice(),
        ProofCheckLimits::default(),
    ) {
        ProofCheckOutcome::Verified(receipt) => Ok(receipt),
        other => Err(format!(
            "semantic record's certificate did not independently verify: {other:?}"
        )),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RunEvidence {
    cnf: Vec<u8>,
    proof: Vec<u8>,
    receipt: ProofCheckReceipt,
    declaration_digest: String,
}

fn run_evidence() -> RunEvidence {
    let outcome = bv_decide(
        &Environment::new(),
        request("bv.deterministic"),
        BvDecideLimits::default(),
    );
    let BvDecideOutcome::Proved(publication) = outcome else {
        panic!("determinism fixture must publish");
    };
    let reflection = publication.reflection();
    RunEvidence {
        cnf: reflection.cnf_bytes().to_vec(),
        proof: reflection.proof_bytes().to_vec(),
        receipt: reflection.proof_receipt,
        declaration_digest: reflection.publication.digest.to_string(),
    }
}

#[test]
fn real_positive_failure_and_recovery_are_failure_atomic() {
    let base = Environment::new();
    let positive = bv_decide(&base, request("bv.e2e.positive"), BvDecideLimits::default());
    let BvDecideOutcome::Proved(positive) = positive else {
        panic!("valid reflected theorem must publish");
    };
    assert!(base.is_empty(), "the immutable base must remain unchanged");
    assert_eq!(positive.reflection().publication.environment.len(), 1);

    let failure_base = Environment::new();
    let failure = bv_decide(
        &failure_base,
        invalid_request("bv.e2e.failure"),
        BvDecideLimits::default(),
    );
    assert!(matches!(
        failure,
        BvDecideOutcome::Refused(BvDecideRefusal::Reflection(
            ReflectedTheoremRefusal::Kernel {
                class: RejectClass::TheoremNotProp,
                ..
            }
        ))
    ));
    assert!(failure_base.is_empty());

    let recovered = bv_decide(
        &failure_base,
        request("bv.e2e.recovered"),
        BvDecideLimits::default(),
    );
    let BvDecideOutcome::Proved(recovered) = recovered else {
        panic!("a refusal must not poison the next independent request");
    };
    assert_eq!(recovered.reflection().publication.environment.len(), 1);
    assert!(failure_base.is_empty());
}

#[test]
fn cancellation_resource_and_internal_fault_never_publish() {
    let environment = Environment::new();
    let cancelled = AtomicBool::new(true);
    let cancellation = bv_decide_with_cancel(
        &environment,
        request("bv.e2e.cancelled"),
        BvDecideLimits::default(),
        Some(&cancelled),
    );
    assert!(matches!(
        cancellation,
        BvDecideOutcome::Inconclusive(BvDecideInconclusive::Pipeline(_))
    ));
    assert!(cancellation.publication().is_none());

    let mut limits = BvDecideLimits::default();
    limits.bitblast.max_ast_nodes = 0;
    let exhausted = bv_decide(&environment, request("bv.e2e.exhausted"), limits);
    assert!(matches!(
        exhausted,
        BvDecideOutcome::Inconclusive(BvDecideInconclusive::Bitblast(_))
    ));
    assert!(exhausted.publication().is_none());

    let internal =
        BvDecideOutcome::InternalFault(BvDecideInternalFault::SatModelDoesNotSatisfyNegation);
    assert!(internal.publication().is_none());
    let allocation =
        BvDecideOutcome::Inconclusive(BvDecideInconclusive::CounterexampleAllocationRefused {
            requested: 1,
        });
    assert!(allocation.publication().is_none());
    assert!(environment.is_empty());
}

#[test]
fn semantic_ndjson_is_canonical_independent_and_telemetry_free() {
    let environment = Environment::new();
    let outcome = bv_decide(
        &environment,
        request("bv.e2e.semantic"),
        BvDecideLimits::default(),
    );
    let BvDecideOutcome::Proved(publication) = outcome else {
        panic!("semantic fixture must publish");
    };
    let semantic = semantic_ndjson("bv.e2e.semantic", &publication);
    let independently_replayed =
        validate_semantic_ndjson(&semantic).expect("semantic record must validate independently");
    assert_eq!(
        independently_replayed,
        publication.reflection().proof_receipt
    );

    let telemetry = telemetry_ndjson(publication.telemetry());
    assert!(
        telemetry.len() <= 512,
        "telemetry record is explicitly bounded"
    );
    let telemetry_fields =
        parse_flat_canonical_object(&telemetry).expect("telemetry keys are canonical");
    assert_eq!(
        telemetry_fields.get("schema").map(String::as_str),
        Some(TELEMETRY_SCHEMA)
    );
    assert!(!semantic.contains("work_units"));
    assert!(!semantic.contains("conflicts"));

    let mut changed = publication.telemetry();
    changed.solver = SolverStatistics {
        work_units: changed.solver.work_units.saturating_add(1),
        ..changed.solver
    };
    assert_ne!(telemetry, telemetry_ndjson(changed));
    assert_eq!(
        semantic,
        semantic_ndjson("bv.e2e.semantic", &publication),
        "telemetry changes cannot affect semantic evidence bytes"
    );

    let mutated = semantic.replace("\"status\":\"published\"", "\"status\":\"refused\"");
    assert!(
        validate_semantic_ndjson(&mutated).is_err(),
        "the independent validator must be fail-capable"
    );
}

#[test]
fn productive_thread_matrix_is_byte_identical_at_1_8_32() {
    let expected = run_evidence();
    for threads in [1_usize, 8, 32] {
        let handles = (0..threads)
            .map(|_| thread::spawn(run_evidence))
            .collect::<Vec<_>>();
        for handle in handles {
            let observed = handle.join().expect("bv_decide worker must join");
            assert_eq!(observed, expected, "thread-count identity drifted");
        }
    }
}
