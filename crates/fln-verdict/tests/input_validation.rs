//! Deterministic negative-path campaign for Verdict's public byte boundaries.
//!
//! Every generated input is reconstructed from one reported seed. The generator
//! is deliberately dependency-free so the campaign stays inside D1's closed
//! dependency universe.

#![forbid(unsafe_code)]

use fln_verdict::{
    Clause, ClauseId, Cnf, InputClause, Literal, Polarity, ProofCheckLimits, ProofCheckOutcome,
    ProofRefusal, ProofRule, ProofStep, ProofStream, SchemaError, SchemaLimits, SolverLimits,
    SolverOutcome, UnsatProof, VariableId, check_unsat_streams, solve,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

const WIRE_MAGIC: &[u8; 8] = b"FLNVRDCT";
const CNF_KIND: u8 = 1;
const SCHEMA_VERSION: u16 = 1;
const WIRE_HEADER_BYTES: usize = 13;
const VERSION_OFFSET: usize = WIRE_MAGIC.len() + 1;
const PROOF_BODY_OFFSET: usize = WIRE_HEADER_BYTES + 8;

const DECODER_ORDINALS_PER_KIND: u64 = 384;
const PROOF_ORDINALS_PER_KIND: u64 = 128;
const DECODER_SEED_BASE: u64 = 0x7ac4_1e00_0000_0000;
const PROOF_SEED_BASE: u64 = 0xc35f_7a00_0000_0000;
const DECODER_INPUTS: u64 = DecoderCaseKind::ALL.len() as u64 * DECODER_ORDINALS_PER_KIND;
const PROOF_INPUTS: u64 = ProofCaseKind::ALL.len() as u64 * PROOF_ORDINALS_PER_KIND;
const TOTAL_SEEDS: u64 = DECODER_INPUTS + PROOF_INPUTS;
const TOTAL_INPUTS: u64 = TOTAL_SEEDS;

const CAMPAIGN_LIMITS: SchemaLimits = SchemaLimits::new(64 * 1024, 4_096, 256, 512, 0, 0, 0);

#[derive(Debug, Clone, Copy)]
struct DeterministicRng {
    state: u64,
}

impl DeterministicRng {
    const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.state
    }

    fn below(&mut self, bound: u64) -> u64 {
        assert!(bound > 0, "generated range must be non-empty");
        self.next() % bound
    }

    fn bit(&mut self) -> bool {
        self.next() & 1 != 0
    }
}

#[derive(Debug, Clone)]
struct RawClause {
    id: u64,
    declared_literals: u64,
    literals: Vec<(u32, u8)>,
}

impl RawClause {
    fn canonical(id: u64, literals: Vec<(u32, u8)>) -> Self {
        Self {
            id,
            declared_literals: literals.len() as u64,
            literals,
        }
    }
}

fn push_u16(bytes: &mut Vec<u8>, value: u16) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn push_u32(bytes: &mut Vec<u8>, value: u32) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn push_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn encode_cnf(variable_count: u32, declared_clause_count: u64, clauses: &[RawClause]) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(WIRE_MAGIC);
    bytes.push(CNF_KIND);
    push_u16(&mut bytes, SCHEMA_VERSION);
    push_u16(&mut bytes, 0);
    push_u32(&mut bytes, variable_count);
    push_u64(&mut bytes, declared_clause_count);
    for clause in clauses {
        push_u64(&mut bytes, clause.id);
        push_u64(&mut bytes, clause.declared_literals);
        for (variable, polarity) in &clause.literals {
            push_u32(&mut bytes, *variable);
            bytes.push(*polarity);
        }
    }
    bytes
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum DecoderCaseKind {
    Truncated = 0,
    ClauseCountMismatch = 1,
    LiteralCountMismatch = 2,
    VariableOutOfRange = 3,
    MalformedEmptyClause = 4,
    DeepTruncation = 5,
    WideClause = 6,
    NonUtf8Bytes = 7,
    RepeatedLiteral = 8,
    ComplementaryLiterals = 9,
    InvalidDimacsLiteral = 10,
    PathologicalCount = 11,
}

impl DecoderCaseKind {
    const ALL: [Self; 12] = [
        Self::Truncated,
        Self::ClauseCountMismatch,
        Self::LiteralCountMismatch,
        Self::VariableOutOfRange,
        Self::MalformedEmptyClause,
        Self::DeepTruncation,
        Self::WideClause,
        Self::NonUtf8Bytes,
        Self::RepeatedLiteral,
        Self::ComplementaryLiterals,
        Self::InvalidDimacsLiteral,
        Self::PathologicalCount,
    ];

    fn from_seed(seed: u64) -> Self {
        match seed as u8 {
            0 => Self::Truncated,
            1 => Self::ClauseCountMismatch,
            2 => Self::LiteralCountMismatch,
            3 => Self::VariableOutOfRange,
            4 => Self::MalformedEmptyClause,
            5 => Self::DeepTruncation,
            6 => Self::WideClause,
            7 => Self::NonUtf8Bytes,
            8 => Self::RepeatedLiteral,
            9 => Self::ComplementaryLiterals,
            10 => Self::InvalidDimacsLiteral,
            11 => Self::PathologicalCount,
            other => panic!("seed carries unknown decoder case tag {other}"),
        }
    }

    fn accepts_error(self, error: &SchemaError) -> bool {
        match self {
            Self::Truncated
            | Self::ClauseCountMismatch
            | Self::LiteralCountMismatch
            | Self::MalformedEmptyClause
            | Self::DeepTruncation => matches!(error, SchemaError::MalformedEncoding { .. }),
            Self::VariableOutOfRange => {
                matches!(error, SchemaError::VariableOutOfRange { .. })
            }
            Self::WideClause | Self::PathologicalCount => {
                matches!(error, SchemaError::ResourceLimitExceeded { .. })
            }
            Self::NonUtf8Bytes => matches!(error, SchemaError::InvalidMagic),
            Self::RepeatedLiteral => {
                matches!(error, SchemaError::NonCanonicalEncoding { .. })
            }
            Self::ComplementaryLiterals => {
                matches!(error, SchemaError::TautologicalClause { .. })
            }
            Self::InvalidDimacsLiteral => matches!(
                error,
                SchemaError::InvalidVariableId { .. } | SchemaError::IntegerOutOfRange { .. }
            ),
        }
    }
}

enum GeneratedDecoderInput {
    Cnf(Vec<u8>),
    Dimacs(i64),
}

impl GeneratedDecoderInput {
    fn parse(self) -> Result<(), SchemaError> {
        match self {
            Self::Cnf(bytes) => Cnf::from_canonical_bytes(&bytes, CAMPAIGN_LIMITS).map(|_| ()),
            Self::Dimacs(value) => Literal::from_dimacs(value).map(|_| ()),
        }
    }
}

fn decoder_seed(kind: DecoderCaseKind, ordinal: u64) -> u64 {
    assert!(ordinal < DECODER_ORDINALS_PER_KIND);
    DECODER_SEED_BASE | (ordinal << 8) | kind as u64
}

fn generate_decoder_input(seed: u64) -> GeneratedDecoderInput {
    let kind = DecoderCaseKind::from_seed(seed);
    let mut rng = DeterministicRng::new(seed);
    match kind {
        DecoderCaseKind::Truncated => {
            let variable_count = 1 + rng.below(16) as u32;
            let variable = 1 + rng.below(u64::from(variable_count)) as u32;
            let row = RawClause::canonical(1 + rng.below(1_000), vec![(variable, rng.bit() as u8)]);
            let mut bytes = encode_cnf(variable_count, 1, &[row]);
            let truncated_len = rng.below(bytes.len() as u64) as usize;
            bytes.truncate(truncated_len);
            GeneratedDecoderInput::Cnf(bytes)
        }
        DecoderCaseKind::ClauseCountMismatch => {
            let claimed = 1 + rng.below(CAMPAIGN_LIMITS.max_clauses);
            GeneratedDecoderInput::Cnf(encode_cnf(1, claimed, &[]))
        }
        DecoderCaseKind::LiteralCountMismatch => {
            let actual = 1 + rng.below(4) as u32;
            let literals = (1..=actual)
                .map(|variable| (variable, rng.bit() as u8))
                .collect::<Vec<_>>();
            let row = RawClause {
                id: 1,
                declared_literals: u64::from(actual) + 1,
                literals,
            };
            GeneratedDecoderInput::Cnf(encode_cnf(actual + 1, 1, &[row]))
        }
        DecoderCaseKind::VariableOutOfRange => {
            let declared = 1 + rng.below(32) as u32;
            let row = RawClause::canonical(1, vec![(declared.saturating_add(1), rng.bit() as u8)]);
            GeneratedDecoderInput::Cnf(encode_cnf(declared, 1, &[row]))
        }
        DecoderCaseKind::MalformedEmptyClause => {
            let row = RawClause::canonical(1, Vec::new());
            let mut bytes = encode_cnf(0, 1, &[row]);
            let trailing = 1 + rng.below(8);
            for _ in 0..trailing {
                bytes.push(rng.next() as u8);
            }
            GeneratedDecoderInput::Cnf(bytes)
        }
        DecoderCaseKind::DeepTruncation => {
            // The v1 CNF schema is intentionally flat. This reaches deeply into
            // a long row sequence without introducing recursive parsing.
            let row_count = 64 + rng.below(64);
            let variable_count = 16;
            let rows = (0..row_count)
                .map(|index| {
                    RawClause::canonical(
                        index + 1,
                        vec![(
                            1 + (index % u64::from(variable_count)) as u32,
                            rng.bit() as u8,
                        )],
                    )
                })
                .collect::<Vec<_>>();
            let mut bytes = encode_cnf(variable_count, row_count, &rows);
            let removed = 1 + rng.below(5) as usize;
            bytes.truncate(bytes.len() - removed);
            GeneratedDecoderInput::Cnf(bytes)
        }
        DecoderCaseKind::WideClause => {
            let width = CAMPAIGN_LIMITS.max_literals + 1 + rng.below(32);
            let literals = (1..=width)
                .map(|variable| (variable as u32, rng.bit() as u8))
                .collect::<Vec<_>>();
            let row = RawClause::canonical(1, literals);
            GeneratedDecoderInput::Cnf(encode_cnf(width as u32, 1, &[row]))
        }
        DecoderCaseKind::NonUtf8Bytes => {
            let mut bytes = vec![0xf0, 0x28, 0x8c, 0x28, 0xff, 0xfe, 0x80, 0x80];
            let suffix_len = WIRE_HEADER_BYTES + rng.below(32) as usize;
            for _ in 0..suffix_len {
                bytes.push(rng.next() as u8);
            }
            GeneratedDecoderInput::Cnf(bytes)
        }
        DecoderCaseKind::RepeatedLiteral => {
            let variable = 1 + rng.below(32) as u32;
            let polarity = rng.bit() as u8;
            let row = RawClause::canonical(1, vec![(variable, polarity), (variable, polarity)]);
            GeneratedDecoderInput::Cnf(encode_cnf(variable, 1, &[row]))
        }
        DecoderCaseKind::ComplementaryLiterals => {
            let variable = 1 + rng.below(32) as u32;
            let row = RawClause::canonical(1, vec![(variable, 0), (variable, 1)]);
            GeneratedDecoderInput::Cnf(encode_cnf(variable, 1, &[row]))
        }
        DecoderCaseKind::InvalidDimacsLiteral => {
            let value = if rng.bit() {
                0
            } else {
                let magnitude = i64::from(u32::MAX) + 1 + rng.below(1 << 20) as i64;
                if rng.bit() { magnitude } else { -magnitude }
            };
            GeneratedDecoderInput::Dimacs(value)
        }
        DecoderCaseKind::PathologicalCount => {
            if rng.bit() {
                GeneratedDecoderInput::Cnf(encode_cnf(1, u64::MAX, &[]))
            } else {
                let row = RawClause {
                    id: 1,
                    declared_literals: u64::MAX,
                    literals: Vec::new(),
                };
                GeneratedDecoderInput::Cnf(encode_cnf(1, 1, &[row]))
            }
        }
    }
}

fn format_seeds(seeds: &[u64]) -> String {
    seeds
        .iter()
        .map(|seed| format!("{seed:#018x}"))
        .collect::<Vec<_>>()
        .join(",")
}

fn format_failures(failures: &[(u64, String)]) -> String {
    failures
        .iter()
        .take(8)
        .map(|(seed, reason)| format!("{seed:#018x}:{reason}"))
        .collect::<Vec<_>>()
        .join(" | ")
}

#[test]
fn generated_nonconforming_inputs_return_typed_errors_without_panicking() {
    let mut panic_seeds = Vec::new();
    let mut accepted_seeds = Vec::new();
    let mut wrong_error_seeds = Vec::new();
    let mut attempted = 0_u64;

    for kind in DecoderCaseKind::ALL {
        for ordinal in 0..DECODER_ORDINALS_PER_KIND {
            let seed = decoder_seed(kind, ordinal);
            attempted += 1;
            match catch_unwind(AssertUnwindSafe(|| generate_decoder_input(seed).parse())) {
                Err(_) => panic_seeds.push(seed),
                Ok(Ok(())) => accepted_seeds.push(seed),
                Ok(Err(error)) if !kind.accepts_error(&error) => {
                    wrong_error_seeds.push(seed);
                }
                Ok(Err(_)) => {}
            }
        }
    }

    println!(
        "verdict-input-validation seeds={attempted} inputs={attempted} panics={} \
         invalid_inputs_accepted={} wrong_typed_errors={}",
        panic_seeds.len(),
        accepted_seeds.len(),
        wrong_error_seeds.len()
    );
    assert_eq!(attempted, DECODER_INPUTS);
    assert!(
        panic_seeds.is_empty() && accepted_seeds.is_empty() && wrong_error_seeds.is_empty(),
        "decoder campaign failed: panic_seeds=[{}] accepted_seeds=[{}] \
         wrong_error_seeds=[{}]",
        format_seeds(&panic_seeds),
        format_seeds(&accepted_seeds),
        format_seeds(&wrong_error_seeds)
    );
}

fn variable(raw: u32) -> VariableId {
    VariableId::new(raw).expect("fixture variable is non-zero")
}

fn clause_id(raw: u64) -> ClauseId {
    ClauseId::new(raw).expect("fixture clause id is non-zero")
}

fn clause(literals: &[(u32, Polarity)]) -> Clause {
    Clause::new(
        literals
            .iter()
            .copied()
            .map(|(raw, polarity)| Literal::new(variable(raw), polarity))
            .collect(),
    )
    .expect("fixture clause is canonicalizable")
}

#[derive(Debug)]
struct ProofFixture {
    cnf: Cnf,
    proof_bytes: Vec<u8>,
    first_derived_id: u64,
    second_derived_id: u64,
}

fn proof_fixture(seed: u64) -> ProofFixture {
    let mut rng = DeterministicRng::new(seed);
    let id_base = 1 + rng.below(1_000_000) * 8;
    let first = clause_id(id_base);
    let second = clause_id(id_base + 1);
    let third = clause_id(id_base + 2);
    let first_derived = clause_id(id_base + 3);
    let second_derived = clause_id(id_base + 4);

    let cnf = Cnf::new(
        2,
        vec![
            InputClause::new(
                first,
                clause(&[(1, Polarity::Positive), (2, Polarity::Positive)]),
            ),
            InputClause::new(second, clause(&[(1, Polarity::Negative)])),
            InputClause::new(third, clause(&[(2, Polarity::Negative)])),
        ],
        SchemaLimits::default(),
    )
    .expect("proof fixture CNF is valid");
    let proof = UnsatProof::new(
        &cnf,
        vec![
            ProofStep::Derive {
                id: first_derived,
                clause: clause(&[(2, Polarity::Positive)]),
                rule: ProofRule::Resolution {
                    pivot: variable(1),
                    positive_parent: first,
                    negative_parent: second,
                },
            },
            ProofStep::Derive {
                id: second_derived,
                clause: clause(&[]),
                rule: ProofRule::Resolution {
                    pivot: variable(2),
                    positive_parent: first_derived,
                    negative_parent: third,
                },
            },
            ProofStep::Conclude {
                empty_clause: second_derived,
            },
        ],
        SchemaLimits::default(),
    )
    .expect("proof fixture is structurally valid");
    let proof_bytes = proof.to_canonical_bytes();
    assert_eq!(
        proof_bytes.len(),
        PROOF_BODY_OFFSET + first_derived_step_len() + second_derived_step_len() + 9
    );
    ProofFixture {
        cnf,
        proof_bytes,
        first_derived_id: first_derived.get(),
        second_derived_id: second_derived.get(),
    }
}

const fn first_derived_step_len() -> usize {
    1 + 8 + 8 + 5 + 1 + 4 + 8 + 8
}

const fn second_derived_step_len() -> usize {
    1 + 8 + 8 + 1 + 4 + 8 + 8
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum ProofCaseKind {
    WrongLiteralSign = 0,
    MissingStep = 1,
    StepsOutOfOrder = 2,
    UnknownVersion = 3,
}

impl ProofCaseKind {
    const ALL: [Self; 4] = [
        Self::WrongLiteralSign,
        Self::MissingStep,
        Self::StepsOutOfOrder,
        Self::UnknownVersion,
    ];

    fn from_seed(seed: u64) -> Self {
        match seed as u8 {
            0 => Self::WrongLiteralSign,
            1 => Self::MissingStep,
            2 => Self::StepsOutOfOrder,
            3 => Self::UnknownVersion,
            other => panic!("seed carries unknown proof case tag {other}"),
        }
    }

    fn accepts_refusal(self, refusal: &ProofRefusal, fixture: &ProofFixture) -> bool {
        match self {
            Self::WrongLiteralSign => matches!(
                refusal,
                ProofRefusal::ResolutionMismatch { step }
                    if *step == fixture.first_derived_id
            ),
            Self::MissingStep => matches!(refusal, ProofRefusal::MissingConclusion),
            Self::StepsOutOfOrder => matches!(
                refusal,
                ProofRefusal::MissingDependency { step, dependency }
                    if *step == fixture.second_derived_id
                        && *dependency == fixture.first_derived_id
            ),
            Self::UnknownVersion => matches!(
                refusal,
                ProofRefusal::UnsupportedVersion {
                    stream: ProofStream::Proof,
                    found,
                    supported: SCHEMA_VERSION,
                } if *found != SCHEMA_VERSION
            ),
        }
    }
}

fn proof_seed(kind: ProofCaseKind, ordinal: u64) -> u64 {
    assert!(ordinal < PROOF_ORDINALS_PER_KIND);
    PROOF_SEED_BASE | (ordinal << 8) | kind as u64
}

fn mutate_proof(seed: u64, fixture: &ProofFixture) -> Vec<u8> {
    let kind = ProofCaseKind::from_seed(seed);
    let mut bytes = fixture.proof_bytes.clone();
    match kind {
        ProofCaseKind::WrongLiteralSign => {
            let polarity_at = PROOF_BODY_OFFSET + 1 + 8 + 8 + 4;
            assert_eq!(bytes[polarity_at], Polarity::Positive as u8);
            bytes[polarity_at] = Polarity::Negative as u8;
        }
        ProofCaseKind::MissingStep => {
            bytes[WIRE_HEADER_BYTES..PROOF_BODY_OFFSET].copy_from_slice(&2_u64.to_le_bytes());
            bytes.truncate(bytes.len() - 9);
        }
        ProofCaseKind::StepsOutOfOrder => {
            let first_end = PROOF_BODY_OFFSET + first_derived_step_len();
            let second_end = first_end + second_derived_step_len();
            let mut reordered = Vec::with_capacity(bytes.len());
            reordered.extend_from_slice(&bytes[..PROOF_BODY_OFFSET]);
            reordered.extend_from_slice(&bytes[first_end..second_end]);
            reordered.extend_from_slice(&bytes[PROOF_BODY_OFFSET..first_end]);
            reordered.extend_from_slice(&bytes[second_end..]);
            bytes = reordered;
        }
        ProofCaseKind::UnknownVersion => {
            let mut rng = DeterministicRng::new(seed ^ 0x91e1_0da5_7c2b_4f63);
            let future_version = 2 + rng.below(u64::from(u16::MAX) - 1) as u16;
            bytes[VERSION_OFFSET..VERSION_OFFSET + 2]
                .copy_from_slice(&future_version.to_le_bytes());
        }
    }
    bytes
}

#[derive(Debug)]
enum ProofCaseResult {
    Passed { checker_work: u64, solver_work: u64 },
    WronglyAccepted,
    Failed(String),
}

fn run_proof_case(seed: u64) -> ProofCaseResult {
    let kind = ProofCaseKind::from_seed(seed);
    let fixture = proof_fixture(seed);
    let invalid_proof = mutate_proof(seed, &fixture);
    let cnf_bytes = fixture.cnf.to_canonical_bytes();
    let outcome = check_unsat_streams(
        &cnf_bytes[..],
        &invalid_proof[..],
        ProofCheckLimits::default(),
    );
    let refusal = match &outcome {
        ProofCheckOutcome::Verified(_) => return ProofCaseResult::WronglyAccepted,
        ProofCheckOutcome::Refused(refusal) if kind.accepts_refusal(refusal, &fixture) => refusal,
        ProofCheckOutcome::Refused(refusal) => {
            return ProofCaseResult::Failed(format!(
                "unexpected typed refusal for {kind:?}: {refusal:?}"
            ));
        }
        ProofCheckOutcome::Inconclusive(reason) => {
            return ProofCaseResult::Failed(format!(
                "invalid proof was inconclusive instead of refused: {reason:?}"
            ));
        }
        ProofCheckOutcome::InternalFault(fault) => {
            return ProofCaseResult::Failed(format!(
                "invalid proof caused an internal fault: {fault:?}"
            ));
        }
    };
    if outcome.receipt().is_some() {
        return ProofCaseResult::Failed(format!(
            "typed refusal {refusal:?} carried a verification receipt"
        ));
    }

    // A refusal has no verdict authority. Recovery therefore solves the exact
    // CNF again and accepts only the solver's newly checker-verified artifact.
    let recomputed = solve(&fixture.cnf, SolverLimits::default());
    let (artifact, statistics) = match &recomputed {
        SolverOutcome::Unsat {
            artifact,
            statistics,
        } => (artifact, statistics),
        other => {
            return ProofCaseResult::Failed(format!(
                "recomputation did not return checked UNSAT: {other:?}"
            ));
        }
    };
    if artifact.proof_bytes() == invalid_proof {
        return ProofCaseResult::Failed("recomputation reused the refused proof bytes".to_owned());
    }
    let fresh_check = check_unsat_streams(
        artifact.cnf_bytes(),
        artifact.proof_bytes(),
        ProofCheckLimits::default(),
    );
    let ProofCheckOutcome::Verified(fresh_receipt) = fresh_check else {
        return ProofCaseResult::Failed(format!(
            "recomputed proof was not independently verified: {fresh_check:?}"
        ));
    };
    if &fresh_receipt != artifact.receipt() {
        return ProofCaseResult::Failed(
            "recomputed artifact receipt differs from independent replay".to_owned(),
        );
    }
    ProofCaseResult::Passed {
        checker_work: fresh_receipt.work_units,
        solver_work: statistics.work_units,
    }
}

#[test]
fn altered_proofs_are_refused_and_recomputed_from_checked_artifacts() {
    let mut panic_seeds = Vec::new();
    let mut wrongly_accepted_seeds = Vec::new();
    let mut failed_cases = Vec::new();
    let mut attempted = 0_u64;
    let mut recomputations = 0_u64;
    let mut largest_checker_work = 0_u64;
    let mut smallest_solver_work = u64::MAX;

    for kind in ProofCaseKind::ALL {
        for ordinal in 0..PROOF_ORDINALS_PER_KIND {
            let seed = proof_seed(kind, ordinal);
            attempted += 1;
            match catch_unwind(AssertUnwindSafe(|| run_proof_case(seed))) {
                Err(_) => panic_seeds.push(seed),
                Ok(ProofCaseResult::WronglyAccepted) => wrongly_accepted_seeds.push(seed),
                Ok(ProofCaseResult::Failed(reason)) => failed_cases.push((seed, reason)),
                Ok(ProofCaseResult::Passed {
                    checker_work,
                    solver_work,
                }) => {
                    recomputations += 1;
                    largest_checker_work = largest_checker_work.max(checker_work);
                    smallest_solver_work = smallest_solver_work.min(solver_work);
                }
            }
        }
    }

    println!(
        "verdict-proof-validation seeds={attempted} inputs={attempted} panics={} \
         proofs_wrongly_accepted={} typed_refusal_recomputations={recomputations} \
         max_checker_work={largest_checker_work} min_solver_work={smallest_solver_work}",
        panic_seeds.len(),
        wrongly_accepted_seeds.len()
    );
    assert_eq!(attempted, PROOF_INPUTS);
    assert!(
        panic_seeds.is_empty()
            && wrongly_accepted_seeds.is_empty()
            && failed_cases.is_empty()
            && recomputations == PROOF_INPUTS,
        "proof campaign failed: panic_seeds=[{}] wrongly_accepted_seeds=[{}] \
         failed_cases=[{}]",
        format_seeds(&panic_seeds),
        format_seeds(&wrongly_accepted_seeds),
        format_failures(&failed_cases)
    );
}

#[test]
fn canonical_empty_clause_remains_a_valid_unsat_input() {
    let cnf = Cnf::new(
        0,
        vec![InputClause::new(
            clause_id(1),
            Clause::new(Vec::new()).expect("empty clause is canonical"),
        )],
        SchemaLimits::default(),
    )
    .expect("empty clause is a valid CNF row");
    assert_eq!(
        Cnf::from_canonical_bytes(&cnf.to_canonical_bytes(), SchemaLimits::default()),
        Ok(cnf.clone())
    );
    assert!(
        matches!(
            solve(&cnf, SolverLimits::default()),
            SolverOutcome::Unsat { .. }
        ),
        "an empty clause denotes UNSAT; it is not a malformed input"
    );
}

fn pigeonhole(pigeons: u32, holes: u32) -> Cnf {
    let variable_for = |pigeon: u32, hole: u32| pigeon * holes + hole + 1;
    let mut clauses = Vec::new();
    for pigeon in 0..pigeons {
        clauses.push(clause(
            &(0..holes)
                .map(|hole| (variable_for(pigeon, hole), Polarity::Positive))
                .collect::<Vec<_>>(),
        ));
    }
    for hole in 0..holes {
        for first in 0..pigeons {
            for second in first + 1..pigeons {
                clauses.push(clause(&[
                    (variable_for(first, hole), Polarity::Negative),
                    (variable_for(second, hole), Polarity::Negative),
                ]));
            }
        }
    }
    Cnf::new(
        pigeons * holes,
        clauses
            .into_iter()
            .enumerate()
            .map(|(index, clause)| InputClause::new(clause_id(index as u64 + 1), clause))
            .collect(),
        SchemaLimits::default(),
    )
    .expect("pigeonhole fixture is a valid CNF")
}

fn complete_assignment_cube(variable_count: u32) -> Cnf {
    let assignment_count = 1_u64
        .checked_shl(variable_count)
        .expect("cost corpus variable count fits the assignment mask");
    let clauses = (0..assignment_count)
        .map(|assignment| {
            let literals = (0..variable_count)
                .map(|variable| {
                    let polarity = if assignment & (1_u64 << variable) == 0 {
                        Polarity::Positive
                    } else {
                        Polarity::Negative
                    };
                    (variable + 1, polarity)
                })
                .collect::<Vec<_>>();
            clause(&literals)
        })
        .enumerate()
        .map(|(index, clause)| InputClause::new(clause_id(index as u64 + 1), clause))
        .collect();
    Cnf::new(variable_count, clauses, SchemaLimits::default())
        .expect("complete assignment cube is a valid UNSAT CNF")
}

#[test]
fn checker_work_is_strictly_below_recomputation_on_unsat_corpus() {
    let corpus = [
        ("pigeonhole", 3, pigeonhole(3, 2)),
        ("pigeonhole", 4, pigeonhole(4, 3)),
        ("pigeonhole", 5, pigeonhole(5, 4)),
        ("assignment-cube", 3, complete_assignment_cube(3)),
        ("assignment-cube", 4, complete_assignment_cube(4)),
        ("assignment-cube", 5, complete_assignment_cube(5)),
    ];
    let mut violations = Vec::new();
    for (family, size, cnf) in corpus {
        let outcome = solve(&cnf, SolverLimits::default());
        let SolverOutcome::Unsat {
            artifact,
            statistics,
        } = outcome
        else {
            panic!("{family}({size}) must produce a checked UNSAT artifact: {outcome:?}");
        };
        let replay = check_unsat_streams(
            artifact.cnf_bytes(),
            artifact.proof_bytes(),
            ProofCheckLimits::default(),
        );
        let receipt = replay
            .receipt()
            .expect("solver-produced proof must replay independently");
        assert_eq!(receipt, artifact.receipt());
        let mut derived_literals = 0_u64;
        let mut rup_assumptions = 0_u64;
        let mut rup_dependencies = 0_u64;
        let mut rup_steps = 0_u64;
        let mut resolution_work = 0_u64;
        let mut resolution_steps = 0_u64;
        for step in artifact.proof().steps() {
            if let ProofStep::Derive { clause, rule, .. } = step {
                let literals = clause.literals().len() as u64;
                derived_literals += literals;
                match rule {
                    ProofRule::Rup { antecedents } => {
                        rup_steps += 1;
                        rup_assumptions += literals;
                        rup_dependencies += antecedents.len() as u64;
                    }
                    ProofRule::Resolution { .. } => {
                        resolution_steps += 1;
                        resolution_work += literals;
                    }
                }
            }
        }
        let structural_work = cnf.facts().clauses
            + cnf.facts().literals
            + receipt.proof_steps
            + derived_literals
            + rup_dependencies
            + rup_assumptions
            + resolution_work;
        let rup_scan_work = receipt
            .work_units
            .checked_sub(structural_work)
            .expect("checker work accounting must conserve registered units");
        println!(
            "verdict-cost-evidence family={family} size={size} variables={} clauses={} \
             proof_steps={} resolution_steps={resolution_steps} rup_steps={rup_steps} \
             dependencies={} structural_work={} rup_scan_work={} \
             checker_work={} solver_work={}",
            cnf.variable_count(),
            cnf.facts().clauses,
            receipt.proof_steps,
            receipt.dependencies,
            structural_work,
            rup_scan_work,
            receipt.work_units,
            statistics.work_units
        );
        if receipt.work_units >= statistics.work_units {
            violations.push((family, size, receipt.work_units, statistics.work_units));
        }
    }
    assert!(
        violations.is_empty(),
        "proof checking must be strictly cheaper than recomputation: {violations:?}"
    );
}

#[test]
fn campaign_accounting_is_stable() {
    assert_eq!(DECODER_INPUTS, 4_608);
    assert_eq!(PROOF_INPUTS, 512);
    assert_eq!(TOTAL_SEEDS, 5_120);
    assert_eq!(TOTAL_INPUTS, 5_120);
}

// ---------------------------------------------------------------------------
// FL-INV-06 census cardinality join (bead fln-h1k.2)
// ---------------------------------------------------------------------------

const CENSUS_DISCLOSURE_PREFIX: &str = "Certificate-accepting path cardinality: `";
const CERTIFICATE_BOUNDARY_MARKER: &str = "FLN-FL-INV-06-CERTIFICATE-BOUNDARY:";
const CERTIFICATE_ALIAS_MARKER: &str = "FLN-FL-INV-06-CERTIFICATE-ALIAS:";
const ANVIL_CENSUS: &str = "crates/fln-anvil/FL_INV_06_CERTIFICATE_CENSUS.md";
const VERDICT_CENSUS: &str = "crates/fln-verdict/FL_INV_06_CERTIFICATE_CENSUS.md";

#[derive(Debug, Clone)]
struct CensusTree {
    files: BTreeMap<String, String>,
}

impl CensusTree {
    fn read(&self, path: &str) -> Result<&str, String> {
        self.files
            .get(path)
            .map(String::as_str)
            .ok_or_else(|| format!("census input {path} was not found"))
    }

    fn insert(&mut self, path: &str, contents: impl Into<String>) {
        self.files.insert(path.to_owned(), contents.into());
    }

    fn edit(&mut self, path: &str, edit: impl FnOnce(&str) -> String) {
        let prior = self
            .files
            .get(path)
            .unwrap_or_else(|| panic!("mutant input {path} must exist"))
            .clone();
        self.files.insert(path.to_owned(), edit(&prior));
    }
}

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("fln-verdict must remain a direct member of the workspace crates directory")
        .to_path_buf()
}

fn collect_census_inputs(
    directory: &Path,
    root: &Path,
    files: &mut BTreeMap<String, String>,
) -> Result<(), String> {
    let entries = fs::read_dir(directory).map_err(|error| {
        format!(
            "census directory {} is unreadable: {error}",
            directory.display()
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|error| {
            format!(
                "an entry under census directory {} is unreadable: {error}",
                directory.display()
            )
        })?;
        let kind = entry.file_type().map_err(|error| {
            format!(
                "census path {} has no readable file type: {error}",
                entry.path().display()
            )
        })?;
        if kind.is_symlink() {
            continue;
        }
        let path = entry.path();
        if kind.is_dir() {
            collect_census_inputs(&path, root, files)?;
            continue;
        }
        let name = path.file_name().and_then(|name| name.to_str());
        let relevant = name == Some("Cargo.toml")
            || path.extension().is_some_and(|extension| extension == "rs")
            || name == Some("FL_INV_06_CERTIFICATE_CENSUS.md");
        if !relevant {
            continue;
        }
        let relative = path
            .strip_prefix(root)
            .map_err(|error| format!("census path {} escaped the root: {error}", path.display()))?
            .to_string_lossy()
            .replace('\\', "/");
        let contents = fs::read_to_string(&path)
            .map_err(|error| format!("census input {relative} is unreadable: {error}"))?;
        files.insert(relative, contents);
    }
    Ok(())
}

fn real_census_tree() -> Result<CensusTree, String> {
    let root = repository_root();
    let mut files = BTreeMap::new();
    files.insert(
        "Cargo.toml".to_owned(),
        fs::read_to_string(root.join("Cargo.toml"))
            .map_err(|error| format!("workspace Cargo.toml is unreadable: {error}"))?,
    );
    collect_census_inputs(&root.join("crates"), &root, &mut files)?;
    Ok(CensusTree { files })
}

fn disclosed_cardinality(tree: &CensusTree, path: &str) -> Result<usize, String> {
    let document = tree.read(path)?;
    let rows: Vec<&str> = document
        .lines()
        .filter_map(|line| line.strip_prefix(CENSUS_DISCLOSURE_PREFIX))
        .collect();
    if rows.len() != 1 {
        return Err(format!(
            "{path} must carry exactly one machine-readable `{CENSUS_DISCLOSURE_PREFIX}<n>`.` \
             row; found {}",
            rows.len()
        ));
    }
    let encoded = rows[0]
        .strip_suffix("`.")
        .ok_or_else(|| format!("{path} has a malformed cardinality disclosure"))?;
    encoded
        .parse()
        .map_err(|error| format!("{path} has a non-numeric cardinality {encoded:?}: {error}"))
}

fn production_prefix(source: &str) -> &str {
    ["\n#[cfg(test)]\nmod ", "\n#[cfg(test)]\npub mod "]
        .iter()
        .filter_map(|marker| source.find(marker))
        .min()
        .map_or(source, |at| &source[..at])
}

fn manifest_facts(manifest: &str) -> (usize, usize) {
    let mut dependency_rows = 0usize;
    let mut target_rows = 0usize;
    let mut section = "";
    for line in manifest.lines() {
        let trimmed = line.split('#').next().unwrap_or_default().trim();
        if trimmed.starts_with('[') && trimmed.ends_with(']') {
            section = trimmed;
            if matches!(
                section,
                "[lib]" | "[[bin]]" | "[[test]]" | "[[bench]]" | "[[example]]"
            ) {
                target_rows += 1;
            }
            if section.starts_with("[dependencies.")
                || section.starts_with("[dev-dependencies.")
                || section.starts_with("[build-dependencies.")
                || section.contains(".dependencies.")
            {
                dependency_rows += 1;
            }
            continue;
        }
        if trimmed.is_empty() || !trimmed.contains('=') {
            continue;
        }
        if matches!(
            section,
            "[dependencies]" | "[dev-dependencies]" | "[build-dependencies]"
        ) || section.ends_with(".dependencies]")
        {
            dependency_rows += 1;
        }
    }
    (dependency_rows, target_rows)
}

fn rust_item_line(line: &str) -> bool {
    let mut text = line.split("//").next().unwrap_or_default().trim();
    if text.is_empty() || text.starts_with("#!") || text.starts_with("#[") {
        return false;
    }
    if let Some(rest) = text.strip_prefix("pub ") {
        text = rest.trim_start();
    } else if text.starts_with("pub(")
        && let Some((_, rest)) = text.split_once(") ")
    {
        text = rest.trim_start();
    }
    for qualifier in ["const ", "async ", "default "] {
        if let Some(rest) = text.strip_prefix(qualifier) {
            text = rest.trim_start();
        }
    }
    [
        "fn ",
        "struct ",
        "enum ",
        "trait ",
        "impl ",
        "mod ",
        "type ",
        "const ",
        "static ",
        "use ",
        "extern crate ",
        "macro_rules!",
    ]
    .iter()
    .any(|prefix| text.starts_with(prefix))
}

fn auto_target_kind(path: &str) -> Option<&'static str> {
    if path == "crates/fln-anvil/src/main.rs" {
        Some("src/main.rs")
    } else if path == "crates/fln-anvil/build.rs" {
        Some("build.rs")
    } else if path.starts_with("crates/fln-anvil/src/bin/") && path.ends_with(".rs") {
        Some("src/bin")
    } else if path.starts_with("crates/fln-anvil/tests/") && path.ends_with(".rs") {
        Some("tests")
    } else if path.starts_with("crates/fln-anvil/benches/") && path.ends_with(".rs") {
        Some("benches")
    } else if path.starts_with("crates/fln-anvil/examples/") && path.ends_with(".rs") {
        Some("examples")
    } else {
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AnvilInventory {
    package_found: bool,
    implicit_lib_found: bool,
    boundary_ids: BTreeSet<String>,
    extra_rust_sources: BTreeSet<String>,
    rust_items: BTreeSet<String>,
    auto_targets: BTreeSet<String>,
    dependency_rows: usize,
    manifest_target_rows: usize,
    workspace_consumers: BTreeSet<String>,
}

fn anvil_inventory(tree: &CensusTree) -> AnvilInventory {
    let manifest = tree
        .files
        .get("crates/fln-anvil/Cargo.toml")
        .map(String::as_str)
        .unwrap_or_default();
    let (dependency_rows, manifest_target_rows) = manifest_facts(manifest);
    let package_found = manifest
        .lines()
        .any(|line| line.trim() == "name = \"fln-anvil\"");
    let implicit_lib_found = tree.files.contains_key("crates/fln-anvil/src/lib.rs");

    let mut boundary_ids = BTreeSet::new();
    let mut extra_rust_sources = BTreeSet::new();
    let mut rust_items = BTreeSet::new();
    let mut auto_targets = BTreeSet::new();
    let mut workspace_consumers = BTreeSet::new();

    for (path, contents) in &tree.files {
        if path.starts_with("crates/fln-anvil/") && path.ends_with(".rs") {
            if path != "crates/fln-anvil/src/lib.rs" {
                extra_rust_sources.insert(path.clone());
            }
            if let Some(kind) = auto_target_kind(path) {
                auto_targets.insert(format!("{kind}:{path}"));
            }
            for (line_number, line) in production_prefix(contents).lines().enumerate() {
                if let Some((_, id)) = line.split_once(CERTIFICATE_BOUNDARY_MARKER) {
                    boundary_ids.insert(id.trim().to_owned());
                }
                if rust_item_line(line) {
                    rust_items.insert(format!("{path}:{}", line_number + 1));
                }
            }
            continue;
        }

        if !path.starts_with("crates/") || path.starts_with("crates/fln-anvil/") {
            continue;
        }
        if path.ends_with("/Cargo.toml") {
            let mut section = "";
            for line in contents.lines() {
                let trimmed = line.split('#').next().unwrap_or_default().trim();
                if trimmed.starts_with('[') && trimmed.ends_with(']') {
                    section = trimmed;
                    continue;
                }
                let dependency_section = matches!(
                    section,
                    "[dependencies]" | "[dev-dependencies]" | "[build-dependencies]"
                ) || section.ends_with(".dependencies]");
                if dependency_section && trimmed.contains("fln-anvil") {
                    workspace_consumers.insert(path.clone());
                }
            }
        } else if path.contains("/src/")
            && path.ends_with(".rs")
            && production_prefix(contents).contains("fln_anvil")
        {
            workspace_consumers.insert(path.clone());
        }
    }

    AnvilInventory {
        package_found,
        implicit_lib_found,
        boundary_ids,
        extra_rust_sources,
        rust_items,
        auto_targets,
        dependency_rows,
        manifest_target_rows,
        workspace_consumers,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FunctionSite {
    path: String,
    line: usize,
    name: String,
    header: String,
    marker: Option<(bool, String)>,
}

fn function_name(line: &str) -> Option<String> {
    let trimmed = line.trim_start();
    if trimmed.starts_with("//") || trimmed.starts_with('#') {
        return None;
    }
    let at = trimmed.find("fn ")?;
    let prefix = &trimmed[..at];
    if !prefix.trim().is_empty()
        && !prefix
            .split_whitespace()
            .all(|word| matches!(word, "pub" | "const" | "async" | "default"))
        && !prefix.starts_with("pub(")
    {
        return None;
    }
    let after = &trimmed[at + 3..];
    let name: String = after
        .chars()
        .take_while(|character| character.is_ascii_alphanumeric() || *character == '_')
        .collect();
    (!name.is_empty()).then_some(name)
}

fn function_sites(path: &str, source: &str) -> Vec<FunctionSite> {
    let production = production_prefix(source);
    let lines: Vec<&str> = production.lines().collect();
    let mut pending_marker: Option<(bool, String)> = None;
    let mut sites = Vec::new();
    let mut index = 0usize;
    while index < lines.len() {
        let line = lines[index];
        if let Some((_, id)) = line.split_once(CERTIFICATE_BOUNDARY_MARKER) {
            pending_marker = Some((true, id.trim().to_owned()));
            index += 1;
            continue;
        }
        if let Some((_, id)) = line.split_once(CERTIFICATE_ALIAS_MARKER) {
            pending_marker = Some((false, id.trim().to_owned()));
            index += 1;
            continue;
        }
        let Some(name) = function_name(line) else {
            index += 1;
            continue;
        };
        let start = index;
        let mut header = line.trim().to_owned();
        while !header.contains('{') && !header.ends_with(';') && index + 1 < lines.len() {
            index += 1;
            header.push(' ');
            header.push_str(lines[index].trim());
        }
        sites.push(FunctionSite {
            path: path.to_owned(),
            line: start + 1,
            name,
            header,
            marker: pending_marker.take(),
        });
        index += 1;
    }
    sites
}

#[derive(Debug, Clone, Copy)]
struct ExpectedBoundary {
    id: &'static str,
    path: &'static str,
    function: &'static str,
}

const EXPECTED_VERDICT_BOUNDARIES: [ExpectedBoundary; 6] = [
    ExpectedBoundary {
        id: "structured-proof-construction",
        path: "crates/fln-verdict/src/lib.rs",
        function: "new",
    },
    ExpectedBoundary {
        id: "canonical-proof-decode",
        path: "crates/fln-verdict/src/lib.rs",
        function: "from_canonical_bytes",
    },
    ExpectedBoundary {
        id: "streaming-semantic-checker",
        path: "crates/fln-verdict/src/checker.rs",
        function: "check_unsat_streams",
    },
    ExpectedBoundary {
        id: "solver-finish-unsat",
        path: "crates/fln-verdict/src/solver.rs",
        function: "finish_unsat",
    },
    ExpectedBoundary {
        id: "reflected-artifact-construction",
        path: "crates/fln-verdict/src/reflection.rs",
        function: "from_bitblast_unsat",
    },
    ExpectedBoundary {
        id: "kernel-capability-publication",
        path: "crates/fln-verdict/src/reflection.rs",
        function: "publish_reflected_theorem",
    },
];

const EXPECTED_VERDICT_ALIASES: [ExpectedBoundary; 1] = [ExpectedBoundary {
    id: "streaming-semantic-checker",
    path: "crates/fln-verdict/src/checker.rs",
    function: "check_unsat_streams_with_cancel",
}];

#[derive(Debug, Clone, PartialEq, Eq)]
struct VerdictInventory {
    source_files: BTreeSet<String>,
    boundaries: BTreeMap<String, (String, String)>,
    aliases: BTreeMap<String, (String, String)>,
    unmarked_sensitive_functions: BTreeSet<String>,
    sensitive_call_counts: BTreeMap<&'static str, usize>,
    marker_faults: Vec<String>,
}

fn verdict_inventory(tree: &CensusTree) -> VerdictInventory {
    let mut source_files = BTreeSet::new();
    let mut boundaries = BTreeMap::new();
    let mut aliases = BTreeMap::new();
    let mut unmarked_sensitive_functions = BTreeSet::new();
    let mut sensitive_call_counts = BTreeMap::from([
        ("check_unsat_streams_with_cancel(", 0usize),
        ("UnsatProof::new(", 0usize),
        ("UnsatProof::from_canonical_bytes(", 0usize),
        ("ReflectedTheoremArtifact::from_bitblast_unsat(", 0usize),
    ]);
    let mut marker_faults = Vec::new();

    for (path, source) in &tree.files {
        if !path.starts_with("crates/fln-verdict/src/") || !path.ends_with(".rs") {
            continue;
        }
        source_files.insert(path.clone());
        let production = production_prefix(source);
        for line in production.lines() {
            let trimmed = line.trim_start();
            if trimmed.starts_with("//") {
                continue;
            }
            for (needle, count) in &mut sensitive_call_counts {
                *count += line.matches(*needle).count();
            }
        }

        for site in function_sites(path, source) {
            match &site.marker {
                Some((true, id)) => {
                    if boundaries
                        .insert(id.clone(), (site.path.clone(), site.name.clone()))
                        .is_some()
                    {
                        marker_faults.push(format!("duplicate-boundary:{id}"));
                    }
                }
                Some((false, id)) => {
                    let key = format!("{id}:{}", site.name);
                    if aliases
                        .insert(key.clone(), (site.path.clone(), site.name.clone()))
                        .is_some()
                    {
                        marker_faults.push(format!("duplicate-alias:{key}"));
                    }
                }
                None => {}
            }

            let sensitive = [
                "UnsatProof",
                "CheckedUnsat",
                "ReflectedTheoremArtifact",
                "ProofCheckOutcome",
            ]
            .iter()
            .any(|needle| site.header.contains(needle))
                || matches!(
                    site.name.as_str(),
                    "check_unsat_streams"
                        | "check_unsat_streams_with_cancel"
                        | "finish_unsat"
                        | "publish_reflected_theorem"
                        | "from_bitblast_unsat"
                );
            let allowed_projection =
                site.path == "crates/fln-verdict/src/solver.rs" && site.name == "proof";
            if sensitive && site.marker.is_none() && !allowed_projection {
                unmarked_sensitive_functions
                    .insert(format!("{}:{}:{}", site.path, site.line, site.name));
            }
        }
    }

    VerdictInventory {
        source_files,
        boundaries,
        aliases,
        unmarked_sensitive_functions,
        sensitive_call_counts,
        marker_faults,
    }
}

fn census_findings(tree: &CensusTree) -> Vec<String> {
    let mut findings = Vec::new();
    let anvil = anvil_inventory(tree);
    if !anvil.package_found {
        findings.push("anvil-sentinel: package manifest was not resolved".to_owned());
    }
    if !anvil.implicit_lib_found {
        findings.push("anvil-sentinel: implicit library root was not resolved".to_owned());
    }
    match disclosed_cardinality(tree, ANVIL_CENSUS) {
        Ok(disclosed) if disclosed != anvil.boundary_ids.len() => findings.push(format!(
            "anvil-cardinality: census discloses {disclosed}, production markers derive {}",
            anvil.boundary_ids.len()
        )),
        Err(error) => findings.push(format!("anvil-cardinality: {error}")),
        Ok(_) => {}
    }
    if !anvil.extra_rust_sources.is_empty() {
        findings.push(format!(
            "anvil-footprint: extra Rust sources {:?}",
            anvil.extra_rust_sources
        ));
    }
    if !anvil.rust_items.is_empty() {
        findings.push(format!(
            "anvil-footprint: Rust items/modules {:?}",
            anvil.rust_items
        ));
    }
    if !anvil.auto_targets.is_empty() {
        findings.push(format!(
            "anvil-footprint: Cargo auto-discovery targets {:?}",
            anvil.auto_targets
        ));
    }
    if anvil.dependency_rows != 0 {
        findings.push(format!(
            "anvil-footprint: {} dependency rows",
            anvil.dependency_rows
        ));
    }
    if anvil.manifest_target_rows != 0 {
        findings.push(format!(
            "anvil-footprint: {} explicit manifest target rows",
            anvil.manifest_target_rows
        ));
    }
    if !anvil.workspace_consumers.is_empty() {
        findings.push(format!(
            "anvil-footprint: workspace consumers {:?}",
            anvil.workspace_consumers
        ));
    }

    let verdict = verdict_inventory(tree);
    if verdict.source_files.len() < 6 {
        findings.push(format!(
            "verdict-sentinel: only {} production source files were resolved",
            verdict.source_files.len()
        ));
    }
    if !verdict.marker_faults.is_empty() {
        findings.push(format!("verdict-markers: {:?}", verdict.marker_faults));
    }
    let expected: BTreeMap<String, (String, String)> = EXPECTED_VERDICT_BOUNDARIES
        .iter()
        .map(|site| {
            (
                site.id.to_owned(),
                (site.path.to_owned(), site.function.to_owned()),
            )
        })
        .collect();
    if verdict.boundaries != expected {
        findings.push(format!(
            "verdict-boundaries: expected {expected:?}, derived {:?}",
            verdict.boundaries
        ));
    }
    let expected_aliases: BTreeMap<String, (String, String)> = EXPECTED_VERDICT_ALIASES
        .iter()
        .map(|site| {
            (
                format!("{}:{}", site.id, site.function),
                (site.path.to_owned(), site.function.to_owned()),
            )
        })
        .collect();
    if verdict.aliases != expected_aliases {
        findings.push(format!(
            "verdict-aliases: expected {expected_aliases:?}, derived {:?}",
            verdict.aliases
        ));
    }
    if !verdict.unmarked_sensitive_functions.is_empty() {
        findings.push(format!(
            "verdict-unmarked: certificate-sensitive functions {:?}",
            verdict.unmarked_sensitive_functions
        ));
    }
    let expected_calls = BTreeMap::from([
        ("check_unsat_streams_with_cancel(", 3usize),
        ("UnsatProof::new(", 1usize),
        ("UnsatProof::from_canonical_bytes(", 0usize),
        ("ReflectedTheoremArtifact::from_bitblast_unsat(", 1usize),
    ]);
    if verdict.sensitive_call_counts != expected_calls {
        findings.push(format!(
            "verdict-calls: expected {expected_calls:?}, derived {:?}",
            verdict.sensitive_call_counts
        ));
    }
    match disclosed_cardinality(tree, VERDICT_CENSUS) {
        Ok(disclosed) if disclosed != verdict.boundaries.len() => findings.push(format!(
            "verdict-cardinality: census discloses {disclosed}, production sites derive {}",
            verdict.boundaries.len()
        )),
        Err(error) => findings.push(format!("verdict-cardinality: {error}")),
        Ok(_) => {}
    }
    findings
}

fn assert_mutant_finding(tree: &CensusTree, needle: &str) {
    let findings = census_findings(tree);
    assert!(
        findings.iter().any(|finding| finding.contains(needle)),
        "mutant survived without its intended {needle:?} finding: {findings:?}"
    );
}

#[test]
fn fl_inv_06_certificate_censuses_match_the_derived_production_cardinalities() {
    let tree = real_census_tree().expect("FL-INV-06 census inputs must be readable");
    let findings = census_findings(&tree);
    assert!(
        findings.is_empty(),
        "FL-INV-06 census cardinality join failed: {findings:#?}"
    );
}

#[test]
fn fl_inv_06_census_mutants_change_the_referent_and_die() {
    let baseline = real_census_tree().expect("FL-INV-06 census inputs must be readable");
    assert!(
        census_findings(&baseline).is_empty(),
        "mutation campaign requires a clean positive control"
    );
    let base_anvil = anvil_inventory(&baseline);
    let base_verdict = verdict_inventory(&baseline);

    let mut auto_bench = baseline.clone();
    auto_bench.insert(
        "crates/fln-anvil/benches/probe.rs",
        "#![forbid(unsafe_code)]\nfn main() {}\n",
    );
    assert_eq!(
        anvil_inventory(&auto_bench).auto_targets.len(),
        base_anvil.auto_targets.len() + 1,
        "auto-discovered benches/*.rs mutant did not enter the derived inventory"
    );
    assert_mutant_finding(&auto_bench, "Cargo auto-discovery targets");

    let mut inline_item = baseline.clone();
    inline_item.edit("crates/fln-anvil/src/lib.rs", |source| {
        format!("{source}\n\npub fn probe_engine() {{}}\n")
    });
    assert_eq!(
        anvil_inventory(&inline_item).rust_items.len(),
        base_anvil.rust_items.len() + 1,
        "inline Anvil item mutant did not enter the derived inventory"
    );
    assert_mutant_finding(&inline_item, "Rust items/modules");

    let mut dependency = baseline.clone();
    dependency.edit("crates/fln-anvil/Cargo.toml", |manifest| {
        manifest.replacen(
            "[dependencies]",
            "[dependencies]\nfln-core = { path = \"../fln-core\" }",
            1,
        )
    });
    assert_eq!(
        anvil_inventory(&dependency).dependency_rows,
        base_anvil.dependency_rows + 1,
        "Anvil dependency mutant did not enter the derived inventory"
    );
    assert_mutant_finding(&dependency, "dependency rows");

    let mut consumer = baseline.clone();
    consumer.edit("crates/fln-core/src/lib.rs", |source| {
        format!("{source}\n\npub fn probe_anvil(_: fln_anvil::Probe) {{}}\n")
    });
    assert_eq!(
        anvil_inventory(&consumer).workspace_consumers.len(),
        base_anvil.workspace_consumers.len() + 1,
        "external Anvil consumer mutant did not enter the derived inventory"
    );
    assert_mutant_finding(&consumer, "workspace consumers");

    let mut seventh = baseline.clone();
    seventh.edit("crates/fln-verdict/src/checker.rs", |source| {
        let injected = "\n// FLN-FL-INV-06-CERTIFICATE-BOUNDARY: foreign-proof-consumer\n\
                        pub fn accept_foreign_proof(proof: UnsatProof) -> ProofCheckOutcome {\n\
                            check_unsat_streams_with_cancel(&[][..], proof.to_canonical_bytes().as_slice(), \
                                                           ProofCheckLimits::default(), || false)\n\
                        }\n";
        match source.split_once("\n#[cfg(test)]") {
            Some((production, tests)) => format!("{production}{injected}\n#[cfg(test)]{tests}"),
            None => format!("{source}{injected}"),
        }
    });
    assert_eq!(
        verdict_inventory(&seventh).boundaries.len(),
        base_verdict.boundaries.len() + 1,
        "seventh Verdict consumer mutant did not enter the derived referent"
    );
    assert_mutant_finding(&seventh, "verdict-boundaries");

    let mut removed = baseline.clone();
    removed.edit("crates/fln-verdict/src/reflection.rs", |source| {
        source.replacen(
            "// FLN-FL-INV-06-CERTIFICATE-BOUNDARY: reflected-artifact-construction\n",
            "",
            1,
        )
    });
    assert_eq!(
        verdict_inventory(&removed).boundaries.len() + 1,
        base_verdict.boundaries.len(),
        "removed Verdict join mutant did not leave the derived referent"
    );
    assert_mutant_finding(&removed, "verdict-boundaries");

    let mut anvil_count = baseline.clone();
    anvil_count.edit(ANVIL_CENSUS, |document| {
        document.replacen(
            "Certificate-accepting path cardinality: `0`.",
            "Certificate-accepting path cardinality: `1`.",
            1,
        )
    });
    assert_mutant_finding(&anvil_count, "anvil-cardinality");

    let mut verdict_count = baseline;
    verdict_count.edit(VERDICT_CENSUS, |document| {
        document.replacen(
            "Certificate-accepting path cardinality: `6`.",
            "Certificate-accepting path cardinality: `5`.",
            1,
        )
    });
    assert_mutant_finding(&verdict_count, "verdict-cardinality");
}
