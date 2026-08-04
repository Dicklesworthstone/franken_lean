#![forbid(unsafe_code)]

use fln_verdict::{
    CNF_SCHEMA, Clause, ClauseId, Cnf, DETERMINISTIC_CDCL_POLICY, InputClause, Literal, Polarity,
    ProofCheckLimits, ProofCheckOutcome, ProofRefusal, ProofStream, SchemaError, SchemaLimits,
    SolverLimits, SolverOutcome, UNSAT_PROOF_SCHEMA, UnsatProof, VERDICT_SCHEMA_VERSION,
    VariableId, check_unsat_streams, solve,
};

const CORPUS: &str = include_str!("corpus/certificate_goldens.hex");
const PROVENANCE: &str = include_str!("corpus/CERTIFICATE_GOLDENS_PROVENANCE.md");
const PRODUCER_COMMIT: &str = "25c0244fc5f6823f5dbbcf9357e7ba34d9c32e15";
const VERSION_OFFSET: usize = 9;
const GOLDEN_ROWS: usize = 3;

#[derive(Debug, Clone, Copy)]
struct GoldenRow<'a> {
    name: &'a str,
    input: &'a str,
    seed: u64,
    solver: &'a str,
    producer_commit: &'a str,
    policy: &'a str,
    cnf_schema: &'a str,
    proof_schema: &'a str,
    cnf_hex: &'a str,
    proof_hex: &'a str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GoldenMismatch {
    Byte { at: usize, expected: u8, actual: u8 },
    Length { expected: usize, actual: usize },
}

#[derive(Debug, Clone, Copy)]
struct Seeded {
    state: u64,
}

impl Seeded {
    const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut mixed = self.state;
        mixed = (mixed ^ (mixed >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        mixed = (mixed ^ (mixed >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        mixed ^ (mixed >> 31)
    }

    fn shuffle<T>(&mut self, values: &mut [T]) {
        for upper in (1..values.len()).rev() {
            let modulus = (upper as u64) + 1;
            let selected = (self.next() % modulus) as usize;
            values.swap(upper, selected);
        }
    }
}

fn parse_corpus() -> Result<Vec<GoldenRow<'static>>, String> {
    let mut rows = Vec::new();
    for (line_index, line) in CORPUS.lines().enumerate() {
        let line_number = line_index + 1;
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields = line.split('|').collect::<Vec<_>>();
        if fields.len() != 10 {
            return Err(format!(
                "certificate golden line {line_number} has {} fields, expected 10",
                fields.len()
            ));
        }
        let seed = fields[2]
            .strip_prefix("0x")
            .ok_or_else(|| format!("certificate golden line {line_number} seed lacks 0x prefix"))
            .and_then(|raw| {
                u64::from_str_radix(raw, 16).map_err(|_| {
                    format!("certificate golden line {line_number} seed is not hexadecimal")
                })
            })?;
        rows.push(GoldenRow {
            name: fields[0],
            input: fields[1],
            seed,
            solver: fields[3],
            producer_commit: fields[4],
            policy: fields[5],
            cnf_schema: fields[6],
            proof_schema: fields[7],
            cnf_hex: fields[8],
            proof_hex: fields[9],
        });
    }
    Ok(rows)
}

fn variable(raw: u32) -> Result<VariableId, String> {
    VariableId::new(raw).map_err(|error| format!("fixture variable {raw} is invalid: {error}"))
}

fn clause_id(raw: u64) -> Result<ClauseId, String> {
    ClauseId::new(raw).map_err(|error| format!("fixture clause id {raw} is invalid: {error}"))
}

fn seeded_cnf(
    variable_count: u32,
    mut raw_clauses: Vec<Vec<(u32, Polarity)>>,
    seed: u64,
) -> Result<Cnf, String> {
    let mut seeded = Seeded::new(seed);
    for literals in &mut raw_clauses {
        seeded.shuffle(literals);
    }
    seeded.shuffle(&mut raw_clauses);

    let mut clauses = Vec::new();
    clauses
        .try_reserve(raw_clauses.len())
        .map_err(|_| "fixture clause allocation was refused".to_owned())?;
    for (index, raw_literals) in raw_clauses.into_iter().enumerate() {
        let mut literals = Vec::new();
        literals
            .try_reserve(raw_literals.len())
            .map_err(|_| "fixture literal allocation was refused".to_owned())?;
        for (raw, polarity) in raw_literals {
            literals.push(Literal::new(variable(raw)?, polarity));
        }
        let clause =
            Clause::new(literals).map_err(|error| format!("fixture clause is invalid: {error}"))?;
        let raw_id = u64::try_from(index)
            .map_err(|_| "fixture clause index does not fit u64".to_owned())?
            .checked_add(1)
            .ok_or_else(|| "fixture clause id overflowed".to_owned())?;
        clauses.push(InputClause::new(clause_id(raw_id)?, clause));
    }
    Cnf::new(variable_count, clauses, SchemaLimits::default())
        .map_err(|error| format!("fixture CNF is invalid: {error}"))
}

fn fixture_cnf(input: &str, seed: u64) -> Result<Cnf, String> {
    match input {
        "unit-conflict/v1" => seeded_cnf(
            1,
            vec![vec![(1, Polarity::Positive)], vec![(1, Polarity::Negative)]],
            seed,
        ),
        "xor-square/v1" => seeded_cnf(
            2,
            vec![
                vec![(1, Polarity::Positive), (2, Polarity::Positive)],
                vec![(1, Polarity::Positive), (2, Polarity::Negative)],
                vec![(1, Polarity::Negative), (2, Polarity::Positive)],
                vec![(1, Polarity::Negative), (2, Polarity::Negative)],
            ],
            seed,
        ),
        "pigeonhole-3-2/v1" => {
            let pigeons = 3_u32;
            let holes = 2_u32;
            let variable_for = |pigeon: u32, hole: u32| pigeon * holes + hole + 1;
            let mut clauses = Vec::new();
            for pigeon in 0..pigeons {
                clauses.push(
                    (0..holes)
                        .map(|hole| (variable_for(pigeon, hole), Polarity::Positive))
                        .collect(),
                );
            }
            for hole in 0..holes {
                for first in 0..pigeons {
                    for second in first + 1..pigeons {
                        clauses.push(vec![
                            (variable_for(first, hole), Polarity::Negative),
                            (variable_for(second, hole), Polarity::Negative),
                        ]);
                    }
                }
            }
            seeded_cnf(pigeons * holes, clauses, seed)
        }
        other => Err(format!("unknown golden fixture input {other}")),
    }
}

fn decode_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn decode_hex(encoded: &str) -> Result<Vec<u8>, String> {
    if !encoded.len().is_multiple_of(2) {
        return Err("golden hex has odd length".to_owned());
    }
    let mut bytes = Vec::new();
    bytes
        .try_reserve(encoded.len() / 2)
        .map_err(|_| "golden hex allocation was refused".to_owned())?;
    for pair in encoded.as_bytes().as_chunks::<2>().0 {
        let high = decode_nibble(pair[0]).ok_or_else(|| "golden hex is invalid".to_owned())?;
        let low = decode_nibble(pair[1]).ok_or_else(|| "golden hex is invalid".to_owned())?;
        bytes.push((high << 4) | low);
    }
    Ok(bytes)
}

fn compare_exact(expected: &[u8], actual: &[u8]) -> Result<(), GoldenMismatch> {
    for (at, (expected, actual)) in expected.iter().zip(actual).enumerate() {
        if expected != actual {
            return Err(GoldenMismatch::Byte {
                at,
                expected: *expected,
                actual: *actual,
            });
        }
    }
    if expected.len() != actual.len() {
        return Err(GoldenMismatch::Length {
            expected: expected.len(),
            actual: actual.len(),
        });
    }
    Ok(())
}

fn solve_unsat(cnf: &Cnf) -> Result<fln_verdict::CheckedUnsat, String> {
    match solve(cnf, SolverLimits::default()) {
        SolverOutcome::Unsat { artifact, .. } => Ok(artifact),
        outcome => Err(format!(
            "golden input did not produce a checked UNSAT artifact: {outcome:?}"
        )),
    }
}

fn schema_name(name: &str, version: u16) -> String {
    format!("{name}/{version}")
}

#[test]
fn golden_certificates_are_byte_exact_and_round_trip() -> Result<(), String> {
    let rows = parse_corpus()?;
    if rows.len() != GOLDEN_ROWS {
        return Err(format!(
            "certificate golden row count drifted: expected {GOLDEN_ROWS}, found {}",
            rows.len()
        ));
    }

    for row in rows {
        let expected_solver = format!("fln-verdict@{}", env!("CARGO_PKG_VERSION"));
        if row.solver != expected_solver
            || row.producer_commit != PRODUCER_COMMIT
            || row.policy != DETERMINISTIC_CDCL_POLICY.policy_id
            || row.cnf_schema != schema_name(CNF_SCHEMA.name, CNF_SCHEMA.version)
            || row.proof_schema != schema_name(UNSAT_PROOF_SCHEMA.name, UNSAT_PROOF_SCHEMA.version)
        {
            return Err(format!(
                "{} has stale or incomplete provenance: {row:?}",
                row.name
            ));
        }

        let cnf = fixture_cnf(row.input, row.seed)?;
        let artifact = solve_unsat(&cnf)?;
        let expected_cnf = decode_hex(row.cnf_hex)?;
        let expected_proof = decode_hex(row.proof_hex)?;
        compare_exact(&expected_cnf, artifact.cnf_bytes())
            .map_err(|mismatch| format!("{} CNF golden drift: {mismatch:?}", row.name))?;
        compare_exact(&expected_proof, artifact.proof_bytes())
            .map_err(|mismatch| format!("{} proof golden drift: {mismatch:?}", row.name))?;

        let decoded_cnf = Cnf::from_canonical_bytes(&expected_cnf, SchemaLimits::default())
            .map_err(|error| format!("{} golden CNF failed to decode: {error}", row.name))?;
        compare_exact(&expected_cnf, &decoded_cnf.to_canonical_bytes()).map_err(|mismatch| {
            format!(
                "{} decoded CNF failed byte round-trip: {mismatch:?}",
                row.name
            )
        })?;
        let decoded_proof = UnsatProof::from_canonical_bytes(
            &expected_proof,
            &decoded_cnf,
            SchemaLimits::default(),
        )
        .map_err(|error| format!("{} golden proof failed to decode: {error}", row.name))?;
        compare_exact(&expected_proof, &decoded_proof.to_canonical_bytes()).map_err(
            |mismatch| {
                format!(
                    "{} decoded proof failed byte round-trip: {mismatch:?}",
                    row.name
                )
            },
        )?;

        match check_unsat_streams(
            &expected_cnf[..],
            &expected_proof[..],
            ProofCheckLimits::default(),
        ) {
            ProofCheckOutcome::Verified(receipt) if receipt == *artifact.receipt() => {}
            outcome => {
                return Err(format!(
                    "{} golden proof was not independently verified: {outcome:?}",
                    row.name
                ));
            }
        }
    }

    Ok(())
}

#[test]
fn every_golden_has_documented_provenance() -> Result<(), String> {
    for row in parse_corpus()? {
        let seed = format!("0x{:016x}", row.seed);
        for required in [
            row.name,
            row.input,
            &seed,
            row.solver,
            row.producer_commit,
            row.policy,
            row.cnf_schema,
            row.proof_schema,
        ] {
            if !PROVENANCE.contains(required) {
                return Err(format!(
                    "{} provenance is missing required value {required}",
                    row.name
                ));
            }
        }
    }
    Ok(())
}

#[test]
fn unknown_cnf_and_proof_versions_are_refused_typed() -> Result<(), String> {
    let cnf = fixture_cnf("xor-square/v1", 0xbb67_ae85_84ca_a73b)?;
    let artifact = solve_unsat(&cnf)?;
    let unknown = u16::MAX;

    let mut future_cnf = artifact.cnf_bytes().to_vec();
    future_cnf[VERSION_OFFSET..VERSION_OFFSET + 2].copy_from_slice(&unknown.to_le_bytes());
    if Cnf::from_canonical_bytes(&future_cnf, SchemaLimits::default())
        != Err(SchemaError::UnsupportedVersion {
            schema: CNF_SCHEMA,
            found: unknown,
            supported: VERDICT_SCHEMA_VERSION,
        })
    {
        return Err("producer decoder did not refuse the unknown CNF version".to_owned());
    }
    if check_unsat_streams(
        &future_cnf[..],
        artifact.proof_bytes(),
        ProofCheckLimits::default(),
    ) != ProofCheckOutcome::Refused(ProofRefusal::UnsupportedVersion {
        stream: ProofStream::Cnf,
        found: unknown,
        supported: VERDICT_SCHEMA_VERSION,
    }) {
        return Err("independent checker did not refuse the unknown CNF version".to_owned());
    }

    let mut future_proof = artifact.proof_bytes().to_vec();
    future_proof[VERSION_OFFSET..VERSION_OFFSET + 2].copy_from_slice(&unknown.to_le_bytes());
    if UnsatProof::from_canonical_bytes(&future_proof, &cnf, SchemaLimits::default())
        != Err(SchemaError::UnsupportedVersion {
            schema: UNSAT_PROOF_SCHEMA,
            found: unknown,
            supported: VERDICT_SCHEMA_VERSION,
        })
    {
        return Err("producer decoder did not refuse the unknown proof version".to_owned());
    }
    if check_unsat_streams(
        artifact.cnf_bytes(),
        &future_proof[..],
        ProofCheckLimits::default(),
    ) != ProofCheckOutcome::Refused(ProofRefusal::UnsupportedVersion {
        stream: ProofStream::Proof,
        found: unknown,
        supported: VERDICT_SCHEMA_VERSION,
    }) {
        return Err("independent checker did not refuse the unknown proof version".to_owned());
    }
    Ok(())
}

#[test]
fn deliberate_certificate_byte_drift_is_named_and_refused() -> Result<(), String> {
    let cnf = fixture_cnf("unit-conflict/v1", 0x6a09_e667_f3bc_c909)?;
    let artifact = solve_unsat(&cnf)?;
    let expected = artifact.proof_bytes();
    let mut drifted = expected.to_vec();
    let at = drifted
        .len()
        .checked_sub(1)
        .ok_or_else(|| "solver emitted an empty proof stream".to_owned())?;
    drifted[at] ^= 1;
    match compare_exact(expected, &drifted) {
        Err(GoldenMismatch::Byte {
            at: found,
            expected,
            actual,
        }) if found == at && expected != actual => Ok(()),
        outcome => Err(format!(
            "golden comparator did not name and refuse deliberate drift: {outcome:?}"
        )),
    }
}

#[test]
fn golden_suite_has_no_self_regeneration_path() {
    let source = include_str!("golden_certificates.rs");
    for forbidden in [
        concat!("UPDATE_", "GOLDENS"),
        concat!("std::", "fs"),
        concat!("File::", "create"),
        concat!("Open", "Options"),
        concat!("write", "_all"),
    ] {
        assert!(
            !source.contains(forbidden),
            "golden suite gained a forbidden self-regeneration API: {forbidden}"
        );
    }
}
