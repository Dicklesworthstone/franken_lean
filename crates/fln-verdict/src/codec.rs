//! Versioned canonical codecs for Verdict artifacts.
//!
//! CNF and model values use bounded slice decoding. Proofs use length-framed records
//! read from [`std::io::Read`]: only one bounded record is buffered at a time while
//! the final, itself bounded, artifact is assembled. Every decoded value is rebuilt
//! through the validating schema constructors. Slice artifacts and individual proof
//! records must re-encode byte-for-byte, so alternate encodings are refused.

use std::io::{ErrorKind, Read};

use fln_hash::canon::{CanonError, CanonReader, CanonWriter, SchemaId};
use fln_hash::domain::Digest;

use crate::schema::{
    CanonicalClause, CanonicalCnf, ClauseId, CnfRoot, InconclusiveReason, Literal, Polarity,
    ProofAction, RatHint, SatModel, UnsatProof, VariableId, VerdictError, VerdictLimits,
    VerdictResource,
};

pub const CNF_SCHEMA: SchemaId = SchemaId {
    name: "fln.verdict.cnf",
    version: 1,
};
pub const SAT_MODEL_SCHEMA: SchemaId = SchemaId {
    name: "fln.verdict.sat-model",
    version: 1,
};
pub const UNSAT_PROOF_SCHEMA: SchemaId = SchemaId {
    name: "fln.verdict.unsat-proof",
    version: 1,
};

const FEATURES_V1: u64 = 0;
const ACTION_ADD_RUP: u8 = 0;
const ACTION_ADD_RAT: u8 = 1;
const ACTION_DELETE: u8 = 2;
const RECORD_CONCLUSION: u8 = 3;

/// Total decode refusal over arbitrary bytes and fallible readers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerdictCodecError {
    Canonical(CanonError),
    Validation(VerdictError),
    SchemaNameMismatch {
        expected: &'static str,
    },
    UnsupportedSchemaVersion {
        schema: &'static str,
        found: u16,
        supported: u16,
    },
    UnsupportedExtensionBits {
        bits: u64,
    },
    UnknownPolarity {
        tag: u8,
    },
    UnknownRecordOpcode {
        opcode: u8,
    },
    CnfRootMismatch {
        expected: CnfRoot,
        actual: CnfRoot,
    },
    VariableCountMismatch {
        expected: u64,
        actual: u64,
    },
    NonCanonicalEncoding,
    Truncated {
        at: u128,
    },
    MissingConclusion,
    TrailingBytes,
    ReadFailure {
        kind: ErrorKind,
    },
    Inconclusive(InconclusiveReason),
}

impl std::fmt::Display for VerdictCodecError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Canonical(error) => error.fmt(formatter),
            Self::Validation(error) => error.fmt(formatter),
            Self::SchemaNameMismatch { expected } => {
                write!(
                    formatter,
                    "canonical schema name does not match `{expected}`"
                )
            }
            Self::UnsupportedSchemaVersion {
                schema,
                found,
                supported,
            } => write!(
                formatter,
                "unsupported `{schema}` schema version {found}; supported={supported}"
            ),
            Self::UnsupportedExtensionBits { bits } => {
                write!(
                    formatter,
                    "unsupported verdict extension bits 0x{bits:016x}"
                )
            }
            Self::UnknownPolarity { tag } => {
                write!(formatter, "unknown literal polarity tag {tag}")
            }
            Self::UnknownRecordOpcode { opcode } => {
                write!(formatter, "unknown proof-record opcode {opcode}")
            }
            Self::CnfRootMismatch { expected, actual } => {
                write!(
                    formatter,
                    "CNF root mismatch: expected={expected}, actual={actual}"
                )
            }
            Self::VariableCountMismatch { expected, actual } => write!(
                formatter,
                "variable-count mismatch: expected={expected}, actual={actual}"
            ),
            Self::NonCanonicalEncoding => {
                formatter.write_str("artifact has a non-canonical encoding")
            }
            Self::Truncated { at } => {
                write!(formatter, "artifact is truncated at byte {at}")
            }
            Self::MissingConclusion => {
                formatter.write_str("proof stream ended before its conclusion record")
            }
            Self::TrailingBytes => formatter.write_str("artifact has trailing bytes"),
            Self::ReadFailure { kind } => {
                write!(formatter, "artifact reader failed with {kind:?}")
            }
            Self::Inconclusive(reason) => {
                write!(formatter, "artifact decoding was inconclusive: {reason:?}")
            }
        }
    }
}

impl std::error::Error for VerdictCodecError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Validation(error) => Some(error),
            _ => None,
        }
    }
}

impl From<CanonError> for VerdictCodecError {
    fn from(error: CanonError) -> Self {
        Self::Canonical(error)
    }
}

impl From<VerdictError> for VerdictCodecError {
    fn from(error: VerdictError) -> Self {
        Self::Validation(error)
    }
}

/// Cooperative cancellation hook for proof-stream decoding.
pub trait CancellationProbe {
    fn is_cancelled(&self) -> bool;
}

/// A probe for callers which do not need cancellation.
#[derive(Debug, Clone, Copy, Default)]
pub struct NeverCancelled;

impl CancellationProbe for NeverCancelled {
    fn is_cancelled(&self) -> bool {
        false
    }
}

impl CancellationProbe for std::sync::atomic::AtomicBool {
    fn is_cancelled(&self) -> bool {
        self.load(std::sync::atomic::Ordering::Relaxed)
    }
}

fn check_slice_bytes(bytes: &[u8], limits: &VerdictLimits) -> Result<(), VerdictCodecError> {
    let actual = bytes.len() as u128;
    if actual > limits.max_encoded_bytes {
        Err(VerdictError::ResourceLimitExceeded {
            resource: VerdictResource::EncodedBytes,
            limit: limits.max_encoded_bytes,
            actual,
        }
        .into())
    } else {
        Ok(())
    }
}

fn checked_count(
    encoded: u64,
    resource: VerdictResource,
    limit: usize,
) -> Result<usize, VerdictCodecError> {
    let count = usize::try_from(encoded).map_err(|_| VerdictError::ResourceLimitExceeded {
        resource,
        limit: limit as u128,
        actual: encoded as u128,
    })?;
    if count > limit {
        return Err(VerdictError::ResourceLimitExceeded {
            resource,
            limit: limit as u128,
            actual: count as u128,
        }
        .into());
    }
    Ok(count)
}

fn checked_add_count(
    current: usize,
    increment: usize,
    resource: VerdictResource,
    limit: usize,
) -> Result<usize, VerdictCodecError> {
    let actual = current
        .checked_add(increment)
        .ok_or(VerdictError::ResourceLimitExceeded {
            resource,
            limit: limit as u128,
            actual: u128::MAX,
        })?;
    if actual > limit {
        return Err(VerdictError::ResourceLimitExceeded {
            resource,
            limit: limit as u128,
            actual: actual as u128,
        }
        .into());
    }
    Ok(actual)
}

fn read_schema(reader: &mut CanonReader<'_>, schema: SchemaId) -> Result<(), VerdictCodecError> {
    if reader.str()? != schema.name {
        return Err(VerdictCodecError::SchemaNameMismatch {
            expected: schema.name,
        });
    }
    let found = reader.u16()?;
    if found != schema.version {
        return Err(VerdictCodecError::UnsupportedSchemaVersion {
            schema: schema.name,
            found,
            supported: schema.version,
        });
    }
    Ok(())
}

fn read_features(reader: &mut CanonReader<'_>) -> Result<(), VerdictCodecError> {
    let bits = reader.u64()?;
    if bits == FEATURES_V1 {
        Ok(())
    } else {
        Err(VerdictCodecError::UnsupportedExtensionBits { bits })
    }
}

fn write_digest(writer: &mut CanonWriter, digest: Digest) {
    for byte in digest.0 {
        writer.u8(byte);
    }
}

fn read_digest(reader: &mut CanonReader<'_>) -> Result<Digest, VerdictCodecError> {
    let mut bytes = [0u8; 32];
    for byte in &mut bytes {
        *byte = reader.u8()?;
    }
    Ok(Digest(bytes))
}

fn write_literal(writer: &mut CanonWriter, literal: Literal) {
    writer.u64(literal.variable().get());
    writer.u8(match literal.polarity() {
        Polarity::Negative => 0,
        Polarity::Positive => 1,
    });
}

fn read_literal(reader: &mut CanonReader<'_>) -> Result<Literal, VerdictCodecError> {
    let variable = VariableId::new(reader.u64()?)?;
    let polarity = match reader.u8()? {
        0 => Polarity::Negative,
        1 => Polarity::Positive,
        tag => return Err(VerdictCodecError::UnknownPolarity { tag }),
    };
    Ok(Literal::new(variable, polarity))
}

fn write_clause(writer: &mut CanonWriter, clause: &CanonicalClause) {
    writer.u64(clause.literals().len() as u64);
    for literal in clause.literals() {
        write_literal(writer, *literal);
    }
}

fn read_clause<P: CancellationProbe + ?Sized>(
    reader: &mut CanonReader<'_>,
    variable_count: u64,
    limits: &VerdictLimits,
    probe: &P,
) -> Result<CanonicalClause, VerdictCodecError> {
    let literal_count = checked_count(
        reader.u64()?,
        VerdictResource::LiteralsPerClause,
        limits.max_literals_per_clause,
    )?;
    let mut literals = Vec::with_capacity(literal_count);
    for _ in 0..literal_count {
        check_cancelled(probe)?;
        literals.push(read_literal(reader)?);
    }
    Ok(CanonicalClause::new(literals, variable_count, limits)?)
}

/// Encode a canonical CNF under schema `fln.verdict.cnf/1`.
pub fn encode_cnf(cnf: &CanonicalCnf) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(CNF_SCHEMA);
    writer.u64(FEATURES_V1);
    writer.u64(cnf.variable_count());
    writer.u64(cnf.clauses().len() as u64);
    for clause in cnf.clauses() {
        write_clause(&mut writer, clause);
    }
    writer.into_bytes()
}

/// Decode and validate a canonical CNF without count-directed allocation before
/// the corresponding limits are checked.
pub fn decode_cnf(bytes: &[u8], limits: &VerdictLimits) -> Result<CanonicalCnf, VerdictCodecError> {
    check_slice_bytes(bytes, limits)?;
    let mut reader = CanonReader::new(bytes);
    read_schema(&mut reader, CNF_SCHEMA)?;
    read_features(&mut reader)?;
    let variable_count = reader.u64()?;
    checked_count(
        variable_count,
        VerdictResource::Variables,
        limits.max_variables,
    )?;
    let clause_count = checked_count(reader.u64()?, VerdictResource::Clauses, limits.max_clauses)?;
    let mut clauses = Vec::with_capacity(clause_count);
    let mut total_literals = 0usize;
    for _ in 0..clause_count {
        let clause = read_clause(&mut reader, variable_count, limits, &NeverCancelled)?;
        total_literals = checked_add_count(
            total_literals,
            clause.literals().len(),
            VerdictResource::TotalLiterals,
            limits.max_total_literals,
        )?;
        clauses.push(clause.literals().to_vec());
    }
    reader.finish()?;
    let cnf = CanonicalCnf::new(variable_count, clauses, limits)?;
    if encode_cnf(&cnf) != bytes {
        return Err(VerdictCodecError::NonCanonicalEncoding);
    }
    Ok(cnf)
}

/// Encode a complete SAT-model artifact under `fln.verdict.sat-model/1`.
pub fn encode_sat_model(model: &SatModel) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(SAT_MODEL_SCHEMA);
    writer.u64(FEATURES_V1);
    write_digest(&mut writer, model.cnf_root().digest());
    writer.u64(model.variable_count());
    writer.u64(model.assignments().len() as u64);
    for assignment in model.assignments() {
        writer.bool(*assignment);
    }
    writer.into_bytes()
}

/// Decode a total SAT model and bind it to the caller-supplied canonical CNF.
pub fn decode_sat_model(
    bytes: &[u8],
    cnf: &CanonicalCnf,
    limits: &VerdictLimits,
) -> Result<SatModel, VerdictCodecError> {
    check_slice_bytes(bytes, limits)?;
    let mut reader = CanonReader::new(bytes);
    read_schema(&mut reader, SAT_MODEL_SCHEMA)?;
    read_features(&mut reader)?;
    let actual_root = CnfRoot::from_digest(read_digest(&mut reader)?);
    let expected_root = cnf.root();
    if actual_root != expected_root {
        return Err(VerdictCodecError::CnfRootMismatch {
            expected: expected_root,
            actual: actual_root,
        });
    }
    let variable_count = reader.u64()?;
    if variable_count != cnf.variable_count() {
        return Err(VerdictCodecError::VariableCountMismatch {
            expected: cnf.variable_count(),
            actual: variable_count,
        });
    }
    let assignment_count = checked_count(
        reader.u64()?,
        VerdictResource::ModelAssignments,
        limits.max_model_assignments,
    )?;
    let mut assignments = Vec::with_capacity(assignment_count);
    for _ in 0..assignment_count {
        assignments.push(reader.bool()?);
    }
    reader.finish()?;
    let model = SatModel::new(cnf, assignments, limits)?;
    if encode_sat_model(&model) != bytes {
        return Err(VerdictCodecError::NonCanonicalEncoding);
    }
    Ok(model)
}

fn write_clause_ids(writer: &mut CanonWriter, ids: &[ClauseId]) {
    writer.u64(ids.len() as u64);
    for id in ids {
        writer.u64(id.get());
    }
}

fn read_clause_ids<P: CancellationProbe + ?Sized>(
    reader: &mut CanonReader<'_>,
    limits: &VerdictLimits,
    probe: &P,
) -> Result<Vec<ClauseId>, VerdictCodecError> {
    let count = checked_count(
        reader.u64()?,
        VerdictResource::DependencyReferences,
        limits.max_dependency_refs,
    )?;
    let mut ids = Vec::with_capacity(count);
    for _ in 0..count {
        check_cancelled(probe)?;
        ids.push(ClauseId::new(reader.u64()?)?);
    }
    Ok(ids)
}

fn encode_action_record(action: &ProofAction) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    match action {
        ProofAction::AddRup { id, clause, hints } => {
            writer.u8(ACTION_ADD_RUP);
            writer.u64(id.get());
            write_clause(&mut writer, clause);
            write_clause_ids(&mut writer, hints);
        }
        ProofAction::AddRat {
            id,
            clause,
            pivot,
            rup_hints,
            rat_hints,
        } => {
            writer.u8(ACTION_ADD_RAT);
            writer.u64(id.get());
            write_clause(&mut writer, clause);
            write_literal(&mut writer, *pivot);
            write_clause_ids(&mut writer, rup_hints);
            writer.u64(rat_hints.len() as u64);
            for rat_hint in rat_hints {
                writer.u64(rat_hint.clause_id().get());
                write_clause_ids(&mut writer, rat_hint.hints());
            }
        }
        ProofAction::Delete { ids } => {
            writer.u8(ACTION_DELETE);
            write_clause_ids(&mut writer, ids);
        }
    }
    writer.into_bytes()
}

fn decode_action_record<P: CancellationProbe + ?Sized>(
    bytes: &[u8],
    variable_count: u64,
    limits: &VerdictLimits,
    probe: &P,
) -> Result<ProofAction, VerdictCodecError> {
    let mut reader = CanonReader::new(bytes);
    let action = match reader.u8()? {
        ACTION_ADD_RUP => {
            let id = ClauseId::new(reader.u64()?)?;
            let clause = read_clause(&mut reader, variable_count, limits, probe)?;
            let hints = read_clause_ids(&mut reader, limits, probe)?;
            ProofAction::add_rup(id, clause, hints)
        }
        ACTION_ADD_RAT => {
            let id = ClauseId::new(reader.u64()?)?;
            let clause = read_clause(&mut reader, variable_count, limits, probe)?;
            let pivot = read_literal(&mut reader)?;
            let rup_hints = read_clause_ids(&mut reader, limits, probe)?;
            let rat_hint_count = checked_count(
                reader.u64()?,
                VerdictResource::RatHints,
                limits.max_rat_hints,
            )?;
            let mut rat_hints = Vec::with_capacity(rat_hint_count);
            for _ in 0..rat_hint_count {
                check_cancelled(probe)?;
                let clause_id = ClauseId::new(reader.u64()?)?;
                let hints = read_clause_ids(&mut reader, limits, probe)?;
                rat_hints.push(RatHint::new(clause_id, hints));
            }
            ProofAction::add_rat(id, clause, pivot, rup_hints, rat_hints)
        }
        ACTION_DELETE => {
            let ids = read_clause_ids(&mut reader, limits, probe)?;
            ProofAction::delete(ids)
        }
        opcode => return Err(VerdictCodecError::UnknownRecordOpcode { opcode }),
    };
    reader.finish()?;
    if encode_action_record(&action) != bytes {
        return Err(VerdictCodecError::NonCanonicalEncoding);
    }
    Ok(action)
}

fn encode_conclusion_record(empty_clause_id: ClauseId) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.u8(RECORD_CONCLUSION);
    writer.u64(empty_clause_id.get());
    writer.into_bytes()
}

fn decode_conclusion_record(bytes: &[u8]) -> Result<ClauseId, VerdictCodecError> {
    let mut reader = CanonReader::new(bytes);
    let opcode = reader.u8()?;
    if opcode != RECORD_CONCLUSION {
        return Err(VerdictCodecError::UnknownRecordOpcode { opcode });
    }
    let id = ClauseId::new(reader.u64()?)?;
    reader.finish()?;
    if encode_conclusion_record(id) != bytes {
        return Err(VerdictCodecError::NonCanonicalEncoding);
    }
    Ok(id)
}

fn append_frame(output: &mut Vec<u8>, record: &[u8]) {
    output.extend_from_slice(&(record.len() as u64).to_le_bytes());
    output.extend_from_slice(record);
}

/// Encode a structurally validated proof as a header followed by length-framed
/// action records and one mandatory conclusion record.
// FLN-FL-INV-06-CERTIFICATE-BOUNDARY: structured-proof-serialization
pub fn encode_unsat_proof(proof: &UnsatProof) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(UNSAT_PROOF_SCHEMA);
    writer.u64(FEATURES_V1);
    write_digest(&mut writer, proof.cnf_root().digest());
    writer.u64(proof.actions().len() as u64);
    let mut output = writer.into_bytes();
    for action in proof.actions() {
        append_frame(&mut output, &encode_action_record(action));
    }
    append_frame(
        &mut output,
        &encode_conclusion_record(proof.empty_clause_id()),
    );
    output
}

fn check_cancelled<P: CancellationProbe + ?Sized>(probe: &P) -> Result<(), VerdictCodecError> {
    if probe.is_cancelled() {
        Err(VerdictCodecError::Inconclusive(
            InconclusiveReason::Cancelled,
        ))
    } else {
        Ok(())
    }
}

struct StreamInput<'a, R, P: ?Sized> {
    reader: R,
    probe: &'a P,
    at: u128,
    max_encoded_bytes: u128,
    max_record_bytes: usize,
}

impl<'a, R: Read, P: CancellationProbe + ?Sized> StreamInput<'a, R, P> {
    fn new(reader: R, limits: &VerdictLimits, probe: &'a P) -> Self {
        Self {
            reader,
            probe,
            at: 0,
            max_encoded_bytes: limits.max_encoded_bytes,
            max_record_bytes: limits.max_record_bytes,
        }
    }

    fn ensure_bytes(&self, increment: usize) -> Result<(), VerdictCodecError> {
        let actual = self.at.saturating_add(increment as u128);
        if actual > self.max_encoded_bytes {
            Err(VerdictError::ResourceLimitExceeded {
                resource: VerdictResource::EncodedBytes,
                limit: self.max_encoded_bytes,
                actual,
            }
            .into())
        } else {
            Ok(())
        }
    }

    fn read_exact(
        &mut self,
        output: &mut [u8],
        missing_conclusion_on_clean_eof: bool,
    ) -> Result<(), VerdictCodecError> {
        self.ensure_bytes(output.len())?;
        let mut filled = 0usize;
        while filled < output.len() {
            check_cancelled(self.probe)?;
            match self.reader.read(&mut output[filled..]) {
                Ok(0) if filled == 0 && missing_conclusion_on_clean_eof => {
                    return Err(VerdictCodecError::MissingConclusion);
                }
                Ok(0) => return Err(VerdictCodecError::Truncated { at: self.at }),
                Ok(read) => {
                    filled += read;
                    self.at += read as u128;
                }
                Err(error) if error.kind() == ErrorKind::Interrupted => {}
                Err(error) => {
                    return Err(VerdictCodecError::ReadFailure { kind: error.kind() });
                }
            }
        }
        Ok(())
    }

    fn read_u16(&mut self) -> Result<u16, VerdictCodecError> {
        let mut bytes = [0u8; 2];
        self.read_exact(&mut bytes, false)?;
        Ok(u16::from_le_bytes(bytes))
    }

    fn read_u64(&mut self) -> Result<u64, VerdictCodecError> {
        let mut bytes = [0u8; 8];
        self.read_exact(&mut bytes, false)?;
        Ok(u64::from_le_bytes(bytes))
    }

    fn read_schema(&mut self, schema: SchemaId) -> Result<(), VerdictCodecError> {
        let name_length = self.read_u64()?;
        if name_length != schema.name.len() as u64 {
            return Err(VerdictCodecError::SchemaNameMismatch {
                expected: schema.name,
            });
        }
        let mut name = vec![0u8; schema.name.len()];
        self.read_exact(&mut name, false)?;
        if name != schema.name.as_bytes() {
            return Err(VerdictCodecError::SchemaNameMismatch {
                expected: schema.name,
            });
        }
        let found = self.read_u16()?;
        if found != schema.version {
            return Err(VerdictCodecError::UnsupportedSchemaVersion {
                schema: schema.name,
                found,
                supported: schema.version,
            });
        }
        Ok(())
    }

    fn read_digest(&mut self) -> Result<Digest, VerdictCodecError> {
        let mut bytes = [0u8; 32];
        self.read_exact(&mut bytes, false)?;
        Ok(Digest(bytes))
    }

    fn read_frame(
        &mut self,
        missing_conclusion_on_clean_eof: bool,
    ) -> Result<Vec<u8>, VerdictCodecError> {
        let mut length_bytes = [0u8; 8];
        self.read_exact(&mut length_bytes, missing_conclusion_on_clean_eof)?;
        let encoded_length = u64::from_le_bytes(length_bytes);
        let length =
            usize::try_from(encoded_length).map_err(|_| VerdictError::ResourceLimitExceeded {
                resource: VerdictResource::RecordBytes,
                limit: self.max_record_bytes as u128,
                actual: encoded_length as u128,
            })?;
        if length > self.max_record_bytes {
            return Err(VerdictError::ResourceLimitExceeded {
                resource: VerdictResource::RecordBytes,
                limit: self.max_record_bytes as u128,
                actual: length as u128,
            }
            .into());
        }
        self.ensure_bytes(length)?;
        let mut record = vec![0u8; length];
        self.read_exact(&mut record, false)?;
        Ok(record)
    }

    fn finish(mut self) -> Result<(), VerdictCodecError> {
        check_cancelled(self.probe)?;
        let mut byte = [0u8; 1];
        loop {
            match self.reader.read(&mut byte) {
                Ok(0) => return Ok(()),
                Ok(_) => return Err(VerdictCodecError::TrailingBytes),
                Err(error) if error.kind() == ErrorKind::Interrupted => {}
                Err(error) => {
                    return Err(VerdictCodecError::ReadFailure { kind: error.kind() });
                }
            }
        }
    }
}

/// Decode a proof stream without cancellation.
// FLN-FL-INV-06-CERTIFICATE-ALIAS: framed-proof-decode
pub fn decode_unsat_proof<R: Read>(
    reader: R,
    cnf: &CanonicalCnf,
    limits: &VerdictLimits,
) -> Result<UnsatProof, VerdictCodecError> {
    decode_unsat_proof_with_cancellation(reader, cnf, limits, &NeverCancelled)
}

/// Decode a proof stream with cooperative cancellation between framing reads and
/// within count-directed record loops.
// FLN-FL-INV-06-CERTIFICATE-BOUNDARY: framed-proof-decode
pub fn decode_unsat_proof_with_cancellation<R: Read, P: CancellationProbe + ?Sized>(
    reader: R,
    cnf: &CanonicalCnf,
    limits: &VerdictLimits,
    probe: &P,
) -> Result<UnsatProof, VerdictCodecError> {
    check_cancelled(probe)?;
    let mut input = StreamInput::new(reader, limits, probe);
    input.read_schema(UNSAT_PROOF_SCHEMA)?;
    let features = input.read_u64()?;
    if features != FEATURES_V1 {
        return Err(VerdictCodecError::UnsupportedExtensionBits { bits: features });
    }
    let actual_root = CnfRoot::from_digest(input.read_digest()?);
    let expected_root = cnf.root();
    if actual_root != expected_root {
        return Err(VerdictCodecError::CnfRootMismatch {
            expected: expected_root,
            actual: actual_root,
        });
    }
    let action_count = checked_count(
        input.read_u64()?,
        VerdictResource::ProofActions,
        limits.max_proof_actions,
    )?;
    let mut actions = Vec::with_capacity(action_count);
    for _ in 0..action_count {
        check_cancelled(probe)?;
        let record = input.read_frame(false)?;
        actions.push(decode_action_record(
            &record,
            cnf.variable_count(),
            limits,
            probe,
        )?);
    }
    check_cancelled(probe)?;
    let conclusion = input.read_frame(true)?;
    let empty_clause_id = decode_conclusion_record(&conclusion)?;
    input.finish()?;
    Ok(UnsatProof::new(cnf, actions, empty_clause_id, limits)?)
}

#[cfg(test)]
mod tests {
    use std::io::{Cursor, Error};
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::sync::atomic::AtomicBool;

    use super::*;
    use crate::schema::{
        InternalFault, SolverUsage, UntrustedArtifactRef, UntrustedSolverOutcome, VerdictFacts,
    };

    const TEST_LIMITS: VerdictLimits =
        VerdictLimits::new(64 * 1024, 4 * 1024, 64, 64, 64, 256, 64, 64, 256, 64, 128);

    fn variable(value: u64) -> VariableId {
        VariableId::new(value).expect("test variable is nonzero")
    }

    fn clause_id(value: u64) -> ClauseId {
        ClauseId::new(value).expect("test clause id is nonzero")
    }

    fn positive(value: u64) -> Literal {
        Literal::new(variable(value), Polarity::Positive)
    }

    fn negative(value: u64) -> Literal {
        Literal::new(variable(value), Polarity::Negative)
    }

    fn clause(literals: Vec<Literal>) -> CanonicalClause {
        CanonicalClause::new(literals, 3, &TEST_LIMITS)
            .expect("test clause respects its declared variables")
    }

    fn sample_cnf() -> CanonicalCnf {
        CanonicalCnf::new(
            3,
            vec![
                vec![positive(1)],
                vec![negative(1), positive(2)],
                vec![negative(2), positive(3)],
            ],
            &TEST_LIMITS,
        )
        .expect("sample CNF is valid")
    }

    fn sample_model(cnf: &CanonicalCnf) -> SatModel {
        SatModel::new(cnf, vec![true, true, true], &TEST_LIMITS).expect("sample model is total")
    }

    fn sample_proof(cnf: &CanonicalCnf) -> UnsatProof {
        let first_added = cnf.clauses().len() as u64 + 1;
        let empty = first_added + 1;
        let actions = vec![
            ProofAction::add_rat(
                clause_id(first_added),
                clause(vec![positive(3)]),
                positive(3),
                vec![clause_id(1)],
                vec![RatHint::new(clause_id(2), vec![clause_id(1), clause_id(3)])],
            ),
            ProofAction::add_rup(
                clause_id(empty),
                clause(Vec::new()),
                vec![clause_id(first_added)],
            ),
            ProofAction::delete(vec![clause_id(1), clause_id(2)]),
        ];
        UnsatProof::new(cnf, actions, clause_id(empty), &TEST_LIMITS)
            .expect("sample proof is structurally closed")
    }

    fn schema_version_offset(schema: SchemaId) -> usize {
        8 + schema.name.len()
    }

    fn feature_offset(schema: SchemaId) -> usize {
        schema_version_offset(schema) + 2
    }

    fn proof_header_len() -> usize {
        8 + UNSAT_PROOF_SCHEMA.name.len() + 2 + 8 + 32 + 8
    }

    fn without_conclusion(bytes: &[u8], action_count: usize) -> Vec<u8> {
        let mut at = proof_header_len();
        for _ in 0..action_count {
            let length = u64::from_le_bytes(
                bytes[at..at + 8]
                    .try_into()
                    .expect("test frame has a length prefix"),
            ) as usize;
            at += 8 + length;
        }
        bytes[..at].to_vec()
    }

    fn raw_cnf_bytes(variable_count: u64, clauses: &[Vec<Literal>]) -> Vec<u8> {
        let mut writer = CanonWriter::new();
        writer.schema(CNF_SCHEMA);
        writer.u64(FEATURES_V1);
        writer.u64(variable_count);
        writer.u64(clauses.len() as u64);
        for raw_clause in clauses {
            writer.u64(raw_clause.len() as u64);
            for literal in raw_clause {
                write_literal(&mut writer, *literal);
            }
        }
        writer.into_bytes()
    }

    #[test]
    fn verdict_schema_totality() {
        assert_eq!(VariableId::new(0), Err(VerdictError::ZeroVariableId));
        assert_eq!(ClauseId::new(0), Err(VerdictError::ZeroClauseId));
        assert_eq!(
            VariableId::new(u64::MAX)
                .expect("maximum nonzero variable id is representable")
                .get(),
            u64::MAX
        );
        assert_eq!(
            ClauseId::new(u64::MAX)
                .expect("maximum nonzero clause id is representable")
                .get(),
            u64::MAX
        );

        assert!(matches!(
            CanonicalCnf::new(1, vec![vec![positive(2)]], &TEST_LIMITS),
            Err(VerdictError::VariableOutOfRange {
                variable: 2,
                variable_count: 1
            })
        ));
        let cnf = sample_cnf();
        assert!(matches!(
            SatModel::new(&cnf, vec![true, false], &TEST_LIMITS),
            Err(VerdictError::ModelLengthMismatch {
                variable_count: 3,
                assignments: 2
            })
        ));

        let model = sample_model(&cnf);
        let proof = sample_proof(&cnf);
        let usage = SolverUsage {
            decisions: 1,
            proof_actions: proof.actions().len() as u64,
            ..SolverUsage::default()
        };
        let outcomes = [
            UntrustedSolverOutcome::Sat {
                model: model.clone(),
                usage,
            },
            UntrustedSolverOutcome::Unsat {
                proof: proof.clone(),
                usage,
            },
            UntrustedSolverOutcome::Inconclusive {
                reason: InconclusiveReason::Cancelled,
                usage,
            },
            UntrustedSolverOutcome::InternalFault {
                fault: InternalFault::new(7),
                usage,
            },
        ];
        assert!(matches!(
            outcomes[0].artifact(),
            Some(UntrustedArtifactRef::SatModel(_))
        ));
        assert!(matches!(
            outcomes[1].artifact(),
            Some(UntrustedArtifactRef::UnsatProof(_))
        ));
        assert_eq!(outcomes[2].artifact(), None);
        assert_eq!(outcomes[3].artifact(), None);
        assert!(outcomes.iter().all(|outcome| outcome.usage() == usage));

        let mut future = cnf.to_canonical_bytes();
        let version_at = schema_version_offset(CNF_SCHEMA);
        future[version_at..version_at + 2].copy_from_slice(&2u16.to_le_bytes());
        assert!(matches!(
            decode_cnf(&future, &TEST_LIMITS),
            Err(VerdictCodecError::UnsupportedSchemaVersion {
                schema: "fln.verdict.cnf",
                found: 2,
                supported: 1
            })
        ));

        let mut extension = cnf.to_canonical_bytes();
        let features_at = feature_offset(CNF_SCHEMA);
        extension[features_at..features_at + 8].copy_from_slice(&1u64.to_le_bytes());
        assert_eq!(
            decode_cnf(&extension, &TEST_LIMITS),
            Err(VerdictCodecError::UnsupportedExtensionBits { bits: 1 })
        );

        let mut wrong_name = cnf.to_canonical_bytes();
        wrong_name[8] ^= 1;
        assert_eq!(
            decode_cnf(&wrong_name, &TEST_LIMITS),
            Err(VerdictCodecError::SchemaNameMismatch {
                expected: CNF_SCHEMA.name
            })
        );

        let mut trailing = cnf.to_canonical_bytes();
        trailing.push(0);
        assert!(matches!(
            decode_cnf(&trailing, &TEST_LIMITS),
            Err(VerdictCodecError::Canonical(CanonError {
                what: "trailing bytes after value",
                ..
            }))
        ));

        let mut proof_bytes = proof.to_canonical_bytes();
        proof_bytes[proof_header_len() + 8] = u8::MAX;
        assert_eq!(
            decode_unsat_proof(Cursor::new(proof_bytes), &cnf, &TEST_LIMITS),
            Err(VerdictCodecError::UnknownRecordOpcode { opcode: u8::MAX })
        );

        let no_conclusion = without_conclusion(&proof.to_canonical_bytes(), proof.actions().len());
        assert_eq!(
            decode_unsat_proof(Cursor::new(no_conclusion), &cnf, &TEST_LIMITS),
            Err(VerdictCodecError::MissingConclusion)
        );

        let mut malformed_model = model.to_canonical_bytes();
        *malformed_model
            .last_mut()
            .expect("sample model has assignment bytes") = 2;
        assert!(matches!(
            decode_sat_model(&malformed_model, &cnf, &TEST_LIMITS),
            Err(VerdictCodecError::Canonical(CanonError {
                what: "non-canonical bool",
                ..
            }))
        ));

        struct FailingReader;
        impl Read for FailingReader {
            fn read(&mut self, _buffer: &mut [u8]) -> std::io::Result<usize> {
                Err(Error::from(ErrorKind::Other))
            }
        }
        assert_eq!(
            decode_unsat_proof(FailingReader, &cnf, &TEST_LIMITS),
            Err(VerdictCodecError::ReadFailure {
                kind: ErrorKind::Other
            })
        );
    }

    #[test]
    fn cnf_canonical_property() {
        let noisy = CanonicalCnf::new(
            2,
            vec![
                vec![positive(2), negative(1), positive(2)],
                vec![positive(1), negative(1)],
                Vec::new(),
                vec![negative(1), positive(2)],
                Vec::new(),
            ],
            &TEST_LIMITS,
        )
        .expect("normalizable CNF is valid");
        let minimal = CanonicalCnf::new(
            2,
            vec![vec![negative(1), positive(2)], Vec::new()],
            &TEST_LIMITS,
        )
        .expect("minimal equivalent CNF is valid");
        assert_eq!(noisy, minimal);
        assert_eq!(noisy.to_canonical_bytes(), minimal.to_canonical_bytes());
        assert_eq!(noisy.root(), minimal.root());
        assert_eq!(
            CanonicalCnf::from_canonical_bytes(&noisy.to_canonical_bytes(), &TEST_LIMITS)
                .expect("canonical CNF decodes"),
            noisy
        );
        assert_eq!(noisy.facts().clauses, 2);
        assert_eq!(noisy.facts().total_literals, 2);
        assert!(noisy.clauses().iter().any(CanonicalClause::is_empty));
        assert!(
            noisy
                .clauses()
                .iter()
                .all(|candidate| !candidate.is_tautology())
        );

        let reordered = raw_cnf_bytes(2, &[vec![positive(2), negative(1)], Vec::new()]);
        assert_eq!(
            decode_cnf(&reordered, &TEST_LIMITS),
            Err(VerdictCodecError::NonCanonicalEncoding)
        );

        let tight = VerdictLimits {
            max_variables: 2,
            ..TEST_LIMITS
        };
        assert!(CanonicalCnf::new(2, Vec::new(), &tight).is_ok());
        assert!(matches!(
            CanonicalCnf::new(3, Vec::new(), &tight),
            Err(VerdictError::ResourceLimitExceeded {
                resource: VerdictResource::Variables,
                limit: 2,
                actual: 3
            })
        ));
    }

    #[test]
    fn proof_dependency_model() {
        let cnf = sample_cnf();
        let proof = sample_proof(&cnf);
        assert_eq!(proof.facts().proof_actions, 3);
        assert_eq!(proof.facts().dependency_references, 5);
        assert_eq!(proof.facts().rat_hints, 1);

        struct OneByteReader<R> {
            inner: R,
        }
        impl<R: Read> Read for OneByteReader<R> {
            fn read(&mut self, buffer: &mut [u8]) -> std::io::Result<usize> {
                let maximum = buffer.len().min(1);
                self.inner.read(&mut buffer[..maximum])
            }
        }
        let fragmented = OneByteReader {
            inner: Cursor::new(proof.to_canonical_bytes()),
        };
        let decoded = decode_unsat_proof(fragmented, &cnf, &TEST_LIMITS)
            .expect("one-byte reads preserve framed decoding");
        assert_eq!(decoded, proof);
        assert_eq!(decoded.to_canonical_bytes(), proof.to_canonical_bytes());
        assert_eq!(decoded.root(), proof.root());

        let base = cnf.clauses().len() as u64;
        let empty = clause(Vec::new());
        let add_empty = |id, hints| ProofAction::add_rup(clause_id(id), empty.clone(), hints);

        assert!(matches!(
            UnsatProof::new(
                &cnf,
                vec![
                    add_empty(base + 1, Vec::new()),
                    add_empty(base + 1, Vec::new())
                ],
                clause_id(base + 1),
                &TEST_LIMITS
            ),
            Err(VerdictError::AddedClauseIdNotFresh { .. })
        ));
        assert!(matches!(
            UnsatProof::new(
                &cnf,
                vec![
                    add_empty(base + 2, Vec::new()),
                    add_empty(base + 1, Vec::new())
                ],
                clause_id(base + 2),
                &TEST_LIMITS
            ),
            Err(VerdictError::AddedClauseIdNotFresh { .. })
        ));
        assert!(matches!(
            UnsatProof::new(
                &cnf,
                vec![add_empty(base + 1, vec![clause_id(999)])],
                clause_id(base + 1),
                &TEST_LIMITS
            ),
            Err(VerdictError::UnknownOrDeletedDependency { clause_id: 999 })
        ));
        assert!(matches!(
            UnsatProof::new(
                &cnf,
                vec![add_empty(base + 1, vec![clause_id(base + 2)])],
                clause_id(base + 1),
                &TEST_LIMITS
            ),
            Err(VerdictError::UnknownOrDeletedDependency { .. })
        ));
        assert!(matches!(
            UnsatProof::new(
                &cnf,
                vec![
                    ProofAction::delete(vec![clause_id(1)]),
                    add_empty(base + 1, vec![clause_id(1)])
                ],
                clause_id(base + 1),
                &TEST_LIMITS
            ),
            Err(VerdictError::UnknownOrDeletedDependency { clause_id: 1 })
        ));
        assert_eq!(
            UnsatProof::new(
                &cnf,
                vec![ProofAction::delete(vec![clause_id(1), clause_id(1)])],
                clause_id(1),
                &TEST_LIMITS
            ),
            Err(VerdictError::NonCanonicalDeletion)
        );
        assert_eq!(
            UnsatProof::new(
                &cnf,
                vec![ProofAction::delete(Vec::new())],
                clause_id(1),
                &TEST_LIMITS
            ),
            Err(VerdictError::EmptyDeletion)
        );
        assert_eq!(
            UnsatProof::new(
                &cnf,
                vec![ProofAction::add_rat(
                    clause_id(base + 1),
                    clause(vec![positive(2)]),
                    positive(3),
                    Vec::new(),
                    Vec::new()
                )],
                clause_id(base + 1),
                &TEST_LIMITS
            ),
            Err(VerdictError::RatPivotAbsent)
        );
        assert_eq!(
            UnsatProof::new(&cnf, Vec::new(), clause_id(999), &TEST_LIMITS),
            Err(VerdictError::ConclusionUnknownOrDeleted { clause_id: 999 })
        );
        assert_eq!(
            UnsatProof::new(&cnf, Vec::new(), clause_id(1), &TEST_LIMITS),
            Err(VerdictError::ConclusionClauseNotEmpty { clause_id: 1 })
        );
        assert!(matches!(
            UnsatProof::new(
                &cnf,
                vec![
                    add_empty(base + 1, Vec::new()),
                    ProofAction::delete(vec![clause_id(base + 1)])
                ],
                clause_id(base + 1),
                &TEST_LIMITS
            ),
            Err(VerdictError::ConclusionUnknownOrDeleted { .. })
        ));
        assert_eq!(
            UnsatProof::new(
                &cnf,
                vec![ProofAction::add_rat(
                    clause_id(base + 1),
                    clause(vec![positive(3)]),
                    positive(3),
                    Vec::new(),
                    vec![
                        RatHint::new(clause_id(2), Vec::new()),
                        RatHint::new(clause_id(1), Vec::new())
                    ]
                )],
                clause_id(base + 1),
                &TEST_LIMITS
            ),
            Err(VerdictError::NonCanonicalRatHints)
        );

        let cancelled = AtomicBool::new(true);
        assert_eq!(
            decode_unsat_proof_with_cancellation(
                Cursor::new(proof.to_canonical_bytes()),
                &cnf,
                &TEST_LIMITS,
                &cancelled
            ),
            Err(VerdictCodecError::Inconclusive(
                InconclusiveReason::Cancelled
            ))
        );

        let mut oversized_frame = proof.to_canonical_bytes();
        oversized_frame[proof_header_len()..proof_header_len() + 8]
            .copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(matches!(
            decode_unsat_proof(Cursor::new(oversized_frame), &cnf, &TEST_LIMITS),
            Err(VerdictCodecError::Validation(
                VerdictError::ResourceLimitExceeded {
                    resource: VerdictResource::RecordBytes,
                    ..
                }
            ))
        ));

        // Structural closure is intentionally weaker than semantic RUP/RAT checking:
        // the sample artifact is accepted here without asserting its logical steps.
        assert_eq!(proof.actions().len(), 3);
    }

    #[derive(Clone, Copy)]
    enum ArtifactKind {
        Cnf,
        Model,
        Proof,
    }

    fn decode_and_reencode(
        kind: ArtifactKind,
        bytes: &[u8],
        cnf: &CanonicalCnf,
    ) -> Result<Vec<u8>, VerdictCodecError> {
        match kind {
            ArtifactKind::Cnf => {
                decode_cnf(bytes, &TEST_LIMITS).map(|value| value.to_canonical_bytes())
            }
            ArtifactKind::Model => {
                decode_sat_model(bytes, cnf, &TEST_LIMITS).map(|value| value.to_canonical_bytes())
            }
            ArtifactKind::Proof => decode_unsat_proof(Cursor::new(bytes), cnf, &TEST_LIMITS)
                .map(|value| value.to_canonical_bytes()),
        }
    }

    #[test]
    fn verdict_codec_fuzz() {
        let cnf = sample_cnf();
        let model = sample_model(&cnf);
        let proof = sample_proof(&cnf);
        let seeds = [
            (ArtifactKind::Cnf, cnf.to_canonical_bytes()),
            (ArtifactKind::Model, model.to_canonical_bytes()),
            (ArtifactKind::Proof, proof.to_canonical_bytes()),
        ];

        for (kind, seed) in &seeds {
            assert_eq!(
                decode_and_reencode(*kind, seed, &cnf).expect("canonical seed must decode"),
                *seed
            );
            for end in 0..seed.len() {
                let attempt = catch_unwind(AssertUnwindSafe(|| {
                    decode_and_reencode(*kind, &seed[..end], &cnf)
                }));
                assert!(attempt.is_ok(), "decoder panicked at truncation {end}");
                assert!(
                    attempt.expect("panic checked above").is_err(),
                    "truncated artifact unexpectedly decoded at {end}"
                );
            }
        }

        let mut state = 0x6a09_e667_f3bc_c909u64;
        for (kind, seed) in &seeds {
            for mutation in 0..512usize {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                let mut candidate = seed.clone();
                let index = (state as usize) % candidate.len();
                let delta = ((state >> 32) as u8) | 1;
                candidate[index] ^= delta;
                let attempt = catch_unwind(AssertUnwindSafe(|| {
                    decode_and_reencode(*kind, &candidate, &cnf)
                }));
                assert!(
                    attempt.is_ok(),
                    "decoder panicked for mutation {mutation} at byte {index}"
                );
                if let Ok(reencoded) = attempt.expect("panic checked above") {
                    assert_eq!(
                        reencoded, candidate,
                        "accepted bytes must be their own canonical re-encoding"
                    );
                }
            }
        }

        let mut unknown_opcode = proof.to_canonical_bytes();
        unknown_opcode[proof_header_len() + 8] = 0xfe;
        assert!(matches!(
            decode_unsat_proof(Cursor::new(unknown_opcode), &cnf, &TEST_LIMITS),
            Err(VerdictCodecError::UnknownRecordOpcode { opcode: 0xfe })
        ));

        let missing_conclusion =
            without_conclusion(&proof.to_canonical_bytes(), proof.actions().len());
        assert_eq!(
            decode_unsat_proof(Cursor::new(missing_conclusion), &cnf, &TEST_LIMITS),
            Err(VerdictCodecError::MissingConclusion)
        );

        let mut inflated_count = cnf.to_canonical_bytes();
        let clause_count_at = feature_offset(CNF_SCHEMA) + 8 + 8;
        inflated_count[clause_count_at..clause_count_at + 8]
            .copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(matches!(
            decode_cnf(&inflated_count, &TEST_LIMITS),
            Err(VerdictCodecError::Validation(
                VerdictError::ResourceLimitExceeded {
                    resource: VerdictResource::Clauses,
                    ..
                }
            ))
        ));

        let mut duplicate_add = proof.actions().to_vec();
        let first_added = cnf.clauses().len() as u64 + 1;
        duplicate_add.insert(
            1,
            ProofAction::add_rup(clause_id(first_added), clause(Vec::new()), Vec::new()),
        );
        assert!(matches!(
            UnsatProof::new(&cnf, duplicate_add, proof.empty_clause_id(), &TEST_LIMITS),
            Err(VerdictError::AddedClauseIdNotFresh { .. })
        ));

        let facts = VerdictFacts {
            variables: cnf.facts().variables,
            clauses: cnf.facts().clauses,
            ..VerdictFacts::default()
        };
        assert_eq!(facts.variables, 3);
        assert_eq!(facts.clauses, 3);
    }
}
