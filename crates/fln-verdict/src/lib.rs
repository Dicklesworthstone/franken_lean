//! **fln-verdict** — Verdict's solver-independent contract plane.
//!
//! This crate owns the versioned, canonical schemas shared by the future bit-blaster,
//! CDCL engine, proof logger, and independent proof checker (plan §12.5). The
//! streaming checker validates raw proof bytes through its own bounded reader,
//! state, and rule semantics; it never turns a solver claim directly into an
//! environment authority.
//!
//! The v1 contract has four structural laws:
//!
//! * variables and clause ids are non-zero semantic newtypes;
//! * clauses, formulas, assignments, dependencies, and deletion sets have one
//!   canonical order;
//! * arbitrary bytes decode totally under explicit resource bounds, with unknown
//!   versions/opcodes/extensions refused as typed values;
//! * cancellation, resource exhaustion, and internal faults have no publication
//!   path to a SAT model or UNSAT proof (FL-INV-07).

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

mod bitblast;
mod checker;
mod reflection;
mod solver;

pub use bitblast::{
    BITBLAST_MANIFEST, BITBLAST_MANIFEST_ID, BITBLAST_MANIFEST_ROWS, BITBLAST_MANIFEST_VERSION,
    BitblastArtifact, BitblastConstruct, BitblastDeterminismPolicy, BitblastFacts,
    BitblastInconclusive, BitblastInputBinding, BitblastInputKind, BitblastInternalFault,
    BitblastLimits, BitblastManifest, BitblastManifestRow, BitblastOutcome, BitblastRefusal,
    BitblastResource, BitblastSupport, BitblastSymbol, BoolBinaryOp, BoolExpr, BvBinaryOp,
    BvComparison, BvExpr, BvShiftOp, BvUnaryOp, CANONICAL_BITBLAST_POLICY,
    CANONICAL_BITBLAST_POLICY_ID, UnsupportedBvOp, bitblast, bitblast_with_cancel,
};
pub use checker::{
    ProofCheckInconclusive, ProofCheckInternalFault, ProofCheckLimits, ProofCheckOutcome,
    ProofCheckReceipt, ProofCheckResource, ProofOpcodeClass, ProofRefusal, ProofStream,
    check_unsat_streams, check_unsat_streams_with_cancel,
};
pub use reflection::{
    REFLECTED_THEOREM_POLICY_ID, ReflectedArtifactError, ReflectedTheoremArtifact,
    ReflectedTheoremCheckpoint, ReflectedTheoremInconclusive, ReflectedTheoremInternalFault,
    ReflectedTheoremLimits, ReflectedTheoremOutcome, ReflectedTheoremProvenance,
    ReflectedTheoremPublication, ReflectedTheoremRefusal, publish_reflected_theorem,
};
pub use solver::{
    CdclDeterminismPolicy, CheckedSat, CheckedSolverArtifact, CheckedUnsat,
    DETERMINISTIC_CDCL_POLICY, IncrementalError, IncrementalSolver, PreparedSolve,
    SolverInconclusive, SolverInternalFault, SolverLimits, SolverOutcome, SolverResource,
    SolverStatistics, solve, solve_with_cancel,
};

const WIRE_MAGIC: [u8; 8] = *b"FLNVRDCT";
#[cfg(test)]
const WIRE_HEADER_BYTES: usize = 13;
pub const VERDICT_SCHEMA_VERSION: u16 = 1;

/// A frozen top-level schema identity. A body change requires a version bump.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchemaId {
    pub name: &'static str,
    pub version: u16,
}

pub const CNF_SCHEMA: SchemaId = SchemaId {
    name: "fln.verdict.cnf",
    version: VERDICT_SCHEMA_VERSION,
};
pub const SAT_MODEL_SCHEMA: SchemaId = SchemaId {
    name: "fln.verdict.sat-model",
    version: VERDICT_SCHEMA_VERSION,
};
pub const UNSAT_PROOF_SCHEMA: SchemaId = SchemaId {
    name: "fln.verdict.unsat-proof",
    version: VERDICT_SCHEMA_VERSION,
};

/// Wire discriminator. Values are permanent once published.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SchemaKind {
    Cnf = 1,
    SatModel = 2,
    UnsatProof = 3,
}

impl SchemaKind {
    pub const fn schema(self) -> SchemaId {
        match self {
            Self::Cnf => CNF_SCHEMA,
            Self::SatModel => SAT_MODEL_SCHEMA,
            Self::UnsatProof => UNSAT_PROOF_SCHEMA,
        }
    }
}

/// Resource dimensions enforced before allocation or publication.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceKind {
    EncodedBytes,
    Variables,
    Clauses,
    Literals,
    Assignments,
    ProofSteps,
    Dependencies,
}

/// Decoder and validator limits. Every count is aggregate, not per-record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchemaLimits {
    pub max_encoded_bytes: u64,
    pub max_variables: u32,
    pub max_clauses: u64,
    pub max_literals: u64,
    pub max_assignments: u64,
    pub max_proof_steps: u64,
    pub max_dependencies: u64,
}

impl SchemaLimits {
    pub const fn new(
        max_encoded_bytes: u64,
        max_variables: u32,
        max_clauses: u64,
        max_literals: u64,
        max_assignments: u64,
        max_proof_steps: u64,
        max_dependencies: u64,
    ) -> Self {
        Self {
            max_encoded_bytes,
            max_variables,
            max_clauses,
            max_literals,
            max_assignments,
            max_proof_steps,
            max_dependencies,
        }
    }
}

impl Default for SchemaLimits {
    fn default() -> Self {
        Self::new(
            256 * 1024 * 1024,
            16_000_000,
            16_000_000,
            128_000_000,
            16_000_000,
            128_000_000,
            512_000_000,
        )
    }
}

/// Typed schema refusal. No error variant contains a partially validated artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchemaError {
    MalformedEncoding {
        at: usize,
        what: &'static str,
    },
    InvalidMagic,
    UnknownSchemaKind {
        found: u8,
    },
    SchemaMismatch {
        expected: SchemaKind,
        found: u8,
    },
    UnsupportedVersion {
        schema: SchemaId,
        found: u16,
        supported: u16,
    },
    UnsupportedExtensions {
        schema: SchemaId,
        bits: u16,
    },
    UnknownOpcode {
        schema: SchemaId,
        at: usize,
        opcode: u8,
    },
    InvalidVariableId {
        raw: u32,
    },
    InvalidClauseId {
        raw: u64,
    },
    IntegerOutOfRange {
        field: &'static str,
        value: u128,
    },
    VariableOutOfRange {
        variable: VariableId,
        declared: u32,
    },
    VariableCountMismatch {
        expected: u32,
        actual: u32,
    },
    DuplicateClauseId {
        id: ClauseId,
    },
    DuplicateAssignment {
        variable: VariableId,
    },
    MissingAssignment {
        variable: VariableId,
    },
    TautologicalClause {
        variable: VariableId,
    },
    DuplicateDependency {
        step: ClauseId,
        dependency: ClauseId,
    },
    ReusedClauseId {
        id: ClauseId,
    },
    MissingDependency {
        step: ClauseId,
        dependency: ClauseId,
    },
    DeletingMissingClause {
        step_index: usize,
        clause: ClauseId,
    },
    DuplicateDeletionTarget {
        step_index: usize,
        clause: ClauseId,
    },
    EmptyDependencyChain {
        step: ClauseId,
    },
    EmptyDeletion {
        step_index: usize,
    },
    ConclusionNotFinal {
        step_index: usize,
    },
    ConclusionNotEmpty {
        clause: ClauseId,
    },
    MissingConclusion,
    ResourceLimitExceeded {
        resource: ResourceKind,
        limit: u64,
        actual: u64,
    },
    NonCanonicalEncoding {
        schema: SchemaId,
    },
}

impl fmt::Display for SchemaError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MalformedEncoding { at, what } => {
                write!(formatter, "malformed Verdict encoding at byte {at}: {what}")
            }
            Self::InvalidMagic => formatter.write_str("invalid Verdict wire magic"),
            Self::UnknownSchemaKind { found } => {
                write!(formatter, "unknown Verdict schema kind {found}")
            }
            Self::SchemaMismatch { expected, found } => write!(
                formatter,
                "Verdict schema mismatch: expected {}, found wire kind {found}",
                expected.schema().name
            ),
            Self::UnsupportedVersion {
                schema,
                found,
                supported,
            } => write!(
                formatter,
                "unsupported {} version {found}; supported={supported}",
                schema.name
            ),
            Self::UnsupportedExtensions { schema, bits } => write!(
                formatter,
                "unsupported {} extension bits 0x{bits:04x}",
                schema.name
            ),
            Self::UnknownOpcode { schema, at, opcode } => write!(
                formatter,
                "unknown {} opcode {opcode} at byte {at}",
                schema.name
            ),
            Self::InvalidVariableId { raw } => {
                write!(formatter, "invalid zero variable id (raw={raw})")
            }
            Self::InvalidClauseId { raw } => {
                write!(formatter, "invalid zero clause id (raw={raw})")
            }
            Self::IntegerOutOfRange { field, value } => {
                write!(
                    formatter,
                    "{field} value {value} is outside its schema range"
                )
            }
            Self::VariableOutOfRange { variable, declared } => write!(
                formatter,
                "variable {} exceeds declared variable count {declared}",
                variable.get()
            ),
            Self::VariableCountMismatch { expected, actual } => write!(
                formatter,
                "variable-count mismatch: expected {expected}, actual {actual}"
            ),
            Self::DuplicateClauseId { id } => {
                write!(formatter, "duplicate CNF clause id {}", id.get())
            }
            Self::DuplicateAssignment { variable } => {
                write!(
                    formatter,
                    "duplicate assignment for variable {}",
                    variable.get()
                )
            }
            Self::MissingAssignment { variable } => {
                write!(
                    formatter,
                    "missing assignment for variable {}",
                    variable.get()
                )
            }
            Self::TautologicalClause { variable } => write!(
                formatter,
                "clause contains both polarities of variable {}",
                variable.get()
            ),
            Self::DuplicateDependency { step, dependency } => write!(
                formatter,
                "proof clause {} repeats dependency {}",
                step.get(),
                dependency.get()
            ),
            Self::ReusedClauseId { id } => {
                write!(formatter, "proof reuses clause id {}", id.get())
            }
            Self::MissingDependency { step, dependency } => write!(
                formatter,
                "proof clause {} references unavailable dependency {}",
                step.get(),
                dependency.get()
            ),
            Self::DeletingMissingClause { step_index, clause } => write!(
                formatter,
                "proof step {step_index} deletes unavailable clause {}",
                clause.get()
            ),
            Self::DuplicateDeletionTarget { step_index, clause } => write!(
                formatter,
                "proof step {step_index} repeats deletion target {}",
                clause.get()
            ),
            Self::EmptyDependencyChain { step } => write!(
                formatter,
                "proof clause {} has an empty dependency chain",
                step.get()
            ),
            Self::EmptyDeletion { step_index } => {
                write!(
                    formatter,
                    "proof step {step_index} has an empty deletion set"
                )
            }
            Self::ConclusionNotFinal { step_index } => {
                write!(
                    formatter,
                    "proof conclusion at step {step_index} is not final"
                )
            }
            Self::ConclusionNotEmpty { clause } => write!(
                formatter,
                "proof conclusion references non-empty clause {}",
                clause.get()
            ),
            Self::MissingConclusion => {
                formatter.write_str("UNSAT proof is partial: final conclusion is missing")
            }
            Self::ResourceLimitExceeded {
                resource,
                limit,
                actual,
            } => write!(
                formatter,
                "Verdict resource {resource:?} exceeded: {actual} > {limit}"
            ),
            Self::NonCanonicalEncoding { schema } => {
                write!(formatter, "{} bytes are not canonical", schema.name)
            }
        }
    }
}

impl std::error::Error for SchemaError {}

/// Non-zero SAT variable id. `u32::MAX` is valid.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VariableId(u32);

impl VariableId {
    pub fn new(raw: u32) -> Result<Self, SchemaError> {
        if raw == 0 {
            Err(SchemaError::InvalidVariableId { raw })
        } else {
            Ok(Self(raw))
        }
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

/// Non-zero clause id shared by input and proof clauses. `u64::MAX` is valid.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseId(u64);

impl ClauseId {
    pub fn new(raw: u64) -> Result<Self, SchemaError> {
        if raw == 0 {
            Err(SchemaError::InvalidClauseId { raw })
        } else {
            Ok(Self(raw))
        }
    }

    pub const fn get(self) -> u64 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum Polarity {
    Negative = 0,
    Positive = 1,
}

/// One canonical literal: variable first, then negative before positive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal {
    variable: VariableId,
    polarity: Polarity,
}

impl Literal {
    pub const fn new(variable: VariableId, polarity: Polarity) -> Self {
        Self { variable, polarity }
    }

    pub fn from_dimacs(value: i64) -> Result<Self, SchemaError> {
        if value == 0 {
            return Err(SchemaError::InvalidVariableId { raw: 0 });
        }
        let magnitude = value.unsigned_abs();
        let raw = u32::try_from(magnitude).map_err(|_| SchemaError::IntegerOutOfRange {
            field: "DIMACS literal",
            value: u128::from(magnitude),
        })?;
        Ok(Self::new(
            VariableId::new(raw)?,
            if value < 0 {
                Polarity::Negative
            } else {
                Polarity::Positive
            },
        ))
    }

    pub const fn variable(self) -> VariableId {
        self.variable
    }

    pub const fn polarity(self) -> Polarity {
        self.polarity
    }

    pub const fn to_dimacs(self) -> i64 {
        match self.polarity {
            Polarity::Negative => -(self.variable.get() as i64),
            Polarity::Positive => self.variable.get() as i64,
        }
    }
}

/// Canonical clause. Duplicate equal literals are normalized away; complementary
/// literals are refused so the durable schema never carries tautological noise.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    literals: Box<[Literal]>,
}

impl Clause {
    pub fn new(mut literals: Vec<Literal>) -> Result<Self, SchemaError> {
        literals.sort_unstable();
        let mut normalized: Vec<Literal> = Vec::with_capacity(literals.len());
        for literal in literals {
            if let Some(previous) = normalized.last().copied()
                && previous.variable() == literal.variable()
            {
                if previous.polarity() != literal.polarity() {
                    return Err(SchemaError::TautologicalClause {
                        variable: literal.variable(),
                    });
                }
                continue;
            }
            normalized.push(literal);
        }
        Ok(Self {
            literals: normalized.into_boxed_slice(),
        })
    }

    pub fn literals(&self) -> &[Literal] {
        &self.literals
    }

    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputClause {
    id: ClauseId,
    clause: Clause,
}

impl InputClause {
    pub const fn new(id: ClauseId, clause: Clause) -> Self {
        Self { id, clause }
    }

    pub const fn id(&self) -> ClauseId {
        self.id
    }

    pub const fn clause(&self) -> &Clause {
        &self.clause
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CnfFacts {
    pub variables: u32,
    pub clauses: u64,
    pub literals: u64,
}

/// Validated CNF sorted by clause id.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cnf {
    variable_count: u32,
    clauses: Box<[InputClause]>,
    facts: CnfFacts,
}

impl Cnf {
    pub fn new(
        variable_count: u32,
        mut clauses: Vec<InputClause>,
        limits: SchemaLimits,
    ) -> Result<Self, SchemaError> {
        enforce_limit(
            ResourceKind::Variables,
            u64::from(limits.max_variables),
            u64::from(variable_count),
        )?;
        let clause_count = usize_as_u64(clauses.len(), "CNF clause count")?;
        enforce_limit(ResourceKind::Clauses, limits.max_clauses, clause_count)?;

        clauses.sort_unstable_by_key(InputClause::id);
        for pair in clauses.windows(2) {
            if pair[0].id == pair[1].id {
                return Err(SchemaError::DuplicateClauseId { id: pair[0].id });
            }
        }

        let mut literal_count = 0_u64;
        for input in &clauses {
            for literal in input.clause.literals() {
                if literal.variable().get() > variable_count {
                    return Err(SchemaError::VariableOutOfRange {
                        variable: literal.variable(),
                        declared: variable_count,
                    });
                }
            }
            literal_count = checked_add(
                literal_count,
                usize_as_u64(input.clause.literals().len(), "CNF literal count")?,
                "CNF literal count",
            )?;
        }
        enforce_limit(ResourceKind::Literals, limits.max_literals, literal_count)?;

        Ok(Self {
            variable_count,
            clauses: clauses.into_boxed_slice(),
            facts: CnfFacts {
                variables: variable_count,
                clauses: clause_count,
                literals: literal_count,
            },
        })
    }

    pub const fn variable_count(&self) -> u32 {
        self.variable_count
    }

    pub fn clauses(&self) -> &[InputClause] {
        &self.clauses
    }

    pub const fn facts(&self) -> CnfFacts {
        self.facts
    }

    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let mut writer = Writer::new();
        writer.header(SchemaKind::Cnf);
        writer.u32(self.variable_count);
        writer.u64(self.facts.clauses);
        for input in &self.clauses {
            writer.u64(input.id.get());
            write_clause(&mut writer, &input.clause);
        }
        writer.finish()
    }

    pub fn from_canonical_bytes(bytes: &[u8], limits: SchemaLimits) -> Result<Self, SchemaError> {
        enforce_encoded_bytes(bytes, limits)?;
        let mut reader = Reader::new(bytes);
        reader.header(SchemaKind::Cnf)?;
        let variable_count = reader.u32()?;
        enforce_limit(
            ResourceKind::Variables,
            u64::from(limits.max_variables),
            u64::from(variable_count),
        )?;
        let count = reader.count(ResourceKind::Clauses, limits.max_clauses)?;
        reader.require_minimum_rows(count, 16, "CNF clauses exceed remaining bytes")?;
        let mut clauses = Vec::new();
        for _ in 0..count {
            let id = ClauseId::new(reader.u64()?)?;
            let clause = read_clause(&mut reader, limits.max_literals)?;
            clauses.push(InputClause::new(id, clause));
        }
        reader.finish()?;
        let value = Self::new(variable_count, clauses, limits)?;
        if value.to_canonical_bytes() != bytes {
            return Err(SchemaError::NonCanonicalEncoding { schema: CNF_SCHEMA });
        }
        Ok(value)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Assignment {
    variable: VariableId,
    value: bool,
}

impl Assignment {
    pub const fn new(variable: VariableId, value: bool) -> Self {
        Self { variable, value }
    }

    pub const fn variable(self) -> VariableId {
        self.variable
    }

    pub const fn value(self) -> bool {
        self.value
    }
}

/// Complete, canonical assignment for variables `1..=variable_count`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SatModel {
    variable_count: u32,
    assignments: Box<[Assignment]>,
}

impl SatModel {
    pub fn new(
        variable_count: u32,
        mut assignments: Vec<Assignment>,
        limits: SchemaLimits,
    ) -> Result<Self, SchemaError> {
        enforce_limit(
            ResourceKind::Variables,
            u64::from(limits.max_variables),
            u64::from(variable_count),
        )?;
        let assignment_count = usize_as_u64(assignments.len(), "SAT assignment count")?;
        enforce_limit(
            ResourceKind::Assignments,
            limits.max_assignments,
            assignment_count,
        )?;
        assignments.sort_unstable_by_key(|assignment| assignment.variable);
        for pair in assignments.windows(2) {
            if pair[0].variable == pair[1].variable {
                return Err(SchemaError::DuplicateAssignment {
                    variable: pair[0].variable,
                });
            }
        }
        for assignment in &assignments {
            if assignment.variable.get() > variable_count {
                return Err(SchemaError::VariableOutOfRange {
                    variable: assignment.variable,
                    declared: variable_count,
                });
            }
        }
        for raw in 1..=variable_count {
            let variable = VariableId(raw);
            if assignments
                .binary_search_by_key(&variable, |assignment| assignment.variable)
                .is_err()
            {
                return Err(SchemaError::MissingAssignment { variable });
            }
        }

        Ok(Self {
            variable_count,
            assignments: assignments.into_boxed_slice(),
        })
    }

    pub const fn variable_count(&self) -> u32 {
        self.variable_count
    }

    pub fn assignments(&self) -> &[Assignment] {
        &self.assignments
    }

    pub fn value(&self, variable: VariableId) -> Option<bool> {
        self.assignments
            .binary_search_by_key(&variable, |assignment| assignment.variable)
            .ok()
            .map(|index| self.assignments[index].value)
    }

    pub fn satisfies(&self, cnf: &Cnf) -> Result<bool, SchemaError> {
        if self.variable_count != cnf.variable_count {
            return Err(SchemaError::VariableCountMismatch {
                expected: cnf.variable_count,
                actual: self.variable_count,
            });
        }
        Ok(cnf.clauses.iter().all(|input| {
            input.clause.literals.iter().any(|literal| {
                let value = self.value(literal.variable()).unwrap_or(false);
                match literal.polarity() {
                    Polarity::Negative => !value,
                    Polarity::Positive => value,
                }
            })
        }))
    }

    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let mut writer = Writer::new();
        writer.header(SchemaKind::SatModel);
        writer.u32(self.variable_count);
        writer.u64(self.assignments.len() as u64);
        for assignment in &self.assignments {
            writer.u32(assignment.variable.get());
            writer.bool(assignment.value);
        }
        writer.finish()
    }

    pub fn from_canonical_bytes(bytes: &[u8], limits: SchemaLimits) -> Result<Self, SchemaError> {
        enforce_encoded_bytes(bytes, limits)?;
        let mut reader = Reader::new(bytes);
        reader.header(SchemaKind::SatModel)?;
        let variable_count = reader.u32()?;
        enforce_limit(
            ResourceKind::Variables,
            u64::from(limits.max_variables),
            u64::from(variable_count),
        )?;
        let count = reader.count(ResourceKind::Assignments, limits.max_assignments)?;
        reader.require_minimum_rows(count, 5, "SAT assignments exceed remaining bytes")?;
        let mut assignments = Vec::new();
        for _ in 0..count {
            assignments.push(Assignment::new(
                VariableId::new(reader.u32()?)?,
                reader.bool()?,
            ));
        }
        reader.finish()?;
        let value = Self::new(variable_count, assignments, limits)?;
        if value.to_canonical_bytes() != bytes {
            return Err(SchemaError::NonCanonicalEncoding {
                schema: SAT_MODEL_SCHEMA,
            });
        }
        Ok(value)
    }
}

/// Solver-produced rule vocabulary. The independent checker assigns semantics to
/// these rows; this crate only freezes their shape and dependency discipline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofRule {
    Resolution {
        pivot: VariableId,
        positive_parent: ClauseId,
        negative_parent: ClauseId,
    },
    Rup {
        antecedents: Box<[ClauseId]>,
    },
}

impl ProofRule {
    pub fn rup(antecedents: Vec<ClauseId>) -> Self {
        Self::Rup {
            antecedents: antecedents.into_boxed_slice(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofStep {
    Derive {
        id: ClauseId,
        clause: Clause,
        rule: ProofRule,
    },
    Delete {
        clauses: Box<[ClauseId]>,
    },
    Conclude {
        empty_clause: ClauseId,
    },
}

impl ProofStep {
    pub fn delete(clauses: Vec<ClauseId>) -> Self {
        Self::Delete {
            clauses: clauses.into_boxed_slice(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofFacts {
    pub steps: u64,
    pub derived_clauses: u64,
    pub derived_literals: u64,
    pub dependencies: u64,
    pub deletions: u64,
}

/// Canonical proof trace whose dependency graph has been validated against a CNF.
/// Rule semantics are deliberately not checked here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsatProof {
    steps: Box<[ProofStep]>,
    facts: ProofFacts,
}

impl UnsatProof {
    pub fn new(
        cnf: &Cnf,
        mut steps: Vec<ProofStep>,
        limits: SchemaLimits,
    ) -> Result<Self, SchemaError> {
        let step_count = usize_as_u64(steps.len(), "UNSAT proof step count")?;
        enforce_limit(ResourceKind::ProofSteps, limits.max_proof_steps, step_count)?;
        normalize_proof_steps(&mut steps)?;
        let facts = validate_dependencies(cnf, &steps, limits)?;
        Ok(Self {
            steps: steps.into_boxed_slice(),
            facts,
        })
    }

    pub fn steps(&self) -> &[ProofStep] {
        &self.steps
    }

    pub const fn facts(&self) -> ProofFacts {
        self.facts
    }

    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let mut writer = Writer::new();
        writer.header(SchemaKind::UnsatProof);
        writer.u64(self.facts.steps);
        for step in &self.steps {
            match step {
                ProofStep::Derive { id, clause, rule } => {
                    writer.u8(1);
                    writer.u64(id.get());
                    write_clause(&mut writer, clause);
                    match rule {
                        ProofRule::Resolution {
                            pivot,
                            positive_parent,
                            negative_parent,
                        } => {
                            writer.u8(1);
                            writer.u32(pivot.get());
                            writer.u64(positive_parent.get());
                            writer.u64(negative_parent.get());
                        }
                        ProofRule::Rup { antecedents } => {
                            writer.u8(2);
                            writer.u64(antecedents.len() as u64);
                            for antecedent in antecedents.iter() {
                                writer.u64(antecedent.get());
                            }
                        }
                    }
                }
                ProofStep::Delete { clauses } => {
                    writer.u8(2);
                    writer.u64(clauses.len() as u64);
                    for clause in clauses.iter() {
                        writer.u64(clause.get());
                    }
                }
                ProofStep::Conclude { empty_clause } => {
                    writer.u8(3);
                    writer.u64(empty_clause.get());
                }
            }
        }
        writer.finish()
    }

    pub fn from_canonical_bytes(
        bytes: &[u8],
        cnf: &Cnf,
        limits: SchemaLimits,
    ) -> Result<Self, SchemaError> {
        enforce_encoded_bytes(bytes, limits)?;
        let mut reader = Reader::new(bytes);
        reader.header(SchemaKind::UnsatProof)?;
        let count = reader.count(ResourceKind::ProofSteps, limits.max_proof_steps)?;
        reader.require_minimum_rows(count, 9, "proof steps exceed remaining bytes")?;
        let mut steps = Vec::new();
        for _ in 0..count {
            let opcode_at = reader.position();
            let opcode = reader.u8()?;
            match opcode {
                1 => {
                    let id = ClauseId::new(reader.u64()?)?;
                    let clause = read_clause(&mut reader, limits.max_literals)?;
                    let rule_at = reader.position();
                    let rule_opcode = reader.u8()?;
                    let rule = match rule_opcode {
                        1 => ProofRule::Resolution {
                            pivot: VariableId::new(reader.u32()?)?,
                            positive_parent: ClauseId::new(reader.u64()?)?,
                            negative_parent: ClauseId::new(reader.u64()?)?,
                        },
                        2 => ProofRule::Rup {
                            antecedents: read_clause_ids(
                                &mut reader,
                                ResourceKind::Dependencies,
                                limits.max_dependencies,
                            )?
                            .into_boxed_slice(),
                        },
                        other => {
                            return Err(SchemaError::UnknownOpcode {
                                schema: UNSAT_PROOF_SCHEMA,
                                at: rule_at,
                                opcode: other,
                            });
                        }
                    };
                    steps.push(ProofStep::Derive { id, clause, rule });
                }
                2 => steps.push(ProofStep::Delete {
                    clauses: read_clause_ids(
                        &mut reader,
                        ResourceKind::Dependencies,
                        limits.max_dependencies,
                    )?
                    .into_boxed_slice(),
                }),
                3 => steps.push(ProofStep::Conclude {
                    empty_clause: ClauseId::new(reader.u64()?)?,
                }),
                other => {
                    return Err(SchemaError::UnknownOpcode {
                        schema: UNSAT_PROOF_SCHEMA,
                        at: opcode_at,
                        opcode: other,
                    });
                }
            }
        }
        reader.finish()?;
        let value = Self::new(cnf, steps, limits)?;
        if value.to_canonical_bytes() != bytes {
            return Err(SchemaError::NonCanonicalEncoding {
                schema: UNSAT_PROOF_SCHEMA,
            });
        }
        Ok(value)
    }
}

/// Typed nonpublication outcomes (FL-INV-07).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InconclusiveReason {
    Cancelled,
    ResourceExhausted {
        resource: ResourceKind,
        limit: u64,
        actual: u64,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttemptOutcome {
    Sat(SatModel),
    Unsat(UnsatProof),
    Inconclusive(InconclusiveReason),
    InternalFault { code: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PublishableArtifact<'a> {
    Sat(&'a SatModel),
    Unsat(&'a UnsatProof),
}

impl AttemptOutcome {
    /// The only publication door. Inconclusive and InternalFault have no artifact.
    pub const fn publishable_artifact(&self) -> Option<PublishableArtifact<'_>> {
        match self {
            Self::Sat(model) => Some(PublishableArtifact::Sat(model)),
            Self::Unsat(proof) => Some(PublishableArtifact::Unsat(proof)),
            Self::Inconclusive(_) | Self::InternalFault { .. } => None,
        }
    }
}

fn normalize_proof_steps(steps: &mut [ProofStep]) -> Result<(), SchemaError> {
    for (step_index, step) in steps.iter_mut().enumerate() {
        match step {
            ProofStep::Derive { id, rule, .. } => match rule {
                ProofRule::Resolution {
                    positive_parent,
                    negative_parent,
                    ..
                } => {
                    if positive_parent == negative_parent {
                        return Err(SchemaError::DuplicateDependency {
                            step: *id,
                            dependency: *positive_parent,
                        });
                    }
                }
                ProofRule::Rup { antecedents } => {
                    let mut canonical = antecedents.to_vec();
                    canonical.sort_unstable();
                    for pair in canonical.windows(2) {
                        if pair[0] == pair[1] {
                            return Err(SchemaError::DuplicateDependency {
                                step: *id,
                                dependency: pair[0],
                            });
                        }
                    }
                    *antecedents = canonical.into_boxed_slice();
                }
            },
            ProofStep::Delete { clauses } => {
                if clauses.is_empty() {
                    return Err(SchemaError::EmptyDeletion { step_index });
                }
                let mut canonical = clauses.to_vec();
                canonical.sort_unstable();
                for pair in canonical.windows(2) {
                    if pair[0] == pair[1] {
                        return Err(SchemaError::DuplicateDeletionTarget {
                            step_index,
                            clause: pair[0],
                        });
                    }
                }
                *clauses = canonical.into_boxed_slice();
            }
            ProofStep::Conclude { .. } => {}
        }
    }
    Ok(())
}

fn validate_dependencies(
    cnf: &Cnf,
    steps: &[ProofStep],
    limits: SchemaLimits,
) -> Result<ProofFacts, SchemaError> {
    let mut live = BTreeMap::<ClauseId, bool>::new();
    let mut all_ids = BTreeSet::<ClauseId>::new();
    for input in &cnf.clauses {
        live.insert(input.id, input.clause.is_empty());
        all_ids.insert(input.id);
    }

    let mut facts = ProofFacts {
        steps: usize_as_u64(steps.len(), "UNSAT proof step count")?,
        derived_clauses: 0,
        derived_literals: 0,
        dependencies: 0,
        deletions: 0,
    };
    let mut concluded = false;

    for (step_index, step) in steps.iter().enumerate() {
        match step {
            ProofStep::Derive { id, clause, rule } => {
                if !all_ids.insert(*id) {
                    return Err(SchemaError::ReusedClauseId { id: *id });
                }
                for literal in clause.literals() {
                    if literal.variable().get() > cnf.variable_count {
                        return Err(SchemaError::VariableOutOfRange {
                            variable: literal.variable(),
                            declared: cnf.variable_count,
                        });
                    }
                }
                facts.derived_clauses =
                    checked_add(facts.derived_clauses, 1, "derived clause count")?;
                facts.derived_literals = checked_add(
                    facts.derived_literals,
                    usize_as_u64(clause.literals().len(), "derived literal count")?,
                    "derived literal count",
                )?;
                match rule {
                    ProofRule::Resolution {
                        pivot,
                        positive_parent,
                        negative_parent,
                    } => {
                        if pivot.get() > cnf.variable_count {
                            return Err(SchemaError::VariableOutOfRange {
                                variable: *pivot,
                                declared: cnf.variable_count,
                            });
                        }
                        require_dependency(&live, *id, *positive_parent)?;
                        require_dependency(&live, *id, *negative_parent)?;
                        facts.dependencies =
                            checked_add(facts.dependencies, 2, "proof dependency count")?;
                    }
                    ProofRule::Rup { antecedents } => {
                        if antecedents.is_empty() {
                            return Err(SchemaError::EmptyDependencyChain { step: *id });
                        }
                        for dependency in antecedents.iter().copied() {
                            require_dependency(&live, *id, dependency)?;
                        }
                        facts.dependencies = checked_add(
                            facts.dependencies,
                            usize_as_u64(antecedents.len(), "proof dependency count")?,
                            "proof dependency count",
                        )?;
                    }
                }
                live.insert(*id, clause.is_empty());
            }
            ProofStep::Delete { clauses } => {
                facts.deletions = checked_add(
                    facts.deletions,
                    usize_as_u64(clauses.len(), "proof deletion count")?,
                    "proof deletion count",
                )?;
                facts.dependencies = checked_add(
                    facts.dependencies,
                    usize_as_u64(clauses.len(), "proof dependency count")?,
                    "proof dependency count",
                )?;
                for clause in clauses.iter().copied() {
                    if live.remove(&clause).is_none() {
                        return Err(SchemaError::DeletingMissingClause { step_index, clause });
                    }
                }
            }
            ProofStep::Conclude { empty_clause } => {
                if step_index + 1 != steps.len() {
                    return Err(SchemaError::ConclusionNotFinal { step_index });
                }
                let is_empty =
                    live.get(empty_clause)
                        .copied()
                        .ok_or(SchemaError::MissingDependency {
                            step: *empty_clause,
                            dependency: *empty_clause,
                        })?;
                if !is_empty {
                    return Err(SchemaError::ConclusionNotEmpty {
                        clause: *empty_clause,
                    });
                }
                facts.dependencies = checked_add(facts.dependencies, 1, "proof dependency count")?;
                concluded = true;
            }
        }
    }

    if !concluded {
        return Err(SchemaError::MissingConclusion);
    }
    enforce_limit(
        ResourceKind::Clauses,
        limits.max_clauses,
        facts.derived_clauses,
    )?;
    enforce_limit(
        ResourceKind::Literals,
        limits.max_literals,
        facts.derived_literals,
    )?;
    enforce_limit(
        ResourceKind::Dependencies,
        limits.max_dependencies,
        facts.dependencies,
    )?;
    Ok(facts)
}

fn require_dependency(
    live: &BTreeMap<ClauseId, bool>,
    step: ClauseId,
    dependency: ClauseId,
) -> Result<(), SchemaError> {
    if live.contains_key(&dependency) {
        Ok(())
    } else {
        Err(SchemaError::MissingDependency { step, dependency })
    }
}

fn enforce_encoded_bytes(bytes: &[u8], limits: SchemaLimits) -> Result<(), SchemaError> {
    enforce_limit(
        ResourceKind::EncodedBytes,
        limits.max_encoded_bytes,
        usize_as_u64(bytes.len(), "encoded byte count")?,
    )
}

fn enforce_limit(resource: ResourceKind, limit: u64, actual: u64) -> Result<(), SchemaError> {
    if actual > limit {
        Err(SchemaError::ResourceLimitExceeded {
            resource,
            limit,
            actual,
        })
    } else {
        Ok(())
    }
}

fn checked_add(left: u64, right: u64, field: &'static str) -> Result<u64, SchemaError> {
    left.checked_add(right)
        .ok_or(SchemaError::IntegerOutOfRange {
            field,
            value: u128::from(left) + u128::from(right),
        })
}

fn usize_as_u64(value: usize, field: &'static str) -> Result<u64, SchemaError> {
    u64::try_from(value).map_err(|_| SchemaError::IntegerOutOfRange {
        field,
        value: value as u128,
    })
}

#[derive(Debug, Default)]
struct Writer {
    bytes: Vec<u8>,
}

impl Writer {
    fn new() -> Self {
        Self::default()
    }

    fn header(&mut self, kind: SchemaKind) {
        self.bytes.extend_from_slice(&WIRE_MAGIC);
        self.u8(kind as u8);
        self.u16(kind.schema().version);
        self.u16(0);
    }

    fn u8(&mut self, value: u8) {
        self.bytes.push(value);
    }

    fn u16(&mut self, value: u16) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn bool(&mut self, value: bool) {
        self.u8(u8::from(value));
    }

    fn finish(self) -> Vec<u8> {
        self.bytes
    }
}

#[derive(Debug)]
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }

    const fn position(&self) -> usize {
        self.at
    }

    fn take(&mut self, amount: usize) -> Result<&'a [u8], SchemaError> {
        let end = self
            .at
            .checked_add(amount)
            .ok_or(SchemaError::MalformedEncoding {
                at: self.at,
                what: "offset overflow",
            })?;
        if end > self.bytes.len() {
            return Err(SchemaError::MalformedEncoding {
                at: self.at,
                what: "input truncated",
            });
        }
        let result = &self.bytes[self.at..end];
        self.at = end;
        Ok(result)
    }

    fn header(&mut self, expected: SchemaKind) -> Result<(), SchemaError> {
        if self.take(WIRE_MAGIC.len())? != WIRE_MAGIC {
            return Err(SchemaError::InvalidMagic);
        }
        let kind = self.u8()?;
        if !matches!(kind, 1..=3) {
            return Err(SchemaError::UnknownSchemaKind { found: kind });
        }
        if kind != expected as u8 {
            return Err(SchemaError::SchemaMismatch {
                expected,
                found: kind,
            });
        }
        let version = self.u16()?;
        if version != expected.schema().version {
            return Err(SchemaError::UnsupportedVersion {
                schema: expected.schema(),
                found: version,
                supported: expected.schema().version,
            });
        }
        let extensions = self.u16()?;
        if extensions != 0 {
            return Err(SchemaError::UnsupportedExtensions {
                schema: expected.schema(),
                bits: extensions,
            });
        }
        Ok(())
    }

    fn u8(&mut self) -> Result<u8, SchemaError> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, SchemaError> {
        let raw = self.take(2)?;
        let mut bytes = [0_u8; 2];
        bytes.copy_from_slice(raw);
        Ok(u16::from_le_bytes(bytes))
    }

    fn u32(&mut self) -> Result<u32, SchemaError> {
        let raw = self.take(4)?;
        let mut bytes = [0_u8; 4];
        bytes.copy_from_slice(raw);
        Ok(u32::from_le_bytes(bytes))
    }

    fn u64(&mut self) -> Result<u64, SchemaError> {
        let raw = self.take(8)?;
        let mut bytes = [0_u8; 8];
        bytes.copy_from_slice(raw);
        Ok(u64::from_le_bytes(bytes))
    }

    fn bool(&mut self) -> Result<bool, SchemaError> {
        let at = self.position();
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(SchemaError::MalformedEncoding {
                at,
                what: "non-canonical boolean",
            }),
        }
    }

    fn count(&mut self, resource: ResourceKind, limit: u64) -> Result<usize, SchemaError> {
        let count = self.u64()?;
        enforce_limit(resource, limit, count)?;
        usize::try_from(count).map_err(|_| SchemaError::IntegerOutOfRange {
            field: "wire count",
            value: u128::from(count),
        })
    }

    fn require_minimum_rows(
        &self,
        count: usize,
        minimum_row_bytes: usize,
        what: &'static str,
    ) -> Result<(), SchemaError> {
        let required =
            count
                .checked_mul(minimum_row_bytes)
                .ok_or(SchemaError::MalformedEncoding {
                    at: self.at,
                    what: "collection byte requirement overflows address space",
                })?;
        if required > self.bytes.len().saturating_sub(self.at) {
            Err(SchemaError::MalformedEncoding { at: self.at, what })
        } else {
            Ok(())
        }
    }

    fn finish(self) -> Result<(), SchemaError> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(SchemaError::MalformedEncoding {
                at: self.at,
                what: "trailing bytes",
            })
        }
    }
}

fn write_clause(writer: &mut Writer, clause: &Clause) {
    writer.u64(clause.literals.len() as u64);
    for literal in clause.literals.iter().copied() {
        writer.u32(literal.variable().get());
        writer.u8(literal.polarity() as u8);
    }
}

fn read_clause(reader: &mut Reader<'_>, max_literals: u64) -> Result<Clause, SchemaError> {
    let count = reader.count(ResourceKind::Literals, max_literals)?;
    reader.require_minimum_rows(count, 5, "clause literals exceed remaining bytes")?;
    let mut literals = Vec::new();
    for _ in 0..count {
        let variable = VariableId::new(reader.u32()?)?;
        let polarity_at = reader.position();
        let polarity = match reader.u8()? {
            0 => Polarity::Negative,
            1 => Polarity::Positive,
            _ => {
                return Err(SchemaError::MalformedEncoding {
                    at: polarity_at,
                    what: "unknown literal polarity",
                });
            }
        };
        literals.push(Literal::new(variable, polarity));
    }
    Clause::new(literals)
}

fn read_clause_ids(
    reader: &mut Reader<'_>,
    resource: ResourceKind,
    limit: u64,
) -> Result<Vec<ClauseId>, SchemaError> {
    let count = reader.count(resource, limit)?;
    reader.require_minimum_rows(count, 8, "clause ids exceed remaining bytes")?;
    let mut ids = Vec::new();
    for _ in 0..count {
        ids.push(ClauseId::new(reader.u64()?)?);
    }
    Ok(ids)
}

#[cfg(test)]
mod test_support {
    use super::*;

    pub fn variable(raw: u32) -> VariableId {
        VariableId::new(raw).expect("test variable is non-zero")
    }

    pub fn clause_id(raw: u64) -> ClauseId {
        ClauseId::new(raw).expect("test clause id is non-zero")
    }

    pub fn literal(raw: i64) -> Literal {
        Literal::from_dimacs(raw).expect("test literal is valid")
    }

    pub fn clause(values: &[i64]) -> Clause {
        Clause::new(values.iter().copied().map(literal).collect()).expect("test clause is valid")
    }

    pub fn sat_formula() -> Cnf {
        Cnf::new(
            3,
            vec![
                InputClause::new(clause_id(3), clause(&[-1, 3])),
                InputClause::new(clause_id(1), clause(&[1, -2])),
                InputClause::new(clause_id(2), clause(&[2])),
            ],
            SchemaLimits::default(),
        )
        .expect("sample CNF is valid")
    }

    pub fn unsat_formula() -> Cnf {
        Cnf::new(
            1,
            vec![
                InputClause::new(clause_id(1), clause(&[1])),
                InputClause::new(clause_id(2), clause(&[-1])),
            ],
            SchemaLimits::default(),
        )
        .expect("sample UNSAT CNF is valid")
    }

    pub fn model() -> SatModel {
        SatModel::new(
            3,
            vec![
                Assignment::new(variable(3), true),
                Assignment::new(variable(1), true),
                Assignment::new(variable(2), true),
            ],
            SchemaLimits::default(),
        )
        .expect("sample model is complete")
    }

    pub fn proof(cnf: &Cnf) -> UnsatProof {
        UnsatProof::new(
            cnf,
            vec![
                ProofStep::Derive {
                    id: clause_id(3),
                    clause: clause(&[]),
                    rule: ProofRule::Resolution {
                        pivot: variable(1),
                        positive_parent: clause_id(1),
                        negative_parent: clause_id(2),
                    },
                },
                ProofStep::Conclude {
                    empty_clause: clause_id(3),
                },
            ],
            SchemaLimits::default(),
        )
        .expect("sample proof is structurally valid")
    }

    pub fn version_offset() -> usize {
        WIRE_MAGIC.len() + 1
    }

    pub fn extensions_offset() -> usize {
        version_offset() + 2
    }
}

#[cfg(test)]
mod verdict_schema_totality {
    use super::test_support::*;
    use super::*;

    #[test]
    fn every_top_level_schema_round_trips_and_has_distinct_identity() {
        let cnf = sat_formula();
        let model = model();
        let unsat = unsat_formula();
        let proof = proof(&unsat);

        let cnf_bytes = cnf.to_canonical_bytes();
        let model_bytes = model.to_canonical_bytes();
        let proof_bytes = proof.to_canonical_bytes();
        assert_ne!(cnf_bytes, model_bytes);
        assert_ne!(cnf_bytes, proof_bytes);
        assert_ne!(model_bytes, proof_bytes);
        assert_eq!(
            Cnf::from_canonical_bytes(&cnf_bytes, SchemaLimits::default()),
            Ok(cnf)
        );
        assert_eq!(
            SatModel::from_canonical_bytes(&model_bytes, SchemaLimits::default()),
            Ok(model)
        );
        assert_eq!(
            UnsatProof::from_canonical_bytes(&proof_bytes, &unsat, SchemaLimits::default()),
            Ok(proof)
        );
    }

    #[test]
    fn versions_extensions_schema_kinds_and_trailing_bytes_fail_typed() {
        let bytes = sat_formula().to_canonical_bytes();

        let mut future = bytes.clone();
        future[version_offset()..version_offset() + 2].copy_from_slice(&2_u16.to_le_bytes());
        assert!(matches!(
            Cnf::from_canonical_bytes(&future, SchemaLimits::default()),
            Err(SchemaError::UnsupportedVersion {
                schema: CNF_SCHEMA,
                found: 2,
                supported: 1
            })
        ));

        let mut extension = bytes.clone();
        extension[extensions_offset()..extensions_offset() + 2]
            .copy_from_slice(&1_u16.to_le_bytes());
        assert!(matches!(
            Cnf::from_canonical_bytes(&extension, SchemaLimits::default()),
            Err(SchemaError::UnsupportedExtensions {
                schema: CNF_SCHEMA,
                bits: 1
            })
        ));

        let mut unknown = bytes.clone();
        unknown[WIRE_MAGIC.len()] = 255;
        assert_eq!(
            Cnf::from_canonical_bytes(&unknown, SchemaLimits::default()),
            Err(SchemaError::UnknownSchemaKind { found: 255 })
        );
        assert!(matches!(
            SatModel::from_canonical_bytes(&bytes, SchemaLimits::default()),
            Err(SchemaError::SchemaMismatch {
                expected: SchemaKind::SatModel,
                found: 1
            })
        ));

        let mut trailing = bytes;
        trailing.push(0);
        assert!(matches!(
            Cnf::from_canonical_bytes(&trailing, SchemaLimits::default()),
            Err(SchemaError::MalformedEncoding {
                what: "trailing bytes",
                ..
            })
        ));
    }

    #[test]
    fn integer_boundaries_and_resource_boundaries_are_explicit() {
        assert_eq!(
            Literal::from_dimacs(i64::MIN),
            Err(SchemaError::IntegerOutOfRange {
                field: "DIMACS literal",
                value: 1_u128 << 63
            })
        );
        let max = VariableId::new(u32::MAX).expect("u32::MAX is a valid variable");
        assert_eq!(
            Literal::new(max, Polarity::Positive).to_dimacs(),
            i64::from(u32::MAX)
        );
        assert!(ClauseId::new(u64::MAX).is_ok());

        let cnf = sat_formula();
        let exact = SchemaLimits {
            max_variables: cnf.facts().variables,
            max_clauses: cnf.facts().clauses,
            max_literals: cnf.facts().literals,
            max_encoded_bytes: cnf.to_canonical_bytes().len() as u64,
            ..SchemaLimits::default()
        };
        assert_eq!(Cnf::new(3, cnf.clauses().to_vec(), exact), Ok(cnf.clone()));
        let too_small = SchemaLimits {
            max_literals: cnf.facts().literals - 1,
            ..exact
        };
        assert!(matches!(
            Cnf::new(3, cnf.clauses().to_vec(), too_small),
            Err(SchemaError::ResourceLimitExceeded {
                resource: ResourceKind::Literals,
                ..
            })
        ));
    }

    #[test]
    fn inconclusive_and_internal_fault_are_structurally_nonpublishable() {
        let cancelled = AttemptOutcome::Inconclusive(InconclusiveReason::Cancelled);
        let exhausted = AttemptOutcome::Inconclusive(InconclusiveReason::ResourceExhausted {
            resource: ResourceKind::ProofSteps,
            limit: 10,
            actual: 11,
        });
        let fault = AttemptOutcome::InternalFault { code: 7 };
        assert_eq!(cancelled.publishable_artifact(), None);
        assert_eq!(exhausted.publishable_artifact(), None);
        assert_eq!(fault.publishable_artifact(), None);
        assert!(matches!(
            AttemptOutcome::Sat(model()).publishable_artifact(),
            Some(PublishableArtifact::Sat(_))
        ));
    }

    #[test]
    fn forged_collection_counts_fail_before_allocation_and_decoder_recovers() {
        let limits = SchemaLimits::default();

        let mut cnf_writer = Writer::new();
        cnf_writer.header(SchemaKind::Cnf);
        cnf_writer.u32(0);
        cnf_writer.u64(limits.max_clauses);
        assert!(matches!(
            Cnf::from_canonical_bytes(&cnf_writer.finish(), limits),
            Err(SchemaError::MalformedEncoding {
                what: "CNF clauses exceed remaining bytes",
                ..
            })
        ));

        let mut model_writer = Writer::new();
        model_writer.header(SchemaKind::SatModel);
        model_writer.u32(0);
        model_writer.u64(limits.max_assignments);
        assert!(matches!(
            SatModel::from_canonical_bytes(&model_writer.finish(), limits),
            Err(SchemaError::MalformedEncoding {
                what: "SAT assignments exceed remaining bytes",
                ..
            })
        ));

        let mut proof_writer = Writer::new();
        proof_writer.header(SchemaKind::UnsatProof);
        proof_writer.u64(limits.max_proof_steps);
        assert!(matches!(
            UnsatProof::from_canonical_bytes(&proof_writer.finish(), &unsat_formula(), limits),
            Err(SchemaError::MalformedEncoding {
                what: "proof steps exceed remaining bytes",
                ..
            })
        ));

        let valid = sat_formula().to_canonical_bytes();
        assert!(Cnf::from_canonical_bytes(&valid, limits).is_ok());
    }
}

#[cfg(test)]
mod cnf_canonical_property {
    use super::test_support::*;
    use super::*;

    #[test]
    fn permutations_and_duplicate_literals_normalize_to_one_stream() {
        let forward = Cnf::new(
            3,
            vec![
                InputClause::new(clause_id(9), clause(&[3, 1, 1, -2])),
                InputClause::new(clause_id(2), clause(&[-3, 2])),
            ],
            SchemaLimits::default(),
        )
        .expect("forward formula");
        let reverse = Cnf::new(
            3,
            vec![
                InputClause::new(clause_id(2), clause(&[2, -3, 2])),
                InputClause::new(clause_id(9), clause(&[-2, 1, 3])),
            ],
            SchemaLimits::default(),
        )
        .expect("reverse formula");
        assert_eq!(forward, reverse);
        assert_eq!(forward.to_canonical_bytes(), reverse.to_canonical_bytes());
    }

    #[test]
    fn duplicate_ids_tautologies_and_out_of_range_variables_fail() {
        let duplicate = Cnf::new(
            1,
            vec![
                InputClause::new(clause_id(1), clause(&[1])),
                InputClause::new(clause_id(1), clause(&[-1])),
            ],
            SchemaLimits::default(),
        );
        assert_eq!(
            duplicate,
            Err(SchemaError::DuplicateClauseId { id: clause_id(1) })
        );
        assert_eq!(
            Clause::new(vec![literal(1), literal(-1)]),
            Err(SchemaError::TautologicalClause {
                variable: variable(1)
            })
        );
        assert_eq!(
            Cnf::new(
                1,
                vec![InputClause::new(clause_id(1), clause(&[2]))],
                SchemaLimits::default()
            ),
            Err(SchemaError::VariableOutOfRange {
                variable: variable(2),
                declared: 1
            })
        );
    }

    #[test]
    fn noncanonical_clause_and_id_order_is_rejected_during_wire_read() {
        let mut writer = Writer::new();
        writer.header(SchemaKind::Cnf);
        writer.u32(2);
        writer.u64(2);
        writer.u64(2);
        write_clause(&mut writer, &clause(&[2, 1]));
        writer.u64(1);
        write_clause(&mut writer, &clause(&[-1]));
        let bytes = writer.finish();
        assert_eq!(
            Cnf::from_canonical_bytes(&bytes, SchemaLimits::default()),
            Err(SchemaError::NonCanonicalEncoding { schema: CNF_SCHEMA })
        );
    }

    #[test]
    fn seeded_formula_permutations_have_stable_canonical_bytes() {
        let mut seed = 0x517c_c1b7_2722_0a95_u64;
        for round in 0_u64..128 {
            let mut rows = Vec::new();
            for id in 1_u64..=12 {
                seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let a = ((seed >> 32) % 16 + 1) as i64;
                seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let b = ((seed >> 32) % 16 + 1) as i64;
                let signed_a = if seed & 1 == 0 { a } else { -a };
                let signed_b = if a == b {
                    signed_a
                } else if seed & 2 == 0 {
                    b
                } else {
                    -b
                };
                rows.push(InputClause::new(
                    clause_id(id),
                    clause(&[signed_a, signed_b]),
                ));
            }
            let canonical =
                Cnf::new(16, rows.clone(), SchemaLimits::default()).expect("canonical formula");
            let rotation = (round as usize) % rows.len();
            rows.rotate_left(rotation);
            for row in &mut rows {
                let mut literals = row.clause.literals().to_vec();
                literals.reverse();
                row.clause = Clause::new(literals).expect("permuted clause");
            }
            let permuted = Cnf::new(16, rows, SchemaLimits::default()).expect("permuted formula");
            assert_eq!(
                canonical.to_canonical_bytes(),
                permuted.to_canonical_bytes()
            );
        }
    }
}

#[cfg(test)]
mod proof_dependency_model {
    use super::test_support::*;
    use super::*;

    #[test]
    fn resolution_trace_round_trips_with_exact_dependency_facts() {
        let cnf = unsat_formula();
        let proof = proof(&cnf);
        assert_eq!(
            proof.facts(),
            ProofFacts {
                steps: 2,
                derived_clauses: 1,
                derived_literals: 0,
                dependencies: 3,
                deletions: 0,
            }
        );
        let bytes = proof.to_canonical_bytes();
        assert_eq!(
            UnsatProof::from_canonical_bytes(&bytes, &cnf, SchemaLimits::default()),
            Ok(proof)
        );
    }

    #[test]
    fn missing_future_deleted_and_reused_dependencies_fail_typed() {
        let cnf = unsat_formula();
        let missing = UnsatProof::new(
            &cnf,
            vec![
                ProofStep::Derive {
                    id: clause_id(3),
                    clause: clause(&[]),
                    rule: ProofRule::rup(vec![clause_id(9)]),
                },
                ProofStep::Conclude {
                    empty_clause: clause_id(3),
                },
            ],
            SchemaLimits::default(),
        );
        assert_eq!(
            missing,
            Err(SchemaError::MissingDependency {
                step: clause_id(3),
                dependency: clause_id(9)
            })
        );

        let deleted = UnsatProof::new(
            &cnf,
            vec![
                ProofStep::delete(vec![clause_id(1)]),
                ProofStep::Derive {
                    id: clause_id(3),
                    clause: clause(&[]),
                    rule: ProofRule::rup(vec![clause_id(1)]),
                },
                ProofStep::Conclude {
                    empty_clause: clause_id(3),
                },
            ],
            SchemaLimits::default(),
        );
        assert_eq!(
            deleted,
            Err(SchemaError::MissingDependency {
                step: clause_id(3),
                dependency: clause_id(1)
            })
        );

        let reused = UnsatProof::new(
            &cnf,
            vec![
                ProofStep::Derive {
                    id: clause_id(1),
                    clause: clause(&[]),
                    rule: ProofRule::rup(vec![clause_id(2)]),
                },
                ProofStep::Conclude {
                    empty_clause: clause_id(1),
                },
            ],
            SchemaLimits::default(),
        );
        assert_eq!(
            reused,
            Err(SchemaError::ReusedClauseId { id: clause_id(1) })
        );
    }

    #[test]
    fn partial_nonfinal_nonempty_and_duplicate_dependency_proofs_fail() {
        let cnf = unsat_formula();
        assert_eq!(
            UnsatProof::new(&cnf, Vec::new(), SchemaLimits::default()),
            Err(SchemaError::MissingConclusion)
        );
        assert_eq!(
            UnsatProof::new(
                &cnf,
                vec![
                    ProofStep::Conclude {
                        empty_clause: clause_id(1)
                    },
                    ProofStep::delete(vec![clause_id(2)])
                ],
                SchemaLimits::default()
            ),
            Err(SchemaError::ConclusionNotFinal { step_index: 0 })
        );
        assert_eq!(
            UnsatProof::new(
                &cnf,
                vec![ProofStep::Conclude {
                    empty_clause: clause_id(1)
                }],
                SchemaLimits::default()
            ),
            Err(SchemaError::ConclusionNotEmpty {
                clause: clause_id(1)
            })
        );
        assert_eq!(
            UnsatProof::new(
                &cnf,
                vec![
                    ProofStep::Derive {
                        id: clause_id(3),
                        clause: clause(&[]),
                        rule: ProofRule::rup(vec![clause_id(1), clause_id(1)])
                    },
                    ProofStep::Conclude {
                        empty_clause: clause_id(3)
                    }
                ],
                SchemaLimits::default()
            ),
            Err(SchemaError::DuplicateDependency {
                step: clause_id(3),
                dependency: clause_id(1)
            })
        );
        assert_eq!(
            UnsatProof::new(
                &cnf,
                vec![
                    ProofStep::delete(vec![clause_id(1), clause_id(1)]),
                    ProofStep::Conclude {
                        empty_clause: clause_id(2)
                    }
                ],
                SchemaLimits::default()
            ),
            Err(SchemaError::DuplicateDeletionTarget {
                step_index: 0,
                clause: clause_id(1)
            })
        );
    }

    #[test]
    fn unknown_step_and_rule_opcodes_are_distinct_typed_refusals() {
        let cnf = unsat_formula();
        let proof = proof(&cnf);
        let mut unknown_step = proof.to_canonical_bytes();
        unknown_step[WIRE_HEADER_BYTES + 8] = 99;
        assert!(matches!(
            UnsatProof::from_canonical_bytes(&unknown_step, &cnf, SchemaLimits::default()),
            Err(SchemaError::UnknownOpcode {
                schema: UNSAT_PROOF_SCHEMA,
                opcode: 99,
                ..
            })
        ));

        let mut unknown_rule = proof.to_canonical_bytes();
        let rule_offset = WIRE_HEADER_BYTES + 8 + 1 + 8 + 8;
        unknown_rule[rule_offset] = 88;
        assert!(matches!(
            UnsatProof::from_canonical_bytes(&unknown_rule, &cnf, SchemaLimits::default()),
            Err(SchemaError::UnknownOpcode {
                schema: UNSAT_PROOF_SCHEMA,
                opcode: 88,
                ..
            })
        ));
    }
}

#[cfg(test)]
mod verdict_checker_state_model {
    use super::test_support::*;
    use super::*;

    fn swapped_resolution_parents(mut bytes: Vec<u8>) -> Vec<u8> {
        let positive_parent_at = WIRE_HEADER_BYTES + 8 + 1 + 8 + 8 + 1 + 4;
        let negative_parent_at = positive_parent_at + 8;
        let mut positive = [0_u8; 8];
        let mut negative = [0_u8; 8];
        positive.copy_from_slice(&bytes[positive_parent_at..positive_parent_at + 8]);
        negative.copy_from_slice(&bytes[negative_parent_at..negative_parent_at + 8]);
        bytes[positive_parent_at..positive_parent_at + 8].copy_from_slice(&negative);
        bytes[negative_parent_at..negative_parent_at + 8].copy_from_slice(&positive);
        bytes
    }

    #[test]
    fn resolution_and_rup_proofs_are_checked_semantically() {
        let cnf = unsat_formula();
        let cnf_bytes = cnf.to_canonical_bytes();
        let resolution_bytes = proof(&cnf).to_canonical_bytes();
        let resolution = check_unsat_streams(
            &cnf_bytes[..],
            &resolution_bytes[..],
            ProofCheckLimits::default(),
        );
        let receipt = resolution.receipt().expect("valid resolution is verified");
        assert_eq!(receipt.input_clauses, 2);
        assert_eq!(receipt.input_literals, 2);
        assert_eq!(receipt.proof_steps, 2);
        assert_eq!(receipt.derived_clauses, 1);
        assert_eq!(receipt.dependencies, 3);

        let rup = UnsatProof::new(
            &cnf,
            vec![
                ProofStep::Derive {
                    id: clause_id(3),
                    clause: clause(&[]),
                    rule: ProofRule::rup(vec![clause_id(1), clause_id(2)]),
                },
                ProofStep::Conclude {
                    empty_clause: clause_id(3),
                },
            ],
            SchemaLimits::default(),
        )
        .expect("RUP fixture is structurally valid")
        .to_canonical_bytes();
        assert!(matches!(
            check_unsat_streams(&cnf_bytes[..], &rup[..], ProofCheckLimits::default()),
            ProofCheckOutcome::Verified(_)
        ));
    }

    #[test]
    fn corrupted_producer_accepted_proof_is_refused_not_rubber_stamped() {
        let cnf = unsat_formula();
        let cnf_bytes = cnf.to_canonical_bytes();
        let corrupted = swapped_resolution_parents(proof(&cnf).to_canonical_bytes());

        assert!(
            UnsatProof::from_canonical_bytes(&corrupted, &cnf, SchemaLimits::default()).is_ok(),
            "the producer-side structural decoder deliberately accepts this semantic mutant"
        );
        let outcome =
            check_unsat_streams(&cnf_bytes[..], &corrupted[..], ProofCheckLimits::default());
        assert_eq!(
            outcome,
            ProofCheckOutcome::Refused(ProofRefusal::InvalidResolutionPivot {
                step: 3,
                parent: 2,
                pivot: 1,
                expected_positive: true,
            })
        );
        assert_eq!(outcome.receipt(), None);
    }

    #[test]
    fn incomplete_rup_and_deleted_dependencies_are_refused() {
        let cnf = unsat_formula();
        let cnf_bytes = cnf.to_canonical_bytes();
        let incomplete = UnsatProof::new(
            &cnf,
            vec![
                ProofStep::Derive {
                    id: clause_id(3),
                    clause: clause(&[]),
                    rule: ProofRule::rup(vec![clause_id(1)]),
                },
                ProofStep::Conclude {
                    empty_clause: clause_id(3),
                },
            ],
            SchemaLimits::default(),
        )
        .expect("incomplete RUP remains structurally well-formed")
        .to_canonical_bytes();
        assert_eq!(
            check_unsat_streams(&cnf_bytes[..], &incomplete[..], ProofCheckLimits::default()),
            ProofCheckOutcome::Refused(ProofRefusal::RupDidNotConflict { step: 3 })
        );

        let mut writer = Writer::new();
        writer.header(SchemaKind::UnsatProof);
        writer.u64(3);
        writer.u8(2);
        writer.u64(1);
        writer.u64(1);
        writer.u8(1);
        writer.u64(3);
        write_clause(&mut writer, &clause(&[]));
        writer.u8(2);
        writer.u64(2);
        writer.u64(1);
        writer.u64(2);
        writer.u8(3);
        writer.u64(3);
        assert_eq!(
            check_unsat_streams(
                &cnf_bytes[..],
                &writer.finish()[..],
                ProofCheckLimits::default()
            ),
            ProofCheckOutcome::Refused(ProofRefusal::MissingDependency {
                step: 3,
                dependency: 1,
            })
        );
    }
}

#[cfg(test)]
mod checker_independence_guard {
    use super::test_support::*;
    use super::*;
    use std::io::Read;

    #[derive(Debug)]
    struct OneByteReader<'a> {
        bytes: &'a [u8],
        at: usize,
        max_requested: usize,
    }

    impl<'a> OneByteReader<'a> {
        const fn new(bytes: &'a [u8]) -> Self {
            Self {
                bytes,
                at: 0,
                max_requested: 0,
            }
        }
    }

    impl Read for OneByteReader<'_> {
        fn read(&mut self, output: &mut [u8]) -> std::io::Result<usize> {
            self.max_requested = self.max_requested.max(output.len());
            if self.at == self.bytes.len() || output.is_empty() {
                return Ok(0);
            }
            output[0] = self.bytes[self.at];
            self.at += 1;
            Ok(1)
        }
    }

    #[test]
    fn checker_source_has_a_separate_reader_state_and_no_producer_decoder_calls() {
        let source = include_str!("checker.rs");
        let identifiers = source
            .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
            .collect::<BTreeSet<_>>();
        for forbidden in ["UnsatProof", "ProofStep", "ProofRule", "SchemaError"] {
            assert!(
                !identifiers.contains(forbidden),
                "independent checker source names forbidden producer type {forbidden}"
            );
        }
        for forbidden_call in [
            "Cnf::",
            "Clause::",
            "from_canonical_bytes",
            "validate_dependencies",
        ] {
            assert!(
                !source.contains(forbidden_call),
                "independent checker source uses forbidden producer call {forbidden_call}"
            );
        }
        assert!(source.contains("struct StreamDecoder"));
        assert!(source.contains("struct CheckState"));
        assert!(source.contains("fn check_resolution"));
        assert!(source.contains("fn check_rup"));
    }

    #[test]
    fn fragmented_readers_are_consumed_incrementally() {
        let cnf = unsat_formula();
        let cnf_bytes = cnf.to_canonical_bytes();
        let proof_bytes = proof(&cnf).to_canonical_bytes();
        let mut cnf_reader = OneByteReader::new(&cnf_bytes);
        let mut proof_reader = OneByteReader::new(&proof_bytes);
        assert!(matches!(
            check_unsat_streams(
                &mut cnf_reader,
                &mut proof_reader,
                ProofCheckLimits::default()
            ),
            ProofCheckOutcome::Verified(_)
        ));
        assert_eq!(cnf_reader.at, cnf_bytes.len());
        assert_eq!(proof_reader.at, proof_bytes.len());
        assert!(
            cnf_reader.max_requested <= 8 && proof_reader.max_requested <= 8,
            "the checker requested a materializing read"
        );
    }

    #[test]
    fn unknown_version_opcodes_truncation_and_trailing_bytes_fail_closed() {
        let cnf = unsat_formula();
        let cnf_bytes = cnf.to_canonical_bytes();
        let proof_bytes = proof(&cnf).to_canonical_bytes();

        let mut future = proof_bytes.clone();
        future[version_offset()..version_offset() + 2].copy_from_slice(&2_u16.to_le_bytes());
        assert_eq!(
            check_unsat_streams(&cnf_bytes[..], &future[..], ProofCheckLimits::default()),
            ProofCheckOutcome::Refused(ProofRefusal::UnsupportedVersion {
                stream: ProofStream::Proof,
                found: 2,
                supported: 1,
            })
        );

        let mut unknown_step = proof_bytes.clone();
        unknown_step[WIRE_HEADER_BYTES + 8] = 0xfe;
        assert_eq!(
            check_unsat_streams(
                &cnf_bytes[..],
                &unknown_step[..],
                ProofCheckLimits::default()
            ),
            ProofCheckOutcome::Refused(ProofRefusal::UnknownOpcode {
                class: ProofOpcodeClass::Step,
                at: (WIRE_HEADER_BYTES + 8) as u64,
                opcode: 0xfe,
            })
        );

        let rule_at = WIRE_HEADER_BYTES + 8 + 1 + 8 + 8;
        let mut unknown_rule = proof_bytes.clone();
        unknown_rule[rule_at] = 0xfd;
        assert_eq!(
            check_unsat_streams(
                &cnf_bytes[..],
                &unknown_rule[..],
                ProofCheckLimits::default()
            ),
            ProofCheckOutcome::Refused(ProofRefusal::UnknownOpcode {
                class: ProofOpcodeClass::Rule,
                at: rule_at as u64,
                opcode: 0xfd,
            })
        );

        assert!(matches!(
            check_unsat_streams(
                &cnf_bytes[..],
                &proof_bytes[..proof_bytes.len() - 1],
                ProofCheckLimits::default()
            ),
            ProofCheckOutcome::Refused(ProofRefusal::Truncated {
                stream: ProofStream::Proof,
                ..
            })
        ));

        let mut trailing = proof_bytes;
        trailing.push(0);
        assert_eq!(
            check_unsat_streams(&cnf_bytes[..], &trailing[..], ProofCheckLimits::default()),
            ProofCheckOutcome::Refused(ProofRefusal::TrailingInput {
                stream: ProofStream::Proof,
                at: (trailing.len() - 1) as u64,
            })
        );
    }
}

#[cfg(test)]
mod streaming_memory_boundaries {
    use super::test_support::*;
    use super::*;
    use std::io::{Error, Read};

    #[derive(Debug)]
    struct FaultingReader<'a> {
        prefix: &'a [u8],
    }

    #[derive(Debug)]
    struct OverreportingReader;

    impl Read for FaultingReader<'_> {
        fn read(&mut self, output: &mut [u8]) -> std::io::Result<usize> {
            if self.prefix.is_empty() {
                return Err(Error::other("injected read fault"));
            }
            let count = output.len().min(self.prefix.len());
            output[..count].copy_from_slice(&self.prefix[..count]);
            self.prefix = &self.prefix[count..];
            Ok(count)
        }
    }

    impl Read for OverreportingReader {
        fn read(&mut self, _output: &mut [u8]) -> std::io::Result<usize> {
            Ok(usize::MAX)
        }
    }

    #[test]
    fn exact_byte_state_and_work_budgets_pass_then_one_less_is_inconclusive() {
        let cnf = unsat_formula();
        let cnf_bytes = cnf.to_canonical_bytes();
        let proof_bytes = proof(&cnf).to_canonical_bytes();
        let baseline = check_unsat_streams(
            &cnf_bytes[..],
            &proof_bytes[..],
            ProofCheckLimits::default(),
        );
        let receipt = *baseline.receipt().expect("baseline proof verifies");
        let exact = ProofCheckLimits {
            max_cnf_bytes: cnf_bytes.len() as u64,
            max_proof_bytes: proof_bytes.len() as u64,
            max_variables: 1,
            max_input_clauses: 2,
            max_proof_steps: 2,
            max_live_clauses: receipt.peak_live_clauses,
            max_live_literals: receipt.peak_live_literals,
            max_clause_literals: 1,
            max_dependencies: receipt.dependencies,
            max_work_units: receipt.work_units,
        };
        assert!(matches!(
            check_unsat_streams(&cnf_bytes[..], &proof_bytes[..], exact),
            ProofCheckOutcome::Verified(_)
        ));

        let proof_byte_short = ProofCheckLimits {
            max_proof_bytes: exact.max_proof_bytes - 1,
            ..exact
        };
        assert!(matches!(
            check_unsat_streams(&cnf_bytes[..], &proof_bytes[..], proof_byte_short),
            ProofCheckOutcome::Inconclusive(ProofCheckInconclusive::ResourceExhausted {
                resource: ProofCheckResource::ProofBytes,
                ..
            })
        ));

        let state_short = ProofCheckLimits {
            max_live_clauses: exact.max_live_clauses - 1,
            ..exact
        };
        assert!(matches!(
            check_unsat_streams(&cnf_bytes[..], &proof_bytes[..], state_short),
            ProofCheckOutcome::Inconclusive(ProofCheckInconclusive::ResourceExhausted {
                resource: ProofCheckResource::LiveClauses,
                ..
            })
        ));

        let work_short = ProofCheckLimits {
            max_work_units: exact.max_work_units - 1,
            ..exact
        };
        let outcome = check_unsat_streams(&cnf_bytes[..], &proof_bytes[..], work_short);
        assert!(matches!(
            outcome,
            ProofCheckOutcome::Inconclusive(ProofCheckInconclusive::ResourceExhausted {
                resource: ProofCheckResource::WorkUnits,
                ..
            })
        ));
        assert_eq!(outcome.receipt(), None);
    }

    #[test]
    fn cancellation_and_io_faults_are_non_verdicts() {
        let cnf = unsat_formula();
        let cnf_bytes = cnf.to_canonical_bytes();
        let proof_bytes = proof(&cnf).to_canonical_bytes();
        let mut observations = 0_u64;
        let cancelled = check_unsat_streams_with_cancel(
            &cnf_bytes[..],
            &proof_bytes[..],
            ProofCheckLimits::default(),
            || {
                observations += 1;
                observations == 3
            },
        );
        assert_eq!(
            cancelled,
            ProofCheckOutcome::Inconclusive(ProofCheckInconclusive::Cancelled)
        );
        assert_eq!(cancelled.receipt(), None);

        let fault = check_unsat_streams(
            FaultingReader {
                prefix: &cnf_bytes[..8],
            },
            &proof_bytes[..],
            ProofCheckLimits::default(),
        );
        assert_eq!(
            fault,
            ProofCheckOutcome::InternalFault(ProofCheckInternalFault::Io {
                stream: ProofStream::Cnf,
            })
        );
        assert_eq!(fault.receipt(), None);

        let dishonest = std::panic::catch_unwind(|| {
            check_unsat_streams(
                OverreportingReader,
                &proof_bytes[..],
                ProofCheckLimits::default(),
            )
        })
        .expect("contract-violating reader must not panic the checker");
        assert_eq!(
            dishonest,
            ProofCheckOutcome::InternalFault(ProofCheckInternalFault::StateInvariant)
        );
    }

    #[test]
    fn impossible_collection_capacity_is_inconclusive_before_allocation() {
        let mut cnf = Writer::new();
        cnf.header(SchemaKind::Cnf);
        cnf.u32(1);
        cnf.u64(1);
        cnf.u64(1);
        cnf.u64(u64::MAX);
        let limits = ProofCheckLimits {
            max_clause_literals: u64::MAX,
            max_live_literals: u64::MAX,
            ..ProofCheckLimits::default()
        };
        assert!(matches!(
            check_unsat_streams(&cnf.finish()[..], &[][..], limits),
            ProofCheckOutcome::Inconclusive(ProofCheckInconclusive::ResourceExhausted {
                resource: ProofCheckResource::AddressSpace,
                ..
            })
        ));
    }
}

#[cfg(test)]
mod proof_checker_fuzz {
    use super::test_support::*;
    use super::*;

    #[test]
    fn arbitrary_and_single_byte_mutated_streams_never_panic_and_checker_recovers() {
        let cnf = unsat_formula();
        let cnf_bytes = cnf.to_canonical_bytes();
        let valid = proof(&cnf).to_canonical_bytes();
        let mut seed = 0x43d7_913e_6f20_ba11_u64;

        for length in 0_usize..192 {
            let mut bytes = vec![0_u8; length];
            for byte in &mut bytes {
                seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                *byte = (seed >> 32) as u8;
            }
            let result = std::panic::catch_unwind(|| {
                check_unsat_streams(&cnf_bytes[..], &bytes[..], ProofCheckLimits::default())
            });
            assert!(result.is_ok(), "arbitrary proof length {length} panicked");
        }

        for index in 0..valid.len() {
            let mut mutated = valid.clone();
            mutated[index] ^= 0xa5;
            let result = std::panic::catch_unwind(|| {
                check_unsat_streams(&cnf_bytes[..], &mutated[..], ProofCheckLimits::default())
            });
            assert!(result.is_ok(), "proof mutation at byte {index} panicked");
        }
        assert!(matches!(
            check_unsat_streams(&cnf_bytes[..], &valid[..], ProofCheckLimits::default()),
            ProofCheckOutcome::Verified(_)
        ));
    }
}

#[cfg(all(test, unix))]
mod verdict_checker_no_mock_e2e {
    use super::test_support::*;
    use super::*;
    use std::io::Write;
    use std::net::Shutdown;
    use std::os::unix::net::UnixStream;

    fn socket_stream(bytes: Vec<u8>) -> (UnixStream, std::thread::JoinHandle<()>) {
        let (reader, mut writer) = UnixStream::pair().expect("kernel stream pair");
        let handle = std::thread::spawn(move || {
            for chunk in bytes.chunks(3) {
                writer.write_all(chunk).expect("stream chunk");
            }
            writer
                .shutdown(Shutdown::Write)
                .expect("stream write shutdown");
        });
        (reader, handle)
    }

    fn run_over_kernel_streams(cnf: Vec<u8>, proof: Vec<u8>) -> ProofCheckOutcome {
        let (cnf_reader, cnf_writer) = socket_stream(cnf);
        let (proof_reader, proof_writer) = socket_stream(proof);
        let outcome = check_unsat_streams(cnf_reader, proof_reader, ProofCheckLimits::default());
        cnf_writer.join().expect("CNF writer final state");
        proof_writer.join().expect("proof writer final state");
        outcome
    }

    #[test]
    fn real_stream_positive_semantic_failure_and_recovery_are_disjoint() {
        let cnf = unsat_formula();
        let cnf_bytes = cnf.to_canonical_bytes();
        let valid = proof(&cnf).to_canonical_bytes();
        assert!(matches!(
            run_over_kernel_streams(cnf_bytes.clone(), valid.clone()),
            ProofCheckOutcome::Verified(_)
        ));

        let positive_parent_at = WIRE_HEADER_BYTES + 8 + 1 + 8 + 8 + 1 + 4;
        let negative_parent_at = positive_parent_at + 8;
        let mut corrupted = valid.clone();
        let mut positive = [0_u8; 8];
        let mut negative = [0_u8; 8];
        positive.copy_from_slice(&corrupted[positive_parent_at..positive_parent_at + 8]);
        negative.copy_from_slice(&corrupted[negative_parent_at..negative_parent_at + 8]);
        corrupted[positive_parent_at..positive_parent_at + 8].copy_from_slice(&negative);
        corrupted[negative_parent_at..negative_parent_at + 8].copy_from_slice(&positive);
        let refused = run_over_kernel_streams(cnf_bytes.clone(), corrupted);
        assert!(matches!(
            refused,
            ProofCheckOutcome::Refused(ProofRefusal::InvalidResolutionPivot { .. })
        ));
        assert_eq!(refused.receipt(), None);

        assert!(matches!(
            run_over_kernel_streams(cnf_bytes, valid),
            ProofCheckOutcome::Verified(_)
        ));
    }
}

#[cfg(test)]
mod verdict_codec_fuzz {
    use super::test_support::*;
    use super::*;

    const DECODER_CORPUS: &str = include_str!("../tests/corpus/decoder_cases.hex");

    fn decode_hex(encoded: &str) -> Result<Vec<u8>, &'static str> {
        if encoded == "-" {
            return Ok(Vec::new());
        }
        if !encoded.len().is_multiple_of(2) {
            return Err("hex input has odd length");
        }
        let mut decoded = Vec::with_capacity(encoded.len() / 2);
        for pair in encoded.as_bytes().as_chunks::<2>().0 {
            let high = char::from(pair[0])
                .to_digit(16)
                .ok_or("hex input has an invalid high nibble")?;
            let low = char::from(pair[1])
                .to_digit(16)
                .ok_or("hex input has an invalid low nibble")?;
            decoded.push(((high << 4) | low) as u8);
        }
        Ok(decoded)
    }

    #[test]
    fn checked_in_decoder_corpus_is_typed_and_canonical() -> Result<(), String> {
        let proof_context = unsat_formula();
        let mut cases = 0_usize;

        for (line_index, line) in DECODER_CORPUS.lines().enumerate() {
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            cases += 1;
            let mut fields = line.split('|');
            let line_number = line_index + 1;
            let target = fields
                .next()
                .ok_or_else(|| format!("decoder corpus line {line_number} has no target"))?;
            let expectation = fields.next().ok_or_else(|| {
                format!("decoder corpus line {line_number} ({target}) has no expectation")
            })?;
            let name = fields.next().ok_or_else(|| {
                format!("decoder corpus line {line_number} ({target}) has no name")
            })?;
            let encoded = fields.next().ok_or_else(|| {
                format!("decoder corpus line {line_number} ({name}) has no encoded bytes")
            })?;
            assert!(
                fields.next().is_none(),
                "decoder corpus line {line_number} has extra fields"
            );
            let bytes = decode_hex(encoded).map_err(|error| {
                format!("decoder corpus line {line_number} ({name}) has invalid hex: {error}")
            })?;

            let outcome = match target {
                "cnf" => Cnf::from_canonical_bytes(&bytes, SchemaLimits::default())
                    .map(|cnf| cnf.to_canonical_bytes()),
                "proof" => UnsatProof::from_canonical_bytes(
                    &bytes,
                    &proof_context,
                    SchemaLimits::default(),
                )
                .map(|proof| proof.to_canonical_bytes()),
                other => {
                    return Err(format!(
                        "decoder corpus line {line_number} ({name}) has unknown target {other}"
                    ));
                }
            };

            match expectation {
                "canonical" => assert_eq!(
                    outcome.as_deref(),
                    Ok(bytes.as_slice()),
                    "decoder corpus line {line_number} ({name}) failed canonical round-trip"
                ),
                "invalid" => assert!(
                    matches!(
                        outcome,
                        Err(error) if !matches!(error, SchemaError::ResourceLimitExceeded { .. })
                    ),
                    "decoder corpus line {line_number} ({name}) did not produce a typed malformed refusal"
                ),
                "budget" => assert!(
                    matches!(outcome, Err(SchemaError::ResourceLimitExceeded { .. })),
                    "decoder corpus line {line_number} ({name}) did not produce a resource refusal"
                ),
                other => {
                    return Err(format!(
                        "decoder corpus line {line_number} ({name}) has unknown expectation {other}"
                    ));
                }
            }
        }

        assert_eq!(cases, 10, "decoder corpus row count drifted");
        Ok(())
    }

    #[test]
    fn arbitrary_and_mutated_streams_never_panic_and_decoder_recovers() {
        let cnf = unsat_formula();
        let valid_cnf = cnf.to_canonical_bytes();
        let valid_model = model().to_canonical_bytes();
        let valid_proof = proof(&cnf).to_canonical_bytes();
        let mut seed = 0x8d58_ac26_afe1_2e47_u64;

        for length in 0_usize..256 {
            let mut bytes = vec![0_u8; length];
            for byte in &mut bytes {
                seed = seed
                    .wrapping_mul(2_862_933_555_777_941_757)
                    .wrapping_add(3_037_000_493);
                *byte = (seed >> 24) as u8;
            }
            let result = std::panic::catch_unwind(|| {
                let _ = Cnf::from_canonical_bytes(&bytes, SchemaLimits::default());
                let _ = SatModel::from_canonical_bytes(&bytes, SchemaLimits::default());
                let _ = UnsatProof::from_canonical_bytes(&bytes, &cnf, SchemaLimits::default());
            });
            assert!(result.is_ok(), "arbitrary length {length} panicked");
        }

        for baseline in [&valid_cnf, &valid_model, &valid_proof] {
            for index in 0..baseline.len() {
                let mut mutated = baseline.clone();
                mutated[index] ^= 0xa5;
                let result = std::panic::catch_unwind(|| {
                    let _ = Cnf::from_canonical_bytes(&mutated, SchemaLimits::default());
                    let _ = SatModel::from_canonical_bytes(&mutated, SchemaLimits::default());
                    let _ =
                        UnsatProof::from_canonical_bytes(&mutated, &cnf, SchemaLimits::default());
                });
                assert!(result.is_ok(), "mutation at byte {index} panicked");
            }
        }

        assert!(Cnf::from_canonical_bytes(&valid_cnf, SchemaLimits::default()).is_ok());
        assert!(SatModel::from_canonical_bytes(&valid_model, SchemaLimits::default()).is_ok());
        assert!(
            UnsatProof::from_canonical_bytes(&valid_proof, &cnf, SchemaLimits::default()).is_ok()
        );
    }
}

#[cfg(test)]
mod verdict_schema_no_mock_e2e {
    use super::test_support::*;
    use super::*;
    use std::fs::OpenOptions;
    use std::io::Write;
    use std::path::Path;

    const E2E_MAX_WORKERS: usize = 41;

    fn hex(bytes: &[u8]) -> String {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";
        let mut encoded = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            encoded.push(char::from(DIGITS[usize::from(byte >> 4)]));
            encoded.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
        }
        encoded
    }

    fn write_new(path: &Path, contents: &str) {
        let mut output = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .expect("Verdict E2E artifact path must be new and writable");
        output
            .write_all(contents.as_bytes())
            .expect("Verdict E2E artifact write must complete");
        output
            .sync_all()
            .expect("Verdict E2E artifact must be durable before test exit");
    }

    fn publish_e2e_artifacts(
        semantic: &str,
        observed_encoded_bytes: usize,
        workers_spawned: usize,
    ) {
        let semantic_path = std::env::var_os("FLN_VERDICT_E2E_SEMANTIC_PATH");
        let telemetry_path = std::env::var_os("FLN_VERDICT_E2E_TELEMETRY_PATH");
        assert_eq!(
            semantic_path.is_some(),
            telemetry_path.is_some(),
            "FLN_VERDICT_E2E_SEMANTIC_PATH and FLN_VERDICT_E2E_TELEMETRY_PATH must be paired"
        );
        match (semantic_path, telemetry_path) {
            (None, None) => {}
            (Some(semantic_path), Some(telemetry_path)) => {
                assert!(
                    workers_spawned <= E2E_MAX_WORKERS,
                    "Verdict E2E exceeded its declared worker bound"
                );
                let telemetry = format!(
                    "{{\"event\":\"phase_resources\",\"max_encoded_bytes\":{},\
                     \"max_workers\":{E2E_MAX_WORKERS},\
                     \"observed_encoded_bytes\":{observed_encoded_bytes},\
                     \"schema\":\"fln.e2e.verdict-telemetry\",\
                     \"timing_used_as_gate\":false,\"version\":1,\
                     \"workers_spawned\":{workers_spawned}}}\n",
                    SchemaLimits::default().max_encoded_bytes
                );
                write_new(Path::new(&semantic_path), semantic);
                write_new(Path::new(&telemetry_path), &telemetry);
            }
            _ => {}
        }
    }

    #[test]
    fn real_positive_failure_recovery_and_thread_matrix_share_authoritative_bytes() {
        let phase =
            std::env::var("FLN_VERDICT_E2E_PHASE").unwrap_or_else(|_| "positive".to_owned());
        let cnf = sat_formula();
        let model = model();
        assert_eq!(model.satisfies(&cnf), Ok(true));

        let false_model = SatModel::new(
            3,
            vec![
                Assignment::new(variable(1), false),
                Assignment::new(variable(2), false),
                Assignment::new(variable(3), false),
            ],
            SchemaLimits::default(),
        )
        .expect("complete false model");
        assert_eq!(false_model.satisfies(&cnf), Ok(false));

        let cnf_bytes = cnf.to_canonical_bytes();
        let model_bytes = model.to_canonical_bytes();
        let unsat = unsat_formula();
        let unsat_bytes = unsat.to_canonical_bytes();
        let proof = proof(&unsat);
        let proof_bytes = proof.to_canonical_bytes();

        match phase.as_str() {
            "positive" => {
                assert!(matches!(
                    check_unsat_streams(
                        &unsat_bytes[..],
                        &proof_bytes[..],
                        ProofCheckLimits::default()
                    ),
                    ProofCheckOutcome::Verified(_)
                ));
                let mut thread_cnf_hex = Vec::new();
                let mut workers_spawned = 0;
                for workers in [1_usize, 8, 32] {
                    let mut handles = Vec::with_capacity(workers);
                    for _ in 0..workers {
                        let cloned = cnf.clone();
                        handles.push(std::thread::spawn(move || cloned.to_canonical_bytes()));
                    }
                    workers_spawned += handles.len();
                    for handle in handles {
                        assert_eq!(handle.join().expect("encoder thread"), cnf_bytes);
                    }
                    thread_cnf_hex.push(hex(&cnf_bytes));
                }
                let semantic = format!(
                    "{{\"cnf_hex\":\"{}\",\"data_grade\":\"verified\",\
                     \"event\":\"positive\",\"model_hex\":\"{}\",\"model_satisfies\":true,\
                     \"proof_hex\":\"{}\",\"schema\":\"fln.e2e.verdict-semantic\",\
                     \"status\":\"pass\",\"thread_cnf_hex\":[\"{}\",\"{}\",\"{}\"],\
                     \"threads\":[1,8,32],\"unsat_cnf_hex\":\"{}\",\"version\":1}}\n",
                    hex(&cnf_bytes),
                    hex(&model_bytes),
                    hex(&proof_bytes),
                    thread_cnf_hex[0],
                    thread_cnf_hex[1],
                    thread_cnf_hex[2],
                    hex(&unsat_bytes)
                );
                publish_e2e_artifacts(
                    &semantic,
                    cnf_bytes.len() + model_bytes.len() + unsat_bytes.len() + proof_bytes.len(),
                    workers_spawned,
                );
            }
            "failure" => {
                let mut corrupted = proof_bytes.clone();
                corrupted[WIRE_HEADER_BYTES + 8] = 0xff;
                let error =
                    UnsatProof::from_canonical_bytes(&corrupted, &unsat, SchemaLimits::default())
                        .expect_err("unknown proof opcode must be refused");
                assert_eq!(
                    error,
                    SchemaError::UnknownOpcode {
                        schema: UNSAT_PROOF_SCHEMA,
                        at: WIRE_HEADER_BYTES + 8,
                        opcode: 0xff,
                    }
                );
                assert_eq!(
                    check_unsat_streams(
                        &unsat_bytes[..],
                        &corrupted[..],
                        ProofCheckLimits::default()
                    ),
                    ProofCheckOutcome::Refused(ProofRefusal::UnknownOpcode {
                        class: ProofOpcodeClass::Step,
                        at: (WIRE_HEADER_BYTES + 8) as u64,
                        opcode: 0xff,
                    })
                );
                let semantic = format!(
                    "{{\"corrupted_proof_hex\":\"{}\",\"data_grade\":\"verified\",\
                     \"error_at\":{},\"error_code\":\"unknown_opcode\",\"event\":\"failure\",\
                     \"opcode\":255,\"partial_artifact_published\":false,\
                     \"schema\":\"fln.e2e.verdict-semantic\",\"status\":\"refused\",\
                     \"version\":1}}\n",
                    hex(&corrupted),
                    WIRE_HEADER_BYTES + 8
                );
                publish_e2e_artifacts(&semantic, corrupted.len(), 0);
                println!(
                    "FLN_VERDICT_E2E_EXPECTED_FAILURE: unknown proof opcode 255 at byte {}",
                    WIRE_HEADER_BYTES + 8
                );
                assert_ne!(
                    phase,
                    "failure",
                    "FLN_VERDICT_E2E_EXPECTED_FAILURE: unknown proof opcode 255 at byte {}",
                    WIRE_HEADER_BYTES + 8
                );
            }
            "recovery" => {
                assert_eq!(
                    Cnf::from_canonical_bytes(&cnf_bytes, SchemaLimits::default()),
                    Ok(cnf)
                );
                assert_eq!(
                    UnsatProof::from_canonical_bytes(&proof_bytes, &unsat, SchemaLimits::default()),
                    Ok(proof)
                );
                assert!(matches!(
                    check_unsat_streams(
                        &unsat_bytes[..],
                        &proof_bytes[..],
                        ProofCheckLimits::default()
                    ),
                    ProofCheckOutcome::Verified(_)
                ));
                let semantic = format!(
                    "{{\"cnf_hex\":\"{}\",\"data_grade\":\"verified\",\
                     \"event\":\"recovery\",\"proof_hex\":\"{}\",\
                     \"recovered_after\":\"unknown_opcode\",\
                     \"schema\":\"fln.e2e.verdict-semantic\",\"status\":\"pass\",\
                     \"version\":1}}\n",
                    hex(&cnf_bytes),
                    hex(&proof_bytes)
                );
                publish_e2e_artifacts(&semantic, cnf_bytes.len() + proof_bytes.len(), 0);
            }
            other => assert_eq!(other, "recovery", "unknown FLN_VERDICT_E2E_PHASE"),
        }
    }
}
