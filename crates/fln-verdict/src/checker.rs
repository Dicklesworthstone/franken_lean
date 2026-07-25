//! Independent, bounded, streaming validation of Verdict UNSAT certificates.
//!
//! This module intentionally owns its wire reader, clause representation, proof
//! state, and rule semantics. It consumes the certificate one step at a time and
//! never constructs the producer's materialized proof representation.

use std::collections::{BTreeMap, BTreeSet};
use std::io::{ErrorKind, Read};

const CHECKER_WIRE_MAGIC: [u8; 8] = *b"FLNVRDCT";
const CHECKER_SCHEMA_VERSION: u16 = 1;
const CNF_KIND: u8 = 1;
const UNSAT_PROOF_KIND: u8 = 3;

/// Which independently decoded stream caused an outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofStream {
    Cnf,
    Proof,
}

/// A bounded resource owned by the streaming checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofCheckResource {
    CnfBytes,
    ProofBytes,
    Variables,
    InputClauses,
    ProofSteps,
    LiveClauses,
    LiveLiterals,
    ClauseLiterals,
    Dependencies,
    WorkUnits,
    AddressSpace,
}

/// Independent checker budgets. Every dimension is a hard upper bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofCheckLimits {
    pub max_cnf_bytes: u64,
    pub max_proof_bytes: u64,
    pub max_variables: u32,
    pub max_input_clauses: u64,
    pub max_proof_steps: u64,
    pub max_live_clauses: u64,
    pub max_live_literals: u64,
    pub max_clause_literals: u64,
    pub max_dependencies: u64,
    pub max_work_units: u64,
}

impl Default for ProofCheckLimits {
    fn default() -> Self {
        Self {
            max_cnf_bytes: 256 * 1024 * 1024,
            max_proof_bytes: 256 * 1024 * 1024,
            max_variables: 16_000_000,
            max_input_clauses: 16_000_000,
            max_proof_steps: 128_000_000,
            max_live_clauses: 16_000_000,
            max_live_literals: 128_000_000,
            max_clause_literals: 16_000_000,
            max_dependencies: 512_000_000,
            max_work_units: 1_000_000_000,
        }
    }
}

/// The location of an unknown proof opcode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofOpcodeClass {
    Step,
    Rule,
}

/// A typed refusal of untrusted bytes or invalid proof semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofRefusal {
    InvalidMagic {
        stream: ProofStream,
    },
    SchemaMismatch {
        stream: ProofStream,
        expected: u8,
        found: u8,
    },
    UnsupportedVersion {
        stream: ProofStream,
        found: u16,
        supported: u16,
    },
    UnsupportedExtensions {
        stream: ProofStream,
        bits: u16,
    },
    Truncated {
        stream: ProofStream,
        at: u64,
        needed: u64,
    },
    TrailingInput {
        stream: ProofStream,
        at: u64,
    },
    InvalidVariableId {
        stream: ProofStream,
        at: u64,
        raw: u32,
    },
    VariableOutOfRange {
        stream: ProofStream,
        at: u64,
        variable: u32,
        declared: u32,
    },
    InvalidClauseId {
        stream: ProofStream,
        at: u64,
        raw: u64,
    },
    UnknownPolarity {
        stream: ProofStream,
        at: u64,
        found: u8,
    },
    NonCanonicalClause {
        stream: ProofStream,
        clause: u64,
    },
    TautologicalClause {
        stream: ProofStream,
        clause: u64,
        variable: u32,
    },
    NonCanonicalInputClauseOrder {
        previous: u64,
        current: u64,
    },
    ReusedClauseId {
        id: u64,
    },
    UnknownOpcode {
        class: ProofOpcodeClass,
        at: u64,
        opcode: u8,
    },
    DuplicateDependency {
        step: u64,
        dependency: u64,
    },
    NonCanonicalDependencyOrder {
        step: u64,
        previous: u64,
        current: u64,
    },
    MissingDependency {
        step: u64,
        dependency: u64,
    },
    EmptyDependencyChain {
        step: u64,
    },
    EmptyDeletion {
        step_index: u64,
    },
    DuplicateDeletionTarget {
        step_index: u64,
        clause: u64,
    },
    NonCanonicalDeletionOrder {
        step_index: u64,
        previous: u64,
        current: u64,
    },
    DeletingMissingClause {
        step_index: u64,
        clause: u64,
    },
    InvalidResolutionPivot {
        step: u64,
        parent: u64,
        pivot: u32,
        expected_positive: bool,
    },
    TautologicalResolvent {
        step: u64,
        variable: u32,
    },
    ResolutionMismatch {
        step: u64,
    },
    RupDidNotConflict {
        step: u64,
    },
    ConclusionNotFinal {
        step_index: u64,
    },
    ConclusionMissingClause {
        clause: u64,
    },
    ConclusionNotEmpty {
        clause: u64,
    },
    MissingConclusion,
}

/// A non-verdict caused by cancellation or an exhausted checker budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofCheckInconclusive {
    Cancelled,
    ResourceExhausted {
        resource: ProofCheckResource,
        limit: u64,
        actual: u64,
    },
}

/// A checker implementation/input-channel fault, never a proof verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofCheckInternalFault {
    Io { stream: ProofStream },
    StateInvariant,
}

/// Bounded facts emitted only after the complete proof and both EOFs validate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofCheckReceipt {
    pub schema_version: u16,
    pub input_clauses: u64,
    pub input_literals: u64,
    pub proof_steps: u64,
    pub derived_clauses: u64,
    pub dependencies: u64,
    pub peak_live_clauses: u64,
    pub peak_live_literals: u64,
    pub work_units: u64,
    pub cnf_bytes_read: u64,
    pub proof_bytes_read: u64,
}

/// The four disjoint terminal classes of an independent proof-check attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofCheckOutcome {
    Verified(ProofCheckReceipt),
    Refused(ProofRefusal),
    Inconclusive(ProofCheckInconclusive),
    InternalFault(ProofCheckInternalFault),
}

impl ProofCheckOutcome {
    /// Only a complete semantic check can produce a receipt.
    pub const fn receipt(&self) -> Option<&ProofCheckReceipt> {
        match self {
            Self::Verified(receipt) => Some(receipt),
            Self::Refused(_) | Self::Inconclusive(_) | Self::InternalFault(_) => None,
        }
    }
}

/// Check canonical CNF and UNSAT-proof byte streams without materializing the proof.
pub fn check_unsat_streams<C, P>(cnf: C, proof: P, limits: ProofCheckLimits) -> ProofCheckOutcome
where
    C: Read,
    P: Read,
{
    check_unsat_streams_with_cancel(cnf, proof, limits, || false)
}

/// As [`check_unsat_streams`], with a deterministic cancellation observation hook.
pub fn check_unsat_streams_with_cancel<C, P, F>(
    cnf: C,
    proof: P,
    limits: ProofCheckLimits,
    mut cancelled: F,
) -> ProofCheckOutcome
where
    C: Read,
    P: Read,
    F: FnMut() -> bool,
{
    match check_inner(cnf, proof, limits, &mut cancelled) {
        Ok(receipt) => ProofCheckOutcome::Verified(receipt),
        Err(Stop::Refused(reason)) => ProofCheckOutcome::Refused(reason),
        Err(Stop::Inconclusive(reason)) => ProofCheckOutcome::Inconclusive(reason),
        Err(Stop::InternalFault(fault)) => ProofCheckOutcome::InternalFault(fault),
    }
}

#[derive(Debug)]
enum Stop {
    Refused(ProofRefusal),
    Inconclusive(ProofCheckInconclusive),
    InternalFault(ProofCheckInternalFault),
}

type CheckResult<T> = Result<T, Stop>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct CheckLiteral {
    variable: u32,
    positive: bool,
}

#[derive(Debug, Default)]
struct CheckState {
    live: BTreeMap<u64, Vec<CheckLiteral>>,
    all_ids: BTreeSet<u64>,
    live_literals: u64,
    peak_live_clauses: u64,
    peak_live_literals: u64,
}

impl CheckState {
    fn reserve_id(&mut self, id: u64) -> CheckResult<()> {
        if self.all_ids.insert(id) {
            Ok(())
        } else {
            Err(Stop::Refused(ProofRefusal::ReusedClauseId { id }))
        }
    }

    fn insert(
        &mut self,
        id: u64,
        clause: Vec<CheckLiteral>,
        limits: ProofCheckLimits,
    ) -> CheckResult<()> {
        let clause_literals = usize_to_u64(clause.len())?;
        let next_clauses = usize_to_u64(self.live.len())?
            .checked_add(1)
            .ok_or_else(|| exhausted(ProofCheckResource::LiveClauses, limits.max_live_clauses))?;
        enforce(
            ProofCheckResource::LiveClauses,
            limits.max_live_clauses,
            next_clauses,
        )?;
        let next_literals = self
            .live_literals
            .checked_add(clause_literals)
            .ok_or_else(|| exhausted(ProofCheckResource::LiveLiterals, limits.max_live_literals))?;
        enforce(
            ProofCheckResource::LiveLiterals,
            limits.max_live_literals,
            next_literals,
        )?;
        if self.live.insert(id, clause).is_some() {
            return Err(Stop::InternalFault(ProofCheckInternalFault::StateInvariant));
        }
        self.live_literals = next_literals;
        self.peak_live_clauses = self.peak_live_clauses.max(next_clauses);
        self.peak_live_literals = self.peak_live_literals.max(next_literals);
        Ok(())
    }

    fn remove(&mut self, id: u64) -> CheckResult<Option<Vec<CheckLiteral>>> {
        let Some(clause) = self.live.remove(&id) else {
            return Ok(None);
        };
        let count = usize_to_u64(clause.len())?;
        self.live_literals = self
            .live_literals
            .checked_sub(count)
            .ok_or(Stop::InternalFault(ProofCheckInternalFault::StateInvariant))?;
        Ok(Some(clause))
    }
}

#[derive(Debug)]
struct StreamDecoder<R> {
    reader: R,
    stream: ProofStream,
    resource: ProofCheckResource,
    max_bytes: u64,
    at: u64,
}

impl<R: Read> StreamDecoder<R> {
    const fn new(
        reader: R,
        stream: ProofStream,
        resource: ProofCheckResource,
        max_bytes: u64,
    ) -> Self {
        Self {
            reader,
            stream,
            resource,
            max_bytes,
            at: 0,
        }
    }

    const fn position(&self) -> u64 {
        self.at
    }

    fn fixed<const N: usize>(&mut self) -> CheckResult<[u8; N]> {
        let amount = u64::try_from(N)
            .map_err(|_| exhausted(ProofCheckResource::AddressSpace, usize::MAX as u64))?;
        let end = self
            .at
            .checked_add(amount)
            .ok_or_else(|| exhausted(self.resource, self.max_bytes))?;
        enforce(self.resource, self.max_bytes, end)?;

        let mut bytes = [0_u8; N];
        let mut filled = 0;
        while filled < N {
            let Some(remaining) = bytes.get_mut(filled..) else {
                return Err(Stop::InternalFault(ProofCheckInternalFault::StateInvariant));
            };
            let remaining_len = remaining.len();
            match self.reader.read(remaining) {
                Ok(0) => {
                    return Err(Stop::Refused(ProofRefusal::Truncated {
                        stream: self.stream,
                        at: self.at,
                        needed: u64::try_from(N - filled).unwrap_or(u64::MAX),
                    }));
                }
                Ok(read) if read > remaining_len => {
                    return Err(Stop::InternalFault(ProofCheckInternalFault::StateInvariant));
                }
                Ok(read) => {
                    filled = filled
                        .checked_add(read)
                        .ok_or(Stop::InternalFault(ProofCheckInternalFault::StateInvariant))?;
                    let read = u64::try_from(read)
                        .map_err(|_| exhausted(ProofCheckResource::AddressSpace, u64::MAX))?;
                    self.at = self
                        .at
                        .checked_add(read)
                        .ok_or_else(|| exhausted(self.resource, self.max_bytes))?;
                }
                Err(error) if error.kind() == ErrorKind::Interrupted => {}
                Err(_) => {
                    return Err(Stop::InternalFault(ProofCheckInternalFault::Io {
                        stream: self.stream,
                    }));
                }
            }
        }
        Ok(bytes)
    }

    fn u8(&mut self) -> CheckResult<u8> {
        let [value] = self.fixed::<1>()?;
        Ok(value)
    }

    fn u16(&mut self) -> CheckResult<u16> {
        Ok(u16::from_le_bytes(self.fixed()?))
    }

    fn u32(&mut self) -> CheckResult<u32> {
        Ok(u32::from_le_bytes(self.fixed()?))
    }

    fn u64(&mut self) -> CheckResult<u64> {
        Ok(u64::from_le_bytes(self.fixed()?))
    }

    fn header(&mut self, expected_kind: u8) -> CheckResult<()> {
        if self.fixed::<8>()? != CHECKER_WIRE_MAGIC {
            return Err(Stop::Refused(ProofRefusal::InvalidMagic {
                stream: self.stream,
            }));
        }
        let found = self.u8()?;
        if found != expected_kind {
            return Err(Stop::Refused(ProofRefusal::SchemaMismatch {
                stream: self.stream,
                expected: expected_kind,
                found,
            }));
        }
        let version = self.u16()?;
        if version != CHECKER_SCHEMA_VERSION {
            return Err(Stop::Refused(ProofRefusal::UnsupportedVersion {
                stream: self.stream,
                found: version,
                supported: CHECKER_SCHEMA_VERSION,
            }));
        }
        let extensions = self.u16()?;
        if extensions != 0 {
            return Err(Stop::Refused(ProofRefusal::UnsupportedExtensions {
                stream: self.stream,
                bits: extensions,
            }));
        }
        Ok(())
    }

    fn finish(&mut self) -> CheckResult<()> {
        let trailing_at = self.at;
        let mut byte = [0_u8; 1];
        loop {
            match self.reader.read(&mut byte) {
                Ok(0) => return Ok(()),
                Ok(read) if read > byte.len() => {
                    return Err(Stop::InternalFault(ProofCheckInternalFault::StateInvariant));
                }
                Ok(_) => {
                    self.at = self
                        .at
                        .checked_add(1)
                        .ok_or_else(|| exhausted(self.resource, self.max_bytes))?;
                    return Err(Stop::Refused(ProofRefusal::TrailingInput {
                        stream: self.stream,
                        at: trailing_at,
                    }));
                }
                Err(error) if error.kind() == ErrorKind::Interrupted => {}
                Err(_) => {
                    return Err(Stop::InternalFault(ProofCheckInternalFault::Io {
                        stream: self.stream,
                    }));
                }
            }
        }
    }
}

#[derive(Debug, Default)]
struct WorkMeter {
    used: u64,
    limit: u64,
}

impl WorkMeter {
    const fn new(limit: u64) -> Self {
        Self { used: 0, limit }
    }

    fn spend(&mut self, amount: u64) -> CheckResult<()> {
        let actual = self
            .used
            .checked_add(amount)
            .ok_or_else(|| exhausted(ProofCheckResource::WorkUnits, self.limit))?;
        enforce(ProofCheckResource::WorkUnits, self.limit, actual)?;
        self.used = actual;
        Ok(())
    }
}

fn check_inner<C, P, F>(
    cnf: C,
    proof: P,
    limits: ProofCheckLimits,
    cancelled: &mut F,
) -> CheckResult<ProofCheckReceipt>
where
    C: Read,
    P: Read,
    F: FnMut() -> bool,
{
    observe_cancellation(cancelled)?;
    let mut work = WorkMeter::new(limits.max_work_units);
    let mut state = CheckState::default();
    let mut cnf_reader = StreamDecoder::new(
        cnf,
        ProofStream::Cnf,
        ProofCheckResource::CnfBytes,
        limits.max_cnf_bytes,
    );
    cnf_reader.header(CNF_KIND)?;
    let variable_count = cnf_reader.u32()?;
    enforce(
        ProofCheckResource::Variables,
        u64::from(limits.max_variables),
        u64::from(variable_count),
    )?;
    let input_clauses = cnf_reader.u64()?;
    enforce(
        ProofCheckResource::InputClauses,
        limits.max_input_clauses,
        input_clauses,
    )?;

    let mut input_literals = 0_u64;
    let mut previous_input_id = None;
    for _ in 0..input_clauses {
        observe_cancellation(cancelled)?;
        work.spend(1)?;
        let id_at = cnf_reader.position();
        let id = read_clause_id(&mut cnf_reader, id_at)?;
        if let Some(previous) = previous_input_id
            && id <= previous
        {
            return Err(Stop::Refused(ProofRefusal::NonCanonicalInputClauseOrder {
                previous,
                current: id,
            }));
        }
        previous_input_id = Some(id);
        state.reserve_id(id)?;
        let clause = read_clause(&mut cnf_reader, id, variable_count, limits, &mut work)?;
        input_literals = checked_add_resource(
            input_literals,
            usize_to_u64(clause.len())?,
            ProofCheckResource::LiveLiterals,
            limits.max_live_literals,
        )?;
        state.insert(id, clause, limits)?;
    }
    cnf_reader.finish()?;
    let cnf_bytes_read = cnf_reader.position();

    observe_cancellation(cancelled)?;
    let mut proof_reader = StreamDecoder::new(
        proof,
        ProofStream::Proof,
        ProofCheckResource::ProofBytes,
        limits.max_proof_bytes,
    );
    proof_reader.header(UNSAT_PROOF_KIND)?;
    let proof_steps = proof_reader.u64()?;
    enforce(
        ProofCheckResource::ProofSteps,
        limits.max_proof_steps,
        proof_steps,
    )?;

    let mut dependencies = 0_u64;
    let mut derived_clauses = 0_u64;
    let mut concluded = false;
    for step_index in 0..proof_steps {
        observe_cancellation(cancelled)?;
        work.spend(1)?;
        let opcode_at = proof_reader.position();
        match proof_reader.u8()? {
            1 => {
                let id_at = proof_reader.position();
                let id = read_clause_id(&mut proof_reader, id_at)?;
                state.reserve_id(id)?;
                let clause = read_clause(&mut proof_reader, id, variable_count, limits, &mut work)?;
                let rule_at = proof_reader.position();
                match proof_reader.u8()? {
                    1 => {
                        let pivot_at = proof_reader.position();
                        let pivot = read_variable(&mut proof_reader, pivot_at, variable_count)?;
                        let positive_at = proof_reader.position();
                        let positive_parent = read_clause_id(&mut proof_reader, positive_at)?;
                        let negative_at = proof_reader.position();
                        let negative_parent = read_clause_id(&mut proof_reader, negative_at)?;
                        if positive_parent == negative_parent {
                            return Err(Stop::Refused(ProofRefusal::DuplicateDependency {
                                step: id,
                                dependency: positive_parent,
                            }));
                        }
                        dependencies = checked_add_resource(
                            dependencies,
                            2,
                            ProofCheckResource::Dependencies,
                            limits.max_dependencies,
                        )?;
                        check_resolution(
                            &state,
                            id,
                            &clause,
                            pivot,
                            positive_parent,
                            negative_parent,
                            limits,
                            &mut work,
                        )?;
                    }
                    2 => {
                        let count = proof_reader.u64()?;
                        if count == 0 {
                            return Err(Stop::Refused(ProofRefusal::EmptyDependencyChain {
                                step: id,
                            }));
                        }
                        dependencies = checked_add_resource(
                            dependencies,
                            count,
                            ProofCheckResource::Dependencies,
                            limits.max_dependencies,
                        )?;
                        let capacity = bounded_capacity::<u64>(
                            count,
                            ProofCheckResource::Dependencies,
                            limits.max_dependencies,
                        )?;
                        let mut antecedents = Vec::with_capacity(capacity);
                        let mut previous = None;
                        for _ in 0..count {
                            work.spend(1)?;
                            let dependency_at = proof_reader.position();
                            let dependency = read_clause_id(&mut proof_reader, dependency_at)?;
                            if let Some(previous_id) = previous {
                                if dependency == previous_id {
                                    return Err(Stop::Refused(ProofRefusal::DuplicateDependency {
                                        step: id,
                                        dependency,
                                    }));
                                }
                                if dependency < previous_id {
                                    return Err(Stop::Refused(
                                        ProofRefusal::NonCanonicalDependencyOrder {
                                            step: id,
                                            previous: previous_id,
                                            current: dependency,
                                        },
                                    ));
                                }
                            }
                            require_live(&state, id, dependency)?;
                            previous = Some(dependency);
                            antecedents.push(dependency);
                        }
                        check_rup(&state, id, &clause, &antecedents, &mut work, cancelled)?;
                    }
                    opcode => {
                        return Err(Stop::Refused(ProofRefusal::UnknownOpcode {
                            class: ProofOpcodeClass::Rule,
                            at: rule_at,
                            opcode,
                        }));
                    }
                }
                derived_clauses = derived_clauses.checked_add(1).ok_or_else(|| {
                    exhausted(ProofCheckResource::ProofSteps, limits.max_proof_steps)
                })?;
                state.insert(id, clause, limits)?;
            }
            2 => {
                let count = proof_reader.u64()?;
                if count == 0 {
                    return Err(Stop::Refused(ProofRefusal::EmptyDeletion { step_index }));
                }
                dependencies = checked_add_resource(
                    dependencies,
                    count,
                    ProofCheckResource::Dependencies,
                    limits.max_dependencies,
                )?;
                let mut previous = None;
                for _ in 0..count {
                    work.spend(1)?;
                    let clause_at = proof_reader.position();
                    let clause = read_clause_id(&mut proof_reader, clause_at)?;
                    if let Some(previous_id) = previous {
                        if clause == previous_id {
                            return Err(Stop::Refused(ProofRefusal::DuplicateDeletionTarget {
                                step_index,
                                clause,
                            }));
                        }
                        if clause < previous_id {
                            return Err(Stop::Refused(ProofRefusal::NonCanonicalDeletionOrder {
                                step_index,
                                previous: previous_id,
                                current: clause,
                            }));
                        }
                    }
                    previous = Some(clause);
                    if state.remove(clause)?.is_none() {
                        return Err(Stop::Refused(ProofRefusal::DeletingMissingClause {
                            step_index,
                            clause,
                        }));
                    }
                }
            }
            3 => {
                let clause_at = proof_reader.position();
                let clause = read_clause_id(&mut proof_reader, clause_at)?;
                if step_index + 1 != proof_steps {
                    return Err(Stop::Refused(ProofRefusal::ConclusionNotFinal {
                        step_index,
                    }));
                }
                let Some(value) = state.live.get(&clause) else {
                    return Err(Stop::Refused(ProofRefusal::ConclusionMissingClause {
                        clause,
                    }));
                };
                if !value.is_empty() {
                    return Err(Stop::Refused(ProofRefusal::ConclusionNotEmpty { clause }));
                }
                dependencies = checked_add_resource(
                    dependencies,
                    1,
                    ProofCheckResource::Dependencies,
                    limits.max_dependencies,
                )?;
                concluded = true;
            }
            opcode => {
                return Err(Stop::Refused(ProofRefusal::UnknownOpcode {
                    class: ProofOpcodeClass::Step,
                    at: opcode_at,
                    opcode,
                }));
            }
        }
    }

    if !concluded {
        return Err(Stop::Refused(ProofRefusal::MissingConclusion));
    }
    proof_reader.finish()?;
    let proof_bytes_read = proof_reader.position();
    Ok(ProofCheckReceipt {
        schema_version: CHECKER_SCHEMA_VERSION,
        input_clauses,
        input_literals,
        proof_steps,
        derived_clauses,
        dependencies,
        peak_live_clauses: state.peak_live_clauses,
        peak_live_literals: state.peak_live_literals,
        work_units: work.used,
        cnf_bytes_read,
        proof_bytes_read,
    })
}

fn read_clause<R: Read>(
    reader: &mut StreamDecoder<R>,
    clause_id: u64,
    variable_count: u32,
    limits: ProofCheckLimits,
    work: &mut WorkMeter,
) -> CheckResult<Vec<CheckLiteral>> {
    let count = reader.u64()?;
    enforce(
        ProofCheckResource::ClauseLiterals,
        limits.max_clause_literals,
        count,
    )?;
    enforce(
        ProofCheckResource::LiveLiterals,
        limits.max_live_literals,
        count,
    )?;
    let capacity = bounded_capacity::<CheckLiteral>(
        count,
        ProofCheckResource::ClauseLiterals,
        limits.max_clause_literals,
    )?;
    let mut clause = Vec::with_capacity(capacity);
    let mut previous: Option<CheckLiteral> = None;
    for _ in 0..count {
        work.spend(1)?;
        let variable_at = reader.position();
        let variable = read_variable(reader, variable_at, variable_count)?;
        let polarity_at = reader.position();
        let positive = match reader.u8()? {
            0 => false,
            1 => true,
            found => {
                return Err(Stop::Refused(ProofRefusal::UnknownPolarity {
                    stream: reader.stream,
                    at: polarity_at,
                    found,
                }));
            }
        };
        let literal = CheckLiteral { variable, positive };
        if let Some(previous_literal) = previous {
            if previous_literal.variable == literal.variable {
                if previous_literal.positive != literal.positive {
                    return Err(Stop::Refused(ProofRefusal::TautologicalClause {
                        stream: reader.stream,
                        clause: clause_id,
                        variable,
                    }));
                }
                return Err(Stop::Refused(ProofRefusal::NonCanonicalClause {
                    stream: reader.stream,
                    clause: clause_id,
                }));
            }
            if literal < previous_literal {
                return Err(Stop::Refused(ProofRefusal::NonCanonicalClause {
                    stream: reader.stream,
                    clause: clause_id,
                }));
            }
        }
        previous = Some(literal);
        clause.push(literal);
    }
    Ok(clause)
}

fn read_variable<R: Read>(
    reader: &mut StreamDecoder<R>,
    at: u64,
    variable_count: u32,
) -> CheckResult<u32> {
    let variable = reader.u32()?;
    if variable == 0 {
        return Err(Stop::Refused(ProofRefusal::InvalidVariableId {
            stream: reader.stream,
            at,
            raw: variable,
        }));
    }
    if variable > variable_count {
        return Err(Stop::Refused(ProofRefusal::VariableOutOfRange {
            stream: reader.stream,
            at,
            variable,
            declared: variable_count,
        }));
    }
    Ok(variable)
}

fn read_clause_id<R: Read>(reader: &mut StreamDecoder<R>, at: u64) -> CheckResult<u64> {
    let id = reader.u64()?;
    if id == 0 {
        Err(Stop::Refused(ProofRefusal::InvalidClauseId {
            stream: reader.stream,
            at,
            raw: id,
        }))
    } else {
        Ok(id)
    }
}

#[allow(clippy::too_many_arguments)]
fn check_resolution(
    state: &CheckState,
    step: u64,
    derived: &[CheckLiteral],
    pivot: u32,
    positive_parent: u64,
    negative_parent: u64,
    limits: ProofCheckLimits,
    work: &mut WorkMeter,
) -> CheckResult<()> {
    let positive = require_live(state, step, positive_parent)?;
    let negative = require_live(state, step, negative_parent)?;
    let positive_pivot = CheckLiteral {
        variable: pivot,
        positive: true,
    };
    let negative_pivot = CheckLiteral {
        variable: pivot,
        positive: false,
    };
    if positive.binary_search(&positive_pivot).is_err() {
        return Err(Stop::Refused(ProofRefusal::InvalidResolutionPivot {
            step,
            parent: positive_parent,
            pivot,
            expected_positive: true,
        }));
    }
    if negative.binary_search(&negative_pivot).is_err() {
        return Err(Stop::Refused(ProofRefusal::InvalidResolutionPivot {
            step,
            parent: negative_parent,
            pivot,
            expected_positive: false,
        }));
    }

    let mut expected = Vec::new();
    let mut positive_index = 0;
    let mut negative_index = 0;
    loop {
        while positive
            .get(positive_index)
            .is_some_and(|literal| literal.variable == pivot)
        {
            positive_index += 1;
        }
        while negative
            .get(negative_index)
            .is_some_and(|literal| literal.variable == pivot)
        {
            negative_index += 1;
        }
        let left = positive.get(positive_index).copied();
        let right = negative.get(negative_index).copied();
        let next = match (left, right) {
            (None, None) => break,
            (Some(literal), None) => {
                positive_index += 1;
                literal
            }
            (None, Some(literal)) => {
                negative_index += 1;
                literal
            }
            (Some(left), Some(right)) if left.variable < right.variable => {
                positive_index += 1;
                left
            }
            (Some(left), Some(right)) if right.variable < left.variable => {
                negative_index += 1;
                right
            }
            (Some(left), Some(right)) => {
                positive_index += 1;
                negative_index += 1;
                if left.positive != right.positive {
                    return Err(Stop::Refused(ProofRefusal::TautologicalResolvent {
                        step,
                        variable: left.variable,
                    }));
                }
                left
            }
        };
        work.spend(1)?;
        let actual = usize_to_u64(expected.len())?
            .checked_add(1)
            .ok_or_else(|| {
                exhausted(
                    ProofCheckResource::ClauseLiterals,
                    limits.max_clause_literals,
                )
            })?;
        enforce(
            ProofCheckResource::ClauseLiterals,
            limits.max_clause_literals,
            actual,
        )?;
        expected.push(next);
    }
    if expected == derived {
        Ok(())
    } else {
        Err(Stop::Refused(ProofRefusal::ResolutionMismatch { step }))
    }
}

fn check_rup<F>(
    state: &CheckState,
    step: u64,
    derived: &[CheckLiteral],
    antecedents: &[u64],
    work: &mut WorkMeter,
    cancelled: &mut F,
) -> CheckResult<()>
where
    F: FnMut() -> bool,
{
    let mut assignments = BTreeMap::<u32, bool>::new();
    for literal in derived {
        work.spend(1)?;
        assignments.insert(literal.variable, !literal.positive);
    }

    loop {
        observe_cancellation(cancelled)?;
        let mut progressed = false;
        for antecedent in antecedents {
            work.spend(1)?;
            let clause = require_live(state, step, *antecedent)?;
            let mut satisfied = false;
            let mut unassigned = None;
            let mut multiple_unassigned = false;
            for literal in clause {
                work.spend(1)?;
                match assignments.get(&literal.variable) {
                    Some(value) if *value == literal.positive => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None if unassigned.is_none() => unassigned = Some(*literal),
                    None => multiple_unassigned = true,
                }
            }
            if satisfied {
                continue;
            }
            if unassigned.is_none() {
                return Ok(());
            }
            if !multiple_unassigned {
                let Some(unit) = unassigned else {
                    return Err(Stop::InternalFault(ProofCheckInternalFault::StateInvariant));
                };
                assignments.insert(unit.variable, unit.positive);
                progressed = true;
            }
        }
        if !progressed {
            return Err(Stop::Refused(ProofRefusal::RupDidNotConflict { step }));
        }
    }
}

fn require_live(state: &CheckState, step: u64, dependency: u64) -> CheckResult<&[CheckLiteral]> {
    state
        .live
        .get(&dependency)
        .map(Vec::as_slice)
        .ok_or(Stop::Refused(ProofRefusal::MissingDependency {
            step,
            dependency,
        }))
}

fn observe_cancellation<F>(cancelled: &mut F) -> CheckResult<()>
where
    F: FnMut() -> bool,
{
    if cancelled() {
        Err(Stop::Inconclusive(ProofCheckInconclusive::Cancelled))
    } else {
        Ok(())
    }
}

fn checked_add_resource(
    current: u64,
    amount: u64,
    resource: ProofCheckResource,
    limit: u64,
) -> CheckResult<u64> {
    let actual = current
        .checked_add(amount)
        .ok_or_else(|| exhausted(resource, limit))?;
    enforce(resource, limit, actual)?;
    Ok(actual)
}

fn bounded_capacity<T>(count: u64, resource: ProofCheckResource, limit: u64) -> CheckResult<usize> {
    enforce(resource, limit, count)?;
    let capacity = usize::try_from(count)
        .map_err(|_| exhausted(ProofCheckResource::AddressSpace, usize::MAX as u64))?;
    let element_bytes = std::mem::size_of::<T>().max(1);
    let max_items = (isize::MAX as usize) / element_bytes;
    let addressable = u64::try_from(max_items).unwrap_or(u64::MAX);
    enforce(ProofCheckResource::AddressSpace, addressable, count)?;
    Ok(capacity)
}

fn usize_to_u64(value: usize) -> CheckResult<u64> {
    u64::try_from(value).map_err(|_| exhausted(ProofCheckResource::AddressSpace, usize::MAX as u64))
}

fn enforce(resource: ProofCheckResource, limit: u64, actual: u64) -> CheckResult<()> {
    if actual > limit {
        Err(exhausted_with_actual(resource, limit, actual))
    } else {
        Ok(())
    }
}

fn exhausted(resource: ProofCheckResource, limit: u64) -> Stop {
    exhausted_with_actual(resource, limit, u64::MAX)
}

fn exhausted_with_actual(resource: ProofCheckResource, limit: u64, actual: u64) -> Stop {
    Stop::Inconclusive(ProofCheckInconclusive::ResourceExhausted {
        resource,
        limit,
        actual,
    })
}
