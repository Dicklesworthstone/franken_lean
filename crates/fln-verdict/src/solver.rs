//! Deterministic, certificate-producing CDCL.
//!
//! The engine is intentionally untrusted.  An UNSAT result is constructed only
//! after the independently implemented streaming checker accepts the exact CNF
//! and proof byte streams.  SAT models are canonicalized, decoded again, and
//! checked against the original CNF before publication.

use crate::{
    Assignment, Clause, ClauseId, Cnf, InputClause, Literal, Polarity, ProofCheckInconclusive,
    ProofCheckInternalFault, ProofCheckLimits, ProofCheckOutcome, ProofCheckReceipt,
    ProofCheckResource, ProofRefusal, ProofRule, ProofStep, ResourceKind, SatModel, SchemaError,
    SchemaLimits, UnsatProof, VariableId, check_unsat_streams_with_cancel,
};
use std::collections::BTreeSet;

/// Registered choices for every semantically free CDCL order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CdclDeterminismPolicy {
    pub policy_id: &'static str,
    pub variable_order: &'static str,
    pub initial_phase: &'static str,
    pub conflict_analysis: &'static str,
    pub restart_schedule: &'static str,
    pub proof_order: &'static str,
}

pub const DETERMINISTIC_CDCL_POLICY: CdclDeterminismPolicy = CdclDeterminismPolicy {
    policy_id: "fln.verdict.cdcl.determinism/2",
    variable_order: "highest-integer-activity-then-smallest-variable",
    initial_phase: "negative-then-saved-phase",
    conflict_analysis: "first-uip-root-context-preserving-backjump",
    restart_schedule: "luby-base-conflicts",
    proof_order: "reverse-trail-resolution-relevant-rup-fallback",
};

/// A solver-owned resource.  These are operation facts, not SAT verdicts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverResource {
    Variables,
    Clauses,
    Literals,
    Decisions,
    Propagations,
    Conflicts,
    LearnedClauses,
    Restarts,
    ProofSteps,
    ProofDependencies,
    WorkUnits,
    ArtifactBytes,
    AddressSpace,
    ClauseIds,
}

/// FL-INV-07 non-verdicts.  None carries a model or proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverInconclusive {
    Cancelled,
    ResourceExhausted {
        resource: SolverResource,
        limit: u64,
        actual: u64,
    },
    AllocationRefused {
        resource: SolverResource,
        requested: u64,
    },
    ClauseIdSpaceExhausted {
        largest_input_id: u64,
    },
    ProofCheckResourceExhausted {
        resource: ProofCheckResource,
        limit: u64,
        actual: u64,
    },
}

/// A producer/checker invariant failure.  This is never rendered as UNSAT.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverInternalFault {
    StateInvariant,
    Schema(SchemaError),
    ModelValidation,
    ProofRefused(ProofRefusal),
    ProofChecker(ProofCheckInternalFault),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SolverStatistics {
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    pub learned_clauses: u64,
    pub restarts: u64,
    pub proof_steps: u64,
    pub proof_dependencies: u64,
    pub work_units: u64,
}

/// Explicit solver, proof, and checker budgets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SolverLimits {
    pub max_variables: u32,
    pub max_clauses: u64,
    pub max_literals: u64,
    pub max_decisions: u64,
    pub max_propagations: u64,
    pub max_conflicts: u64,
    pub max_learned_clauses: u64,
    pub max_restarts: u64,
    pub max_proof_steps: u64,
    pub max_proof_dependencies: u64,
    pub max_work_units: u64,
    pub max_artifact_bytes: u64,
    /// Zero disables restarts.  Otherwise the interval is
    /// `restart_base_conflicts * luby(restart_index)`.
    pub restart_base_conflicts: u64,
    pub schema: SchemaLimits,
    pub checker: ProofCheckLimits,
}

impl Default for SolverLimits {
    fn default() -> Self {
        Self {
            max_variables: 1_000_000,
            max_clauses: 8_000_000,
            max_literals: 64_000_000,
            max_decisions: 100_000_000,
            max_propagations: 1_000_000_000,
            max_conflicts: 100_000_000,
            max_learned_clauses: 8_000_000,
            max_restarts: 1_000_000,
            max_proof_steps: 16_000_000,
            max_proof_dependencies: 512_000_000,
            max_work_units: 4_000_000_000,
            max_artifact_bytes: 256 * 1024 * 1024,
            restart_base_conflicts: 64,
            schema: SchemaLimits::default(),
            checker: ProofCheckLimits::default(),
        }
    }
}

/// A SAT artifact re-decoded and validated against the exact input bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedSat {
    model: SatModel,
    cnf_bytes: Box<[u8]>,
    model_bytes: Box<[u8]>,
}

impl CheckedSat {
    pub const fn model(&self) -> &SatModel {
        &self.model
    }

    pub const fn cnf_bytes(&self) -> &[u8] {
        &self.cnf_bytes
    }

    pub const fn model_bytes(&self) -> &[u8] {
        &self.model_bytes
    }
}

/// An UNSAT artifact accepted by the independent streaming checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedUnsat {
    proof: UnsatProof,
    receipt: ProofCheckReceipt,
    cnf_bytes: Box<[u8]>,
    proof_bytes: Box<[u8]>,
}

impl CheckedUnsat {
    pub const fn proof(&self) -> &UnsatProof {
        &self.proof
    }

    pub const fn receipt(&self) -> &ProofCheckReceipt {
        &self.receipt
    }

    pub const fn cnf_bytes(&self) -> &[u8] {
        &self.cnf_bytes
    }

    pub const fn proof_bytes(&self) -> &[u8] {
        &self.proof_bytes
    }

    /// Move the exact independently checked streams into another trust-boundary
    /// consumer without re-encoding or copying them.
    pub(crate) fn into_canonical_streams(self) -> (Box<[u8]>, Box<[u8]>) {
        let Self {
            proof: _,
            receipt: _,
            cnf_bytes,
            proof_bytes,
        } = self;
        (cnf_bytes, proof_bytes)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverOutcome {
    Sat {
        artifact: CheckedSat,
        statistics: SolverStatistics,
    },
    Unsat {
        artifact: CheckedUnsat,
        statistics: SolverStatistics,
    },
    Inconclusive {
        cause: SolverInconclusive,
        statistics: SolverStatistics,
    },
    InternalFault {
        fault: SolverInternalFault,
        statistics: SolverStatistics,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckedSolverArtifact<'a> {
    Sat(&'a CheckedSat),
    Unsat(&'a CheckedUnsat),
}

impl SolverOutcome {
    pub const fn checked_artifact(&self) -> Option<CheckedSolverArtifact<'_>> {
        match self {
            Self::Sat { artifact, .. } => Some(CheckedSolverArtifact::Sat(artifact)),
            Self::Unsat { artifact, .. } => Some(CheckedSolverArtifact::Unsat(artifact)),
            Self::Inconclusive { .. } | Self::InternalFault { .. } => None,
        }
    }

    pub const fn statistics(&self) -> SolverStatistics {
        match self {
            Self::Sat { statistics, .. }
            | Self::Unsat { statistics, .. }
            | Self::Inconclusive { statistics, .. }
            | Self::InternalFault { statistics, .. } => *statistics,
        }
    }
}

/// Solve one already-canonical CNF through the deterministic authority lane.
pub fn solve(cnf: &Cnf, limits: SolverLimits) -> SolverOutcome {
    solve_with_cancel(cnf, limits, || false)
}

/// As [`solve`], observing cancellation at deterministic operation boundaries.
pub fn solve_with_cancel<F>(cnf: &Cnf, limits: SolverLimits, mut cancelled: F) -> SolverOutcome
where
    F: FnMut() -> bool,
{
    let mut engine = match Engine::new(cnf, limits) {
        Ok(engine) => engine,
        Err(stop) => return stop.into_outcome(SolverStatistics::default()),
    };
    engine.run(&mut cancelled)
}

/// Failure to materialize a canonical incremental/assumption input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IncrementalError {
    NoOpenScope,
    VariableOutOfRange { variable: VariableId, declared: u32 },
    Inconclusive(SolverInconclusive),
    Schema(SchemaError),
}

/// A solve result paired with the exact CNF checked by its artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedSolve {
    cnf: Cnf,
    outcome: SolverOutcome,
}

impl PreparedSolve {
    pub const fn cnf(&self) -> &Cnf {
        &self.cnf
    }

    pub const fn outcome(&self) -> &SolverOutcome {
        &self.outcome
    }

    pub fn into_parts(self) -> (Cnf, SolverOutcome) {
        (self.cnf, self.outcome)
    }
}

/// Deterministic scoped CNF construction.  Scope and assumption order cannot
/// leak into the materialized clause order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IncrementalSolver {
    base: Cnf,
    active: Vec<Clause>,
    scope_starts: Vec<usize>,
}

impl IncrementalSolver {
    pub const fn new(base: Cnf) -> Self {
        Self {
            base,
            active: Vec::new(),
            scope_starts: Vec::new(),
        }
    }

    pub const fn scope_depth(&self) -> usize {
        self.scope_starts.len()
    }

    pub fn push_scope(&mut self) -> Result<(), IncrementalError> {
        self.scope_starts.try_reserve(1).map_err(|_| {
            IncrementalError::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: 1,
            })
        })?;
        self.scope_starts.push(self.active.len());
        Ok(())
    }

    pub fn pop_scope(&mut self) -> Result<(), IncrementalError> {
        let start = self
            .scope_starts
            .pop()
            .ok_or(IncrementalError::NoOpenScope)?;
        self.active.truncate(start);
        Ok(())
    }

    pub fn add_clause(&mut self, clause: Clause) -> Result<(), IncrementalError> {
        if let Some(literal) = clause
            .literals()
            .iter()
            .find(|literal| literal.variable().get() > self.base.variable_count())
        {
            return Err(IncrementalError::VariableOutOfRange {
                variable: literal.variable(),
                declared: self.base.variable_count(),
            });
        }
        self.active.try_reserve(1).map_err(|_| {
            IncrementalError::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: 1,
            })
        })?;
        self.active.push(clause);
        Ok(())
    }

    /// Canonicalize active scoped clauses and assumptions into an ordinary CNF.
    pub fn materialize(
        &self,
        assumptions: &[Literal],
        limits: SchemaLimits,
    ) -> Result<Cnf, IncrementalError> {
        let mut extras = Vec::new();
        extras
            .try_reserve(self.active.len().saturating_add(assumptions.len()))
            .map_err(|_| {
                IncrementalError::Inconclusive(SolverInconclusive::AllocationRefused {
                    resource: SolverResource::AddressSpace,
                    requested: self.active.len().saturating_add(assumptions.len()) as u64,
                })
            })?;
        extras.extend(self.active.iter().cloned());
        for assumption in assumptions {
            if assumption.variable().get() > self.base.variable_count() {
                return Err(IncrementalError::VariableOutOfRange {
                    variable: assumption.variable(),
                    declared: self.base.variable_count(),
                });
            }
            extras.push(Clause::new(vec![*assumption]).map_err(IncrementalError::Schema)?);
        }
        extras.sort_unstable_by(|left, right| left.literals().cmp(right.literals()));
        extras.dedup();

        let mut rows = Vec::new();
        rows.try_reserve(self.base.clauses().len().saturating_add(extras.len()))
            .map_err(|_| {
                IncrementalError::Inconclusive(SolverInconclusive::AllocationRefused {
                    resource: SolverResource::AddressSpace,
                    requested: self.base.clauses().len().saturating_add(extras.len()) as u64,
                })
            })?;
        rows.extend(self.base.clauses().iter().cloned());
        let mut largest = self
            .base
            .clauses()
            .iter()
            .map(|row| row.id().get())
            .max()
            .unwrap_or(0);
        for clause in extras {
            largest = largest.checked_add(1).ok_or({
                IncrementalError::Inconclusive(SolverInconclusive::ClauseIdSpaceExhausted {
                    largest_input_id: u64::MAX,
                })
            })?;
            let id = ClauseId::new(largest).map_err(IncrementalError::Schema)?;
            rows.push(InputClause::new(id, clause));
        }
        Cnf::new(self.base.variable_count(), rows, limits).map_err(|error| match error {
            SchemaError::ResourceLimitExceeded {
                resource,
                limit,
                actual,
            } => IncrementalError::Inconclusive(SolverInconclusive::ResourceExhausted {
                resource: schema_resource(resource),
                limit,
                actual,
            }),
            other => IncrementalError::Schema(other),
        })
    }

    pub fn solve(
        &self,
        assumptions: &[Literal],
        limits: SolverLimits,
    ) -> Result<PreparedSolve, IncrementalError> {
        self.solve_with_cancel(assumptions, limits, || false)
    }

    pub fn solve_with_cancel<F>(
        &self,
        assumptions: &[Literal],
        limits: SolverLimits,
        cancelled: F,
    ) -> Result<PreparedSolve, IncrementalError>
    where
        F: FnMut() -> bool,
    {
        let cnf = self.materialize(assumptions, limits.schema)?;
        let outcome = solve_with_cancel(&cnf, limits, cancelled);
        Ok(PreparedSolve { cnf, outcome })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct SolverLiteral {
    variable: usize,
    positive: bool,
}

impl SolverLiteral {
    fn from_public(literal: Literal) -> Result<Self, Stop> {
        Ok(Self {
            variable: usize::try_from(literal.variable().get()).map_err(|_| {
                Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                    resource: SolverResource::AddressSpace,
                    requested: u64::from(literal.variable().get()),
                })
            })?,
            positive: literal.polarity() == Polarity::Positive,
        })
    }

    const fn negated(self) -> Self {
        Self {
            variable: self.variable,
            positive: !self.positive,
        }
    }

    fn to_public(self) -> Result<Literal, Stop> {
        let raw = u32::try_from(self.variable)
            .map_err(|_| Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        let variable = VariableId::new(raw)
            .map_err(|error| Stop::InternalFault(SolverInternalFault::Schema(error)))?;
        Ok(Literal::new(
            variable,
            if self.positive {
                Polarity::Positive
            } else {
                Polarity::Negative
            },
        ))
    }
}

#[derive(Debug)]
struct SolverClause {
    id: ClauseId,
    literals: Vec<SolverLiteral>,
    watches: [usize; 2],
}

#[derive(Debug)]
enum SearchResult {
    Sat,
    Unsat(usize),
}

#[derive(Debug, Clone, Copy)]
struct ResolutionLink {
    pivot: usize,
    reason: usize,
}

#[derive(Debug)]
struct ConflictAnalysis {
    learned: Vec<SolverLiteral>,
    backtrack_level: u32,
    resolution_links: Vec<ResolutionLink>,
}

#[derive(Debug)]
enum Stop {
    Inconclusive(SolverInconclusive),
    InternalFault(SolverInternalFault),
}

impl Stop {
    fn into_outcome(self, statistics: SolverStatistics) -> SolverOutcome {
        match self {
            Self::Inconclusive(cause) => SolverOutcome::Inconclusive { cause, statistics },
            Self::InternalFault(fault) => SolverOutcome::InternalFault { fault, statistics },
        }
    }
}

type EngineResult<T> = Result<T, Stop>;

struct Engine<'a> {
    cnf: &'a Cnf,
    limits: SolverLimits,
    clauses: Vec<SolverClause>,
    watch_lists: Vec<Vec<usize>>,
    assignments: Vec<Option<bool>>,
    levels: Vec<u32>,
    reasons: Vec<Option<usize>>,
    saved_phase: Vec<bool>,
    activity: Vec<u64>,
    seen: Vec<bool>,
    trail: Vec<SolverLiteral>,
    trail_limits: Vec<usize>,
    propagation_head: usize,
    proof_steps: Vec<ProofStep>,
    active_ids: BTreeSet<ClauseId>,
    next_clause_id: Option<u64>,
    initial_conflict: Option<usize>,
    total_literals: u64,
    conflicts_since_restart: u64,
    restart_index: u64,
    statistics: SolverStatistics,
}

impl<'a> Engine<'a> {
    fn new(cnf: &'a Cnf, limits: SolverLimits) -> EngineResult<Self> {
        enforce_initial(
            SolverResource::Variables,
            u64::from(limits.max_variables),
            u64::from(cnf.variable_count()),
        )?;
        enforce_initial(
            SolverResource::Clauses,
            limits.max_clauses,
            cnf.facts().clauses,
        )?;
        enforce_initial(
            SolverResource::Literals,
            limits.max_literals,
            cnf.facts().literals,
        )?;
        let initial_work = cnf
            .facts()
            .clauses
            .checked_add(cnf.facts().literals)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(
            SolverResource::WorkUnits,
            limits.max_work_units,
            initial_work,
        )?;

        let variable_count = usize::try_from(cnf.variable_count()).map_err(|_| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: u64::from(cnf.variable_count()),
            })
        })?;
        let variable_slots = variable_count.checked_add(1).ok_or_else(|| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: u64::from(cnf.variable_count()),
            })
        })?;
        let watch_slots = variable_slots.checked_mul(2).ok_or_else(|| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: u64::from(cnf.variable_count()).saturating_mul(2),
            })
        })?;

        let mut engine = Self {
            cnf,
            limits,
            clauses: fallible_vec(cnf.clauses().len(), SolverResource::Clauses)?,
            watch_lists: fallible_nested_vec(watch_slots)?,
            assignments: fallible_filled_vec(variable_slots, None)?,
            levels: fallible_filled_vec(variable_slots, 0_u32)?,
            reasons: fallible_filled_vec(variable_slots, None)?,
            saved_phase: fallible_filled_vec(variable_slots, false)?,
            activity: fallible_filled_vec(variable_slots, 0_u64)?,
            seen: fallible_filled_vec(variable_slots, false)?,
            trail: fallible_vec(variable_slots, SolverResource::Variables)?,
            trail_limits: Vec::new(),
            propagation_head: 0,
            proof_steps: Vec::new(),
            active_ids: BTreeSet::new(),
            next_clause_id: cnf
                .clauses()
                .iter()
                .map(|row| row.id().get())
                .max()
                .unwrap_or(0)
                .checked_add(1),
            initial_conflict: None,
            total_literals: cnf.facts().literals,
            conflicts_since_restart: 0,
            restart_index: 1,
            statistics: SolverStatistics {
                work_units: initial_work,
                ..SolverStatistics::default()
            },
        };

        for row in cnf.clauses() {
            let mut literals = Vec::new();
            literals
                .try_reserve(row.clause().literals().len())
                .map_err(|_| {
                    Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                        resource: SolverResource::AddressSpace,
                        requested: row.clause().literals().len() as u64,
                    })
                })?;
            for literal in row.clause().literals() {
                literals.push(SolverLiteral::from_public(*literal)?);
            }
            let index = engine.install_clause(row.id(), literals)?;
            engine.active_ids.insert(row.id());
            if engine.clauses[index].literals.is_empty() && engine.initial_conflict.is_none() {
                engine.initial_conflict = Some(index);
            }
        }

        for index in 0..engine.clauses.len() {
            if engine.clauses[index].literals.len() == 1 {
                let literal = engine.clauses[index].literals[0];
                if !engine.enqueue(literal, Some(index), true)? && engine.initial_conflict.is_none()
                {
                    engine.initial_conflict = Some(index);
                }
            }
        }
        Ok(engine)
    }

    fn run<F>(&mut self, cancelled: &mut F) -> SolverOutcome
    where
        F: FnMut() -> bool,
    {
        let search = self.search(cancelled);
        match search {
            Ok(SearchResult::Sat) => match self.finish_sat() {
                Ok(outcome) => outcome,
                Err(stop) => stop.into_outcome(self.statistics),
            },
            Ok(SearchResult::Unsat(conflict)) => match self.finish_unsat(conflict, cancelled) {
                Ok(outcome) => outcome,
                Err(stop) => stop.into_outcome(self.statistics),
            },
            Err(stop) => stop.into_outcome(self.statistics),
        }
    }

    fn search<F>(&mut self, cancelled: &mut F) -> EngineResult<SearchResult>
    where
        F: FnMut() -> bool,
    {
        self.observe_cancel(cancelled)?;
        if let Some(conflict) = self.initial_conflict {
            return Ok(SearchResult::Unsat(conflict));
        }

        loop {
            self.observe_cancel(cancelled)?;
            if let Some(conflict) = self.propagate(cancelled)? {
                self.charge_conflict()?;
                if self.decision_level() == 0 {
                    return Ok(SearchResult::Unsat(conflict));
                }
                let analysis = self.analyze(conflict)?;
                self.backtrack(analysis.backtrack_level)?;
                let asserting = analysis
                    .learned
                    .first()
                    .copied()
                    .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
                let learned_index = self.log_learned_clause(
                    conflict,
                    analysis.learned,
                    &analysis.resolution_links,
                    cancelled,
                )?;
                if !self.enqueue(asserting, Some(learned_index), true)? {
                    return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
                }
                self.conflicts_since_restart = self
                    .conflicts_since_restart
                    .checked_add(1)
                    .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
                self.maybe_restart()?;
                continue;
            }

            let Some(variable) = self.select_variable()? else {
                return Ok(SearchResult::Sat);
            };
            self.charge_counter(
                self.statistics.decisions,
                self.limits.max_decisions,
                SolverResource::Decisions,
            )?;
            self.statistics.decisions += 1;
            self.trail_limits.try_reserve(1).map_err(|_| {
                Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                    resource: SolverResource::AddressSpace,
                    requested: self.trail_limits.len().saturating_add(1) as u64,
                })
            })?;
            self.trail_limits.push(self.trail.len());
            let decision = SolverLiteral {
                variable,
                positive: self.saved_phase[variable],
            };
            if !self.enqueue(decision, None, false)? {
                return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
            }
        }
    }

    fn install_clause(
        &mut self,
        id: ClauseId,
        literals: Vec<SolverLiteral>,
    ) -> EngineResult<usize> {
        self.clauses.try_reserve(1).map_err(|_| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: self.clauses.len().saturating_add(1) as u64,
            })
        })?;
        let index = self.clauses.len();
        let watches = if literals.len() >= 2 { [0, 1] } else { [0, 0] };
        if let Some(first) = literals.first().copied() {
            self.reserve_watch(first)?;
            if literals.len() >= 2 {
                self.reserve_watch(literals[1])?;
            }
        }
        self.clauses.push(SolverClause {
            id,
            literals,
            watches,
        });
        if let Some(first) = self.clauses[index].literals.first().copied() {
            let first_watch = literal_index(first)?;
            self.watch_lists[first_watch].push(index);
            if self.clauses[index].literals.len() >= 2 {
                let second = self.clauses[index].literals[1];
                let second_watch = literal_index(second)?;
                self.watch_lists[second_watch].push(index);
            }
        }
        Ok(index)
    }

    fn reserve_watch(&mut self, literal: SolverLiteral) -> EngineResult<()> {
        let index = literal_index(literal)?;
        self.watch_lists[index].try_reserve(1).map_err(|_| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: self.watch_lists[index].len().saturating_add(1) as u64,
            })
        })
    }

    fn propagate<F>(&mut self, cancelled: &mut F) -> EngineResult<Option<usize>>
    where
        F: FnMut() -> bool,
    {
        while self.propagation_head < self.trail.len() {
            self.observe_cancel(cancelled)?;
            let false_literal = self.trail[self.propagation_head].negated();
            self.propagation_head += 1;
            let false_index = literal_index(false_literal)?;
            let pending = std::mem::take(&mut self.watch_lists[false_index]);
            let mut retained = Vec::new();
            retained.try_reserve(pending.len()).map_err(|_| {
                Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                    resource: SolverResource::AddressSpace,
                    requested: pending.len() as u64,
                })
            })?;
            let mut iterator = pending.into_iter();
            while let Some(clause_index) = iterator.next() {
                self.spend_work(1)?;
                let (false_slot, other_slot, other_literal) = {
                    let clause = self
                        .clauses
                        .get(clause_index)
                        .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
                    let first = clause.watches[0];
                    let second = clause.watches[1];
                    if clause.literals.get(first).copied() == Some(false_literal) {
                        (0, second, clause.literals[second])
                    } else if clause.literals.get(second).copied() == Some(false_literal) {
                        (1, first, clause.literals[first])
                    } else {
                        return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
                    }
                };

                if self.literal_value(other_literal) == Some(true) {
                    retained.push(clause_index);
                    continue;
                }

                let mut replacement = None;
                let clause_len = self.clauses[clause_index].literals.len();
                for literal_index_in_clause in 0..clause_len {
                    self.spend_work(1)?;
                    let literal = self.clauses[clause_index].literals[literal_index_in_clause];
                    if literal_index_in_clause != other_slot
                        && self.literal_value(literal) != Some(false)
                    {
                        replacement = Some((literal_index_in_clause, literal));
                        break;
                    }
                }

                if let Some((replacement_index, replacement_literal)) = replacement {
                    self.reserve_watch(replacement_literal)?;
                    self.clauses[clause_index].watches[false_slot] = replacement_index;
                    let watch = literal_index(replacement_literal)?;
                    self.watch_lists[watch].push(clause_index);
                    continue;
                }

                retained.push(clause_index);
                if self.literal_value(other_literal) == Some(false) {
                    retained.extend(iterator);
                    self.watch_lists[false_index] = retained;
                    return Ok(Some(clause_index));
                }
                if !self.enqueue(other_literal, Some(clause_index), true)? {
                    retained.extend(iterator);
                    self.watch_lists[false_index] = retained;
                    return Ok(Some(clause_index));
                }
            }
            self.watch_lists[false_index] = retained;
        }
        Ok(None)
    }

    /// Return true for a consistent assignment, false for an immediate conflict.
    fn enqueue(
        &mut self,
        literal: SolverLiteral,
        reason: Option<usize>,
        implied: bool,
    ) -> EngineResult<bool> {
        if let Some(value) = self.assignments[literal.variable] {
            return Ok(value == literal.positive);
        }
        if implied {
            self.charge_counter(
                self.statistics.propagations,
                self.limits.max_propagations,
                SolverResource::Propagations,
            )?;
            self.statistics.propagations += 1;
        }
        self.trail.try_reserve(1).map_err(|_| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: self.trail.len().saturating_add(1) as u64,
            })
        })?;
        self.assignments[literal.variable] = Some(literal.positive);
        self.levels[literal.variable] = self.decision_level();
        self.reasons[literal.variable] = reason;
        self.saved_phase[literal.variable] = literal.positive;
        self.trail.push(literal);
        Ok(true)
    }

    fn analyze(&mut self, conflict: usize) -> EngineResult<ConflictAnalysis> {
        let current_level = self.decision_level();
        if current_level == 0 {
            return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
        }
        let mut learned = Vec::new();
        learned.try_reserve(4).map_err(|_| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: 4,
            })
        })?;
        learned.push(SolverLiteral {
            variable: 0,
            positive: false,
        });
        let mut unresolved = 0_usize;
        let mut trail_index = self.trail.len();
        let mut clause_index = conflict;
        let mut skip_variable = None;
        let mut resolution_links = Vec::new();

        loop {
            let literal_count = self
                .clauses
                .get(clause_index)
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?
                .literals
                .len();
            for literal_index in 0..literal_count {
                self.spend_work(1)?;
                let literal = self
                    .clauses
                    .get(clause_index)
                    .and_then(|clause| clause.literals.get(literal_index))
                    .copied()
                    .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
                if skip_variable == Some(literal.variable) || self.seen[literal.variable] {
                    continue;
                }
                self.seen[literal.variable] = true;
                if self.levels[literal.variable] == 0 {
                    learned.try_reserve(1).map_err(|_| {
                        Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                            resource: SolverResource::AddressSpace,
                            requested: learned.len().saturating_add(1) as u64,
                        })
                    })?;
                    learned.push(literal);
                    continue;
                }
                self.bump_activity(literal.variable);
                if self.levels[literal.variable] == current_level {
                    unresolved = unresolved
                        .checked_add(1)
                        .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
                } else {
                    learned.try_reserve(1).map_err(|_| {
                        Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                            resource: SolverResource::AddressSpace,
                            requested: learned.len().saturating_add(1) as u64,
                        })
                    })?;
                    learned.push(literal);
                }
            }

            let pivot = loop {
                trail_index = trail_index
                    .checked_sub(1)
                    .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
                let candidate = self.trail[trail_index];
                if self.seen[candidate.variable] {
                    break candidate;
                }
            };
            self.seen[pivot.variable] = false;
            unresolved = unresolved
                .checked_sub(1)
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            if unresolved == 0 {
                learned[0] = pivot.negated();
                break;
            }
            let reason = self.reasons[pivot.variable]
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            resolution_links.try_reserve(1).map_err(|_| {
                Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                    resource: SolverResource::ProofDependencies,
                    requested: resolution_links.len().saturating_add(1) as u64,
                })
            })?;
            resolution_links.push(ResolutionLink {
                pivot: pivot.variable,
                reason,
            });
            clause_index = reason;
            skip_variable = Some(pivot.variable);
        }

        for literal in learned.iter().skip(1) {
            self.seen[literal.variable] = false;
        }
        if learned.len() > 2 {
            let best = (1..learned.len())
                .max_by_key(|index| {
                    (
                        self.levels[learned[*index].variable],
                        usize::MAX - learned[*index].variable,
                    )
                })
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            learned.swap(1, best);
        }
        let backtrack = learned
            .iter()
            .skip(1)
            .map(|literal| self.levels[literal.variable])
            .max()
            .unwrap_or(0);
        Ok(ConflictAnalysis {
            learned,
            backtrack_level: backtrack,
            resolution_links,
        })
    }

    fn log_learned_clause<F>(
        &mut self,
        conflict: usize,
        learned: Vec<SolverLiteral>,
        resolution_links: &[ResolutionLink],
        cancelled: &mut F,
    ) -> EngineResult<usize>
    where
        F: FnMut() -> bool,
    {
        self.charge_counter(
            self.statistics.learned_clauses,
            self.limits.max_learned_clauses,
            SolverResource::LearnedClauses,
        )?;
        self.charge_counter(
            self.clauses.len() as u64,
            self.limits.max_clauses,
            SolverResource::Clauses,
        )?;
        let learned_literals = learned.len() as u64;
        let total = self
            .total_literals
            .checked_add(learned_literals)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(SolverResource::Literals, self.limits.max_literals, total)?;
        let id = if let Some(id) =
            self.record_learned_resolution_chain(conflict, &learned, resolution_links, cancelled)?
        {
            id
        } else {
            let id = self.allocate_clause_id()?;
            let public = self.public_clause(&learned)?;
            let antecedents = self.relevant_rup_antecedents(&learned, cancelled)?;
            self.record_rup(id, public, antecedents)?;
            id
        };
        let index = self.install_clause(id, learned)?;
        self.active_ids.insert(id);
        self.total_literals = total;
        self.statistics.learned_clauses += 1;
        Ok(index)
    }

    fn record_learned_resolution_chain<F>(
        &mut self,
        conflict: usize,
        learned: &[SolverLiteral],
        links: &[ResolutionLink],
        cancelled: &mut F,
    ) -> EngineResult<Option<ClauseId>>
    where
        F: FnMut() -> bool,
    {
        let conflict_clause = self
            .clauses
            .get(conflict)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        let mut current = canonical_solver_literals(&conflict_clause.literals)?;
        let mut current_id = conflict_clause.id;
        let target = canonical_solver_literals(learned)?;
        let mut derived_any = false;
        for link in links {
            self.observe_cancel(cancelled)?;
            let reason = self
                .clauses
                .get(link.reason)
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            let (resolvent, positive_parent, negative_parent) =
                resolve_solver_literals(&current, current_id, reason, link.pivot)?;
            let id = self.allocate_clause_id()?;
            let public = self.public_clause(&resolvent)?;
            let pivot = u32::try_from(link.pivot)
                .ok()
                .and_then(|raw| VariableId::new(raw).ok())
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            self.record_resolution(id, public, pivot, positive_parent, negative_parent)?;
            current = resolvent;
            current_id = id;
            derived_any = true;
        }

        if current == target {
            Ok(derived_any.then_some(current_id))
        } else {
            Err(Stop::InternalFault(SolverInternalFault::StateInvariant))
        }
    }

    fn relevant_rup_antecedents<F>(
        &self,
        derived: &[SolverLiteral],
        cancelled: &mut F,
    ) -> EngineResult<Vec<ClauseId>>
    where
        F: FnMut() -> bool,
    {
        let mut previous_id = None;
        let mut active_clause_count = 0_usize;
        for clause in &self.clauses {
            if !self.active_ids.contains(&clause.id) {
                continue;
            }
            if previous_id.is_some_and(|previous| previous >= clause.id) {
                return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
            }
            previous_id = Some(clause.id);
            active_clause_count = active_clause_count
                .checked_add(1)
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        }
        if active_clause_count != self.active_ids.len() {
            return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
        }

        let mut assignments = fallible_filled_vec(self.assignments.len(), None)?;
        for literal in derived {
            let Some(slot) = assignments.get_mut(literal.variable) else {
                return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
            };
            if slot.replace(!literal.positive).is_some() {
                return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
            }
        }
        let mut antecedents =
            fallible_vec(self.assignments.len(), SolverResource::ProofDependencies)?;

        loop {
            self.observe_cancel(cancelled)?;
            let mut progressed = false;
            for clause in &self.clauses {
                if !self.active_ids.contains(&clause.id) {
                    continue;
                }
                let mut satisfied = false;
                let mut unit = None;
                let mut multiple_unassigned = false;
                for literal in &clause.literals {
                    match assignments.get(literal.variable).copied().flatten() {
                        Some(value) if value == literal.positive => {
                            satisfied = true;
                            break;
                        }
                        Some(_) => {}
                        None if unit.is_none() => unit = Some(*literal),
                        None => multiple_unassigned = true,
                    }
                }
                if satisfied {
                    continue;
                }
                if unit.is_none() {
                    antecedents.push(clause.id);
                    antecedents.sort_unstable();
                    return Ok(antecedents);
                }
                if multiple_unassigned {
                    continue;
                }
                let Some(unit) = unit else {
                    return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
                };
                let Some(slot) = assignments.get_mut(unit.variable) else {
                    return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
                };
                if slot.replace(unit.positive).is_some() {
                    return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
                }
                antecedents.push(clause.id);
                progressed = true;
            }
            if !progressed {
                return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
            }
        }
    }

    fn record_rup(
        &mut self,
        id: ClauseId,
        clause: Clause,
        antecedents: Vec<ClauseId>,
    ) -> EngineResult<()> {
        if antecedents.is_empty() {
            return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
        }
        let dependencies = antecedents.len() as u64;
        let dependency_total = self
            .statistics
            .proof_dependencies
            .checked_add(dependencies)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(
            SolverResource::ProofDependencies,
            self.limits.max_proof_dependencies,
            dependency_total,
        )?;
        let step_total = self
            .statistics
            .proof_steps
            .checked_add(1)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(
            SolverResource::ProofSteps,
            self.limits.max_proof_steps,
            step_total,
        )?;
        self.proof_steps.try_reserve(1).map_err(|_| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: step_total,
            })
        })?;
        self.proof_steps.push(ProofStep::Derive {
            id,
            clause,
            rule: ProofRule::rup(antecedents),
        });
        self.statistics.proof_steps = step_total;
        self.statistics.proof_dependencies = dependency_total;
        Ok(())
    }

    fn record_resolution(
        &mut self,
        id: ClauseId,
        clause: Clause,
        pivot: VariableId,
        positive_parent: ClauseId,
        negative_parent: ClauseId,
    ) -> EngineResult<()> {
        if positive_parent == negative_parent {
            return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
        }
        let dependency_total = self
            .statistics
            .proof_dependencies
            .checked_add(2)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(
            SolverResource::ProofDependencies,
            self.limits.max_proof_dependencies,
            dependency_total,
        )?;
        let step_total = self
            .statistics
            .proof_steps
            .checked_add(1)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(
            SolverResource::ProofSteps,
            self.limits.max_proof_steps,
            step_total,
        )?;
        self.proof_steps.try_reserve(1).map_err(|_| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: step_total,
            })
        })?;
        self.proof_steps.push(ProofStep::Derive {
            id,
            clause,
            rule: ProofRule::Resolution {
                pivot,
                positive_parent,
                negative_parent,
            },
        });
        self.statistics.proof_steps = step_total;
        self.statistics.proof_dependencies = dependency_total;
        Ok(())
    }

    fn record_empty_resolution_chain<F>(
        &mut self,
        conflict: usize,
        cancelled: &mut F,
    ) -> EngineResult<ClauseId>
    where
        F: FnMut() -> bool,
    {
        let conflict_clause = self
            .clauses
            .get(conflict)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        let mut current = canonical_solver_literals(&conflict_clause.literals)?;
        let mut current_id = conflict_clause.id;
        let mut steps = 0_usize;
        while !current.is_empty() {
            self.observe_cancel(cancelled)?;
            steps = steps
                .checked_add(1)
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            if steps > self.assignments.len() {
                return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
            }
            if current
                .iter()
                .any(|literal| self.literal_value(*literal) != Some(false))
            {
                return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
            }
            let pivot = self
                .trail
                .iter()
                .rev()
                .find(|assigned| {
                    current
                        .iter()
                        .any(|literal| literal.variable == assigned.variable)
                })
                .copied()
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            let reason_index = self.reasons[pivot.variable]
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            let reason = self
                .clauses
                .get(reason_index)
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            let (resolvent, positive_parent, negative_parent) =
                resolve_solver_literals(&current, current_id, reason, pivot.variable)?;
            let id = self.allocate_clause_id()?;
            let public = self.public_clause(&resolvent)?;
            let pivot = u32::try_from(pivot.variable)
                .ok()
                .and_then(|raw| VariableId::new(raw).ok())
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            self.record_resolution(id, public, pivot, positive_parent, negative_parent)?;
            current = resolvent;
            current_id = id;
        }
        Ok(current_id)
    }

    fn finish_unsat<F>(&mut self, conflict: usize, cancelled: &mut F) -> EngineResult<SolverOutcome>
    where
        F: FnMut() -> bool,
    {
        self.observe_cancel(cancelled)?;
        let empty_id = self.record_empty_resolution_chain(conflict, cancelled)?;

        let final_steps = self
            .statistics
            .proof_steps
            .checked_add(1)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(
            SolverResource::ProofSteps,
            self.limits.max_proof_steps,
            final_steps,
        )?;
        self.proof_steps.try_reserve(1).map_err(|_| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: final_steps,
            })
        })?;
        self.proof_steps.push(ProofStep::Conclude {
            empty_clause: empty_id,
        });
        self.statistics.proof_steps = final_steps;
        self.statistics.proof_dependencies = self
            .statistics
            .proof_dependencies
            .checked_add(1)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(
            SolverResource::ProofDependencies,
            self.limits.max_proof_dependencies,
            self.statistics.proof_dependencies,
        )?;

        let proof = UnsatProof::new(
            self.cnf,
            std::mem::take(&mut self.proof_steps),
            self.limits.schema,
        )
        .map_err(schema_stop)?;
        let cnf_bytes = self.cnf.to_canonical_bytes();
        let proof_bytes = proof.to_canonical_bytes();
        self.enforce_artifact_bytes(&cnf_bytes)?;
        self.enforce_artifact_bytes(&proof_bytes)?;
        let outcome = check_unsat_streams_with_cancel(
            &cnf_bytes[..],
            &proof_bytes[..],
            self.limits.checker,
            cancelled,
        );
        let receipt = match outcome {
            ProofCheckOutcome::Verified(receipt) => receipt,
            ProofCheckOutcome::Refused(reason) => {
                return Err(Stop::InternalFault(SolverInternalFault::ProofRefused(
                    reason,
                )));
            }
            ProofCheckOutcome::Inconclusive(ProofCheckInconclusive::Cancelled) => {
                return Err(Stop::Inconclusive(SolverInconclusive::Cancelled));
            }
            ProofCheckOutcome::Inconclusive(ProofCheckInconclusive::ResourceExhausted {
                resource,
                limit,
                actual,
            }) => {
                return Err(Stop::Inconclusive(
                    SolverInconclusive::ProofCheckResourceExhausted {
                        resource,
                        limit,
                        actual,
                    },
                ));
            }
            ProofCheckOutcome::InternalFault(fault) => {
                return Err(Stop::InternalFault(SolverInternalFault::ProofChecker(
                    fault,
                )));
            }
        };
        Ok(SolverOutcome::Unsat {
            artifact: CheckedUnsat {
                proof,
                receipt,
                cnf_bytes: cnf_bytes.into_boxed_slice(),
                proof_bytes: proof_bytes.into_boxed_slice(),
            },
            statistics: self.statistics,
        })
    }

    fn finish_sat(&mut self) -> EngineResult<SolverOutcome> {
        let mut assignments = Vec::new();
        assignments
            .try_reserve(self.cnf.variable_count() as usize)
            .map_err(|_| {
                Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                    resource: SolverResource::AddressSpace,
                    requested: u64::from(self.cnf.variable_count()),
                })
            })?;
        for raw in 1..=self.cnf.variable_count() {
            let index = raw as usize;
            let value = self.assignments[index]
                .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
            let variable = VariableId::new(raw)
                .map_err(|error| Stop::InternalFault(SolverInternalFault::Schema(error)))?;
            assignments.push(Assignment::new(variable, value));
        }
        let model = SatModel::new(self.cnf.variable_count(), assignments, self.limits.schema)
            .map_err(schema_stop)?;
        if !model
            .satisfies(self.cnf)
            .map_err(|error| Stop::InternalFault(SolverInternalFault::Schema(error)))?
        {
            return Err(Stop::InternalFault(SolverInternalFault::ModelValidation));
        }
        let cnf_bytes = self.cnf.to_canonical_bytes();
        let model_bytes = model.to_canonical_bytes();
        self.enforce_artifact_bytes(&cnf_bytes)?;
        self.enforce_artifact_bytes(&model_bytes)?;
        let decoded = SatModel::from_canonical_bytes(&model_bytes, self.limits.schema)
            .map_err(schema_stop)?;
        if decoded != model
            || !decoded
                .satisfies(self.cnf)
                .map_err(|error| Stop::InternalFault(SolverInternalFault::Schema(error)))?
        {
            return Err(Stop::InternalFault(SolverInternalFault::ModelValidation));
        }
        Ok(SolverOutcome::Sat {
            artifact: CheckedSat {
                model,
                cnf_bytes: cnf_bytes.into_boxed_slice(),
                model_bytes: model_bytes.into_boxed_slice(),
            },
            statistics: self.statistics,
        })
    }

    fn public_clause(&self, literals: &[SolverLiteral]) -> EngineResult<Clause> {
        let mut public = Vec::new();
        public.try_reserve(literals.len()).map_err(|_| {
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: literals.len() as u64,
            })
        })?;
        for literal in literals {
            public.push(literal.to_public()?);
        }
        Clause::new(public).map_err(|error| Stop::InternalFault(SolverInternalFault::Schema(error)))
    }

    fn select_variable(&mut self) -> EngineResult<Option<usize>> {
        let mut selected = None;
        for variable in 1..self.assignments.len() {
            self.spend_work(1)?;
            if self.assignments[variable].is_some() {
                continue;
            }
            selected = match selected {
                None => Some(variable),
                Some(previous)
                    if self.activity[variable] > self.activity[previous]
                        || (self.activity[variable] == self.activity[previous]
                            && variable < previous) =>
                {
                    Some(variable)
                }
                Some(previous) => Some(previous),
            };
        }
        Ok(selected)
    }

    fn backtrack(&mut self, target_level: u32) -> EngineResult<()> {
        let target = usize::try_from(target_level)
            .map_err(|_| Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        if target >= self.trail_limits.len() {
            if target == self.trail_limits.len() {
                return Ok(());
            }
            return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
        }
        let new_trail_len = self.trail_limits[target];
        for literal in self.trail.drain(new_trail_len..) {
            self.assignments[literal.variable] = None;
            self.levels[literal.variable] = 0;
            self.reasons[literal.variable] = None;
        }
        self.trail_limits.truncate(target);
        self.propagation_head = self.propagation_head.min(self.trail.len());
        Ok(())
    }

    fn maybe_restart(&mut self) -> EngineResult<()> {
        if self.limits.restart_base_conflicts == 0 || self.decision_level() == 0 {
            return Ok(());
        }
        let interval = self
            .limits
            .restart_base_conflicts
            .checked_mul(luby(self.restart_index))
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        if self.conflicts_since_restart < interval
            || self.statistics.restarts >= self.limits.max_restarts
        {
            return Ok(());
        }
        self.charge_counter(
            self.statistics.restarts,
            self.limits.max_restarts,
            SolverResource::Restarts,
        )?;
        self.statistics.restarts += 1;
        self.restart_index = self
            .restart_index
            .checked_add(1)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        self.conflicts_since_restart = 0;
        self.backtrack(0)
    }

    fn bump_activity(&mut self, variable: usize) {
        if self.activity[variable] == u64::MAX {
            for activity in self.activity.iter_mut().skip(1) {
                *activity >>= 1;
            }
        }
        self.activity[variable] = self.activity[variable].saturating_add(1);
    }

    fn allocate_clause_id(&mut self) -> EngineResult<ClauseId> {
        let raw = self.next_clause_id.ok_or({
            Stop::Inconclusive(SolverInconclusive::ClauseIdSpaceExhausted {
                largest_input_id: u64::MAX,
            })
        })?;
        self.next_clause_id = raw.checked_add(1);
        ClauseId::new(raw).map_err(|error| Stop::InternalFault(SolverInternalFault::Schema(error)))
    }

    fn literal_value(&self, literal: SolverLiteral) -> Option<bool> {
        self.assignments[literal.variable].map(|value| value == literal.positive)
    }

    fn decision_level(&self) -> u32 {
        u32::try_from(self.trail_limits.len()).unwrap_or(u32::MAX)
    }

    fn observe_cancel<F>(&self, cancelled: &mut F) -> EngineResult<()>
    where
        F: FnMut() -> bool,
    {
        if cancelled() {
            Err(Stop::Inconclusive(SolverInconclusive::Cancelled))
        } else {
            Ok(())
        }
    }

    fn spend_work(&mut self, amount: u64) -> EngineResult<()> {
        let actual = self
            .statistics
            .work_units
            .checked_add(amount)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(
            SolverResource::WorkUnits,
            self.limits.max_work_units,
            actual,
        )?;
        self.statistics.work_units = actual;
        Ok(())
    }

    fn charge_conflict(&mut self) -> EngineResult<()> {
        self.charge_counter(
            self.statistics.conflicts,
            self.limits.max_conflicts,
            SolverResource::Conflicts,
        )?;
        self.statistics.conflicts += 1;
        Ok(())
    }

    fn charge_counter(
        &self,
        current: u64,
        limit: u64,
        resource: SolverResource,
    ) -> EngineResult<()> {
        let actual = current
            .checked_add(1)
            .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(resource, limit, actual)
    }

    fn enforce_artifact_bytes(&self, bytes: &[u8]) -> EngineResult<()> {
        let actual = u64::try_from(bytes.len())
            .map_err(|_| Stop::InternalFault(SolverInternalFault::StateInvariant))?;
        enforce_initial(
            SolverResource::ArtifactBytes,
            self.limits.max_artifact_bytes,
            actual,
        )
    }
}

fn clone_solver_literals(literals: &[SolverLiteral]) -> EngineResult<Vec<SolverLiteral>> {
    let mut cloned = fallible_vec(literals.len(), SolverResource::AddressSpace)?;
    cloned.extend_from_slice(literals);
    Ok(cloned)
}

fn canonical_solver_literals(literals: &[SolverLiteral]) -> EngineResult<Vec<SolverLiteral>> {
    canonicalize_solver_literals(clone_solver_literals(literals)?)
}

fn canonicalize_solver_literals(
    mut literals: Vec<SolverLiteral>,
) -> EngineResult<Vec<SolverLiteral>> {
    literals.sort_unstable();
    literals.dedup();
    if literals.iter().any(|literal| literal.variable == 0)
        || literals
            .windows(2)
            .any(|pair| pair[0].variable == pair[1].variable)
    {
        return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
    }
    Ok(literals)
}

fn resolve_solver_literals(
    current: &[SolverLiteral],
    current_id: ClauseId,
    reason: &SolverClause,
    pivot: usize,
) -> EngineResult<(Vec<SolverLiteral>, ClauseId, ClauseId)> {
    let mut current_polarity = None;
    for literal in current {
        if literal.variable == pivot && current_polarity.replace(literal.positive).is_some() {
            return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
        }
    }
    let mut reason_polarity = None;
    for literal in &reason.literals {
        if literal.variable == pivot && reason_polarity.replace(literal.positive).is_some() {
            return Err(Stop::InternalFault(SolverInternalFault::StateInvariant));
        }
    }
    let current_polarity =
        current_polarity.ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
    let reason_polarity =
        reason_polarity.ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
    let (positive_parent, negative_parent) = match (current_polarity, reason_polarity) {
        (true, false) => (current_id, reason.id),
        (false, true) => (reason.id, current_id),
        _ => return Err(Stop::InternalFault(SolverInternalFault::StateInvariant)),
    };

    let capacity = current
        .len()
        .checked_add(reason.literals.len())
        .ok_or(Stop::InternalFault(SolverInternalFault::StateInvariant))?;
    let mut resolvent = fallible_vec(capacity, SolverResource::AddressSpace)?;
    resolvent.extend(
        current
            .iter()
            .chain(&reason.literals)
            .copied()
            .filter(|literal| literal.variable != pivot),
    );
    Ok((
        canonicalize_solver_literals(resolvent)?,
        positive_parent,
        negative_parent,
    ))
}

fn enforce_initial(resource: SolverResource, limit: u64, actual: u64) -> EngineResult<()> {
    if actual <= limit {
        Ok(())
    } else {
        Err(Stop::Inconclusive(SolverInconclusive::ResourceExhausted {
            resource,
            limit,
            actual,
        }))
    }
}

fn schema_resource(resource: ResourceKind) -> SolverResource {
    match resource {
        ResourceKind::EncodedBytes => SolverResource::ArtifactBytes,
        ResourceKind::Variables | ResourceKind::Assignments => SolverResource::Variables,
        ResourceKind::Clauses => SolverResource::Clauses,
        ResourceKind::Literals => SolverResource::Literals,
        ResourceKind::ProofSteps => SolverResource::ProofSteps,
        ResourceKind::Dependencies => SolverResource::ProofDependencies,
    }
}

fn schema_stop(error: SchemaError) -> Stop {
    match error {
        SchemaError::ResourceLimitExceeded {
            resource,
            limit,
            actual,
        } => Stop::Inconclusive(SolverInconclusive::ResourceExhausted {
            resource: schema_resource(resource),
            limit,
            actual,
        }),
        other => Stop::InternalFault(SolverInternalFault::Schema(other)),
    }
}

fn fallible_vec<T>(capacity: usize, resource: SolverResource) -> EngineResult<Vec<T>> {
    let mut values = Vec::new();
    values.try_reserve(capacity).map_err(|_| {
        Stop::Inconclusive(SolverInconclusive::AllocationRefused {
            resource,
            requested: capacity as u64,
        })
    })?;
    Ok(values)
}

fn fallible_filled_vec<T: Clone>(count: usize, value: T) -> EngineResult<Vec<T>> {
    let mut values = fallible_vec(count, SolverResource::AddressSpace)?;
    values.resize(count, value);
    Ok(values)
}

fn fallible_nested_vec(count: usize) -> EngineResult<Vec<Vec<usize>>> {
    let mut values = fallible_vec(count, SolverResource::AddressSpace)?;
    values.resize_with(count, Vec::new);
    Ok(values)
}

fn literal_index(literal: SolverLiteral) -> EngineResult<usize> {
    literal
        .variable
        .checked_mul(2)
        .and_then(|base| base.checked_add(usize::from(literal.positive)))
        .ok_or({
            Stop::Inconclusive(SolverInconclusive::AllocationRefused {
                resource: SolverResource::AddressSpace,
                requested: literal.variable as u64,
            })
        })
}

/// The one-indexed Luby sequence: 1, 1, 2, 1, 1, 2, 4, ...
fn luby(index: u64) -> u64 {
    let mut index = index.saturating_sub(1);
    let mut size = 1_u64;
    while size < index.saturating_add(1) {
        size = size.saturating_mul(2).saturating_add(1);
    }
    while size.saturating_sub(1) != index {
        size = (size.saturating_sub(1)) / 2;
        index %= size;
    }
    size.saturating_add(1) / 2
}

#[cfg(test)]
mod cdcl_state_model {
    use super::*;

    fn variable(raw: u32) -> VariableId {
        VariableId::new(raw).expect("non-zero test variable")
    }

    fn id(raw: u64) -> ClauseId {
        ClauseId::new(raw).expect("non-zero test clause")
    }

    fn literal(raw: i64) -> Literal {
        Literal::from_dimacs(raw).expect("test literal")
    }

    pub(super) fn clause(values: &[i64]) -> Clause {
        Clause::new(values.iter().copied().map(literal).collect()).expect("test clause")
    }

    pub(super) fn cnf(variable_count: u32, rows: &[&[i64]]) -> Cnf {
        Cnf::new(
            variable_count,
            rows.iter()
                .enumerate()
                .map(|(index, row)| InputClause::new(id(index as u64 + 1), clause(row)))
                .collect(),
            SchemaLimits::default(),
        )
        .expect("test CNF")
    }

    pub(super) fn decision_unsat() -> Cnf {
        cnf(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]])
    }

    pub(super) fn pigeonhole(pigeons: u32, holes: u32) -> Cnf {
        let variable = |pigeon: u32, hole: u32| pigeon * holes + hole + 1;
        let mut clauses = Vec::new();
        for pigeon in 0..pigeons {
            let literals = (0..holes)
                .map(|hole| literal(i64::from(variable(pigeon, hole))))
                .collect();
            clauses.push(Clause::new(literals).expect("pigeon placement clause"));
        }
        for hole in 0..holes {
            for first in 0..pigeons {
                for second in first + 1..pigeons {
                    clauses.push(
                        Clause::new(vec![
                            literal(-i64::from(variable(first, hole))),
                            literal(-i64::from(variable(second, hole))),
                        ])
                        .expect("exclusive hole clause"),
                    );
                }
            }
        }
        Cnf::new(
            pigeons * holes,
            clauses
                .into_iter()
                .enumerate()
                .map(|(index, clause)| InputClause::new(id(index as u64 + 1), clause))
                .collect(),
            SchemaLimits::default(),
        )
        .expect("pigeonhole CNF")
    }

    #[test]
    fn sat_and_unsat_are_checked_before_publication() {
        let sat = cnf(3, &[&[1, -2], &[2], &[-1, 3]]);
        let sat_outcome = solve(&sat, SolverLimits::default());
        let SolverOutcome::Sat { artifact, .. } = sat_outcome else {
            panic!("expected checked SAT artifact");
        };
        assert_eq!(artifact.cnf_bytes(), sat.to_canonical_bytes());
        assert_eq!(artifact.model().satisfies(&sat), Ok(true));

        let unsat = decision_unsat();
        let unsat_outcome = solve(&unsat, SolverLimits::default());
        let SolverOutcome::Unsat { artifact, .. } = unsat_outcome else {
            panic!("expected checked UNSAT artifact");
        };
        assert_eq!(artifact.cnf_bytes(), unsat.to_canonical_bytes());
        assert!(artifact.receipt().derived_clauses >= 1);
        assert!(matches!(
            crate::check_unsat_streams(
                artifact.cnf_bytes(),
                artifact.proof_bytes(),
                ProofCheckLimits::default()
            ),
            ProofCheckOutcome::Verified(_)
        ));
    }

    #[test]
    fn root_empty_clause_and_zero_variable_formula_are_total() {
        let empty = cnf(0, &[&[]]);
        let SolverOutcome::Unsat { artifact, .. } = solve(&empty, SolverLimits::default()) else {
            panic!("input empty clause must be UNSAT");
        };
        assert_eq!(artifact.proof().facts().derived_clauses, 0);

        let true_formula = cnf(0, &[]);
        let SolverOutcome::Sat { artifact, .. } = solve(&true_formula, SolverLimits::default())
        else {
            panic!("empty conjunction must be SAT");
        };
        assert!(artifact.model().assignments().is_empty());
    }

    #[test]
    fn fixed_policy_rows_are_load_bearing() {
        assert_eq!(
            DETERMINISTIC_CDCL_POLICY,
            CdclDeterminismPolicy {
                policy_id: "fln.verdict.cdcl.determinism/2",
                variable_order: "highest-integer-activity-then-smallest-variable",
                initial_phase: "negative-then-saved-phase",
                conflict_analysis: "first-uip-root-context-preserving-backjump",
                restart_schedule: "luby-base-conflicts",
                proof_order: "reverse-trail-resolution-relevant-rup-fallback",
            }
        );
        assert_eq!(
            (1..=15).map(luby).collect::<Vec<_>>(),
            vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]
        );
    }

    #[test]
    fn incremental_scopes_assumptions_and_recovery_use_exact_effective_cnf() {
        let base = cnf(2, &[&[1, 2]]);
        let mut incremental = IncrementalSolver::new(base);
        incremental.push_scope().expect("push scope");
        incremental
            .add_clause(clause(&[-1]))
            .expect("add first unit");
        incremental
            .add_clause(clause(&[-2]))
            .expect("add second unit");
        let scoped = incremental
            .solve(&[], SolverLimits::default())
            .expect("materialize scoped formula");
        assert!(matches!(scoped.outcome(), SolverOutcome::Unsat { .. }));

        incremental.pop_scope().expect("pop scope");
        let recovered = incremental
            .solve(&[], SolverLimits::default())
            .expect("materialize recovered formula");
        assert!(matches!(recovered.outcome(), SolverOutcome::Sat { .. }));

        let assumptions_a = incremental
            .solve(&[literal(-2), literal(-1)], SolverLimits::default())
            .expect("assumption solve");
        let assumptions_b = incremental
            .solve(&[literal(-1), literal(-2)], SolverLimits::default())
            .expect("permuted assumption solve");
        assert_eq!(
            assumptions_a.cnf().to_canonical_bytes(),
            assumptions_b.cnf().to_canonical_bytes()
        );
        assert_eq!(assumptions_a.outcome(), assumptions_b.outcome());
        assert!(matches!(
            assumptions_a.outcome(),
            SolverOutcome::Unsat { .. }
        ));
        assert_eq!(incremental.pop_scope(), Err(IncrementalError::NoOpenScope));
    }

    #[test]
    fn out_of_range_incremental_input_is_a_typed_preparation_failure() {
        let mut incremental = IncrementalSolver::new(cnf(1, &[]));
        assert_eq!(
            incremental.add_clause(clause(&[2])),
            Err(IncrementalError::VariableOutOfRange {
                variable: variable(2),
                declared: 1,
            })
        );
        assert_eq!(
            incremental.materialize(&[literal(2)], SchemaLimits::default()),
            Err(IncrementalError::VariableOutOfRange {
                variable: variable(2),
                declared: 1,
            })
        );
    }
}

#[cfg(test)]
mod propagation_conflict_property {
    use super::cdcl_state_model::{clause, cnf};
    use super::*;

    const CAMPAIGN_SEEDS: [u64; 4] = [
        0x8c67_4f3a_2d91_b5e7,
        0x39a4_71d8_e2c6_0b5f,
        0xd14f_02a9_6c83_7be5,
        0x52be_c701_94ad_f638,
    ];
    const CASES_PER_SEED: u64 = 256;

    fn brute_force(formula: &Cnf) -> bool {
        let variables = formula.variable_count();
        assert!(variables <= 12);
        for bits in 0_u64..(1_u64 << variables) {
            let assignments = (1..=variables)
                .map(|raw| {
                    Assignment::new(
                        VariableId::new(raw).expect("brute variable"),
                        bits & (1_u64 << (raw - 1)) != 0,
                    )
                })
                .collect();
            let model = SatModel::new(variables, assignments, SchemaLimits::default())
                .expect("brute model");
            if model.satisfies(formula) == Ok(true) {
                return true;
            }
        }
        false
    }

    fn corrupt_conclusion_id(proof_bytes: &[u8]) -> Vec<u8> {
        let mut corrupted = proof_bytes.to_vec();
        let conclusion_id = corrupted
            .len()
            .checked_sub(8)
            .expect("canonical proof has a conclusion clause id");
        corrupted[conclusion_id..].fill(0);
        corrupted
    }

    #[test]
    fn seeded_solver_checker_campaign_accepts_every_artifact_and_refuses_every_mutation() {
        let mut sat_cases = 0_u64;
        let mut unsat_cases = 0_u64;
        let mut refused_mutations = 0_u64;

        for (seed_index, initial_seed) in CAMPAIGN_SEEDS.into_iter().enumerate() {
            let mut state = initial_seed;
            for round in 0..CASES_PER_SEED {
                let variables = (round % 5 + 1) as u32;
                let row_count = (round % 10 + 1) as usize;
                let mut rows = Vec::new();
                for _ in 0..row_count {
                    state = state
                        .wrapping_mul(6_364_136_223_846_793_005)
                        .wrapping_add(1);
                    let width = ((state >> 32) % 3 + 1) as usize;
                    let mut selected = BTreeSet::new();
                    while selected.len() < width.min(variables as usize) {
                        state = state
                            .wrapping_mul(6_364_136_223_846_793_005)
                            .wrapping_add(1);
                        selected.insert((state >> 32) as u32 % variables + 1);
                    }
                    let mut literals = Vec::new();
                    for variable in selected {
                        state = state
                            .wrapping_mul(6_364_136_223_846_793_005)
                            .wrapping_add(1);
                        let signed = if state & 1 == 0 {
                            i64::from(variable)
                        } else {
                            -i64::from(variable)
                        };
                        literals.push(signed);
                    }
                    rows.push(clause(&literals));
                }
                let formula = Cnf::new(
                    variables,
                    rows.into_iter()
                        .enumerate()
                        .map(|(index, row)| {
                            InputClause::new(
                                ClauseId::new(index as u64 + 1).expect("campaign id"),
                                row,
                            )
                        })
                        .collect(),
                    SchemaLimits::default(),
                )
                .expect("campaign CNF");
                let expected_sat = brute_force(&formula);
                match solve(&formula, SolverLimits::default()) {
                    SolverOutcome::Sat { artifact, .. } => {
                        sat_cases += 1;
                        assert!(
                            expected_sat,
                            "seed {seed_index} round {round} produced false SAT"
                        );
                        assert_eq!(artifact.cnf_bytes(), formula.to_canonical_bytes());
                        let independently_decoded = SatModel::from_canonical_bytes(
                            artifact.model_bytes(),
                            SchemaLimits::default(),
                        )
                        .expect("checked SAT bytes must decode independently");
                        assert_eq!(&independently_decoded, artifact.model());
                        assert_eq!(independently_decoded.satisfies(&formula), Ok(true));
                    }
                    SolverOutcome::Unsat { artifact, .. } => {
                        unsat_cases += 1;
                        assert!(
                            !expected_sat,
                            "seed {seed_index} round {round} produced false UNSAT"
                        );
                        assert!(matches!(
                            crate::check_unsat_streams(
                                artifact.cnf_bytes(),
                                artifact.proof_bytes(),
                                ProofCheckLimits::default()
                            ),
                            ProofCheckOutcome::Verified(_)
                        ));

                        let corrupted = corrupt_conclusion_id(artifact.proof_bytes());
                        assert!(matches!(
                            crate::check_unsat_streams(
                                artifact.cnf_bytes(),
                                &corrupted[..],
                                ProofCheckLimits::default()
                            ),
                            ProofCheckOutcome::Refused(ProofRefusal::InvalidClauseId { .. })
                        ));
                        refused_mutations += 1;
                    }
                    other => {
                        panic!("seed {seed_index} round {round} produced non-verdict {other:?}")
                    }
                }
            }
        }

        assert!(sat_cases > 0, "campaign must exercise checked SAT");
        assert!(unsat_cases > 0, "campaign must exercise checked UNSAT");
        assert_eq!(
            refused_mutations, unsat_cases,
            "every emitted proof must have a refused mutation"
        );

        let unit_chain = cnf(4, &[&[1], &[-1, 2], &[-2, 3], &[-3, 4], &[-4]]);
        assert!(matches!(
            solve(&unit_chain, SolverLimits::default()),
            SolverOutcome::Unsat { .. }
        ));
    }
}

#[cfg(test)]
mod deterministic_restart_matrix {
    use super::cdcl_state_model::{decision_unsat, pigeonhole};
    use super::*;
    use std::thread;

    fn semantic_bytes(outcome: &SolverOutcome) -> (&[u8], SolverStatistics) {
        match outcome {
            SolverOutcome::Sat {
                artifact,
                statistics,
            } => (artifact.model_bytes(), *statistics),
            SolverOutcome::Unsat {
                artifact,
                statistics,
            } => (artifact.proof_bytes(), *statistics),
            other => panic!("matrix produced non-verdict {other:?}"),
        }
    }

    #[test]
    fn concurrent_one_eight_and_thirty_two_runs_are_byte_identical() {
        let formula = pigeonhole(4, 3);
        let limits = SolverLimits {
            restart_base_conflicts: 1,
            ..SolverLimits::default()
        };
        let mut expected: Option<(Vec<u8>, SolverStatistics)> = None;
        for workers in [1_usize, 8, 32] {
            let mut handles = Vec::new();
            for _ in 0..workers {
                let cloned = formula.clone();
                handles.push(thread::spawn(move || solve(&cloned, limits)));
            }
            for handle in handles {
                let outcome = handle.join().expect("solver thread");
                let (bytes, statistics) = semantic_bytes(&outcome);
                assert!(statistics.restarts > 0, "restart lane was not exercised");
                let current = (bytes.to_vec(), statistics);
                if let Some(expected) = &expected {
                    assert_eq!(&current, expected);
                } else {
                    expected = Some(current);
                }
            }
        }
    }

    #[test]
    fn exact_operation_budgets_pass_and_one_less_is_inconclusive() {
        let formula = decision_unsat();
        let baseline = solve(&formula, SolverLimits::default());
        let stats = baseline.statistics();
        assert!(matches!(baseline, SolverOutcome::Unsat { .. }));
        let exact = SolverLimits {
            max_decisions: stats.decisions,
            max_propagations: stats.propagations,
            max_conflicts: stats.conflicts,
            max_learned_clauses: stats.learned_clauses,
            max_proof_steps: stats.proof_steps,
            max_proof_dependencies: stats.proof_dependencies,
            max_work_units: stats.work_units,
            ..SolverLimits::default()
        };
        assert!(matches!(
            solve(&formula, exact),
            SolverOutcome::Unsat { .. }
        ));

        let short = SolverLimits {
            max_decisions: stats.decisions - 1,
            ..exact
        };
        let outcome = solve(&formula, short);
        assert!(matches!(
            outcome,
            SolverOutcome::Inconclusive {
                cause: SolverInconclusive::ResourceExhausted {
                    resource: SolverResource::Decisions,
                    limit,
                    actual,
                },
                ..
            } if actual == limit + 1
        ));
        assert_eq!(outcome.checked_artifact(), None);
    }
}

#[cfg(test)]
mod proof_logger_mutations {
    use super::cdcl_state_model::decision_unsat;
    use super::*;

    #[test]
    fn every_emitted_proof_round_trips_and_a_corruption_is_refused() {
        let formula = decision_unsat();
        let SolverOutcome::Unsat { artifact, .. } = solve(&formula, SolverLimits::default()) else {
            panic!("proof fixture must be UNSAT");
        };
        assert!(matches!(
            crate::check_unsat_streams(
                artifact.cnf_bytes(),
                artifact.proof_bytes(),
                ProofCheckLimits::default()
            ),
            ProofCheckOutcome::Verified(_)
        ));

        let mut corrupted = artifact.proof_bytes().to_vec();
        let conclusion_id = corrupted
            .len()
            .checked_sub(8)
            .expect("proof has conclusion id");
        corrupted[conclusion_id..].fill(0);
        assert!(matches!(
            crate::check_unsat_streams(
                artifact.cnf_bytes(),
                &corrupted[..],
                ProofCheckLimits::default()
            ),
            ProofCheckOutcome::Refused(ProofRefusal::InvalidClauseId { .. })
        ));
    }

    #[test]
    fn cancellation_and_resource_exhaustion_never_publish_artifacts() {
        let formula = decision_unsat();
        let cancelled = solve_with_cancel(&formula, SolverLimits::default(), || true);
        assert!(matches!(
            cancelled,
            SolverOutcome::Inconclusive {
                cause: SolverInconclusive::Cancelled,
                ..
            }
        ));
        assert_eq!(cancelled.checked_artifact(), None);

        let exhausted = solve(
            &formula,
            SolverLimits {
                max_decisions: 0,
                ..SolverLimits::default()
            },
        );
        assert!(matches!(
            exhausted,
            SolverOutcome::Inconclusive {
                cause: SolverInconclusive::ResourceExhausted {
                    resource: SolverResource::Decisions,
                    limit: 0,
                    actual: 1,
                },
                ..
            }
        ));
        assert_eq!(exhausted.checked_artifact(), None);

        assert!(matches!(
            solve(&formula, SolverLimits::default()),
            SolverOutcome::Unsat { .. }
        ));
    }
}

#[cfg(all(test, unix))]
mod verdict_solver_no_mock_e2e {
    use super::cdcl_state_model::decision_unsat;
    use super::*;
    use std::io::{Read, Write};
    use std::os::unix::net::UnixStream;

    #[test]
    fn real_kernel_stream_carries_positive_corruption_and_recovery() {
        let formula = decision_unsat();
        let SolverOutcome::Unsat { artifact, .. } = solve(&formula, SolverLimits::default()) else {
            panic!("stream fixture must be UNSAT");
        };
        let (mut reader, mut writer) = UnixStream::pair().expect("stream pair");
        let bytes = artifact.proof_bytes().to_vec();
        let handle = std::thread::spawn(move || {
            for chunk in bytes.chunks(5) {
                writer.write_all(chunk).expect("proof chunk");
            }
        });
        let mut streamed = Vec::new();
        reader
            .read_to_end(&mut streamed)
            .expect("read proof stream");
        handle.join().expect("writer final state");
        assert!(matches!(
            crate::check_unsat_streams(
                artifact.cnf_bytes(),
                &streamed[..],
                ProofCheckLimits::default()
            ),
            ProofCheckOutcome::Verified(_)
        ));

        let final_index = streamed.len() - 1;
        streamed[final_index] ^= 0x80;
        assert!(matches!(
            crate::check_unsat_streams(
                artifact.cnf_bytes(),
                &streamed[..],
                ProofCheckLimits::default()
            ),
            ProofCheckOutcome::Refused(_)
        ));
        assert!(matches!(
            solve(&formula, SolverLimits::default()),
            SolverOutcome::Unsat { .. }
        ));
    }
}
