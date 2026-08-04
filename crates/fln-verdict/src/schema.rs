//! Validated, canonical artifact schemas for the untrusted Verdict engine.
//!
//! This module deliberately stops at structural validation. In particular, an
//! [`UnsatProof`] records a closed LRAT-shaped dependency graph, but does not claim
//! that its RUP or RAT steps are semantically valid. The independent proof checker
//! is a later authority boundary; constructing or decoding one of these values can
//! never admit a declaration.

use std::collections::BTreeMap;

use fln_hash::domain::{Digest, Domain, hash};

/// Hard limits shared by construction and decoding.
///
/// The byte limits are checked before count-directed allocation by the codec. The
/// remaining limits bound normalization and structural proof validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerdictLimits {
    pub max_encoded_bytes: u128,
    pub max_record_bytes: usize,
    pub max_variables: usize,
    pub max_clauses: usize,
    pub max_literals_per_clause: usize,
    pub max_total_literals: usize,
    pub max_model_assignments: usize,
    pub max_proof_actions: usize,
    pub max_dependency_refs: usize,
    pub max_rat_hints: usize,
    pub max_live_clauses: usize,
}

impl VerdictLimits {
    #[allow(clippy::too_many_arguments)]
    pub const fn new(
        max_encoded_bytes: u128,
        max_record_bytes: usize,
        max_variables: usize,
        max_clauses: usize,
        max_literals_per_clause: usize,
        max_total_literals: usize,
        max_model_assignments: usize,
        max_proof_actions: usize,
        max_dependency_refs: usize,
        max_rat_hints: usize,
        max_live_clauses: usize,
    ) -> Self {
        Self {
            max_encoded_bytes,
            max_record_bytes,
            max_variables,
            max_clauses,
            max_literals_per_clause,
            max_total_literals,
            max_model_assignments,
            max_proof_actions,
            max_dependency_refs,
            max_rat_hints,
            max_live_clauses,
        }
    }
}

impl Default for VerdictLimits {
    fn default() -> Self {
        Self::new(
            512 * 1024 * 1024,
            16 * 1024 * 1024,
            100_000_000,
            100_000_000,
            10_000_000,
            500_000_000,
            100_000_000,
            500_000_000,
            2_000_000_000,
            100_000_000,
            200_000_000,
        )
    }
}

/// A dimension which can exhaust a construction or decode budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerdictResource {
    EncodedBytes,
    RecordBytes,
    Variables,
    Clauses,
    LiteralsPerClause,
    TotalLiterals,
    ModelAssignments,
    ProofActions,
    DependencyReferences,
    RatHints,
    LiveClauses,
}

/// Typed schema or structural-validation refusal.
///
/// No constructor returns a partially validated artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerdictError {
    ZeroVariableId,
    ZeroClauseId,
    VariableOutOfRange {
        variable: u64,
        variable_count: u64,
    },
    ModelLengthMismatch {
        variable_count: u64,
        assignments: usize,
    },
    ResourceLimitExceeded {
        resource: VerdictResource,
        limit: u128,
        actual: u128,
    },
    AddedClauseIdNotFresh {
        previous: u64,
        actual: u64,
    },
    UnknownOrDeletedDependency {
        clause_id: u64,
    },
    EmptyDeletion,
    NonCanonicalDeletion,
    NonCanonicalRatHints,
    RatPivotAbsent,
    ConclusionUnknownOrDeleted {
        clause_id: u64,
    },
    ConclusionClauseNotEmpty {
        clause_id: u64,
    },
}

impl std::fmt::Display for VerdictError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ZeroVariableId => formatter.write_str("variable id zero is invalid"),
            Self::ZeroClauseId => formatter.write_str("clause id zero is invalid"),
            Self::VariableOutOfRange {
                variable,
                variable_count,
            } => write!(
                formatter,
                "variable id {variable} exceeds declared variable count {variable_count}"
            ),
            Self::ModelLengthMismatch {
                variable_count,
                assignments,
            } => write!(
                formatter,
                "model has {assignments} assignments for {variable_count} variables"
            ),
            Self::ResourceLimitExceeded {
                resource,
                limit,
                actual,
            } => write!(
                formatter,
                "verdict resource {resource:?} exceeded: limit={limit}, actual={actual}"
            ),
            Self::AddedClauseIdNotFresh { previous, actual } => write!(
                formatter,
                "added clause id {actual} is not strictly greater than {previous}"
            ),
            Self::UnknownOrDeletedDependency { clause_id } => write!(
                formatter,
                "proof dependency {clause_id} is unknown, forward, or deleted"
            ),
            Self::EmptyDeletion => formatter.write_str("proof deletion set is empty"),
            Self::NonCanonicalDeletion => {
                formatter.write_str("proof deletion ids are not strictly increasing")
            }
            Self::NonCanonicalRatHints => {
                formatter.write_str("RAT target ids are not strictly increasing")
            }
            Self::RatPivotAbsent => {
                formatter.write_str("RAT pivot does not occur in the added clause")
            }
            Self::ConclusionUnknownOrDeleted { clause_id } => write!(
                formatter,
                "proof conclusion references unknown or deleted clause {clause_id}"
            ),
            Self::ConclusionClauseNotEmpty { clause_id } => {
                write!(
                    formatter,
                    "proof conclusion clause {clause_id} is not empty"
                )
            }
        }
    }
}

impl std::error::Error for VerdictError {}

fn check_limit(resource: VerdictResource, actual: usize, limit: usize) -> Result<(), VerdictError> {
    if actual > limit {
        Err(VerdictError::ResourceLimitExceeded {
            resource,
            limit: limit as u128,
            actual: actual as u128,
        })
    } else {
        Ok(())
    }
}

fn checked_total(
    resource: VerdictResource,
    current: usize,
    increment: usize,
    limit: usize,
) -> Result<usize, VerdictError> {
    let actual = current
        .checked_add(increment)
        .ok_or(VerdictError::ResourceLimitExceeded {
            resource,
            limit: limit as u128,
            actual: u128::MAX,
        })?;
    check_limit(resource, actual, limit)?;
    Ok(actual)
}

/// A DIMACS-style variable id. Zero is never representable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VariableId(u64);

impl VariableId {
    pub fn new(value: u64) -> Result<Self, VerdictError> {
        if value == 0 {
            Err(VerdictError::ZeroVariableId)
        } else {
            Ok(Self(value))
        }
    }

    pub const fn get(self) -> u64 {
        self.0
    }
}

/// A proof-clause id. Zero is never representable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClauseId(u64);

impl ClauseId {
    pub fn new(value: u64) -> Result<Self, VerdictError> {
        if value == 0 {
            Err(VerdictError::ZeroClauseId)
        } else {
            Ok(Self(value))
        }
    }

    pub const fn get(self) -> u64 {
        self.0
    }
}

/// Literal polarity. Declaration order is the canonical wire and sort order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Polarity {
    Negative,
    Positive,
}

/// A nonzero variable together with its polarity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal {
    variable: VariableId,
    polarity: Polarity,
}

impl Literal {
    pub const fn new(variable: VariableId, polarity: Polarity) -> Self {
        Self { variable, polarity }
    }

    pub const fn variable(self) -> VariableId {
        self.variable
    }

    pub const fn polarity(self) -> Polarity {
        self.polarity
    }

    pub const fn negated(self) -> Self {
        let polarity = match self.polarity {
            Polarity::Negative => Polarity::Positive,
            Polarity::Positive => Polarity::Negative,
        };
        Self {
            variable: self.variable,
            polarity,
        }
    }
}

/// A sorted, duplicate-free clause. Empty and tautological clauses are representable.
///
/// Tautological input clauses are removed by [`CanonicalCnf::new`]. They remain
/// representable here because an LRAT-shaped proof record can structurally add one.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CanonicalClause {
    literals: Vec<Literal>,
}

impl CanonicalClause {
    pub fn new(
        mut literals: Vec<Literal>,
        variable_count: u64,
        limits: &VerdictLimits,
    ) -> Result<Self, VerdictError> {
        check_limit(
            VerdictResource::LiteralsPerClause,
            literals.len(),
            limits.max_literals_per_clause,
        )?;
        for literal in &literals {
            if literal.variable().get() > variable_count {
                return Err(VerdictError::VariableOutOfRange {
                    variable: literal.variable().get(),
                    variable_count,
                });
            }
        }
        literals.sort_unstable();
        literals.dedup();
        Ok(Self { literals })
    }

    pub fn literals(&self) -> &[Literal] {
        &self.literals
    }

    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    pub fn is_tautology(&self) -> bool {
        self.literals
            .windows(2)
            .any(|pair| pair[0].variable == pair[1].variable)
    }

    pub fn contains(&self, literal: Literal) -> bool {
        self.literals.binary_search(&literal).is_ok()
    }
}

/// Exact dimensions of one validated artifact.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct VerdictFacts {
    pub variables: usize,
    pub clauses: usize,
    pub total_literals: usize,
    pub model_assignments: usize,
    pub proof_actions: usize,
    pub dependency_references: usize,
    pub rat_hints: usize,
    pub maximum_live_clauses: usize,
}

/// Domain-separated identity of a canonical CNF.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CnfRoot(Digest);

impl CnfRoot {
    pub const fn from_digest(digest: Digest) -> Self {
        Self(digest)
    }

    pub const fn digest(self) -> Digest {
        self.0
    }
}

impl std::fmt::Display for CnfRoot {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

/// Canonical CNF: clauses and literals are sorted and deduplicated; tautological
/// clauses are dropped; an empty clause is retained.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalCnf {
    variable_count: u64,
    clauses: Vec<CanonicalClause>,
    facts: VerdictFacts,
}

impl CanonicalCnf {
    pub fn new(
        variable_count: u64,
        clauses: Vec<Vec<Literal>>,
        limits: &VerdictLimits,
    ) -> Result<Self, VerdictError> {
        let variable_count_usize =
            usize::try_from(variable_count).map_err(|_| VerdictError::ResourceLimitExceeded {
                resource: VerdictResource::Variables,
                limit: limits.max_variables as u128,
                actual: variable_count as u128,
            })?;
        check_limit(
            VerdictResource::Variables,
            variable_count_usize,
            limits.max_variables,
        )?;
        check_limit(VerdictResource::Clauses, clauses.len(), limits.max_clauses)?;

        let mut total_literals = 0usize;
        let mut canonical = Vec::with_capacity(clauses.len());
        for literals in clauses {
            total_literals = checked_total(
                VerdictResource::TotalLiterals,
                total_literals,
                literals.len(),
                limits.max_total_literals,
            )?;
            let clause = CanonicalClause::new(literals, variable_count, limits)?;
            if !clause.is_tautology() {
                canonical.push(clause);
            }
        }
        canonical.sort_unstable();
        canonical.dedup();

        let canonical_literals = canonical.iter().try_fold(0usize, |total, clause| {
            checked_total(
                VerdictResource::TotalLiterals,
                total,
                clause.literals.len(),
                limits.max_total_literals,
            )
        })?;
        let facts = VerdictFacts {
            variables: variable_count_usize,
            clauses: canonical.len(),
            total_literals: canonical_literals,
            ..VerdictFacts::default()
        };
        Ok(Self {
            variable_count,
            clauses: canonical,
            facts,
        })
    }

    pub fn variable_count(&self) -> u64 {
        self.variable_count
    }

    pub fn clauses(&self) -> &[CanonicalClause] {
        &self.clauses
    }

    pub fn facts(&self) -> VerdictFacts {
        self.facts
    }

    pub fn root(&self) -> CnfRoot {
        CnfRoot(hash(Domain::VerdictCnf, &crate::codec::encode_cnf(self)))
    }

    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        crate::codec::encode_cnf(self)
    }

    pub fn from_canonical_bytes(
        bytes: &[u8],
        limits: &VerdictLimits,
    ) -> Result<Self, crate::codec::VerdictCodecError> {
        crate::codec::decode_cnf(bytes, limits)
    }
}

/// Domain-separated identity of a complete SAT model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SatModelRoot(Digest);

impl SatModelRoot {
    pub const fn digest(self) -> Digest {
        self.0
    }
}

impl std::fmt::Display for SatModelRoot {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

/// A total assignment bound to an exact canonical CNF root.
///
/// This is an untrusted solver artifact. A later checker must still evaluate every
/// clause before treating the model as evidence of satisfiability.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SatModel {
    cnf_root: CnfRoot,
    variable_count: u64,
    assignments: Vec<bool>,
    facts: VerdictFacts,
}

impl SatModel {
    pub fn new(
        cnf: &CanonicalCnf,
        assignments: Vec<bool>,
        limits: &VerdictLimits,
    ) -> Result<Self, VerdictError> {
        check_limit(
            VerdictResource::ModelAssignments,
            assignments.len(),
            limits.max_model_assignments,
        )?;
        if u64::try_from(assignments.len()).ok() != Some(cnf.variable_count) {
            return Err(VerdictError::ModelLengthMismatch {
                variable_count: cnf.variable_count,
                assignments: assignments.len(),
            });
        }
        Ok(Self {
            cnf_root: cnf.root(),
            variable_count: cnf.variable_count,
            facts: VerdictFacts {
                variables: cnf.facts.variables,
                model_assignments: assignments.len(),
                ..VerdictFacts::default()
            },
            assignments,
        })
    }

    pub fn cnf_root(&self) -> CnfRoot {
        self.cnf_root
    }

    pub fn variable_count(&self) -> u64 {
        self.variable_count
    }

    pub fn assignments(&self) -> &[bool] {
        &self.assignments
    }

    pub fn assignment(&self, variable: VariableId) -> Option<bool> {
        let zero_based = variable.get().checked_sub(1)?;
        let index = usize::try_from(zero_based).ok()?;
        self.assignments.get(index).copied()
    }

    pub fn facts(&self) -> VerdictFacts {
        self.facts
    }

    pub fn root(&self) -> SatModelRoot {
        SatModelRoot(hash(
            Domain::VerdictSatModel,
            &crate::codec::encode_sat_model(self),
        ))
    }

    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        crate::codec::encode_sat_model(self)
    }

    pub fn from_canonical_bytes(
        bytes: &[u8],
        cnf: &CanonicalCnf,
        limits: &VerdictLimits,
    ) -> Result<Self, crate::codec::VerdictCodecError> {
        crate::codec::decode_sat_model(bytes, cnf, limits)
    }
}

/// One RAT target and its ordered propagation hints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RatHint {
    clause_id: ClauseId,
    hints: Vec<ClauseId>,
}

impl RatHint {
    pub fn new(clause_id: ClauseId, hints: Vec<ClauseId>) -> Self {
        Self { clause_id, hints }
    }

    pub fn clause_id(&self) -> ClauseId {
        self.clause_id
    }

    pub fn hints(&self) -> &[ClauseId] {
        &self.hints
    }
}

/// A canonical, LRAT-shaped proof action.
///
/// Hint order is retained because it is replay data. Deletion ids and RAT target
/// rows are sets and therefore must be strictly increasing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofAction {
    AddRup {
        id: ClauseId,
        clause: CanonicalClause,
        hints: Vec<ClauseId>,
    },
    AddRat {
        id: ClauseId,
        clause: CanonicalClause,
        pivot: Literal,
        rup_hints: Vec<ClauseId>,
        rat_hints: Vec<RatHint>,
    },
    Delete {
        ids: Vec<ClauseId>,
    },
}

impl ProofAction {
    pub fn add_rup(id: ClauseId, clause: CanonicalClause, hints: Vec<ClauseId>) -> Self {
        Self::AddRup { id, clause, hints }
    }

    pub fn add_rat(
        id: ClauseId,
        clause: CanonicalClause,
        pivot: Literal,
        rup_hints: Vec<ClauseId>,
        rat_hints: Vec<RatHint>,
    ) -> Self {
        Self::AddRat {
            id,
            clause,
            pivot,
            rup_hints,
            rat_hints,
        }
    }

    pub fn delete(ids: Vec<ClauseId>) -> Self {
        Self::Delete { ids }
    }
}

/// Domain-separated identity of a complete structural proof artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnsatProofRoot(Digest);

impl UnsatProofRoot {
    pub const fn digest(self) -> Digest {
        self.0
    }
}

impl std::fmt::Display for UnsatProofRoot {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

/// A complete, structurally closed LRAT-shaped proof stream.
///
/// Construction proves only framing and dependency properties: added ids are fresh,
/// every reference is backward and live, deletion sets are canonical, RAT pivots
/// occur in their clauses, and the explicit conclusion names a live empty clause.
/// It does not prove the semantic RUP/RAT obligations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsatProof {
    cnf_root: CnfRoot,
    actions: Vec<ProofAction>,
    empty_clause_id: ClauseId,
    facts: VerdictFacts,
}

impl UnsatProof {
    pub fn new(
        cnf: &CanonicalCnf,
        actions: Vec<ProofAction>,
        empty_clause_id: ClauseId,
        limits: &VerdictLimits,
    ) -> Result<Self, VerdictError> {
        check_limit(
            VerdictResource::ProofActions,
            actions.len(),
            limits.max_proof_actions,
        )?;

        let mut live = BTreeMap::new();
        for (index, clause) in cnf.clauses.iter().enumerate() {
            let id_value = u64::try_from(index)
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or(VerdictError::ResourceLimitExceeded {
                    resource: VerdictResource::Clauses,
                    limit: limits.max_clauses as u128,
                    actual: u128::MAX,
                })?;
            live.insert(
                ClauseId::new(id_value).expect("one-based clause id is nonzero"),
                clause.is_empty(),
            );
        }
        check_limit(
            VerdictResource::LiveClauses,
            live.len(),
            limits.max_live_clauses,
        )?;

        let mut previous_added =
            u64::try_from(cnf.clauses.len()).map_err(|_| VerdictError::ResourceLimitExceeded {
                resource: VerdictResource::Clauses,
                limit: limits.max_clauses as u128,
                actual: u128::MAX,
            })?;
        let mut total_literals = 0usize;
        let mut dependency_references = 0usize;
        let mut rat_hint_count = 0usize;
        let mut maximum_live = live.len();

        for action in &actions {
            match action {
                ProofAction::AddRup { id, clause, hints } => {
                    validate_added_clause(cnf, *id, clause, &mut previous_added, limits)?;
                    total_literals = checked_total(
                        VerdictResource::TotalLiterals,
                        total_literals,
                        clause.literals.len(),
                        limits.max_total_literals,
                    )?;
                    validate_dependencies(hints, &live, &mut dependency_references, limits)?;
                    live.insert(*id, clause.is_empty());
                }
                ProofAction::AddRat {
                    id,
                    clause,
                    pivot,
                    rup_hints,
                    rat_hints,
                } => {
                    validate_added_clause(cnf, *id, clause, &mut previous_added, limits)?;
                    if !clause.contains(*pivot) {
                        return Err(VerdictError::RatPivotAbsent);
                    }
                    total_literals = checked_total(
                        VerdictResource::TotalLiterals,
                        total_literals,
                        clause.literals.len(),
                        limits.max_total_literals,
                    )?;
                    validate_dependencies(rup_hints, &live, &mut dependency_references, limits)?;
                    if !strictly_increasing_by(rat_hints, |hint| hint.clause_id) {
                        return Err(VerdictError::NonCanonicalRatHints);
                    }
                    rat_hint_count = checked_total(
                        VerdictResource::RatHints,
                        rat_hint_count,
                        rat_hints.len(),
                        limits.max_rat_hints,
                    )?;
                    for rat_hint in rat_hints {
                        validate_dependencies(
                            std::slice::from_ref(&rat_hint.clause_id),
                            &live,
                            &mut dependency_references,
                            limits,
                        )?;
                        validate_dependencies(
                            &rat_hint.hints,
                            &live,
                            &mut dependency_references,
                            limits,
                        )?;
                    }
                    live.insert(*id, clause.is_empty());
                }
                ProofAction::Delete { ids } => {
                    if ids.is_empty() {
                        return Err(VerdictError::EmptyDeletion);
                    }
                    if !ids.windows(2).all(|pair| pair[0] < pair[1]) {
                        return Err(VerdictError::NonCanonicalDeletion);
                    }
                    for id in ids {
                        if live.remove(id).is_none() {
                            return Err(VerdictError::UnknownOrDeletedDependency {
                                clause_id: id.get(),
                            });
                        }
                    }
                }
            }
            check_limit(
                VerdictResource::LiveClauses,
                live.len(),
                limits.max_live_clauses,
            )?;
            maximum_live = maximum_live.max(live.len());
        }

        let conclusion_is_empty = live.get(&empty_clause_id).copied().ok_or(
            VerdictError::ConclusionUnknownOrDeleted {
                clause_id: empty_clause_id.get(),
            },
        )?;
        if !conclusion_is_empty {
            return Err(VerdictError::ConclusionClauseNotEmpty {
                clause_id: empty_clause_id.get(),
            });
        }

        let action_count = actions.len();
        Ok(Self {
            cnf_root: cnf.root(),
            actions,
            empty_clause_id,
            facts: VerdictFacts {
                variables: cnf.facts.variables,
                clauses: cnf.facts.clauses,
                total_literals,
                proof_actions: action_count,
                dependency_references,
                rat_hints: rat_hint_count,
                maximum_live_clauses: maximum_live,
                ..VerdictFacts::default()
            },
        })
    }

    pub fn cnf_root(&self) -> CnfRoot {
        self.cnf_root
    }

    pub fn actions(&self) -> &[ProofAction] {
        &self.actions
    }

    pub fn empty_clause_id(&self) -> ClauseId {
        self.empty_clause_id
    }

    pub fn facts(&self) -> VerdictFacts {
        self.facts
    }

    pub fn root(&self) -> UnsatProofRoot {
        UnsatProofRoot(hash(
            Domain::VerdictUnsatProof,
            &crate::codec::encode_unsat_proof(self),
        ))
    }

    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        crate::codec::encode_unsat_proof(self)
    }
}

fn validate_added_clause(
    cnf: &CanonicalCnf,
    id: ClauseId,
    clause: &CanonicalClause,
    previous_added: &mut u64,
    limits: &VerdictLimits,
) -> Result<(), VerdictError> {
    if id.get() <= *previous_added {
        return Err(VerdictError::AddedClauseIdNotFresh {
            previous: *previous_added,
            actual: id.get(),
        });
    }
    check_limit(
        VerdictResource::LiteralsPerClause,
        clause.literals.len(),
        limits.max_literals_per_clause,
    )?;
    for literal in &clause.literals {
        if literal.variable.get() > cnf.variable_count {
            return Err(VerdictError::VariableOutOfRange {
                variable: literal.variable.get(),
                variable_count: cnf.variable_count,
            });
        }
    }
    *previous_added = id.get();
    Ok(())
}

fn validate_dependencies(
    dependencies: &[ClauseId],
    live: &BTreeMap<ClauseId, bool>,
    total: &mut usize,
    limits: &VerdictLimits,
) -> Result<(), VerdictError> {
    *total = checked_total(
        VerdictResource::DependencyReferences,
        *total,
        dependencies.len(),
        limits.max_dependency_refs,
    )?;
    for dependency in dependencies {
        if !live.contains_key(dependency) {
            return Err(VerdictError::UnknownOrDeletedDependency {
                clause_id: dependency.get(),
            });
        }
    }
    Ok(())
}

fn strictly_increasing_by<T, K: Ord + Copy>(values: &[T], mut key: impl FnMut(&T) -> K) -> bool {
    values.windows(2).all(|pair| key(&pair[0]) < key(&pair[1]))
}

/// Deterministic solver resource dimensions. Wall-clock time is intentionally absent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverResource {
    Decisions,
    Conflicts,
    Propagations,
    LearnedClauses,
    ProofActions,
    ProofBytes,
}

/// Monotone counters reported by an untrusted solver run.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SolverUsage {
    pub decisions: u64,
    pub conflicts: u64,
    pub propagations: u64,
    pub learned_clauses: u64,
    pub proof_actions: u64,
    pub proof_bytes: u64,
}

/// A run which made no SAT/UNSAT claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InconclusiveReason {
    Cancelled,
    ResourceExceeded {
        resource: SolverResource,
        limit: u64,
        actual: u64,
    },
}

/// Stable, non-diagnostic classification for an internal solver fault.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InternalFault {
    code: u32,
}

impl InternalFault {
    pub const fn new(code: u32) -> Self {
        Self { code }
    }

    pub const fn code(self) -> u32 {
        self.code
    }
}

/// Artifact-bearing outcomes are disjoint from non-claims by construction.
///
/// Both artifact variants remain untrusted until an independent checker validates
/// them; this enum is a solver result algebra, not an admission authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UntrustedSolverOutcome {
    Sat {
        model: SatModel,
        usage: SolverUsage,
    },
    Unsat {
        proof: UnsatProof,
        usage: SolverUsage,
    },
    Inconclusive {
        reason: InconclusiveReason,
        usage: SolverUsage,
    },
    InternalFault {
        fault: InternalFault,
        usage: SolverUsage,
    },
}

/// Borrowed artifact projection used without weakening the outcome partition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UntrustedArtifactRef<'a> {
    SatModel(&'a SatModel),
    UnsatProof(&'a UnsatProof),
}

impl UntrustedSolverOutcome {
    pub fn usage(&self) -> SolverUsage {
        match self {
            Self::Sat { usage, .. }
            | Self::Unsat { usage, .. }
            | Self::Inconclusive { usage, .. }
            | Self::InternalFault { usage, .. } => *usage,
        }
    }

    pub fn artifact(&self) -> Option<UntrustedArtifactRef<'_>> {
        match self {
            Self::Sat { model, .. } => Some(UntrustedArtifactRef::SatModel(model)),
            Self::Unsat { proof, .. } => Some(UntrustedArtifactRef::UnsatProof(proof)),
            Self::Inconclusive { .. } | Self::InternalFault { .. } => None,
        }
    }
}
