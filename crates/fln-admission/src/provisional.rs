//! Provisional frontier exploration past inconclusive imports
//! (bead `fln-provisional-frontier-vf32`, FL-INV-01 / FL-INV-02 / FL-INV-06 / FL-INV-07).
//!
//! Phase 1 runs the existing authoritative frontier unchanged. Phase 2 re-runs
//! each Phase-1 `inconclusive` root declaration-by-declaration (assuming whole
//! atomic admission units that stop on resource bounds — never partial mutual
//! or inductive blocks) and then checks every `blocked` module whose transitive
//! blocker chain reaches *only* `inconclusive` roots. Modules behind any
//! `failed` or `internal-fault` row stay `blocked` unconditionally.
//!
//! An assumption is never an admission: Phase 2 operates exclusively on
//! [`ProvisionalEnvironment`], never returns assumed declarations in an
//! [`Admitted`] engine, always sets `authority: false` when Phase 2 produced
//! any row, never counts `accepted-under-assumptions` in `accepted`, and never
//! yields exit code 0 unless every module is Phase-1 `accepted`.

use super::*;
use fln_core::outcome::InconclusiveCause;
pub use fln_env::environment::ProvisionalEnvironment;

/// Outcome of checking one atomic declaration unit (a single declaration, or an
/// entire mutual/inductive/quotient block) in declaration-by-declaration mode.
#[derive(Debug)]
pub enum ProvisionalDeclarationVerdict {
    Accepted {
        checker: Option<CheckerAgreement>,
        policy_decision: Option<CheckerSelectionDecision>,
        k1_step_floor: bool,
        k1_steps: u64,
    },
    Assumed {
        reason: Inconclusive,
        k1_steps: u64,
    },
    Failed(OleanCheckError),
    InternalFault(InternalFault),
}

/// Per-unit record for declaration-by-declaration checking, shared with
/// unfold-differential and reject-side consumers.
#[derive(Debug)]
pub struct ProvisionalDeclarationUnit {
    pub names: Vec<Name>,
    pub verdict: ProvisionalDeclarationVerdict,
}

/// One module's verdict in a `--provisional` frontier run.
#[derive(Debug)]
pub enum ProvisionalModuleVerdict {
    /// Accepted in Phase 1 with zero assumptions.
    Accepted { declarations: usize },
    /// Accepted in Phase 2 against one or more assumed inconclusive roots.
    /// Never counted in `accepted`, never authoritative, never yields exit 0.
    AcceptedUnderAssumptions { declarations: usize },
    /// Refused by K1, the independent checker, or artifact/import validation.
    Failed(OleanCheckError),
    /// No verdict was reached (FL-INV-07). On roots re-run declaration by
    /// declaration, `accepted_declarations` of `total_declarations` passed and
    /// `assumed_declaration_names` names the stuck declarations assumed whole.
    Inconclusive {
        reason: Inconclusive,
        accepted_declarations: usize,
        total_declarations: usize,
        assumed_declaration_names: Vec<Name>,
    },
    /// Internal invariant failure.
    InternalFault(InternalFault),
    /// Not checked: blocked behind a `Failed`, `InternalFault`, or un-decodable
    /// module. Preserved as unchecked and never counted as accepted or rejected.
    Blocked { by: Name, reason: &'static str },
}

/// One row of a `--provisional` frontier run.
#[derive(Debug)]
pub struct ProvisionalFrontierRow {
    pub name: Name,
    /// 1 for Phase-1 rows (accepted, failed, internal-fault, ineligible blocked);
    /// 2 for Phase-2 rows (inconclusive roots re-run declaration by declaration,
    /// and eligible blocked modules evaluated under assumptions).
    pub phase: u8,
    pub verdict: ProvisionalModuleVerdict,
    /// Sorted inconclusive root module names in this module's import closure,
    /// derived strictly from the import graph (never from execution order).
    pub assumes: Vec<Name>,
    /// Number of unchecked declarations contributed by `assumes` (for downstream
    /// Phase-2 modules) or assumed within this module itself (for roots).
    pub assumed_declarations: usize,
    /// Total K1 steps consumed while checking this module (0 when not checked).
    pub k1_steps: u64,
    pub elapsed: std::time::Duration,
    pub memory_retry: Option<OleanFrontierMemoryRetry>,
    pub decode_memory_retry: Option<OleanDecodeMemoryRetry>,
    pub memory: OleanFrontierMemoryAttribution,
    pub policy_summary: CheckerPolicySummary,
    pub unit_reports: Vec<ProvisionalDeclarationUnit>,
}

/// Per-root summary combining import-graph dominator unlock value, first-blocker
/// chain count, and declaration-by-declaration results.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvisionalRootSummary {
    pub module: Name,
    /// Import-graph dominator unlock value: number of Phase-1 blocked modules
    /// for which this root lies on every blocked path from the root set.
    pub unlock_value: usize,
    /// Number of Phase-1 blocked modules whose first-blocker chain terminates
    /// at this root (recorded alongside `unlock_value` because first-blocker
    /// over-credits whichever root the planner encountered first).
    pub first_blocker_count: usize,
    pub accepted_declarations: usize,
    pub total_declarations: usize,
    pub assumed_declarations: usize,
    pub assumed_declaration_names: Vec<Name>,
}

/// Conserved verdict totals across a [`ProvisionalFrontier`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProvisionalCounts {
    pub modules: usize,
    pub accepted: usize,
    pub accepted_under_assumptions: usize,
    pub failed: usize,
    pub inconclusive: usize,
    pub internal_fault: usize,
    pub blocked: usize,
    pub accepted_declarations: usize,
    pub accepted_under_assumptions_declarations: usize,
}

impl ProvisionalCounts {
    /// Enforce FL-INV-07 count conservation: every module belongs to exactly one
    /// verdict bucket and `accepted_under_assumptions` is never folded into `accepted`.
    pub fn assert_conservation(&self) {
        let sum = self
            .accepted
            .saturating_add(self.accepted_under_assumptions)
            .saturating_add(self.failed)
            .saturating_add(self.inconclusive)
            .saturating_add(self.internal_fault)
            .saturating_add(self.blocked);
        assert_eq!(
            sum,
            self.modules,
            "provisional frontier count conservation violated: \
             accepted({}) + accepted_under_assumptions({}) + failed({}) + inconclusive({}) \
             + internal_fault({}) + blocked({}) != modules({})",
            self.accepted,
            self.accepted_under_assumptions,
            self.failed,
            self.inconclusive,
            self.internal_fault,
            self.blocked,
            self.modules,
        );
    }
}

/// Combined Phase-1 + Phase-2 result of `fln check-olean --continue --provisional`.
#[derive(Debug)]
pub struct ProvisionalFrontier<E = Admitted> {
    /// Authoritative Phase-1 merged engine holding *only* Phase-1 accepted
    /// modules. No assumed declaration or Phase-2 result ever enters this engine.
    pub phase1_engine: Result<E, OleanCheckError>,
    /// Exact Phase-1 rows as produced before Phase 2.
    pub phase1_rows: Vec<OleanFrontierRow>,
    /// Combined per-module rows in deterministic frontier order.
    pub rows: Vec<ProvisionalFrontierRow>,
    /// True whenever Phase 2 produced at least one row. Forces `authority: false`.
    pub has_phase2_rows: bool,
    /// Exact Phase-1 blocked modules eligible for Phase 2 (blocker chain reaches
    /// only inconclusive roots), in frontier order.
    pub eligible_blocked: Vec<Name>,
    /// Exact Phase-1 blocked modules ineligible for Phase 2 (behind any failed
    /// or internal-fault root), in frontier order.
    pub ineligible_blocked: Vec<Name>,
    /// Per-root dominator unlock values, first-blocker counts, and declaration stats.
    pub roots: Vec<ProvisionalRootSummary>,
    /// Deterministic aggregate plan §8.3c checker-selection summary.
    pub policy_summary: CheckerPolicySummary,
}

impl<E> ProvisionalFrontier<E> {
    pub fn map_engine<F>(self, map: impl FnOnce(E) -> F) -> ProvisionalFrontier<F> {
        ProvisionalFrontier {
            phase1_engine: self.phase1_engine.map(map),
            phase1_rows: self.phase1_rows,
            rows: self.rows,
            has_phase2_rows: self.has_phase2_rows,
            eligible_blocked: self.eligible_blocked,
            ineligible_blocked: self.ineligible_blocked,
            roots: self.roots,
            policy_summary: self.policy_summary,
        }
    }

    pub fn counts(&self) -> ProvisionalCounts {
        let mut counts = ProvisionalCounts {
            modules: self.rows.len(),
            accepted: 0,
            accepted_under_assumptions: 0,
            failed: 0,
            inconclusive: 0,
            internal_fault: 0,
            blocked: 0,
            accepted_declarations: 0,
            accepted_under_assumptions_declarations: 0,
        };
        for row in &self.rows {
            match &row.verdict {
                ProvisionalModuleVerdict::Accepted { declarations } => {
                    counts.accepted += 1;
                    counts.accepted_declarations += *declarations;
                }
                ProvisionalModuleVerdict::AcceptedUnderAssumptions { declarations } => {
                    counts.accepted_under_assumptions += 1;
                    counts.accepted_under_assumptions_declarations += *declarations;
                }
                ProvisionalModuleVerdict::Failed(_) => counts.failed += 1,
                ProvisionalModuleVerdict::Inconclusive { .. } => counts.inconclusive += 1,
                ProvisionalModuleVerdict::InternalFault(_) => counts.internal_fault += 1,
                ProvisionalModuleVerdict::Blocked { .. } => counts.blocked += 1,
            }
        }
        counts.assert_conservation();
        counts
    }

    /// Report authority: strictly `false` whenever Phase 2 produced any row.
    pub fn is_authoritative(&self) -> bool {
        self.policy_summary.attestable && !self.has_phase2_rows
    }

    /// Exit code: 0 only when every module is Phase-1 `accepted` with zero Phase-2 rows.
    pub fn exit_code(&self) -> u8 {
        let counts = self.counts();
        if counts.internal_fault > 0 {
            4
        } else if counts.failed > 0 || counts.blocked > 0 {
            1
        } else if counts.inconclusive > 0
            || counts.accepted_under_assumptions > 0
            || self.has_phase2_rows
        {
            3
        } else {
            0
        }
    }
}

/// Result of checking one decoded module declaration by declaration against a
/// [`ProvisionalEnvironment`].
#[derive(Debug)]
pub struct PerDeclarationModuleCheck {
    pub verdict: PerDeclarationModuleOutcome,
    pub entries: Vec<(EnvironmentEntry, bool)>,
    pub final_env: Option<ProvisionalEnvironment>,
    pub accepted_declarations: usize,
    pub total_declarations: usize,
    pub assumed_declaration_names: Vec<Name>,
    pub k1_steps: u64,
    pub checker_bytes: u64,
    pub policy_summary: CheckerPolicySummary,
    pub unit_reports: Vec<ProvisionalDeclarationUnit>,
}

/// Terminal outcome of [`check_decoded_olean_per_declaration`].
#[derive(Debug)]
pub enum PerDeclarationModuleOutcome {
    /// Every declaration unit was accepted without assuming any unit in this module.
    AllAccepted,
    /// At least one declaration unit hit a resource stop and was assumed whole;
    /// every remaining unit either passed or was assumed whole.
    PartialAssumed(Inconclusive),
    /// A declaration unit was rejected or disagreed between K1 and the checker.
    Failed(OleanCheckError),
    /// An internal invariant fault stopped the check.
    InternalFault(InternalFault),
}

/// Compute exact import-graph dominator unlock values and first-blocker chain
/// counts for every non-accepted root over the Phase-1 blocked subgraph.
///
/// A root `r` dominates a blocked module `b` iff `r` lies on *every* path from
/// the non-accepted root set to `b` in the blocked import DAG. Pure function of
/// the import graph and Phase-1 statuses; schedule-independent by construction.
pub fn compute_root_dominators(
    order: &[usize],
    dependencies: &[BTreeSet<usize>],
    is_accepted: &[bool],
    is_blocked: &[bool],
    first_blocker: &[Option<usize>],
) -> (BTreeMap<usize, usize>, BTreeMap<usize, usize>) {
    let count = order.len();
    let mut dom: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); count];
    let mut is_root = vec![false; count];
    for &index in order {
        if is_accepted[index] {
            continue;
        }
        if !is_blocked[index] {
            is_root[index] = true;
            dom[index].insert(index);
            continue;
        }
        let mut non_accepted_preds = dependencies[index]
            .iter()
            .copied()
            .filter(|&dep| !is_accepted[dep]);
        let mut intersection = match non_accepted_preds.next() {
            Some(first) => dom[first].clone(),
            None => BTreeSet::new(),
        };
        for pred in non_accepted_preds {
            intersection.retain(|node| dom[pred].contains(node));
        }
        intersection.insert(index);
        dom[index] = intersection;
    }

    let mut unlock_value: BTreeMap<usize, usize> = BTreeMap::new();
    let mut first_blocker_count: BTreeMap<usize, usize> = BTreeMap::new();
    for &index in order {
        if is_root[index] {
            unlock_value.entry(index).or_insert(0);
            first_blocker_count.entry(index).or_insert(0);
        }
    }
    for &index in order {
        if !is_blocked[index] {
            continue;
        }
        for &dominator in &dom[index] {
            if is_root[dominator] {
                *unlock_value.entry(dominator).or_insert(0) += 1;
            }
        }
        // Trace the first-blocker pointer chain to its non-blocked root.
        let mut cursor = first_blocker[index];
        let mut hops = 0_usize;
        while let Some(node) = cursor {
            if hops >= count {
                break;
            }
            hops += 1;
            if !is_blocked[node] {
                if is_root[node] {
                    *first_blocker_count.entry(node).or_insert(0) += 1;
                }
                break;
            }
            cursor = first_blocker[node];
        }
    }
    (unlock_value, first_blocker_count)
}

/// Partition Phase-1 `Blocked` modules into `(eligible, ineligible, blocking_roots)`
/// purely from the import graph and Phase-1 verdicts.
///
/// A blocked module is eligible iff its transitive non-accepted root set is
/// non-empty and consists *exclusively* of `OleanModuleVerdict::Inconclusive`
/// roots (never `Failed` or `InternalFault`).
pub fn classify_blocked_eligibility(
    order: &[usize],
    dependencies: &[BTreeSet<usize>],
    phase1_verdicts: &[&OleanModuleVerdict],
) -> (Vec<usize>, Vec<usize>, Vec<BTreeSet<usize>>) {
    let count = order.len();
    let mut blocking_roots: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); count];
    let mut eligible = Vec::new();
    let mut ineligible = Vec::new();
    for &index in order {
        match phase1_verdicts[index] {
            OleanModuleVerdict::Accepted { .. } => {}
            OleanModuleVerdict::Blocked { .. } => {
                let mut roots = BTreeSet::new();
                for &dep in &dependencies[index] {
                    roots.extend(blocking_roots[dep].iter().copied());
                }
                let all_inconclusive = !roots.is_empty()
                    && roots.iter().all(|&root| {
                        matches!(phase1_verdicts[root], OleanModuleVerdict::Inconclusive(_))
                    });
                blocking_roots[index] = roots;
                if all_inconclusive {
                    eligible.push(index);
                } else {
                    ineligible.push(index);
                }
            }
            // Non-accepted, non-blocked root (Failed, Inconclusive, InternalFault).
            _ => {
                blocking_roots[index].insert(index);
            }
        }
    }
    (eligible, ineligible, blocking_roots)
}

fn inconclusive_steps(reason: &Inconclusive) -> u64 {
    match &reason.cause {
        InconclusiveCause::ResourceExhausted { usage } => usage.observed,
        _ => 0,
    }
}

enum UnitCheckOutcome {
    Accepted {
        environment: Environment,
        checker_environment: Option<CheckerConstantEnvironment>,
        checker: Option<CheckerAgreement>,
        policy_decision: CheckerSelectionDecision,
        k1_step_floor: bool,
        k1_steps: u64,
    },
    Inconclusive {
        reason: Inconclusive,
        k1_steps: u64,
    },
    Failed(EngineAdmissionError),
    InternalFault(InternalFault),
}

fn check_unit_against_environment(
    environment: &Environment,
    retained_checker_env: Option<&CheckerConstantEnvironment>,
    declaration: Declaration,
    limits: EngineAdmissionLimits,
    reading: ReadingCheck<'_>,
    retained_checker_bytes: &mut u64,
    transient_checker_bytes: &mut u64,
) -> UnitCheckOutcome {
    if !matches!(
        declaration,
        Declaration::Axiom(_)
            | Declaration::Defn(_)
            | Declaration::Thm(_)
            | Declaration::Opaque(_)
            | Declaration::Mutual(_)
            | Declaration::Inductive(_)
            | Declaration::Quotient(_)
    ) {
        return UnitCheckOutcome::Failed(EngineAdmissionError::UnsupportedDeclaration {
            kind: declaration_kind(&declaration),
        });
    }

    let admitted = match admit(environment, declaration.clone(), limits.kernel) {
        Outcome::Complete(admitted) => admitted,
        Outcome::Inconclusive(reason) => {
            let k1_steps = inconclusive_steps(&reason);
            return UnitCheckOutcome::Inconclusive { reason, k1_steps };
        }
        Outcome::InternalFault(fault) => return UnitCheckOutcome::InternalFault(fault),
    };
    let k1_steps_used = match &admitted {
        fln_kernel::capability::Admitted::Accepted(reviewable) => {
            reviewable.consumption().steps_used
        }
        fln_kernel::capability::Admitted::Rejected { .. } => {
            return match convene(&Council::nobody_was_asked(), admitted) {
                CouncilOutcome::KernelRejected { class, message, .. } => {
                    UnitCheckOutcome::Failed(EngineAdmissionError::KernelRejected {
                        class,
                        message,
                    })
                }
                _ => UnitCheckOutcome::Failed(EngineAdmissionError::CheckerBridge {
                    detail: "rejected kernel verdict did not produce KernelRejected".to_owned(),
                }),
            };
        }
    };

    let (selected, sampled_decision, k1_step_floor) = match limits.policy {
        VerificationPolicy::Release | VerificationPolicy::Paranoid => (true, None, false),
        VerificationPolicy::Standard | VerificationPolicy::CompatBench => {
            let content = declaration_content_digest(&declaration);
            let risks = classify_declaration_risks(&declaration);
            let mut decision = CheckerPolicyV1.decide(limits.policy, content, risks);
            let k1_step_floor = k1_steps_used > limits.high_risk_k1_steps;
            if k1_step_floor && !decision.selected {
                decision.selected = true;
                decision.reason = CheckerSelectionReason::HighRiskFloor;
            }
            (decision.selected, Some(decision), k1_step_floor)
        }
    };

    let (checked, checker, checker_environment) = if selected {
        let checker_review = review_with_independent_checker(
            environment,
            retained_checker_env,
            &declaration,
            limits.checker,
            reading,
        );
        *retained_checker_bytes =
            retained_checker_bytes.saturating_add(checker_review.retained_delta_bytes);
        *transient_checker_bytes = (*transient_checker_bytes).max(checker_review.candidate_bytes);
        let council = if limits.policy == VerificationPolicy::Paranoid {
            let mut seats = checker_review.council.seats().to_vec();
            seats.push(Seat::new(
                "paranoid-second-witness",
                SeatOrigin::FrankenLeanEngine,
                SeatBounds::not_established(
                    "paranoid policy requires a second kernel lane (K2) or external witness",
                ),
                SeatVerdict::NoAnswer {
                    reason: PARANOID_WITNESS_UNAVAILABLE_REASON.to_owned(),
                },
            ));
            Council::of(seats)
        } else {
            checker_review.council
        };
        let checked = match convene(&council, admitted) {
            CouncilOutcome::Agreed(checked) => checked,
            CouncilOutcome::KernelRejected { class, message, .. } => {
                return UnitCheckOutcome::Failed(EngineAdmissionError::KernelRejected {
                    class,
                    message,
                });
            }
            CouncilOutcome::Halted(halt) if halt.is_purely_resource() => {
                return UnitCheckOutcome::Inconclusive {
                    reason: Inconclusive::authority_incomplete(halt.summary()),
                    k1_steps: k1_steps_used,
                };
            }
            CouncilOutcome::Halted(halt) => {
                return UnitCheckOutcome::Failed(EngineAdmissionError::CouncilHalted {
                    summary: halt.summary(),
                });
            }
        };
        let Some(checker) = checker_review.agreement else {
            return UnitCheckOutcome::Failed(EngineAdmissionError::CheckerBridge {
                detail: "the checker council agreed without an admission record".to_owned(),
            });
        };
        let Some(checker_environment) = checker_review.successor_environment else {
            return UnitCheckOutcome::Failed(EngineAdmissionError::CheckerBridge {
                detail: "the checker council agreed without a retained successor environment"
                    .to_owned(),
            });
        };
        (checked, Some(checker), Some(checker_environment))
    } else {
        let checked = match convene(&Council::nobody_was_asked(), admitted) {
            CouncilOutcome::Agreed(checked) => checked,
            CouncilOutcome::KernelRejected { class, message, .. } => {
                return UnitCheckOutcome::Failed(EngineAdmissionError::KernelRejected {
                    class,
                    message,
                });
            }
            CouncilOutcome::Halted(halt) => {
                return UnitCheckOutcome::Inconclusive {
                    reason: Inconclusive::authority_incomplete(halt.summary()),
                    k1_steps: k1_steps_used,
                };
            }
        };
        (checked, None, retained_checker_env.cloned())
    };

    let expects_block = matches!(
        declaration,
        Declaration::Mutual(_) | Declaration::Inductive(_) | Declaration::Quotient(_)
    );
    let next_environment = match checked.publish(limits.declaration, limits.collisions, None) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(publication))) => {
            if expects_block {
                return UnitCheckOutcome::Failed(EngineAdmissionError::UnexpectedPublication {
                    detail: "a block declaration published as one constant",
                });
            }
            publication.environment
        }
        Outcome::Complete(Published::Committed(DeclarationCommitted::DuplicateName { name }))
        | Outcome::Complete(Published::DuplicateName { name }) => {
            return UnitCheckOutcome::Failed(EngineAdmissionError::DuplicateName { name });
        }
        Outcome::Complete(Published::BlockCommitted(publication)) => {
            if !expects_block {
                return UnitCheckOutcome::Failed(EngineAdmissionError::UnexpectedPublication {
                    detail: "a non-block declaration published as a block",
                });
            }
            publication.environment
        }
        Outcome::Inconclusive(reason) => {
            return UnitCheckOutcome::Inconclusive {
                reason,
                k1_steps: k1_steps_used,
            };
        }
        Outcome::InternalFault(fault) => return UnitCheckOutcome::InternalFault(fault),
    };

    let policy_decision = match sampled_decision {
        Some(decision) => decision,
        None => CheckerPolicyV1.decide(
            limits.policy,
            published_declaration_content_digest(&next_environment, &declaration),
            CheckerRiskProfile::none(),
        ),
    };

    UnitCheckOutcome::Accepted {
        environment: next_environment,
        checker_environment,
        checker,
        policy_decision,
        k1_step_floor,
        k1_steps: k1_steps_used,
    }
}

fn extend_checker_with_assumed(
    retained: Option<CheckerConstantEnvironment>,
    constants: &[ConstantInfo],
    limits: CheckerExecutionLimits,
) -> Option<CheckerConstantEnvironment> {
    let mut env = retained?;
    for info in constants {
        let Ok(entry) = checker_entry(info, limits.decode) else {
            return None;
        };
        match env.extend(entry, limits.environment) {
            CheckerEnvironmentOutcome::Complete { environment, .. } => env = environment,
            _ => return None,
        }
    }
    Some(env)
}

/// Check a decoded module declaration unit by declaration unit against a
/// [`ProvisionalEnvironment`].
///
/// When `assume_inconclusive_units` is true, any unit that hits an `Inconclusive`
/// stop (e.g., K1 step budget or checker resource bound) is inserted *whole*
/// (mutual definition blocks and inductive blocks with types, constructors, and
/// recursors together) as provisional assumptions so the remaining declarations
/// of the module are still checked. Any `Failed` or `InternalFault` unit stops
/// immediately and is never assumed.
pub fn check_decoded_olean_per_declaration(
    base: &ProvisionalEnvironment,
    decoded: &DecodedOlean,
    limits: OleanCheckLimits,
    assume_inconclusive_units: bool,
) -> Result<PerDeclarationModuleCheck, OleanCheckError> {
    let plan = plan_olean_declarations(base.as_check_environment(), &decoded.constants, limits)?;
    let readings = match ArtifactReadings::new(&decoded.independent) {
        Ok(readings) => readings,
        Err(error) => {
            let reason = match error.into_nonanswer::<()>() {
                Ok(Outcome::Inconclusive(reason)) => reason,
                Ok(Outcome::InternalFault(fault)) => {
                    return Ok(PerDeclarationModuleCheck {
                        verdict: PerDeclarationModuleOutcome::InternalFault(fault),
                        entries: Vec::new(),
                        final_env: None,
                        accepted_declarations: 0,
                        total_declarations: decoded.constants.len(),
                        assumed_declaration_names: Vec::new(),
                        k1_steps: 0,
                        checker_bytes: 0,
                        policy_summary: CheckerPolicySummary::empty(limits.admission.policy),
                        unit_reports: Vec::new(),
                    });
                }
                Err(err) => return Err(err),
                Ok(Outcome::Complete(())) => Inconclusive::authority_incomplete(
                    "independent artifact reading returned no answer",
                ),
            };
            return Ok(PerDeclarationModuleCheck {
                verdict: PerDeclarationModuleOutcome::PartialAssumed(reason),
                entries: Vec::new(),
                final_env: None,
                accepted_declarations: 0,
                total_declarations: decoded.constants.len(),
                assumed_declaration_names: Vec::new(),
                k1_steps: 0,
                checker_bytes: 0,
                policy_summary: CheckerPolicySummary::empty(limits.admission.policy),
                unit_reports: Vec::new(),
            });
        }
    };
    let by_name: BTreeMap<&Name, &ConstantInfo> = decoded
        .constants
        .iter()
        .map(|info| (info.name(), info))
        .collect();
    for (name, _) in &plan.already_present {
        let Some(info) = by_name.get(name) else {
            return Err(OleanCheckError::InternalInvariant {
                detail: "an already-present declaration is not in the decoded table",
            });
        };
        if let Some(objection) = readings.objection(info, limits.admission.checker.decode)
            && let Err(error) = unreviewed_reading_refusal::<()>(name, objection)
        {
            return Ok(PerDeclarationModuleCheck {
                verdict: PerDeclarationModuleOutcome::Failed(error),
                entries: Vec::new(),
                final_env: None,
                accepted_declarations: 0,
                total_declarations: decoded.constants.len(),
                assumed_declaration_names: Vec::new(),
                k1_steps: 0,
                checker_bytes: 0,
                policy_summary: CheckerPolicySummary::empty(limits.admission.policy),
                unit_reports: Vec::new(),
            });
        }
    }

    let reading = ReadingCheck::Artifact(&readings);
    let mut env = base.clone();
    let mut checker_env: Option<CheckerConstantEnvironment> = None;
    let mut retained_checker_bytes = 0_u64;
    let mut transient_checker_bytes = 0_u64;
    let mut k1_steps_total = 0_u64;
    let mut accepted_declarations = plan.already_present.len();
    let mut checked_rows: Vec<OleanCheckedDeclaration> = plan
        .already_present
        .iter()
        .map(|(name, checker)| OleanCheckedDeclaration {
            name: name.clone(),
            checker: Some(*checker),
            policy_decision: None,
            k1_step_floor: false,
        })
        .collect();
    let mut assumed_names: BTreeSet<Name> = BTreeSet::new();
    let mut first_inconclusive: Option<Inconclusive> = None;
    let mut unit_reports = Vec::with_capacity(plan.order.len());

    for &unit_index in &plan.order {
        let Some(unit) = plan.units.get(unit_index) else {
            return Err(OleanCheckError::InternalInvariant {
                detail: "planned declaration unit is outside the unit table",
            });
        };
        match check_unit_against_environment(
            env.as_check_environment(),
            checker_env.as_ref(),
            unit.declaration.clone(),
            limits.admission,
            reading,
            &mut retained_checker_bytes,
            &mut transient_checker_bytes,
        ) {
            UnitCheckOutcome::Accepted {
                environment: next_env,
                checker_environment: next_checker,
                checker,
                policy_decision,
                k1_step_floor,
                k1_steps,
            } => {
                k1_steps_total = k1_steps_total.saturating_add(k1_steps);
                env = env.with_checked_successor(next_env).map_err(|_| {
                    OleanCheckError::InternalInvariant {
                        detail: "checked successor could not preserve provisional assumptions",
                    }
                })?;
                checker_env = next_checker;
                accepted_declarations += unit.names.len();
                for name in &unit.names {
                    checked_rows.push(OleanCheckedDeclaration {
                        name: name.clone(),
                        checker,
                        policy_decision: Some(policy_decision),
                        k1_step_floor,
                    });
                }
                unit_reports.push(ProvisionalDeclarationUnit {
                    names: unit.names.clone(),
                    verdict: ProvisionalDeclarationVerdict::Accepted {
                        checker,
                        policy_decision: Some(policy_decision),
                        k1_step_floor,
                        k1_steps,
                    },
                });
            }
            UnitCheckOutcome::Inconclusive { reason, k1_steps } => {
                k1_steps_total = k1_steps_total.saturating_add(k1_steps);
                if !assume_inconclusive_units {
                    unit_reports.push(ProvisionalDeclarationUnit {
                        names: unit.names.clone(),
                        verdict: ProvisionalDeclarationVerdict::Assumed {
                            reason: reason.clone(),
                            k1_steps,
                        },
                    });
                    return Ok(PerDeclarationModuleCheck {
                        verdict: PerDeclarationModuleOutcome::PartialAssumed(reason),
                        entries: Vec::new(),
                        final_env: None,
                        accepted_declarations,
                        total_declarations: decoded.constants.len(),
                        assumed_declaration_names: Vec::new(),
                        k1_steps: k1_steps_total,
                        checker_bytes: retained_checker_bytes
                            .saturating_add(transient_checker_bytes),
                        policy_summary: CheckerPolicySummary::from_declarations(
                            limits.admission.policy,
                            &checked_rows,
                        ),
                        unit_reports,
                    });
                }
                // Assume the ENTIRE atomic unit (mutual block or inductive block whole).
                let mut unit_constants = Vec::with_capacity(unit.names.len());
                for name in &unit.names {
                    let Some(info) = by_name.get(name) else {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "unit declaration name missing from decoded constant table",
                        });
                    };
                    unit_constants.push((*info).clone());
                }
                env = env.assume_constants(&unit_constants).map_err(|error| {
                    OleanCheckError::Admission(EngineAdmissionError::DuplicateName {
                        name: match error {
                            fln_env::environment::EnvError::DuplicateDeclaration { name } => name,
                            _ => unit.names[0].clone(),
                        },
                    })
                })?;
                checker_env = extend_checker_with_assumed(
                    checker_env,
                    &unit_constants,
                    limits.admission.checker,
                );
                for name in &unit.names {
                    assumed_names.insert(name.clone());
                }
                if first_inconclusive.is_none() {
                    first_inconclusive = Some(reason.clone());
                }
                unit_reports.push(ProvisionalDeclarationUnit {
                    names: unit.names.clone(),
                    verdict: ProvisionalDeclarationVerdict::Assumed { reason, k1_steps },
                });
            }
            UnitCheckOutcome::Failed(error) => {
                let err = OleanCheckError::Admission(error);
                unit_reports.push(ProvisionalDeclarationUnit {
                    names: unit.names.clone(),
                    verdict: ProvisionalDeclarationVerdict::Failed(err.clone()),
                });
                return Ok(PerDeclarationModuleCheck {
                    verdict: PerDeclarationModuleOutcome::Failed(err),
                    entries: Vec::new(),
                    final_env: None,
                    accepted_declarations,
                    total_declarations: decoded.constants.len(),
                    assumed_declaration_names: assumed_names.into_iter().collect(),
                    k1_steps: k1_steps_total,
                    checker_bytes: retained_checker_bytes.saturating_add(transient_checker_bytes),
                    policy_summary: CheckerPolicySummary::from_declarations(
                        limits.admission.policy,
                        &checked_rows,
                    ),
                    unit_reports,
                });
            }
            UnitCheckOutcome::InternalFault(fault) => {
                unit_reports.push(ProvisionalDeclarationUnit {
                    names: unit.names.clone(),
                    verdict: ProvisionalDeclarationVerdict::InternalFault(fault.clone()),
                });
                return Ok(PerDeclarationModuleCheck {
                    verdict: PerDeclarationModuleOutcome::InternalFault(fault),
                    entries: Vec::new(),
                    final_env: None,
                    accepted_declarations,
                    total_declarations: decoded.constants.len(),
                    assumed_declaration_names: assumed_names.into_iter().collect(),
                    k1_steps: k1_steps_total,
                    checker_bytes: retained_checker_bytes.saturating_add(transient_checker_bytes),
                    policy_summary: CheckerPolicySummary::from_declarations(
                        limits.admission.policy,
                        &checked_rows,
                    ),
                    unit_reports,
                });
            }
        }
    }

    // Recheck subsumed repeats against the provisional environment.
    for repeat in plan.subsumed {
        let name = repeat.name().clone();
        let objection = readings.objection(&repeat, limits.admission.checker.decode);
        match repeat {
            ConstantInfo::Thm(mut theorem) => {
                let mut scratch = Name::str(name.clone(), "_fln_subsumed_repeat");
                let mut suffix = 0_u64;
                while env.contains(&scratch) {
                    suffix += 1;
                    scratch = Name::num(Name::str(name.clone(), "_fln_subsumed_repeat"), suffix);
                }
                theorem.base.name = scratch.clone();
                for member in &mut theorem.all {
                    if *member == name {
                        *member = scratch.clone();
                    }
                }
                let repeat_reading = ReadingCheck::Settled(objection.as_ref());
                let mut repeat_retained = 0_u64;
                let mut repeat_transient = 0_u64;
                match check_unit_against_environment(
                    env.as_check_environment(),
                    checker_env.as_ref(),
                    Declaration::Thm(theorem),
                    limits.admission,
                    repeat_reading,
                    &mut repeat_retained,
                    &mut repeat_transient,
                ) {
                    UnitCheckOutcome::Accepted {
                        checker,
                        policy_decision,
                        k1_step_floor,
                        k1_steps,
                        ..
                    } => {
                        k1_steps_total = k1_steps_total.saturating_add(k1_steps);
                        accepted_declarations += 1;
                        checked_rows.push(OleanCheckedDeclaration {
                            name,
                            checker,
                            policy_decision: Some(policy_decision),
                            k1_step_floor,
                        });
                    }
                    UnitCheckOutcome::Inconclusive { reason, k1_steps } => {
                        k1_steps_total = k1_steps_total.saturating_add(k1_steps);
                        if first_inconclusive.is_none() {
                            first_inconclusive = Some(reason);
                        }
                        assumed_names.insert(name);
                    }
                    UnitCheckOutcome::Failed(error) => {
                        return Ok(PerDeclarationModuleCheck {
                            verdict: PerDeclarationModuleOutcome::Failed(
                                OleanCheckError::Admission(error),
                            ),
                            entries: Vec::new(),
                            final_env: None,
                            accepted_declarations,
                            total_declarations: decoded.constants.len(),
                            assumed_declaration_names: assumed_names.into_iter().collect(),
                            k1_steps: k1_steps_total,
                            checker_bytes: retained_checker_bytes
                                .saturating_add(transient_checker_bytes),
                            policy_summary: CheckerPolicySummary::from_declarations(
                                limits.admission.policy,
                                &checked_rows,
                            ),
                            unit_reports,
                        });
                    }
                    UnitCheckOutcome::InternalFault(fault) => {
                        return Ok(PerDeclarationModuleCheck {
                            verdict: PerDeclarationModuleOutcome::InternalFault(fault),
                            entries: Vec::new(),
                            final_env: None,
                            accepted_declarations,
                            total_declarations: decoded.constants.len(),
                            assumed_declaration_names: assumed_names.into_iter().collect(),
                            k1_steps: k1_steps_total,
                            checker_bytes: retained_checker_bytes
                                .saturating_add(transient_checker_bytes),
                            policy_summary: CheckerPolicySummary::from_declarations(
                                limits.admission.policy,
                                &checked_rows,
                            ),
                            unit_reports,
                        });
                    }
                }
            }
            ConstantInfo::Axiom(_) => {
                if let Some(objection) = objection
                    && let Err(error) = unreviewed_reading_refusal::<()>(&name, objection)
                {
                    return Ok(PerDeclarationModuleCheck {
                        verdict: PerDeclarationModuleOutcome::Failed(error),
                        entries: Vec::new(),
                        final_env: None,
                        accepted_declarations,
                        total_declarations: decoded.constants.len(),
                        assumed_declaration_names: assumed_names.into_iter().collect(),
                        k1_steps: k1_steps_total,
                        checker_bytes: retained_checker_bytes
                            .saturating_add(transient_checker_bytes),
                        policy_summary: CheckerPolicySummary::from_declarations(
                            limits.admission.policy,
                            &checked_rows,
                        ),
                        unit_reports,
                    });
                }
                accepted_declarations += 1;
                checked_rows.push(OleanCheckedDeclaration {
                    name,
                    checker: Some(CheckerAgreement {
                        schema: "fln-checker/v1",
                        ground: CheckerAdmissionGround::AxiomPreamble,
                    }),
                    policy_decision: None,
                    k1_step_floor: false,
                });
            }
            _ => {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "only theorems and axioms can subsume an admitted repeat",
                });
            }
        }
    }

    if !assumed_names.is_empty() {
        env = env.mark_assumed_batch(assumed_names.clone());
    }
    let entries: Vec<(EnvironmentEntry, bool)> = decoded
        .constants
        .iter()
        .filter(|info| !base.contains(info.name()))
        .filter_map(|info| {
            let entry = env.entry(info.name())?;
            let is_assumed = assumed_names.contains(info.name());
            Some((entry, is_assumed))
        })
        .collect();
    let assumed_declaration_names: Vec<Name> = assumed_names.into_iter().collect();
    let verdict = match first_inconclusive {
        Some(reason) => PerDeclarationModuleOutcome::PartialAssumed(reason),
        None => PerDeclarationModuleOutcome::AllAccepted,
    };
    Ok(PerDeclarationModuleCheck {
        verdict,
        entries,
        final_env: Some(env),
        accepted_declarations,
        total_declarations: decoded.constants.len(),
        assumed_declaration_names,
        k1_steps: k1_steps_total,
        checker_bytes: retained_checker_bytes.saturating_add(transient_checker_bytes),
        policy_summary: CheckerPolicySummary::from_declarations(
            limits.admission.policy,
            &checked_rows,
        ),
        unit_reports,
    })
}

/// Phase-2 payload retained only in-process for checking downstream eligible
/// modules. Never exported into an `Admitted` engine, `.olean`, or cache record.
struct Phase2ModulePayload {
    position: usize,
    entries: Vec<(EnvironmentEntry, bool)>,
}

struct Phase2Work {
    index: usize,
    is_phase1_root: bool,
    phase1_reason: Option<Inconclusive>,
    phase1_memory_retry: Option<OleanFrontierMemoryRetry>,
    phase1_decode_retry: Option<OleanDecodeMemoryRetry>,
    estimated_bytes: u64,
    base_provisional: Option<std::sync::Arc<ProvisionalEnvironment>>,
    assumes: Vec<Name>,
    phase1_accepted_closure: Vec<std::sync::Arc<FrontierAccepted>>,
    phase2_closure: Vec<std::sync::Arc<Phase2ModulePayload>>,
    retain_final_env: bool,
    retain_payload_entries: bool,
}

struct Phase2Done {
    index: usize,
    host_memory_refusal: bool,
    usable: bool,
    contributes_assumptions: bool,
    row: ProvisionalFrontierRow,
    payload: Option<Phase2ModulePayload>,
    final_env: Option<ProvisionalEnvironment>,
}

fn assemble_provisional_environment(
    base: &Environment,
    base_provisional: Option<&ProvisionalEnvironment>,
    phase1_closure: &[std::sync::Arc<FrontierAccepted>],
    phase2_closure: &[std::sync::Arc<Phase2ModulePayload>],
) -> Result<(ProvisionalEnvironment, usize), OleanCheckError> {
    enum ClosureItem<'a> {
        Phase1(&'a FrontierAccepted),
        Phase2(&'a Phase2ModulePayload),
    }
    let mut ordered: Vec<(usize, ClosureItem<'_>)> =
        Vec::with_capacity(phase1_closure.len() + phase2_closure.len());
    for module in phase1_closure {
        ordered.push((module.position, ClosureItem::Phase1(module)));
    }
    for module in phase2_closure {
        ordered.push((module.position, ClosureItem::Phase2(module)));
    }
    ordered.sort_by_key(|(pos, _)| *pos);

    let mut env = match base_provisional {
        Some(existing) => existing.clone(),
        None => ProvisionalEnvironment::from_admitted(base.clone()),
    };
    let mut assumed_to_mark: BTreeSet<Name> = BTreeSet::new();
    let mut merge_one =
        |entry: &EnvironmentEntry, is_assumed: bool| -> Result<(), OleanCheckError> {
            let name = entry.declaration().name();
            if let Some(present) = env.as_check_environment().entry(name) {
                if present.digest() != entry.digest() {
                    let lookup = |n: &Name| env.as_check_environment().find(n);
                    if !crate::olean_imports::subsumes_info(
                        &lookup,
                        present.declaration(),
                        entry.declaration(),
                    ) && !crate::olean_imports::subsumes_info(
                        &lookup,
                        entry.declaration(),
                        present.declaration(),
                    ) {
                        return Err(OleanCheckError::DuplicateDeclaration { name: name.clone() });
                    }
                }
            } else {
                env = env
                    .merge_entry(entry.clone(), false)
                    .map_err(|_| OleanCheckError::DuplicateDeclaration { name: name.clone() })?;
            }
            if is_assumed {
                assumed_to_mark.insert(name.clone());
            }
            Ok(())
        };
    for (_, item) in ordered {
        match item {
            ClosureItem::Phase1(module) => {
                for entry in &module.admitted {
                    merge_one(entry, false)?;
                }
            }
            ClosureItem::Phase2(module) => {
                for (entry, is_assumed) in &module.entries {
                    merge_one(entry, *is_assumed)?;
                }
            }
        }
    }
    if !assumed_to_mark.is_empty() {
        env = env.mark_assumed_batch(assumed_to_mark);
    }
    let assumed_count = env.assumed_count();
    Ok((env, assumed_count))
}

fn phase2_error_verdict(error: OleanCheckError) -> ProvisionalModuleVerdict {
    match frontier_error_verdict(error) {
        OleanModuleVerdict::Inconclusive(reason) => ProvisionalModuleVerdict::Inconclusive {
            reason,
            accepted_declarations: 0,
            total_declarations: 0,
            assumed_declaration_names: Vec::new(),
        },
        OleanModuleVerdict::InternalFault(fault) => ProvisionalModuleVerdict::InternalFault(fault),
        OleanModuleVerdict::Failed(err) => ProvisionalModuleVerdict::Failed(err),
        _ => ProvisionalModuleVerdict::InternalFault(InternalFault::new(
            "FL-INV-07",
            "provisional error mapped to unexpected verdict",
        )),
    }
}

/// Guard a Phase-2 worker check against panics and `HostAllocationFailure`
/// unwinds (`fln-frontier-oom-abort-w9dx`), converting any unwind into a typed
/// `Phase2Done` so the worker thread never dies and the scheduler never stalls.
fn phase2_guarded(
    base: &Environment,
    module_name: &Name,
    mut work: Phase2Work,
    limits: OleanCheckLimits,
    decode: &(dyn Fn(usize) -> Result<DecodedOlean, OleanCheckError> + Sync),
) -> Phase2Done {
    let started = std::time::Instant::now();
    let index = work.index;
    let estimated_bytes = work.estimated_bytes;
    // This is reporting metadata; checking uses the provisional environment.
    // Keep it outside the unwind boundary without cloning: cloning here could
    // itself exhaust memory before the worker's guard was active.
    let assumes = std::mem::take(&mut work.assumes);
    let policy = limits.admission.policy;
    let mut done = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run_phase2_module(base, module_name, work, limits, decode)
    }))
    .unwrap_or_else(|payload| {
        let error = frontier_unwound(payload);
        let host_memory_refusal = olean_host_memory_refusal(&error);
        Phase2Done {
            index,
            host_memory_refusal,
            usable: false,
            contributes_assumptions: false,
            row: ProvisionalFrontierRow {
                name: module_name.clone(),
                phase: 2,
                verdict: phase2_error_verdict(error),
                assumes: Vec::new(),
                assumed_declarations: 0,
                k1_steps: 0,
                elapsed: started.elapsed(),
                memory_retry: None,
                decode_memory_retry: None,
                memory: OleanFrontierMemoryAttribution::from_components(
                    estimated_bytes,
                    0,
                    0,
                    0,
                    0,
                    0,
                ),
                policy_summary: CheckerPolicySummary::empty(policy),
                unit_reports: Vec::new(),
            },
            payload: None,
            final_env: None,
        }
    });
    done.row.assumes = assumes;
    done
}

fn run_phase2_module(
    base: &Environment,
    module_name: &Name,
    work: Phase2Work,
    limits: OleanCheckLimits,
    decode: &(dyn Fn(usize) -> Result<DecodedOlean, OleanCheckError> + Sync),
) -> Phase2Done {
    let started = std::time::Instant::now();
    let index = work.index;
    let empty_policy = CheckerPolicySummary::empty(limits.admission.policy);
    let assumes = work.assumes;

    let (provisional_env, closure_assumed_count) = match assemble_provisional_environment(
        base,
        work.base_provisional.as_deref(),
        &work.phase1_accepted_closure,
        &work.phase2_closure,
    ) {
        Ok(assembled) => assembled,
        Err(error) => {
            let host_memory_refusal = olean_host_memory_refusal(&error);
            return Phase2Done {
                index,
                host_memory_refusal,
                usable: false,
                contributes_assumptions: false,
                row: ProvisionalFrontierRow {
                    name: module_name.clone(),
                    phase: 2,
                    verdict: phase2_error_verdict(error),
                    assumes,
                    assumed_declarations: 0,
                    k1_steps: 0,
                    elapsed: started.elapsed(),
                    memory_retry: work.phase1_memory_retry,
                    decode_memory_retry: work.phase1_decode_retry,
                    memory: OleanFrontierMemoryAttribution::from_components(
                        work.estimated_bytes,
                        0,
                        0,
                        0,
                        0,
                        0,
                    ),
                    policy_summary: empty_policy,
                    unit_reports: Vec::new(),
                },
                payload: None,
                final_env: None,
            };
        }
    };

    let decoded = match decode(index) {
        Ok(decoded) => decoded,
        Err(error) => {
            let host_memory_refusal = olean_host_memory_refusal(&error);
            return Phase2Done {
                index,
                host_memory_refusal,
                usable: false,
                contributes_assumptions: false,
                row: ProvisionalFrontierRow {
                    name: module_name.clone(),
                    phase: 2,
                    verdict: phase2_error_verdict(error),
                    assumes,
                    assumed_declarations: closure_assumed_count,
                    k1_steps: 0,
                    elapsed: started.elapsed(),
                    memory_retry: work.phase1_memory_retry,
                    decode_memory_retry: work.phase1_decode_retry,
                    memory: OleanFrontierMemoryAttribution::from_components(
                        work.estimated_bytes,
                        0,
                        0,
                        0,
                        0,
                        0,
                    ),
                    policy_summary: empty_policy,
                    unit_reports: Vec::new(),
                },
                payload: None,
                final_env: None,
            };
        }
    };

    let decoded_bytes = decoded_olean_image_bytes(&decoded);
    let checked =
        match check_decoded_olean_per_declaration(&provisional_env, &decoded, limits, true) {
            Ok(checked) => checked,
            Err(error) => {
                let host_memory_refusal = olean_host_memory_refusal(&error);
                let mut verdict = phase2_error_verdict(error);
                if let ProvisionalModuleVerdict::Inconclusive {
                    total_declarations, ..
                } = &mut verdict
                {
                    *total_declarations = decoded.constants.len();
                }
                return Phase2Done {
                    index,
                    host_memory_refusal,
                    usable: false,
                    contributes_assumptions: false,
                    row: ProvisionalFrontierRow {
                        name: module_name.clone(),
                        phase: 2,
                        verdict,
                        assumes,
                        assumed_declarations: closure_assumed_count,
                        k1_steps: 0,
                        elapsed: started.elapsed(),
                        memory_retry: work.phase1_memory_retry,
                        decode_memory_retry: work.phase1_decode_retry,
                        memory: OleanFrontierMemoryAttribution::from_components(
                            work.estimated_bytes,
                            0,
                            0,
                            decoded_bytes,
                            0,
                            0,
                        ),
                        policy_summary: empty_policy,
                        unit_reports: Vec::new(),
                    },
                    payload: None,
                    final_env: None,
                };
            }
        };

    let admitted_bytes = environment_entries_bytes(
        &checked
            .entries
            .iter()
            .map(|(entry, _)| entry.clone())
            .collect::<Vec<_>>(),
    );
    let own_assumed_count = checked.assumed_declaration_names.len();
    let total_assumed = closure_assumed_count.saturating_add(own_assumed_count);
    let memory = OleanFrontierMemoryAttribution::from_components(
        work.estimated_bytes,
        admitted_bytes,
        checked.checker_bytes,
        decoded_bytes,
        admitted_bytes,
        0,
    );
    let retain_env = work.retain_final_env.then_some(checked.final_env).flatten();
    let retain_entries = work.retain_payload_entries;

    match checked.verdict {
        PerDeclarationModuleOutcome::Failed(error) => Phase2Done {
            index,
            host_memory_refusal: false,
            usable: false,
            contributes_assumptions: false,
            row: ProvisionalFrontierRow {
                name: module_name.clone(),
                phase: 2,
                verdict: ProvisionalModuleVerdict::Failed(error),
                assumes,
                assumed_declarations: closure_assumed_count,
                k1_steps: checked.k1_steps,
                elapsed: started.elapsed(),
                memory_retry: work.phase1_memory_retry,
                decode_memory_retry: work.phase1_decode_retry,
                memory,
                policy_summary: checked.policy_summary,
                unit_reports: checked.unit_reports,
            },
            payload: None,
            final_env: None,
        },
        PerDeclarationModuleOutcome::InternalFault(fault) => Phase2Done {
            index,
            host_memory_refusal: false,
            usable: false,
            contributes_assumptions: false,
            row: ProvisionalFrontierRow {
                name: module_name.clone(),
                phase: 2,
                verdict: ProvisionalModuleVerdict::InternalFault(fault),
                assumes,
                assumed_declarations: closure_assumed_count,
                k1_steps: checked.k1_steps,
                elapsed: started.elapsed(),
                memory_retry: work.phase1_memory_retry,
                decode_memory_retry: work.phase1_decode_retry,
                memory,
                policy_summary: checked.policy_summary,
                unit_reports: checked.unit_reports,
            },
            payload: None,
            final_env: None,
        },
        PerDeclarationModuleOutcome::PartialAssumed(reason) => {
            let payload = retain_entries.then_some(Phase2ModulePayload {
                position: 0, // overwritten by scheduler with frontier position
                entries: checked.entries,
            });
            Phase2Done {
                index,
                host_memory_refusal: false,
                usable: true,
                contributes_assumptions: own_assumed_count > 0,
                row: ProvisionalFrontierRow {
                    name: module_name.clone(),
                    phase: 2,
                    verdict: ProvisionalModuleVerdict::Inconclusive {
                        reason,
                        accepted_declarations: checked.accepted_declarations,
                        total_declarations: checked.total_declarations,
                        assumed_declaration_names: checked.assumed_declaration_names,
                    },
                    assumes,
                    assumed_declarations: total_assumed,
                    k1_steps: checked.k1_steps,
                    elapsed: started.elapsed(),
                    memory_retry: work.phase1_memory_retry,
                    decode_memory_retry: work.phase1_decode_retry,
                    memory,
                    policy_summary: checked.policy_summary,
                    unit_reports: checked.unit_reports,
                },
                payload,
                final_env: retain_env,
            }
        }
        PerDeclarationModuleOutcome::AllAccepted => {
            let payload = retain_entries.then_some(Phase2ModulePayload {
                position: 0,
                entries: checked.entries,
            });
            if work.is_phase1_root {
                // Never promote a Phase-1 inconclusive root to accepted in Phase 2.
                let reason = work.phase1_reason.unwrap_or_else(|| {
                    Inconclusive::authority_incomplete("phase-1 inconclusive root")
                });
                Phase2Done {
                    index,
                    host_memory_refusal: false,
                    usable: true,
                    contributes_assumptions: false,
                    row: ProvisionalFrontierRow {
                        name: module_name.clone(),
                        phase: 2,
                        verdict: ProvisionalModuleVerdict::Inconclusive {
                            reason,
                            accepted_declarations: checked.accepted_declarations,
                            total_declarations: checked.total_declarations,
                            assumed_declaration_names: Vec::new(),
                        },
                        assumes,
                        assumed_declarations: closure_assumed_count,
                        k1_steps: checked.k1_steps,
                        elapsed: started.elapsed(),
                        memory_retry: work.phase1_memory_retry,
                        decode_memory_retry: work.phase1_decode_retry,
                        memory,
                        policy_summary: checked.policy_summary,
                        unit_reports: checked.unit_reports,
                    },
                    payload,
                    final_env: retain_env,
                }
            } else {
                Phase2Done {
                    index,
                    host_memory_refusal: false,
                    usable: true,
                    contributes_assumptions: false,
                    row: ProvisionalFrontierRow {
                        name: module_name.clone(),
                        phase: 2,
                        verdict: ProvisionalModuleVerdict::AcceptedUnderAssumptions {
                            declarations: checked.accepted_declarations,
                        },
                        assumes,
                        assumed_declarations: closure_assumed_count,
                        k1_steps: checked.k1_steps,
                        elapsed: started.elapsed(),
                        memory_retry: work.phase1_memory_retry,
                        decode_memory_retry: work.phase1_decode_retry,
                        memory,
                        policy_summary: checked.policy_summary,
                        unit_reports: checked.unit_reports,
                    },
                    payload,
                    final_env: retain_env,
                }
            }
        }
    }
}

fn phase1_row_to_provisional(row: &OleanFrontierRow) -> ProvisionalFrontierRow {
    let verdict = match &row.verdict {
        OleanModuleVerdict::Accepted { declarations } => ProvisionalModuleVerdict::Accepted {
            declarations: *declarations,
        },
        OleanModuleVerdict::Failed(err) => ProvisionalModuleVerdict::Failed(err.clone()),
        OleanModuleVerdict::Inconclusive(reason) => ProvisionalModuleVerdict::Inconclusive {
            reason: reason.clone(),
            accepted_declarations: 0,
            total_declarations: 0,
            assumed_declaration_names: Vec::new(),
        },
        OleanModuleVerdict::InternalFault(fault) => {
            ProvisionalModuleVerdict::InternalFault(fault.clone())
        }
        OleanModuleVerdict::Blocked { by } => ProvisionalModuleVerdict::Blocked {
            by: by.clone(),
            reason: "blocked behind failed or internal-fault import",
        },
    };
    ProvisionalFrontierRow {
        name: row.name.clone(),
        phase: 1,
        verdict,
        assumes: Vec::new(),
        assumed_declarations: 0,
        k1_steps: 0,
        elapsed: row.elapsed,
        memory_retry: row
            .memory_retry
            .as_ref()
            .map(|retry| OleanFrontierMemoryRetry {
                first_refusal: retry.first_refusal.clone(),
                first_elapsed: retry.first_elapsed,
            }),
        decode_memory_retry: row
            .decode_memory_retry
            .as_ref()
            .map(|retry| OleanDecodeMemoryRetry {
                first_error: retry.first_error.clone(),
                first_elapsed: retry.first_elapsed,
                retry_elapsed: retry.retry_elapsed,
                retry_result: retry.retry_result.clone(),
            }),
        memory: row.memory,
        policy_summary: row.policy_summary,
        unit_reports: Vec::new(),
    }
}

/// Optional streaming progress callback invoked as each Phase-2 module settles:
/// `(completed, total, row)`.
pub type Phase2ProgressCallback<'a> = &'a mut dyn FnMut(usize, usize, &ProvisionalFrontierRow);

impl Admitted {
    /// Run Phase 1 (identical to [`Admitted::check_olean_frontier_scheduled`]),
    /// followed by Phase 2 over inconclusive roots (declaration by declaration)
    /// and blocked modules whose blocker chain reaches only inconclusive roots.
    pub fn check_olean_frontier_provisional_scheduled(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        cancellation: Option<&dyn CancellationProbe>,
        on_event: &mut dyn FnMut(OleanFrontierEvent<'_>),
    ) -> Result<ProvisionalFrontier, OleanCheckError> {
        self.check_olean_frontier_provisional_scheduled_with_progress(
            modules,
            options,
            limits,
            jobs,
            cancellation,
            on_event,
            None,
        )
    }

    /// Like [`Self::check_olean_frontier_provisional_scheduled`], also reporting
    /// each Phase-2 module row as soon as it finishes (`(completed, total, row)`).
    #[allow(clippy::too_many_arguments)]
    pub fn check_olean_frontier_provisional_scheduled_with_progress(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        cancellation: Option<&dyn CancellationProbe>,
        on_event: &mut dyn FnMut(OleanFrontierEvent<'_>),
        on_phase2: Option<Phase2ProgressCallback<'_>>,
    ) -> Result<ProvisionalFrontier, OleanCheckError> {
        self.check_olean_frontier_provisional_using_with_progress(
            modules,
            limits,
            jobs,
            cancellation,
            on_event,
            on_phase2,
            FrontierRunHooks {
                check: &|job| self.frontier_check_module(job, options, limits),
                decode: &|index| {
                    decode_olean_module_input_with(&modules[index], limits, CheckerReading::Read)
                },
                memory: &HostProcessMemorySource,
            },
        )
    }

    /// Memory-bounded streaming variant of
    /// [`Self::check_olean_frontier_provisional_scheduled_with_progress`] for
    /// callers that report rows without needing a merged Phase-1 union engine.
    #[allow(clippy::too_many_arguments)]
    pub fn check_olean_frontier_provisional_rows_scheduled_with_progress(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        cancellation: Option<&dyn CancellationProbe>,
        on_event: &mut dyn FnMut(OleanFrontierEvent<'_>),
        on_phase2: Option<Phase2ProgressCallback<'_>>,
    ) -> Result<ProvisionalFrontier<()>, OleanCheckError> {
        let hooks = FrontierRunHooks {
            check: &|job| self.frontier_check_module(job, options, limits),
            decode: &|index| {
                decode_olean_module_input_with(&modules[index], limits, CheckerReading::Read)
            },
            memory: &HostProcessMemorySource,
        };
        let phase1 = self.check_olean_frontier_phase1_core_with_options(
            modules,
            limits,
            jobs,
            on_event,
            hooks,
            FrontierExecutionOptions::STREAMING_PROVISIONAL_ROWS,
        )?;
        self.check_olean_frontier_provisional_after_phase1(
            phase1,
            modules,
            limits,
            jobs,
            cancellation,
            on_phase2,
            hooks,
        )
        .map(|frontier| frontier.map_engine(|_| ()))
    }

    /// Hookable entry point for deterministic unit, fault, and mutant tests.
    pub fn check_olean_frontier_provisional_using(
        &self,
        modules: &[OleanModuleInput<'_>],
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        cancellation: Option<&dyn CancellationProbe>,
        on_event: &mut dyn FnMut(OleanFrontierEvent<'_>),
        hooks: FrontierRunHooks<'_>,
    ) -> Result<ProvisionalFrontier, OleanCheckError> {
        self.check_olean_frontier_provisional_using_with_progress(
            modules,
            limits,
            jobs,
            cancellation,
            on_event,
            None,
            hooks,
        )
    }

    /// Hookable entry point with optional Phase-2 progress callback.
    #[allow(clippy::too_many_arguments)]
    pub fn check_olean_frontier_provisional_using_with_progress(
        &self,
        modules: &[OleanModuleInput<'_>],
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        cancellation: Option<&dyn CancellationProbe>,
        on_event: &mut dyn FnMut(OleanFrontierEvent<'_>),
        on_phase2: Option<Phase2ProgressCallback<'_>>,
        hooks: FrontierRunHooks<'_>,
    ) -> Result<ProvisionalFrontier, OleanCheckError> {
        let phase1 =
            self.check_olean_frontier_phase1_core(modules, limits, jobs, on_event, hooks)?;
        self.check_olean_frontier_provisional_after_phase1(
            phase1,
            modules,
            limits,
            jobs,
            cancellation,
            on_phase2,
            hooks,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn check_olean_frontier_provisional_after_phase1<E>(
        &self,
        phase1: Phase1FrontierOutput<E>,
        modules: &[OleanModuleInput<'_>],
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        cancellation: Option<&dyn CancellationProbe>,
        mut on_phase2: Option<Phase2ProgressCallback<'_>>,
        hooks: FrontierRunHooks<'_>,
    ) -> Result<ProvisionalFrontier<E>, OleanCheckError> {
        let count = modules.len();
        let order = &phase1.order;
        let position = &phase1.position;
        let dependencies = &phase1.dependencies;
        let closures = &phase1.closures;

        // Index Phase-1 rows by original module index.
        let mut phase1_by_index: Vec<Option<&OleanFrontierRow>> = vec![None; count];
        for (pos, row) in phase1.frontier.rows.iter().enumerate() {
            phase1_by_index[order[pos]] = Some(row);
        }
        let mut name_to_index: BTreeMap<&Name, usize> = BTreeMap::new();
        for (index, module) in modules.iter().enumerate() {
            name_to_index.insert(module.name, index);
        }

        let mut phase1_verdicts: Vec<&OleanModuleVerdict> = Vec::with_capacity(count);
        let mut is_accepted = vec![false; count];
        let mut is_blocked = vec![false; count];
        let mut first_blocker = vec![None; count];
        let mut phase1_inconclusive_roots = Vec::new();
        for index in 0..count {
            let row = phase1_by_index[index].ok_or(OleanCheckError::InternalInvariant {
                detail: "phase-1 frontier row missing for module index",
            })?;
            phase1_verdicts.push(&row.verdict);
            match &row.verdict {
                OleanModuleVerdict::Accepted { .. } => is_accepted[index] = true,
                OleanModuleVerdict::Blocked { by } => {
                    is_blocked[index] = true;
                    first_blocker[index] = name_to_index.get(by).copied();
                }
                OleanModuleVerdict::Inconclusive(_) => {}
                _ => {}
            }
        }
        for &index in order {
            if matches!(phase1_verdicts[index], OleanModuleVerdict::Inconclusive(_)) {
                phase1_inconclusive_roots.push(index);
            }
        }

        let (eligible_indices, ineligible_indices, _blocking_roots) =
            classify_blocked_eligibility(order, dependencies, &phase1_verdicts);
        let (unlock_values, first_blocker_counts) = compute_root_dominators(
            order,
            dependencies,
            &is_accepted,
            &is_blocked,
            &first_blocker,
        );

        let eligible_blocked: Vec<Name> = eligible_indices
            .iter()
            .map(|&idx| modules[idx].name.clone())
            .collect();
        let ineligible_blocked: Vec<Name> = ineligible_indices
            .iter()
            .map(|&idx| modules[idx].name.clone())
            .collect();

        if phase1_inconclusive_roots.is_empty() {
            let rows: Vec<ProvisionalFrontierRow> = phase1
                .frontier
                .rows
                .iter()
                .map(phase1_row_to_provisional)
                .collect();
            let policy_summary = CheckerPolicySummary::merge(
                limits.admission.policy,
                rows.iter().map(|row| &row.policy_summary),
            );
            let result = ProvisionalFrontier {
                phase1_engine: phase1.frontier.engine,
                phase1_rows: phase1.frontier.rows,
                rows,
                has_phase2_rows: false,
                eligible_blocked,
                ineligible_blocked,
                roots: Vec::new(),
                policy_summary,
            };
            result.counts().assert_conservation();
            return Ok(result);
        }

        // Phase 2: check Phase-1 inconclusive roots declaration-by-declaration,
        // then check all eligible blocked modules in topological order.
        let mut phase2_candidates: BTreeSet<usize> = BTreeSet::new();
        for &idx in &phase1_inconclusive_roots {
            phase2_candidates.insert(idx);
        }
        for &idx in &eligible_indices {
            phase2_candidates.insert(idx);
        }
        let phase1_root_set: BTreeSet<usize> = phase1_inconclusive_roots.iter().copied().collect();

        // Pick each Phase-2 module's largest direct Phase-2 dependency as its
        // persistent `ProvisionalEnvironment` base (deterministic function of
        // import graph + frontier position; FL-INV-01). Only modules outside
        // `closures[base_dep]` are merged as deltas, slashing Phase-2 allocation
        // churn by ~1000x on deep Mathlib closures.
        let mut phase2_base_of: Vec<Option<usize>> = vec![None; count];
        let mut base_env_consumers: Vec<usize> = vec![0; count];
        let mut remaining_delta_consumers: Vec<usize> = vec![0; count];
        for &idx in &phase2_candidates {
            let best_dep = dependencies[idx]
                .iter()
                .copied()
                .filter(|dep| phase2_candidates.contains(dep))
                .max_by_key(|&dep| (closures[dep].len(), std::cmp::Reverse(position[dep])));
            phase2_base_of[idx] = best_dep;
            if let Some(dep) = best_dep {
                base_env_consumers[dep] += 1;
            }
            for &member in closures[idx].iter() {
                if member == idx {
                    continue;
                }
                if best_dep.is_some_and(|dep| closures[dep].contains(&member)) {
                    continue;
                }
                remaining_delta_consumers[member] += 1;
            }
        }
        // Release every Phase-1 accepted payload that no Phase-2 delta needs
        // BEFORE spawning Phase-2 workers, reclaiming peak RSS up front.
        let mut phase1_accepted = phase1.accepted;
        for member in 0..count {
            if remaining_delta_consumers[member] == 0 {
                phase1_accepted[member] = None;
            }
        }

        let mut phase2_rows: Vec<Option<ProvisionalFrontierRow>> =
            (0..count).map(|_| None).collect();
        let mut phase2_payloads: Vec<Option<std::sync::Arc<Phase2ModulePayload>>> =
            vec![None; count];
        let mut phase2_envs: Vec<Option<std::sync::Arc<ProvisionalEnvironment>>> =
            vec![None; count];
        let mut phase2_usable = vec![false; count];
        let mut phase2_contributes_assumptions = vec![false; count];
        let mut phase2_decided = vec![false; count];
        let mut phase2_running = vec![false; count];
        let mut phase2_memory_retries: Vec<Option<OleanFrontierMemoryRetry>> =
            (0..count).map(|_| None).collect();
        let mut retry_pending: BTreeSet<(usize, usize)> = BTreeSet::new();
        let mut isolated_running: Option<usize> = None;
        let threads = jobs.threads.get();
        let base_env = &self.environment;
        let decode = hooks.decode;
        let memory = hooks.memory;

        std::thread::scope(|scope| -> Result<(), OleanCheckError> {
            let (work_tx, work_rx) = std::sync::mpsc::channel::<Phase2Work>();
            let (done_tx, done_rx) = std::sync::mpsc::channel::<Phase2Done>();
            let work_rx = std::sync::Arc::new(std::sync::Mutex::new(work_rx));
            if threads > 1 {
                for worker in 0..threads {
                    let work_rx = std::sync::Arc::clone(&work_rx);
                    let done_tx = done_tx.clone();
                    std::thread::Builder::new()
                        .name(format!("fln-provisional-{worker}"))
                        .stack_size(jobs.worker_stack_bytes)
                        .spawn_scoped(scope, move || {
                            loop {
                                let next = match work_rx.lock() {
                                    Ok(rx) => rx.recv(),
                                    Err(_) => return,
                                };
                                let Ok(work) = next else { return };
                                let done = phase2_guarded(
                                    base_env,
                                    modules[work.index].name,
                                    work,
                                    limits,
                                    decode,
                                );
                                if done_tx.send(done).is_err() {
                                    return;
                                }
                            }
                        })
                        .map_err(|_| OleanCheckError::InternalInvariant {
                            detail: "could not start a provisional frontier worker thread",
                        })?;
                }
            }
            drop(done_tx);

            let build_work = |index: usize,
                              retain_final_env: bool,
                              retain_payload_entries: bool,
                              phase1_accepted: &[Option<std::sync::Arc<FrontierAccepted>>],
                              phase2_payloads: &[Option<std::sync::Arc<Phase2ModulePayload>>],
                              phase2_envs: &[Option<std::sync::Arc<ProvisionalEnvironment>>],
                              phase2_contributes_assumptions: &[bool]|
             -> Phase2Work {
                let p1 = phase1_by_index[index].expect("phase1 row");
                let phase1_reason = match &p1.verdict {
                    OleanModuleVerdict::Inconclusive(reason) => Some(reason.clone()),
                    _ => None,
                };
                let base_dep = phase2_base_of[index];
                let base_provisional = base_dep.and_then(|dep| phase2_envs[dep].clone());
                let mut assumes_set: BTreeSet<Name> = BTreeSet::new();
                let mut p1_closure = Vec::new();
                let mut p2_closure = Vec::new();
                for &member in closures[index].iter() {
                    if member == index {
                        continue;
                    }
                    if phase2_contributes_assumptions[member] {
                        assumes_set.insert(modules[member].name.clone());
                    }
                    if base_dep.is_some_and(|dep| closures[dep].contains(&member)) {
                        continue;
                    }
                    if let Some(acc) = &phase1_accepted[member] {
                        p1_closure.push(std::sync::Arc::clone(acc));
                    } else if let Some(payload) = &phase2_payloads[member] {
                        p2_closure.push(std::sync::Arc::clone(payload));
                    }
                }
                Phase2Work {
                    index,
                    is_phase1_root: phase1_root_set.contains(&index),
                    phase1_reason,
                    phase1_memory_retry: p1.memory_retry.as_ref().map(|r| {
                        OleanFrontierMemoryRetry {
                            first_refusal: r.first_refusal.clone(),
                            first_elapsed: r.first_elapsed,
                        }
                    }),
                    phase1_decode_retry: p1.decode_memory_retry.as_ref().map(|r| {
                        OleanDecodeMemoryRetry {
                            first_error: r.first_error.clone(),
                            first_elapsed: r.first_elapsed,
                            retry_elapsed: r.retry_elapsed,
                            retry_result: r.retry_result.clone(),
                        }
                    }),
                    estimated_bytes: p1.memory.estimated_bytes,
                    base_provisional,
                    assumes: assumes_set.into_iter().collect(),
                    phase1_accepted_closure: p1_closure,
                    phase2_closure: p2_closure,
                    retain_final_env,
                    retain_payload_entries,
                }
            };

            let release_consumers = |idx: usize,
                                     base_env_consumers: &mut [usize],
                                     remaining_delta_consumers: &mut [usize],
                                     phase1_accepted: &mut [Option<
                std::sync::Arc<FrontierAccepted>,
            >],
                                     phase2_payloads: &mut [Option<
                std::sync::Arc<Phase2ModulePayload>,
            >],
                                     phase2_envs: &mut [Option<
                std::sync::Arc<ProvisionalEnvironment>,
            >]| {
                let base_dep = phase2_base_of[idx];
                if let Some(dep) = base_dep {
                    base_env_consumers[dep] = base_env_consumers[dep].saturating_sub(1);
                    if base_env_consumers[dep] == 0 {
                        phase2_envs[dep] = None;
                    }
                }
                for &member in closures[idx].iter() {
                    if member == idx {
                        continue;
                    }
                    if base_dep.is_some_and(|dep| closures[dep].contains(&member)) {
                        continue;
                    }
                    remaining_delta_consumers[member] =
                        remaining_delta_consumers[member].saturating_sub(1);
                    if remaining_delta_consumers[member] == 0 {
                        phase1_accepted[member] = None;
                        phase2_payloads[member] = None;
                    }
                }
            };

            let mut in_flight = 0_usize;
            let mut in_flight_estimated_bytes = 0_u64;
            let mut idle_rss_bytes = memory.sample().rss_bytes;
            let estimated_bytes: Vec<u64> = phase1_by_index
                .iter()
                .map(|row| row.expect("phase1 row").memory.estimated_bytes)
                .collect();
            let mut admission_deferrals: Vec<u64> = phase1_by_index
                .iter()
                .map(|row| row.expect("phase1 row").memory.admission_deferrals)
                .collect();
            let mut cancelled = false;
            let phase2_total = phase2_candidates.len();
            let mut phase2_completed = 0_usize;
            loop {
                cancelled = cancelled || cancellation.is_some_and(CancellationProbe::is_cancelled);

                // First settle any Phase-2 candidate whose dependency became
                // non-assumable (failed/internal-fault/un-decodable) or was cancelled,
                // including a module whose memory retry has not started yet.
                let mut ready = Vec::new();
                for &index in order {
                    if !phase2_candidates.contains(&index)
                        || phase2_decided[index]
                        || phase2_running[index]
                    {
                        continue;
                    }
                    if cancelled {
                        retry_pending.remove(&(position[index], index));
                        let elapsed = phase2_memory_retries[index]
                            .take()
                            .map_or(std::time::Duration::ZERO, |retry| retry.first_elapsed);
                        phase2_decided[index] = true;
                        release_consumers(
                            index,
                            &mut base_env_consumers,
                            &mut remaining_delta_consumers,
                            &mut phase1_accepted,
                            &mut phase2_payloads,
                            &mut phase2_envs,
                        );
                        let p1 = phase1_by_index[index].expect("phase1 row");
                        let row = ProvisionalFrontierRow {
                            name: modules[index].name.clone(),
                            phase: 2,
                            verdict: ProvisionalModuleVerdict::Inconclusive {
                                reason: Inconclusive::cancelled("olean-frontier/provisional"),
                                accepted_declarations: 0,
                                total_declarations: 0,
                                assumed_declaration_names: Vec::new(),
                            },
                            assumes: Vec::new(),
                            assumed_declarations: 0,
                            k1_steps: 0,
                            elapsed,
                            memory_retry: None,
                            decode_memory_retry: None,
                            memory: p1.memory.with_schedule_context(
                                estimated_bytes[index],
                                admission_deferrals[index],
                            ),
                            policy_summary: CheckerPolicySummary::empty(limits.admission.policy),
                            unit_reports: Vec::new(),
                        };
                        phase2_completed += 1;
                        if let Some(cb) = on_phase2.as_deref_mut() {
                            cb(phase2_completed, phase2_total, &row);
                        }
                        phase2_rows[index] = Some(row);
                        continue;
                    }
                    if retry_pending.contains(&(position[index], index)) {
                        continue;
                    }
                    let deps_done = dependencies[index]
                        .iter()
                        .all(|&dep| is_accepted[dep] || phase2_decided[dep]);
                    if !deps_done {
                        continue;
                    }
                    let blocker = dependencies[index]
                        .iter()
                        .copied()
                        .find(|&dep| !is_accepted[dep] && !phase2_usable[dep]);
                    if let Some(blocker_idx) = blocker {
                        phase2_decided[index] = true;
                        release_consumers(
                            index,
                            &mut base_env_consumers,
                            &mut remaining_delta_consumers,
                            &mut phase1_accepted,
                            &mut phase2_payloads,
                            &mut phase2_envs,
                        );
                        let p1 = phase1_by_index[index].expect("phase1 row");
                        let row = ProvisionalFrontierRow {
                            name: modules[index].name.clone(),
                            phase: 2,
                            verdict: ProvisionalModuleVerdict::Blocked {
                                by: modules[blocker_idx].name.clone(),
                                reason: "import failed or could not be decoded in phase 2",
                            },
                            assumes: Vec::new(),
                            assumed_declarations: 0,
                            k1_steps: 0,
                            elapsed: std::time::Duration::ZERO,
                            memory_retry: None,
                            decode_memory_retry: None,
                            memory: p1.memory.with_schedule_context(
                                estimated_bytes[index],
                                admission_deferrals[index],
                            ),
                            policy_summary: CheckerPolicySummary::empty(limits.admission.policy),
                            unit_reports: Vec::new(),
                        };
                        phase2_completed += 1;
                        if let Some(cb) = on_phase2.as_deref_mut() {
                            cb(phase2_completed, phase2_total, &row);
                        }
                        phase2_rows[index] = Some(row);
                        continue;
                    }
                    ready.push(index);
                }

                let all_decided = phase2_candidates.iter().all(|&idx| phase2_decided[idx]);
                if all_decided && in_flight == 0 {
                    break;
                }

                // Isolated single-threaded memory retry once in-flight workers drain.
                if !cancelled
                    && isolated_running.is_none()
                    && in_flight == 0
                    && let Some((_, retry_idx)) = retry_pending.pop_first()
                {
                    let work = build_work(
                        retry_idx,
                        base_env_consumers[retry_idx] > 0,
                        remaining_delta_consumers[retry_idx] > 0,
                        &phase1_accepted,
                        &phase2_payloads,
                        &phase2_envs,
                        &phase2_contributes_assumptions,
                    );
                    phase2_running[retry_idx] = true;
                    isolated_running = Some(retry_idx);
                    in_flight = 1;
                    in_flight_estimated_bytes = estimated_bytes[retry_idx];
                    if threads == 1 {
                        let mut done =
                            phase2_guarded(base_env, modules[retry_idx].name, work, limits, decode);
                        in_flight = 0;
                        in_flight_estimated_bytes = 0;
                        isolated_running = None;
                        phase2_running[retry_idx] = false;
                        phase2_decided[retry_idx] = true;
                        phase2_usable[retry_idx] = done.usable;
                        phase2_contributes_assumptions[retry_idx] = done.contributes_assumptions;
                        if let Some(retry) = phase2_memory_retries[retry_idx].take() {
                            done.row.memory_retry = Some(retry);
                        }
                        if let Some(mut payload) = done.payload.take() {
                            payload.position = position[retry_idx];
                            phase2_payloads[retry_idx] = Some(std::sync::Arc::new(payload));
                        }
                        if let Some(env) = done.final_env.take() {
                            phase2_envs[retry_idx] = Some(std::sync::Arc::new(env));
                        }
                        release_consumers(
                            retry_idx,
                            &mut base_env_consumers,
                            &mut remaining_delta_consumers,
                            &mut phase1_accepted,
                            &mut phase2_payloads,
                            &mut phase2_envs,
                        );
                        done.row.memory = done.row.memory.with_schedule_context(
                            estimated_bytes[retry_idx],
                            admission_deferrals[retry_idx],
                        );
                        phase2_completed += 1;
                        if let Some(cb) = on_phase2.as_deref_mut() {
                            cb(phase2_completed, phase2_total, &done.row);
                        }
                        phase2_rows[retry_idx] = Some(done.row);
                        continue;
                    }
                    if work_tx.send(work).is_err() {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "every provisional frontier worker thread has stopped",
                        });
                    }
                }

                // Do not start new concurrent modules while a memory retry is pending or isolated.
                for index in ready
                    .into_iter()
                    .filter(|_| retry_pending.is_empty() && isolated_running.is_none())
                {
                    if in_flight >= threads {
                        break;
                    }
                    // Phase 1's retained import payloads remain resident here.
                    // Account for that live baseline and reserve each in-flight
                    // closure estimate before admitting another worker, just as
                    // the authoritative frontier does. A lone module is always
                    // allowed to try: an estimate is not a resource verdict.
                    let sample = memory.sample();
                    if in_flight == 0 {
                        idle_rss_bytes = sample.rss_bytes;
                    } else if let Some(limit_bytes) = sample.limit_bytes {
                        let committed_bytes = sample
                            .rss_bytes
                            .max(idle_rss_bytes.saturating_add(in_flight_estimated_bytes));
                        if committed_bytes.saturating_add(estimated_bytes[index]) > limit_bytes {
                            admission_deferrals[index] =
                                admission_deferrals[index].saturating_add(1);
                            continue;
                        }
                    }
                    let work = build_work(
                        index,
                        base_env_consumers[index] > 0,
                        remaining_delta_consumers[index] > 0,
                        &phase1_accepted,
                        &phase2_payloads,
                        &phase2_envs,
                        &phase2_contributes_assumptions,
                    );
                    phase2_running[index] = true;
                    in_flight += 1;
                    in_flight_estimated_bytes =
                        in_flight_estimated_bytes.saturating_add(estimated_bytes[index]);
                    if threads == 1 {
                        let mut done =
                            phase2_guarded(base_env, modules[index].name, work, limits, decode);
                        in_flight -= 1;
                        in_flight_estimated_bytes =
                            in_flight_estimated_bytes.saturating_sub(estimated_bytes[index]);
                        phase2_running[index] = false;
                        phase2_decided[index] = true;
                        phase2_usable[index] = done.usable;
                        phase2_contributes_assumptions[index] = done.contributes_assumptions;
                        if let Some(mut payload) = done.payload.take() {
                            payload.position = position[index];
                            phase2_payloads[index] = Some(std::sync::Arc::new(payload));
                        }
                        if let Some(env) = done.final_env.take() {
                            phase2_envs[index] = Some(std::sync::Arc::new(env));
                        }
                        release_consumers(
                            index,
                            &mut base_env_consumers,
                            &mut remaining_delta_consumers,
                            &mut phase1_accepted,
                            &mut phase2_payloads,
                            &mut phase2_envs,
                        );
                        done.row.memory = done.row.memory.with_schedule_context(
                            estimated_bytes[index],
                            admission_deferrals[index],
                        );
                        phase2_completed += 1;
                        if let Some(cb) = on_phase2.as_deref_mut() {
                            cb(phase2_completed, phase2_total, &done.row);
                        }
                        phase2_rows[index] = Some(done.row);
                        break;
                    }
                    if work_tx.send(work).is_err() {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "every provisional frontier worker thread has stopped",
                        });
                    }
                }

                if threads == 1 {
                    continue;
                }
                if in_flight == 0 {
                    if phase2_candidates.iter().all(|&idx| phase2_decided[idx]) {
                        break;
                    }
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "provisional frontier stalled with eligible modules undecided",
                    });
                }
                let mut done = done_rx
                    .recv()
                    .map_err(|_| OleanCheckError::InternalInvariant {
                        detail: "every provisional frontier worker thread has stopped",
                    })?;
                in_flight -= 1;
                let idx = done.index;
                in_flight_estimated_bytes =
                    in_flight_estimated_bytes.saturating_sub(estimated_bytes[idx]);
                phase2_running[idx] = false;
                if done.host_memory_refusal
                    && isolated_running != Some(idx)
                    && phase2_memory_retries[idx].is_none()
                {
                    let first_refusal = match done.row.verdict {
                        ProvisionalModuleVerdict::Inconclusive { reason, .. } => reason,
                        _ => Inconclusive::dependency_unavailable(
                            "host memory refusal during phase-2 provisional check",
                        ),
                    };
                    phase2_memory_retries[idx] = Some(OleanFrontierMemoryRetry {
                        first_refusal,
                        first_elapsed: done.row.elapsed,
                    });
                    retry_pending.insert((position[idx], idx));
                    continue;
                }
                if isolated_running == Some(idx) {
                    isolated_running = None;
                }
                if let Some(retry) = phase2_memory_retries[idx].take() {
                    done.row.memory_retry = Some(retry);
                }
                phase2_decided[idx] = true;
                phase2_usable[idx] = done.usable;
                phase2_contributes_assumptions[idx] = done.contributes_assumptions;
                if let Some(mut payload) = done.payload.take() {
                    payload.position = position[idx];
                    phase2_payloads[idx] = Some(std::sync::Arc::new(payload));
                }
                if let Some(env) = done.final_env.take() {
                    phase2_envs[idx] = Some(std::sync::Arc::new(env));
                }
                release_consumers(
                    idx,
                    &mut base_env_consumers,
                    &mut remaining_delta_consumers,
                    &mut phase1_accepted,
                    &mut phase2_payloads,
                    &mut phase2_envs,
                );
                done.row.memory = done
                    .row
                    .memory
                    .with_schedule_context(estimated_bytes[idx], admission_deferrals[idx]);
                phase2_completed += 1;
                if let Some(cb) = on_phase2.as_deref_mut() {
                    cb(phase2_completed, phase2_total, &done.row);
                }
                phase2_rows[idx] = Some(done.row);
            }
            drop(work_tx);
            Ok(())
        })?;

        let mut rows = Vec::with_capacity(count);
        let mut has_phase2_rows = false;
        for (pos, p1_row) in phase1.frontier.rows.iter().enumerate() {
            let index = order[pos];
            if let Some(p2_row) = phase2_rows[index].take() {
                has_phase2_rows = true;
                rows.push(p2_row);
            } else {
                rows.push(phase1_row_to_provisional(p1_row));
            }
        }

        let mut roots = Vec::with_capacity(phase1_inconclusive_roots.len());
        for &root_idx in &phase1_inconclusive_roots {
            let row = &rows[position[root_idx]];
            let (accepted_declarations, total_declarations, assumed_declaration_names) =
                match &row.verdict {
                    ProvisionalModuleVerdict::Inconclusive {
                        accepted_declarations,
                        total_declarations,
                        assumed_declaration_names,
                        ..
                    } => (
                        *accepted_declarations,
                        *total_declarations,
                        assumed_declaration_names.clone(),
                    ),
                    _ => (0, 0, Vec::new()),
                };
            roots.push(ProvisionalRootSummary {
                module: modules[root_idx].name.clone(),
                unlock_value: unlock_values.get(&root_idx).copied().unwrap_or(0),
                first_blocker_count: first_blocker_counts.get(&root_idx).copied().unwrap_or(0),
                accepted_declarations,
                total_declarations,
                assumed_declarations: assumed_declaration_names.len(),
                assumed_declaration_names,
            });
        }

        let policy_summary = CheckerPolicySummary::merge(
            limits.admission.policy,
            rows.iter().map(|row| &row.policy_summary),
        );
        let result = ProvisionalFrontier {
            phase1_engine: phase1.frontier.engine,
            phase1_rows: phase1.frontier.rows,
            rows,
            has_phase2_rows,
            eligible_blocked,
            ineligible_blocked,
            roots,
            policy_summary,
        };
        result.counts().assert_conservation();
        Ok(result)
    }
}
