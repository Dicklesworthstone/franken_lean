//! End-to-end `bv_decide` orchestration over Verdict's untrusted engines.
//!
//! The proposition is negated before bitblasting. An UNSAT result therefore
//! establishes the proposition, but it is still non-authoritative until the exact
//! proof stream is independently replayed and the reflected theorem is admitted
//! through Crucible's opaque checked-declaration capability. A SAT result is an
//! independently re-decoded counterexample and has no environment-publication path.

#![forbid(unsafe_code)]

use fln_core::expr::Expr;
use fln_core::mode::{Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::Inconclusive;
use fln_env::environment::Environment;
use fln_env::modules::CancellationProbe;

use crate::{
    BitblastArtifact, BitblastFacts, BitblastInconclusive, BitblastInputKind,
    BitblastInternalFault, BitblastLimits, BitblastOutcome, BitblastRefusal, BitblastSymbol,
    BoolExpr, Cnf, ReflectedArtifactError, ReflectedTheoremArtifact, ReflectedTheoremInconclusive,
    ReflectedTheoremInternalFault, ReflectedTheoremLimits, ReflectedTheoremOutcome,
    ReflectedTheoremProvenance, ReflectedTheoremPublication, ReflectedTheoremRefusal, SatModel,
    SchemaError, SchemaLimits, SolverInconclusive, SolverInternalFault, SolverLimits,
    SolverOutcome, SolverStatistics, VariableId, bitblast_with_cancel, publish_reflected_theorem,
    solve_with_cancel,
};

/// The registered orchestration policy for the complete `bv_decide` path.
///
/// This is an in-memory algorithm identity, not a new durable schema.
pub const BV_DECIDE_POLICY_ID: &str = "fln.verdict.bv-decide/1";

/// One theorem request. Policy identities are intentionally not caller supplied.
#[derive(Debug, Clone)]
pub struct BvDecideRequest {
    proposition: BoolExpr,
    theorem_name: Name,
    level_params: Vec<Name>,
    source_proposition: Expr,
    reflected_proof: Expr,
    mode: Mode,
    reproducibility: ReproducibilityProfile,
}

impl BvDecideRequest {
    pub fn new(
        proposition: BoolExpr,
        theorem_name: Name,
        level_params: Vec<Name>,
        source_proposition: Expr,
        reflected_proof: Expr,
        mode: Mode,
        reproducibility: ReproducibilityProfile,
    ) -> Self {
        Self {
            proposition,
            theorem_name,
            level_params,
            source_proposition,
            reflected_proof,
            mode,
            reproducibility,
        }
    }

    pub const fn policy_id(&self) -> &'static str {
        BV_DECIDE_POLICY_ID
    }

    pub const fn proposition(&self) -> &BoolExpr {
        &self.proposition
    }

    pub const fn theorem_name(&self) -> &Name {
        &self.theorem_name
    }

    pub const fn mode(&self) -> Mode {
        self.mode
    }

    pub const fn reproducibility(&self) -> ReproducibilityProfile {
        self.reproducibility
    }
}

/// Bounded resources for the three authority-separated phases.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct BvDecideLimits {
    pub bitblast: BitblastLimits,
    pub solver: SolverLimits,
    pub reflection: ReflectedTheoremLimits,
}

/// Telemetry is deliberately separate from semantic outcome and artifact identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BvDecideTelemetry {
    pub bitblast: BitblastFacts,
    pub solver: SolverStatistics,
    pub proof_checker_work_units: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvDecideInputValue {
    Boolean(bool),
    Bitvector(Box<[bool]>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvDecideInputAssignment {
    symbol: BitblastSymbol,
    value: BvDecideInputValue,
}

impl BvDecideInputAssignment {
    pub const fn symbol(&self) -> BitblastSymbol {
        self.symbol
    }

    pub const fn value(&self) -> &BvDecideInputValue {
        &self.value
    }
}

/// A SAT model for the negated proposition, independently decoded and checked.
///
/// This is a completed negative determination, not an inconclusive result and not
/// an environment authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvDecideCounterexample {
    cnf_bytes: Box<[u8]>,
    model_bytes: Box<[u8]>,
    inputs: Box<[BvDecideInputAssignment]>,
    telemetry: BvDecideTelemetry,
}

impl BvDecideCounterexample {
    pub fn cnf_bytes(&self) -> &[u8] {
        &self.cnf_bytes
    }

    pub fn model_bytes(&self) -> &[u8] {
        &self.model_bytes
    }

    pub fn inputs(&self) -> &[BvDecideInputAssignment] {
        &self.inputs
    }

    pub fn input(&self, symbol: BitblastSymbol) -> Option<&BvDecideInputValue> {
        self.inputs
            .binary_search_by_key(&symbol, BvDecideInputAssignment::symbol)
            .ok()
            .map(|index| self.inputs[index].value())
    }

    pub const fn telemetry(&self) -> BvDecideTelemetry {
        self.telemetry
    }
}

/// The only successful theorem result: a Crucible-checked, capability-published
/// declaration plus non-semantic resource telemetry.
#[derive(Debug)]
pub struct BvDecidePublication {
    reflection: ReflectedTheoremPublication,
    telemetry: BvDecideTelemetry,
}

impl BvDecidePublication {
    pub const fn reflection(&self) -> &ReflectedTheoremPublication {
        &self.reflection
    }

    pub const fn telemetry(&self) -> BvDecideTelemetry {
        self.telemetry
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvDecideRefusal {
    Bitblast(BitblastRefusal),
    Reflection(ReflectedTheoremRefusal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvDecideInconclusive {
    Pipeline(Inconclusive),
    Bitblast(BitblastInconclusive),
    Solver {
        cause: SolverInconclusive,
        statistics: SolverStatistics,
    },
    CounterexampleAllocationRefused {
        requested: u64,
    },
    Reflection(ReflectedTheoremInconclusive),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvDecideInternalFault {
    Bitblast(BitblastInternalFault),
    Solver {
        fault: SolverInternalFault,
        statistics: SolverStatistics,
    },
    ReflectedArtifact(ReflectedArtifactError),
    SatCnfMismatch {
        bitblast_bytes: u64,
        solver_bytes: u64,
    },
    SatDecode {
        stream: &'static str,
        error: SchemaError,
    },
    SatModelDoesNotSatisfyNegation,
    InputBindingShape {
        symbol: BitblastSymbol,
        expected_bits: u32,
        actual_bits: u64,
    },
    MissingInputAssignment {
        symbol: BitblastSymbol,
        variable: VariableId,
    },
    Reflection(ReflectedTheoremInternalFault),
}

/// The five disjoint terminal classes. Only [`Self::Proved`] carries a published
/// environment; resource or cancellation outcomes cannot be mistaken for false.
#[derive(Debug)]
#[must_use]
pub enum BvDecideOutcome {
    Proved(Box<BvDecidePublication>),
    Counterexample(Box<BvDecideCounterexample>),
    Refused(BvDecideRefusal),
    Inconclusive(BvDecideInconclusive),
    InternalFault(BvDecideInternalFault),
}

impl BvDecideOutcome {
    pub const fn publication(&self) -> Option<&BvDecidePublication> {
        match self {
            Self::Proved(publication) => Some(publication),
            Self::Counterexample(_)
            | Self::Refused(_)
            | Self::Inconclusive(_)
            | Self::InternalFault(_) => None,
        }
    }

    pub const fn counterexample(&self) -> Option<&BvDecideCounterexample> {
        match self {
            Self::Counterexample(counterexample) => Some(counterexample),
            Self::Proved(_) | Self::Refused(_) | Self::Inconclusive(_) | Self::InternalFault(_) => {
                None
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BvDecideCheckpoint {
    Bitblast,
    Solve,
    Reflection,
}

impl BvDecideCheckpoint {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Bitblast => "bv-decide/before-bitblast",
            Self::Solve => "bv-decide/before-solve",
            Self::Reflection => "bv-decide/before-reflection",
        }
    }
}

enum CounterexampleValidationStop {
    AllocationRefused { requested: u64 },
    InternalFault(Box<BvDecideInternalFault>),
}

impl From<BvDecideInternalFault> for CounterexampleValidationStop {
    fn from(fault: BvDecideInternalFault) -> Self {
        Self::InternalFault(Box::new(fault))
    }
}

fn is_cancelled(cancellation: Option<&dyn CancellationProbe>) -> bool {
    cancellation.is_some_and(CancellationProbe::is_cancelled)
}

fn cancelled(checkpoint: BvDecideCheckpoint) -> BvDecideOutcome {
    BvDecideOutcome::Inconclusive(BvDecideInconclusive::Pipeline(Inconclusive::cancelled(
        checkpoint.as_str(),
    )))
}

fn slice_len<T>(values: &[T]) -> u64 {
    u64::try_from(values.len()).unwrap_or(u64::MAX)
}

fn input_values(
    bitblast: &BitblastArtifact,
    model: &SatModel,
) -> Result<Box<[BvDecideInputAssignment]>, CounterexampleValidationStop> {
    let mut values = Vec::new();
    values.try_reserve(bitblast.inputs().len()).map_err(|_| {
        CounterexampleValidationStop::AllocationRefused {
            requested: slice_len(bitblast.inputs()),
        }
    })?;
    for binding in bitblast.inputs() {
        let variables = binding.variables_lsb_first();
        let value = match binding.kind() {
            BitblastInputKind::Boolean => {
                let [variable] = variables else {
                    return Err(BvDecideInternalFault::InputBindingShape {
                        symbol: binding.symbol(),
                        expected_bits: 1,
                        actual_bits: slice_len(variables),
                    }
                    .into());
                };
                let value = model.value(*variable).ok_or(
                    BvDecideInternalFault::MissingInputAssignment {
                        symbol: binding.symbol(),
                        variable: *variable,
                    },
                )?;
                BvDecideInputValue::Boolean(value)
            }
            BitblastInputKind::Bitvector { width } => {
                if variables.len() != usize::try_from(width).unwrap_or(usize::MAX) {
                    return Err(BvDecideInternalFault::InputBindingShape {
                        symbol: binding.symbol(),
                        expected_bits: width,
                        actual_bits: slice_len(variables),
                    }
                    .into());
                }
                let mut bits = Vec::new();
                bits.try_reserve(variables.len()).map_err(|_| {
                    CounterexampleValidationStop::AllocationRefused {
                        requested: slice_len(variables),
                    }
                })?;
                for variable in variables {
                    bits.push(model.value(*variable).ok_or(
                        BvDecideInternalFault::MissingInputAssignment {
                            symbol: binding.symbol(),
                            variable: *variable,
                        },
                    )?);
                }
                BvDecideInputValue::Bitvector(bits.into_boxed_slice())
            }
        };
        values.push(BvDecideInputAssignment {
            symbol: binding.symbol(),
            value,
        });
    }
    Ok(values.into_boxed_slice())
}

fn independently_validate_counterexample(
    bitblast: &BitblastArtifact,
    artifact: crate::CheckedSat,
    statistics: SolverStatistics,
    limits: SchemaLimits,
) -> Result<BvDecideCounterexample, CounterexampleValidationStop> {
    let bitblast_bytes = bitblast.cnf_bytes();
    if bitblast_bytes.as_slice() != artifact.cnf_bytes() {
        return Err(BvDecideInternalFault::SatCnfMismatch {
            bitblast_bytes: slice_len(&bitblast_bytes),
            solver_bytes: slice_len(artifact.cnf_bytes()),
        }
        .into());
    }
    let cnf = Cnf::from_canonical_bytes(artifact.cnf_bytes(), limits).map_err(|error| {
        BvDecideInternalFault::SatDecode {
            stream: "cnf",
            error,
        }
    })?;
    let model =
        SatModel::from_canonical_bytes(artifact.model_bytes(), limits).map_err(|error| {
            BvDecideInternalFault::SatDecode {
                stream: "sat-model",
                error,
            }
        })?;
    match model.satisfies(&cnf) {
        Ok(true) => {}
        Ok(false) => {
            return Err(BvDecideInternalFault::SatModelDoesNotSatisfyNegation.into());
        }
        Err(error) => {
            return Err(BvDecideInternalFault::SatDecode {
                stream: "sat-model-validation",
                error,
            }
            .into());
        }
    }
    let inputs = input_values(bitblast, &model)?;
    let (cnf_bytes, model_bytes) = artifact.into_canonical_streams();
    Ok(BvDecideCounterexample {
        cnf_bytes,
        model_bytes,
        inputs,
        telemetry: BvDecideTelemetry {
            bitblast: bitblast.facts(),
            solver: statistics,
            proof_checker_work_units: None,
        },
    })
}

/// Decide without cancellation.
pub fn bv_decide(
    environment: &Environment,
    request: BvDecideRequest,
    limits: BvDecideLimits,
) -> BvDecideOutcome {
    bv_decide_with_cancel(environment, request, limits, None)
}

/// Canonical bitblast, deterministic solve, independent artifact validation, and
/// capability-bound theorem publication.
pub fn bv_decide_with_cancel(
    environment: &Environment,
    request: BvDecideRequest,
    limits: BvDecideLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> BvDecideOutcome {
    if is_cancelled(cancellation) {
        return cancelled(BvDecideCheckpoint::Bitblast);
    }
    let BvDecideRequest {
        proposition,
        theorem_name,
        level_params,
        source_proposition,
        reflected_proof,
        mode,
        reproducibility,
    } = request;
    let negated = BoolExpr::logical_not(proposition);
    let bitblast =
        match bitblast_with_cancel(&negated, limits.bitblast, || is_cancelled(cancellation)) {
            BitblastOutcome::Complete(artifact) => artifact,
            BitblastOutcome::Refused(refusal) => {
                return BvDecideOutcome::Refused(BvDecideRefusal::Bitblast(refusal));
            }
            BitblastOutcome::Inconclusive(inconclusive) => {
                return BvDecideOutcome::Inconclusive(BvDecideInconclusive::Bitblast(inconclusive));
            }
            BitblastOutcome::InternalFault(fault) => {
                return BvDecideOutcome::InternalFault(BvDecideInternalFault::Bitblast(fault));
            }
        };
    if is_cancelled(cancellation) {
        return cancelled(BvDecideCheckpoint::Solve);
    }
    match solve_with_cancel(bitblast.cnf(), limits.solver, || is_cancelled(cancellation)) {
        SolverOutcome::Sat {
            artifact,
            statistics,
        } => match independently_validate_counterexample(
            &bitblast,
            artifact,
            statistics,
            limits.solver.schema,
        ) {
            Ok(counterexample) => BvDecideOutcome::Counterexample(Box::new(counterexample)),
            Err(CounterexampleValidationStop::AllocationRefused { requested }) => {
                BvDecideOutcome::Inconclusive(
                    BvDecideInconclusive::CounterexampleAllocationRefused { requested },
                )
            }
            Err(CounterexampleValidationStop::InternalFault(fault)) => {
                BvDecideOutcome::InternalFault(*fault)
            }
        },
        SolverOutcome::Unsat {
            artifact,
            statistics,
        } => {
            if is_cancelled(cancellation) {
                return cancelled(BvDecideCheckpoint::Reflection);
            }
            let reflected = match ReflectedTheoremArtifact::from_bitblast_unsat(
                bitblast,
                artifact,
                theorem_name,
                level_params,
                source_proposition,
                reflected_proof,
                ReflectedTheoremProvenance::new(mode, reproducibility),
            ) {
                Ok(reflected) => reflected,
                Err(error) => {
                    return BvDecideOutcome::InternalFault(
                        BvDecideInternalFault::ReflectedArtifact(error),
                    );
                }
            };
            match publish_reflected_theorem(environment, reflected, limits.reflection, cancellation)
            {
                ReflectedTheoremOutcome::Published(publication) => {
                    let proof_checker_work_units = Some(publication.proof_receipt.work_units);
                    let bitblast = publication.bitblast_facts();
                    BvDecideOutcome::Proved(Box::new(BvDecidePublication {
                        reflection: *publication,
                        telemetry: BvDecideTelemetry {
                            bitblast,
                            solver: statistics,
                            proof_checker_work_units,
                        },
                    }))
                }
                ReflectedTheoremOutcome::Refused(refusal) => {
                    BvDecideOutcome::Refused(BvDecideRefusal::Reflection(refusal))
                }
                ReflectedTheoremOutcome::Inconclusive(inconclusive) => {
                    BvDecideOutcome::Inconclusive(BvDecideInconclusive::Reflection(inconclusive))
                }
                ReflectedTheoremOutcome::InternalFault(fault) => {
                    BvDecideOutcome::InternalFault(BvDecideInternalFault::Reflection(fault))
                }
            }
        }
        SolverOutcome::Inconclusive { cause, statistics } => {
            BvDecideOutcome::Inconclusive(BvDecideInconclusive::Solver { cause, statistics })
        }
        SolverOutcome::InternalFault { fault, statistics } => {
            BvDecideOutcome::InternalFault(BvDecideInternalFault::Solver { fault, statistics })
        }
    }
}
