//! Untrusted arithmetic-engine protocol. The elaborator owns proof replay;
//! a provider supplies data, never an admitted declaration or a proof verdict.
//!
//! Anvil is linked by the embedding facade and passed explicitly in the source
//! scope. This keeps the tactic framework independent of higher-ranked engines.

use fln_bignum::{int::BigInt, nat::BigNat};

pub const OMEGA_CERTIFICATE_VERSION: u32 = 1;
pub const OMEGA_BRANCH_CERTIFICATE_VERSION: u32 = 1;

/// The integer inequality `sum(coeffs[i] * values[i]) <= bound`.
/// Missing trailing coefficients denote zero.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearConstraint {
    pub coeffs: Vec<BigInt>,
    pub bound: BigInt,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OmegaLimits {
    pub max_steps: u64,
    pub max_variables: usize,
    pub max_rows: usize,
    pub max_coefficient_limbs: usize,
    pub max_certificate_bytes: usize,
}

impl Default for OmegaLimits {
    fn default() -> Self {
        Self {
            max_steps: 1_000_000,
            max_variables: 256,
            max_rows: 16_384,
            max_coefficient_limbs: 256,
            max_certificate_bytes: 16 * 1024 * 1024,
        }
    }
}

/// Each parent must precede the step that references it. Combination scales
/// are strictly positive; division uses the positive gcd of the source coefficients
/// and rounds its upper bound down, preserving integer satisfaction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OmegaStep {
    Input {
        index: u32,
    },
    Combine {
        left: u32,
        right: u32,
        left_scale: BigNat,
        right_scale: BigNat,
    },
    DivideGcd {
        source: u32,
    },
}

/// Inputs are retained exactly. Replay must bind them to the reified local
/// hypotheses before using any step; the conclusion must be `0 <= b`, `b < 0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OmegaCertificate {
    pub version: u32,
    pub inputs: Vec<LinearConstraint>,
    pub steps: Vec<OmegaStep>,
    pub conclusion: u32,
}

/// A postorder tree of integer case splits. A split covers the disjoint,
/// exhaustive cases `values[variable] <= cut` and `cut + 1 <= values[variable]`.
/// Child indices must precede their parent. Each leaf binds its linear
/// certificate to the root inputs followed by exactly its path assumptions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OmegaBranchNode {
    Leaf {
        certificate: OmegaCertificate,
    },
    Split {
        variable: u32,
        cut: BigInt,
        le: u32,
        gt: u32,
    },
}

/// Branch certificates have their own version and codec; existing linear
/// certificates retain their V1 representation. The conclusion is the last
/// node and every node belongs to exactly one branch of the tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OmegaBranchCertificate {
    pub version: u32,
    pub inputs: Vec<LinearConstraint>,
    pub nodes: Vec<OmegaBranchNode>,
    pub conclusion: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OmegaResource {
    Steps,
    Variables,
    Rows,
    CoefficientLimbs,
    CertificateBytes,
    Allocation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OmegaInconclusive {
    ResourceLimit {
        resource: OmegaResource,
        limit: u64,
        observed: u64,
    },
    Cancelled,
    IntegerSearchRequired,
}

impl OmegaInconclusive {
    /// Preserve engine stops through the source facade's ordinary nonanswer
    /// channel. Neither an exhausted search nor missing integer elimination is
    /// evidence that the user's proposition is false.
    pub fn into_source_outcome(self) -> fln_core::outcome::Inconclusive {
        use fln_core::diag::{ResourceReason, StructuralUnit};
        use fln_core::outcome::{Inconclusive, ResourceUsage};
        match self {
            Self::Cancelled => Inconclusive::cancelled("source/omega"),
            Self::IntegerSearchRequired => {
                Inconclusive::unsupported("omega integer residue elimination")
            }
            Self::ResourceLimit {
                resource,
                limit,
                observed,
            } => Inconclusive::resource(ResourceUsage {
                reason: match resource {
                    OmegaResource::Steps => ResourceReason::ExecutionSteps,
                    OmegaResource::CertificateBytes => {
                        ResourceReason::Memory { limit_bytes: limit }
                    }
                    _ => ResourceReason::StructuralBudget {
                        unit: StructuralUnit::ProducedNodes,
                    },
                },
                allowed: limit,
                observed,
            })
            .with_progress(format!("source/omega/{resource:?}")),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OmegaOutcome {
    Unsat {
        certificate: OmegaCertificate,
        steps_used: u64,
    },
    UnsatBranches {
        certificate: OmegaBranchCertificate,
        steps_used: u64,
    },
    Sat {
        witness: Vec<BigInt>,
        steps_used: u64,
    },
    Inconclusive {
        reason: OmegaInconclusive,
        steps_used: u64,
    },
}

/// An explicitly supplied, stateless native accelerator. Its output remains
/// untrusted and is replayed into ordinary kernel-checked proof terms.
#[derive(Clone, Copy)]
pub struct ArithmeticProvider(pub fn(&[LinearConstraint], OmegaLimits) -> OmegaOutcome);

impl std::fmt::Debug for ArithmeticProvider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ArithmeticProvider")
    }
}

impl PartialEq for ArithmeticProvider {
    fn eq(&self, other: &Self) -> bool {
        // This is in-process source-scope equality, never an artifact identity.
        std::ptr::fn_addr_eq(self.0, other.0)
    }
}

impl Eq for ArithmeticProvider {}
