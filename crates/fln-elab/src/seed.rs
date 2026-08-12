//! The deliberately tiny environment used to exercise Athanor's first
//! elaboration seam (bead `fln-5720`; plan §10, §4.3).
//!
//! Parsing, syntax validation, literal decoding, declaration construction, and
//! kernel checking each have one implementation in the crate root. This module
//! owns the one separate concern needed by the executable seed: constructing an
//! environment in which `Nat` is known, through the same kernel admission,
//! council, and publication capabilities as every other declaration.
//!
//! This is not FrankenLean's real Prelude. It admits an opaque `Nat : Sort 1`
//! axiom, enough for the kernel to resolve a natural literal's synthesized type
//! but not enough to compute, eliminate, or inspect a natural. The real
//! inductive block belongs to inductive elaboration and Prelude ingestion.
//!
//! Every refusal and non-answer remains typed. In particular, a budget stop or
//! internal fault while constructing this environment is never rendered as a
//! kernel rejection (FL-INV-07).

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
use fln_env::constants::{AxiomVal, ConstantVal};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, RejectClass};

/// Why the minimal seed environment could not be constructed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeedEnvironmentError {
    KernelRejected { class: RejectClass, message: String },
    CouncilHalted { summary: String },
    DuplicateName { name: Name },
    UnexpectedPublication { detail: &'static str },
    Inconclusive(Inconclusive),
    InternalFault(InternalFault),
}

impl core::fmt::Display for SeedEnvironmentError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SeedEnvironmentError::KernelRejected { class, message } => {
                write!(
                    f,
                    "kernel rejected the seed Nat axiom ({class:?}): {message}"
                )
            }
            SeedEnvironmentError::CouncilHalted { summary } => {
                write!(f, "seed Nat council halted: {summary}")
            }
            SeedEnvironmentError::DuplicateName { name } => {
                write!(
                    f,
                    "seed environment already contains {}",
                    name.to_display_string()
                )
            }
            SeedEnvironmentError::UnexpectedPublication { detail } => {
                write!(f, "unexpected seed publication result: {detail}")
            }
            SeedEnvironmentError::Inconclusive(inconclusive) => {
                write!(
                    f,
                    "seed environment construction was inconclusive: {inconclusive:?}"
                )
            }
            SeedEnvironmentError::InternalFault(fault) => {
                write!(f, "seed environment construction faulted: {fault:?}")
            }
        }
    }
}

impl std::error::Error for SeedEnvironmentError {}

/// Construct the seed's single candidate declaration without admitting it.
///
/// Keeping the candidate construction here gives the raw elaborator fixture
/// and the embeddable facade one source of truth while leaving publication
/// authority with their respective admission paths.
pub fn nat_seed_declaration() -> Declaration {
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::from_components(["Nat"]),
            level_params: Vec::new(),
            type_: Expr::sort(Level::one()),
        },
        is_unsafe: false,
    })
}

/// Build the seed's minimal environment.
///
/// The kernel refuses a
/// definition whose type names a constant the environment does not hold —
/// `unknown constant Nat`. That refusal is the kernel doing its job (FL-INV-02),
/// so even this bounded fixture goes through admission and publication.
pub fn bootstrap_nat_environment(budget: Budget) -> Result<Environment, SeedEnvironmentError> {
    let env = Environment::new();
    let nat_axiom = nat_seed_declaration();

    let checked = match admit(&env, nat_axiom, budget) {
        Outcome::Complete(admitted) => match convene(&Council::nobody_was_asked(), admitted) {
            CouncilOutcome::Agreed(checked) => checked,
            CouncilOutcome::KernelRejected { class, message, .. } => {
                return Err(SeedEnvironmentError::KernelRejected { class, message });
            }
            CouncilOutcome::Halted(halt) => {
                return Err(SeedEnvironmentError::CouncilHalted {
                    summary: halt.summary(),
                });
            }
        },
        Outcome::Inconclusive(inconclusive) => {
            return Err(SeedEnvironmentError::Inconclusive(inconclusive));
        }
        Outcome::InternalFault(fault) => {
            return Err(SeedEnvironmentError::InternalFault(fault));
        }
    };

    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(publication))) => {
            Ok(publication.environment)
        }
        Outcome::Complete(Published::Committed(DeclarationCommitted::DuplicateName { name }))
        | Outcome::Complete(Published::DuplicateName { name }) => {
            Err(SeedEnvironmentError::DuplicateName { name })
        }
        Outcome::Complete(Published::BlockCommitted(_)) => {
            Err(SeedEnvironmentError::UnexpectedPublication {
                detail: "the single Nat axiom published as a block",
            })
        }
        Outcome::Inconclusive(inconclusive) => {
            Err(SeedEnvironmentError::Inconclusive(inconclusive))
        }
        Outcome::InternalFault(fault) => Err(SeedEnvironmentError::InternalFault(fault)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bootstrap_publishes_only_the_opaque_nat_seed() {
        let environment =
            bootstrap_nat_environment(Budget::DEFAULT).expect("the bounded Nat seed publishes");
        assert!(environment.contains(&Name::from_components(["Nat"])));
        assert_eq!(environment.len(), 1);
    }
}
