//! The deliberately tiny environment used to exercise Athanor's first
//! elaboration seam (bead `fln-5720`; plan §10, §4.3).
//!
//! Parsing, syntax validation, literal decoding, declaration construction, and
//! kernel checking each have one implementation in the crate root. This module
//! owns the one separate concern needed by the executable seed: constructing an
//! environment in which the bounded source types are known, through the same
//! kernel admission, council, and publication capabilities as every other
//! declaration.
//!
//! This is not FrankenLean's real Prelude. Its raw fixture admits an opaque
//! `Nat : Sort 1`; the embeddable source constructor additionally admits opaque
//! `String : Sort 1`, exact `Nat.add`/`Nat.sub`/`Nat.mul`, and the checked
//! `String.append`/`String.length`/`String.utf8ByteSize` extern signatures. The
//! types are enough to resolve literals, while those checked rows let the
//! compiler reach Golem's matching intrinsic implementations; no constructor or
//! eliminator is implied. The real inductive blocks belong to inductive
//! elaboration and Prelude ingestion.
//!
//! Every refusal and non-answer remains typed. In particular, a budget stop or
//! internal fault while constructing this environment is never rendered as a
//! kernel rejection (FL-INV-07).

use fln_core::expr::{BinderInfo, Expr};
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

/// Construct the equally opaque `String : Sort 1` candidate needed to type
/// string literals at the bounded source front door.
///
/// This grants no constructor, eliminator, or runtime authority. The embeddable
/// engine admits it through the same K1 plus independent-checker council as the
/// Nat seed before exposing a successor.
pub fn string_seed_declaration() -> Declaration {
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::from_components(["String"]),
            level_params: Vec::new(),
            type_: Expr::sort(Level::one()),
        },
        is_unsafe: false,
    })
}

fn nat_binary_seed_declaration(operation: &str) -> Declaration {
    let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::from_components(["Nat", operation]),
            level_params: Vec::new(),
            type_: Expr::forall_e(
                Name::from_components(["left"]),
                nat.clone(),
                Expr::forall_e(
                    Name::from_components(["right"]),
                    nat.clone(),
                    nat,
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        },
        is_unsafe: false,
    })
}

/// Construct the exact `Nat.add : Nat -> Nat -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_add_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("add")
}

/// Construct the exact `Nat.sub : Nat -> Nat -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_sub_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("sub")
}

/// Construct the exact `Nat.mul : Nat -> Nat -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_mul_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("mul")
}

/// Construct the exact `String.append : String -> String -> String` candidate
/// recognized by the bounded compiler bridge.
pub fn string_append_seed_declaration() -> Declaration {
    let string = Expr::const_(Name::from_components(["String"]), Vec::new());
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::from_components(["String", "append"]),
            level_params: Vec::new(),
            type_: Expr::forall_e(
                Name::from_components(["left"]),
                string.clone(),
                Expr::forall_e(
                    Name::from_components(["right"]),
                    string.clone(),
                    string,
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        },
        is_unsafe: false,
    })
}

fn string_to_nat_seed_declaration(operation: &str) -> Declaration {
    let string = Expr::const_(Name::from_components(["String"]), Vec::new());
    let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::from_components(["String", operation]),
            level_params: Vec::new(),
            type_: Expr::forall_e(
                Name::from_components(["value"]),
                string,
                nat,
                BinderInfo::Default,
            ),
        },
        is_unsafe: false,
    })
}

/// Construct the exact `String.length : String -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn string_length_seed_declaration() -> Declaration {
    string_to_nat_seed_declaration("length")
}

/// Construct the exact `String.utf8ByteSize : String -> Nat` candidate
/// recognized by the bounded compiler bridge.
pub fn string_utf8_byte_size_seed_declaration() -> Declaration {
    string_to_nat_seed_declaration("utf8ByteSize")
}

/// Return the exact source-seed declaration for an executable intrinsic name.
///
/// This is an allowlist, not a shape-based constructor: another generated row
/// with the same apparent type receives no source or runtime authority.
pub fn source_intrinsic_seed_declaration(name: &Name) -> Option<Declaration> {
    if name == &Name::from_components(["Nat", "add"]) {
        Some(nat_add_seed_declaration())
    } else if name == &Name::from_components(["Nat", "sub"]) {
        Some(nat_sub_seed_declaration())
    } else if name == &Name::from_components(["Nat", "mul"]) {
        Some(nat_mul_seed_declaration())
    } else if name == &Name::from_components(["String", "append"]) {
        Some(string_append_seed_declaration())
    } else if name == &Name::from_components(["String", "length"]) {
        Some(string_length_seed_declaration())
    } else if name == &Name::from_components(["String", "utf8ByteSize"]) {
        Some(string_utf8_byte_size_seed_declaration())
    } else {
        None
    }
}

/// The exact declaration sequence required by the bounded Nat/String source
/// frontend. Order is part of the deterministic seed contract: both types must
/// exist before the intrinsic signature can be admitted.
pub fn source_seed_declarations() -> [Declaration; 8] {
    [
        nat_seed_declaration(),
        string_seed_declaration(),
        nat_add_seed_declaration(),
        nat_sub_seed_declaration(),
        nat_mul_seed_declaration(),
        string_append_seed_declaration(),
        string_length_seed_declaration(),
        string_utf8_byte_size_seed_declaration(),
    ]
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

    #[test]
    fn source_seed_orders_types_before_the_exact_intrinsic_signatures() {
        let declarations = source_seed_declarations();
        assert_eq!(declarations[0], nat_seed_declaration());
        assert_eq!(declarations[1], string_seed_declaration());
        assert_eq!(declarations[2], nat_add_seed_declaration());
        assert_eq!(declarations[3], nat_sub_seed_declaration());
        assert_eq!(declarations[4], nat_mul_seed_declaration());
        assert_eq!(declarations[5], string_append_seed_declaration());
        assert_eq!(declarations[6], string_length_seed_declaration());
        assert_eq!(declarations[7], string_utf8_byte_size_seed_declaration());
        assert!(
            source_intrinsic_seed_declaration(&Name::from_components(["Nat", "div"])).is_none(),
            "an unimplemented generated row is not source authority"
        );
    }
}
