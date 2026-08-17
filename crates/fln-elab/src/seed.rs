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
//! `String : Sort 1`, the pin-shaped `Bool` inductive block, an explicit
//! allowlist of checked scalar Nat operations, and the checked String extern
//! signatures. Those checked rows let the compiler reach Golem's matching
//! intrinsic implementations. Bool's two nullary constructors are live; source
//! pattern syntax, recursor elaboration, Nat/String constructors, and the rest
//! of Prelude still belong to later ingestion work.
//!
//! Every refusal and non-answer remains typed. In particular, a budget stop or
//! internal fault while constructing this environment is never rendered as a
//! kernel rejection (FL-INV-07).

use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
use fln_env::constants::{
    AxiomVal, ConstantVal, ConstructorVal, InductiveVal, RecursorRule, RecursorVal,
};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, RejectClass};
use fln_kernel::{Declaration, InductiveBlock};

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

/// Construct the pin-shaped `Bool` inductive block used by the bounded source
/// facade.
///
/// The block contains the exact type, nullary constructors, and generated
/// recursor names and shapes from `Init.Prelude`. It is still only one tiny
/// Prelude slice: source pattern syntax, recursor elaboration, and the wider
/// Bool library remain outside this facade.
pub fn bool_seed_declaration() -> Declaration {
    let bool_name = Name::from_components(["Bool"]);
    let false_name = Name::from_components(["Bool", "false"]);
    let true_name = Name::from_components(["Bool", "true"]);
    let rec_name = Name::from_components(["Bool", "rec"]);
    let bool_type = || Expr::const_(bool_name.clone(), Vec::new());
    let false_value = || Expr::const_(false_name.clone(), Vec::new());
    let true_value = || Expr::const_(true_name.clone(), Vec::new());
    let bvar = |index| Expr::bvar(index).expect("the fixed Bool recursor indices fit");
    let universe_name = Name::from_components(["u"]);
    let universe = Level::param(universe_name.clone());
    let motive_type = Expr::forall_e(
        Name::from_components(["t"]),
        bool_type(),
        Expr::sort(universe.clone()),
        BinderInfo::Default,
    );
    let recursor_type = Expr::forall_e(
        Name::from_components(["motive"]),
        motive_type.clone(),
        Expr::forall_e(
            Name::from_components(["false"]),
            Expr::app(bvar(0), false_value()),
            Expr::forall_e(
                Name::from_components(["true"]),
                Expr::app(bvar(1), true_value()),
                Expr::forall_e(
                    Name::from_components(["t"]),
                    bool_type(),
                    Expr::app(bvar(3), bvar(0)),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let rule_rhs = |selected| {
        Expr::lam(
            Name::from_components(["motive"]),
            motive_type.clone(),
            Expr::lam(
                Name::from_components(["false"]),
                Expr::app(bvar(0), false_value()),
                Expr::lam(
                    Name::from_components(["true"]),
                    Expr::app(bvar(1), true_value()),
                    bvar(selected),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    };

    Declaration::Inductive(InductiveBlock {
        types: vec![InductiveVal {
            base: ConstantVal {
                name: bool_name.clone(),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![bool_name.clone()],
            ctors: vec![false_name.clone(), true_name.clone()],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }],
        ctors: vec![
            ConstructorVal {
                base: ConstantVal {
                    name: false_name.clone(),
                    level_params: Vec::new(),
                    type_: bool_type(),
                },
                induct: bool_name.clone(),
                cidx: 0,
                num_params: 0,
                num_fields: 0,
                is_unsafe: false,
            },
            ConstructorVal {
                base: ConstantVal {
                    name: true_name.clone(),
                    level_params: Vec::new(),
                    type_: bool_type(),
                },
                induct: bool_name.clone(),
                cidx: 1,
                num_params: 0,
                num_fields: 0,
                is_unsafe: false,
            },
        ],
        recursors: vec![RecursorVal {
            base: ConstantVal {
                name: rec_name,
                level_params: vec![universe_name],
                type_: recursor_type,
            },
            all: vec![bool_name],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 2,
            rules: vec![
                RecursorRule {
                    ctor: false_name.clone(),
                    nfields: 0,
                    rhs: rule_rhs(1),
                },
                RecursorRule {
                    ctor: true_name.clone(),
                    nfields: 0,
                    rhs: rule_rhs(0),
                },
            ],
            k: false,
            is_unsafe: false,
        }],
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

fn nat_unary_seed_declaration(operation: &str) -> Declaration {
    let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::from_components(["Nat", operation]),
            level_params: Vec::new(),
            type_: Expr::forall_e(
                Name::from_components(["value"]),
                nat.clone(),
                nat,
                BinderInfo::Default,
            ),
        },
        is_unsafe: false,
    })
}

fn nat_binary_to_bool_seed_declaration(operation: &str) -> Declaration {
    let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
    let bool_ = Expr::const_(Name::from_components(["Bool"]), Vec::new());
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::from_components(["Nat", operation]),
            level_params: Vec::new(),
            type_: Expr::forall_e(
                Name::from_components(["left"]),
                nat.clone(),
                Expr::forall_e(
                    Name::from_components(["right"]),
                    nat,
                    bool_,
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

/// Construct the exact `Nat.div : Nat -> Nat -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_div_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("div")
}

/// Construct the exact `Nat.gcd : Nat -> Nat -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_gcd_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("gcd")
}

/// Construct the exact `Nat.land : Nat -> Nat -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_land_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("land")
}

/// Construct the exact `Nat.log2 : Nat -> Nat` candidate recognized by the
/// bounded compiler bridge.
pub fn nat_log2_seed_declaration() -> Declaration {
    nat_unary_seed_declaration("log2")
}

/// Construct the exact `Nat.lor : Nat -> Nat -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_lor_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("lor")
}

/// Construct the exact `Nat.mod : Nat -> Nat -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_mod_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("mod")
}

/// Construct the exact `Nat.pow : Nat -> Nat -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_pow_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("pow")
}

/// Construct the exact `Nat.pred : Nat -> Nat` candidate recognized by the
/// bounded compiler bridge.
pub fn nat_pred_seed_declaration() -> Declaration {
    nat_unary_seed_declaration("pred")
}

/// Construct the exact `Nat.shiftLeft : Nat -> Nat -> Nat` candidate recognized
/// by the bounded compiler bridge.
pub fn nat_shift_left_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("shiftLeft")
}

/// Construct the exact `Nat.shiftRight : Nat -> Nat -> Nat` candidate
/// recognized by the bounded compiler bridge.
pub fn nat_shift_right_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("shiftRight")
}

/// Construct the exact `Nat.xor : Nat -> Nat -> Nat` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_xor_seed_declaration() -> Declaration {
    nat_binary_seed_declaration("xor")
}

/// Construct the exact `Nat.beq : Nat -> Nat -> Bool` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_beq_seed_declaration() -> Declaration {
    nat_binary_to_bool_seed_declaration("beq")
}

/// Construct the exact `Nat.ble : Nat -> Nat -> Bool` candidate recognized by
/// the bounded compiler bridge.
pub fn nat_ble_seed_declaration() -> Declaration {
    nat_binary_to_bool_seed_declaration("ble")
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

/// Construct the exact `String.decEq : String -> String -> Bool` candidate
/// recognized by the bounded compiler bridge.
pub fn string_dec_eq_seed_declaration() -> Declaration {
    let string = Expr::const_(Name::from_components(["String"]), Vec::new());
    let bool_ = Expr::const_(Name::from_components(["Bool"]), Vec::new());
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::from_components(["String", "decEq"]),
            level_params: Vec::new(),
            type_: Expr::forall_e(
                Name::from_components(["left"]),
                string.clone(),
                Expr::forall_e(
                    Name::from_components(["right"]),
                    string,
                    bool_,
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        },
        is_unsafe: false,
    })
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
    } else if name == &Name::from_components(["Nat", "div"]) {
        Some(nat_div_seed_declaration())
    } else if name == &Name::from_components(["Nat", "gcd"]) {
        Some(nat_gcd_seed_declaration())
    } else if name == &Name::from_components(["Nat", "land"]) {
        Some(nat_land_seed_declaration())
    } else if name == &Name::from_components(["Nat", "log2"]) {
        Some(nat_log2_seed_declaration())
    } else if name == &Name::from_components(["Nat", "lor"]) {
        Some(nat_lor_seed_declaration())
    } else if name == &Name::from_components(["Nat", "mod"]) {
        Some(nat_mod_seed_declaration())
    } else if name == &Name::from_components(["Nat", "pow"]) {
        Some(nat_pow_seed_declaration())
    } else if name == &Name::from_components(["Nat", "pred"]) {
        Some(nat_pred_seed_declaration())
    } else if name == &Name::from_components(["Nat", "shiftLeft"]) {
        Some(nat_shift_left_seed_declaration())
    } else if name == &Name::from_components(["Nat", "shiftRight"]) {
        Some(nat_shift_right_seed_declaration())
    } else if name == &Name::from_components(["Nat", "xor"]) {
        Some(nat_xor_seed_declaration())
    } else if name == &Name::from_components(["Nat", "beq"]) {
        Some(nat_beq_seed_declaration())
    } else if name == &Name::from_components(["Nat", "ble"]) {
        Some(nat_ble_seed_declaration())
    } else if name == &Name::from_components(["String", "append"]) {
        Some(string_append_seed_declaration())
    } else if name == &Name::from_components(["String", "length"]) {
        Some(string_length_seed_declaration())
    } else if name == &Name::from_components(["String", "utf8ByteSize"]) {
        Some(string_utf8_byte_size_seed_declaration())
    } else if name == &Name::from_components(["String", "decEq"]) {
        Some(string_dec_eq_seed_declaration())
    } else {
        None
    }
}

/// The exact declaration sequence required by the bounded Nat/String/Bool
/// source frontend. Order is part of the deterministic seed contract: the
/// scalar type rows and Bool block must exist before intrinsic signatures can
/// be admitted.
pub fn source_seed_declarations() -> [Declaration; 23] {
    [
        nat_seed_declaration(),
        string_seed_declaration(),
        bool_seed_declaration(),
        nat_add_seed_declaration(),
        nat_sub_seed_declaration(),
        nat_mul_seed_declaration(),
        nat_div_seed_declaration(),
        nat_gcd_seed_declaration(),
        nat_land_seed_declaration(),
        nat_log2_seed_declaration(),
        nat_lor_seed_declaration(),
        nat_mod_seed_declaration(),
        nat_pow_seed_declaration(),
        nat_pred_seed_declaration(),
        nat_shift_left_seed_declaration(),
        nat_shift_right_seed_declaration(),
        nat_xor_seed_declaration(),
        string_append_seed_declaration(),
        string_length_seed_declaration(),
        string_utf8_byte_size_seed_declaration(),
        nat_beq_seed_declaration(),
        nat_ble_seed_declaration(),
        string_dec_eq_seed_declaration(),
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
        assert_eq!(declarations[2], bool_seed_declaration());
        assert_eq!(declarations[3], nat_add_seed_declaration());
        assert_eq!(declarations[4], nat_sub_seed_declaration());
        assert_eq!(declarations[5], nat_mul_seed_declaration());
        assert_eq!(declarations[6], nat_div_seed_declaration());
        assert_eq!(declarations[7], nat_gcd_seed_declaration());
        assert_eq!(declarations[8], nat_land_seed_declaration());
        assert_eq!(declarations[9], nat_log2_seed_declaration());
        assert_eq!(declarations[10], nat_lor_seed_declaration());
        assert_eq!(declarations[11], nat_mod_seed_declaration());
        assert_eq!(declarations[12], nat_pow_seed_declaration());
        assert_eq!(declarations[13], nat_pred_seed_declaration());
        assert_eq!(declarations[14], nat_shift_left_seed_declaration());
        assert_eq!(declarations[15], nat_shift_right_seed_declaration());
        assert_eq!(declarations[16], nat_xor_seed_declaration());
        assert_eq!(declarations[17], string_append_seed_declaration());
        assert_eq!(declarations[18], string_length_seed_declaration());
        assert_eq!(declarations[19], string_utf8_byte_size_seed_declaration());
        assert_eq!(declarations[20], nat_beq_seed_declaration());
        assert_eq!(declarations[21], nat_ble_seed_declaration());
        assert_eq!(declarations[22], string_dec_eq_seed_declaration());
        assert!(
            source_intrinsic_seed_declaration(&Name::from_components(["Nat", "modCore"])).is_none(),
            "an unimplemented generated row is not source authority"
        );
    }

    #[test]
    fn bool_seed_is_the_exact_two_constructor_inductive_block() {
        let Declaration::Inductive(block) = bool_seed_declaration() else {
            panic!("the Bool seed must not remain an opaque axiom");
        };
        assert_eq!(block.types.len(), 1);
        assert_eq!(block.ctors.len(), 2);
        assert_eq!(block.recursors.len(), 1);

        let bool_name = Name::from_components(["Bool"]);
        let false_name = Name::from_components(["Bool", "false"]);
        let true_name = Name::from_components(["Bool", "true"]);
        let bool_type = Expr::const_(bool_name.clone(), Vec::new());
        let inductive = &block.types[0];
        assert_eq!(inductive.base.name, bool_name);
        assert_eq!(inductive.base.type_, Expr::sort(Level::one()));
        assert_eq!(inductive.ctors, vec![false_name.clone(), true_name.clone()]);
        assert_eq!(inductive.num_params, 0);
        assert_eq!(inductive.num_indices, 0);
        assert!(!inductive.is_rec);

        for (constructor, expected_name, expected_index) in [
            (&block.ctors[0], false_name.clone(), 0),
            (&block.ctors[1], true_name.clone(), 1),
        ] {
            assert_eq!(constructor.base.name, expected_name);
            assert_eq!(constructor.base.type_, bool_type);
            assert_eq!(constructor.induct, bool_name);
            assert_eq!(constructor.cidx, expected_index);
            assert_eq!(constructor.num_params, 0);
            assert_eq!(constructor.num_fields, 0);
        }

        let recursor = &block.recursors[0];
        assert_eq!(recursor.base.name, Name::from_components(["Bool", "rec"]));
        assert_eq!(recursor.rules.len(), 2);
        assert_eq!(recursor.rules[0].ctor, false_name);
        assert_eq!(recursor.rules[1].ctor, true_name);
        assert_eq!(recursor.rules[0].nfields, 0);
        assert_eq!(recursor.rules[1].nfields, 0);
    }
}
