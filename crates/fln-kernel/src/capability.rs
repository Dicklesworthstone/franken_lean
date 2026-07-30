//! The checked-declaration capability (bead `fln-yswb`; D6, FL-INV-02, FL-INV-06).
//!
//! # The hole this closes
//!
//! [`crate::check`] returns a [`Verdict`] whose `Accepted` arm carries only a
//! [`Consumption`], while `fln_env::Environment::plan_add_decl` accepts a raw
//! `ConstantInfo`. Nothing in the type system connects the two, so **checking
//! declaration A and publishing declaration B is representable** — and an
//! invariant that is merely tested against is audited, not enforced.
//!
//! [`CheckedDecl`] makes it unrepresentable. It is produced only by [`admit`],
//! only on acceptance, and it is the only input [`CheckedDecl::publish`]
//! accepts. There is no route from a rejection, an inconclusive, or an internal
//! fault to a value of this type.
//!
//! # Why it cannot be forged outside this crate
//!
//! Every field is private, and one of them has a **private type** ([`Seal`])
//! that no other crate can name. A struct-literal expression outside
//! `fln-kernel` therefore cannot be written even if every other field were made
//! public later, and there is no constructor, no `Default`, no `From`, and no
//! deserialisation. D6 says nothing but the kernel may admit a constant; this
//! is that sentence expressed as a type rather than as a convention.
//!
//! # Why the base environment cannot be substituted or moved out from under it
//!
//! The capability **borrows** the base environment it was checked against, and
//! [`CheckedDecl::publish`] takes no environment parameter — it publishes into
//! the environment it holds. So there is no argument to get wrong, the borrow
//! checker refuses any attempt to move or mutate that environment while the
//! capability is alive, and a capability cannot outlive its base. The binding
//! costs nothing: no digest of a 15,000-constant environment is taken.
//!
//! # Why it cannot be replayed
//!
//! [`CheckedDecl`] is deliberately **not** `Clone` and **not** `Copy`, and
//! `publish` consumes `self` by value. A second publication from one check is a
//! use-after-move, refused at compile time rather than at run time.
//!
//! # What this is not
//!
//! It is not a second admission authority. [`crate::check`] answers a question
//! and cannot admit anything; [`admit`] is the only producer of a capability
//! and [`CheckedDecl::publish`] its only consumer. The raw
//! `Environment::add_decl` / `plan_add_decl` surface still exists in `fln-env`
//! and is still reachable — closing that is a separate bead, because `fln-env`
//! sits BELOW `fln-kernel` in the crate graph and cannot depend on it. This
//! type is the higher-layer handoff the graph permits.

use crate::verdict::{Consumption, RejectClass, Verdict};
use crate::{Declaration, check};
use fln_core::name::Name;
use fln_core::outcome::{InternalFault, Outcome};
use fln_env::constants::ConstantInfo;
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, DeclarationPlan, Environment};
use fln_env::modules::CancellationProbe;
use fln_env::pmap::CollisionBudget;

/// Un-nameable outside this module. Its only purpose is to make
/// [`CheckedDecl`] unconstructible anywhere else, now and after any later edit
/// that widens the other fields.
struct Seal;

/// Proof that THIS declaration was accepted against THIS base environment.
///
/// Not `Clone`, not `Copy`, not serialisable, not constructible outside
/// `fln-kernel`. See the module documentation for why each of those matters.
pub struct CheckedDecl<'env> {
    /// The exact base the kernel checked against. Borrowed, so it cannot be
    /// substituted, moved, or mutated while this capability lives.
    base: &'env Environment,
    /// The exact declaration the kernel accepted. Publication uses this and
    /// never a caller-supplied one, so "check A, publish B" has no expression.
    decl: Declaration,
    consumption: Consumption,
    /// The bound the accepting check ran under, with its calibration attached
    /// (bead `franken_lean-4o3n`). Retained because a council cannot classify a
    /// seat's resource stop — or refuse to, when the two bounds are not
    /// comparable — without knowing what the kernel's own bound was.
    budget: crate::Budget,
    _seal: Seal,
}

/// A kernel acceptance that has not yet been put to a council (bead
/// `fln-glml`).
///
/// # Why the acceptance and the publication right are different values
///
/// [`admit`] used to hand back the [`CheckedDecl`] itself, and publishing
/// without convening a council was then a matter of simply not calling
/// [`convene`](crate::council::convene). That is not hypothetical: the one
/// production publisher in the tree, `fln_verdict::reflection`, did exactly
/// that — obtained the capability and published, with no `Council` anywhere in
/// the file. Nothing was misbehaving, because an empty council agrees
/// vacuously and the outcome was identical. The defect was that **"policy
/// decided nobody was asked" and "nobody thought to ask" were the same
/// program**.
///
/// `fln-uc44` spelled [`Council::nobody_was_asked`](crate::council::Council::nobody_was_asked)
/// so the empty case would be visible at the call site. It made that visibility
/// *available*; this type makes it *required*. The empty council stays legal and
/// stays vacuous — what changes is that a publication site can no longer omit
/// the question.
///
/// # What it deliberately exposes, and what it does not
///
/// The reporting accessors are here because a caller that must decide *which*
/// council to convene needs to know what it is convening about. What is not
/// here is any route to the capability: [`CheckedDecl`] leaves this type only
/// through `convene`, in the same crate, via a `pub(crate)` move.
///
/// Boxed, which is not decoration. [`CheckedDecl`] began carrying the
/// calibrated [`crate::Budget`] it was checked under (bead
/// `franken_lean-4o3n`), which took the accepted arm far past the rejected one
/// and made every [`Admitted`] value pay that width. It is boxed rather than
/// `#[allow]`ed because FLN-STRUCT-030 admits no `allow` attribute inside
/// `fln-kernel`: the reviewed builtin inventory is `cfg`, `derive`, `forbid`
/// and `test`, so silencing a lint here is not an option the kernel has.
pub struct Reviewable<'env> {
    checked: Box<CheckedDecl<'env>>,
}

impl<'env> Reviewable<'env> {
    /// The name the kernel accepted, for choosing a council and for the record.
    pub fn name(&self) -> Option<&Name> {
        self.checked.name()
    }

    /// What the accepting check cost.
    pub fn consumption(&self) -> Consumption {
        self.checked.consumption()
    }

    /// The bound the accepting check ran under, carrying its calibration — what
    /// a council's seats must be established comparable against (bead
    /// `franken_lean-4o3n`).
    pub fn budget(&self) -> crate::Budget {
        self.checked.budget()
    }

    /// The one exit, and it is `pub(crate)`: only
    /// [`convene`](crate::council::convene) can turn a reviewed acceptance into
    /// a publication right.
    pub(crate) fn into_checked(self) -> CheckedDecl<'env> {
        *self.checked
    }
}

/// What [`admit`] concluded.
///
/// The accepted arm carries a [`Reviewable`], **not** a publication right: see
/// that type for why the two are different values.
pub enum Admitted<'env> {
    Accepted(Reviewable<'env>),
    Rejected {
        class: RejectClass,
        message: String,
        consumption: Consumption,
    },
}

/// What a publication did. Every arm that is not `Committed` published nothing.
#[derive(Debug)]
pub enum Published {
    /// The transaction completed and the new environment is authoritative.
    Committed(DeclarationCommitted),
    /// The base already holds this name. Nothing published.
    DuplicateName { name: Name },
    /// Every member of one kernel-checked block committed, and only the final
    /// environment is exposed.
    BlockCommitted(BlockPublication),
}

/// The atomic publication of one multi-constant declaration.
///
/// `names` preserves the declaration's source order for receipts and
/// diagnostics. No intermediate environment is retained here: a caller can
/// either carry the complete block forward or carry none of it.
#[derive(Debug, Clone)]
pub struct BlockPublication {
    /// The one immutable environment containing the complete checked block.
    pub environment: Environment,
    /// Every published constant name, in the block's checked order.
    pub names: Vec<Name>,
}

/// The constants one checked declaration is allowed to publish.
///
/// Keeping the single/block distinction after moving the declaration matters:
/// a one-member mutual block is still one block authority transition, not a
/// single declaration that happened to arrive in a vector.
enum PublicationUnits {
    Single(ConstantInfo),
    Block(Vec<ConstantInfo>),
}

fn publication_units(decl: Declaration) -> PublicationUnits {
    match decl {
        Declaration::Axiom(v) => PublicationUnits::Single(ConstantInfo::Axiom(v)),
        Declaration::Defn(v) => PublicationUnits::Single(ConstantInfo::Defn(v)),
        Declaration::Thm(v) => PublicationUnits::Single(ConstantInfo::Thm(v)),
        Declaration::Opaque(v) => PublicationUnits::Single(ConstantInfo::Opaque(v)),
        Declaration::Mutual(definitions) => {
            PublicationUnits::Block(definitions.into_iter().map(ConstantInfo::Defn).collect())
        }
        Declaration::Inductive(block) => {
            let mut constants = Vec::new();
            constants.extend(block.types.into_iter().map(ConstantInfo::Induct));
            constants.extend(block.ctors.into_iter().map(ConstantInfo::Ctor));
            constants.extend(block.recursors.into_iter().map(ConstantInfo::Rec));
            PublicationUnits::Block(constants)
        }
        Declaration::Quotient(declarations) => {
            PublicationUnits::Block(declarations.into_iter().map(ConstantInfo::Quot).collect())
        }
    }
}

/// The single admission authority: check, and on acceptance mint the capability
/// that publication requires.
///
/// Takes the declaration **by value** so the capability owns exactly what was
/// checked; a caller that keeps a copy cannot make the capability describe it.
pub fn admit<'env>(
    base: &'env Environment,
    decl: Declaration,
    budget: crate::Budget,
) -> Outcome<Admitted<'env>> {
    match check(base, &decl, budget) {
        Outcome::Complete(Verdict::Accepted { consumption }) => {
            Outcome::complete(Admitted::Accepted(Reviewable {
                checked: Box::new(CheckedDecl {
                    base,
                    decl,
                    consumption,
                    budget,
                    _seal: Seal,
                }),
            }))
        }
        Outcome::Complete(Verdict::Rejected {
            class,
            message,
            consumption,
        }) => Outcome::complete(Admitted::Rejected {
            class,
            message,
            consumption,
        }),
        // A non-answer is propagated unchanged and mints nothing. FL-INV-07:
        // inconclusive is never promoted to acceptance OR rejection, and here
        // it is additionally never promoted to a publication right. The same
        // holds for an internal fault, which is OUR accounting failing and is
        // even further from a licence to publish.
        Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
        Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
    }
}

impl<'env> CheckedDecl<'env> {
    /// What the accepting check cost.
    pub fn consumption(&self) -> Consumption {
        self.consumption
    }

    /// The bound the accepting check ran under, carrying its calibration.
    pub fn budget(&self) -> crate::Budget {
        self.budget
    }

    /// The name this capability authorises, for reporting only.
    pub fn name(&self) -> Option<&Name> {
        self.decl.name()
    }

    /// Publish, consuming the capability.
    ///
    /// Takes no environment: it publishes into the base it was checked against.
    /// That is what makes substitution and replay-on-a-moved-base
    /// inexpressible rather than merely detected — there is no argument to get
    /// wrong. `fln-env`'s own plan/commit discipline still revalidates the base
    /// immediately before publication, so this composes with that check rather
    /// than replacing it.
    pub fn publish(
        self,
        budget: DeclarationBudget,
        collisions: CollisionBudget,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Published> {
        let CheckedDecl {
            base,
            decl,
            consumption: _,
            budget: _,
            _seal: _,
        } = self;
        match publication_units(decl) {
            PublicationUnits::Single(info) => {
                match base.plan_add_decl(info, budget, collisions, cancellation) {
                    Outcome::Complete(DeclarationPlan::Prepared(plan)) => {
                        match plan.commit(base, cancellation) {
                            Outcome::Complete(committed) => {
                                Outcome::complete(Published::Committed(committed))
                            }
                            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                        }
                    }
                    Outcome::Complete(DeclarationPlan::DuplicateName { name }) => {
                        Outcome::complete(Published::DuplicateName { name })
                    }
                    Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                }
            }
            PublicationUnits::Block(constants) => {
                publish_block(base, constants, budget, collisions, cancellation)
            }
        }
    }
}

/// Publish one already-checked block without ever exposing an accepted prefix.
///
/// Each `plan_add_decl`/`commit` pair produces an immutable staged environment.
/// Those values remain private locals until every member succeeds; duplicate,
/// resource, cancellation, and internal-fault paths drop the staged value and
/// return no environment. The existing declaration and collision budgets apply
/// to each member exactly as they do to a single declaration, while the kernel
/// check that minted this capability already bounded and accepted the block as
/// a unit.
fn publish_block(
    base: &Environment,
    constants: Vec<ConstantInfo>,
    budget: DeclarationBudget,
    collisions: CollisionBudget,
    cancellation: Option<&dyn CancellationProbe>,
) -> Outcome<Published> {
    if constants.is_empty() {
        return Outcome::InternalFault(InternalFault::new(
            "FL-INV-02",
            "the kernel accepted a block with no constants to publish",
        ));
    }

    let mut staged = base.clone();
    let mut names = Vec::with_capacity(constants.len());
    for info in constants {
        let name = info.name().clone();
        let plan = match staged.plan_add_decl(info, budget, collisions, cancellation) {
            Outcome::Complete(DeclarationPlan::Prepared(plan)) => plan,
            Outcome::Complete(DeclarationPlan::DuplicateName { name }) => {
                return Outcome::complete(Published::DuplicateName { name });
            }
            Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };
        match plan.commit(&staged, cancellation) {
            Outcome::Complete(DeclarationCommitted::Published(publication)) => {
                staged = publication.environment;
                names.push(name);
            }
            Outcome::Complete(DeclarationCommitted::DuplicateName { name }) => {
                return Outcome::complete(Published::DuplicateName { name });
            }
            Outcome::Inconclusive(reason) => return Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        }
    }
    Outcome::complete(Published::BlockCommitted(BlockPublication {
        environment: staged,
        names,
    }))
}
