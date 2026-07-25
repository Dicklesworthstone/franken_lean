//! The checked-declaration capability contract (bead `fln-yswb`; D6, FL-INV-02,
//! FL-INV-06).
//!
//! # What is under test
//!
//! `fln_kernel::check` returns a verdict whose `Accepted` arm carried only a
//! `Consumption`, while `fln_env::Environment::plan_add_decl` accepts a raw
//! `ConstantInfo`. Nothing connected them, so **checking declaration A and
//! publishing declaration B was representable**. An invariant that is merely
//! tested against is audited; this bead is about making it enforced.
//!
//! # Most of this contract is not testable at run time, and that is the point
//!
//! The strongest properties here are compile-time: they are the programs that
//! do NOT compile. A run-time test can only observe that a forged capability
//! was rejected — it cannot observe that forging one is inexpressible. So the
//! refusals are recorded as commented programs beside the test that exercises
//! the legitimate path, and `the_capability_has_no_public_constructor_surface`
//! pins the API shape those refusals depend on.
//!
//! Each entry names the mutant it corresponds to from the bead's list.

#![forbid(unsafe_code)]

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::{AxiomVal, ConstantVal};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Admitted, Published, admit};
use fln_kernel::verdict::Budget;

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn sort1() -> Expr {
    Expr::sort(Level::one())
}

fn axiom(name: &str, type_: Expr) -> Declaration {
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        is_unsafe: false,
    })
}

fn accepted<'e>(
    env: &'e Environment,
    decl: Declaration,
) -> fln_kernel::capability::CheckedDecl<'e> {
    match admit(env, decl, Budget::DEFAULT) {
        Outcome::Complete(Admitted::Accepted(cap)) => cap,
        other => panic!(
            "expected an accepted admission, got {}",
            match other {
                Outcome::Complete(Admitted::Rejected { class, .. }) =>
                    format!("rejected {class:?}"),
                Outcome::Inconclusive(_) => "inconclusive".to_string(),
                Outcome::InternalFault(_) => "internal fault".to_string(),
                Outcome::Complete(Admitted::Accepted(_)) => unreachable!(),
            }
        ),
    }
}

// ---------------------------------------------------------------------------
// The legitimate path still works
// ---------------------------------------------------------------------------

#[test]
fn an_accepted_declaration_publishes_through_its_capability() {
    // Without this the refusals below could all be passing because nothing
    // works at all, which is the cheapest way to make a capability look sound.
    let env = Environment::new();
    let cap = accepted(&env, axiom("A", sort1()));
    assert!(cap.name().is_some());
    assert!(
        cap.consumption().steps_used > 0,
        "a real check was performed"
    );
    match cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
            // The new environment really did gain the constant.
            assert!(p.environment.find(&n("A")).is_some());
        }
        other => panic!("a legitimate publication did not commit: {other:?}"),
    }
    // And the base is untouched: publication returns a NEW environment rather
    // than mutating the one that was checked against.
    assert!(env.find(&n("A")).is_none(), "the base was mutated in place");
}

// ---------------------------------------------------------------------------
// MUTANT: check A, publish B
// ---------------------------------------------------------------------------

#[test]
fn the_capability_carries_the_declaration_that_was_checked() {
    // `publish` takes no declaration parameter, so there is nothing to
    // substitute. This test pins the consequence: what lands is what was
    // checked, by name.
    let env = Environment::new();
    let cap = accepted(&env, axiom("Checked", sort1()));
    assert_eq!(cap.name(), Some(&n("Checked")));
    match cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
            assert!(p.environment.find(&n("Checked")).is_some());
            assert!(
                p.environment.find(&n("Substituted")).is_none(),
                "a declaration nobody checked reached the environment"
            );
        }
        other => panic!("unexpected: {other:?}"),
    }

    // MUTANT `check-A-publish-B`, refused at compile time. There is no
    // signature that accepts a second declaration:
    //
    //   cap.publish(axiom("Substituted", sort1()), ..)   // too many arguments
    //
    // and the field holding the checked declaration is private, so it cannot be
    // overwritten either:
    //
    //   cap.decl = axiom("Substituted", sort1());        // field `decl` is private
}

// ---------------------------------------------------------------------------
// MUTANT: forged capability
// ---------------------------------------------------------------------------

#[test]
fn the_capability_has_no_public_constructor_surface() {
    // MUTANT `forged capability`, refused at compile time. Every field is
    // private and one has a private TYPE (`Seal`) that no other crate can name,
    // so none of these compiles from outside `fln-kernel`:
    //
    //   CheckedDecl { base: &env, decl, consumption, _seal: Seal }
    //       // error: fields `base`, `decl`, `consumption`, `_seal` are private
    //       // error: cannot find type `Seal` in this scope
    //
    //   CheckedDecl::default()      // no Default impl
    //   CheckedDecl::from(decl)     // no From impl
    //
    // This test pins the shape those refusals rest on: the ONLY way to obtain
    // one is `admit`, and it is reachable.
    let env = Environment::new();
    let cap = accepted(&env, axiom("Only", sort1()));
    let _ = cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    );
}

// ---------------------------------------------------------------------------
// MUTANTS: rejection, inconclusive, internal fault cannot inhabit it
// ---------------------------------------------------------------------------

#[test]
fn a_rejected_declaration_yields_no_capability() {
    // `Prop`-typed value where a sort is required: a real rejection.
    let env = Environment::new();
    let bad = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n("Bad"),
            level_params: vec![],
            // A bound variable with no binder is not a type.
            type_: Expr::bvar(0).expect("a loose bvar is representable"),
        },
        is_unsafe: false,
    });
    match admit(&env, bad, Budget::DEFAULT) {
        Outcome::Complete(Admitted::Rejected { .. }) => {}
        Outcome::Complete(Admitted::Accepted(_)) => {
            panic!("a rejected declaration minted a publication capability")
        }
        // A non-answer is equally acceptable here; what must NOT happen is a
        // capability.
        Outcome::Inconclusive(_) | Outcome::InternalFault(_) => {}
    }
    // MUTANT `InternalFault`: the `Admitted` enum has no arm carrying a
    // capability alongside a fault, and `admit` propagates
    // Inconclusive/InternalFault unchanged. There is no expression that turns
    // either into a `CheckedDecl`:
    //
    //   let cap: CheckedDecl = Outcome::InternalFault(f).into();  // no From impl
}

#[test]
fn an_exhausted_budget_yields_no_capability() {
    // MUTANT `exhaustion`. A budget too small to complete the check must
    // produce a non-answer, never a capability — FL-INV-07 says resource
    // exhaustion is never promoted to acceptance, and here it additionally
    // cannot be promoted to a publication right.
    let env = Environment::new();
    let starved = Budget::DEFAULT.narrowed(0, Budget::DEFAULT.depth);
    if let Outcome::Complete(Admitted::Accepted(_)) =
        admit(&env, axiom("Starved", sort1()), starved)
    {
        panic!("an exhausted check minted a publication capability");
    }
}

// ---------------------------------------------------------------------------
// MUTANTS: replay, stale base, substitution of the base
// ---------------------------------------------------------------------------

#[test]
fn publication_consumes_the_capability_exactly_once() {
    let env = Environment::new();
    let cap = accepted(&env, axiom("Once", sort1()));
    let _first = cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    );

    // MUTANT `replay`, refused at compile time. `publish` takes `self` by value
    // and `CheckedDecl` is deliberately neither `Clone` nor `Copy`:
    //
    //   let second = cap.publish(..);   // error: use of moved value `cap`
    //   let copy = cap.clone();         // error: no method named `clone`
    //
    // A second publication from one check is a use-after-move, not a run-time
    // check that could be forgotten.
}

#[test]
fn the_base_environment_cannot_be_substituted_or_moved() {
    // MUTANT `stale base`. `publish` takes NO environment parameter — it
    // publishes into the base it borrowed — so there is no argument to get
    // wrong:
    //
    //   cap.publish(&other_env, ..);    // too many arguments
    //
    // and the borrow prevents the base being moved or mutated while the
    // capability is alive:
    //
    //   let cap = accepted(&env, decl);
    //   drop(env);                      // error: cannot move out of `env`
    //   cap.publish(..);                //        because it is borrowed
    //
    // This test pins the observable half: two capabilities against two
    // different bases publish into their own bases and do not cross.
    let env_a = Environment::new();
    let env_b = Environment::new();
    let cap_a = accepted(&env_a, axiom("InA", sort1()));
    let cap_b = accepted(&env_b, axiom("InB", sort1()));
    let a = cap_a.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    );
    let b = cap_b.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    );
    match (a, b) {
        (
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(pa))),
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(pb))),
        ) => {
            assert!(pa.environment.find(&n("InA")).is_some());
            assert!(pa.environment.find(&n("InB")).is_none());
            assert!(pb.environment.find(&n("InB")).is_some());
            assert!(pb.environment.find(&n("InA")).is_none());
        }
        other => panic!("unexpected: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Blocks refuse rather than publish through a per-constant path
// ---------------------------------------------------------------------------

#[test]
fn a_block_declaration_publishes_nothing_through_this_handoff() {
    // An inductive block publishes several constants at once. The bound handoff
    // for that is not built, and the honest behaviour is to publish NOTHING
    // rather than to push the block through a per-constant path that never
    // checked it as a unit. Refusing is safe; the alternative is not.
    let env = Environment::new();
    let quot = Declaration::Quotient(vec![]);
    // If the empty quotient block is not accepted the refusal is upstream and
    // equally fine — nothing was published either way.
    if let Outcome::Complete(Admitted::Accepted(cap)) = admit(&env, quot, Budget::DEFAULT) {
        match cap.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::BlockHandoffUnavailable) => {}
            other => panic!("a block published through the single-constant path: {other:?}"),
        }
    }
}
