//! Indexed constructor matches through the native parser, elaborator and kernel.
//! The splitter generalizes independent local indices with the discriminant, as
//! `Lean/Meta/Tactic/Split.lean` does when applying the generated match splitter.
#![forbid(unsafe_code)]

use fln_core::outcome::Outcome;
use fln_elab::{
    check_definition_source,
    records::RecordBudget,
    seed::source_seed_declarations,
    source::scope::{self, SourceScope},
};
use fln_env::{
    environment::{DeclarationBudget, DeclarationCommitted, Environment},
    pmap::CollisionBudget,
};
use fln_kernel::{
    Declaration,
    capability::{Published, admit},
    council::{Council, CouncilOutcome, convene},
    verdict::{Budget, Verdict},
};

fn budget() -> Budget {
    Budget::for_stack_bytes(8 * 1024 * 1024)
}

fn publish(environment: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(environment, declaration, budget()) else {
        panic!("declaration admission exhausted its budget");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("declaration was not accepted");
    };
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
            result.environment
        }
        Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
        other => panic!("declaration publication {other:?}"),
    }
}

fn environment() -> Environment {
    let mut environment = Environment::new();
    for declaration in source_seed_declarations() {
        environment = publish(&environment, declaration);
    }
    for source in [
        "inductive Vec (A : Type) : Nat -> Type where\n  | nil : Vec A 0\n  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)",
        "inductive Grid : Nat -> Nat -> Type where\n  | origin : Grid 0 0\n  | step (n m : Nat) (rest : Grid n m) : Grid (Nat.succ n) (Nat.succ m)",
    ] {
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        let declaration = scope::elaborate_inductive(
            parsed.syntax(),
            &environment,
            budget(),
            RecordBudget::default(),
            &SourceScope::default(),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        environment = publish(&environment, declaration);
    }
    environment
}

fn accepted(environment: &Environment, source: &str) {
    let checked = check_definition_source(source.as_bytes(), environment, budget())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    assert!(
        matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}\n{:?}",
        checked.outcome
    );
    let Declaration::Thm(proof) = checked.declaration else {
        panic!("expected a theorem with an actual proof");
    };
    assert!(!proof.value.has_expr_mvar());
    assert!(!proof.value.has_level_mvar());
    assert!(!proof.value.has_fvar());
}

#[test]
fn indexed_split_specializes_indices_and_preserves_source_alternative_order() {
    let environment = environment();
    // Reconstruction supplies the dependent result type: without that annotation,
    // result inference fails before either `split` or ordinary `cases` can run.
    for source in [
        "theorem length (A : Type) (n : Nat) (xs : Vec A n) : (match xs with | .nil => 0 | .cons k a tail => Nat.succ k) = n := by split <;> rfl",
        "theorem reordered (A : Type) (n : Nat) (xs : Vec A n) : match xs with | .cons k a tail => Nat.succ k = Nat.succ k | .nil => True := by\n  split\n  next k a tail => rfl\n  next => exact True.intro",
        "theorem reconstruct (A : Type) (n : Nat) (xs : Vec A n) : ((match xs with | .nil => Vec.nil | .cons k a tail => Vec.cons k a tail) : Vec A n) = xs := by split <;> rfl",
        "theorem underBinder (A : Type) (n : Nat) (xs : Vec A n) : ∀ z : Nat, (match xs with | .nil => 0 | .cons k a tail => Nat.succ k) = n := by split <;> intro z <;> rfl",
        "theorem twoIndices (n m : Nat) (grid : Grid n m) : (match grid with | .origin => 0 | .step a b rest => Nat.succ a) = n := by split <;> rfl",
    ] {
        accepted(&environment, source);
    }
}

#[test]
fn indexed_split_transports_dependent_hypotheses_and_splits_hypothesis_types() {
    let environment = environment();
    for source in [
        "theorem dependent (A : Type) (n : Nat) (xs : Vec A n) (P : (k : Nat) -> Vec A k -> Prop) (h : P n xs) : match xs with | .nil => P 0 Vec.nil | .cons k a tail => P (Nat.succ k) (Vec.cons k a tail) := by split <;> assumption",
        "theorem atHypothesis (A : Type) (n : Nat) (xs : Vec A n) (Q : Prop) (h : match xs with | .nil => False | .cons k a tail => Q) : Q := by\n  split at h\n  next => exact False.elim h\n  next k a tail => exact h",
        "theorem atWildcard (A : Type) (n : Nat) (xs : Vec A n) (h : match xs with | .nil => False | .cons k a tail => True) : True := by\n  split at *\n  next => exact False.elim h\n  next k a tail => exact h",
    ] {
        accepted(&environment, source);
    }
}

#[test]
fn indexed_split_keeps_false_and_unfinished_constructor_branches() {
    let environment = environment();
    for source in [
        "theorem falseBranch (A : Type) (n : Nat) (xs : Vec A n) : match xs with | .nil => True | .cons k a tail => False := by split <;> exact True.intro",
        "theorem missingBranch (A : Type) (n : Nat) (xs : Vec A n) : match xs with | .nil => True | .cons k a tail => True := by split; exact True.intro",
        "theorem wrongIndex (A : Type) (n : Nat) (xs : Vec A n) : (match xs with | .nil => 1 | .cons k a tail => Nat.succ k) = n := by split <;> rfl",
    ] {
        let error = check_definition_source(source.as_bytes(), &environment, budget())
            .expect_err("every constructor must supply a well-typed proof");
        assert!(
            !format!("{error:?}").contains("SplitMatchUnsupported"),
            "the negative control must reach real constructor goals: {source}\n{error:?}"
        );
    }
}

#[test]
fn indexed_split_hides_nonselected_dependent_hypotheses() {
    let environment = environment();
    let source = "theorem hiddenDependent (A : Type) (n : Nat) (xs : Vec A n) (P : (k : Nat) -> Vec A k -> Prop) (h : P n xs) : match xs with | .nil => P 0 Vec.nil | .cons k a tail => P (Nat.succ k) (Vec.cons k a tail) := by split <;> exact h";
    let error = check_definition_source(source.as_bytes(), &environment, budget())
        .expect_err("the pin makes the generalized hypothesis inaccessible after split");
    assert!(
        format!("{error:?}").contains("UnknownConstant"),
        "the hidden source name must not resolve: {source}\n{error:?}"
    );
}

#[test]
fn indexed_split_refuses_forward_dependencies_on_the_selected_hypothesis() {
    let environment = environment();
    // The pin preserves q and leaves h's specialized match unsimplified. Until that
    // congruence is supported, refuse before omitting the original h from the context.
    let source = "theorem dependentSelected (A : Type) (n : Nat) (xs : Vec A n) (h : match xs with | .nil => False | .cons k a tail => True) (q : h = h) : True := by split at h <;> exact True.intro";
    let error = check_definition_source(source.as_bytes(), &environment, budget())
        .expect_err("forward dependencies must be refused before constructing split branches");
    assert!(
        format!("{error:?}").contains("SplitMatchUnsupported"),
        "the dependent context must retain its typed refusal: {source}\n{error:?}"
    );
}
