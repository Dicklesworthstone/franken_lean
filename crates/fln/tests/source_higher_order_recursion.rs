//! Higher-order recursive constructors are checked independently at admission.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
const TREE: &str =
    "inductive Branching where | leaf (value : Nat) | node (children : Nat -> Branching)\n";
#[test]
fn higher_order_children_support_construction_matching_and_computation() {
    check(&format!(
        r#"{TREE}
        def first (t : Branching) : Nat := match t with
          | .leaf value => value
          | .node children => match children 0 with
            | .leaf value => value
            | .node other => 99
        theorem selected : first (Branching.node (fun n => Branching.leaf (n + 7))) = 7 := by rfl
        theorem deeper : first (Branching.node (fun n => Branching.node (fun k => Branching.leaf k))) = 99 := by rfl
    "#
    ));
}
#[test]
fn induction_hypotheses_quantify_the_child_functions_arguments() {
    check(&format!(
        r#"{TREE}
        theorem principle (P : Branching -> Prop)
            (atLeaf : forall n : Nat, P (Branching.leaf n))
            (atNode : forall f : Nat -> Branching, (forall n : Nat, P (f n)) -> P (Branching.node f))
            (t : Branching) : P t := by
          induction t with
          | leaf n => exact atLeaf n
          | node f ih => exact atNode f ih
    "#
    ));
}
#[test]
fn accessibility_elimination_returns_dependent_data_without_an_axiom() {
    check(
        r#"
        inductive Accessible (A : Type) (R : A -> A -> Prop) : A -> Prop where
          | intro (x : A) (next : forall y : A, R y x -> Accessible A R y) : Accessible A R x
        def fold (A : Type) (R : A -> A -> Prop) (P : A -> Type)
            (step : forall x : A, (forall y : A, R y x -> P y) -> P x)
            (a : A) (h : Accessible A R a) : P a := by
          induction h with
          | intro x next ih => exact step x ih
    "#,
    );
}
#[test]
fn function_valued_children_with_dependent_arguments_and_indices() {
    check(
        r#"
        inductive Trace (A : Type) (B : A -> Type) : A -> Type where
          | stop (a : A) : Trace A B a
          | more (a : A) (children : forall x : A, B x -> Trace A B x) : Trace A B a
        def inspect (a : Nat) (t : Trace Nat (fun x => Bool) a) : Nat := match t with
          | .stop x => x
          | .more x next => match next 13 true with
            | .stop value => value
            | .more value child => value + 1
        theorem read : inspect 7 (Trace.more 7 (fun x p => Trace.stop x)) = 13 := by rfl
    "#,
    );
}
#[test]
fn direct_and_function_children_share_the_correct_minor_telescope() {
    check(
        r#"
        inductive Mixed (A : Type) (B : A -> Type) where
          | leaf (a : A)
          | node (a : A) (b : B a) (one : B a -> Mixed A B)
              (many : forall x : A, B x -> Mixed A B) (tail : Mixed A B)
        theorem principle (A : Type) (B : A -> Type) (P : Mixed A B -> Prop)
            (base : forall a : A, P (Mixed.leaf a))
            (step : forall a : A, forall b : B a, forall one : B a -> Mixed A B,
              forall many : (forall x : A, B x -> Mixed A B), forall tail : Mixed A B,
              (forall z : B a, P (one z)) -> (forall x : A, forall z : B x, P (many x z)) ->
              P tail -> P (Mixed.node a b one many tail)) (t : Mixed A B) : P t := by
          induction t with
          | leaf a => exact base a
          | node a b one many tail ihOne ihMany ihTail => exact step a b one many tail ihOne ihMany ihTail
    "#,
    );
}
fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let before = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits)
            )
            .is_err(),
        "{source}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}
#[test]
fn nonpositive_nested_nonuniform_and_oversized_children_never_publish() {
    for source in [
        "inductive Bad where | mk (next : Bad -> Bad)",
        "inductive Bad where | mk (next : (Bad -> Nat) -> Bad)",
        "inductive Box (A : Type) where | mk (a : A)\ninductive Bad where | mk (next : Nat -> Box Bad)",
        "inductive Bad (A : Type) where | mk (next : Nat -> Bad Nat)",
        "inductive Tiny : Type where | mk (next : Type -> Tiny)",
    ] {
        reject(source);
    }
}
#[test]
fn cases_does_not_expose_function_induction_hypotheses() {
    reject(&format!(
        r#"{TREE}
        theorem bad (P : Branching -> Prop)
            (atLeaf : forall n : Nat, P (Branching.leaf n))
            (atNode : forall f : Nat -> Branching, (forall n : Nat, P (f n)) -> P (Branching.node f))
            (t : Branching) : P t := by
          cases t with
          | leaf n => exact atLeaf n
          | node f => apply atNode; assumption
    "#
    ));
}
#[test]
fn higher_order_small_elimination_cannot_extract_a_hidden_witness() {
    reject(
        r#"
        inductive Hidden (A : Type) : Prop where
          | mk (witness : A) (next : Nat -> Hidden A)
        def bad (A : Type) (h : Hidden A) : A := by
          induction h with
          | mk a next ih => exact a
    "#,
    );
}
#[test]
fn invalid_unused_function_bodies_are_not_erased_by_matching() {
    reject(&format!(
        r#"{TREE}
        def ignored : Nat := match Branching.node (fun n => let bad : String := n; Branching.leaf n) with
          | .leaf value => value
          | .node children => 0
    "#
    ));
}
