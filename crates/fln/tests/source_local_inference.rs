//! Ordinary local helper signatures can be constrained by their continuations.
//! Their original values still pass both checkers, including unused values and
//! selected synthetic failures inside tactic alternatives.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    VmExit,
};
use std::sync::OnceLock;

const TYPES: &str = r#"
inductive Span where
  | empty
  | pair (start stop : Nat)
structure Ref where
  start : Option Nat
  stop : Option Nat
def Span.score : Span → Nat
  | .empty => 0
  | .pair start stop => start * 100 + stop
"#;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn seed() -> Engine {
    static SEED: OnceLock<Engine> = OnceLock::new();
    SEED.get_or_init(|| {
        Engine::with_source_seed(limits())
            .unwrap()
            .into_complete()
            .unwrap()
    })
    .clone()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both checkers complete")
    .engine
}

fn values(base: &Engine, source: &str) -> Vec<String> {
    let batch = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("native execution completes");
    batch
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let VmExit::Returned(value) = &batch.executions[index].exit else {
                panic!("expected returned Nat: {:?}", batch.executions[index]);
            };
            fln_vm::interpreter::nat_decimal(&value.value).expect("Nat result")
        })
        .collect()
}

#[test]
fn shadowed_field_receivers_and_anonymous_results_infer_from_local_uses() {
    let base = checked(&seed(), TYPES);
    let receiver = checked(
        &base,
        r#"def receiverOnly (ref : Ref) : Option Nat :=
  let get ref := ref.start
  get ref
theorem receiverValue :
  receiverOnly (Ref.mk (Option.some 23) Option.none) = Option.some 23 := rfl
def drop (n : Nat) : Nat :=
  let keep _ := n
  keep true
"#,
    );
    assert!(
        receiver
            .environment()
            .contains(&Name::from_components(["receiverValue"]))
    );
    assert_eq!(values(&receiver, "#eval drop 17\n"), ["17"]);
    for (parameter, result) in [
        ("ref", ""),
        ("(ref : Ref)", ""),
        ("ref", ": Span"),
        ("(ref : Ref)", ": Span"),
    ] {
        let source = format!(
            r#"def fromRef (ref : Ref) : Span :=
  let fallback {parameter} {result} :=
    match ref.start, ref.stop with
    | Option.some start, Option.some stop => .pair start stop
    | _, _ => .empty
  fallback ref
"#
        );
        let checked = checked(&base, &source);
        assert_eq!(
            values(
                &checked,
                "#eval Span.score (fromRef (Ref.mk (Option.some 4) (Option.some 9)))\n\
                 #eval Span.score (fromRef (Ref.mk Option.none (Option.some 9)))\n\
                 #eval Span.score (fromRef (Ref.mk (Option.some 4) Option.none))\n"
            ),
            ["409", "0", "0"]
        );
        assert!(
            !checked
                .environment()
                .contains(&Name::from_components(["fallback"]))
        );
    }
}

#[test]
fn result_inference_preserves_polymorphic_captures_and_tactic_choices() {
    let source = format!(
        r#"{TYPES}
def simple (n : Nat) : Span :=
  let make (x : Nat) := .pair x x
  make n
def wrap {{α : Type}} (value : α) : Option α :=
  let make (x : α) := .some x
  make value
theorem wrapped : wrap 37 = Option.some 37 := rfl
def eagerChoice : Span := by
  first
  | exact (let make (x : Nat) : Span := .missing; make 0)
  | exact Span.empty
def innerChoice : Span :=
  let make (x : Nat) := (by
    first
    | exact .missing
    | exact (.pair x x))
  make 3
def validUnused (n : Nat) : Nat :=
  let make (x : Nat) := true
  n
"#
    );
    let checked = checked(&seed(), &source);
    assert_eq!(
        values(
            &checked,
            "#eval Span.score (simple 5)\n#eval Span.score eagerChoice\n\
             #eval Span.score innerChoice\n#eval validUnused 17\n"
        ),
        ["505", "0", "303", "17"]
    );
}

#[test]
fn unresolved_unused_and_selected_invalid_values_never_disappear() {
    let base = checked(&seed(), TYPES);
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad (n : Nat) : Span := let make (x : Nat) := .pair x x; .empty",
        "def bad : Span := let make x := .pair x x; let first : Span := make 3; make true",
        "def bad : Span := let make (x : Nat) := missingBody x; make 3",
        "def bad : Span := by\n  first\n  | exact (let make (x : Nat) := .missing; make 0)\n  | exact Span.empty",
    ] {
        let source = format!("def prefix := 7\n{source}\n");
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "accepted {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["prefix"]))
        );
    }
}
