//! Equality transports retain checked typing but do not execute proof evidence.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};
fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn run(source: &str, expected: &str) -> u64 {
    let batch = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
        panic!("native return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
    value.usage.steps
}
#[test]
fn transport_keeps_a_scalar_payload() {
    run(
        "def transport (a b : Nat) (h : a = b) (n : Nat) : Nat := Eq.rec (motive := fun k proof => Nat) n h\n#eval transport 1 1 (by rfl) 42",
        "42",
    );
}
/// Refused before anything is published; `reason` names the refusal that
/// corresponds to the pinned Reference's own reason.
fn refuse(source: &str, reason: &str) {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let error = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .expect_err(source);
    let rendered = format!("{error:?}");
    assert!(
        rendered.contains(reason),
        "expected {reason} for:\n{source}\ngot {rendered}"
    );
    assert_eq!(root, engine.logical_root(&KVMap::new()));
}
// A written index that every constructor binds as its own field and returns
// unchanged is promoted to a parameter by the pinned Reference
// (`fixedIndicesToParams`), so a constructor pattern may only write `_` there:
// a named variable is the pin's "Type mismatch" and FrankenLean's
// `InaccessibleParameter`. A family that binds the index elsewhere, or not at
// all in some constructor, keeps it as an index, and a match refines it to the
// constructor's fields. Every `run` program below is accepted by pinned `lean`
// v4.32.0 with the same `#eval` output, and every `refuse` program is refused.
#[test]
fn a_constructor_field_index_can_be_matched() {
    // `zero` keeps the index, so `k` is a stored field refined against `n`.
    run(
        "inductive Indexed : Nat -> Type where | make (n : Nat) : Indexed n | zero : Indexed 0\ndef value (n : Nat) (x : Indexed n) : Nat := match x with | .make k => k | .zero => 0\n#eval value 42 (Indexed.make 42)",
        "42",
    );
    refuse(
        "inductive Indexed : Nat -> Type where | make (n : Nat) : Indexed n\ndef value (n : Nat) (x : Indexed n) : Nat := match x with | .make k => k\n#eval value 42 (Indexed.make 42)",
        "InaccessibleParameter",
    );
    // With `make` alone the index is promoted and the pin reads the parameter.
    run(
        "inductive Indexed : Nat -> Type where | make (n : Nat) : Indexed n\ndef value (n : Nat) (x : Indexed n) : Nat := match x with | .make _ => n\n#eval value 42 (Indexed.make 42)",
        "42",
    );
}

const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\ndef total (n : Nat) (xs : Vec Nat n) : Nat := by induction xs with | nil => exact 0 | cons k x tail ih => exact x + ih\n";
#[test]
fn equality_transport_preserves_the_indexed_object_representation() {
    run(
        &format!(
            "{VEC}def castVec (a b : Nat) (h : a = b) (xs : Vec Nat a) : Vec Nat b := Eq.rec (motive := fun k proof => Vec Nat k) xs h\n#eval total 2 (castVec 2 2 (by rfl) (Vec.cons 1 20 (Vec.cons 0 22 Vec.nil)))"
        ),
        "42",
    );
}
#[test]
fn refined_matches_can_rebuild_recursive_objects() {
    // `step` raises the index, so it is kept: each match refines it to `k`.
    run(
        "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk (Nat.succ n)\ndef copy (n : Nat) (w : Walk n) : Walk n := match w with | .done k => Walk.done k | .step k child => Walk.step k (copy k child)\ndef depth (n : Nat) (w : Walk n) : Nat := match w with | .done k => k | .step k child => depth k child + 1\n#eval depth 42 (copy 42 (Walk.step 41 (Walk.step 40 (Walk.done 40))))",
        "42",
    );
    refuse(
        "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\ndef copy (n : Nat) (w : Walk n) : Walk n := match w with | .done k => Walk.done k | .step k child => Walk.step k (copy k child)\ndef depth (n : Nat) (w : Walk n) : Nat := by induction w with | done k => exact k | step k child ih => exact ih + 1\n#eval depth 40 (copy 40 (Walk.step 40 (Walk.step 40 (Walk.done 40))))",
        "InaccessibleParameter",
    );
    // The same family with its index promoted, in the pin's form.
    run(
        "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\ndef copy (n : Nat) (w : Walk n) : Walk n := match w with | .done _ => Walk.done n | .step _ child => Walk.step n (copy n child)\ndef depth (n : Nat) (w : Walk n) : Nat := match w with | .done _ => n | .step _ child => depth n child + 1\n#eval depth 40 (copy 40 (Walk.step 40 (Walk.step 40 (Walk.done 40))))",
        "42",
    );
}
#[test]
fn repeated_indices_and_two_recursive_children_retain_their_evidence() {
    // `leaf` binds its payload first, so neither index is promoted: both are
    // refined to the repeated `k`, and each child keeps its own evidence.
    run(
        "inductive TreeAt : Nat -> Nat -> Type where | leaf (a : Nat) (n : Nat) : TreeAt n n | fork (n : Nat) (left right : TreeAt n n) : TreeAt n n\ndef copy (n m : Nat) (t : TreeAt n m) : TreeAt n m := match t with | .leaf a k => TreeAt.leaf a k | .fork k l r => TreeAt.fork k (copy k k l) (copy k k r)\ndef sum (n m : Nat) (t : TreeAt n m) : Nat := match t with | .leaf a k => a | .fork k l r => sum k k l + sum k k r\n#eval sum 3 3 (copy 3 3 (TreeAt.fork 3 (TreeAt.leaf 20 3) (TreeAt.leaf 22 3)))",
        "42",
    );
    refuse(
        "inductive TreeAt : Nat -> Nat -> Type where | leaf (n : Nat) (a : Nat) : TreeAt n n | fork (n : Nat) (left right : TreeAt n n) : TreeAt n n\ndef copy (n m : Nat) (t : TreeAt n m) : TreeAt n m := match t with | .leaf k a => TreeAt.leaf k a | .fork k l r => TreeAt.fork k (copy k k l) (copy k k r)\ndef sum (n m : Nat) (t : TreeAt n m) : Nat := by induction t with | leaf k a => exact a | fork k l r ihl ihr => exact ihl + ihr\n#eval sum 3 3 (copy 3 3 (TreeAt.fork 3 (TreeAt.leaf 3 20) (TreeAt.leaf 3 22)))",
        "InaccessibleParameter",
    );
    // With `leaf (n : Nat) (a : Nat)` the first index is promoted; the second
    // is still refined to that parameter, in the pin's form.
    run(
        "inductive TreeAt : Nat -> Nat -> Type where | leaf (n : Nat) (a : Nat) : TreeAt n n | fork (n : Nat) (left right : TreeAt n n) : TreeAt n n\ndef copy (n m : Nat) (t : TreeAt n m) : TreeAt n m := match t with | .leaf _ a => TreeAt.leaf n a | .fork _ l r => TreeAt.fork n (copy n n l) (copy n n r)\ndef sum (n m : Nat) (t : TreeAt n m) : Nat := match t with | .leaf _ a => a | .fork _ l r => sum n n l + sum n n r\n#eval sum 3 3 (copy 3 3 (TreeAt.fork 3 (TreeAt.leaf 3 20) (TreeAt.leaf 3 22)))",
        "42",
    );
}
#[test]
fn transported_callbacks_support_captures_and_partial_application() {
    run(
        "def transfer (a b : Nat) (h : a = b) (f : Nat -> Nat -> Nat) : Nat -> Nat -> Nat := Eq.rec (motive := fun k proof => Nat -> Nat -> Nat) f h\ndef result (offset : Nat) : Nat := let f := transfer 1 1 (by rfl) (fun x y => offset + x + y); let g := f 2; g 3\n#eval result 37",
        "42",
    );
    run(
        "def result (offset : Nat) : Nat := Eq.rec (motive := fun (k : Nat) proof => Nat -> Nat -> Nat) (fun x y => offset + x + y) (Eq.refl 1) 2 3\n#eval result 37",
        "42",
    );
}
#[test]
fn scalar_and_static_type_carriers_are_not_confused() {
    run(
        "def transfer (a b : Bool) (h : a = b) (x : Nat) : Nat := Eq.rec (motive := fun k proof => Nat) x h\n#eval transfer true true (by rfl) 42",
        "42",
    );
    run(
        "def transfer (a b : String) (h : a = b) (x : Nat) : Nat := Eq.rec (motive := fun k proof => Nat) x h\n#eval transfer \"same\" \"same\" (by rfl) 42",
        "42",
    );
    run(
        "def cast (A B : Type) (h : A = B) (x : A) : B := Eq.rec (motive := fun T proof => T) x h\n#eval cast Nat Nat (by rfl) 42",
        "42",
    );
}
#[test]
fn ordinary_endpoints_and_payloads_are_strict_but_evidence_is_erased() {
    let prefix = "def expensive (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) n\ndef transport (a b : Nat) (h : a = b) (x : Nat) : Nat := Eq.rec (motive := fun k proof => Nat) x h\n";
    let small = run(&format!("{prefix}#eval transport 0 0 (by rfl) 42"), "42");
    let endpoints = run(
        &format!("{prefix}#eval transport (expensive 40) (expensive 40) (by rfl) 42"),
        "42",
    );
    assert!(
        endpoints > small + 100,
        "ordinary endpoints must not be discarded"
    );
    let payload = run(
        &format!("{prefix}#eval transport 0 0 (by rfl) (expensive 40 + 42)"),
        "42",
    );
    assert!(payload > small + 50, "ordinary payload must execute");
}
#[test]
fn invalid_evidence_and_resource_stops_do_not_publish() {
    let source = "def cast (a b : Nat) (h : a = b) (n : Nat) : Nat := Eq.rec (motive := fun k proof => Nat) n h\n#eval cast 0 1 (by rfl) 42";
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
            .is_err()
    );
    assert_eq!(root, engine.logical_root(&KVMap::new()));
    let valid = source.replace("cast 0 1", "cast 0 0");
    let mut bounded = limits();
    bounded.ingress.max_nodes = 1;
    assert!(
        engine
            .execute_source_definitions(&[valid.as_bytes()], &KVMap::new(), bounded)
            .is_err()
    );
    assert_eq!(root, engine.logical_root(&KVMap::new()));
    run(&valid, "42");
}
