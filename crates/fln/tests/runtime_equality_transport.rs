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
#[test]
fn a_constructor_field_index_can_be_matched() {
    run(
        "inductive Indexed : Nat -> Type where | make (n : Nat) : Indexed n\ndef value (n : Nat) (x : Indexed n) : Nat := match x with | .make k => k\n#eval value 42 (Indexed.make 42)",
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
    run(
        "inductive Walk : Nat -> Type where | done (n : Nat) : Walk n | step (n : Nat) (child : Walk n) : Walk n\ndef copy (n : Nat) (w : Walk n) : Walk n := match w with | .done k => Walk.done k | .step k child => Walk.step k (copy k child)\ndef depth (n : Nat) (w : Walk n) : Nat := by induction w with | done k => exact k | step k child ih => exact ih + 1\n#eval depth 40 (copy 40 (Walk.step 40 (Walk.step 40 (Walk.done 40))))",
        "42",
    );
}
#[test]
fn repeated_indices_and_two_recursive_children_retain_their_evidence() {
    run(
        "inductive TreeAt : Nat -> Nat -> Type where | leaf (n : Nat) (a : Nat) : TreeAt n n | fork (n : Nat) (left right : TreeAt n n) : TreeAt n n\ndef copy (n m : Nat) (t : TreeAt n m) : TreeAt n m := match t with | .leaf k a => TreeAt.leaf k a | .fork k l r => TreeAt.fork k (copy k k l) (copy k k r)\ndef sum (n m : Nat) (t : TreeAt n m) : Nat := by induction t with | leaf k a => exact a | fork k l r ihl ihr => exact ihl + ihr\n#eval sum 3 3 (copy 3 3 (TreeAt.fork 3 (TreeAt.leaf 3 20) (TreeAt.leaf 3 22)))",
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
