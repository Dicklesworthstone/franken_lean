//! Pattern functions use the production term worklist and both admission engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
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
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
#[test]
fn functions_can_be_values_and_higher_order_arguments() {
    check(
        "def choose : Bool -> Nat := fun | true => 7 | false => 9\n\
 def apply (f : Bool -> Nat) (b : Bool) : Nat := f b\n\
 theorem selected : choose false = 9 := by rfl\n\
 theorem applied : apply (fun | true => 3 | false => 4) true = 3 := by rfl",
    );
}
#[test]
fn multiple_columns_preserve_priority_and_simultaneous_bindings() {
    check(
        "def priority : Bool -> Bool -> Nat := fun | true, _ => 1 | _, true => 2 | _, _ => 3\n\
 theorem first : priority true true = 1 := by rfl\n\
 theorem second : priority false true = 2 := by rfl\n\
 def swapped : Nat -> Nat -> Nat := fun | y,x => x\n theorem swap : swapped 3 9 = 9 := by rfl",
    );
}
#[test]
fn nested_patterns_and_nested_function_bodies_are_supported() {
    check(
        "inductive Maybe (A : Type) where | none | some (x : A)\n\
 def nested : Maybe (Maybe Nat) -> Nat := fun | .none => 0 | .some .none => 1 | .some (.some n) => n\n\
 theorem n : nested (Maybe.some (Maybe.some 8)) = 8 := by rfl\n\
 def nestedFun : Bool -> Bool -> Nat := fun\n | true => (fun | true => 1 | false => 2)\n | false => (fun | true => 3 | false => 4)\n\
 theorem nf : nestedFun false true = 3 := by rfl",
    );
}
#[test]
fn generic_and_dependent_function_domains_are_not_guessed() {
    check(
        "def identity {A : Type} : A -> A := fun | value => value\n\
 def dependent : forall A : Type, A -> A := fun | A, value => value\n\
 theorem a : identity 9 = 9 := by rfl\n theorem b : dependent Bool false = false := by rfl",
    );
}
#[test]
fn expected_indexed_results_are_refined_in_each_branch() {
    check(
        "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (Nat.succ n)\n\
 def tail {A : Type} (n : Nat) : Vec A (Nat.succ n) -> Vec A n := fun | .cons k x xs => xs\n\
 theorem t : tail 0 (Vec.cons 0 7 Vec.nil) = Vec.nil := by rfl\n\
 structure Package where\n carrier : Type\n value : carrier\n\
 def unpack : forall p : Package, p.carrier := fun | .mk A value => value\n\
 def package : Package := { carrier := Nat, value := 8 }\n theorem p : unpack package = 8 := by rfl",
    );
}
#[test]
fn proof_bodies_keep_local_facts_and_their_own_scopes() {
    check(
        "theorem same : forall b : Bool, b = b := fun\n | true => by\n   have h : true = true := rfl\n   exact h\n | false => by rfl\n\
 theorem used : same true = same true := by rfl\n\
 def saved : Nat := by\n let f : Bool -> Nat := fun | true => 7 | false => 8\n exact f true\ntheorem seven : saved = 7 := by rfl",
    );
}
#[test]
fn record_methods_receive_expected_pattern_function_types() {
    check(
        "structure Function where\n run : Bool -> Nat\n\
 def f : Function := { run := fun | true => 5 | false => 6 }\n\
 theorem result : f.run false = 6 := by rfl",
    );
}
#[test]
fn every_reachable_branch_and_unused_annotation_remains_checked() {
    for source in [
        "def bad : Bool -> Nat := fun | true => 1 | false => (1 : String)",
        "def bad : Bool -> Nat := fun | true => 1 | false => let ignored := (1 : String); 2",
        "def bad : Bool -> Nat := fun | true => 1",
        "def bad : Bool -> Nat := fun | _ => 1 | false => (1 : String)",
        "theorem bad : forall b : Bool, 0 = 1 := fun | true => by rfl | false => by rfl",
        "def bad : Nat := (fun | true => 1 | false => 2)",
        "def bad : Bool -> Nat := fun | true, false => 1",
        "def bad : Nat -> Nat -> Nat := fun | x,x => x",
    ] {
        reject(source);
    }
}
#[test]
fn branch_bindings_do_not_leak_or_capture_ambient_names() {
    check(
        "def f (n : Nat) : Bool -> Nat := fun | true => n | false => 0\n theorem ok : f 8 true = 8 := by rfl",
    );
    reject(
        "def bad : Bool -> Nat := fun\n | true => by\n   let hidden := 7\n   exact hidden\n | false => hidden",
    );
}
#[test]
fn recursive_calls_inside_pattern_functions_cannot_evade_structural_checks() {
    reject(
        "def bad (n : Nat) : Nat := match n with\n | .zero => 0\n | .succ k => let hidden : Bool -> Nat := fun | true => bad n | false => 0; 0",
    );
}
#[test]
fn pattern_functions_preserve_small_elimination_restrictions() {
    reject(
        "inductive Witness (A : Type) where | intro (x : A)\n\
 inductive Exists (A : Type) : Prop where | intro (x : A)\n\
 def extract (A : Type) : Exists A -> A := fun | .intro x => x",
    );
    check(
        "inductive Exists (A : Type) (P : A -> Prop) : Prop where | intro (x : A) (h : P x)\n\
 theorem preserve (A : Type) (P : A -> Prop) : Exists A P -> Exists A P := fun | .intro x h => Exists.intro x h",
    );
}
#[test]
fn an_unused_invalid_pattern_function_still_reaches_the_kernel() {
    let source = "theorem bad : 0 = 0 := by\n have ignored : Bool -> Nat := fun | true => 1 | false => (1 : String)\n rfl";
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let error = engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_err();
    assert!(
        error.disposition().1,
        "expected actual checking rejection, got {error:?}"
    );
}
