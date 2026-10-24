//! Runtime motive normalization must not guess a dependent representation.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Mode, VmExit};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
/// Directly written recursors execute only in the `frontier` mode; the default refuses
/// them as the pin's code generator does (bead `franken_lean-z8j.1.6.6`).
fn engine() -> Engine {
    Engine::builder()
        .mode(Mode::Frontier)
        .build_with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn execute(source: &str, expected: &str) {
    execute_in(engine(), source, expected);
}
fn execute_in(engine: Engine, source: &str, expected: &str) {
    let run = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("execution did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

#[test]
fn constructor_index_arithmetic_does_not_require_an_executable_history_layout() {
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    execute_in(
        engine,
        "inductive Vec (α : Type) : Nat → Type\n\
         | nil : Vec α 0\n\
         | cons : α → {n : Nat} → Vec α n → Vec α (n+1)\n\
         open Vec\n\
         def h1 : Vec Nat (n+1) → Nat\n\
         | cons b bv => b\n\
         #eval h1 (cons 42 nil)",
        "42",
    );
}

#[test]
fn dynamic_and_nonzero_motives_with_different_runtime_families_still_refuse() {
    let definitions = "def Vary : Nat → Type\n\
        | 0 => Nat\n\
        | n+1 => Bool\n";
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for declaration in [
        "def choose (n : Nat) : Vary n := @Nat.rec Vary (42 : Nat) (fun n ih => (true : Bool)) n",
        "def choose : Vary 1 := @Nat.rec Vary (42 : Nat) (fun n ih => (true : Bool)) 1",
    ] {
        let source = format!("{definitions}{declaration}");
        base.check_source_files(
            &[source.as_bytes()],
            &options,
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap_or_else(|error| panic!("the refusal control must be checked source: {error:?}"))
        .into_complete()
        .unwrap();
        let error = base
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .expect_err("an unknown or nonzero major must still require a uniform runtime family");
        assert!(format!("{error:?}").contains("dependent Nat recursor motive"));
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn named_reducible_motives_work_in_direct_and_first_class_recursors() {
    execute(
        "def Result (n : Nat) : Type := Nat\n#eval @Nat.rec Result (0 : Nat) (fun (n ih : Nat) => ih + 1) 42",
        "42",
    );
    execute(
        "def Result (n : Nat) : Type := Nat\n#eval let fold : Nat -> Nat := @Nat.rec Result (0 : Nat) (fun (n ih : Nat) => ih + 1); fold 42",
        "42",
    );
}

#[test]
fn normalized_function_motives_keep_changing_accumulator_arguments() {
    execute(
        "def Accum (n : Nat) : Type := Nat -> Nat\n#eval @Nat.rec Accum (fun (acc : Nat) => acc) (fun (n : Nat) (ih : Nat -> Nat) (acc : Nat) => ih (acc + 1)) 40 2",
        "42",
    );
}

#[test]
fn record_motives_erase_major_dependent_callback_proofs_before_layout_discovery() {
    execute(
        "structure Pair where\n  first : Nat\n  second : Nat\ndef unpack (p : Pair) : ((q : Pair) -> q.first = p.first -> Nat) -> Nat := @Pair.rec (fun p : Pair => ((q : Pair) -> q.first = p.first -> Nat) -> Nat) (fun first second next => next (Pair.mk first second) (Eq.refl first)) p\n#eval unpack (Pair.mk 19 23) (fun q h => q.first + q.second)",
        "42",
    );
}

const VECTORS: &str = "inductive Vec (A : Type) : Nat -> Type where\n  | nil : Vec A 0\n  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\ndef Result (n : Nat) : Type := Vec Nat n\ndef copies (value count : Nat) : Vec Nat count := @Nat.rec Result Vec.nil (fun (n : Nat) (tail : Vec Nat n) => Vec.cons n value tail) count\ndef total (n : Nat) (xs : Vec Nat n) : Nat := by\n  induction xs with\n  | nil => exact 0\n  | cons k x tail ih => exact x + ih\n";

#[test]
fn nat_recursion_returns_uniform_length_indexed_data_at_the_real_index() {
    execute(&format!("{VECTORS}#eval total 6 (copies 7 6)"), "42");
    execute(&format!("{VECTORS}#eval total 0 (copies 7 0)"), "0");
}

#[test]
fn source_length_errors_remain_errors_after_runtime_index_erasure() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let invalid = format!("{VECTORS}#eval total 5 (copies 7 6)");
    assert!(
        base.execute_source_definitions(&[invalid.as_bytes()], &options, limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn layout_discovery_stops_do_not_poison_a_clean_retry() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!("{VECTORS}#eval total 6 (copies 7 6)");
    let mut bounded = limits();
    bounded.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let run = || {
        base.execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    assert_eq!(
        run().executions.last().unwrap().flbc_artifact,
        run().executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}
