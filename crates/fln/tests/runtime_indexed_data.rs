//! Indexed data executes only after ordinary dual-checker admission.
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
const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where | nil : Vec A 0 | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n";
fn run(source: &str, expected: &str) -> u64 {
    let batch = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
        panic!("native return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}
#[test]
fn indexed_constructor_arguments_have_uniform_runtime_layouts() {
    run(
        &format!(
            "{VEC}def ignore (n : Nat) (xs : Vec Nat n) : Nat := 42\n#eval ignore 1 (Vec.cons 0 7 Vec.nil)"
        ),
        "42",
    );
}
#[test]
fn indexed_cases_extract_real_fields() {
    run(
        &format!(
            "{VEC}def head (n : Nat) (xs : Vec Nat n) : Nat := match xs with | .nil => 0 | .cons k x tail => x\n#eval head 2 (Vec.cons 1 42 (Vec.cons 0 7 Vec.nil))"
        ),
        "42",
    );
}
#[test]
fn indexed_recursors_compute_and_return_refined_data() {
    run(
        &format!(
            "{VEC}def length {{A : Type}} (n : Nat) (xs : Vec A n) : Nat := by\n  induction xs with\n  | nil => exact 0\n  | cons k x tail ih => exact Nat.succ ih\n#eval length 2 (Vec.cons 1 7 (Vec.cons 0 9 Vec.nil))"
        ),
        "2",
    );
}

#[test]
fn dependent_motives_return_vectors_without_length_specific_layouts() {
    run(
        &format!(
            "{VEC}\
        def copy {{A : Type}} (n : Nat) (xs : Vec A n) : Vec A n := by\n  induction xs with\n  | nil => exact Vec.nil\n  | cons k x tail ih => exact Vec.cons k x ih\n\
        def total (n : Nat) (xs : Vec Nat n) : Nat := by\n  induction xs with\n  | nil => exact 0\n  | cons k x tail ih => exact x + ih\n\
        #eval total 2 (copy 2 (Vec.cons 1 37 (Vec.cons 0 5 Vec.nil)))"
        ),
        "42",
    );
}

#[test]
fn indexed_folds_preserve_captures_and_accumulator_arguments() {
    run(
        &format!(
            "{VEC}\
        def fold (offset : Nat) (n : Nat) (xs : Vec Nat n) : Nat -> Nat := by\n  induction xs with\n  | nil => exact fun acc => acc + offset\n  | cons k x tail ih => exact fun acc => ih (acc + x)\n\
        #eval fold 2 2 (Vec.cons 1 20 (Vec.cons 0 17 Vec.nil)) 3"
        ),
        "42",
    );
}

#[test]
fn multiple_indices_and_recursive_fields_keep_distinct_arguments() {
    run(
        "inductive Path : Nat -> Nat -> Type where\n\
         | refl (a : Nat) : Path a a\n\
         | join (a b c : Nat) (left : Path a b) (right : Path b c) : Path a c\n\
         def count (a b : Nat) (p : Path a b) : Nat := by\n  induction p with\n  | refl k => exact k\n  | join a b c first second ih1 ih2 => exact ih1 + ih2\n\
         #eval count 21 21 (Path.join 21 21 21 (Path.refl 21) (Path.refl 21))",
        "42",
    );
}

#[test]
fn nonrecursive_singleton_and_sum_indices_use_checked_tags() {
    run(
        "inductive Tagged : Bool -> Type where | no (n : Nat) : Tagged false | yes (s : String) : Tagged true\n\
         def size (b : Bool) (v : Tagged b) : Nat := by\n  cases v with\n  | no n => exact n\n  | yes s => exact String.length s\n\
         #eval size false (Tagged.no 37) + size true (Tagged.yes \"hello\")",
        "42",
    );
    run(
        "inductive Named : String -> Type where | make (n : Nat) : Named \"x\"\n\
         def value (s : String) (v : Named s) : Nat := by\n  cases v with\n  | make n => exact n\n\
         #eval value \"x\" (Named.make 42)",
        "42",
    );
}

#[test]
fn indexed_values_cross_collection_and_callback_boundaries() {
    run(
        &format!(
            "{VEC}\
        def size {{A : Type}} (n : Nat) (v : Vec A n) : Nat := by\n  induction v with\n  | nil => exact 0\n  | cons k x tail ih => exact ih + 1\n\
        def apply (f : Vec Nat 1 -> Nat) : Nat := f (Vec.cons 0 42 Vec.nil)\n\
        #eval apply (fun v => size 1 v) + List.length [Vec.cons 0 true Vec.nil, Vec.cons 0 false Vec.nil]"
        ),
        "3",
    );
}

#[test]
fn proof_fields_remain_checked_and_erased_in_indexed_data() {
    run(
        "inductive Checked : Nat -> Type where\n\
         | stop : Checked 0\n\
         | more (n : Nat) (h : n = n) (tail : Checked n) : Checked (Nat.succ n)\n\
         def size (n : Nat) (x : Checked n) : Nat := by\n  induction x with\n  | stop => exact 0\n  | more k h tail ih => exact ih + 1\n\
         #eval size 2 (Checked.more 1 (by rfl) (Checked.more 0 (by rfl) Checked.stop))",
        "2",
    );
}

#[test]
fn stored_indices_and_call_indices_are_strict_ordinary_computations() {
    let prefix = format!(
        "{VEC}\
        def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\n\
        def ignore (n : Nat) (v : Vec Nat n) : Nat := 42\n"
    );
    let idle = run(
        &format!("{prefix}#eval ignore 1 (Vec.cons 0 7 Vec.nil)"),
        "42",
    );
    let busy = run(
        &format!("{prefix}#eval ignore (work 1) (Vec.cons (work 0) 7 Vec.nil)"),
        "42",
    );
    assert!(
        busy > idle,
        "ordinary index computation was discarded: {idle} vs {busy}"
    );
    // A closed index annotation does not license evaluating or discarding an
    // expensive ordinary constructor field whose result has that index.
    let source = "inductive Tagged : Nat -> Type where | make (n : Nat) : Tagged 0\n\
        def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\n\
        def ignore (x : Tagged 0) : Nat := 42\n";
    let idle = run(&format!("{source}#eval ignore (Tagged.make 0)"), "42");
    let busy = run(
        &format!("{source}#eval ignore (Tagged.make (work 30))"),
        "42",
    );
    assert!(
        busy > idle + 30,
        "strict constructor field was discarded: {idle} vs {busy}"
    );
}

#[test]
fn invalid_indices_and_static_obligations_never_publish() {
    use fln::{Outcome, SourceCheckLimits};
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for suffix in [
        "def invalid : Vec Nat 1 := Vec.nil",
        "def invalid : Vec Nat 2 := Vec.cons 0 7 Vec.nil",
        "def invalid : Vec Nat 1 := Vec.cons 0 true Vec.nil",
        "def invalid : Nat := let T : Type := (1 : Type); 42",
    ] {
        let source = format!("{VEC}{suffix}\n#eval 42");
        assert!(
            !matches!(
                base.execute_source_definitions(&[source.as_bytes()], &options, limits()),
                Ok(Outcome::Complete(_))
            ),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
    let source = format!(
        "{VEC}def keep (n : Nat) (v : Vec Nat n) : Nat := 42\ndef result : Nat := keep 1 (Vec.cons 0 7 Vec.nil)"
    );
    let executed = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let checked = base
        .check_source_files(
            &[source.split("#eval").next().unwrap().as_bytes()],
            &options,
            SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        executed.engine.logical_root(&options),
        checked.engine.logical_root(&options)
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn type_indices_and_existential_runtime_representations_are_refused() {
    use fln::{Outcome, SourceCheckLimits};
    for source in [
        "inductive Dynamic : Type -> Type where | nat (n : Nat) : Dynamic Nat | flag (b : Bool) : Dynamic Bool\n\
         def ignore (x : Dynamic Nat) : Nat := 42\n#eval ignore (Dynamic.nat 7)",
        "inductive Dynamic : Nat -> Type 1 where | pack (A : Type) (value : A) : Dynamic 0\n\
         def ignore (x : Dynamic 0) : Nat := 42\n#eval ignore (Dynamic.pack Bool true)",
    ] {
        let base = engine();
        let options = KVMap::new();
        let root = base.logical_root(&options);
        // These are valid logical declarations, not parser-error controls.
        base.check_source_files(
            &[source.split("#eval").next().unwrap().as_bytes()],
            &options,
            SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        assert!(
            !matches!(
                base.execute_source_definitions(&[source.as_bytes()], &options, limits()),
                Ok(Outcome::Complete(_))
            ),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn stopped_indexed_execution_is_atomic_and_deterministically_retryable() {
    use fln::Outcome;
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!(
        "{VEC}def size (n : Nat) (xs : Vec Nat n) : Nat := by\n  induction xs with\n  | nil => exact 0\n  | cons k x tail ih => exact ih + 1\n#eval size 1 (Vec.cons 0 42 Vec.nil)"
    );
    for bound in 0..3 {
        let mut limited = limits();
        match bound {
            0 => limited.ingress.max_nodes = 1,
            1 => limited.ingress.max_lambda_bindings = 0,
            _ => limited.ingress.max_context_depth = 1,
        }
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &options, limited)
                .is_err()
        );
    }
    let mut limited = limits();
    limited.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, limited)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    let one = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let two = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        one.executions.last().unwrap().flbc_artifact,
        two.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn used_induction_hypotheses_are_shared_instead_of_expanded() {
    let mut source = format!(
        "{VEC}def count (n : Nat) (xs : Vec Nat n) : Nat := by\n  induction xs with\n  | nil => exact 1\n  | cons k x tail ih => exact ih + ih\n#eval count 20 ("
    );
    for n in (0..20).rev() {
        source.push_str(&format!("Vec.cons {n} 0 ("));
    }
    source.push_str("Vec.nil");
    source.push_str(&")".repeat(21));
    let steps = run(&source, "1048576");
    assert!(steps < 10_000, "repeated recursive work: {steps}");
}
