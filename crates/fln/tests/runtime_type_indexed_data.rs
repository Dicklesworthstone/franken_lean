//! Genuine Type indices choose no native layout. Scalar indices remain strict,
//! and a motive must still have one checked runtime result representation.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits, KVMap,
    Outcome, SourceCheckLimits, VmExit,
};
use fln_comp::ingress::{IngressError, IngressResource};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}

fn execute(base: &Engine, source: &str) -> fln::DefinitionBatchExecution {
    base.execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn cause(mut error: EngineExecutionError) -> EngineExecutionError {
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    error
}

fn run(source: &str, expected: &str) -> u64 {
    let batch = execute(&engine(), source);
    for execution in &batch.executions {
        assert!(matches!(execution.exit, VmExit::Returned(_)), "{source}");
    }
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

// Structural source recursion is executable by the pinned Reference too;
// its compiler refuses direct `by induction` Type-indexed data recursors.
const TREE: &str = r#"inductive TypedTree : Type -> Type 1 where
  | nat (value : Nat) : TypedTree Nat
  | text (value : String) : TypedTree String
  | join (A : Type) (B : Type) (left : TypedTree A) (right : TypedTree B) : TypedTree Nat
def total (A : Type) (tree : TypedTree A) : Nat := match tree with
  | .nat value => value
  | .text value => String.length value
  | .join A B left right => total A left + total B right
"#;

#[test]
fn heterogeneous_type_indexed_trees_fold_across_different_child_indices() {
    let source = format!(
        "{TREE}#eval total Nat (TypedTree.join Nat String (TypedTree.nat 37) (TypedTree.text \"hello\"))"
    );
    run(&source, "42");
    let checked = engine()
        .check_source_files(
            &[TREE.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let Some(ConstantInfo::Induct(family)) = checked
        .engine
        .environment()
        .find(&Name::from_components(["TypedTree"]))
    else {
        panic!("admitted typed family")
    };
    assert_eq!(family.num_params, 0, "not a promoted type parameter");
    assert_eq!(family.num_indices, 1);
}

#[test]
fn uniform_index_dependent_reconstruction_survives_ordinary_containers() {
    run(
        &format!(
            r#"{TREE}def copy (A : Type) (tree : TypedTree A) : TypedTree A := match tree with
  | .nat value => TypedTree.nat value
  | .text value => TypedTree.text value
  | .join A B left right => TypedTree.join A B (copy A left) (copy B right)
def totals (xs : List (TypedTree Nat)) : Nat := xs.foldl (fun (acc : Nat) (tree : TypedTree Nat) => acc + total Nat tree) 0
#eval totals [copy Nat (TypedTree.join Nat String (TypedTree.nat 17) (TypedTree.text "hello")), TypedTree.nat 20]"#
        ),
        "42",
    );
}

#[test]
fn type_indexed_payloads_keep_boxed_callbacks_and_concrete_calling_interfaces() {
    run(
        r#"inductive Packed : Type -> Type 1 where
  | data (A : Type) (value : A) (measure : A -> Nat) : Packed A
  | blank : Packed Bool
def read (A : Type) (value : Packed A) : Nat := match value with
  | .data A value measure => measure value
  | .blank => 0
#eval read Nat (Packed.data Nat 37 (fun n => n)) + read String (Packed.data String "hello" String.length) + read Bool Packed.blank"#,
        "42",
    );
}

#[test]
fn mixed_type_and_value_indices_keep_function_children_and_accumulator_stages() {
    run(
        r#"inductive Route : Type -> Nat -> Type where
  | leaf (index : Nat) (value : Nat) : Route Nat index
  | node (offset : Nat) (child : (i : Nat) -> Route Nat (offset + i)) : Route Bool offset
def fold (A : Type) (index : Nat) (route : Route A index) : Nat -> Nat := match route with
  | .leaf index value => fun acc => value + acc
  | .node offset child => fun acc => fold Nat (offset + 20) (child 20) (acc + 2)
#eval fold Bool 20 (Route.node 20 (fun i => Route.leaf (20 + i) i)) 20"#,
        "42",
    );
}

const STRICT: &str = r#"def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1
inductive Expensive : Nat -> Type -> Type where
  | leaf (index : Nat) (value : Nat) : Expensive index Nat
  | node (child : (i : Nat) -> Expensive (work i) Nat) : Expensive 0 Bool
def read (index : Nat) (A : Type) (tree : Expensive index A) : Nat := match tree with
  | .leaf index value => value
  | .node child => read (work 80) Nat (child 80)
def ignore (index : Nat) (A : Type) (tree : Expensive index A) : Nat := match tree with
  | .leaf index value => value
  | .node child => 42
"#;

#[test]
fn type_index_erasure_does_not_discard_or_duplicate_actual_value_indices() {
    let idle = run(
        &format!(
            "{STRICT}#eval ignore 0 Bool (Expensive.node (fun i => Expensive.leaf (work i) 42))"
        ),
        "42",
    );
    let used = run(
        &format!(
            "{STRICT}#eval read 0 Bool (Expensive.node (fun i => Expensive.leaf (work i) 42))"
        ),
        "42",
    );
    let direct = run(
        &format!("{STRICT}#eval read 80 Nat (Expensive.leaf (work 80) 42)"),
        "42",
    );
    let zero = STRICT.replace(
        "read (work 80) Nat (child 80)",
        "read (work 0) Nat (child 0)",
    );
    let used_zero = run(
        &format!("{zero}#eval read 0 Bool (Expensive.node (fun i => Expensive.leaf (work i) 42))"),
        "42",
    );
    let direct_zero = run(
        &format!("{zero}#eval read 0 Nat (Expensive.leaf (work 0) 42)"),
        "42",
    );
    // One call computes the actual child's constructor index, and one the
    // recursor call's index. Erasing the neighboring Type slot changes neither.
    assert_eq!(used - used_zero, 2 * (direct - direct_zero));
    assert!(direct > idle + 80, "ordinary index computation was dropped");
}

const SELECTED: &str = r#"inductive Selected : Type -> Type 1 where
  | pack (A : Type) (value : A) : Selected A
  | nat (value : Nat) : Selected Nat
def extract (A : Type) (value : Selected A) : A := match value with
  | .pack A value => value
  | .nat value => value
"#;

#[test]
fn type_index_selected_results_preserve_scalar_object_and_callback_payloads() {
    for (expression, expected) in [
        ("extract Nat (Selected.nat 42)", "42"),
        ("extract Nat (Selected.pack Nat 42)", "42"),
        (
            "extract Nat (Selected.pack Nat 18446744073709551616)",
            "18446744073709551616",
        ),
        (
            r#"String.length (extract String (Selected.pack String "hello")) + 37"#,
            "42",
        ),
        (
            "if extract Bool (Selected.pack Bool true) then 42 else 0",
            "42",
        ),
        (
            "if extract Bool (Selected.pack Bool false) then 0 else 42",
            "42",
        ),
        (
            "List.foldl (fun (acc : Nat) (n : Nat) => acc + n) 0 (extract (List Nat) (Selected.pack (List Nat) [20, 22]))",
            "42",
        ),
        (
            "let f : Nat -> Nat := extract (Nat -> Nat) (Selected.pack (Nat -> Nat) (fun n => n + 5)); f 37",
            "42",
        ),
        (
            r#"let f : String -> Nat := extract (String -> Nat) (Selected.pack (String -> Nat) (fun s => String.length s + 37)); f "hello""#,
            "42",
        ),
    ] {
        run(&format!("{SELECTED}#eval {expression}"), expected);
    }
}

#[test]
fn type_index_selected_results_survive_recursive_wrappers_and_captured_functions() {
    let source = r#"inductive Wrapped : Type -> Type 1 where
  | pack (A : Type) (value : A) : Wrapped A
  | nat (value : Nat) : Wrapped Nat
  | next (A : Type) (child : Wrapped A) : Wrapped A
def extract (A : Type) (value : Wrapped A) : A := match value with
  | .pack A value => value
  | .nat value => value
  | .next A child => extract A child
def result (offset : Nat) : Nat :=
  let packed := Wrapped.next (Nat -> Nat) (Wrapped.pack (Nat -> Nat) (fun n => offset + n))
  let f : Nat -> Nat := extract (Nat -> Nat) packed
  f 5
#eval result 37"#;
    run(source, "42");
}

#[test]
fn type_index_selected_payloads_execute_once_and_retry_after_resource_stops() {
    let prefix = format!(
        "{SELECTED}def work (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) n\n"
    );
    let selected = |n| format!("{prefix}#eval extract Nat (Selected.pack Nat (work {n} + 42))");
    let direct = |n| format!("{prefix}#eval work {n} + 42");
    assert_eq!(
        run(&selected(80), "42") - run(&selected(0), "42"),
        run(&direct(80), "42") - run(&direct(0), "42"),
        "boxing must preserve exactly one payload evaluation"
    );

    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = selected(80);
    let mut bounded = limits();
    bounded.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    let first = execute(&base, &source);
    let second = execute(&base, &source);
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn index_computed_runtime_results_and_dependent_layouts_remain_refusals() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        r#"inductive Selected : Type -> Type 1 where
  | pack (A : Type) (value : A) : Selected A
  | nat (value : Nat) : Selected Nat
def extractList (A : Type) (value : Selected A) : List A := match value with
  | .pack A value => [value]
  | .nat value => [value]
#eval extractList Nat (Selected.nat 42)"#,
        r#"inductive Dependent : (A : Type) -> A -> Type 1 where
  | nat (n : Nat) : Dependent Nat n
  | flag (b : Bool) : Dependent Bool b
def ignore (value : Dependent Nat 7) : Nat := 42
#eval ignore (Dependent.nat 7)"#,
        r#"inductive Changing : Type -> Type 1 where
  | pack (b : Bool) (value : if b then Nat else String) : Changing Nat
  | flag (b : Bool) : Changing Bool
def ignore (value : Changing Nat) : Nat := 42
#eval ignore (Changing.pack true (7 : Nat))"#,
    ] {
        // These are genuine runtime refusals after both logical checkers have
        // admitted the same declarations, not invalid syntax/type controls.
        base.check_source_files(
            &[source.split("#eval").next().unwrap().as_bytes()],
            &options,
            SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
        let error = cause(
            base.execute_source_definitions(&[source.as_bytes()], &options, limits())
                .expect_err(source),
        );
        assert!(
            matches!(&error, EngineExecutionError::Ingress(reason) if !reason.is_resource_exhaustion()),
            "{error:?}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn wrong_type_indices_and_stopped_execution_are_atomic_and_retryable() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let invalid = format!("{TREE}#eval 42\ndef bad : TypedTree Bool := TypedTree.nat 42");
    assert!(
        base.execute_source_definitions(&[invalid.as_bytes()], &options, limits())
            .is_err()
    );
    let source = format!(
        "{TREE}#eval total Nat (TypedTree.join Nat String (TypedTree.nat 37) (TypedTree.text \"hello\"))"
    );
    for kind in 0..2 {
        let mut bounded = limits();
        if kind == 0 {
            bounded.ingress.max_nodes = 1;
        } else {
            bounded.ingress.fir.max_closure_types = 0;
        }
        let error = cause(
            base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
                .expect_err("bounded native compilation"),
        );
        let expected_resource = if kind == 0 {
            matches!(
                error,
                EngineExecutionError::Ingress(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes,
                    limit: 1,
                    ..
                })
            )
        } else {
            matches!(
                error,
                EngineExecutionError::Ingress(IngressError::ResourceLimit {
                    resource: IngressResource::ProgramTables,
                    limit: 0,
                    observed: 1,
                })
            )
        };
        assert!(expected_resource, "{error:?}");
        assert_eq!(base.logical_root(&options), root);
    }
    let mut bounded = limits();
    bounded.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    let first = execute(&base, &source);
    let second = execute(&base, &source);
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}
