//! Indexed higher-order recursive fields keep their checked child indices.
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
const TREE: &str = "inductive IndexedTree : Nat -> Type where | leaf (index : Nat) (value : Nat) : IndexedTree index | node (children : (index : Nat) -> IndexedTree index) : IndexedTree 0\n";
const READ: &str = "def read (index : Nat) (tree : IndexedTree index) : Nat := by\n  induction tree with\n  | leaf k value => exact value\n  | node children ih => exact ih 42\n";
#[test]
fn indexed_function_children_use_the_called_child_index() {
    run(
        &format!("{TREE}{READ}#eval read 0 (IndexedTree.node (fun i => IndexedTree.leaf i i))"),
        "42",
    );
}

#[test]
fn several_indices_and_prior_constructor_fields_keep_lexical_scope() {
    run(
        r#"inductive Route : Nat -> Bool -> String -> Type where
  | leaf (n : Nat) (b : Bool) (s : String) (value : Nat) : Route n b s
  | node (offset : Nat) (child : (n : Nat) -> (b : Bool) -> (s : String) -> Route (offset + n) b s) : Route offset true "root"
def read (n : Nat) (b : Bool) (s : String) (route : Route n b s) : Nat := by
  induction route with
  | leaf n b s value => exact n + value + String.length s
  | node offset child ih => exact ih 20 true "ok"
#eval read 20 true "root" (Route.node 20 (fun n b s => Route.leaf (20 + n) b s (if b then 0 else 100)))"#,
        "42",
    );
}

#[test]
fn indexed_children_keep_captured_values_and_accumulator_stages() {
    run(
        &format!(
            "{TREE}def fold (offset : Nat) (index : Nat) (tree : IndexedTree index) : Nat -> Nat := by\n  induction tree with\n  | leaf k value => exact fun acc => value + offset + acc\n  | node children ih => exact fun acc => ih 20 (acc + 2)\n#eval fold 10 0 (IndexedTree.node (fun i => IndexedTree.leaf i i)) 10"
        ),
        "42",
    );
}

#[test]
fn mapped_indexed_children_escape_the_mapping_call_without_losing_captures() {
    run(
        r#"inductive Tree : Nat -> Type where
  | leaf (index : Nat) (value : Nat) : Tree index
  | node (index : Nat) (child : (n : Nat) -> Tree n) : Tree index
def map (delta : Nat) (index : Nat) (tree : Tree index) : Tree index := by
  induction tree with
  | leaf k value => exact Tree.leaf k (value + delta)
  | node k child ih => exact Tree.node k (fun n => ih n)
def read (index : Nat) (tree : Tree index) : Nat := by
  induction tree with
  | leaf k value => exact value
  | node k child ih => exact ih 20
#eval read 0 (map 2 0 (Tree.node 0 (fun i => Tree.node i (fun j => Tree.leaf j (i + j)))))"#,
        "42",
    );
}

#[test]
fn proof_arguments_are_checked_before_becoming_inert_callback_slots() {
    run(
        r#"inductive Proven : Nat -> Type where
  | leaf (index : Nat) (value : Nat) : Proven index
  | node (child : (index : Nat) -> index = index -> Proven index) : Proven 0
def read (index : Nat) (tree : Proven index) : Nat := by
  induction tree with
  | leaf k value => exact value
  | node child ih => exact ih 40 (Eq.refl 40)
#eval read 0 (Proven.node (fun i h => Proven.leaf i (i + 2)))"#,
        "42",
    );
}

#[test]
fn actual_child_index_computations_are_strict_but_unused_hypotheses_stay_lazy() {
    let source = r#"def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1
inductive Expensive : Nat -> Type where
  | leaf (index : Nat) (value : Nat) : Expensive index
  | node (child : (i : Nat) -> Expensive (work i)) : Expensive 0
def read (index : Nat) (tree : Expensive index) : Nat := by
  induction tree with
  | leaf k value => exact value
  | node child ih => exact ih 80
def ignore (index : Nat) (tree : Expensive index) : Nat := by
  induction tree with
  | leaf k value => exact value
  | node child ih => exact 42
"#;
    let idle = run(
        &format!("{source}#eval ignore 0 (Expensive.node (fun i => Expensive.leaf (work i) 42))"),
        "42",
    );
    let used = run(
        &format!("{source}#eval read 0 (Expensive.node (fun i => Expensive.leaf (work i) 42))"),
        "42",
    );
    let direct = run(
        &format!("{source}#eval read 80 (Expensive.leaf (work 80) 42)"),
        "42",
    );
    let zero = source.replace("exact ih 80", "exact ih 0");
    let used_zero = run(
        &format!("{zero}#eval read 0 (Expensive.node (fun i => Expensive.leaf (work i) 42))"),
        "42",
    );
    let direct_zero = run(
        &format!("{zero}#eval read 0 (Expensive.leaf (work 0) 42)"),
        "42",
    );
    // One work call produces the constructor index; one computes the actual
    // recursive-call index. Both scale identically, while all dispatch overhead
    // is fixed. Dropping or duplicating either ordinary computation fails this.
    assert_eq!(used - used_zero, 2 * (direct - direct_zero));
    assert!(
        direct > idle + 80,
        "ordinary constructor index computation was discarded"
    );
}

#[test]
fn invalid_indexed_children_cannot_publish_and_valid_calls_recover() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for bad in [
        "def bad : IndexedTree 0 := IndexedTree.node (fun i => IndexedTree.leaf 0 i)",
        "def bad (n : Nat) (t : IndexedTree n) : Nat := match t with | .leaf k value => value | .node child => bad n t",
        "inductive Bad : Nat -> Type where | mk (f : Bad 0 -> Nat) : Bad 0",
    ] {
        assert!(
            base.execute_source_definitions(
                &[format!("{TREE}#eval 42\n{bad}").as_bytes()],
                &options,
                limits()
            )
            .is_err(),
            "{bad}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
    let source =
        format!("{TREE}{READ}#eval read 0 (IndexedTree.node (fun i => IndexedTree.leaf i i))");
    let mut small = limits();
    small.ingress.fir.max_closure_types = 0;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, small)
            .is_err()
    );
    let mut small = limits();
    small.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, small)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    let execute = || {
        base.execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = execute();
    let second = execute();
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn ground_element_specializations_do_not_mix_payload_layouts() {
    run(
        r#"inductive Tree (A : Type u) : Nat -> Type u where
  | leaf (index : Nat) (value : A) : Tree A index
  | node (child : (i : Nat) -> Tree A i) : Tree A 0
def read {A : Type u} (index : Nat) (tree : Tree A index) : A := by
  induction tree with
  | leaf k value => exact value
  | node child ih => exact ih 0
#eval read 0 (Tree.node (fun i => Tree.leaf i 37)) + String.length (read 0 (Tree.node (fun i => Tree.leaf i "hello")))"#,
        "42",
    );
}

#[test]
fn structural_source_recursion_selects_indexed_function_children() {
    run(
        &format!(
            "{TREE}def follow (index : Nat) (tree : IndexedTree index) : Nat := match tree with | .leaf k value => value | .node child => follow 40 (child 40)\n#eval follow 0 (IndexedTree.node (fun i => IndexedTree.leaf i (i + 2)))"
        ),
        "42",
    );
}
