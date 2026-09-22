//! Function-valued recursive children execute only through admitted recursors.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Outcome, VmExit};

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
        panic!("VM return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}

const TREE: &str =
    "inductive Branching where | leaf (value : Nat) | node (children : Nat -> Branching)\n";

#[test]
fn function_children_construct_and_match_without_forcing_other_children() {
    run(
        &format!(
            r#"{TREE}
def first (t : Branching) : Nat := match t with
  | .leaf n => n
  | .node children => match children 2 with
    | .leaf n => n
    | .node other => 0
#eval first (Branching.node (fun n => Branching.leaf (40 + n)))"#
        ),
        "42",
    );
}

#[test]
fn structural_calls_on_function_children_keep_changing_accumulators() {
    run(
        &format!(
            r#"{TREE}
def follow (t : Branching) (route : Nat) : Nat := match t with
  | .leaf n => n + route
  | .node children => follow (children route) (route + 1)
#eval follow (Branching.node (fun n => Branching.leaf n)) 20"#
        ),
        "41",
    );
}

#[test]
fn multiple_child_arguments_and_callback_domains_keep_their_order() {
    run(
        r#"
inductive Tree where
  | leaf (n : Nat)
  | node (child : Nat -> Bool -> Tree)
def follow (t : Tree) : Nat := match t with
  | .leaf n => n
  | .node child => follow (child 40 true)
#eval follow (Tree.node (fun n b => if b then Tree.leaf (n + 2) else Tree.leaf 0))
"#,
        "42",
    );
    run(
        r#"
inductive Tree where
  | leaf (n : Nat)
  | node (child : (Nat -> Nat) -> Tree)
def follow (t : Tree) : Nat := match t with
  | .leaf n => n
  | .node child => let bump (n : Nat) : Nat := n + 2; follow (child bump)
#eval follow (Tree.node (fun f => Tree.leaf (f 40)))
"#,
        "42",
    );
}

#[test]
fn mapped_children_retain_recursive_closures_after_the_parent_returns() {
    run(
        &format!(
            r#"{TREE}
def map (delta : Nat) (t : Branching) : Branching := match t with
  | .leaf n => Branching.leaf (n + delta)
  | .node child => Branching.node (fun n => map delta (child n))
def follow (t : Branching) (route : Nat) : Nat := match t with
  | .leaf n => n
  | .node child => follow (child route) (route + 1)
def sample : Branching := Branching.node (fun n => Branching.node (fun m => Branching.leaf (n + m)))
#eval follow (map 3 sample) 19"#
        ),
        "42",
    );
}

#[test]
fn mixed_recursive_field_arities_preserve_hypothesis_order() {
    run(
        r#"
inductive Tree where
  | leaf (n : Nat)
  | node (first : Nat -> Tree) (middle : Tree) (last : Bool -> Nat -> Tree)
def sum (t : Tree) : Nat := match t with
  | .leaf n => n
  | .node first middle last => sum (first 1) + sum middle + sum (last true 2)
#eval sum (Tree.node (fun n => Tree.leaf (19 + n)) (Tree.leaf 10) (fun b n => if b then Tree.leaf (10 + n) else Tree.leaf 0))
"#,
        "42",
    );
}

#[test]
fn generic_function_children_specialize_without_mixing_payload_layouts() {
    run(
        r#"
inductive Tree (A : Type u) where
  | leaf (value : A)
  | node (child : Nat -> Tree A)
def readNat (t : Tree Nat) : Nat := match t with
  | .leaf n => n
  | .node f => readNat (f 2)
def readText (t : Tree String) : String := match t with
  | .leaf text => text
  | .node f => readText (f 0)
#eval readNat (Tree.node (fun n => Tree.leaf (35 + n))) + String.length (readText (Tree.node (fun n => Tree.leaf "hello")))
"#,
        "42",
    );
}

#[test]
fn constructor_initializers_are_strict_but_child_bodies_are_lazy() {
    let definitions = format!(
        r#"{TREE}
def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1
def ignore (t : Branching) : Nat := match t with | .leaf n => n | .node child => 42
def computed (n : Nat) : Branching := let value : Nat := work n; Branching.node (fun i => Branching.leaf value)
"#
    );
    let idle = run(
        &format!("{definitions}#eval ignore (Branching.node (fun n => Branching.leaf n))"),
        "42",
    );
    let lazy = run(
        &format!(
            "{definitions}#eval ignore (Branching.node (fun n => Branching.leaf (work 2000)))"
        ),
        "42",
    );
    assert!(lazy < idle + 20, "unselected child body was executed");
    let strict = run(&format!("{definitions}#eval ignore (computed 80)"), "42");
    assert!(
        strict > idle + 80,
        "computed child initializer was discarded"
    );
}

#[test]
fn invalid_function_children_and_nondecreasing_recursion_publish_nothing() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for bad in [
        "def bad : Branching := Branching.node (fun n => let x : String := n; Branching.leaf n)",
        "def bad (t : Branching) : Nat := match t with | .leaf n => n | .node f => bad t",
        "inductive Bad where | mk (f : Bad -> Nat)",
    ] {
        assert!(
            base.execute_source_definitions(
                &[format!("{TREE}#eval 42\n{bad}").as_bytes()],
                &options,
                limits(),
            )
            .is_err(),
            "{bad}"
        );
        assert_eq!(base.logical_root(&options), before);
    }
}

#[test]
fn resource_stops_are_nonanswers_and_recovery_is_byte_identical() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let source = format!(
        r#"{TREE}
def make (n : Nat) : Branching := match n with
  | .zero => Branching.leaf 42
  | .succ k => Branching.node (fun i => make k)
def read (t : Branching) : Nat := match t with
  | .leaf n => n
  | .node f => read (f 0)
#eval read (make 30)"#
    );
    let mut small = limits();
    small.ingress.fir.max_closure_types = 0;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, small)
            .is_err()
    );
    let mut small = limits();
    small.vm.max_steps = 10;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, small)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), before);
    let first = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let retry = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        retry.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(
        first.engine.logical_root(&options),
        retry.engine.logical_root(&options)
    );
}
