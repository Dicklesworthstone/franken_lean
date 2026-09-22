//! Ground mutual families cross the checked-source/FIR/VM boundary natively.
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
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
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
const TREE: &str = "mutual\ninductive Tree (A : Type) where | node (value : A) (children : Forest A)\ninductive Forest (B : Type) where | nil | cons (head : Tree B) (tail : Forest B)\nend\n";
const HEAD: &str = "def value (t : Tree Nat) : Nat := match t with | .node n children => n\ndef first (xs : Forest Nat) : Nat := match xs with | .nil => 0 | .cons t rest => value t\n";

#[test]
fn both_family_positions_and_colliding_local_tags_execute() {
    run(
        &format!("{TREE}{HEAD}#eval value (Tree.node 42 (@Forest.nil Nat))"),
        "42",
    );
    run(
        &format!(
            "{TREE}{HEAD}#eval first (Forest.cons (Tree.node 42 (@Forest.nil Nat)) (@Forest.nil Nat))"
        ),
        "42",
    );
    run(&format!("{TREE}{HEAD}#eval first (@Forest.nil Nat)"), "0");
}
#[test]
fn nested_matches_and_distinct_ground_instantiations_keep_layouts() {
    run(
        &format!(
            "{TREE}def next (t : Tree Nat) : Nat := match t with | .node n xs => match xs with | .nil => n | .cons t rest => match t with | .node k children => k\n#eval next (Tree.node 1 (Forest.cons (Tree.node 42 (@Forest.nil Nat)) (@Forest.nil Nat)))"
        ),
        "42",
    );
    run(
        &format!(
            "{TREE}{HEAD}def text (t : Tree String) : String := match t with | .node s children => s\n#eval value (Tree.node 37 (@Forest.nil Nat)) + String.length (text (Tree.node \"hello\" (@Forest.nil String)))"
        ),
        "42",
    );
}
#[test]
fn mutual_fields_and_returned_closures_keep_their_interfaces() {
    run(
        &format!(
            "{TREE}def apply (t : Tree (Nat -> Nat)) : Nat := match t with | .node f children => f 40\n#eval apply (Tree.node (Nat.add 2) (@Forest.nil (Nat -> Nat)))"
        ),
        "42",
    );
    run(
        &format!(
            "{TREE}def action (t : Tree Nat) : Nat -> Nat := match t with | .node n children => fun k => n + k\n#eval action (Tree.node 40 (@Forest.nil Nat)) 2"
        ),
        "42",
    );
}
#[test]
fn unselected_cases_are_lazy_and_constructor_fields_remain_strict() {
    let prefix = format!(
        "{TREE}def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\ndef inspect (xs : Forest Nat) : Nat := match xs with | .nil => 42 | .cons t rest => work 60\n"
    );
    let idle = run(&format!("{prefix}#eval inspect (@Forest.nil Nat)"), "42");
    let busy = run(
        &format!(
            "{prefix}#eval inspect (Forest.cons (Tree.node 0 (@Forest.nil Nat)) (@Forest.nil Nat))"
        ),
        "60",
    );
    assert!(busy > idle + 60);
    let idle = run(
        &format!(
            "{TREE}{HEAD}def ignore (t : Tree Nat) : Nat := 42\n#eval ignore (Tree.node 0 (@Forest.nil Nat))"
        ),
        "42",
    );
    let busy = run(
        &format!(
            "{prefix}def ignore (t : Tree Nat) : Nat := 42\n#eval ignore (Tree.node (work 60) (@Forest.nil Nat))"
        ),
        "42",
    );
    assert!(busy > idle + 60, "unused constructor field was erased");
}
#[test]
fn stopped_mutual_layouts_do_not_publish_and_retries_are_identical() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!(
        "{TREE}{HEAD}#eval first (Forest.cons (Tree.node 42 (@Forest.nil Nat)) (@Forest.nil Nat))"
    );
    let mut small = limits();
    small.ingress.fir.max_constructors = 2;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, small)
            .is_err()
    );
    let mut small = limits();
    small.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, small)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
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
    assert_eq!(
        one.engine.logical_root(&options),
        two.engine.logical_root(&options)
    );
}
#[test]
fn unsupported_sibling_layouts_and_false_source_never_gain_runtime_authority() {
    {
        let source = "mutual\ninductive A where | mk (f : Nat -> B)\ninductive B where | nil | cons (a : A)\nend\ndef ignore (b : B) : Nat := 42\n#eval ignore B.nil";
        let base = engine();
        let root = base.logical_root(&KVMap::new());
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(root, base.logical_root(&KVMap::new()));
    }
    assert!(
        engine()
            .execute_source_definitions(
                &[format!("{TREE}theorem falsehood : 0 = 1 := by rfl").as_bytes()],
                &KVMap::new(),
                limits()
            )
            .is_err()
    );
}
