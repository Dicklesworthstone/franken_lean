//! Mutual recursive callbacks retain each peer's checked argument and index scope.
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

const DATA: &str = "mutual\ninductive Tree : Nat -> Type where | leaf (n : Nat) (value : Nat) : Tree n | node (offset : Nat) (child : (i : Nat) -> Forest (offset + i)) : Tree offset\ninductive Forest : Nat -> Type where | leaf (n : Nat) (value : Nat) : Forest n | node (offset : Nat) (child : (i : Nat) -> Tree (offset + i)) : Forest offset\nend\n";
const MOTIVES: &str = "(fun (n : Nat) (t : Tree n) => Nat) (fun (n : Nat) (f : Forest n) => Nat)";
const MINORS: &str = "(fun (n : Nat) (value : Nat) => value) (fun (offset : Nat) (child : (i : Nat) -> Forest (offset + i)) (ih : Nat -> Nat) => ih 20) (fun (n : Nat) (value : Nat) => value) (fun (offset : Nat) (child : (i : Nat) -> Tree (offset + i)) (ih : Nat -> Nat) => ih 22)";

#[test]
fn mutual_indexed_callbacks_follow_actual_child_indices() {
    run(
        &format!(
            "{DATA}def total (n : Nat) (t : Tree n) : Nat := @Tree.rec {MOTIVES} {MINORS} n t\n#eval total 0 (Tree.node 0 (fun i => Forest.node (0 + i) (fun j => Tree.leaf ((0 + i) + j) (i + j))))"
        ),
        "42",
    );
}

#[test]
fn mutual_callback_case_splits_do_not_request_induction_hypotheses() {
    run(
        &format!(
            "{DATA}def first (n : Nat) (t : Tree n) : Nat := match t with | .leaf k value => value | .node offset child => match child 20 with | .leaf k value => value | .node k next => 0\n#eval first 0 (Tree.node 0 (fun i => Forest.leaf (0 + i) (i + 22)))"
        ),
        "42",
    );
}

#[test]
fn unindexed_and_three_member_callbacks_use_their_own_peer() {
    let data = "mutual\ninductive A where | leaf (value : Nat) | node (child : Nat -> B true)\ninductive B : Bool -> Type where | node (child : String -> C) : B true\ninductive C where | node (child : Nat -> A)\nend\n";
    // A's callback result fixes B's index, whereas B and C have unindexed
    // callback results. Peer positions cannot be inferred from field arity.
    let motives = "(fun (a : A) => Nat) (fun (b : Bool) (v : B b) => Nat) (fun (v : C) => Nat)";
    let minors = "(fun (value : Nat) => value) (fun (child : Nat -> B true) (ih : Nat -> Nat) => ih 20) (fun (child : String -> C) (ih : String -> Nat) => ih \"ok\") (fun (child : Nat -> A) (ih : Nat -> Nat) => ih 20)";
    run(
        &format!(
            "{data}def total (a : A) : Nat := @A.rec {motives} {minors} a\n#eval total (A.node (fun n => B.node (fun s => C.node (fun k => A.leaf (n + String.length s + k)))))"
        ),
        "42",
    );
}

#[test]
fn sibling_callback_domains_indices_and_accumulators_can_differ() {
    let data = r#"mutual
inductive Tree : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Tree n
  | node (prefix : String) (child : (b : Bool) -> (s : String) -> Forest b (prefix ++ s)) : Tree 0
inductive Forest : Bool -> String -> Type where
  | leaf (b : Bool) (s : String) (value : Nat) : Forest b s
  | node (b : Bool) (s : String) (offset : Nat) (child : (n : Nat) -> Tree (offset + n)) : Forest b s
end
"#;
    let motives = "(fun (n : Nat) (t : Tree n) => Nat -> Nat) (fun (b : Bool) (s : String) (f : Forest b s) => Nat -> Nat -> Nat)";
    let minors = "(fun n value acc => value + acc + captured) (fun prefix child ih acc => ih true \"k\" acc 3) (fun b s value acc extra => value + acc + extra) (fun b s offset child ih acc extra => ih 20 (acc + extra + String.length s))";
    let value = "Tree.node \"ok\" (fun b s => Forest.node b (\"ok\" ++ s) 10 (fun n => Tree.leaf (10 + n) n))";
    run(
        &format!(
            "{data}def total (captured : Nat) (n : Nat) (t : Tree n) : Nat -> Nat := @Tree.rec {motives} {minors} n t\n#eval let f : Nat -> Nat := total 10 0 ({value}); f 6"
        ),
        "42",
    );
}

#[test]
fn proof_bearing_callback_arguments_use_checked_inert_slots() {
    run(
        r#"mutual
inductive Tree : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Tree n
  | node (child : (n : Nat) -> n = n -> Forest n) : Tree 0
inductive Forest : Nat -> Type where
  | node (n : Nat) (child : Tree n) : Forest n
end
def total (n : Nat) (t : Tree n) : Nat :=
  @Tree.rec (fun n t => Nat) (fun n f => Nat)
    (fun n value => value) (fun child ih => ih 40 (Eq.refl 40))
    (fun n child ih => ih) n t
#eval total 0 (Tree.node (fun n h => Forest.node n (Tree.leaf n (n + 2))))"#,
        "42",
    );
}

#[test]
fn mapped_mutual_callback_objects_escape_with_live_captures() {
    run(
        include_str!("../../../examples/native_mutual_function_children.lean"),
        "42",
    );
}

#[test]
fn both_unindexed_peers_and_heterogeneous_payload_specializations_execute() {
    run(
        r#"mutual
inductive Tree (A : Type u) where
  | leaf (value : A)
  | node (child : Nat -> Forest A)
inductive Forest (A : Type u) where
  | node (child : Nat -> Tree A)
end
def first {A : Type u} (t : Tree A) : A :=
  @Tree.rec A (fun t => A) (fun f => A)
    (fun value => value) (fun child ih => ih 20) (fun child ih => ih 22) t
#eval first (Tree.node (fun i => Forest.node (fun j => Tree.leaf (i + j - 5)))) + String.length (first (Tree.node (fun i => Forest.node (fun j => Tree.leaf "hello"))))"#,
        "42",
    );
}

#[test]
fn selecting_a_callback_from_an_impossible_indexed_arm_is_checked() {
    run(
        r#"mutual
inductive Tree : Nat -> Type where
  | leaf (value : Nat) : Tree 0
  | node (n : Nat) (child : Nat -> Forest n) : Tree (Nat.succ n)
inductive Forest : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Forest n
  | node (n : Nat) (tree : Tree n) : Forest n
end
def select (n : Nat) (t : Tree (Nat.succ n)) : Nat -> Forest n :=
  fun i => match t with | .node k child => child i
def read (n : Nat) (f : Forest n) : Nat := match f with
  | .leaf k value => value
  | .node k t => 0
#eval read 0 ((select 0 (Tree.node 0 (fun i => Forest.leaf 0 (i + 2)))) 40)"#,
        "42",
    );
}

#[test]
fn child_index_computations_are_deferred_and_execute_once_per_call() {
    let data = r#"def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1
mutual
inductive Tree : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Tree n
  | node (child : (i : Nat) -> Forest (work i)) : Tree 0
inductive Forest : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Forest n
  | node (n : Nat) (child : Tree n) : Forest n
end
"#;
    let make = "Tree.node (fun i => Forest.leaf (work i) 42)";
    let mut growth = Vec::new();
    for body in ["42", "ih count", "ih count + ih count - 42"] {
        let defs = format!(
            "{data}def total (count : Nat) (n : Nat) (t : Tree n) : Nat := @Tree.rec {MOTIVES} (fun n value => value) (fun child ih => {body}) (fun n value => value) (fun n child ih => ih) n t\n"
        );
        let low = run(&format!("{defs}#eval total 0 0 ({make})"), "42");
        let high = run(&format!("{defs}#eval total 60 0 ({make})"), "42");
        growth.push(high - low);
    }
    let low = run(&format!("{data}#eval let x : Nat := work 0; 42"), "42");
    let high = run(&format!("{data}#eval let x : Nat := work 60; 42"), "42");
    assert!(high > low);
    // Constructing a closure does not select a child. Each IH invocation
    // computes both the peer-call index and the constructor's index, exactly
    // once. Repeated applications are not memoized or substituted away.
    assert_eq!(growth, [0, 2 * (high - low), 4 * (high - low)]);
}

#[test]
fn invalid_callback_indices_and_negative_occurrences_never_publish() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for bad in [
        "def bad : Tree 0 := Tree.node 0 (fun i => Forest.leaf 0 i)",
        "def bad (n : Nat) (t : Tree n) : Nat := match t with | .leaf k value => value",
        "def bad : 0 = 1 := by rfl",
        "mutual\ninductive Bad where | mk (f : Worse -> Nat)\ninductive Worse where | mk (b : Bad)\nend",
    ] {
        assert!(
            !matches!(
                base.execute_source_definitions(
                    &[format!("{DATA}#eval 42\n{bad}").as_bytes()],
                    &options,
                    limits()
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{bad}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn resource_stops_recover_identical_artifacts_and_logical_roots() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let defs = include_str!("../../../examples/native_mutual_function_children.lean");
    let (defs, expr) = defs.split_once("#eval").unwrap();
    let source = format!("{defs}def answer : Nat := {expr}");
    let checked = base
        .check_source_files(
            &[source.as_bytes()],
            &options,
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for bounded in [
        {
            let mut x = limits();
            x.ingress.max_nodes = 10;
            x
        },
        {
            let mut x = limits();
            x.ingress.fir.max_constructors = 1;
            x
        },
        {
            let mut x = limits();
            x.ingress.fir.max_closure_types = 0;
            x
        },
        {
            let mut x = limits();
            x.ingress.max_lambda_bindings = 1;
            x
        },
        {
            let mut x = limits();
            x.vm.max_steps = 1;
            x
        },
        {
            let mut x = limits();
            x.vm.max_stack_depth = 1;
            x
        },
    ] {
        assert!(!matches!(
            base.execute_source_definitions(&[source.as_bytes()], &options, bounded),
            Ok(fln::Outcome::Complete(_))
        ));
        assert_eq!(base.logical_root(&options), root);
    }
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
    assert_eq!(
        first.engine.logical_root(&options),
        checked.engine.logical_root(&options)
    );
    assert_eq!(
        first.engine.logical_root(&options),
        second.engine.logical_root(&options)
    );
    assert_eq!(base.logical_root(&options), root);
}
