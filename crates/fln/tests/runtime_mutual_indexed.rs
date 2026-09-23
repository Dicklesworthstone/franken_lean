//! Mutually indexed families retain logical indices and use uniform native layouts.
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
        panic!("VM return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}
const DATA: &str = "mutual\ninductive Tree : Nat -> Type where | leaf (n : Nat) (x : Nat) : Tree n | node (n : Nat) (xs : Forest n) : Tree n\ninductive Forest : Nat -> Type where | nil (n : Nat) : Forest n | cons (n : Nat) (t : Tree n) (xs : Forest n) : Forest n\nend\n";
const MOTIVES: &str = "(fun (n : Nat) (t : Tree n) => Nat) (fun (n : Nat) (xs : Forest n) => Nat)";
const SUM: &str = "(fun (n : Nat) (x : Nat) => x) (fun (n : Nat) (xs : Forest n) (ih : Nat) => ih) (fun (n : Nat) => 0) (fun (n : Nat) (t : Tree n) (xs : Forest n) (ihT : Nat) (ihF : Nat) => ihT + ihF)";
const VALUE: &str = "Forest.cons 7 (Tree.leaf 7 40) (Forest.cons 7 (Tree.node 7 (Forest.cons 7 (Tree.leaf 7 2) (Forest.nil 7))) (Forest.nil 7))";
#[test]
fn indexed_mutual_values_are_constructed_and_matched() {
    run(
        &format!(
            "{DATA}def first (n : Nat) (xs : Forest n) : Nat := match xs with | .nil k => 0 | .cons k t rest => match t with | .leaf j x => x | .node j ys => 0\n#eval first 7 (Forest.cons 7 (Tree.leaf 7 42) (Forest.nil 7))"
        ),
        "42",
    );
}
#[test]
fn indexed_mutual_folds_execute_from_either_member() {
    run(
        &format!(
            "{DATA}def total (n : Nat) (xs : Forest n) : Nat := @Forest.rec {MOTIVES} {SUM} n xs\n#eval total 7 ({VALUE})"
        ),
        "42",
    );
    run(
        &format!(
            "{DATA}def total (n : Nat) (t : Tree n) : Nat := @Tree.rec {MOTIVES} {SUM} n t\n#eval total 7 (Tree.node 7 ({VALUE}))"
        ),
        "42",
    );
}

#[test]
fn sibling_index_domains_arities_and_result_interfaces_are_independent() {
    let data = r#"mutual
inductive Tree : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Tree n
  | node (b : Bool) (s : String) (xs : Forest b s) : Tree (String.length s)
inductive Forest : Bool -> String -> Type where
  | nil (b : Bool) (s : String) : Forest b s
  | cons (n : Nat) (b : Bool) (s : String) (t : Tree n) (xs : Forest b s) : Forest b s
end
"#;
    let text = "def text (n : Nat) : String := match n with | .zero => \"\" | .succ k => \"x\" ++ text k\n";
    let motives = "(fun (n : Nat) (t : Tree n) => Nat -> Nat) (fun (b : Bool) (s : String) (xs : Forest b s) => String)";
    let minors = "(fun (n : Nat) (value : Nat) (acc : Nat) => value + n + acc) (fun (b : Bool) (s : String) (xs : Forest b s) (ih : String) (acc : Nat) => String.length ih + acc) (fun (b : Bool) (s : String) => s) (fun (n : Nat) (b : Bool) (s : String) (t : Tree n) (xs : Forest b s) (ihT : Nat -> Nat) (ihF : String) => if b then text (ihT (String.length ihF)) else ihF)";
    let value = "Forest.cons 1 true \"root\" (Tree.leaf 1 36) (Forest.nil true \"root\")";
    run(
        &format!(
            "{data}{text}def total (n : Nat) (t : Tree n) : Nat -> Nat := @Tree.rec {motives} {minors} n t\n#eval let f : Nat -> Nat := total (String.length \"root\") (Tree.node true \"root\" ({value})); f 1"
        ),
        "42",
    );
    run(
        &format!(
            "{data}{text}def total (b : Bool) (s : String) (xs : Forest b s) : String := @Forest.rec {motives} {minors} b s xs\n#eval String.length (total true \"root\" ({value})) + 1"
        ),
        "42",
    );
}

#[test]
fn three_members_mix_indexed_and_unindexed_siblings() {
    let data = "mutual\ninductive A : Nat -> Type where | base (n : Nat) (value : Nat) : A n | step (b : Bool) (child : B b) : A 0\ninductive B : Bool -> Type where | step (child : C) : B true\ninductive C where | step (n : Nat) (child : A n)\nend\n";
    let motives = "(fun (n : Nat) (a : A n) => Nat) (fun (b : Bool) (child : B b) => Nat) (fun (c : C) => Nat)";
    let minors = "(fun (n : Nat) (value : Nat) => value) (fun (b : Bool) (child : B b) (ih : Nat) => ih) (fun (child : C) (ih : Nat) => ih) (fun (n : Nat) (child : A n) (ih : Nat) => ih)";
    for (member, params, args, value) in [
        (
            "A",
            "(n : Nat) (v : A n)",
            "n v",
            "0 (A.step true (B.step (C.step 7 (A.base 7 42))))",
        ),
        (
            "B",
            "(b : Bool) (v : B b)",
            "b v",
            "true (B.step (C.step 7 (A.base 7 42)))",
        ),
        (
            "C",
            "(v : C)",
            "v",
            "(C.step 0 (A.step true (B.step (C.step 7 (A.base 7 42)))))",
        ),
    ] {
        run(
            &format!(
                "{data}def total {params} : Nat := @{member}.rec {motives} {minors} {args}\n#eval total {value}"
            ),
            "42",
        );
    }
}

#[test]
fn ground_type_parameters_and_proof_fields_preserve_distinct_layouts() {
    run(
        r#"mutual
inductive Tree (A : Type u) : Nat -> Type u where
  | leaf (n : Nat) (value : A) (h : n = n) : Tree A n
  | node (n : Nat) (child : Forest A n) : Tree A n
inductive Forest (B : Type u) : Nat -> Type u where
  | nil (n : Nat) : Forest B n
  | cons (n : Nat) (t : Tree B n) (rest : Forest B n) : Forest B n
end
def first {A : Type u} (fallback : A) (n : Nat) (t : Tree A n) : A :=
  @Tree.rec A (fun n t => A) (fun n xs => A)
    (fun n value h => value) (fun n child ih => ih)
    (fun n => fallback) (fun n t rest ihT ihF => ihT) n t
#eval first 0 1 (Tree.node 1 (Forest.cons 1 (Tree.leaf 1 37 (Eq.refl 1)) (Forest.nil 1))) + String.length (first "" 2 (Tree.node 2 (Forest.cons 2 (Tree.leaf 2 "hello" (Eq.refl 2)) (Forest.nil 2))))"#,
        "42",
    );
}

#[test]
fn mutual_motives_return_owned_indexed_objects_that_escape_the_fold() {
    let motives =
        "(fun (n : Nat) (t : Tree n) => Tree n) (fun (n : Nat) (xs : Forest n) => Forest n)";
    let minors = "(fun (n : Nat) (x : Nat) => Tree.leaf n (x + delta)) (fun (n : Nat) (xs : Forest n) (ih : Forest n) => Tree.node n ih) (fun (n : Nat) => Forest.nil n) (fun (n : Nat) (t : Tree n) (xs : Forest n) (ihT : Tree n) (ihF : Forest n) => Forest.cons n ihT ihF)";
    run(
        &format!(
            "{DATA}def map (delta : Nat) (n : Nat) (xs : Forest n) : Forest n := @Forest.rec {motives} {minors} n xs\ndef sum (n : Nat) (xs : Forest n) : Nat := @Forest.rec {MOTIVES} {SUM} n xs\n#eval sum 7 (map 1 7 (Forest.cons 7 (Tree.node 7 (Forest.cons 7 (Tree.leaf 7 39) (Forest.nil 7))) (Forest.cons 7 (Tree.leaf 7 1) (Forest.nil 7))))"
        ),
        "42",
    );
}

#[test]
fn repeated_mutual_hypotheses_are_shared_and_unused_peers_stay_lazy() {
    let build = "def build (depth : Nat) : Tree 7 := match depth with | .zero => Tree.leaf 7 1 | .succ k => let child : Tree 7 := build k; Tree.node 7 (Forest.cons 7 child (Forest.cons 7 child (Forest.nil 7)))\n";
    let minors = "(fun (n : Nat) (x : Nat) => x) (fun (n : Nat) (xs : Forest n) (ih : Nat) => ih) (fun (n : Nat) => 0) (fun (n : Nat) (t : Tree n) (xs : Forest n) (ihT : Nat) (ihF : Nat) => ihT + ihT)";
    let steps = run(
        &format!(
            "{DATA}{build}def double (n : Nat) (t : Tree n) : Nat := @Tree.rec {MOTIVES} {minors} n t\n#eval double 7 (build 24)"
        ),
        "16777216",
    );
    assert!(steps < 10_000, "repeated IH expanded: {steps}");
    let work = "def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\n";
    let minors = "(fun (n : Nat) (x : Nat) => x) (fun (n : Nat) (xs : Forest n) (ih : Nat) => ih) (fun (n : Nat) => work 2000) (fun (n : Nat) (t : Tree n) (xs : Forest n) (ihT : Nat) (ihF : Nat) => ihT)";
    let steps = run(
        &format!(
            "{DATA}{work}def first (n : Nat) (t : Tree n) : Nat := @Tree.rec {MOTIVES} {minors} n t\n#eval first 7 (Tree.node 7 (Forest.cons 7 (Tree.leaf 7 42) (Forest.nil 7)))"
        ),
        "42",
    );
    assert!(steps < 700, "unused sibling forced: {steps}");
}

#[test]
fn actual_peer_indices_are_evaluated_once_and_only_when_hypotheses_are_used() {
    let source = r#"def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1
mutual
inductive Tree : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Tree n
  | node (n : Nat) (child : Forest (work n)) : Tree n
inductive Forest : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Forest n
  | node (n : Nat) (child : Tree (work n)) : Forest n
end
"#;
    let motives = "(fun (n : Nat) (t : Tree n) => Nat) (fun (n : Nat) (xs : Forest n) => Nat)";
    let minors = "(fun (n : Nat) (value : Nat) => value) (fun (n : Nat) (child : Forest (work n)) (ih : Nat) => ih) (fun (n : Nat) (value : Nat) => value) (fun (n : Nat) (child : Tree (work n)) (ih : Nat) => ih)";
    let defs = format!(
        "{source}def total (n : Nat) (t : Tree n) : Nat := @Tree.rec {motives} {minors} n t\ndef ignore (n : Nat) (t : Tree n) : Nat := match t with | .leaf k value => value | .node k child => 42\n"
    );
    let mut used = Vec::new();
    let mut ignored = Vec::new();
    for n in [0, 60] {
        let value = format!("Tree.node {n} (Forest.leaf (work {n}) 42)");
        used.push(run(&format!("{defs}#eval total {n} ({value})"), "42"));
        ignored.push(run(&format!("{defs}#eval ignore {n} ({value})"), "42"));
    }
    // Constructor evaluation computes its index once in either program.
    // Only the used hypothesis also computes the recovered peer-call index.
    // Fixed dispatch costs cancel, detecting dropped or duplicated work.
    assert!(ignored[1] > ignored[0]);
    assert_eq!(used[1] - used[0], 2 * (ignored[1] - ignored[0]));
}

#[test]
fn case_indices_remain_strict_without_any_induction_hypotheses() {
    let work = "def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\n";
    let minors = "(fun (n : Nat) (x : Nat) => x) (fun (n : Nat) (xs : Forest n) (ih : Nat) => 42) (fun (n : Nat) => 42) (fun (n : Nat) (t : Tree n) (xs : Forest n) (ihT : Nat) (ihF : Nat) => 42)";
    let mut case = Vec::new();
    let mut direct = Vec::new();
    for n in [0, 60] {
        case.push(run(&format!("{DATA}{work}#eval @Tree.rec {MOTIVES} {minors} (work {n}) (Tree.leaf (work {n}) 42)"), "42"));
        direct.push(run(
            &format!("{work}#eval let index : Nat := work {n}; 42"),
            "42",
        ));
    }
    assert!(direct[1] > direct[0]);
    assert_eq!(case[1] - case[0], 2 * (direct[1] - direct[0]));
}

#[test]
fn invalid_indices_and_reachable_omissions_publish_nothing() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for bad in [
        "def bad : Tree 0 := Tree.leaf 1 42",
        "def bad : Tree 0 := Tree.node 0 (Forest.nil 1)",
        "def bad (n : Nat) (xs : Forest n) : Nat := match xs with | .nil k => 42",
        "def bad (n : Nat) (t : Tree n) : Nat := match t with | .leaf k value => value | .node k child => \"bad\"",
        "def bad : 0 = 1 := by rfl",
    ] {
        let source = format!("{DATA}#eval 42\n{bad}");
        assert!(
            !matches!(
                base.execute_source_definitions(&[source.as_bytes()], &options, limits()),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
        assert_eq!(root, base.logical_root(&options));
    }
}

#[test]
fn group_resource_stops_recover_identical_artifacts_and_logical_roots() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let defs = format!(
        "{DATA}def sum (n : Nat) (xs : Forest n) : Nat := @Forest.rec {MOTIVES} {SUM} n xs\n"
    );
    let source = format!("{defs}def result : Nat := sum 7 ({VALUE})");
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
        assert_eq!(root, base.logical_root(&options));
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
        second.engine.logical_root(&options)
    );
    let checked = base
        .check_source_files(
            &[source.as_bytes()],
            &options,
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        first.engine.logical_root(&options),
        checked.engine.logical_root(&options)
    );
    assert_eq!(root, base.logical_root(&options));
}

#[test]
fn changing_runtime_layouts_and_higher_order_mutual_fields_are_still_refused() {
    let base = engine();
    let options = KVMap::new();
    for source in [
        "mutual\ninductive A : Type -> Type 1 where | leaf (T : Type) (value : T) : A T | node (T : Type) (b : B T) : A T\ninductive B : Type -> Type 1 where | node (T : Type) (a : A T) : B T\nend\ndef read (x : A Nat) : Nat := match x with | .leaf T value => 42 | .node T b => 42\n#eval read (A.leaf Nat 42)",
        "mutual\ninductive A : Nat -> Type where | leaf (n : Nat) : A n | node (f : (n : Nat) -> B n) : A 0\ninductive B : Nat -> Type where | node (n : Nat) (a : A n) : B n\nend\ndef ignore (x : A 0) : Nat := 42\n#eval ignore (A.node (fun n => B.node n (A.leaf n)))",
    ] {
        // Refusal must be in preparation, not a vacuous parser/kernel failure.
        let checked = base.check_source_files(
            &[source.split("#eval").next().unwrap().as_bytes()],
            &options,
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        );
        checked.unwrap().into_complete().unwrap();
        assert!(
            !matches!(
                base.execute_source_definitions(&[source.as_bytes()], &options, limits()),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

#[test]
fn impossible_mutual_indexed_arms_use_checked_empty_elimination() {
    run(
        r#"mutual
inductive Tree : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Tree (Nat.succ n)
  | node (n : Nat) (xs : Forest n) : Tree (Nat.succ n)
inductive Forest : Nat -> Type where
  | nil : Forest 0
  | cons (n : Nat) (t : Tree (Nat.succ n)) (rest : Forest n) : Forest (Nat.succ n)
end
def first (n : Nat) (xs : Forest (Nat.succ n)) : Nat :=
  match xs with
  | .cons k t rest => match t with | .leaf j value => value | .node j children => 0
#eval first 0 (Forest.cons 0 (Tree.leaf 0 42) Forest.nil)"#,
        "42",
    );
}

#[test]
fn recursively_staged_nested_results_still_require_explicit_abi_adaptation() {
    let choose = "def choose (offset : Nat) (n : Nat) (xs : Forest n) : Nat -> Nat := match xs with | .nil k => fun x => offset + x | .cons k t rest => match t with | .leaf j value => fun x => value + offset + x | .node j children => fun x => offset + x\n";
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    base.check_source_files(
        &[format!("{DATA}{choose}").as_bytes()],
        &options,
        fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let source = format!(
        "{DATA}{choose}#eval let f : Nat -> Nat := choose 10 7 (Forest.cons 7 (Tree.leaf 7 30) (Forest.nil 7)); f 2"
    );
    let error = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap_err();
    assert!(
        matches!(error, fln::EngineExecutionError::BatchCommand { error, .. }
        if matches!(*error, fln::EngineExecutionError::Ingress(fln_comp::ingress::IngressError::LambdaResultType { .. })))
    );
    assert_eq!(base.logical_root(&options), root);
}
