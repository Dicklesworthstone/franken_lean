//! Checked mutual recursors execute through native peer-closure groups.
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

const DATA: &str = "mutual\ninductive Tree where | leaf (n : Nat) | node (xs : Forest)\ninductive Forest where | nil | cons (t : Tree) (xs : Forest)\nend\n";
const MOTIVES: &str = "(fun (t : Tree) => Nat) (fun (xs : Forest) => Nat)";
const SUM: &str = "(fun (n : Nat) => n) (fun (xs : Forest) (ih : Nat) => ih) 0 (fun (t : Tree) (xs : Forest) (ihT : Nat) (ihF : Nat) => ihT + ihF)";
const VALUE: &str = "Forest.cons (Tree.leaf 40) (Forest.cons (Tree.node (Forest.cons (Tree.leaf 2) Forest.nil)) Forest.nil)";

#[test]
fn mutual_folds_execute_from_each_member_with_family_local_tags() {
    for (member, type_, value) in [
        ("Tree", "Tree", format!("Tree.node ({VALUE})")),
        ("Forest", "Forest", VALUE.to_string()),
    ] {
        run(
            &format!(
                "{DATA}def total (v : {type_}) : Nat := @{member}.rec {MOTIVES} {SUM} v\n#eval total ({value})"
            ),
            "42",
        );
    }
}

#[test]
fn mutual_folds_capture_outer_values_used_only_by_a_sibling() {
    let minors = "(fun (n : Nat) => n + offset) (fun (xs : Forest) (ih : Nat) => ih) 0 (fun (t : Tree) (xs : Forest) (ihT : Nat) (ihF : Nat) => ihT + ihF)";
    run(
        &format!(
            "{DATA}def total (offset : Nat) (xs : Forest) : Nat := @Forest.rec {MOTIVES} {minors} xs\n#eval total 2 (Forest.cons (Tree.leaf 40) Forest.nil)"
        ),
        "42",
    );
}

#[test]
fn nested_group_dependencies_are_discovered_to_a_fixed_point() {
    let helper = format!("def sum (t : Tree) : Nat := @Tree.rec {MOTIVES} {SUM} t\n");
    let minors = "(fun (n : Nat) => sum (Tree.leaf n)) (fun (xs : Forest) (ih : Nat) => ih) 0 (fun (t : Tree) (xs : Forest) (ihT : Nat) (ihF : Nat) => ihT + ihF)";
    run(
        &format!(
            "{DATA}{helper}def nested (xs : Forest) : Nat := @Forest.rec {MOTIVES} {minors} xs\n#eval nested ({VALUE})"
        ),
        "42",
    );
    // The same code at two different captured values must not share state.
    let minors = "(fun (n : Nat) => n + offset) (fun (xs : Forest) (ih : Nat) => ih) 0 (fun (t : Tree) (xs : Forest) (ihT : Nat) (ihF : Nat) => ihT + ihF)";
    run(
        &format!(
            "{DATA}def shifted (offset : Nat) (t : Tree) : Nat := @Tree.rec {MOTIVES} {minors} t\n#eval shifted 1 (Tree.leaf 19) + shifted 2 (Tree.leaf 20)"
        ),
        "42",
    );
}

#[test]
fn ground_parameters_and_three_member_peer_indices_are_not_special_cases() {
    let data = "mutual\ninductive Tree (A : Type u) where | node (n : A) (xs : Forest A)\ninductive Forest (B : Type u) where | nil | cons (t : Tree B) (xs : Forest B)\nend\n";
    let motives = "(fun (t : Tree Nat) => Nat) (fun (xs : Forest Nat) => Nat)";
    let minors = "(fun (n : Nat) (xs : Forest Nat) (ih : Nat) => n + ih) 0 (fun (t : Tree Nat) (xs : Forest Nat) (ihT : Nat) (ihF : Nat) => ihT + ihF)";
    run(
        &format!(
            "{data}def total (xs : Forest Nat) : Nat := @Forest.rec Nat {motives} {minors} xs\n#eval total (Forest.cons (Tree.node 40 (@Forest.nil Nat)) (Forest.cons (Tree.node 2 (@Forest.nil Nat)) (@Forest.nil Nat)))"
        ),
        "42",
    );
    let data = "mutual\ninductive A where | base (n : Nat) | step (b : B)\ninductive B where | step (c : C)\ninductive C where | step (a : A)\nend\n";
    let motives = "(fun (a : A) => Nat) (fun (b : B) => Nat) (fun (c : C) => Nat)";
    let minors = "(fun (n : Nat) => n) (fun (b : B) (ih : Nat) => ih) (fun (c : C) (ih : Nat) => ih) (fun (a : A) (ih : Nat) => ih)";
    run(
        &format!(
            "{data}def total (a : A) : Nat := @A.rec {motives} {minors} a\n#eval total (A.step (B.step (C.step (A.base 42))))"
        ),
        "42",
    );
}

#[test]
fn heterogeneous_motives_collect_transitive_dependencies_of_hidden_peers() {
    let helper = "def text (n : Nat) : String := match n with | .zero => \"\" | .succ k => \"x\" ++ text k\n";
    let motives = "(fun (t : Tree) => String) (fun (xs : Forest) => Nat)";
    let minors = "(fun (n : Nat) => text n) (fun (xs : Forest) (ih : Nat) => text ih) 0 (fun (t : Tree) (xs : Forest) (ihT : String) (ihF : Nat) => String.length ihT + ihF)";
    run(
        &format!(
            "{DATA}{helper}def total (xs : Forest) : Nat := @Forest.rec {motives} {minors} xs\n#eval total ({VALUE})"
        ),
        "42",
    );
}

#[test]
fn different_peer_arities_and_partial_accumulator_closures_preserve_scope() {
    let motives = "(fun (t : Tree) => Nat -> Nat) (fun (xs : Forest) => Nat)";
    let minors = "(fun (n : Nat) => fun (acc : Nat) => n + acc) (fun (xs : Forest) (ih : Nat) => fun (acc : Nat) => ih + acc) 0 (fun (t : Tree) (xs : Forest) (ihT : Nat -> Nat) (ihF : Nat) => ihT ihF)";
    run(
        &format!(
            "{DATA}def total (t : Tree) (acc : Nat) : Nat := @Tree.rec {motives} {minors} t acc\n#eval total (Tree.node (Forest.cons (Tree.leaf 40) Forest.nil)) 2"
        ),
        "42",
    );
    run(
        &format!(
            "{DATA}def partial (t : Tree) : Nat -> Nat := @Tree.rec {motives} {minors} t\n#eval let f : Nat -> Nat := partial (Tree.node (Forest.cons (Tree.leaf 40) Forest.nil)); f 2"
        ),
        "42",
    );
}

#[test]
fn mutual_folds_return_owned_sibling_objects_for_later_matches() {
    let motives = "(fun (t : Tree) => Tree) (fun (xs : Forest) => Forest)";
    let minors = "(fun (n : Nat) => Tree.leaf (n + 1)) (fun (xs : Forest) (ih : Forest) => Tree.node ih) Forest.nil (fun (t : Tree) (xs : Forest) (ihT : Tree) (ihF : Forest) => Forest.cons ihT ihF)";
    let inspect = "def first (xs : Forest) : Nat := match xs with | .nil => 0 | .cons t rest => match t with | .leaf n => n | .node xs => 0\n";
    run(
        &format!(
            "{DATA}{inspect}def copy (xs : Forest) : Forest := @Forest.rec {motives} {minors} xs\n#eval first (copy (Forest.cons (Tree.leaf 41) Forest.nil))"
        ),
        "42",
    );
}

#[test]
fn repeated_hypotheses_share_work_and_ignored_siblings_are_not_forced() {
    let make = "def build (n : Nat) : Tree := match n with | .zero => Tree.leaf 1 | .succ k => let child : Tree := build k; Tree.node (Forest.cons child (Forest.cons child Forest.nil))\n";
    let minors = "(fun (n : Nat) => n) (fun (xs : Forest) (ih : Nat) => ih) 0 (fun (t : Tree) (xs : Forest) (ihT : Nat) (ihF : Nat) => ihT + ihT)";
    let source = format!(
        "{DATA}{make}def double (t : Tree) : Nat := @Tree.rec {MOTIVES} {minors} t\n#eval double (build 28)"
    );
    let steps = run(&source, "268435456");
    assert!(
        steps < 10_000,
        "repeated IH expanded exponentially: {steps}"
    );
    let work = "def work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\n";
    let minors = "(fun (n : Nat) => n) (fun (xs : Forest) (ih : Nat) => ih) (work 2000) (fun (t : Tree) (xs : Forest) (ihT : Nat) (ihF : Nat) => ihT)";
    let source = format!(
        "{DATA}{work}def first (t : Tree) : Nat := @Tree.rec {MOTIVES} {minors} t\n#eval first (Tree.node (Forest.cons (Tree.leaf 42) Forest.nil))"
    );
    let steps = run(&source, "42");
    assert!(steps < 500, "ignored sibling was forced: {steps}");
}

#[test]
fn mutual_closure_resource_stops_publish_nothing_and_recover_deterministically() {
    let source = format!(
        "{DATA}def total (xs : Forest) : Nat := @Forest.rec {MOTIVES} {SUM} xs\n#eval total ({VALUE})"
    );
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for small in [
        {
            let mut small = limits();
            small.vm.max_steps = 3;
            small
        },
        {
            let mut small = limits();
            small.vm.max_stack_depth = 2;
            small
        },
    ] {
        assert!(matches!(
            base.execute_source_definitions(&[source.as_bytes()], &options, small)
                .unwrap(),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(root, base.logical_root(&options));
    }
    let mut small = limits();
    small.ingress.max_lambda_bindings = 2;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, small)
            .is_err()
    );
    assert_eq!(root, base.logical_root(&options));
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
        one.engine.logical_root(&options),
        two.engine.logical_root(&options)
    );
    assert_eq!(
        one.executions.last().unwrap().flbc_artifact,
        two.executions.last().unwrap().flbc_artifact
    );
}
