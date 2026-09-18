//! Lists and trees execute through admitted recursors and native self closures.
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
fn run(source: &str, expected: &str) {
    let batch = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
        panic!("VM return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}
const CHAIN: &str = "inductive Chain where\n | nil\n | cons (head : Nat) (tail : Chain)\n";
const MAKE: &str = "def make (n : Nat) : Chain := match n with | .zero => Chain.nil | .succ k => Chain.cons n (make k)\n";
const TREE: &str = "inductive Tree where\n | leaf (value : Nat)\n | node (left right : Tree)\n";
#[test]
fn list_construction_and_structural_folds_are_native() {
    run(
        &format!(
            "{CHAIN}{MAKE}def length (xs : Chain) : Nat := match xs with | .nil => 0 | .cons head tail => length tail + 1\n#eval length (make 42)"
        ),
        "42",
    );
    run(
        &format!(
            "{CHAIN}{MAKE}def sum (xs : Chain) : Nat := match xs with | .nil => 0 | .cons head tail => head + sum tail\n#eval sum (make 9)"
        ),
        "45",
    );
}
#[test]
fn trees_supply_independent_hypotheses_for_every_recursive_field() {
    run(
        &format!(
            "{TREE}def sum (tree : Tree) : Nat := match tree with | .leaf n => n | .node left right => sum left + sum right\n#eval sum (Tree.node (Tree.leaf 17) (Tree.node (Tree.leaf 20) (Tree.leaf 5)))"
        ),
        "42",
    );
}
#[test]
fn list_copy_reuses_the_constructor_layout_and_returns_owned_objects() {
    run(
        &format!(
            "{CHAIN}{MAKE}def copy (xs : Chain) : Chain := match xs with | .nil => Chain.nil | .cons head tail => Chain.cons (head + 1) (copy tail)\ndef first (xs : Chain) : Nat := match xs with | .nil => 0 | .cons head tail => head\n#eval first (copy (make 41))"
        ),
        "42",
    );
}
#[test]
fn changing_accumulators_and_partial_recursive_calls_keep_lexical_scope() {
    run(
        &format!(
            "{CHAIN}{MAKE}def sum (xs : Chain) (acc : Nat) : Nat := match xs with | .nil => acc | .cons head tail => let next : Nat -> Nat := sum tail; next (head + acc)\n#eval sum (make 8) 6"
        ),
        "42",
    );
}
#[test]
fn fixed_outer_values_and_nested_local_closures_are_captured() {
    run(
        &format!(
            "{CHAIN}{MAKE}def fold (delta : Nat) (xs : Chain) : Nat := match xs with | .nil => 0 | .cons head tail => let bump (x : Nat) : Nat := x + delta; bump (fold delta tail)\n#eval fold 7 (make 6)"
        ),
        "42",
    );
}
#[test]
fn recursive_payloads_and_results_preserve_owned_strings() {
    run(
        "inductive Texts where\n | nil\n | cons (head : String) (tail : Texts)\ndef join (xs : Texts) : String := match xs with | .nil => \"\" | .cons head tail => head ++ join tail\n#eval String.length (join (Texts.cons \"hello\" (Texts.cons \"world\" Texts.nil)))",
        "10",
    );
}
#[test]
fn recursive_results_can_be_records_and_record_accumulators() {
    run(
        &format!(
            "{CHAIN}{MAKE}structure Total where\n  count : Nat\n  label : String\ndef fold (xs : Chain) (acc : Total) : Total := match xs with | .nil => acc | .cons head tail => fold tail {{ acc with count := acc.count + head }}\n#eval (fold (make 8) {{ count := 6, label := \"sum\" }}).count"
        ),
        "42",
    );
}
#[test]
fn ignored_recursive_subtrees_are_not_forced() {
    run(
        &format!(
            "{TREE}def first (tree : Tree) : Nat := match tree with | .leaf n => n | .node left right => first left\n#eval first (Tree.node (Tree.leaf 42) (Tree.node (Tree.leaf 0) (Tree.leaf 7)))"
        ),
        "42",
    );
}
#[test]
fn undecreasing_recursion_and_invalid_unused_branches_are_refused_atomically() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for bad in [
        "def bad (xs : Chain) : Nat := match xs with | .nil => 0 | .cons head tail => bad xs",
        "def bad (xs : Chain) : Nat := match xs with | .nil => 0 | .cons head tail => let unused : Bool := head; bad tail",
    ] {
        let source = format!("{CHAIN}#eval 42\n{bad}");
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &options, limits())
                .is_err()
        );
        assert_eq!(base.logical_root(&options), root);
    }
}
#[test]
fn exhaustion_is_a_nonanswer_and_does_not_publish_a_successor() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!(
        "{CHAIN}{MAKE}def length (xs : Chain) : Nat := match xs with | .nil => 0 | .cons head tail => length tail + 1\n#eval length (make 100)"
    );
    for small in [
        {
            let mut x = limits();
            x.vm.max_steps = 20;
            x
        },
        {
            let mut x = limits();
            x.vm.max_stack_depth = 5;
            x
        },
    ] {
        assert!(matches!(
            base.execute_source_definitions(&[source.as_bytes()], &options, small)
                .unwrap(),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(base.logical_root(&options), root);
    }
    run(&source, "100");
}

#[test]
fn repeated_hypotheses_share_work_and_ignored_tree_children_remain_lazy() {
    let double = format!(
        "{CHAIN}{MAKE}def double (xs : Chain) : Nat := match xs with | .nil => 1 | .cons head tail => double tail + double tail\n#eval double (make 35)"
    );
    let left = format!(
        "{TREE}def full (n : Nat) : Tree := match n with | .zero => Tree.leaf 42 | .succ k => let child : Tree := full k; Tree.node child child\ndef leftmost (tree : Tree) : Nat := match tree with | .leaf n => n | .node left right => leftmost left\n#eval leftmost (full 60)"
    );
    for (source, expected) in [(double, "34359738368"), (left, "42")] {
        let mut bounded = limits();
        bounded.vm.max_steps = 30000;
        bounded.vm.max_stack_depth = 600;
        let batch = engine()
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), bounded)
            .unwrap()
            .into_complete()
            .expect("linear sharing must stay within the instruction budget");
        let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
            panic!("VM return");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}
#[test]
fn recursion_rebinds_the_current_root_instead_of_capturing_the_original_one() {
    run(
        &format!(
            "{CHAIN}{MAKE}def first (xs : Chain) : Nat := match xs with | .nil => 0 | .cons head tail => head\ndef fold (xs : Chain) : Nat := match xs with | .nil => 0 | .cons head tail => first xs + fold tail\n#eval fold (make 9)"
        ),
        "45",
    );
}
