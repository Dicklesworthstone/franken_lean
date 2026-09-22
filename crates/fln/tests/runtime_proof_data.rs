//! Proof-bearing objects retain logical field positions without executing evidence.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};
fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn run(source: &str, expected: &str) -> u64 {
    let batch = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
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
#[test]
fn dependent_record_proof_fields_keep_projection_positions() {
    run(
        "structure Certified where\n  value : Nat\n  proof : value = value\n  offset : Nat\ndef c : Certified := { value := 40, proof := by rfl, offset := 2 }\n#eval c.value + c.offset",
        "42",
    );
    run(
        "structure Certified where\n  before : 0 = 0\n  value : Nat\n  after : value = value\ndef c : Certified := { before := by rfl, value := 42, after := by rfl }\ndef use (n : Nat) (h : n = n) : Nat := n\n#eval use c.value c.after",
        "42",
    );
}
#[test]
fn proof_bearing_variants_and_recursive_cases_execute() {
    run(
        "inductive Ticket where\n| empty\n| paid (n : Nat) (h : n = n) (fee : Nat)\ndef total (t : Ticket) : Nat := match t with | .empty => 0 | .paid n h fee => n + fee\n#eval total (Ticket.paid 40 (by rfl) 2)",
        "42",
    );
    run(
        "inductive Chain where\n| nil\n| cons (n : Nat) (h : n = n) (tail : Chain)\ndef total (xs : Chain) : Nat := match xs with | .nil => 0 | .cons n h tail => n + total tail\n#eval total (Chain.cons 17 (by rfl) (Chain.cons 25 (by rfl) Chain.nil))",
        "42",
    );
}
#[test]
fn function_fields_and_defaults_accept_erased_evidence() {
    run(
        "structure Runner where\n  proof : 0 = 0 := by rfl\n  run : (n : Nat) -> n = n -> Nat\ndef r : Runner := { run := fun n h => n + 2 }\n#eval r.run 40 (by rfl)",
        "42",
    );
    run(
        "structure Certified where\n  value : Nat\n  proof : value = value := by rfl\ndef c : Certified := { value := 40 }\n#eval { c with value := 42, proof := by rfl }.value",
        "42",
    );
}
#[test]
fn mutual_sibling_proof_fields_and_recursive_hypotheses_keep_their_slots() {
    run(
        "mutual\ninductive A where | mk (b : B)\ninductive B where | nil | proof (p : 0 = 0)\nend\ndef ignore (b : B) : Nat := match b with | .nil => 0 | .proof p => 42\n#eval ignore (B.proof (by rfl))",
        "42",
    );
}
#[test]
fn whole_mutual_folds_erase_proof_fields_without_losing_recursive_results() {
    let data = "mutual\ninductive Tree where | leaf (n : Nat) (h : n = n) | node (xs : Forest) (h : 0 = 0)\ninductive Forest where | nil | cons (h : 0 = 0) (t : Tree) (xs : Forest)\nend\n";
    let motives = "(fun (t : Tree) => Nat) (fun (xs : Forest) => Nat)";
    let minors = "(fun (n : Nat) (h : n = n) => n) (fun (xs : Forest) (h : 0 = 0) (ih : Nat) => ih) 0 (fun (h : 0 = 0) (t : Tree) (xs : Forest) (ihT : Nat) (ihF : Nat) => ihT + ihF)";
    let value = "Tree.node (Forest.cons (by rfl) (Tree.leaf 40 (by rfl)) (Forest.cons (by rfl) (Tree.leaf 2 (by rfl)) Forest.nil)) (by rfl)";
    run(
        &format!(
            "{data}def total (t : Tree) : Nat := @Tree.rec {motives} {minors} t\n#eval total ({value})"
        ),
        "42",
    );
}
#[test]
fn nested_objects_and_proof_projections_use_original_lexical_types() {
    let data = "structure Certified where\n  value : Nat\n  proof : value = value\nstructure Box (A : Type) where\n  item : A\n";
    run(
        &format!(
            "{data}def use (n : Nat) (h : n = n) : Nat := n\ndef box : Box Certified := {{ item := {{ value := 42, proof := by rfl }} }}\n#eval use box.item.value box.item.proof"
        ),
        "42",
    );
    run(
        &format!(
            "{data}def use (c : Certified) : Nat := let proof := c.proof; let f (n : Nat) (h : n = n) := n; f c.value proof\n#eval use {{ value := 42, proof := by rfl }}"
        ),
        "42",
    );
}
#[test]
fn fields_before_and_after_a_proof_remain_strict_but_proof_receivers_are_erased() {
    let data = "structure Certified where\n  before : Nat\n  proof : 0 = 0\n  after : Nat\ndef work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\ndef evidence (n : Nat) : 0 = 0 := let discarded : Nat := work n; by rfl\ndef keep (h : 0 = 0) : Nat := 42\n";
    let source = |proof: u64, before: u64, after: u64| {
        format!(
            "{data}#eval let c : Certified := {{ before := work {before}, proof := evidence {proof}, after := work {after} }}; 42"
        )
    };
    let cheap = run(&source(0, 0, 0), "42");
    assert_eq!(
        cheap,
        run(&source(1000000, 0, 0), "42"),
        "field evidence reached the VM"
    );
    assert!(
        run(&source(0, 40, 60), "42") > cheap + 100,
        "ordinary object fields were erased"
    );
    // The entire projection is a proof. Its discarded receiver computation is
    // part of constructing evidence, unlike the strict ordinary let above.
    let proof_projection = |n| {
        format!(
            "{data}#eval keep ({{ before := work {n}, proof := by rfl, after := work {n} }} : Certified).proof"
        )
    };
    assert_eq!(
        run(&proof_projection(0), "42"),
        run(&proof_projection(1000000), "42")
    );
}
#[test]
fn classifiers_do_not_erase_type_valued_decisions_or_false_proofs() {
    run(
        "def choose (d : Decidable (0 = 0)) : Nat := match d with | .isTrue h => 42 | .isFalse h => 0\n#eval choose (Decidable.isTrue (by rfl))",
        "42",
    );
    run(
        "def choose (d : Decidable (0 = 1)) : Nat := match d with | .isTrue h => 0 | .isFalse h => 42\n#eval choose (Decidable.isFalse (by intro h; cases h))",
        "42",
    );
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "structure Bad where\n  value : Nat\n  proof : 0 = 1\ndef b : Bad := { value := 42, proof := by rfl }\n#eval b.value",
        "structure Package where\n  carrier : Type\n  value : carrier\ndef p : Package := { carrier := Nat, value := 42 }\n#eval 42",
        "structure Certified where\n  value : Nat\n  proof : value = value\ndef c : Certified := { value := 40, proof := by rfl }\n#eval { c with value := 42 }.value",
        "structure Certified where\n  value : Nat\n  proof : value = value\ndef c : Certified := { value := 42, proof := by rfl }\n#eval c.value\ntheorem bad : 0 = 1 := by rfl",
    ] {
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(root, base.logical_root(&options));
    }
}

#[test]
fn ground_proposition_parameters_and_inherited_class_defaults_execute() {
    run(
        "structure ProofBox (p : Prop) where\n  evidence : p\n  value : Nat\ndef use (p : Prop) (b : ProofBox p) : Nat := b.value\n#eval use (0 = 0) { evidence := by rfl, value := 42 }",
        "42",
    );
    run(
        "class Base where\n  value : Nat\n  proof : value = value := by rfl\nclass Child extends Base where\n  offset : Nat\ndef c : Child := { value := 40, offset := 2 }\n#eval c.value + c.offset",
        "42",
    );
}
#[test]
fn stopped_proof_layouts_publish_nothing_and_recover_exact_bytecode() {
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let source = b"structure Certified where\n  value : Nat\n  proof : value = value\ndef c : Certified := { value := 42, proof := by rfl }\n#eval c.value";
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut small = limits();
    small.ingress.fir.max_constructors = 0;
    assert!(
        base.execute_source_definitions(&[source], &options, small)
            .is_err()
    );
    let mut small = limits();
    small.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[source], &options, small)
            .is_err()
    );
    let mut small = limits();
    small.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source], &options, small)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(root, base.logical_root(&options));
    let run = || {
        base.execute_source_definitions(&[source], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let one = run();
    let two = run();
    assert_eq!(
        one.engine.logical_root(&options),
        two.engine.logical_root(&options)
    );
    for (one, two) in one.executions.iter().zip(&two.executions) {
        assert_eq!(one.flbc_artifact, two.flbc_artifact);
    }
    assert_eq!(root, base.logical_root(&options));
}

#[test]
fn function_child_recursion_composes_with_dependent_proof_slots() {
    run(
        "inductive Tree where\n| leaf (n : Nat) (h : n = n)\n| node (h : 0 = 0) (child : (n : Nat) -> n = n -> Tree)\ndef follow (t : Tree) : Nat := match t with | .leaf n h => n | .node h child => follow (child 40 (by rfl))\n#eval follow (Tree.node (by rfl) (fun n h => Tree.leaf (n + 2) (by rfl)))",
        "42",
    );
}

#[test]
fn successful_execution_preserves_the_check_only_logical_environment() {
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let source = b"structure Certified where\n  value : Nat\n  proof : value = value := by rfl\ndef keep (n : Nat) (h : n = n) : Nat := n\ndef c : Certified := { value := 42 }";
    let options = KVMap::new();
    let checked = base
        .check_source_files(
            &[source],
            &options,
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let executed = base
        .execute_source_definitions(&[source], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        checked.engine.logical_root(&options),
        executed.engine.logical_root(&options)
    );
}
