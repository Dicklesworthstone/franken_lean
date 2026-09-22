//! Checked source records use native object slots, closures and FLBC replay.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn base(declarations: &str) -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[declarations.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}
fn run(base: &Engine, source: &str, expected: &str) {
    let result = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("not returned")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}
#[test]
fn constructors_projections_and_reusable_record_functions_execute() {
    let engine = base("structure Point where\n  x : Nat\n  y : Nat");
    run(
        &engine,
        "def point : Point := { x := 17, y := 25 }\ndef sum (p : Point) : Nat := p.x + p.y\n#eval sum point",
        "42",
    );
}
#[test]
fn record_updates_and_chained_projections_preserve_nested_owned_fields() {
    let engine = base(
        "structure Item where\n  label : String\n  count : Nat\nstructure Box where\n  item : Item\n  flag : Bool",
    );
    run(
        &engine,
        "def b : Box := { item := { label := \"hello\", count := 7 }, flag := true }\ndef updated : Box := { b with item := { b.item with count := 37 } }\n#eval updated.item.count + String.length updated.item.label",
        "42",
    );
}
#[test]
fn records_are_captured_and_returned_by_local_closures() {
    let engine = base("structure Item where\n  count : Nat\n  label : String");
    run(
        &engine,
        "def work (p : Item) : Nat := let f (x : Nat) : Item := { p with count := p.count + x }; let q : Item := f 35; q.count + String.length q.label\n#eval work { count := 2, label := \"hello\" }",
        "42",
    );
}
#[test]
fn conditional_record_results_are_lazy_and_owned() {
    let engine = base("structure Item where\n  count : Nat\n  label : String");
    run(
        &engine,
        "def choose (b : Bool) (p q : Item) : Item := if b then p else q\n#eval (choose true { count := 42, label := \"yes\" } { count := 7, label := \"no\" }).count",
        "42",
    );
}
#[test]
fn single_constructor_inductives_and_empty_data_records_have_object_layouts() {
    let engine = base("inductive Pair where\n | mk (x y : Nat)\nstructure Marker : Type where");
    run(
        &engine,
        "def p : Pair := Pair.mk 17 25\n#eval let unused : Pair := p; 42",
        "42",
    );
    // An empty record can be passed without inventing a scalar ABI.
    run(
        &engine,
        "def ignore (e : Marker) : Nat := 42\n#eval ignore Marker.mk",
        "42",
    );
}
#[test]
fn distinct_record_layouts_do_not_alias_by_constructor_tag() {
    let engine = base("structure A where\n  x : Nat\nstructure B where\n  x : String");
    run(
        &engine,
        "def a : A := { x := 37 }\ndef b : B := { x := \"hello\" }\n#eval a.x + String.length b.x",
        "42",
    );
}
#[test]
fn unsupported_value_dependent_fields_do_not_become_unchecked_objects() {
    let engine = base("structure Package where\n  carrier : Type\n  value : carrier");
    let source = "def p : Package := { carrier := Nat, value := 42 }";
    let root = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .execute_source_definitions(
                &[source.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(admission().kernel)
            )
            .is_err()
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    run(&engine, "#eval 42", "42");
}
#[test]
fn layout_budget_refusal_and_late_type_errors_preserve_the_engine() {
    let engine = base("structure Point where\n  x : Nat\n  y : Nat");
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let mut tiny = EngineExecutionLimits::new(admission().kernel);
    tiny.ingress.fir.max_constructors = 0;
    assert!(
        engine
            .execute_source_definitions(&[b"#eval (Point.mk 17 25).x"], &options, tiny)
            .is_err()
    );
    assert!(
        engine
            .execute_source_definitions(
                &[b"#eval 42\ndef bad : Point := { x := true, y := 1 }"],
                &options,
                EngineExecutionLimits::new(admission().kernel)
            )
            .is_err()
    );
    assert_eq!(engine.logical_root(&options), root);
    run(&engine, "#eval (Point.mk 42 0).x", "42");
}
#[test]
fn repeated_compilation_produces_identical_record_bytecode() {
    let engine = base("structure Point where\n  x : Nat\n  y : Nat");
    let source = b"def p : Point := { x := 17, y := 25 }\n#eval p.x + p.y";
    let one = engine
        .execute_source_definitions(
            &[source],
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let two = engine
        .execute_source_definitions(
            &[source],
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for (a, b) in one.executions.iter().zip(&two.executions) {
        assert_eq!(a.flbc_artifact, b.flbc_artifact);
        assert_eq!(a.declaration, b.declaration);
    }
}

#[test]
fn matching_destructures_records_and_nested_payloads() {
    let engine = base(
        "structure Point where\n  x : Nat\n  y : Nat\nstructure Box where\n  point : Point\n  label : String",
    );
    run(
        &engine,
        "def sum (p : Point) : Nat := match p with | .mk x y => x + y\n#eval sum { x := 17, y := 25 }",
        "42",
    );
    run(
        &engine,
        "def sum (p : Box) : Nat := match p with | .mk point label => match point with | .mk x y => x + y + String.length label\n#eval sum { point := { x := 17, y := 20 }, label := \"hello\" }",
        "42",
    );
}
#[test]
fn record_match_returns_owned_records_without_duplicating_the_major() {
    let engine = base("structure Item where\n  label : String\n  count : Nat");
    run(
        &engine,
        "def grow (p : Item) : Item := match p with | .mk label count => { label := label ++ label, count := count + count }\n#eval let p : Item := grow { label := \"hello\", count := 16 }; p.count + String.length p.label",
        "42",
    );
}
#[test]
fn nat_recursion_can_return_records_and_share_recursive_objects() {
    let engine = base("structure State where\n  count : Nat\n  label : String");
    run(
        &engine,
        "def grow (n : Nat) : State := match n with | .zero => { count := 1, label := \"x\" } | .succ k => let p : State := grow k; { p with count := p.count + p.count }\n#eval (grow 10).count",
        "1024",
    );
}
#[test]
fn changing_record_accumulators_execute_with_native_ownership() {
    let engine = base("structure State where\n  count : Nat\n  label : String");
    run(
        &engine,
        "def walk (n : Nat) (p : State) : State := match n with | .zero => p | .succ k => walk k { p with count := p.count + n, label := p.label ++ \"x\" }\n#eval let result : State := walk 7 { count := 7, label := \"\" }; result.count + String.length result.label",
        "42",
    );
}
