//! Real source streams: record/theorem admission interleaved with execution.
#![forbid(unsafe_code)]
use fln::{
    Budget, DefinitionBatchExecution, Engine, EngineAdmissionLimits, EngineExecutionError,
    EngineExecutionLimits, KVMap, Name, Outcome, SourceModuleInput, VmExit,
};
fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn value(result: &DefinitionBatchExecution, expected: &str) {
    let VmExit::Returned(returned) = &result.executions.last().unwrap().exit else {
        panic!("VM return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
        Some(expected)
    );
}
const POINT: &str = "structure Point where\n  x : Nat\n  y : Nat\n";

#[test]
fn structure_theorem_and_execution_share_one_atomic_source_stream() {
    let base = engine();
    let opts = KVMap::new();
    let root = base.logical_root(&opts);
    let source = format!(
        "{POINT}def sum (p : Point) : Nat := match p with | .mk x y => x + y\ntheorem sum_ok : sum (Point.mk 17 25) = 42 := by rfl\n#eval sum {{ x := 17, y := 25 }}"
    );
    let batch = base
        .execute_source_definitions(&[source.as_bytes()], &opts, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    value(&batch, "42");
    assert_eq!(batch.executions.len(), 2);
    assert_eq!(batch.source_execution_command_indices, [1, 3]);
    assert_eq!(batch.source_evaluation_indices, [1]);
    assert_eq!(batch.source_admissions.len(), 2);
    assert_eq!(batch.source_admissions[0].command_index, 0);
    assert_eq!(batch.source_admissions[0].admission.admissions.len(), 3);
    assert_eq!(batch.source_admissions[1].command_index, 2);
    assert_eq!(batch.source_admissions[0].admission.base_logical_root, root);
    assert_eq!(
        batch.executions[0].base_logical_root,
        batch.source_admissions[0].admission.result_logical_root
    );
    assert_eq!(
        batch.source_admissions[1].admission.base_logical_root,
        batch.executions[0].result_logical_root
    );
    assert_eq!(
        batch.executions[1].base_logical_root,
        batch.source_admissions[1].admission.result_logical_root
    );
    assert_eq!(base.logical_root(&opts), root);
    assert!(
        batch
            .engine
            .environment()
            .contains(&Name::from_components(["sum_ok"]))
    );
}

#[test]
fn definitions_in_separate_source_files_see_admitted_records() {
    let batch = engine()
        .execute_source_definitions(
            &[
                POINT.as_bytes(),
                b"#eval (Point.mk 17 25).x + (Point.mk 17 25).y",
            ],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    value(&batch, "42");
}

#[test]
fn declaration_only_streams_and_scratch_checks_do_not_fabricate_executions() {
    let base = engine();
    let source = format!("{POINT}#check Point.mk");
    let result = base
        .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(result.batch.executions.is_empty());
    assert!(result.execution_command_indices.is_empty());
    assert_eq!(result.command_count, 2);
    assert_eq!(result.checks.len(), 1);
    assert_eq!(result.batch.source_admissions.len(), 1);
    assert_eq!(
        result.batch.engine.logical_root(&KVMap::new()),
        result.checks[0].environment_root
    );
    let batch = base
        .execute_source_definitions(&[POINT.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(batch.executions.is_empty());
    assert_eq!(batch.source_admissions.len(), 1);
}

#[test]
fn single_constructor_inductives_are_usable_in_ordinary_source_files() {
    let batch = engine().execute_source_definitions(&[b"inductive Item where\n  | mk (value : Nat)\ndef get (p : Item) : Nat := match p with | .mk n => n\n#eval get (Item.mk 42)"], &KVMap::new(), limits())
        .unwrap().into_complete().unwrap();
    value(&batch, "42");
}

#[test]
fn imported_records_work_and_keep_dependency_only_prefix_evidence() {
    let [a, b, entry] = ["A", "B", "Entry"].map(|s| Name::from_components([s]));
    let modules = [
        SourceModuleInput {
            name: &entry,
            source: b"import B\n#eval sum { x := 17, y := 25 }",
        },
        SourceModuleInput {
            name: &b,
            source: b"import A\ndef sum (p : Point) : Nat := p.x + p.y",
        },
        SourceModuleInput {
            name: &a,
            source: POINT.as_bytes(),
        },
    ];
    let batch = engine()
        .execute_source_modules(&modules, &entry, &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    value(&batch, "42");
    assert_eq!(
        batch.source_module_order,
        [a.clone(), b.clone(), entry.clone()]
    );
    assert_eq!(batch.source_execution_command_indices, [1, 2]);
    let modules = [
        SourceModuleInput {
            name: &entry,
            source: b"import A\n#eval (Point.mk 42 0).x",
        },
        SourceModuleInput {
            name: &a,
            source: POINT.as_bytes(),
        },
    ];
    let mixed = engine()
        .execute_source_modules_with_entry_checks(&modules, &entry, &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let prefix = mixed
        .dependency_prefix
        .expect("admitted record evidence survives without executions");
    assert!(prefix.executions.is_empty());
    assert_eq!(prefix.source_admissions.len(), 1);
    assert_eq!(mixed.dependency_command_count, 1);
    value(&mixed.entry.batch, "42");
}

#[test]
fn unimported_sibling_types_constructors_projections_defaults_and_proofs_are_refused() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let [a, b, entry] = ["A", "B", "Entry"].map(|s| Name::from_components([s]));
    let first = format!("{POINT}def secret : Nat := 42\ntheorem secret_ok : secret = 42 := by rfl");
    for sibling in [
        "def bad (p : Point) : Nat := p.x",
        "#eval (Point.mk 17 25).x",
        "#eval Point.x (Point.mk 17 25)",
        "structure Holder where\n  point : Point",
        "structure Hidden where\n  count : Nat := secret",
        "theorem stolen : secret = 42 := by exact secret_ok",
    ] {
        let modules = [
            SourceModuleInput {
                name: &entry,
                source: b"import A B\n#eval 42",
            },
            SourceModuleInput {
                name: &b,
                source: sibling.as_bytes(),
            },
            SourceModuleInput {
                name: &a,
                source: first.as_bytes(),
            },
        ];
        assert!(
            matches!(
                base.execute_source_modules(&modules, &entry, &KVMap::new(), limits()),
                Err(EngineExecutionError::SourceModuleVisibility { .. })
            ),
            "{sibling}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn record_scopes_and_invalid_late_theorems_never_publish_partial_success() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for suffix in [
        "structure Broken where\n  x : Missing",
        "theorem bad : 1 = 2 := by rfl",
        "def wrong : Point := { x := true, y := 7 }",
    ] {
        let source = format!("{POINT}#eval 42\n{suffix}");
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{suffix}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
    let mut tiny = limits();
    tiny.vm.max_steps = 0;
    let source = format!("{POINT}#eval (Point.mk 42 0).x");
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, tiny)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["Point"]))
    );
    let good = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    value(&good, "42");
}
