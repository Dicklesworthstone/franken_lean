//! Explicit unsafe source code is executable, never evidence for safe proofs.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    VmExit,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(budget()))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(EngineAdmissionLimits::new(budget())),
    )
    .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
    .into_complete()
    .unwrap()
    .engine
}
fn run(base: &Engine, source: &str, expected: &str) {
    let result = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let execution = result.executions.last().expect("an evaluation");
    let VmExit::Returned(value) = &execution.exit else {
        panic!("{execution:?}");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}

#[test]
fn unsafe_definitions_keep_their_safety_and_run_without_logical_companions() {
    let base = checked(
        &engine(),
        "unsafe def inc (n : Nat) : Nat := n + 1\nunsafe abbrev answer : Nat := inc 41",
    );
    for id in ["inc", "answer"] {
        let name = Name::from_components([id]);
        assert!(
            matches!(base.environment().find(&name), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Unsafe)
        );
        assert!(!base.environment().contains(&Name::str(name, "_unsafe_rec")));
    }
    run(&base, "#eval answer", "42");
    run(&base, "#eval inc 5", "6");
}

#[test]
fn recursive_unsafe_source_runs_its_actual_body_without_termination_evidence() {
    let base = checked(
        &engine(),
        "unsafe def gcd' (a b : Nat) : Nat := if b == 0 then a else gcd' b (a % b)",
    );
    run(&base, "#eval gcd' 48 18", "6");
    let base = checked(
        &base,
        "unsafe def down : Nat -> Nat | 0 => 7 | n + 1 => down n",
    );
    run(&base, "#eval down 12", "7");
}

#[test]
fn unsafe_code_cannot_become_a_safe_definition_or_theorem() {
    let base = checked(
        &engine(),
        "unsafe def value : Nat := 7\nunsafe def absurd (n : Nat) : False := absurd n",
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def leak : Nat := value",
        "theorem leak : False := absurd 0",
        "def leak : False := absurd 0",
        "theorem leak : value = value := by rfl",
        "unsafe theorem leak : True := by constructor",
        "unsafe partial def leak (n : Nat) : Nat := leak n",
        "unsafe def leak (n : Nat) : Nat := true",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(EngineAdmissionLimits::new(budget()))
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["leak"]))
        );
    }
    run(&base, "#eval value", "7");
}

#[test]
fn inferred_unsafe_recursion_and_section_captures_keep_types_and_scope() {
    let base = checked(
        &engine(),
        "section\nvariable (offset : Nat)\nunsafe def count (n : Nat) := if n == 0 then offset else count (n - 1)\nend",
    );
    run(&base, "#eval count 9 3", "9");
    let base = checked(&base, "unsafe def identity {A : Type} (x : A) : A := x");
    run(&base, "#eval identity 27", "27");
}

#[test]
fn unsafe_data_instances_are_registered_and_selected_without_losing_safety() {
    let base = checked(
        &engine(),
        "unsafe instance (priority := 2000) chosen : Inhabited Nat := ⟨42⟩",
    );
    let registry = fln_elab::instances::InstanceRegistry::read(base.environment()).unwrap();
    assert!(
        registry
            .candidates(&Name::from_components(["Inhabited"]))
            .iter()
            .any(|row| row.declaration == Name::from_components(["chosen"]))
    );
    assert!(
        matches!(base.environment().find(&Name::from_components(["chosen"])),
        Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Unsafe)
    );
    run(&base, "#eval (default : Nat)", "42");
    let base = checked(&base, "unsafe def selected : Nat := default");
    run(&base, "#eval selected", "42");
    let base = checked(
        &base,
        "unsafe instance (priority := 3000) : Inhabited Nat := ⟨43⟩",
    );
    run(&base, "#eval (default : Nat)", "43");
}

#[test]
fn unsafe_instance_dependencies_and_explicit_attributes_reach_the_runtime() {
    let base = checked(
        &engine(),
        "class Seed where\n  value : Nat\nclass Answer where\n  value : Nat\nunsafe def seed : Seed := ⟨41⟩\nattribute [instance] seed\nunsafe instance answer [s : Seed] : Answer := ⟨s.value + 1⟩\ndef pick [a : Answer] : Nat := a.value",
    );
    run(&base, "#eval pick", "42");
    // Turning off a selected unsafe rule must not keep its previous answer.
    // Erasures are lexical source-scope effects, not mutations of a dictionary
    // declaration. Keep the erasure and its consumer in the same source scope.
    assert!(
        base.execute_source_definitions(
            &[b"attribute [-instance] seed\n#eval pick"],
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .is_err()
    );
    run(
        &base,
        "attribute [-instance] seed\nattribute [instance] seed\n#eval pick",
        "42",
    );
}

#[test]
fn synthesized_unsafe_dictionaries_cannot_escape_into_safe_evidence() {
    let base = checked(
        &engine(),
        "unsafe def impossible : False := impossible\nunsafe instance falseDefault : Inhabited False := ⟨impossible⟩\nunsafe instance (priority := 2000) natDefault : Inhabited Nat := ⟨42⟩",
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def leak : Nat := default",
        "theorem leak : False := default",
        "def leak : False := default",
        "theorem leak : (default : Nat) = default := by rfl",
        "def leak : Nat := (fun (_ : False) => 0) default",
        "def leak : Nat := (fun (_ : Inhabited False) => 0) falseDefault",
        "unsafe instance bogus : Nat := 7",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(EngineAdmissionLimits::new(budget())),
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["leak"]))
        );
    }
    // Merely retaining unsafe instances must not poison unrelated safe proofs.
    checked(&base, "theorem valid : True := by constructor");
    run(&base, "#eval (default : Nat)", "42");
}

#[test]
fn unsafe_local_and_scoped_instances_keep_their_lexical_lifetimes() {
    let base = checked(
        &engine(),
        "class Pick where\n  value : Nat\ninstance fallback : Pick := ⟨1⟩\ndef selected [p : Pick] : Nat := p.value",
    );
    let source = "section\nunsafe local instance choice : Pick := ⟨7⟩\nunsafe def inside : Nat := selected\nend\ndef outside : Nat := selected\nnamespace N\nunsafe scoped instance scopedChoice : Pick := ⟨9⟩\nend N\nsection\nopen scoped N\nunsafe def opened : Nat := selected\nend\ndef restored : Nat := selected";
    let after = checked(&base, source);
    run(&after, "#eval inside", "7");
    run(&after, "#eval outside", "1");
    run(&after, "#eval opened", "9");
    run(&after, "#eval restored", "1");
    let registry = fln_elab::instances::InstanceRegistry::read(after.environment()).unwrap();
    let candidates = registry.candidates(&Name::from_components(["Pick"]));
    assert_eq!(candidates.len(), 1);
    assert_eq!(
        candidates[0].declaration,
        Name::from_components(["fallback"])
    );
}

#[test]
fn unsafe_instance_module_roundtrip_preserves_selection_and_safe_rejection() {
    use fln::source_check::modules::{SourceModuleCheckLimits, imported::SourceOleanImportLimits};
    use fln::{OleanCheckLimits, OleanModuleInput, OleanWriteBudget, SourceModuleInput};
    let base = Engine::builder().build_empty();
    let lib = Name::from_components(["Library"]);
    let main = Name::from_components(["Main"]);
    // No ambient seed: every declaration and registry entry has module provenance.
    let library = b"prelude\ninductive Choice where\n  | low\n  | high\nclass Pick where\n  value : Choice\nunsafe instance chosen : Pick := Pick.mk Choice.high\ndef selected [p : Pick] : Choice := p.value";
    let consumer = b"prelude\nimport Library\nunsafe def answer : Choice := selected";
    let modules = [
        SourceModuleInput {
            name: &main,
            source: consumer,
        },
        SourceModuleInput {
            name: &lib,
            source: library,
        },
    ];
    let build = base
        .compile_source_modules(
            &modules,
            &main,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
                budget(),
            ))),
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(build.artifacts.len(), 2);
    let inputs: Vec<_> = build
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    let imported = base
        .import_olean_modules_for_source(
            &inputs,
            &[main],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(4 * 1024 * 1024, budget())),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let original = build.checked.checked.engine.environment();
    assert_eq!(imported.environment().len(), original.len());
    for (name, value) in original.constants() {
        assert_eq!(imported.environment().find(name), Some(value), "{name:?}");
    }
    let registry = fln_elab::instances::InstanceRegistry::read(imported.environment()).unwrap();
    let candidates = registry.candidates(&Name::from_components(["Pick"]));
    assert_eq!(candidates.len(), 1);
    assert_eq!(candidates[0].declaration, Name::from_components(["chosen"]));
    let result = imported
        .execute_source_definitions(
            &[b"#eval selected"],
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let [execution] = result.executions.as_slice() else {
        panic!("one evaluation")
    };
    let VmExit::Returned(value) = &execution.exit else {
        panic!("{execution:?}")
    };
    assert_eq!(
        fln::vm_value_kind(&value.value),
        fln_vm::interpreter::ValueKind::Ctor(1)
    );
    assert!(
        imported
            .check_source_files(
                &[b"def leak : Choice := selected"],
                &KVMap::new(),
                SourceCheckLimits::new(EngineAdmissionLimits::new(budget())),
            )
            .is_err()
    );
    assert!(base.environment().is_empty());
}

#[test]
fn guard_queries_do_not_gain_eval_permissions_for_unsafe_dictionaries() {
    let base = checked(
        &engine(),
        "unsafe instance (priority := 2000) chosen : Inhabited Nat := ⟨42⟩",
    );
    run(&base, "#eval (default : Nat)", "42");
    let error = base
        .execute_source_commands_with_presentation(
            b"#guard (default : Nat) == 42",
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
            fln::EvaluationPresentation::Lean,
        )
        .unwrap_err();
    let diagnostic = format!("{error:?}");
    assert!(diagnostic.contains("SafetyViolation"), "{diagnostic}");
    assert!(diagnostic.contains("chosen"), "{diagnostic}");
    base.execute_source_commands_with_presentation(
        b"#guard (42 : Nat) == 42",
        &KVMap::new(),
        EngineExecutionLimits::new(budget()),
        fln::EvaluationPresentation::Lean,
    )
    .unwrap()
    .into_complete()
    .unwrap();
}
