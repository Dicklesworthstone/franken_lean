//! Local recursive helpers are checked source declarations, not name aliases.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
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
fn check(base: &Engine, source: &str) -> Engine {
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
    let fln::VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("no returned value")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}
fn helper<'a>(base: &'a Engine, components: &[&str]) -> &'a fln_env::constants::DefinitionVal {
    let name = Name::from_components(components.iter().copied());
    let Some(ConstantInfo::Defn(value)) = base.environment().find(&name) else {
        panic!("no checked helper {name:?}");
    };
    for e in [&value.base.type_, &value.value] {
        assert!(!e.has_fvar() && !e.has_loose_bvars() && !e.has_expr_mvar() && !e.has_level_mvar());
    }
    value
}

#[test]
fn local_and_where_helpers_have_public_checked_names() {
    let base = check(
        &engine(),
        "def foo : Nat := let rec bar : Nat := 5; bar\ndef other : Nat := value where\n  value : Nat := 6",
    );
    helper(&base, &["foo", "bar"]);
    helper(&base, &["other", "value"]);
    check(
        &base,
        "theorem a : foo.bar = 5 := rfl\ntheorem b : other.value = 6 := rfl",
    );
    run(&base, "#eval foo.bar + other.value", "11");
}

#[test]
fn recursive_helpers_close_only_used_parameters_in_the_original_order() {
    let base = check(
        &engine(),
        "def count (unused offset n : Nat) : Nat :=\n  let rec go (m : Nat) : Nat := match m with\n    | 0 => offset\n    | k+1 => go k + 1\n  go n",
    );
    helper(&base, &["count", "go"]);
    run(&base, "#eval count.go 7 3", "10");
    check(&base, "theorem a : count 99 7 3 = count.go 7 3 := rfl");
}

#[test]
fn nested_helpers_use_their_lexical_parent_names_and_dead_helpers_are_retained() {
    let base = check(
        &engine(),
        "def outer : Nat :=\n  let rec inner : Nat :=\n    let rec nested : Nat := 12\n    nested\n  let rec unused : Nat := 8\n  inner",
    );
    for parts in [
        &["outer", "inner"][..],
        &["outer", "inner", "nested"],
        &["outer", "unused"],
    ] {
        helper(&base, parts);
    }
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["inner"]))
    );
    run(&base, "#eval outer.inner.nested + outer.unused", "20");
}

#[test]
fn fresh_helper_names_cannot_overwrite_existing_or_duplicate_declarations() {
    let base = engine();
    for source in [
        "def foo.bar : Nat := 1\ndef foo : Nat := let rec bar : Nat := 5; bar",
        "def foo : Nat := let rec bar : Nat := 1; let rec bar : Nat := 2; bar",
        "def foo : Nat := let rec bar : Nat := true; 1",
    ] {
        let root = base.logical_root(&KVMap::new());
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
        assert!(!base.environment().contains(&Name::from_components(["foo"])));
    }
    check(
        &base,
        "def recovered : Nat := let rec good : Nat := 3; good\ntheorem a : recovered.good = 3 := rfl",
    );
}

#[test]
fn lifted_helpers_preserve_unsafe_classification_and_cannot_supply_safe_evidence() {
    let base = check(
        &engine(),
        "unsafe def outer : Nat := let rec helper : Nat := 42; helper",
    );
    assert_eq!(
        helper(&base, &["outer", "helper"]).safety,
        DefinitionSafety::Unsafe
    );
    run(&base, "#eval outer.helper", "42");
    for source in [
        "def leak : Nat := outer.helper",
        "theorem leak : outer.helper = 42 := rfl",
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
    }
}

#[test]
fn polymorphic_and_late_instance_captures_keep_closed_typed_interfaces() {
    let base = check(
        &engine(),
        "def poly.{u} {A : Sort u} (x : A) : A := let rec get (flag : Bool) : A := x; get false\ndef unrelated.{u} {A : Sort u} (x : A) : A := let rec get : Nat := 4; x",
    );
    helper(&base, &["poly", "get"]);
    assert!(
        helper(&base, &["unrelated", "get"])
            .base
            .level_params
            .is_empty()
    );
    run(&base, "#eval poly.get 17 false", "17");
    let base = check(
        &base,
        "class Choice (A : Type) where chosen : A\ndef choose {A : Type} [Choice A] : A := Choice.chosen\ndef captureLate [Choice Nat] : Nat := let rec get (flag : Bool) : _ := choose; get false",
    );
    helper(&base, &["captureLate", "get"]);
    run(&base, "#eval @captureLate.get ⟨7⟩ false", "7");
}

#[test]
fn theorems_type_positions_and_namespaces_keep_helper_identity() {
    let base = check(
        &engine(),
        "namespace N\ndef owned : Nat := let rec «a.b» : Nat := 8; «a.b»\ntheorem proof (P : Prop) (hp : P) : P := let rec evidence : P := hp; evidence\ndef typed : (let rec A : Type := Nat; Nat) := 5\nend N",
    );
    helper(&base, &["N", "owned", "a.b"]);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["N", "owned", "a", "b"]))
    );
    assert!(matches!(
        base.environment()
            .find(&Name::from_components(["N", "proof", "evidence"])),
        Some(ConstantInfo::Thm(_))
    ));
    check(
        &base,
        "theorem fromLifted (P : Prop) (h : P) : P := N.proof.evidence P h\ntheorem sameType : N.typed.A = Nat := rfl",
    );
    run(&base, "#eval N.owned.«a.b»", "8");
}

#[test]
fn single_source_admission_retains_every_real_checker_transition() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let admitted = base.admit_source_declaration(b"def owner : Nat := let rec first : Nat := 3; let rec second : Nat := 4; first + second", &KVMap::new(), EngineAdmissionLimits::new(budget())).unwrap().into_complete().unwrap();
    assert_eq!(admitted.admissions.len(), 3);
    assert_eq!(admitted.base_logical_root, root);
    let mut previous = root;
    for receipt in &admitted.admissions {
        assert_eq!(receipt.base_logical_root, previous);
        assert_eq!(
            receipt.result_logical_root,
            receipt.engine.logical_root(&KVMap::new())
        );
        previous = receipt.result_logical_root;
    }
    assert_eq!(previous, admitted.result_logical_root);
    assert_eq!(
        admitted.result_logical_root,
        admitted.engine.logical_root(&KVMap::new())
    );
    helper(&admitted.engine, &["owner", "second"]);
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn lifted_helpers_roundtrip_through_independent_olean_import() {
    use fln::source_check::modules::{SourceModuleCheckLimits, imported::SourceOleanImportLimits};
    use fln::{OleanCheckLimits, OleanModuleInput, OleanWriteBudget, SourceModuleInput};
    let base = Engine::builder().build_empty();
    let library = Name::from_components(["Library"]);
    let main = Name::from_components(["Main"]);
    let input = [
        SourceModuleInput { name: &library, source: b"prelude\ninductive Bit where | off | on\ndef owner : Bit := let rec chosen : Bit := Bit.on; chosen" },
        SourceModuleInput { name: &main, source: b"prelude\nimport Library\ndef selected : Bit := owner.chosen" },
    ];
    let built = base
        .compile_source_modules(
            &input,
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
    let artifacts: Vec<_> = built
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
            &artifacts,
            &[main],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(4 * 1024 * 1024, budget())),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    for parts in [&["owner", "chosen"][..], &["selected"]] {
        let name = Name::from_components(parts.iter().copied());
        assert_eq!(
            imported.environment().find(&name),
            built.checked.checked.engine.environment().find(&name)
        );
        assert!(imported.environment().contains(&name));
    }
    let result = imported
        .execute_source_definitions(
            &[b"#eval owner.chosen"],
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("no returned helper")
    };
    assert_eq!(
        fln::vm_value_kind(&value.value),
        fln_vm::interpreter::ValueKind::Ctor(1)
    );
}
