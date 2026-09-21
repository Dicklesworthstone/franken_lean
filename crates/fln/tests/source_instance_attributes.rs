//! Real source attributes, dictionary synthesis, checker admission and imports.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits, SourceModuleInput,
};
use fln_elab::instances::InstanceRegistry;

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn standalone_attributes_drive_the_checked_example() {
    let base = engine();
    let checked = base
        .check_source_files(
            &[include_bytes!(
                "../../../examples/native_instance_attributes.lean"
            )],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.commands, 14);
    assert_eq!(checked.theorems, 5);
    assert_ne!(checked.base_logical_root, checked.result_logical_root);
}

#[test]
fn default_priority_and_multiple_names_preserve_registration_order() {
    checked(
        &engine(),
        "\
        def firstDictionary : Inhabited Nat := Inhabited.mk 7\n\
        def secondDictionary : Inhabited Nat := Inhabited.mk 9\n\
        attribute [instance] firstDictionary secondDictionary\n\
        theorem newestDictionary : default = 9 := by rfl",
    );
}

#[test]
fn attributes_resolve_namespaces_and_escaped_components_without_splitting_names() {
    checked(
        &engine(),
        "\
        namespace A\n\
        def «dictionary.part» : Inhabited Nat := Inhabited.mk 7\n\
        end A\n\
        namespace dictionary\n\
        def part : Inhabited Nat := Inhabited.mk 9\n\
        end dictionary\n\
        open A\n\
        attribute [instance 2000] «dictionary.part»\n\
        theorem structuralName : default = 7 := by rfl",
    );
}

#[test]
fn attributed_generic_instances_synthesize_their_prerequisites() {
    checked(
        &engine(),
        "\
        def functionDefault {A : Type} [Inhabited A] : Inhabited (Nat -> A) := Inhabited.mk (fun x => default)\n\
        attribute [instance 2000] functionDefault\n\
        def selectedFunction : Nat -> Nat := default\n\
        theorem nestedDictionary : selectedFunction 123 = 0 := by rfl",
    );
}

#[test]
fn late_unknown_or_nonclass_names_publish_no_attribute_prefix() {
    let base = checked(
        &engine(),
        "\
        def seven : Inhabited Nat := Inhabited.mk 7\n\
        def plain : Nat := 0",
    );
    let before = base.logical_root(&KVMap::new());
    for suffix in ["missing", "plain"] {
        let source = format!("attribute [instance 2000] seven {suffix}");
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err()
        );
        assert_eq!(before, base.logical_root(&KVMap::new()));
        assert!(
            !InstanceRegistry::read(base.environment())
                .unwrap()
                .candidates(&n("Inhabited"))
                .iter()
                .any(|entry| entry.declaration == n("seven"))
        );
        checked(&base, "theorem recovery : default = 0 := by rfl");
    }
}

#[test]
fn global_instance_attributes_survive_scope_and_source_file_boundaries() {
    let base = engine();
    let one = b"namespace Exported\n\
        def dictionary : Inhabited Nat := Inhabited.mk 7\n\
        attribute [instance 2000] dictionary\n\
        end Exported";
    let two = b"theorem fromEarlierFile : default = 7 := by rfl\n\
        attribute [instance 3000] Exported.dictionary\n\
        theorem afterUpdate : default = 7 := by rfl";
    let result = base
        .check_source_files(&[one.as_slice(), two.as_slice()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.files, 2);
    assert_eq!(result.theorems, 2);
    assert_eq!(
        InstanceRegistry::read(result.engine.environment())
            .unwrap()
            .candidates(&n("Inhabited"))[0]
            .declaration,
        n("Exported.dictionary")
    );
}

#[test]
fn unsupported_scoped_erasure_and_inline_forms_are_not_silent_noops() {
    let base = checked(&engine(), "def seven : Inhabited Nat := Inhabited.mk 7");
    let before = base.logical_root(&KVMap::new());
    for source in [
        "attribute [-instance] instInhabitedNat",
        "attribute [local instance] seven",
        "attribute [scoped instance] seven",
        "attribute [instance high] seven",
        "@[instance] def unsupported : Inhabited Nat := Inhabited.mk 7",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
}

#[test]
fn oversized_attribute_lists_are_resource_stops_without_publication() {
    let base = checked(&engine(), "def seven : Inhabited Nat := Inhabited.mk 7");
    let before = base.logical_root(&KVMap::new());
    let source = format!("attribute [instance] {}", "seven ".repeat(4097));
    let error = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_err();
    assert_eq!(error.disposition(), ("resource", false, 3));
    assert_eq!(before, base.logical_root(&KVMap::new()));
    checked(&base, "theorem intact : default = 0 := by rfl");
}

#[test]
fn updates_replay_across_imports_and_invalidate_cached_consumers() {
    const DICTIONARIES: &str = "prelude\n\
        def seven : Inhabited Nat := Inhabited.mk 7\n\
        def nine : Inhabited Nat := Inhabited.mk 9\n\
        attribute [instance 3000] seven\n\
        attribute [instance 4000] nine";
    const HIGH: &str = "prelude\nimport Dictionaries\nattribute [instance 5000] seven";
    const LOW: &str = "prelude\nimport Dictionaries\nattribute [instance 2000] seven";
    const USE_SEVEN: &str =
        "prelude\nimport Adjusted\ntheorem importedSelection : default = 7 := by rfl";
    const USE_NINE: &str =
        "prelude\nimport Adjusted\ntheorem importedSelection : default = 9 := by rfl";
    fn inputs<'a>(
        names: &'a [Name; 3],
        update: &'a str,
        consumer: &'a str,
    ) -> [SourceModuleInput<'a>; 3] {
        [
            SourceModuleInput {
                name: &names[0],
                source: DICTIONARIES.as_bytes(),
            },
            SourceModuleInput {
                name: &names[1],
                source: update.as_bytes(),
            },
            SourceModuleInput {
                name: &names[2],
                source: consumer.as_bytes(),
            },
        ]
    }
    let base = engine();
    let names = [n("Dictionaries"), n("Adjusted"), n("Consumer")];
    let module_limits = SourceModuleCheckLimits::new(limits());
    let mut session = SourceModuleSession::new(
        base.clone(),
        KVMap::new(),
        module_limits,
        SourceModuleCacheLimits::default(),
    );
    let first = session
        .check(&inputs(&names, HIGH, USE_SEVEN), &names[2])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(first.elaborated_modules, 3);
    assert_eq!(first.reused_modules, 0);
    let original_root = first.checked.checked.result_logical_root;
    let warm = session
        .check(&inputs(&names, HIGH, USE_SEVEN), &names[2])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(warm.reused_modules, 3);
    assert_eq!(warm.elaborated_modules, 0);
    assert_eq!(warm.checked.checked.result_logical_root, original_root);

    // Changing only an imported priority must not return the old checked proof.
    assert!(
        session
            .check(&inputs(&names, LOW, USE_SEVEN), &names[2])
            .is_err()
    );
    assert_eq!(session.retained_modules(), 3);
    let recovered = session
        .check(&inputs(&names, HIGH, USE_SEVEN), &names[2])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(recovered.reused_modules, 3);
    assert_eq!(recovered.checked.checked.result_logical_root, original_root);

    let fixed = inputs(&names, LOW, USE_NINE);
    let changed = session
        .check(&fixed, &names[2])
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(changed.reused_modules, 1);
    assert_eq!(changed.elaborated_modules, 2);
    assert_ne!(changed.checked.checked.result_logical_root, original_root);
    let cold = base
        .check_source_modules(&fixed, &names[2], &KVMap::new(), module_limits)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        changed.checked.checked.result_logical_root,
        cold.checked.result_logical_root
    );
}
