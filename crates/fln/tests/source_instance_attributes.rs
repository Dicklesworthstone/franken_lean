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

#[test]
fn global_reducibility_attributes_control_real_instance_conversion() {
    let checked = checked(
        &engine(),
        "def namedOne : Nat := 1\n\
         attribute [reducible] namedOne\n\
         def literalAtNamedIndex {A : Type} [OfNat A namedOne] : A := 1",
    );
    assert_eq!(
        fln_elab::reducibility::known_status(checked.environment(), &n("namedOne")),
        Ok(Some(fln_elab::reducibility::Reducibility::Reducible)),
    );
    let control = engine().check_source_files(
        &[b"def namedOne : Nat := 1\n\
            def literalAtNamedIndex {A : Type} [OfNat A namedOne] : A := 1"],
        &KVMap::new(),
        limits(),
    );
    let error = control.unwrap_err();
    assert_eq!(error.disposition(), ("elaboration", false, 1));
}

#[test]
fn global_reducibility_resolves_exact_names_and_survives_the_file() {
    let base = engine();
    let before = fln_elab::reducibility::ReducibilityTable::read(base.environment()).unwrap();
    let one = b"namespace Visibility\n\
        def hidden : Nat := 4\n\
        def \xc2\xabpart.name\xc2\xbb : Nat := 5\n\
        end Visibility\n\
        open Visibility\n\
        attribute [irreducible] hidden \xc2\xabpart.name\xc2\xbb";
    let result = base
        .check_source_files(
            &[one.as_slice(), b"def nextFile : Nat := 6"],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for name in [
        n("Visibility.hidden"),
        Name::from_components(["Visibility", "part.name"]),
    ] {
        assert_eq!(
            fln_elab::reducibility::known_status(result.engine.environment(), &name),
            Ok(Some(fln_elab::reducibility::Reducibility::Irreducible)),
        );
    }
    assert_eq!(
        fln_elab::reducibility::ReducibilityTable::read(base.environment()).unwrap(),
        before,
        "source attribute updates must preserve every existing base status",
    );
}

#[test]
fn reducibility_validation_rejects_invalid_transitions_and_nondefinitions() {
    // Pin authority: Lean/ReducibilityAttrs.lean's `validate`, also exercised by
    // tests/elab/reducibilityAttrValidation.lean. Global semireducible is never
    // a reset operation under the default options.
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for tail in [
        "attribute [semireducible] value",
        "attribute [reducible] value\nattribute [reducible] value",
        "attribute [irreducible] value\nattribute [irreducible] value",
        "attribute [reducible] value\nattribute [irreducible] value",
        "attribute [irreducible] value\nattribute [reducible] value",
        "attribute [irreducible] reflexive",
        "attribute [irreducible] Nat",
        "attribute [reducible] Nat.zero",
        "attribute [scoped irreducible] value",
        "namespace Scope\nattribute [scoped reducible] value\nend Scope",
    ] {
        let source = format!("def value : Nat := 4\ntheorem reflexive : 0 = 0 := rfl\n{tail}");
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .unwrap_err();
        assert!(
            error.to_string().contains("reducibility"),
            "{tail}: {error}"
        );
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
}

#[test]
fn global_reducibility_cannot_rewrite_declarations_from_earlier_files() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for attribute in ["reducible", "irreducible", "semireducible"] {
        let command = format!("attribute [{attribute}] importedValue");
        let error = base
            .check_source_files(
                &[b"def importedValue : Nat := 4", command.as_bytes()],
                &KVMap::new(),
                limits(),
            )
            .unwrap_err();
        assert!(error.to_string().contains("this file"), "{error}");
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
}

#[test]
fn reducibility_updates_replay_through_native_source_module_imports() {
    let names = [n("NamedIndex"), n("IndexConsumer")];
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: b"prelude\ndef namedOne : Nat := 1\nattribute [reducible] namedOne",
        },
        SourceModuleInput {
            name: &names[1],
            source: b"prelude\nimport NamedIndex\n\
                def importedIndex {A : Type} [OfNat A namedOne] : A := 1",
        },
    ];
    let result = engine()
        .check_source_modules(
            &inputs,
            &names[1],
            &KVMap::new(),
            SourceModuleCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        result
            .checked
            .engine
            .environment()
            .contains(&n("importedIndex"))
    );
    assert_eq!(
        fln_elab::reducibility::known_status(result.checked.engine.environment(), &n("namedOne")),
        Ok(Some(fln_elab::reducibility::Reducibility::Reducible)),
    );
}

#[test]
fn late_reducibility_failures_and_oversized_lists_leave_no_prefix() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for suffix in ["missing", "Nat.zero", "value"] {
        let source = format!("def value : Nat := 4\nattribute [irreducible] value {suffix}");
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .unwrap_err();
        assert!(error.to_string().contains("reducibility"), "{error}");
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
    let source = format!(
        "def value : Nat := 4\nattribute [irreducible] {}",
        "value ".repeat(4097),
    );
    let error = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_err();
    assert_eq!(error.disposition(), ("resource", false, 3));
    assert_eq!(before, base.logical_root(&KVMap::new()));
    checked(&base, "theorem recovery : 4 = 4 := rfl");
}

#[test]
fn standalone_instance_attributes_preserve_reducibility_until_explicitly_changed() {
    for attribute in ["implicit_reducible", "instance_reducible", "reducible"] {
        let source = format!(
            "def dictionary : Inhabited Nat := Inhabited.mk 7\n\
             attribute [instance 2000] dictionary\n\
             attribute [{attribute}] dictionary\n\
             theorem selected : default = 7 := rfl"
        );
        let result = checked(&engine(), &source);
        assert_eq!(
            fln_elab::reducibility::known_status(result.environment(), &n("dictionary")),
            Ok(Some(if attribute == "reducible" {
                fln_elab::reducibility::Reducibility::Reducible
            } else {
                fln_elab::reducibility::Reducibility::ImplicitReducible
            })),
        );
    }
    let result = checked(
        &engine(),
        "def dictionary : Inhabited Nat := Inhabited.mk 7\n\
         attribute [instance 2000] dictionary",
    );
    assert_eq!(
        fln_elab::reducibility::known_status(result.environment(), &n("dictionary")),
        Ok(Some(fln_elab::reducibility::Reducibility::Semireducible)),
    );
    let result = checked(
        &engine(),
        "instance dictionary : Inhabited Nat := Inhabited.mk 7\n\
         attribute [irreducible] dictionary",
    );
    assert_eq!(
        fln_elab::reducibility::known_status(result.environment(), &n("dictionary")),
        Ok(Some(fln_elab::reducibility::Reducibility::Irreducible)),
    );
}

#[test]
fn local_reducibility_is_explicitly_refused_without_persisting_the_override() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[b"def value : Nat := 4\nattribute [local irreducible] value"],
            &KVMap::new(),
            limits(),
        )
        .unwrap_err();
    assert!(error.to_string().contains("lexical restoration"), "{error}");
    assert_eq!(error.disposition(), ("input", false, 1));
    assert_eq!(before, base.logical_root(&KVMap::new()));
}

#[test]
fn generated_projection_statuses_distinguish_class_fields_and_default_helpers() {
    use fln_elab::reducibility::{Reducibility, known_status};
    let source = "structure Plain where\n  value : Nat\n\
        class Choice where\n  value : Nat := 4";
    let base = engine();
    let result = checked(&base, source);
    assert_eq!(
        known_status(result.environment(), &n("Plain.value")),
        Ok(Some(Reducibility::Reducible)),
    );
    assert_eq!(
        known_status(result.environment(), &n("Choice.value")),
        Ok(Some(Reducibility::Semireducible)),
    );
    let helper = fln_elab::records::defaults::helper_name(&n("Choice"), &n("value"));
    assert_eq!(
        known_status(result.environment(), &helper),
        Ok(Some(Reducibility::Semireducible)),
    );
    for attribute in ["reducible", "irreducible", "implicit_reducible"] {
        let source = format!("{source}\nattribute [{attribute}] Plain.value");
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .unwrap_err();
        assert!(error.to_string().contains("transition"), "{error}");
    }
    let source = format!("{source}\nattribute [irreducible] Choice.value");
    let result = checked(&base, &source);
    assert_eq!(
        known_status(result.environment(), &n("Choice.value")),
        Ok(Some(Reducibility::Irreducible)),
    );
}

#[test]
fn proof_projections_are_checked_as_theorems_and_cannot_receive_reducibility_attributes() {
    let source = "structure Witness where\n  value : Nat\n  equal : value = 7\n\
        class Evidence (p : Prop) where\n  proof : p\n\
        structure DefaultProof where\n  proof : 0 = 0 := rfl\n\
        structure InheritedProof extends DefaultProof\n\
        def witness : Witness := { equal := rfl, value := 7 }\n\
        theorem useProjection (w : Witness) : w.value = 7 := w.equal\n\
        theorem useInherited (w : InheritedProof) : 0 = 0 := w.proof\n\
        theorem useExplicit (p : Prop) (w : Evidence p) : p := w.proof";
    let base = engine();
    let result = checked(&base, source);
    for name in ["Witness.equal", "Evidence.proof", "DefaultProof.proof"] {
        assert!(
            matches!(
                result.environment().find(&n(name)),
                Some(fln::ConstantInfo::Thm(_))
            ),
            "{name} must be a checked theorem",
        );
    }
    let helper = fln_elab::records::defaults::helper_name(&n("DefaultProof"), &n("proof"));
    assert!(matches!(
        result.environment().find(&helper),
        Some(fln::ConstantInfo::Defn(_)),
    ));
    for name in ["Witness.equal", "Evidence.proof", "DefaultProof.proof"] {
        let source = format!("{source}\nattribute [irreducible] {name}");
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .unwrap_err();
        assert!(error.to_string().contains("not a definition"), "{error}");
    }
    assert!(!base.environment().contains(&n("Witness")));
}
