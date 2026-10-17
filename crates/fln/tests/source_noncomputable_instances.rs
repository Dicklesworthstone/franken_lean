//! Noncomputable dictionaries and opaque constants through native council admission
//! and the executing source door. No Reference artifact or runtime is used here.
#![forbid(unsafe_code)]
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    SourceCheckLimits,
};
use std::collections::BTreeSet;

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn seed() -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("the council completes")
    .engine
}
fn executed(base: &Engine, source: &str) -> Engine {
    base.execute_source_commands_with_checks(
        source.as_bytes(),
        &KVMap::new(),
        EngineExecutionLimits::new(admission().kernel),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("the command stream completes")
    .batch
    .engine
}
fn tags(engine: &Engine) -> BTreeSet<Name> {
    fln_elab::noncomputable::read(engine.environment()).expect("valid noncomputable journal")
}
fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
const CLASS: &str =
    "class Marker where\n  value : Nat\ndef read [m : Marker] : Nat := @Marker.value m\n";

#[test]
fn named_noncomputable_instances_remain_available_to_checked_proofs() {
    let base = executed(&seed(), CLASS);
    let next = executed(
        &base,
        "noncomputable instance chosen : Marker := Marker.mk 23\ntheorem chosenValue : read = 23 := by rfl\n",
    );
    assert_eq!(tags(&next), BTreeSet::from([n("chosen")]));
    assert!(
        fln_elab::instances::InstanceRegistry::read(next.environment())
            .unwrap()
            .is_instance(&n("chosen"))
    );
    assert!(
        matches!(next.environment().find(&n("chosen")), Some(ConstantInfo::Defn(value)) if value.safety == fln_env::constants::DefinitionSafety::Safe)
    );
}

#[test]
fn anonymous_instances_bind_tags_to_each_fresh_admitted_name() {
    let base = checked(&seed(), CLASS);
    let next = checked(
        &base,
        "noncomputable instance : Marker := Marker.mk 3\nnoncomputable instance : Marker := Marker.mk 5\ntheorem newest : read = 5 := by rfl\n",
    );
    let tagged = tags(&next);
    assert_eq!(tagged.len(), 2);
    let registry = fln_elab::instances::InstanceRegistry::read(next.environment()).unwrap();
    for name in tagged {
        assert!(!name.is_anonymous());
        assert!(!base.environment().contains(&name));
        assert!(registry.is_instance(&name));
        assert!(matches!(
            next.environment().find(&name),
            Some(ConstantInfo::Defn(_))
        ));
    }
}

#[test]
fn single_declaration_door_tags_anonymous_and_named_instances_after_admission() {
    let base = checked(&seed(), CLASS);
    for source in [
        "noncomputable instance : Marker := Marker.mk 7",
        "noncomputable instance named : Marker := Marker.mk 11",
    ] {
        let result = base
            .admit_source_declaration(source.as_bytes(), &KVMap::new(), admission())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"))
            .into_complete()
            .unwrap();
        let tagged = tags(&result.engine);
        assert_eq!(tagged.len(), 1);
        let declared = match &result.declaration {
            fln::Declaration::Defn(value) => &value.base.name,
            other => panic!("data instance: {other:?}"),
        };
        assert_eq!(tagged, BTreeSet::from([declared.clone()]));
        assert_eq!(
            result.result_logical_root,
            result.engine.logical_root(&KVMap::new())
        );
    }
    assert!(tags(&base).is_empty());
}

#[test]
fn noncomputable_instance_dictionaries_cannot_enter_runtime_code() {
    let base = executed(&seed(), CLASS);
    let control = executed(
        &base,
        "instance chosen : Marker := Marker.mk 23\n#eval read\n",
    );
    assert!(tags(&control).is_empty());
    let next = executed(
        &base,
        "noncomputable instance chosen : Marker := Marker.mk 23\n",
    );
    let root = next.logical_root(&KVMap::new());
    for source in [
        "#eval read\n",
        "def bad : Nat := read\n",
        "#eval chosen.value\n",
    ] {
        assert!(
            next.execute_source_commands_with_checks(
                source.as_bytes(),
                &KVMap::new(),
                EngineExecutionLimits::new(admission().kernel)
            )
            .is_err(),
            "accepted {source}"
        );
        assert_eq!(next.logical_root(&KVMap::new()), root);
    }
    executed(
        &next,
        "noncomputable def allowed : Nat := read\ntheorem value : allowed = 23 := by rfl\n",
    );
}

#[test]
fn lexical_noncomputable_instances_restore_computable_outer_selection() {
    let base = executed(&seed(), CLASS);
    let next = executed(
        &base,
        "instance fallback : Marker := Marker.mk 2\nsection\nnoncomputable local instance selected : Marker := Marker.mk 13\ntheorem inner : read = 13 := by rfl\nend\n#eval read\ntheorem outer : read = 2 := by rfl\n",
    );
    assert_eq!(tags(&next), BTreeSet::from([n("selected")]));
    executed(
        &next,
        "theorem afterFile : read = 2 := by rfl\n#eval read\n",
    );
}

#[test]
fn scoped_noncomputable_instances_are_usable_only_when_activated() {
    let base = executed(&seed(), CLASS);
    let next = executed(
        &base,
        "instance fallback : Marker := Marker.mk 2\nnamespace N\nnoncomputable scoped instance chosen : Marker := Marker.mk 17\nend N\n#eval read\nsection\nopen scoped N\ntheorem selected : read = 17 := by rfl\nend\n#eval read\n",
    );
    assert_eq!(tags(&next), BTreeSet::from([n("N.chosen")]));
}

#[test]
fn proof_instances_are_checked_as_theorems_but_may_carry_the_noncomputable_modifier() {
    let base = checked(&seed(), "class Certified : Prop where\n  proof : True\n");
    let next = executed(
        &base,
        "noncomputable instance certified : Certified := Certified.mk True.intro\ntheorem usesProof : Certified := inferInstance\n",
    );
    assert!(matches!(
        next.environment().find(&n("certified")),
        Some(ConstantInfo::Thm(_))
    ));
    assert_eq!(tags(&next), BTreeSet::from([n("certified")]));
}

#[test]
fn noncomputable_opaques_keep_their_type_and_opaque_kernel_behavior() {
    let next = executed(
        &seed(),
        "namespace N\nnoncomputable opaque secret : Nat := 5\nnoncomputable opaque bare : Nat\nend N\ntheorem reflexive : N.secret = N.secret := by rfl\n",
    );
    assert_eq!(tags(&next), BTreeSet::from([n("N.secret"), n("N.bare")]));
    for name in ["N.secret", "N.bare"] {
        assert!(
            matches!(next.environment().find(&n(name)), Some(ConstantInfo::Opaque(value)) if !value.is_unsafe)
        );
        assert!(
            next.execute_source_commands_with_checks(
                format!("#eval {name}\n").as_bytes(),
                &KVMap::new(),
                EngineExecutionLimits::new(admission().kernel)
            )
            .is_err()
        );
    }
    assert!(
        next.check_source_files(
            &[b"theorem cannotUnfold : N.secret = 5 := by rfl\n"],
            &KVMap::new(),
            SourceCheckLimits::new(admission())
        )
        .is_err()
    );
}

#[test]
fn failed_noncomputable_declarations_publish_neither_constants_nor_tags() {
    let base = checked(&seed(), CLASS);
    let before = base.logical_root(&KVMap::new());
    for source in [
        "noncomputable instance bad : Marker := True\n",
        "noncomputable opaque bad : Nat := True\n",
        "noncomputable theorem bad : True := True.intro\n",
        "noncomputable axiom bad : Nat\n",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission())
            )
            .is_err(),
            "accepted {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(tags(&base).is_empty());
        assert!(!base.environment().contains(&n("bad")));
    }
}

#[test]
fn noncomputable_proofs_and_type_arguments_remain_erasable() {
    executed(
        &seed(),
        "noncomputable def logical : Nat := 5\ndef eraseProof (h : logical = logical) : Nat := 7\n#eval eraseProof rfl\nnoncomputable def Carrier : Type := Nat\ndef keep.{u} (A : Type u) (x : A) : A := x\n#eval keep Carrier (8 : Nat)\n",
    );
    let base = checked(&seed(), "class Certified : Prop where\n  proof : True\n");
    executed(
        &base,
        "noncomputable instance certified : Certified := Certified.mk True.intro\ndef eraseDictionary [Certified] : Nat := 3\n#eval eraseDictionary\n",
    );
}

fn module_checked(files: &[(&str, &str)]) -> Engine {
    use fln::source_check::modules::SourceModuleCheckLimits;
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| fln::SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    seed()
        .check_source_modules(
            &inputs,
            &n("Main"),
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
        )
        .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
        .into_complete()
        .expect("module council completes")
        .checked
        .engine
}

#[test]
fn private_instance_tags_use_the_actual_mangled_name() {
    let source = format!(
        "module\nprelude\n{CLASS}\nnoncomputable instance chosen : Marker := Marker.mk 31\ntheorem value : read = 31 := by rfl\n"
    );
    let result = module_checked(&[("Main", &source)]);
    let tagged = tags(&result);
    assert_eq!(tagged.len(), 1);
    for name in tagged {
        assert_ne!(name, n("chosen"));
        assert!(result.environment().contains(&name));
        assert!(name.to_display_string().contains("_private.Main"));
        assert!(
            fln_elab::instances::InstanceRegistry::read(result.environment())
                .unwrap()
                .is_instance(&name)
        );
    }
}

#[test]
fn public_instances_preserve_noncomputable_tags_through_module_replay() {
    let library = format!(
        "module\nprelude\n@[expose] public section\n{CLASS}\nnoncomputable instance chosen : Marker := Marker.mk 37\n"
    );
    let result = module_checked(&[
        (
            "Main",
            "prelude\nimport Library\ntheorem importedValue : read = 37 := by rfl\n",
        ),
        ("Library", &library),
    ]);
    assert_eq!(tags(&result), BTreeSet::from([n("chosen")]));
    assert!(
        result
            .execute_source_commands_with_checks(
                b"#eval read\n",
                &KVMap::new(),
                EngineExecutionLimits::new(admission().kernel)
            )
            .is_err()
    );
}

#[test]
fn public_proof_instances_publish_the_tag_once_in_each_world() {
    let result = module_checked(&[(
        "Main",
        "module\nprelude\npublic class Certified : Prop where\n  proof : True\npublic noncomputable instance certified : Certified := Certified.mk True.intro\npublic theorem use : Certified := inferInstance\n",
    )]);
    assert_eq!(tags(&result), BTreeSet::from([n("certified")]));
    let imported = module_checked(&[
        (
            "Main",
            "prelude\nimport Library\ntheorem use : Certified := inferInstance\n",
        ),
        (
            "Library",
            "module\nprelude\npublic class Certified : Prop where\n  proof : True\npublic noncomputable instance certified : Certified := Certified.mk True.intro\n",
        ),
    ]);
    assert_eq!(tags(&imported), BTreeSet::from([n("certified")]));
}

#[test]
fn noncomputable_definitions_may_use_recursors_that_have_no_default_codegen() {
    let base = executed(&seed(), "inductive Tree where | leaf | next (t : Tree)\n");
    for modifier in ["def", "abbrev"] {
        let source = format!(
            "noncomputable {modifier} depth (t : Tree) : Nat := Tree.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) t\ntheorem result : depth (Tree.next (Tree.next Tree.leaf)) = 2 := by rfl\n"
        );
        let next = executed(&base, &source);
        assert_eq!(tags(&next), BTreeSet::from([n("depth")]));
        assert!(
            next.execute_source_commands_with_checks(
                b"#eval depth Tree.leaf\n",
                &KVMap::new(),
                EngineExecutionLimits::new(admission().kernel)
            )
            .is_err()
        );
    }
    for declaration in ["def", "abbrev"] {
        let source = format!(
            "{declaration} depth (t : Tree) : Nat := Tree.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) t\n"
        );
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission()),
            )
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("code generator does not support recursor"),
            "{error}"
        );
    }
}

#[test]
fn noncomputable_instance_and_opaque_bodies_keep_kernel_checked_recursors() {
    let base = executed(
        &seed(),
        &format!("inductive Tree where | leaf | next (t : Tree)\n{CLASS}"),
    );
    let value = "Tree.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) (Tree.next Tree.leaf)";
    let instance = executed(
        &base,
        &format!(
            "noncomputable instance chosen : Marker := Marker.mk ({value})\ntheorem result : read = 1 := by rfl\n"
        ),
    );
    assert_eq!(tags(&instance), BTreeSet::from([n("chosen")]));
    let opaque = executed(
        &base,
        &format!(
            "noncomputable opaque hidden : Nat := {value}\ntheorem result : hidden = hidden := by rfl\n"
        ),
    );
    assert_eq!(tags(&opaque), BTreeSet::from([n("hidden")]));
    let invalid = "noncomputable def wrong (t : Tree) : Nat := Tree.rec (motive := fun _ => Nat) True (fun _ ih => ih) t\n";
    assert!(
        base.check_source_files(
            &[invalid.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission())
        )
        .is_err()
    );
    assert!(tags(&base).is_empty());
}

#[test]
fn a_noncomputable_record_cannot_be_unfolded_to_bypass_runtime_refusal() {
    let base = executed(&seed(), CLASS);
    let computable = executed(
        &base,
        "def dictionary : Marker := Marker.mk 43\n#eval dictionary.value\n",
    );
    assert!(tags(&computable).is_empty());
    let noncomputable = executed(
        &base,
        "noncomputable def dictionary : Marker := Marker.mk 43\n",
    );
    for source in [
        "#eval dictionary.value\n",
        "#eval (fun (ignored : Marker) => 0) dictionary\n",
    ] {
        assert!(
            noncomputable
                .execute_source_commands_with_checks(
                    source.as_bytes(),
                    &KVMap::new(),
                    EngineExecutionLimits::new(admission().kernel)
                )
                .is_err(),
            "noncomputable dependency disappeared: {source}"
        );
    }
    checked(
        &noncomputable,
        "theorem stillLogical : dictionary.value = 43 := by rfl\n",
    );
}
