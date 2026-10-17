//! Section-inferred compiler failures follow the actual partial executable body.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
};
use std::collections::BTreeSet;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn seed() -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(base: &Engine, text: &str) -> Engine {
    base.check_source_files(
        &[text.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
    )
    .unwrap_or_else(|e| panic!("{text}\n{e:?}"))
    .into_complete()
    .unwrap()
    .engine
}
fn tags(engine: &Engine) -> BTreeSet<Name> {
    fln_elab::noncomputable::read(engine.environment()).unwrap()
}
fn rejects_alias(engine: &Engine, call: &str) {
    let before = engine.logical_root(&KVMap::new());
    let error = engine
        .check_source_files(
            &[format!("def leak : Nat := {call}\n").as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission()),
        )
        .unwrap_err();
    assert!(error.to_string().contains("noncomputable"), "{error:?}");
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&n("leak")));
}
const RECURSIVE: &str =
    "partial def recur (n : Nat) : Nat := if n == 0 then secret else recur (n - 1)\n";

#[test]
fn singleton_recursion_marks_its_companion_not_its_logical_interface() {
    let base = check(&seed(), "noncomputable def secret : Nat := 41\n");
    let next = check(&base, &format!("noncomputable section\n{RECURSIVE}end\n"));
    assert_eq!(
        tags(&next),
        BTreeSet::from([n("secret"), n("recur._unsafe_rec")])
    );
    rejects_alias(&next, "recur 0");
    let wrapped = check(
        &next,
        "noncomputable section\ndef wrapped : Nat := recur 0\nend\n",
    );
    assert!(tags(&wrapped).contains(&n("wrapped")));
    assert!(
        next.execute_source_commands_with_checks(
            b"#eval recur 0\n",
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel)
        )
        .is_err()
    );
}

#[test]
fn nonrecursive_partial_helper_keeps_its_real_definition_name() {
    let next = check(
        &seed(),
        "noncomputable def secret : Nat := 41\nnoncomputable section\npartial def alias (n : Nat) : Nat := secret + n\nend\ntheorem logical : alias 1 = 42 := by rfl\n",
    );
    assert_eq!(tags(&next), BTreeSet::from([n("secret"), n("alias")]));
    assert!(!next.environment().contains(&n("alias._unsafe_rec")));
    rejects_alias(&next, "alias 1");
}

#[test]
fn mutual_cycle_propagates_the_compiler_failure_to_both_companions() {
    let next = check(
        &seed(),
        "noncomputable def secret : Nat := 41\nnoncomputable section\nmutual\npartial def left (n : Nat) : Nat := if n == 0 then secret else right (n - 1)\npartial def right (n : Nat) : Nat := if n == 0 then 7 else left (n - 1)\nend\nend\n",
    );
    assert_eq!(
        tags(&next),
        BTreeSet::from([n("secret"), n("left._unsafe_rec"), n("right._unsafe_rec")])
    );
    rejects_alias(&next, "left 0");
    rejects_alias(&next, "right 0");
}

#[test]
fn acyclic_mutual_dependents_are_tagged_without_contaminating_clean_siblings() {
    let next = check(
        &seed(),
        "noncomputable def secret : Nat := 41\nnoncomputable section\nmutual\npartial def consumer (n : Nat) : Nat := provider n\npartial def provider (n : Nat) : Nat := secret + n\npartial def clean (n : Nat) : Nat := n + 1\nend\nend\ntheorem logical : consumer 1 = 42 := by rfl\n",
    );
    assert_eq!(
        tags(&next),
        BTreeSet::from([n("secret"), n("consumer"), n("provider")])
    );
    rejects_alias(&next, "consumer 1");
    assert!(
        next.execute_source_commands_with_checks(
            b"#eval clean 6\n",
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel)
        )
        .unwrap()
        .into_complete()
        .is_ok()
    );
}

#[test]
fn partial_tag_names_are_qualified_and_council_failure_publishes_nothing() {
    let base = check(&seed(), "noncomputable def secret : Nat := 41\n");
    let next = check(
        &base,
        "noncomputable section\nnamespace N\npartial def localName (n : Nat) : Nat := secret + n\nend N\nend\n",
    );
    assert_eq!(tags(&next), BTreeSet::from([n("secret"), n("N.localName")]));
    let before = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[
                format!("noncomputable section\n{RECURSIVE}def broken : Nat := true\nend\n")
                    .as_bytes()
            ],
            &KVMap::new(),
            SourceCheckLimits::new(admission())
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(!base.environment().contains(&n("recur")));
}

fn evaluate(engine: &Engine, source: &str) -> Vec<String> {
    engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .batch
        .executions
        .iter()
        .map(|execution| {
            let fln::VmExit::Returned(returned) = &execution.exit else {
                panic!("{execution:?}")
            };
            fln_vm::interpreter::nat_decimal(&returned.value).unwrap()
        })
        .collect()
}

#[test]
fn erased_peer_proofs_do_not_inherit_a_data_helpers_compilation_failure() {
    let next = check(
        &seed(),
        r#"
noncomputable def secret : Nat := 41
noncomputable section
mutual
partial def consumer (n : Nat) : Nat := let proof : True := (fun (_ : Nat) => True.intro) (provider n); n + 1
partial def provider (n : Nat) : Nat := secret + n
end
end
"#,
    );
    assert_eq!(tags(&next), BTreeSet::from([n("secret"), n("provider")]));
    assert_eq!(evaluate(&next, "#eval consumer 6\n"), ["7"]);
}

#[test]
fn polymorphic_peer_dependencies_use_their_original_universe_telescope() {
    let next = check(
        &seed(),
        r#"
noncomputable def secret {A : Type} (x : A) : A := x
noncomputable section
mutual
partial def consumer {A : Type} (x : A) : A := provider x
partial def provider {A : Type} (x : A) : A := secret x
end
end
theorem logical : consumer 42 = 42 := by rfl
"#,
    );
    assert_eq!(
        tags(&next),
        BTreeSet::from([n("secret"), n("provider"), n("consumer")])
    );
    rejects_alias(&next, "consumer 42");
}

#[test]
fn computable_recursion_in_a_noncomputable_section_is_still_executable() {
    let next = check(
        &seed(),
        r#"
noncomputable section
partial def count (n : Nat) : Nat := if n == 0 then 7 else count (n - 1)
end
"#,
    );
    assert!(tags(&next).is_empty());
    assert_eq!(evaluate(&next, "#eval count 3\n"), ["7"]);
}

#[test]
fn private_partial_companion_tags_bind_to_the_actual_checked_module_names() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    let name = n("Main");
    let result = seed().check_source_modules(&[fln::SourceModuleInput {
        name: &name,
        source: format!("module\nprelude\nnoncomputable def secret : Nat := 41\nnoncomputable section\n{RECURSIVE}end\n").as_bytes(),
    }], &name, &KVMap::new(), SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())))
        .unwrap().into_complete().unwrap().checked.engine;
    let names = tags(&result);
    assert_eq!(names.len(), 2);
    for name in &names {
        assert!(result.environment().contains(name));
        assert!(
            name.to_display_string().starts_with("_private.Main."),
            "{name:?}"
        );
    }
    assert_eq!(
        names
            .iter()
            .filter(|name| matches!(
                name.leaf_view(),
                fln_core::name::LeafView::Str("_unsafe_rec")
            ))
            .count(),
        1
    );
    assert!(!result.environment().contains(&n("recur")));
}

#[test]
fn captured_mutual_parameters_keep_tags_on_closed_executable_units() {
    let next = check(
        &seed(),
        include_str!("../../fln-parse/tests/fixtures/noncomputable_captured_partial.lean"),
    );
    assert_eq!(
        tags(&next),
        BTreeSet::from([
            n("secret"),
            n("left._unsafe_rec"),
            n("right._unsafe_rec"),
            n("consumer"),
        ])
    );
    rejects_alias(&next, "consumer 3 0");
    assert_eq!(evaluate(&next, "#eval clean 6 7\n"), ["13"]);
    let root = next.logical_root(&KVMap::new());
    assert!(
        next.execute_source_commands_with_checks(
            b"#eval right 3 0\n",
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .is_err()
    );
    assert_eq!(next.logical_root(&KVMap::new()), root);
}

#[test]
fn captured_polymorphic_peer_failures_retain_original_universe_parameters() {
    let next = check(
        &seed(),
        include_str!("../../fln-parse/tests/fixtures/noncomputable_polymorphic_partial.lean"),
    );
    assert_eq!(
        tags(&next),
        BTreeSet::from([n("secret"), n("provider"), n("consumer")])
    );
    rejects_alias(&next, "consumer 43 0");
    assert_eq!(evaluate(&next, "#eval clean 43 0\n"), ["43"]);
}
