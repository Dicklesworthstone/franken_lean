//! Executable noncomputable references are checked before any source declaration publishes.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    VmExit,
};
use std::collections::BTreeSet;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn tags(engine: &Engine) -> BTreeSet<Name> {
    fln_elab::noncomputable::read(engine.environment()).unwrap()
}
fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
}
fn refuse(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert!(error.to_string().contains("noncomputable"), "{error:?}");
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
fn evaluate(base: &Engine, source: &str) -> Vec<String> {
    let result = base
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    result
        .batch
        .executions
        .iter()
        .map(|execution| {
            let VmExit::Returned(result) = &execution.exit else {
                panic!("returned value")
            };
            fln_vm::interpreter::nat_decimal(&result.value).unwrap()
        })
        .collect()
}

#[test]
fn inferred_noncomputability_propagates_through_section_definitions() {
    let base = check(&seed(), "noncomputable def secret : Nat := 41\n");
    let next = check(
        &base,
        "noncomputable section\ndef alias : Nat := secret\ndef successor : Nat := alias + 1\ntheorem computed : successor = 42 := by rfl\nend\n",
    );
    assert_eq!(
        tags(&next),
        BTreeSet::from([n("secret"), n("alias"), n("successor")])
    );
    refuse(&next, "def outside : Nat := successor\n");
    let root = next.logical_root(&KVMap::new());
    assert!(
        next.execute_source_commands_with_checks(
            b"noncomputable section\n#eval successor\nend\n",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel)
        )
        .is_err()
    );
    assert_eq!(next.logical_root(&KVMap::new()), root);
}

#[test]
fn check_only_declarations_cannot_publish_executable_noncomputable_dependencies() {
    let base = check(
        &seed(),
        "class Marker where\n  value : Nat\nnoncomputable def secret : Nat := 41\n",
    );
    for source in [
        "def alias : Nat := secret\n",
        "abbrev alias : Nat := secret\n",
        "opaque alias : Nat := secret\n",
        "instance chosen : Marker := Marker.mk secret\n",
        "def alias (x : Nat) : Nat := secret + x\n",
        "def alias : Nat := let x := secret; x\n",
    ] {
        refuse(&base, source);
    }
    let next = check(
        &base,
        "noncomputable def allowed : Nat := secret\ntheorem computed : allowed = 41 := by rfl\n",
    );
    assert_eq!(tags(&next), BTreeSet::from([n("secret"), n("allowed")]));
}

#[test]
fn erased_proofs_types_and_dependent_binder_domains_do_not_propagate_tags() {
    let base = check(
        &seed(),
        "noncomputable def secret : Nat := 41\nnoncomputable def hiddenType : Type := Nat\ndef sink (_ : True) : Nat := 7\ndef idType (A : Type) (x : A) : A := x\n",
    );
    let next = check(
        &base,
        "def proofOnly : Nat := sink ((fun (_ : Nat) => True.intro) secret)\ndef typeOnly : Nat := idType hiddenType (8 : Nat)\ndef withProof (h : secret = 41) : Nat := 9\ndef withLet : Nat := let h : secret = 41 := (by rfl); 10\n",
    );
    assert_eq!(tags(&next), tags(&base));
    assert_eq!(
        evaluate(
            &next,
            "#eval proofOnly\n#eval typeOnly\n#eval withProof (by rfl)\n#eval withLet\n"
        ),
        ["7", "8", "9", "10"]
    );
}

#[test]
fn implicit_dictionaries_and_record_projections_are_executable_dependencies() {
    let base = check(
        &seed(),
        "class Marker where\n  value : Nat\nnoncomputable instance chosen : Marker := Marker.mk 23\ndef read [m : Marker] : Nat := @Marker.value m\n",
    );
    refuse(&base, "def bad : Nat := read\n");
    refuse(&base, "def bad : Nat := chosen.value\n");
    let next = check(
        &base,
        "noncomputable section\ndef selected : Nat := read\ndef projected : Nat := chosen.value\nend\ntheorem correct : selected + projected = 46 := by rfl\n",
    );
    assert_eq!(
        tags(&next),
        BTreeSet::from([n("chosen"), n("selected"), n("projected")])
    );
}

#[test]
fn private_declarations_are_tagged_by_actual_identity_and_not_exported() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    let name = n("Main");
    let input = fln::SourceModuleInput { name: &name, source: b"module\nprelude\nnoncomputable def secret : Nat := 41\nnoncomputable section\ndef hidden : Nat := secret\nend\ntheorem computed : hidden = 41 := by rfl\n" };
    let result = seed()
        .check_source_modules(
            &[input],
            &name,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .checked
        .engine;
    let tags = tags(&result);
    assert_eq!(tags.len(), 2);
    for name in tags {
        assert!(result.environment().contains(&name));
        assert!(name.to_display_string().starts_with("_private.Main."));
    }
    assert!(!result.environment().contains(&n("hidden")));
}

#[test]
fn public_dependency_tags_survive_module_replay_without_changing_proof_use() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    let main_name = n("Main");
    let lib_name = n("Library");
    let inputs = [
        fln::SourceModuleInput { name: &lib_name, source: b"module\nprelude\n@[expose] public noncomputable section\nnoncomputable def secret : Nat := 41\ndef exposed : Nat := secret\nend\n" },
        fln::SourceModuleInput { name: &main_name, source: b"prelude\nimport Library\ntheorem computed : exposed = 41 := by rfl\n" },
    ];
    let result = seed()
        .check_source_modules(
            &inputs,
            &main_name,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .checked
        .engine;
    assert_eq!(tags(&result), BTreeSet::from([n("secret"), n("exposed")]));
    refuse(&result, "def bad : Nat := exposed\n");
}

#[test]
fn fresh_requests_do_not_reuse_another_environments_dependency_classification() {
    let plain = check(&seed(), "def value : Nat := 11\n");
    let hidden = check(&seed(), "noncomputable def value : Nat := 13\n");
    for _ in 0..2 {
        let next = check(&plain, "def alias : Nat := value\n");
        assert!(tags(&next).is_empty());
        assert_eq!(evaluate(&next, "#eval alias\n"), ["11"]);
        refuse(&hidden, "def alias : Nat := value\n");
        assert_eq!(tags(&hidden), BTreeSet::from([n("value")]));
    }
}

#[test]
fn partial_batches_never_drop_a_suppressed_compilation_failure() {
    let base = check(&seed(), "noncomputable def secret : Nat := 41\n");
    for body in [
        "partial def bad (n : Nat) : Nat := if n == 0 then secret else bad (n - 1)\n",
        "mutual\npartial def bad (n : Nat) : Nat := if n == 0 then secret else peer (n - 1)\npartial def peer (n : Nat) : Nat := bad n\nend\n",
    ] {
        refuse(&base, body);
        // The section admits checked logical interfaces, but preserves the
        // failure on every executable member of the recursive component.
        let next = check(&base, &format!("noncomputable section\n{body}end\n"));
        for name in ["bad", "peer"] {
            if !next.environment().contains(&n(name)) {
                continue;
            }
            assert!(!tags(&next).contains(&n(name)));
            assert!(tags(&next).contains(&Name::str(n(name), "_unsafe_rec")));
            refuse(&next, &format!("def leak : Nat := {name} 0\n"));
            let before = next.environment().clone();
            let error = next
                .execute_source_commands_with_checks(
                    format!("#eval {name} 0\n").as_bytes(),
                    &KVMap::new(),
                    EngineExecutionLimits::new(limits().kernel),
                )
                .unwrap_err();
            assert!(format!("{error:?}").contains("Noncomputable"), "{error:?}");
            assert_eq!(next.environment(), &before);
        }
    }
    assert_eq!(tags(&base), BTreeSet::from([n("secret")]));
    assert_eq!(evaluate(&base, "#eval 7\n"), ["7"]);
}
