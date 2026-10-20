//! Data axioms have logical meaning, not executable implementations. Exercise
//! the ordinary source, section and execution doors rather than a mock checker.
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
fn tags(base: &Engine) -> BTreeSet<Name> {
    fln_elab::noncomputable::read(base.environment()).unwrap()
}
fn refuse(base: &Engine, source: &str, dependency: &str) {
    let root = base.logical_root(&KVMap::new());
    let result = base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    let error = match result {
        Err(error) => error,
        Ok(_) => panic!("accepted an executable axiom dependency: {source}"),
    };
    let message = error.to_string();
    assert!(message.contains("noncomputable"), "{source}: {error:?}");
    assert!(message.contains(dependency), "{source}: {error:?}");
    assert_eq!(root, base.logical_root(&KVMap::new()));
}
fn value(base: &Engine, source: &str) -> Vec<String> {
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
                panic!("expected a return")
            };
            fln_vm::interpreter::nat_decimal(&result.value).unwrap()
        })
        .collect()
}

#[test]
fn untagged_data_axioms_are_not_executable_declarations() {
    let base = check(
        &seed(),
        "axiom oracle : Nat\nclass Marker where\n  value : Nat\n",
    );
    assert!(
        tags(&base).is_empty(),
        "an axiom need not carry a noncomputable tag"
    );
    for source in [
        "def alias : Nat := oracle\n",
        "abbrev alias : Nat := oracle\n",
        "opaque alias : Nat := oracle\n",
        "instance chosen : Marker := Marker.mk oracle\n",
        "def alias (x : Nat) : Nat := oracle + x\n",
        "def alias : Nat := let x := oracle; x\n",
    ] {
        refuse(&base, source, "oracle");
        assert!(!base.environment().contains(&n("alias")));
    }
    assert_eq!(
        value(&check(&base, "def alias : Nat := 7\n"), "#eval alias\n"),
        ["7"]
    );
}

#[test]
fn function_axioms_cannot_hide_in_higher_order_or_record_values() {
    let base = check(
        &seed(),
        "axiom oracle : Nat -> Nat\nstructure Box where\n  run : Nat -> Nat\n",
    );
    for source in [
        "def alias : Nat -> Nat := oracle\n",
        "def alias (x : Nat) : Nat := oracle x\n",
        "def alias : Box := Box.mk oracle\n",
        "def alias : Nat -> Nat := fun x => oracle x\n",
    ] {
        refuse(&base, source, "oracle");
    }
}

#[test]
fn sections_infer_and_propagate_axiom_compilation_effects_without_tagging_the_axiom() {
    let base = check(&seed(), "axiom oracle : Nat\n");
    let next = check(
        &base,
        "noncomputable section\ndef first : Nat := oracle\ndef second : Nat := first + 1\ndef clean : Nat := 17\nend\ntheorem same : first = oracle := by rfl\n",
    );
    assert_eq!(tags(&next), BTreeSet::from([n("first"), n("second")]));
    assert_eq!(value(&next, "#eval clean\n"), ["17"]);
    refuse(&next, "def outside : Nat := second\n", "second");
    assert!(
        next.execute_source_commands_with_checks(
            b"noncomputable section\n#eval first\nend\n",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .is_err()
    );
    assert_eq!(tags(&base), BTreeSet::new());
}

#[test]
fn explicit_noncomputability_preserves_logical_axiom_use() {
    let base = check(&seed(), "axiom oracle : Nat\n");
    let next = check(
        &base,
        "noncomputable def first : Nat := oracle\nnoncomputable opaque hidden : Nat := oracle\ntheorem same : first = oracle := by rfl\n",
    );
    assert_eq!(tags(&next), BTreeSet::from([n("first"), n("hidden")]));
    refuse(&next, "def bad : Nat := first\n", "first");
}

#[test]
fn proof_axioms_and_axioms_in_erased_proofs_or_types_remain_usable() {
    let base = check(
        &seed(),
        "axiom oracle : Nat\naxiom proof : True\naxiom Abstract : Type\ndef sink (_ : True) : Nat := 7\ndef identity (A : Type) (x : A) : A := x\n",
    );
    let next = check(
        &base,
        "def viaProof : Nat := sink proof\ndef proofOnly : Nat := sink ((fun (_ : Nat) => True.intro) oracle)\ndef withDomain (_ : oracle = oracle) : Nat := 9\ndef withLet : Nat := let h : True := proof; 10\ndef abstractIdentity (x : Abstract) : Abstract := identity Abstract x\ntheorem oracleRefl : oracle = oracle := by rfl\n",
    );
    assert!(tags(&next).is_empty());
    assert_eq!(
        value(
            &next,
            "#eval viaProof\n#eval proofOnly\n#eval withDomain (by rfl)\n#eval withLet\n"
        ),
        ["7", "7", "9", "10"]
    );
}

#[test]
fn implicit_axiom_dictionaries_are_executable_dependencies() {
    let base = check(
        &seed(),
        "class Marker where\n  value : Nat\naxiom chosen : Marker\nattribute [instance] chosen\ndef read [m : Marker] : Nat := @Marker.value m\n",
    );
    refuse(&base, "def selected : Nat := read\n", "chosen");
    let next = check(
        &base,
        "noncomputable section\ndef selected : Nat := read\ndef projected : Nat := chosen.value\nend\n",
    );
    assert_eq!(tags(&next), BTreeSet::from([n("selected"), n("projected")]));
}

#[test]
fn recursive_companions_inherit_axiom_failure_and_clean_siblings_do_not() {
    let base = check(&seed(), "axiom oracle : Nat\n");
    refuse(
        &base,
        "partial def countdown (x : Nat) : Nat := if x == 0 then oracle else countdown (x - 1)\n",
        "oracle",
    );
    let next = check(
        &base,
        "noncomputable section\npartial def countdown (x : Nat) : Nat := if x == 0 then oracle else countdown (x - 1)\ndef alias : Nat := countdown 0\ndef clean : Nat := 23\nend\n",
    );
    assert!(tags(&next).contains(&n("countdown._unsafe_rec")));
    assert!(tags(&next).contains(&n("alias")));
    assert!(!tags(&next).contains(&n("countdown")));
    assert!(!tags(&next).contains(&n("clean")));
    assert_eq!(value(&next, "#eval clean\n"), ["23"]);
}

#[test]
fn fresh_environments_do_not_share_executable_status_by_name() {
    let ordinary = check(&seed(), "def same : Nat := 11\n");
    let abstract_ = check(&seed(), "axiom same : Nat\n");
    for _ in 0..2 {
        assert_eq!(
            value(
                &check(&ordinary, "def alias : Nat := same\n"),
                "#eval alias\n"
            ),
            ["11"]
        );
        refuse(&abstract_, "def alias : Nat := same\n", "same");
    }
}

#[test]
fn imported_axioms_and_inferred_restrictions_survive_real_olean_roundtrips() {
    use fln::source_check::modules::{SourceModuleCheckLimits, imported::SourceOleanImportLimits};
    use fln::{OleanCheckLimits, OleanModuleInput, OleanWriteBudget, SourceModuleInput};
    let base = Engine::builder().build_empty();
    let lib = n("Lib");
    let main = n("Main");
    let built = base.compile_source_modules(
        &[
            SourceModuleInput {
                name: &lib,
                source: b"prelude\ninductive Flag where | off | on\naxiom oracle : Flag\naxiom choose : Flag -> Flag\n",
            },
            SourceModuleInput {
                name: &main,
                source: b"prelude\nimport Lib\nnoncomputable section\ndef alias : Flag := oracle\ndef mapped : Flag := choose alias\ndef clean : Flag := Flag.on\nend\n",
            },
        ],
        &main, &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        OleanWriteBudget::default(),
    ).unwrap().into_complete().unwrap();
    let inputs: Vec<_> = built
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    let import_limits =
        SourceOleanImportLimits::new(OleanCheckLimits::new(4 << 20, limits().kernel));
    let library = base
        .import_olean_modules_for_source(
            &inputs
                .iter()
                .filter(|input| input.name == &lib)
                .copied()
                .collect::<Vec<_>>(),
            std::slice::from_ref(&lib),
            &KVMap::new(),
            import_limits,
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    assert!(
        tags(&library).is_empty(),
        "the library exports axioms, not invented tags"
    );
    refuse(&library, "def leak : Flag := oracle\n", "oracle");
    refuse(&library, "def leak : Flag := choose Flag.on\n", "choose");
    let imported = base
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&main),
            &KVMap::new(),
            import_limits,
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    assert_eq!(tags(&imported), BTreeSet::from([n("alias"), n("mapped")]));
    assert_eq!(tags(&imported), tags(&built.checked.checked.engine));
    refuse(&imported, "def leak : Flag := mapped\n", "mapped");
    let result = imported
        .execute_source_commands_with_checks(
            b"#eval clean\n",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(returned) = &result.batch.executions[0].exit else {
        panic!("returned constructor")
    };
    assert_eq!(
        fln::vm_value_kind(&returned.value),
        fln_vm::interpreter::ValueKind::Ctor(1)
    );
}
