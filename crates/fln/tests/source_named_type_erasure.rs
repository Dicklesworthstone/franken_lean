//! Named sorts and dependent telescopes are erased by their reduced types,
//! never by their spelling or merely because their types inhabit a universe.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    VmExit,
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}
fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both native checkers complete")
    .engine
}
fn eval(base: &Engine, source: &str) -> Vec<String> {
    base.execute_source_commands_with_checks(
        source.as_bytes(),
        &KVMap::new(),
        EngineExecutionLimits::new(limits().kernel),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("native execution completes")
    .batch
    .executions
    .iter()
    .map(|execution| {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("returned value")
        };
        fln_vm::interpreter::nat_decimal(&value.value).expect("returned Nat")
    })
    .collect()
}
fn no_tags(engine: &Engine) {
    assert!(
        fln_elab::noncomputable::read(engine.environment())
            .unwrap()
            .is_empty()
    );
}
fn refuse(base: &Engine, source: &str, dependency: &str) {
    let root = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err("a data dependency still needs executable code");
    assert!(error.to_string().contains("noncomputable"), "{error:?}");
    assert!(error.to_string().contains(dependency), "{error:?}");
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn named_sorts_and_type_families_do_not_acquire_executable_dependencies() {
    let source = include_str!("../../fln-parse/tests/fixtures/bodyless_codegen_types.lean");
    let next = check(&seed(), source);
    let tags = fln_elab::noncomputable::read(next.environment()).unwrap();
    assert_eq!(
        tags,
        std::collections::BTreeSet::from([n("hidden"), n("successor")])
    );
    assert_eq!(eval(&next, "#eval ordinary\n"), ["7"]);
    refuse(&next, "def leak : Nat := successor\n", "successor");
}

#[test]
fn dependent_polymorphic_type_formers_open_their_original_telescope() {
    let next = check(
        &seed(),
        "universe u\ndef U : Type (u + 1) := Type u\naxiom Family : (A : Type u) -> A -> U\ndef alias : (A : Type u) -> A -> U := Family\ndef keep (F : (A : Type u) -> A -> U) : Nat := 11\ndef answer : Nat := keep Family\n",
    );
    no_tags(&next);
    // Input and output universe parameters generalize independently.
    assert_eq!(eval(&next, "#eval answer.{0, 0}\n"), ["11"]);
}

#[test]
fn sort_aliases_reduce_after_dependent_binder_substitution() {
    let next = check(
        &seed(),
        "def U (_ : Nat) : Type 1 := Type\naxiom Family : (n : Nat) -> U n\ndef alias : (n : Nat) -> U n := Family\ndef consume (F : (n : Nat) -> U n) : Nat := 13\ndef answer : Nat := consume Family\n",
    );
    no_tags(&next);
    assert_eq!(eval(&next, "#eval answer\n"), ["13"]);
}

#[test]
fn local_let_sort_aliases_and_proof_sort_aliases_are_erased() {
    let next = check(
        &seed(),
        "def U : Type 1 := Type\ndef Logic : Type := Prop\naxiom Carrier : U\naxiom P : Logic\naxiom proof : P\ndef take (_ : P) : Nat := 17\ndef answer : Nat := let Local : Type 1 := Type; let ignore : Local -> Nat := fun _ => take proof; ignore Carrier\n",
    );
    no_tags(&next);
    assert_eq!(eval(&next, "#eval answer\n"), ["17"]);
}

#[test]
fn data_type_aliases_and_abstract_type_parameters_are_not_erased_values() {
    let base = check(
        &seed(),
        "def Number : Type := Nat\naxiom oracle : Number\naxiom choose : (A : Type) -> A\n",
    );
    refuse(&base, "def bad : Number := oracle\n", "oracle");
    refuse(&base, "def bad : (A : Type) -> A := choose\n", "choose");
    refuse(&base, "def bad (A : Type) : A := choose A\n", "choose");
    let recovered = check(&base, "def good (A : Type) (x : A) : A := x\n");
    assert_eq!(eval(&recovered, "#eval good Nat 19\n"), ["19"]);
}

#[test]
fn opaque_and_irreducible_sort_lookalikes_do_not_supply_erasure_authority() {
    for declaration in [
        "opaque U : Type 1 := Type",
        "@[irreducible] def U : Type 1 := Type",
    ] {
        let base = check(&seed(), &format!("{declaration}\naxiom oracle : U\n"));
        refuse(&base, "def bad : U := oracle\n", "oracle");
        let logical = check(&base, "noncomputable def logical : U := oracle\n");
        assert!(
            fln_elab::noncomputable::read(logical.environment())
                .unwrap()
                .contains(&n("logical"))
        );
    }
}

#[test]
fn named_type_erasure_is_bound_to_the_environment_not_the_declaration_spelling() {
    let erased = check(&seed(), "def U : Type 1 := Type\naxiom value : U\n");
    let data = check(&seed(), "def U : Type := Nat\naxiom value : U\n");
    for _ in 0..2 {
        no_tags(&check(&erased, "def alias : U := value\n"));
        refuse(&data, "def alias : U := value\n", "value");
    }
}

#[test]
fn proof_and_type_erasure_does_not_admit_an_invalid_proof() {
    let base = check(
        &seed(),
        "def U : Type 1 := Type\naxiom Carrier : U\naxiom secret : Nat\nnoncomputable def hidden : Nat := secret\ndef keep (_ : U) : Nat := 23\ndef answer : Nat := keep Carrier\n",
    );
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[b"theorem wrong : answer = 24 := by rfl\n"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    check(&base, "theorem correct : answer = 23 := by rfl\n");
    assert_eq!(eval(&base, "#eval answer\n"), ["23"]);
}

#[test]
fn named_sorts_survive_compiled_module_export_checked_import_and_execution() {
    use fln::source_check::modules::{SourceModuleCheckLimits, imported::SourceOleanImportLimits};
    use fln::{OleanCheckLimits, OleanModuleInput, OleanWriteBudget, SourceModuleInput};
    let base = Engine::builder().build_empty();
    let lib = n("TypeLibrary");
    let main = n("Consumer");
    let built = base.compile_source_modules(
        &[
            SourceModuleInput {
                name: &lib,
                source: b"prelude\ndef U : Type 1 := Type\naxiom Carrier : U\naxiom Family : U -> U\ninductive Bit where | off | on\ndef keep (_ : U) : Bit := Bit.on\n",
            },
            SourceModuleInput {
                name: &main,
                source: b"prelude\nimport TypeLibrary\ndef carrierAlias : U := Carrier\ndef familyAlias : U -> U := Family\ndef answer : Bit := keep Carrier\n",
            },
        ],
        &main,
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        OleanWriteBudget::default(),
    ).unwrap().into_complete().unwrap();
    no_tags(&built.checked.checked.engine);
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
    let imported = base
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&main),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(4 << 20, limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    no_tags(&imported);
    let next = check(
        &imported,
        "def secondAlias : U := carrierAlias\ndef secondFamily : U -> U := familyAlias\n",
    );
    no_tags(&next);
    let run = next
        .execute_source_commands_with_checks(
            b"#eval answer\n",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.batch.executions[0].exit else {
        panic!("returned constructor")
    };
    assert_eq!(
        fln::vm_value_kind(&value.value),
        fln_vm::interpreter::ValueKind::Ctor(1)
    );
}
