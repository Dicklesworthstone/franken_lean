//! Bodyless data dependencies must not acquire executable code by being untagged.
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
fn refuse(base: &Engine, source: &str) {
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err("a bodyless data dependency is not executable");
    assert!(error.to_string().contains("noncomputable"), "{error:?}");
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(!base.environment().contains(&n("answer")));
}
fn eval(base: &Engine, source: &str) -> Vec<String> {
    base.execute_source_commands_with_checks(
        source.as_bytes(),
        &KVMap::new(),
        EngineExecutionLimits::new(limits().kernel),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .batch
    .executions
    .iter()
    .map(|execution| {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("returned value")
        };
        fln_vm::interpreter::nat_decimal(&value.value).unwrap()
    })
    .collect()
}

#[test]
fn untagged_data_axioms_refuse_in_every_compiled_declaration_form() {
    let base = check(
        &seed(),
        "axiom secret : Nat\nclass Boxed where\n  value : Nat\n",
    );
    assert!(
        fln_elab::noncomputable::read(base.environment())
            .unwrap()
            .is_empty()
    );
    for source in [
        "def answer : Nat := secret\n",
        "abbrev answer : Nat := secret\n",
        "opaque answer : Nat := secret\n",
        "instance answer : Boxed := Boxed.mk secret\n",
        "def answer (x : Nat) : Nat := secret + x\n",
        "def answer : Nat := let value := secret; value\n",
        "def answer : Nat := (Boxed.mk secret).value\n",
    ] {
        refuse(&base, source);
    }
    let recovered = check(&base, "def answer : Nat := 7\n");
    assert_eq!(eval(&recovered, "#eval answer\n"), ["7"]);
}

#[test]
fn sections_tag_actual_axiom_dependents_without_tagging_the_axiom_or_clean_siblings() {
    let base = check(&seed(), "axiom secret : Nat\n");
    let next = check(
        &base,
        "noncomputable section\ndef answer : Nat := secret\ndef successor : Nat := answer + 1\ndef ordinary : Nat := 7\ntheorem identity : answer = secret := by rfl\nend\n",
    );
    assert_eq!(
        fln_elab::noncomputable::read(next.environment()).unwrap(),
        BTreeSet::from([n("answer"), n("successor")])
    );
    assert_eq!(eval(&next, "#eval ordinary\n"), ["7"]);
    assert!(
        next.execute_source_commands_with_checks(
            b"#eval successor\n",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel)
        )
        .is_err()
    );
    refuse(
        &base,
        "noncomputable section\ndef inside : Nat := secret\nend\ndef answer : Nat := secret\n",
    );
}

#[test]
fn proofs_types_and_dependent_binder_domains_do_not_require_axiom_code() {
    let base = check(
        &seed(),
        "axiom Carrier : Type\naxiom element : Carrier\naxiom predicate : Nat -> Prop\naxiom evidence : predicate 7\n",
    );
    let next = check(
        &base,
        "def identity (x : Carrier) : Carrier := x\ndef universeAlias : Type := Carrier\ndef proofAlias : predicate 7 := evidence\ndef ignoreProof (h : predicate 7) : Nat := 9\ndef answer : Nat := ignoreProof evidence\ndef dependent (x : Nat) (h : predicate x) : Nat := x\n",
    );
    assert!(
        fln_elab::noncomputable::read(next.environment())
            .unwrap()
            .is_empty()
    );
    assert_eq!(eval(&next, "#eval answer\n"), ["9"]);
    refuse(&base, "def answer : Carrier := element\n");
}

#[test]
fn explicit_noncomputable_values_remain_logical_and_proof_use_is_checked() {
    let base = check(
        &seed(),
        "axiom secret : Nat\nnoncomputable def answer : Nat := secret\ntheorem identity : answer = secret := by rfl\n",
    );
    assert!(
        fln_elab::noncomputable::read(base.environment())
            .unwrap()
            .contains(&n("answer"))
    );
    assert!(
        base.check_source_files(
            &[b"theorem wrong : answer = 0 := by rfl\n"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
    assert!(
        base.execute_source_commands_with_checks(
            b"#eval answer\n",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel)
        )
        .is_err()
    );
}

#[test]
fn partial_compilation_groups_propagate_bodyless_dependencies() {
    let base = check(&seed(), "axiom secret : Nat\n");
    refuse(
        &base,
        "partial def answer (n : Nat) : Nat := if n == 0 then secret else answer (n - 1)\n",
    );
    let next = check(
        &base,
        "noncomputable section\npartial def answer (n : Nat) : Nat := if n == 0 then secret else answer (n - 1)\ndef consumer : Nat := answer 2\ndef ordinary : Nat := 11\nend\n",
    );
    let tags = fln_elab::noncomputable::read(next.environment()).unwrap();
    assert!(tags.contains(&n("answer._unsafe_rec")));
    assert!(!tags.contains(&n("answer")));
    assert!(tags.contains(&n("consumer")));
    assert!(!tags.contains(&n("ordinary")));
    assert_eq!(eval(&next, "#eval ordinary\n"), ["11"]);
}
