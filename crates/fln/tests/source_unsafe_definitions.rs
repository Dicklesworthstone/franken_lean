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
