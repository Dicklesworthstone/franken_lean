//! Unsafe SCCs have checked executable bodies, never safe logical witnesses.
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
    let answer = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let [execution] = answer.executions.as_slice() else {
        panic!("{answer:?}")
    };
    let VmExit::Returned(value) = &execution.exit else {
        panic!("{execution:?}")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}
fn refuses(base: &Engine, source: &str) {
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
}
const CYCLE: &str = "mutual\nunsafe def ping (n : Nat) : Nat := if n == 0 then 7 else pong (n - 1)\nunsafe def pong (n : Nat) : Nat := if n == 0 then 13 else ping (n - 1)\nend\n";

#[test]
fn recursive_unsafe_components_keep_original_names_and_execute_both_members() {
    let base = checked(&engine(), CYCLE);
    for text in ["ping", "pong"] {
        let name = Name::from_components([text]);
        assert!(
            matches!(base.environment().find(&name), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Unsafe && value.all == vec![Name::from_components(["ping"]), Name::from_components(["pong"])])
        );
        assert!(!base.environment().contains(&Name::str(name, "_unsafe_rec")));
    }
    run(&base, "#eval ping 5", "13");
    run(&base, "#eval pong 5", "7");
    run(&engine(), &format!("{CYCLE}#eval ping 4"), "7");
}

#[test]
fn dependency_partition_never_promotes_acyclic_unsafe_definitions_to_safe() {
    let source = "mutual\nunsafe def start (n : Nat) : Nat := left n\nunsafe def left (n : Nat) : Nat := if n == 0 then seed else right (n - 1)\nunsafe def right (n : Nat) : Nat := if n == 0 then seed + 1 else left (n - 1)\nunsafe def seed : Nat := 41\nend";
    let base = checked(&engine(), source);
    for text in ["start", "left", "right", "seed"] {
        let name = Name::from_components([text]);
        assert!(
            matches!(base.environment().find(&name), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Unsafe)
        );
        assert!(!base.environment().contains(&Name::str(name, "_unsafe_rec")));
    }
    run(&base, "#eval start 3", "42");
    refuses(&base, "def leak : Nat := seed");
    refuses(&base, "theorem leak : seed = seed := by rfl");
}

#[test]
fn unsafe_groups_do_not_require_inhabitants_but_cannot_prove_false_safely() {
    let base = checked(
        &engine(),
        "mutual\nunsafe def first : False := second\nunsafe def second : False := first\nend",
    );
    refuses(&base, "theorem leak : False := first");
    refuses(&base, "def leak : False := second");
    assert!(
        matches!(base.environment().find(&Name::from_components(["first"])), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Unsafe)
    );
    // A subsequent safe request still has its original authority rules.
    checked(&base, "theorem valid : True := by constructor");
}

#[test]
fn unsafe_mutual_sections_preserve_dependent_captures_and_peer_universes() {
    let base = checked(
        &engine(),
        r#"
universe u v
section
variable {A : Type u} {B : Type v} (a : A) (b : B) (unused : String)
mutual
  unsafe def first (n : Nat) : A := if n == 0 then a else second (n - 1) b
  unsafe def second (n : Nat) (unused : B) : A := first n
end
end
"#,
    );
    run(&base, "#eval first 43 true 5", "43");
    run(&base, "#eval second 47 false 4 true", "47");
}

#[test]
fn unsafe_group_binders_shadow_peers_and_namespaces_keep_distinct_arities() {
    let base = checked(
        &engine(),
        "mutual\nunsafe def first (second : Nat) : Nat := second\nunsafe def second : Nat := first 23\nend",
    );
    run(&base, "#eval second", "23");
    let base = checked(
        &base,
        "namespace N\nmutual\nunsafe def a (n : Nat) : Nat := if n == 0 then 17 else b (n - 1) 5\nunsafe def b (n extra : Nat) : Nat := if n == 0 then extra else c (n - 1)\nunsafe def c : Nat -> Nat := fun n => if n == 0 then 29 else a (n - 1)\nend\nend N",
    );
    run(&base, "#eval N.a 1", "5");
    run(&base, "#eval N.a 2", "29");
    run(&base, "#eval N.a 3", "17");
}

#[test]
fn mixed_safety_bad_late_bodies_and_duplicate_names_publish_no_group_prefix() {
    let base = engine();
    for source in [
        "mutual\nunsafe def ping (n : Nat) : Nat := pong n\nunsafe def pong (n : Nat) : Nat := true\nend",
        "mutual\nunsafe def ping (n : Nat) : Nat := pong n\ndef pong (n : Nat) : Nat := ping n\nend",
        "mutual\nunsafe def ping (n : Nat) : Nat := pong n\npartial def pong (n : Nat) : Nat := ping n\nend",
        "mutual\nunsafe def ping (n : Nat) : Nat := ping n\nunsafe def ping (n : Nat) : Nat := n\nend",
        "mutual\nunsafe partial def ping (n : Nat) : Nat := ping n\nend",
        "mutual\nunsafe def ping (n : Nat) : Nat := unknown n\nend",
        "mutual\nunsafe def ping (n : Nat) : Nat := n\nunsafe theorem wrong : True := by constructor\nend",
    ] {
        refuses(&base, source);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["ping"]))
        );
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["pong"]))
        );
    }
    run(&engine(), &format!("{CYCLE}#eval pong 2"), "13");
}

#[test]
fn unsafe_mutual_nontermination_is_a_resource_stop_not_a_proof_or_host_recursion() {
    let base = checked(
        &engine(),
        "mutual\nunsafe def a (n : Nat) : Nat := b n\nunsafe def b (n : Nat) : Nat := a n\nend",
    );
    let mut limits = EngineExecutionLimits::new(budget());
    limits.vm.max_steps = 1000;
    assert!(matches!(
        base.execute_source_definitions(&[b"#eval a 0"], &KVMap::new(), limits)
            .unwrap(),
        fln_core::outcome::Outcome::Inconclusive(_)
    ));
    run(&base, "#eval 42", "42");
}
