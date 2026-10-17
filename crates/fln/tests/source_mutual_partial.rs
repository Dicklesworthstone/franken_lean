//! Mutual partial definitions cross one ordinary, atomic two-checker batch.
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
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
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
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
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
        Some(expected)
    );
}
const CYCLE: &str = include_str!("../../fln-parse/tests/fixtures/partial_definitions/Mutual.lean");
fn refuses(base: &Engine, source: &str) {
    let before = base.environment().clone();
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(budget()))
        )
        .is_err(),
        "{source}"
    );
    assert_eq!(base.environment(), &before);
}
#[test]
fn mutually_recursive_bodies_execute_instead_of_logical_witnesses() {
    let base = checked(&engine(), CYCLE);
    for text in ["ping", "pong"] {
        let name = Name::from_components([text]);
        assert!(
            matches!(base.environment().find(&name), Some(ConstantInfo::Opaque(value)) if !value.is_unsafe)
        );
        assert!(
            matches!(base.environment().find(&Name::str(name, "_unsafe_rec")), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Partial && value.all.len() == 2)
        );
    }
    run(&base, "#eval ping 5", "13");
    run(&base, "#eval pong 5", "7");
    run(&engine(), &format!("{CYCLE}\n#eval ping 4"), "7");
}
#[test]
fn dependency_components_preserve_nonrecursive_reduction_and_forward_references() {
    let source = r#"
mutual
  partial def start (n : Nat) : Nat := left n
  partial def left (n : Nat) : Nat := if n == 0 then seed else right (n - 1)
  partial def right (n : Nat) : Nat := if n == 0 then seed + 1 else left (n - 1)
  partial def seed : Nat := 41
end
theorem seed_eq : seed = 41 := by rfl
"#;
    let base = checked(&engine(), source);
    for name in ["start", "seed"] {
        assert!(
            matches!(base.environment().find(&Name::from_components([name])), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Safe)
        );
        assert!(
            !base
                .environment()
                .contains(&Name::from_components([name, "_unsafe_rec"]))
        );
    }
    run(&base, "#eval start 3", "42");
}
#[test]
fn three_member_cycle_preserves_distinct_arities_and_namespaces() {
    let source = r#"
namespace N
mutual
  partial def a (n : Nat) : Nat := if n == 0 then 17 else b (n - 1) 5
  partial def b (n extra : Nat) : Nat := if n == 0 then extra else c (n - 1)
  partial def c : Nat → Nat := fun n => if n == 0 then 29 else a (n - 1)
end
end N
"#;
    let base = checked(&engine(), source);
    run(&base, "#eval N.a 1", "5");
    run(&base, "#eval N.a 2", "29");
    run(&base, "#eval N.a 3", "17");
}
#[test]
fn mutual_polymorphic_headers_instantiate_peer_universes_independently() {
    let source = r#"
mutual
  partial def first {α : Type} (x : α) (n : Nat) : α := if n == 0 then x else second x (n - 1)
  partial def second {α : Type} (x : α) (n : Nat) : α := if n == 0 then x else first x (n - 1)
end
"#;
    run(&engine(), &format!("{source}\n#eval first 42 4"), "42");
}
#[test]
fn mutual_logical_interfaces_stay_opaque_and_companions_cannot_escape() {
    let base = checked(&engine(), CYCLE);
    for source in [
        "theorem bad : ping 0 = 7 := by rfl",
        "def leak : Nat := ping._unsafe_rec 0",
        "theorem other : pong 0 = 13 := by rfl",
    ] {
        refuses(&base, source);
    }
    run(&base, "#eval pong 1", "7");
}
#[test]
fn malformed_late_member_or_missing_inhabitant_rolls_back_the_whole_group() {
    let base = engine();
    for source in [
        "mutual\npartial def ping (n : Nat) : Nat := pong n\npartial def pong (n : Nat) : Nat := true\nend",
        "mutual\npartial def ping (n : Nat) : False := pong n\npartial def pong (n : Nat) : False := ping n\nend",
        "mutual\npartial def ping (n : Nat) : Nat := pong n\npartial def pong (n : Nat) : Nat := ping n\nend\ntheorem invalid : 1 = 2 := by rfl",
        "mutual\npartial def ping (n : Nat) : Nat := ping n\npartial def ping (n : Nat) : Nat := n\nend",
        "mutual\npartial def ping (n : Nat) : Nat := pong n\ndef pong (n : Nat) : Nat := ping n\nend",
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
                .contains(&Name::from_components(["ping", "_unsafe_rec"]))
        );
    }
    checked(&base, CYCLE);
}
#[test]
fn lexical_binders_shadow_peers_without_creating_false_cycles() {
    let source = r#"
mutual
  partial def first (second : Nat) : Nat := second
  partial def second : Nat := first 23
end
theorem second_eq : second = 23 := by rfl
"#;
    let base = checked(&engine(), source);
    run(&base, "#eval second", "23");
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["first", "_unsafe_rec"]))
    );
}
#[test]
fn recursive_group_nontermination_retains_the_existing_vm_limit() {
    let base = checked(
        &engine(),
        "mutual\npartial def a (n : Nat) : Nat := b n\npartial def b (n : Nat) : Nat := a n\nend",
    );
    let mut limits = EngineExecutionLimits::new(budget());
    limits.vm.max_steps = 1000;
    assert!(matches!(
        base.execute_source_definitions(&[b"#eval a 0"], &KVMap::new(), limits)
            .unwrap(),
        fln_core::outcome::Outcome::Inconclusive(_)
    ));
}

#[test]
fn mutually_recursive_peers_keep_distinct_polymorphic_universe_parameters() {
    let source = r#"
universe u v
mutual
  partial def first {α : Type u} {β : Type v} (a : α) (b : β) (n : Nat) : α :=
    if n == 0 then a else second b a (n - 1)
  partial def second {β : Type v} {α : Type u} (b : β) (a : α) (n : Nat) : α :=
    if n == 0 then a else first a b (n - 1)
end
"#;
    let base = checked(&engine(), source);
    run(&base, "#eval first 43 true 5", "43");
}

#[test]
fn companion_collisions_refuse_and_unused_section_variables_preserve_arity() {
    let base = checked(&engine(), "def pong._unsafe_rec (n : Nat) : Nat := n");
    refuses(&base, CYCLE);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["ping"]))
    );
    run(&base, "#eval pong._unsafe_rec 19", "19");
    // An unused section variable is not an extra public argument. The
    // group's ordinary arity and its recursive execution are preserved.
    let captured = checked(
        &engine(),
        &format!("section\nvariable (offset : Nat)\n{CYCLE}end"),
    );
    run(&captured, "#eval ping 5", "13");
    refuses(&captured, "theorem invalid : ping 0 = 7 := by rfl");
}

#[test]
fn mutual_companions_cannot_launder_noncomputable_dependencies() {
    let base = engine();
    let source = r#"
noncomputable def hiddenValue (n : Nat) : Nat := n + 23
mutual
  partial def first (n : Nat) : Nat := if n == 0 then hiddenValue n else second (n - 1)
  partial def second (n : Nat) : Nat := first n
end
"#;
    // Executable dependencies now fail at source compilation, not only #eval.
    // A noncomputable section permits the logical declarations but never
    // grants their companions permission to run.
    refuses(&base, source);
    let admitted = checked(&base, &format!("noncomputable section\n{source}\nend\n"));
    for name in ["first", "second"] {
        let request = format!("#eval {name} 2");
        assert!(
            admitted
                .execute_source_definitions(
                    &[request.as_bytes()],
                    &KVMap::new(),
                    EngineExecutionLimits::new(budget()),
                )
                .is_err(),
            "neither executable companion may erase a noncomputable dependency"
        );
        assert!(!base.environment().contains(&Name::from_components([name])));
    }
    let recovered = checked(&base, CYCLE);
    run(&recovered, "#eval ping 5", "13");
}
