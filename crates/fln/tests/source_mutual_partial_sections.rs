//! Section capture closure for native mutually recursive partial definitions.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

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
        panic!("{answer:?}");
    };
    let VmExit::Returned(value) = &execution.exit else {
        panic!("{execution:?}");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

const CAPTURED: &str = r#"
section
variable (unused : String) (left right : Nat)
mutual
  partial def ping (n : Nat) : Nat := if n == 0 then left else pong (n - 1)
  partial def pong (n : Nat) : Nat := if n == 0 then right else ping (n - 1)
  partial def plain (n : Nat) : Nat := n + 1
end
end
"#;

#[test]
fn shared_captures_cover_peer_only_dependencies_and_preserve_public_arity() {
    let base = checked(&engine(), CAPTURED);
    run(&base, "#eval ping 7 13 5", "13");
    run(&base, "#eval pong 7 13 5", "7");
    // The pin closes every top-level member over the same used telescope,
    // before SCC partitioning; even the independent helper receives it.
    run(&base, "#eval plain 7 13 9", "10");
    checked(
        &base,
        "theorem plain_type : plain = (fun (left right n : Nat) => n + 1) := by rfl",
    );
}

#[test]
fn unrelated_section_variables_do_not_become_parameters() {
    let base = checked(
        &engine(),
        "section\nvariable (unused : Nat)\nmutual\npartial def first (n : Nat) : Nat := second n\npartial def second (n : Nat) : Nat := n + 2\nend\nend",
    );
    run(&base, "#eval first 19", "21");
    checked(
        &base,
        "theorem first_type : first = (fun (n : Nat) => n + 2) := by rfl",
    );
}

#[test]
fn dependent_section_telescope_and_fixed_universes_survive_peer_instantiation() {
    let base = checked(
        &engine(),
        r#"
universe u v
section
variable {α : Type u} {β : Type v} (a : α) (b : β)
mutual
  partial def first (n : Nat) : α := if n == 0 then a else second (n - 1) b
  partial def second (n : Nat) (unused : β) : α := first n
end
end
"#,
    );
    run(&base, "#eval first 43 true 5", "43");
    run(&base, "#eval second 47 false 4 true", "47");
}

#[test]
fn shadowed_binder_names_do_not_confuse_capture_identities() {
    let base = checked(
        &engine(),
        r#"
section
variable (value : Nat)
mutual
  partial def first (value n : Nat) : Nat := if n == 0 then value else second (n - 1)
  partial def second (n : Nat) : Nat := if n == 0 then value else first (value + 1) (n - 1)
end
end
"#,
    );
    run(&base, "#eval first 7 13 0", "13");
    run(&base, "#eval first 7 13 1", "7");
    run(&base, "#eval second 7 1", "8");
}

#[test]
fn higher_order_peer_references_close_over_captured_arguments() {
    let base = checked(
        &engine(),
        r#"
def apply (f : Nat → Nat) (n : Nat) : Nat := f n
section
variable (offset : Nat)
mutual
  partial def first (n : Nat) : Nat := if n == 0 then offset else apply second (n - 1)
  partial def second (n : Nat) : Nat := first n
end
end
"#,
    );
    run(&base, "#eval first 41 5", "41");
    run(&base, "#eval apply (second 43) 3", "43");
}

#[test]
fn captured_instances_remain_implicit_at_public_and_peer_calls() {
    let base = checked(
        &engine(),
        r#"
universe u
section
variable {α : Type u} [inst : Inhabited α]
mutual
  partial def first (n : Nat) : α := if n == 0 then default else second (n - 1)
  partial def second (n : Nat) : α := first n
end
end
def specialized : Nat → Nat := first
"#,
    );
    run(&base, "#eval specialized 4", "0");
    run(&base, "#eval (second 3 : Nat)", "0");
}

#[test]
fn recursive_capture_interfaces_remain_opaque_and_companions_private() {
    let base = checked(&engine(), CAPTURED);
    for source in [
        "theorem invalid : ping 7 13 0 = 7 := by rfl",
        "def leak : Nat := ping._unsafe_rec 7 13 0",
        "def bad_argument : Nat := ping true 13 0",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(EngineAdmissionLimits::new(budget())),
            )
            .is_err(),
            "{source}"
        );
    }
    run(&base, "#eval ping 7 13 4", "7");
}

#[test]
fn unused_proof_variables_cannot_invent_a_logical_inhabitant() {
    let base = engine();
    let before = base.environment().clone();
    let source = r#"
section
variable (h : False)
mutual
  partial def first (n : Nat) : False := second n
  partial def second (n : Nat) : False := first n
end
end
"#;
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(budget())),
        )
        .is_err()
    );
    assert_eq!(base.environment(), &before);
    run(&checked(&base, CAPTURED), "#eval pong 7 13 0", "13");
}
