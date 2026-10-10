//! Literal callbacks forwarded to an unknown runtime consumer retain their type.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, FlbcExecutionLimits, KVMap,
    Outcome, VmExit, execute_flbc_artifact,
};

fn returned(exit: &VmExit, expected: &str) -> u64 {
    let VmExit::Returned(result) = exit else {
        panic!("the checked callback program must return natively");
    };
    assert_eq!(fln::nat_decimal(&result.value).as_deref(), Some(expected));
    result.usage.steps
}

#[test]
fn flat_callbacks_forwarded_to_runtime_consumers_execute_and_replay() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for (source, expected) in [
        (
            "def forward (g : (Nat -> Nat) -> Nat) : Nat := (fun (f : Nat -> Nat) => g f) (fun x => x + 1)\n#eval forward (fun f => f 41)",
            "42",
        ),
        (
            "def forwardCaptured (offset : Nat) (g : (Nat -> Nat) -> Nat) : Nat := (fun (f : Nat -> Nat) => g f) (fun x => x + offset)\n#eval forwardCaptured 32 (fun f => f 10)",
            "42",
        ),
        (
            "def forwardString (pfx : String) (g : (String -> String) -> Nat) : Nat := (fun (f : String -> String) => g f) (fun s => pfx ++ s)\n#eval forwardString \"hello\" (fun f => String.length (f \"world\"))",
            "10",
        ),
    ] {
        let run = base
            .execute_source_definitions(&[source.as_bytes()], &options, limits)
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
        let execution = run.executions.last().unwrap();
        returned(&execution.exit, expected);
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        returned(&replay, expected);
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn forwarding_a_computed_callback_preserves_its_strict_initializer() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = |cost| {
        format!(
            "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\ndef forwardComputed (g : (Nat -> Nat) -> Nat) (cost : Nat) : Nat := (fun (f : Nat -> Nat) => g f) (let paid : Nat := spend cost; fun x => x + paid)\n#eval forwardComputed (fun f => 42) {cost}"
        )
    };
    let execute = |cost| {
        let run = base
            .execute_source_definitions(&[source(cost).as_bytes()], &options, limits)
            .unwrap()
            .into_complete()
            .unwrap();
        returned(&run.executions.last().unwrap().exit, "42")
    };
    let idle = execute(0);
    let busy = execute(30);
    assert!(
        busy > idle + 30,
        "strict callback work disappeared: {idle} vs {busy}"
    );
    let mut bounded = limits;
    bounded.vm.max_steps = idle;
    assert!(matches!(
        base.execute_source_definitions(&[source(30).as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
}
