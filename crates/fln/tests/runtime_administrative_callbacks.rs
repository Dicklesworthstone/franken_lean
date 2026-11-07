//! Value-only aliases do not invent a strict runtime callback stage.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits,
    FlbcExecutionLimits, IngressError, KVMap, Outcome, VmExit, execute_flbc_artifact,
};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}

fn returned(exit: &VmExit, expected: &str) -> u64 {
    let VmExit::Returned(result) = exit else {
        panic!("the admitted callback must return natively");
    };
    assert_eq!(fln::nat_decimal(&result.value).as_deref(), Some(expected));
    result.usage.steps
}

#[test]
fn unused_administrative_gaps_keep_flat_consumers_captures_and_canonical_replay() {
    let engine = engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for (source, expected) in [
        (
            r#"
def forwardAlias (consumer : (Bool -> Nat -> Nat) -> Nat) (captured : Nat) : Nat :=
  consumer (fun _ =>
    let unused := captured
    let message := "unreachable"
    let forwarded := message
    let action : Nat -> Nat := fun n => n + captured
    let result := action
    result)
#eval forwardAlias (fun callback => callback false 10) 32
"#,
            "42",
        ),
        (
            r#"
def forwardOwned (consumer : (Bool -> String -> String) -> Nat) (capturedText : String) : Nat :=
  consumer (fun _ =>
    let unused := capturedText
    let message := "unreachable"
    let forwarded := message
    let action : String -> String := fun suffix => capturedText ++ suffix
    let result := action
    result)
#eval forwardOwned (fun callback => String.length (callback false "!")) "hello"
"#,
            "6",
        ),
        (
            r#"
def forwardRecursive (consumer : (Bool -> Nat -> Nat) -> Nat) (captured : Nat) : Nat :=
  consumer (fun _ =>
    let unused := captured
    let action : Nat -> Nat := fun n => Nat.rec captured (fun _ total => total + 1) n
    let result := action
    result)
#eval forwardRecursive (fun callback => callback false 35) 7
"#,
            "42",
        ),
        (
            r#"
def forwardSelected (select : Bool) (consumer : (Bool -> Nat -> Nat) -> Nat) (captured : Nat) : Nat :=
  let callback : Bool -> Nat -> Nat := if select then
    (fun _ =>
      let unused := captured
      let action : Nat -> Nat := fun n => n + captured
      let result := action
      result)
    else (fun _ => fun n => n)
  consumer callback
#eval forwardSelected true (fun callback => callback false 10) 32
"#,
            "42",
        ),
        (
            r#"
def forwardPrepared (consumer : (Bool -> Nat -> Nat) -> Nat) (captured : Nat) : Nat :=
  consumer (fun _ =>
    let message := (fun text : String => text) "unreachable"
    let unused := captured
    let action : Nat -> Nat := fun n => n + 32
    let result := action
    result)
#eval forwardPrepared (fun callback => callback false 10) 7
"#,
            "42",
        ),
    ] {
        let run = || {
            engine
                .execute_source_definitions(&[source.as_bytes()], &options, limits())
                .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
                .into_complete()
                .unwrap()
        };
        let first = run();
        let second = run();
        let execution = first.executions.last().unwrap();
        let steps = returned(&execution.exit, expected);
        assert_eq!(
            execution.flbc_artifact,
            second.executions.last().unwrap().flbc_artifact
        );
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        assert_eq!(returned(&replay, expected), steps);
        assert_eq!(engine.logical_root(&options), root);
    }
}

const SPEND: &str =
    "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n";

#[test]
fn dead_first_stages_are_cheap_and_used_stages_keep_exact_vm_bounds() {
    let engine = engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let discarded = |cost| {
        format!(
            "{SPEND}def ignorePartial (f : Nat -> Nat -> Nat) (n : Nat) : Nat := let unused : Nat -> Nat := f n; 42\n#eval ignorePartial (fun n => let paid := spend n; let result : Nat -> Nat := fun y => y; result) {cost}"
        )
    };
    let source = |cost| {
        format!(
            "{SPEND}def usePartial (f : Nat -> Nat -> Nat) (n : Nat) : Nat := let action : Nat -> Nat := f n; action 42\n#eval usePartial (fun n => let paid := spend n; let result : Nat -> Nat := fun y => paid + y; result) {cost}"
        )
    };
    let run = |source: &str, expected| {
        let run = engine
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
        returned(&run.executions.last().unwrap().exit, expected)
    };
    assert_eq!(
        run(&discarded(0), "42"),
        run(&discarded(30), "42"),
        "the original discarded result must not execute its producer"
    );
    let idle = run(&source(0), "42");
    let busy = run(&source(30), "72");
    assert!(
        busy > idle + 30,
        "the first runtime stage disappeared: {idle} vs {busy}"
    );
    let mut bounded = limits();
    bounded.vm.max_steps = idle;
    let stopped = engine
        .execute_source_definitions(&[source(30).as_bytes()], &options, bounded)
        .unwrap();
    assert!(matches!(
        stopped,
        Outcome::Inconclusive(stop) if matches!(&stop.cause,
            fln_core::outcome::InconclusiveCause::ResourceExhausted { usage }
                if usage.reason == fln_core::diag::ResourceReason::ExecutionSteps
                    && usage.allowed == idle && usage.observed == idle + 1)
    ));
    assert_eq!(run(&source(0), "42"), idle);
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn a_dynamic_flat_consumer_does_not_cast_a_genuinely_staged_callback() {
    let engine = engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for consumer in [
        "fun callback => let unused := callback false; 42",
        "fun callback => let used := callback false; used 12",
    ] {
        let source = format!(
            "{SPEND}def forwardStrict (consumer : (Bool -> Nat -> Nat) -> Nat) (cost : Nat) : Nat := consumer (fun _ => let paid := spend cost; fun n => n + paid)\n#eval forwardStrict ({consumer}) 30"
        );
        // The declaration itself passes a staged closure to a flat dynamic
        // consumer and is compiled before either caller can discard work.
        let mut error = engine
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap_err();
        while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
            error = *inner;
        }
        assert!(
            matches!(
                error,
                EngineExecutionError::Ingress(IngressError::LambdaApplicationArgumentType { .. })
            ),
            "an incompatible runtime callback must remain refused: {error:?}"
        );
        assert_eq!(engine.logical_root(&options), root);
    }
}
