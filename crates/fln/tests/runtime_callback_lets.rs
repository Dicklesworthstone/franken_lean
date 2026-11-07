//! Callback annotations preserve live let prefixes and discard dead source work.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Outcome, VmExit};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}

fn execute(source: &str, expected: &str) {
    let run = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("callback did not return: {source}");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

#[test]
fn global_consumers_receive_callbacks_after_strict_let_prefixes() {
    execute(
        "def consume (f : Nat -> Nat) : Nat := f 7\n\
         def value : Nat := consume (let retained := 2; fun x => retained + x)\n\
         #eval value",
        "9",
    );
    execute(
        "def consume (f : Nat -> Nat) : Nat := f 7\n\
         def value : Nat := consume (let retained := 2; let next := retained + 1; fun x => retained + next + x)\n\
         #eval value",
        "12",
    );
}

#[test]
fn local_consumers_keep_the_original_callback_telescope() {
    execute(
        "def withConsumer (consume : (Nat -> Nat) -> Nat) (offset : Nat) : Nat := consume (let retained := offset + 1; fun x => retained + x)\n\
         #eval withConsumer (fun f => f 7) 1",
        "9",
    );
}

#[test]
fn callback_let_captures_keep_owned_strings_and_result_types() {
    execute(
        "def consume (f : String -> String) : Nat := String.length (f \"x\") + String.length (f \"yz\")\n\
         def value : Nat := consume (let retained := \"a\" ++ \"bc\"; fun s => retained ++ s ++ retained)\n\
         #eval value",
        "15",
    );
}

const SPEND: &str =
    "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n";

#[test]
fn dead_callback_initializers_are_cheap_and_live_initializers_remain_bounded() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let consumers = [
        (
            "def ignore (f : Nat -> Nat) : Nat := 42\n\
             def run (cost : Nat) : Nat := ignore (let paid := spend cost; fun x => x)\n",
            "def consume (f : Nat -> Nat) : Nat := f 42\n\
             def run (cost : Nat) : Nat := consume (let paid := spend cost; fun x => paid + x)\n",
        ),
        (
            "def withConsumer (consume : (Nat -> Nat) -> Nat) (cost : Nat) : Nat := consume (let paid := spend cost; fun x => x)\n\
             def run (cost : Nat) : Nat := withConsumer (fun f => 42) cost\n",
            "def withConsumer (consume : (Nat -> Nat) -> Nat) (cost : Nat) : Nat := consume (let paid := spend cost; fun x => paid + x)\n\
             def run (cost : Nat) : Nat := withConsumer (fun f => f 42) cost\n",
        ),
    ];
    let mut bounded = limits();
    bounded.vm.max_steps = 2000;
    bounded.vm.max_stack_depth = 256;
    for (discarded, consumer) in consumers {
        let mut dead_steps = None;
        for cost in [0, 100000] {
            let source = format!("{SPEND}{discarded}#eval run {cost}");
            let completed = base
                .execute_source_definitions(&[source.as_bytes()], &options, bounded)
                .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
                .into_complete()
                .expect("the original discarded initializer must fit the same VM bound");
            let VmExit::Returned(value) = &completed.executions.last().unwrap().exit else {
                panic!("discarded callback did not return: {source}");
            };
            assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some("42"));
            if let Some(idle) = dead_steps {
                assert_eq!(value.usage.steps, idle, "dead source work consumed VM fuel");
            }
            dead_steps = Some(value.usage.steps);
        }
        execute(&format!("{SPEND}{consumer}#eval run 30"), "72");
        let expensive = format!("{SPEND}{consumer}#eval run 100000");
        assert!(matches!(
            base.execute_source_definitions(&[expensive.as_bytes()], &options, bounded)
                .unwrap_or_else(|error| panic!("{expensive}\n{error:?}")),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(base.logical_root(&options), root);
        let cheap = format!("{SPEND}{consumer}#eval run 0");
        let retry = || {
            base.execute_source_definitions(&[cheap.as_bytes()], &options, bounded)
                .unwrap_or_else(|error| panic!("{cheap}\n{error:?}"))
                .into_complete()
                .unwrap()
        };
        let first = retry();
        let second = retry();
        let VmExit::Returned(value) = &first.executions.last().unwrap().exit else {
            panic!("callback clean retry did not return");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42")
        );
        assert_eq!(
            first.executions.last().unwrap().flbc_artifact,
            second.executions.last().unwrap().flbc_artifact
        );
        assert_eq!(base.logical_root(&options), root);
    }
}
