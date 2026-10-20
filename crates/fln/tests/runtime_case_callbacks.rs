//! Case-only elimination of recursive data preserves staged callback execution.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, FlbcExecutionLimits, KVMap,
    Outcome, VmExit, execute_flbc_artifact,
};

const DEFINITIONS: &str = r#"
inductive Chain where
  | nil : Chain
  | cons : Nat -> Chain -> Chain
def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1
def choose (xs : Chain) : (Bool -> Nat -> Nat) -> Nat -> Nat :=
  match xs with
  | .nil => fun fallback n => fallback false n
  | .cons head tail => fun fallback n => n + 1
"#;

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn returned(exit: &VmExit, expected: u64) -> u64 {
    let VmExit::Returned(value) = exit else {
        panic!("expected return, got {exit:?}");
    };
    assert_eq!(
        fln::nat_decimal(&value.value).as_deref(),
        Some(expected.to_string().as_str())
    );
    value.usage.steps
}
fn execute(source: &str, expected: u64) -> u64 {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let run = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let execution = run.executions.last().unwrap();
    let steps = returned(&execution.exit, expected);
    let replay = execute_flbc_artifact(
        &execution.flbc_artifact,
        &options,
        FlbcExecutionLimits::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_eq!(returned(&replay, expected), steps);
    assert_eq!(base.logical_root(&options), root);
    reference(source, expected);
    steps
}
fn program(input: &str, cost: u64) -> String {
    format!(
        "{DEFINITIONS}\n#eval choose ({input}) (fun (_ : Bool) => let paid : Nat := spend {cost}; fun (n : Nat) => n + paid) 41"
    )
}

#[test]
fn a_recursive_datatype_case_keeps_a_known_staged_callback() {
    for input in ["Chain.nil", "Chain.cons 7 Chain.nil"] {
        execute(&program(input, 1), 42);
    }
}
#[test]
fn bound_arguments_reach_the_selected_case_before_callback_join() {
    for input in ["Chain.nil", "Chain.cons 7 Chain.nil"] {
        execute(
            &format!(
                "{DEFINITIONS}\n#eval let n : Nat := 41; choose ({input}) (fun (_ : Bool) => let paid : Nat := spend 1; fun (n : Nat) => n + paid) n"
            ),
            42,
        );
    }
}
#[test]
fn the_selected_callback_stage_runs_and_an_unselected_stage_stays_lazy() {
    let idle = execute(&program("Chain.nil", 0), 41);
    let busy = execute(&program("Chain.nil", 30), 71);
    assert!(
        busy > idle + 30,
        "strict stage disappeared: {idle} / {busy}"
    );
    let unused_idle = execute(&program("Chain.cons 7 Chain.nil", 0), 42);
    let unused_busy = execute(&program("Chain.cons 7 Chain.nil", 30), 42);
    assert_eq!(
        unused_idle, unused_busy,
        "unselected callback body executed"
    );
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let mut bounded = limits();
    bounded.vm.max_steps = idle;
    assert!(matches!(
        base.execute_source_definitions(
            &[program("Chain.nil", 30).as_bytes()],
            &KVMap::new(),
            bounded
        )
        .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
#[test]
fn a_case_callback_retains_outer_captures_and_heap_values() {
    execute(
        &format!(
            r#"{DEFINITIONS}
def run (suffix : String) (delta : Nat) : Nat :=
  choose Chain.nil (fun (_ : Bool) => let saved : String := suffix ++ suffix; fun (n : Nat) => n + String.length saved + delta) 30
#eval run "abc" 6
"#
        ),
        42,
    );
}
#[test]
fn real_induction_hypotheses_and_partial_data_results_keep_the_existing_path() {
    execute(
        &format!(
            r#"{DEFINITIONS}
def sum (xs : Chain) : Nat := match xs with
  | .nil => 0
  | .cons x tail => x + sum tail
#eval sum (Chain.cons 20 (Chain.cons 22 Chain.nil))
"#
        ),
        42,
    );
    execute(
        &format!(
            r#"{DEFINITIONS}
#eval let selected := choose (Chain.cons 7 Chain.nil); selected (fun (_ : Bool) (n : Nat) => n + 1) 41
"#
        ),
        42,
    );
}
#[test]
fn malformed_callbacks_and_compilation_stops_leave_a_fresh_retry_identical() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = program("Chain.nil", 1);
    let mut tiny = limits();
    tiny.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, tiny)
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let bad = format!("{DEFINITIONS}\n#eval choose Chain.nil (fun (s : String) (n : Nat) => n) 41");
    assert!(
        base.execute_source_definitions(&[bad.as_bytes()], &options, limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let first = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let second = base
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    returned(&first.executions.last().unwrap().exit, 42);
}

fn reference(source: &str, expected: u64) {
    use std::{
        path::PathBuf,
        process::Command,
        sync::{
            OnceLock,
            atomic::{AtomicUsize, Ordering},
        },
    };
    static PIN: OnceLock<Option<PathBuf>> = OnceLock::new();
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let pin = PIN.get_or_init(|| {
        let row = include_str!("../../../SUITE.lock")
            .lines()
            .find(|line| line.starts_with("reference leanprover/lean4 "))
            .unwrap();
        let field = |key: &str| {
            row.split_whitespace()
                .find_map(|word| word.strip_prefix(key))
                .unwrap()
        };
        let library = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    PathBuf::from(home)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{}", field("tag=")))
                        .join("lib/lean")
                })
            });
        let executable = library
            .and_then(|lib| Some(lib.parent()?.parent()?.join("bin/lean")))
            .filter(|path| path.is_file());
        let Some(executable) = executable else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Lean required"
            );
            eprintln!("SKIP: case-callback differential requires the pinned compiler");
            return None;
        };
        let result = Command::new(&executable).arg("--version").output().unwrap();
        let version = String::from_utf8(result.stdout).unwrap();
        assert!(
            result.status.success()
                && version.contains(field("tag=").trim_start_matches('v'))
                && version.contains(field("commit=")),
            "{version}"
        );
        Some(executable)
    });
    let Some(pin) = pin else {
        return;
    };
    let dir = std::env::temp_dir().join(format!("fln-case-callbacks-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(
        &path,
        format!("set_option linter.unusedVariables false\n{source}\n"),
    )
    .unwrap();
    let result = Command::new(pin).arg(path).output().unwrap();
    assert!(
        result.status.success(),
        "{source}\n{}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(
        String::from_utf8(result.stdout).unwrap().trim(),
        expected.to_string()
    );
}
