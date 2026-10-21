//! Deeper source recursion must execute on the native VM and survive FLBC replay.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};
use std::{
    path::PathBuf,
    process::Command,
    sync::{
        OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
};

fn execute(source: &str, expected: &str) {
    let limits = EngineExecutionLimits::for_user_program(Budget::for_stack_bytes(8 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let run = engine
        .execute_source_definitions(&[source.as_bytes()], &options, limits)
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let execution = run.executions.last().unwrap();
    let VmExit::Returned(value) = &execution.exit else {
        panic!("{:?}", execution.exit);
    };
    assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
    let replay = fln::execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = replay else {
        panic!("{replay:?}");
    };
    assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
    assert_eq!(engine.logical_root(&options), root);
    reference(source, expected);
}

#[test]
fn fibonacci_reads_both_previous_results_instead_of_refusing_history() {
    execute(
        "def fib : Nat -> Nat\n | 0 => 0\n | 1 => 1\n | n+2 => fib n + fib (n+1)\ntermination_by structural n => n\n#eval fib 10\n",
        "55",
    );
}

#[test]
fn two_step_recursion_preserves_base_cases_and_runtime_arguments() {
    for (n, expected) in [(0, "0"), (1, "0"), (2, "1"), (9, "4"), (40, "20")] {
        execute(
            &format!(
                "def half : Nat -> Nat\n | 0 => 0\n | 1 => 0\n | n+2 => half n + 1\ntermination_by structural n => n\ndef run (n : Nat) : Nat := half n\n#eval run {n}\n"
            ),
            expected,
        );
    }
}

#[test]
fn three_previous_results_and_four_step_descent_use_their_actual_window() {
    execute(
        "def tri : Nat -> Nat\n | 0 => 0\n | 1 => 0\n | 2 => 1\n | n+3 => tri n + tri (n+1) + tri (n+2)\ntermination_by structural n => n\n#eval tri 10\n",
        "81",
    );
    execute(
        "def quarters : Nat -> Nat\n | 0 => 0\n | 1 => 0\n | 2 => 0\n | 3 => 0\n | n+4 => quarters n + 1\ntermination_by structural n => n\n#eval quarters 23\n",
        "5",
    );
}

#[test]
fn fixed_runtime_captures_are_not_shifted_into_the_window_binders() {
    execute(
        "def shifted (seed n : Nat) : Nat := match n with\n | 0 => seed\n | 1 => seed+1\n | k+2 => shifted seed k + shifted seed (k+1)\ntermination_by structural n\n#eval shifted 3 8\n",
        "123",
    );
}

#[test]
fn function_valued_history_preserves_changed_accumulators() {
    execute(
        "def walk (n acc : Nat) : Nat := match n with\n | 0 => acc\n | 1 => acc\n | k+2 => walk k (acc+2)\ntermination_by structural n\n#eval walk 30 7\n",
        "37",
    );
}

fn reference(source: &str, expected: &str) {
    static PIN: OnceLock<Option<PathBuf>> = OnceLock::new();
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let pin = PIN.get_or_init(|| {
        let row = include_str!("../../../SUITE.lock")
            .lines()
            .find(|line| line.starts_with("reference leanprover/lean4 "))
            .unwrap();
        let field = |key: &str| {
            row.split_whitespace()
                .find_map(|s| s.strip_prefix(key))
                .unwrap()
        };
        let lib = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|h| {
                    PathBuf::from(h)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{}", field("tag=")))
                        .join("lib/lean")
                })
            });
        let pin = lib
            .and_then(|p| Some(p.parent()?.parent()?.join("bin/lean")))
            .filter(|p| p.is_file());
        if let Some(pin) = &pin {
            let out = Command::new(pin).arg("--version").output().unwrap();
            let version = String::from_utf8(out.stdout).unwrap();
            assert!(
                out.status.success()
                    && version.contains(field("tag=").trim_start_matches('v'))
                    && version.contains(field("commit=")),
                "{version}"
            );
        } else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference required"
            );
            eprintln!("SKIP: course-of-values differential requires the pinned Lean compiler");
        }
        pin
    });
    let Some(pin) = pin else {
        return;
    };
    let dir = std::env::temp_dir().join(format!("fln-runtime-history-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let out = Command::new(pin).arg(path).output().unwrap();
    assert!(
        out.status.success(),
        "{source}\n{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8(out.stdout).unwrap().trim(),
        expected,
        "{source}"
    );
}

#[test]
fn an_unused_history_branch_does_not_execute_a_diverging_callback() {
    let source = "partial def spin (n : Nat) : Nat := spin n\ndef evens : Nat -> Nat\n | 0 => 0\n | 1 => spin 0\n | n+2 => evens n + 1\ntermination_by structural n => n\n#eval evens 10\n";
    reference(source, "5");
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(8 * 1024 * 1024));
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let run = base
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits)
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!(
            "unused odd callback executed: {:?}",
            run.executions.last().unwrap().exit
        );
    };
    assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some("5"));
}

#[test]
fn the_zero_callback_can_also_remain_unused() {
    execute(
        "partial def spin (n : Nat) : Nat := spin n\ndef odds : Nat -> Nat\n | 0 => spin 0\n | 1 => 1\n | n+2 => odds n + 1\ntermination_by structural n => n\n#eval odds 9\n",
        "5",
    );
}

#[test]
fn all_three_step_boundary_cases_keep_the_correct_history_order() {
    let definition = "def tri : Nat -> Nat\n | 0 => 0\n | 1 => 0\n | 2 => 1\n | n+3 => tri n + tri (n+1) + tri (n+2)\ntermination_by structural n => n\n";
    execute(
        &format!(
            "{definition}#eval tri 0 + tri 1 * 10 + tri 2 * 100 + tri 3 * 1000 + tri 4 * 10000\n"
        ),
        "21100",
    );
}

#[test]
fn requested_divergence_is_a_typed_stop_and_does_not_publish() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(8 * 1024 * 1024));
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = "partial def spin (n : Nat) : Nat := spin n\ndef evens : Nat -> Nat\n | 0 => 0\n | 1 => spin 0\n | n+2 => evens n + 1\ntermination_by structural n => n\n#eval evens 1\n";
    let result = base.execute_source_definitions(&[source.as_bytes()], &options, limits);
    assert!(
        matches!(result, Ok(fln::Outcome::Inconclusive(_))),
        "{result:?}"
    );
    assert!(format!("{result:?}").contains("ExecutionSteps"));
    assert_eq!(base.logical_root(&options), root);
}
