//! Deeper List histories run from the actual admitted pinned Prelude.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionLimits, Environment, KVMap, Name,
    OleanCheckLimits, OleanModuleInput,
};
use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::{
        OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
};

const STACK: usize = 256 * 1024 * 1024;
const COUNT: &str = "def count : List Nat -> Nat\n | [] => 0\n | [_] => 1\n | _ :: _ :: t => count t + 2\ntermination_by structural xs => xs\n";
const SPIN: &str = "partial def spin (n : Nat) : Nat := spin n\n";

fn with_fixture(test: impl FnOnce(&Engine, &Path) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            static FIXTURE: OnceLock<Option<(Engine, PathBuf)>> = OnceLock::new();
            let fixture = FIXTURE.get_or_init(|| {
                let row = include_str!("../../../SUITE.lock")
                    .lines()
                    .find(|line| line.starts_with("reference leanprover/lean4 "))
                    .unwrap();
                let field = |key: &str| {
                    row.split_whitespace()
                        .find_map(|x| x.strip_prefix(key))
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
                    })
                    .filter(|path| path.is_dir());
                let Some(library) = library else {
                    assert!(
                        std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                        "pinned Reference required"
                    );
                    eprintln!("SKIP: pinned Reference library is absent");
                    return None;
                };
                let compiler = library.parent().unwrap().parent().unwrap().join("bin/lean");
                let version = Command::new(&compiler).arg("--version").output().unwrap();
                let text = String::from_utf8(version.stdout).unwrap();
                assert!(
                    version.status.success()
                        && text.contains(field("tag=").trim_start_matches('v'))
                        && text.contains(field("commit=")),
                    "{text}"
                );
                let path = library.join("Init/Prelude.olean");
                let parts = [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ];
                let module = Name::from_components(["Init", "Prelude"]);
                let inputs = [OleanModuleInput {
                    name: &module,
                    artifact: &parts[0],
                    server_artifact: Some(&parts[1]),
                    private_artifact: Some(&parts[2]),
                }];
                let engine = Engine::from_environment(Environment::new())
                    .import_olean_modules_for_source(
                        &inputs,
                        std::slice::from_ref(&module),
                        &KVMap::new(),
                        SourceOleanImportLimits::new(OleanCheckLimits::new(
                            STACK,
                            Budget::for_stack_bytes(STACK),
                        )),
                    )
                    .unwrap()
                    .into_complete()
                    .unwrap()
                    .engine;
                Some((engine, compiler))
            });
            if let Some((engine, compiler)) = fixture {
                test(engine, compiler);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn reference(compiler: &Path, source: &str, expected: Option<&str>) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!("fln-list-course-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let result = Command::new(compiler).arg(path).output().unwrap();
    assert_eq!(
        result.status.success(),
        expected.is_some(),
        "{source}\n{}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    if let Some(expected) = expected {
        assert_eq!(
            String::from_utf8(result.stdout).unwrap().trim(),
            expected,
            "{source}"
        );
    }
}

fn execute(engine: &Engine, compiler: &Path, source: &str, expected: ClosedVmValue, printed: &str) {
    reference(compiler, source, Some(printed));
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let run = || {
        engine
            .execute_source_commands_with_checks(
                source.as_bytes(),
                &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
            .into_complete()
            .unwrap()
    };
    let first = run();
    let execution = first.batch.executions.last().unwrap();
    assert_eq!(
        fln::closed_vm_value(&execution.exit).unwrap(),
        Some(expected.clone()),
        "{source}"
    );
    let replay = fln::execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        fln::closed_vm_value(&replay).unwrap(),
        Some(expected),
        "{source}"
    );
    let second = run();
    assert_eq!(
        execution.flbc_artifact,
        second.batch.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn imported_two_step_lists_cover_every_boundary_and_bytecode_replay() {
    with_fixture(|engine, compiler| {
        for (list, expected) in [
            ("[]", 0),
            ("[10]", 1),
            ("[10,20]", 2),
            ("[10,20,30]", 3),
            ("[10,20,30,40,50]", 5),
        ] {
            execute(
                engine,
                compiler,
                &format!("{COUNT}#eval count {list}\n"),
                ClosedVmValue::Scalar(expected),
                &expected.to_string(),
            );
        }
    });
}

#[test]
fn three_and_four_step_histories_preserve_payloads_and_order() {
    with_fixture(|engine, compiler| {
        execute(
            engine,
            compiler,
            "def triples : List Nat -> Nat\n | [] => 0\n | [a] => a\n | [a,b] => a+b\n | a :: b :: c :: t => a + 10*b + 100*c + triples t\ntermination_by structural xs => xs\n#eval triples [1,2,3,4,5,6]\n",
            ClosedVmValue::Scalar(975),
            "975",
        );
        execute(
            engine,
            compiler,
            "def quarters : List Nat -> Nat\n | [] => 0\n | [_] => 1\n | [_,_] => 2\n | [_,_,_] => 3\n | _ :: _ :: _ :: _ :: t => quarters t + 4\ntermination_by structural xs => xs\n#eval quarters [1,2,3,4,5,6,7]\n",
            ClosedVmValue::Scalar(7),
            "7",
        );
        execute(
            engine,
            compiler,
            "def ways : List Nat -> Nat\n | [] => 1\n | [_] => 1\n | _ :: b :: t => ways (b::t) + ways t\ntermination_by structural xs => xs\n#eval ways [1,2,3,4,5]\n",
            ClosedVmValue::Scalar(8),
            "8",
        );
    });
}

#[test]
fn captured_values_and_changed_accumulators_keep_their_closure_interfaces() {
    with_fixture(|engine, compiler| {
        execute(
            engine,
            compiler,
            "def shifted (seed : Nat) : List Nat -> Nat\n | [] => seed\n | [_] => seed+1\n | _ :: _ :: t => shifted seed t + 2\ntermination_by structural xs => xs\n#eval shifted 37 [1,2,3,4,5]\n",
            ClosedVmValue::Scalar(42),
            "42",
        );
        execute(
            engine,
            compiler,
            "def walk (xs : List Nat) (acc : Nat) : Nat := match xs with\n | [] => acc\n | [a] => acc+a\n | a :: b :: t => walk t (acc+a+b)\ntermination_by structural xs\n#eval walk [1,2,3,4,5] 27\n",
            ClosedVmValue::Scalar(42),
            "42",
        );
    });
}

#[test]
fn owned_elements_and_results_survive_history_capture() {
    with_fixture(|engine, compiler| {
        execute(
            engine,
            compiler,
            "def pick : List String -> String\n | [] => \"empty\"\n | [a] => a\n | _ :: _ :: t => pick t\ntermination_by structural xs => xs\n#eval pick [\"first\",\"second\",\"λtail\"]\n",
            ClosedVmValue::String("λtail".into()),
            "\"λtail\"",
        );
        execute(
            engine,
            compiler,
            "def countAny {A : Type u} : List A -> Nat\n | [] => 0\n | [_] => 1\n | _ :: _ :: t => countAny t + 2\ntermination_by structural xs => xs\n#eval countAny [\"first\",\"second\",\"third\"]\n",
            ClosedVmValue::Scalar(3),
            "3",
        );
    });
}

#[test]
fn skipped_history_entries_and_empty_callback_are_not_evaluated() {
    with_fixture(|engine, compiler| {
        execute(
            engine,
            compiler,
            &format!(
                "{SPIN}def evens : List Nat -> Nat\n | [] => 0\n | [_] => spin 0\n | _ :: _ :: t => evens t + 2\ntermination_by structural xs => xs\n#eval evens [1,2,3,4]\n"
            ),
            ClosedVmValue::Scalar(4),
            "4",
        );
        execute(
            engine,
            compiler,
            &format!(
                "{SPIN}def odds : List Nat -> Nat\n | [] => spin 0\n | [_] => 1\n | _ :: _ :: t => odds t + 2\ntermination_by structural xs => xs\n#eval odds [1,2,3,4,5]\n"
            ),
            ClosedVmValue::Scalar(5),
            "5",
        );
    });
}

#[test]
fn live_divergence_remains_a_typed_stop_and_does_not_publish() {
    with_fixture(|engine, compiler| {
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        for query in ["[1]", "[1,2]"] {
            let source = format!(
                "{SPIN}def live : List Nat -> Nat\n | [] => 0\n | [_] => spin 0\n | _ :: _ :: t => let unused := spin 0; live t + 2\ntermination_by structural xs => xs\n#eval live {query}\n"
            );
            let result = engine.execute_source_commands_with_checks(
                source.as_bytes(),
                &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            );
            assert!(
                matches!(result, Ok(fln::Outcome::Inconclusive(_))),
                "{result:?}"
            );
            assert!(format!("{result:?}").contains("ExecutionSteps"));
            assert_eq!(engine.logical_root(&options), root);
        }
        execute(
            engine,
            compiler,
            &format!("{COUNT}#eval count [1,2,3]\n"),
            ClosedVmValue::Scalar(3),
            "3",
        );
    });
}

#[test]
fn nondecreasing_calls_and_invalid_live_types_still_refuse() {
    with_fixture(|engine, compiler| {
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        for body in ["loop (a::b::t)", "let invalid : Bool := a; loop t"] {
            let source = format!(
                "def loop : List Nat -> Nat\n | [] => 0\n | [_] => 1\n | a :: b :: t => {body}\ntermination_by structural xs => xs\n#eval loop [1,2]\n"
            );
            reference(compiler, &source, None);
            assert!(
                engine
                    .execute_source_commands_with_checks(
                        source.as_bytes(),
                        &options,
                        EngineExecutionLimits::new(Budget::for_stack_bytes(STACK))
                    )
                    .is_err(),
                "{source}"
            );
            assert_eq!(engine.logical_root(&options), root);
        }
    });
}
