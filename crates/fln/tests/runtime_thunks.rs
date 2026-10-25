//! Real checked Init.Core/Init.Util Thunks reach Golem's memoized objects.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionError, EngineExecutionLimits, KVMap, Name,
    OleanCheckLimits, OleanModuleInput, Outcome, SourceCheckLimits, StdoutCapture,
};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{
    OnceLock,
    atomic::{AtomicUsize, Ordering},
};

const STACK: usize = 64 * 1024 * 1024;
// The oracle needs the syntax implementation behind dbg_trace's s! expansion;
// native source elaboration supplies its own implementation of that surface.
const HEADER: &str = "prelude\nimport Init.Util\nimport Init.Data.ToString.Macro\n";

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK))
}

fn fixture(test: impl FnOnce(&Engine, &Path) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            static FIXTURE: OnceLock<Option<(Engine, PathBuf)>> = OnceLock::new();
            let fixture = FIXTURE.get_or_init(|| {
                let library = std::env::var_os("FLN_REFERENCE_LIB")
                    .map(PathBuf::from)
                    .filter(|path| path.join("Init/Util.olean").is_file());
                let Some(library) = library else {
                    assert!(
                        std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                        "actual pinned Init.Util required"
                    );
                    eprintln!("SKIP: pinned Reference library absent");
                    return None;
                };
                let compiler = std::env::var_os("FLN_REFERENCE_BIN")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| {
                        library.parent().unwrap().parent().unwrap().join("bin/lean")
                    });
                let pin = include_str!("../../../SUITE.lock")
                    .lines()
                    .find(|line| line.starts_with("reference leanprover/lean4 "))
                    .unwrap();
                let field = |key| {
                    pin.split_whitespace()
                        .find_map(|word| word.strip_prefix(key))
                        .unwrap()
                };
                let version = Command::new(&compiler).arg("--version").output().unwrap();
                let text = String::from_utf8(version.stdout).unwrap();
                assert!(
                    version.status.success()
                        && text.contains(field("tag=").trim_start_matches('v'))
                        && text.contains(field("commit=")),
                    "{text}"
                );
                let root = name("Init.Util");
                let mut pending = vec![root.clone()];
                let mut artifacts = BTreeMap::new();
                while let Some(module) = pending.pop() {
                    if artifacts.contains_key(&module) {
                        continue;
                    }
                    assert!(artifacts.len() < 256, "bounded actual Init.Util closure");
                    let path = library
                        .join(module.to_display_string().replace('.', "/"))
                        .with_extension("olean");
                    let parts = [
                        std::fs::read(&path).unwrap(),
                        std::fs::read(path.with_extension("olean.server")).unwrap(),
                        std::fs::read(path.with_extension("olean.private")).unwrap(),
                    ];
                    pending.extend(
                        fln::olean_module_imports(&parts[0], fln::OleanDecodeLimits::new(STACK))
                            .unwrap(),
                    );
                    artifacts.insert(module, parts);
                }
                let inputs: Vec<_> = artifacts
                    .iter()
                    .map(|(module, parts)| OleanModuleInput {
                        name: module,
                        artifact: &parts[0],
                        server_artifact: Some(&parts[1]),
                        private_artifact: Some(&parts[2]),
                    })
                    .collect();
                let mut admission =
                    SourceOleanImportLimits::new(OleanCheckLimits::new(STACK, limits().kernel));
                admission.jobs.threads = std::num::NonZeroUsize::new(1).unwrap();
                admission.jobs.worker_stack_bytes = STACK;
                admission.read_jobs = admission.jobs;
                let imported = Engine::builder()
                    .build_empty()
                    .import_olean_modules_for_source(&inputs, &[root], &KVMap::new(), admission)
                    .unwrap()
                    .into_complete()
                    .unwrap();
                assert_eq!(imported.checked.modules.len(), inputs.len());
                for checked in &imported.checked.modules {
                    assert!(matches!(
                        &checked.decoded.independent,
                        fln::IndependentReading::Read(_)
                    ));
                    assert_eq!(checked.declarations.len(), checked.decoded.constants.len());
                }
                for (target, symbol) in [
                    ("Thunk.mk", "lean_mk_thunk"),
                    ("Thunk.pure", "lean_thunk_pure"),
                    ("Thunk.get", "lean_thunk_get_own"),
                ] {
                    let table = fln_elab::externs::ExternTable::read(imported.engine.environment())
                        .unwrap();
                    assert_eq!(
                        table.get(&name(target)),
                        Some(
                            [fln_elab::externs::ExternEntry::Standard {
                                backend: name("all"),
                                symbol: symbol.to_owned(),
                            }]
                            .as_slice()
                        )
                    );
                }
                Some((imported.engine, compiler))
            });
            if let Some((engine, compiler)) = fixture {
                test(engine, compiler);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn pin(compiler: &Path, source: &str, trace: &str, printed: &str) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!("fln-source-thunks-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, format!("{HEADER}{source}")).unwrap();
    let output = Command::new(compiler).arg(path).output().unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(output.status.success(), "{source}\n{stdout}{stderr}");
    assert_eq!(stdout, format!("{trace}{printed}\n"), "{source}");
    assert_eq!(stderr, "", "{source}");
}

fn captured<T>(run: impl FnOnce() -> T) -> (T, String) {
    let capture = StdoutCapture::begin_evaluation(1024 * 1024).unwrap();
    let result = run();
    let captured = capture.finish();
    assert!(captured.error.is_none(), "{:?}", captured.error);
    (result, String::from_utf8(captured.bytes).unwrap())
}

fn run(engine: &Engine, source: &str) -> fln::DefinitionBatchExecution {
    engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn check(
    engine: &Engine,
    compiler: &Path,
    source: &str,
    trace: &str,
    expected: ClosedVmValue,
    printed: &str,
) -> Vec<u8> {
    pin(compiler, source, trace, printed);
    check_native(engine, source, trace, expected)
}

fn check_native(engine: &Engine, source: &str, trace: &str, expected: ClosedVmValue) -> Vec<u8> {
    let root = engine.logical_root(&KVMap::new());
    let (batch, captured_trace) = captured(|| run(engine, source));
    assert_eq!(batch.source_evaluation_indices.len(), 1);
    let execution = &batch.executions[batch.source_evaluation_indices[0]];
    assert_eq!(
        fln::closed_vm_value(&execution.exit).unwrap_or_else(|error| {
            panic!(
                "{source}\n{error:?}\nexit: {:?}\ntrace: {captured_trace:?}",
                execution.exit
            )
        }),
        Some(expected.clone()),
        "{source}\nexit: {:?}\ntrace: {captured_trace:?}",
        execution.exit
    );
    assert_eq!(captured_trace, trace, "{source}");
    let artifact = execution.flbc_artifact.clone();
    let (replay, replay_trace) = captured(|| {
        fln::execute_flbc_artifact(&artifact, &KVMap::new(), Default::default())
            .unwrap()
            .into_complete()
            .unwrap()
    });
    assert_eq!(fln::closed_vm_value(&replay).unwrap(), Some(expected));
    assert_eq!(
        replay_trace, trace,
        "canonical FLBC replay must keep the same lazy effects"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    artifact
}

#[test]
fn checked_thunks_share_forces_keep_allocations_distinct_and_delay_only_the_body() {
    fixture(|engine, compiler| {
        for (source, trace) in [
            (
                r#"#eval let t := Thunk.mk (fun _ => dbg_trace "forced"; 21); t.get + t.get"#,
                "forced\n",
            ),
            (
                r#"#eval let t := Thunk.mk (fun _ => dbg_trace "alias"; 21); let pair := (t, t); pair.1.get + pair.2.get"#,
                "alias\n",
            ),
            (
                r#"#eval let _t := Thunk.mk (fun _ => dbg_trace "unforced"; 21); 42"#,
                "",
            ),
            (
                r#"#eval let t := (dbg_trace "producer"; Thunk.mk (fun _ => dbg_trace "body"; 21)); t.get + t.get"#,
                "producer\nbody\n",
            ),
            (
                r#"#eval let a := Thunk.mk (fun _ => dbg_trace "allocation a"; 21); let first := a.get; let b := Thunk.mk (fun _ => dbg_trace "allocation b"; first); first + b.get"#,
                "allocation a\nallocation b\n",
            ),
            (
                r#"#eval let t := Thunk.pure (dbg_trace "eager"; 21); t.get + t.get"#,
                "eager\n",
            ),
        ] {
            let artifact = check(
                engine,
                compiler,
                source,
                trace,
                ClosedVmValue::Scalar(42),
                "42",
            );
            let program = fln_comp::flbc::decode_canonical(&artifact, Default::default()).unwrap();
            let rows: BTreeSet<_> = program
                .functions()
                .iter()
                .flat_map(|function| &function.code)
                .filter_map(|instruction| {
                    if let fln_comp::flbc::Instruction::Intrinsic { row, .. } = instruction {
                        Some(row.as_str())
                    } else {
                        None
                    }
                })
                .collect();
            if source.contains("t.get") || source.contains("a.get") || source.contains("pair.1.get")
            {
                assert!(rows.contains("extern:Thunk.get"), "{rows:?}");
            }
            assert!(
                rows.contains(if source.contains("Thunk.pure") {
                    "extern:Thunk.pure"
                } else {
                    "extern:Thunk.mk"
                }),
                "{rows:?}"
            );
        }
    });
}

#[test]
fn public_fields_patterns_and_first_class_operations_keep_cached_getters() {
    fixture(|engine, compiler| {
        for (source, trace) in [
            (
                r#"#eval let t := Thunk.mk (fun _ => dbg_trace "field"; 21); let f := t.fn; f () + f ()"#,
                "field\n",
            ),
            (
                r#"#eval let f := (Thunk.mk (fun _ => dbg_trace "direct field"; 21)).fn; f () + f ()"#,
                "direct field\n",
            ),
            (
                r#"def fromPattern (t : Thunk Nat) : Nat := match t with | .mk f => f () + f ()
#eval fromPattern (Thunk.mk (fun _ => dbg_trace "pattern"; 21))"#,
                "pattern\n",
            ),
            (
                r#"def build (factory : (Unit -> Nat) -> Thunk Nat) : Thunk Nat := factory (fun _ => dbg_trace "callback"; 21)
def twice (force : Thunk Nat -> Nat) (t : Thunk Nat) : Nat := force t + force t
#eval twice (@Thunk.get Nat) (build (@Thunk.mk Nat))"#,
                "callback\n",
            ),
            (
                r#"def wrap (pure : Nat -> Thunk Nat) : Thunk Nat := pure (dbg_trace "pure callback"; 21)
#eval let t := wrap (@Thunk.pure Nat); t.get + t.get"#,
                "pure callback\n",
            ),
            (
                r#"def mkNat : (Unit -> Nat) -> Thunk Nat := @Thunk.mk Nat
def forceNat : Thunk Nat -> Nat := @Thunk.get Nat
#eval let t := mkNat (fun _ => dbg_trace "global alias"; 21); forceNat t + forceNat t"#,
                "global alias\n",
            ),
        ] {
            check(
                engine,
                compiler,
                source,
                trace,
                ClosedVmValue::Scalar(42),
                "42",
            );
        }
    });
}

#[test]
fn mapped_nested_and_callable_payloads_keep_values_and_ownership() {
    fixture(|engine, compiler| {
        for (source, trace) in [
            // Fully implicit traced map/bind still exhausts elaboration's
            // defaulting budget. One receiver annotation isolates the native
            // imported map/bind path while callback/result types remain inferred.
            (
                r#"#eval let t : Thunk Nat := Thunk.mk (fun _ => dbg_trace "base"; 10); let mapped := t.map (fun n => dbg_trace "map"; n + 11); let bound := mapped.bind (fun n => dbg_trace "bind"; Thunk.pure n); bound.get + bound.get"#,
                "base\nmap\nbind\n",
            ),
            (
                r#"#eval let t := Thunk.mk (fun _ => dbg_trace "outer"; Thunk.mk (fun _ => dbg_trace "inner"; 21)); t.get.get + t.get.get"#,
                "outer\ninner\n",
            ),
            (
                r#"structure Payload where
  text : String
  count : Nat
#eval let t := Thunk.mk (fun _ => dbg_trace "record"; Payload.mk "kept" 21); t.get.count + t.get.count"#,
                "record\n",
            ),
            (
                r#"#eval let t := Thunk.pure (dbg_trace "function producer"; fun n : Nat => n + 21); t.get 0 + t.get 0"#,
                "function producer\n",
            ),
            (
                r#"#eval let t := Thunk.mk (fun _ => fun n : Nat => n + 21); t.get 0 + t.get 0"#,
                "",
            ),
        ] {
            check(
                engine,
                compiler,
                source,
                trace,
                ClosedVmValue::Scalar(42),
                "42",
            );
        }
        check(
            engine,
            compiler,
            r#"#eval let t := Thunk.mk (fun _ => dbg_trace "string"; "kept"); t.get"#,
            "string\n",
            ClosedVmValue::String("kept".to_owned()),
            "\"kept\"",
        );

        // The checked source product exposes actual closure objects. Both
        // forces must return the identical cached closure, not new adapters.
        let source = "def closurePair : (Nat -> Nat) × (Nat -> Nat) := let t := Thunk.mk (fun _ => fun n => n + 1); (t.get, t.get)";
        pin(
            compiler,
            &format!("{source}\n#eval closurePair.1 20 + closurePair.2 20"),
            "",
            "42",
        );
        let batch = run(engine, source);
        let fln::VmExit::Returned(returned) = &batch.executions.last().unwrap().exit else {
            panic!("returned closure product");
        };
        let first = returned.value.try_ctor_child(0).unwrap();
        let second = returned.value.try_ctor_child(1).unwrap();
        assert!(first.closure_shell_parts().is_some());
        assert_eq!(first.identity_token(), second.identity_token());
    });
}

fn cause(mut error: EngineExecutionError) -> EngineExecutionError {
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    error
}

fn changed_getter(engine: &Engine) -> Engine {
    let target = name("Thunk.get");
    let fln::ConstantInfo::Defn(original) = engine.environment().find(&target).unwrap() else {
        panic!("the pin supplies a checked getter definition")
    };
    let mut changed = original.clone();
    changed.value = fln::Expr::app(
        fln::Expr::lam(
            name("retainGetter"),
            changed.base.type_.clone(),
            fln::Expr::bvar(0).unwrap(),
            fln::BinderInfo::Default,
        ),
        changed.value,
    );
    let mut environment = fln::Environment::new();
    for (name, _) in engine.environment().constants() {
        if name != &target {
            environment = environment
                .with_entry(engine.environment().entry(name).unwrap())
                .unwrap();
        }
    }
    for (journal, state) in engine.environment().extensions() {
        environment = environment
            .register_extension(state.descriptor.clone())
            .unwrap();
        for entry in state.entries() {
            environment = environment
                .push_extension_entry(journal, entry.payload.clone())
                .unwrap();
        }
    }
    // A well-typed equivalent body still differs from the serialized native
    // contract. Both checker seats admit it; only executable recognition refuses.
    let admitted = Engine::from_environment(environment)
        .admit_declaration(
            fln::Declaration::Defn(changed),
            &KVMap::new(),
            limits().admission(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        admitted.checker.ground,
        fln::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    admitted.engine
}

#[test]
fn counterfeit_thunk_contracts_and_private_names_never_acquire_native_authority() {
    fixture(|engine, _| {
        let conflicting = Engine::from_environment(
            fln_elab::externs::register(
                engine.environment(),
                &name("Thunk.get"),
                vec![fln_elab::externs::ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "foreign_get".to_owned(),
                }],
            )
            .unwrap(),
        );
        let collision = engine
            .check_source_files(
                &[b"def _fln_runtime_thunk_payload := Nat"],
                &KVMap::new(),
                SourceCheckLimits::new(limits().admission()),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let changed = changed_getter(engine);
        for candidate in [&conflicting, &collision, &changed] {
            let root = candidate.logical_root(&KVMap::new());
            let (error, trace) = captured(|| {
                candidate.execute_source_definitions(
                &[b"#eval let t := Thunk.mk (fun _ => dbg_trace \"MUST_NOT_RUN\"; 21); t.get"],
                &KVMap::new(), limits(),
            ).unwrap_err()
            });
            assert!(matches!(
                cause(error),
                EngineExecutionError::Ingress(fln::IngressError::UnsupportedNode { .. })
            ));
            assert!(trace.is_empty());
            assert_eq!(candidate.logical_root(&KVMap::new()), root);
        }
        let replacement = engine
            .check_source_files(
                &[b"def replacementUnit : Unit := dbg_trace \"unit replacement\"; PUnit.unit"],
                &KVMap::new(),
                SourceCheckLimits::new(limits().admission()),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let replacement = Engine::from_environment(
            fln_elab::implemented_by::register(
                replacement.environment(),
                &name("Unit.unit"),
                &name("replacementUnit"),
            )
            .unwrap(),
        );
        let (direct, trace) = captured(|| {
            run(
                &replacement,
                "#eval let u := Unit.unit; (fun _ : Unit => 42) u",
            )
        });
        assert_eq!(trace, "unit replacement\n");
        assert_eq!(
            fln::closed_vm_value(&direct.executions[0].exit).unwrap(),
            Some(ClosedVmValue::Scalar(42))
        );
        let (forced, trace) = captured(|| {
            run(
                &replacement,
                r#"#eval let t := Thunk.mk (fun _ => dbg_trace "forced"; 21); t.get + t.get"#,
            )
        });
        assert_eq!(trace, "forced\n", "forcing supplies a raw Unit value");
        assert_eq!(
            fln::closed_vm_value(&forced.executions[0].exit).unwrap(),
            Some(ClosedVmValue::Scalar(42))
        );
        let seed = Engine::with_source_seed(limits().admission())
            .unwrap()
            .into_complete()
            .unwrap();
        let ordinary = seed
            .check_source_files(
                &[b"def Thunk.get (n : Nat) : Nat := n + 1"],
                &KVMap::new(),
                SourceCheckLimits::new(limits().admission()),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        assert_eq!(
            fln::closed_vm_value(&run(&ordinary, "#eval Thunk.get 41").executions[0].exit).unwrap(),
            Some(ClosedVmValue::Scalar(42))
        );
        let forged = Engine::from_environment(
            fln_elab::externs::register(
                ordinary.environment(),
                &name("Thunk.get"),
                vec![fln_elab::externs::ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "lean_thunk_get_own".to_owned(),
                }],
            )
            .unwrap(),
        );
        let error = forged
            .execute_source_definitions(&[b"#eval Thunk.get 41"], &KVMap::new(), limits())
            .unwrap_err();
        assert!(matches!(
            cause(error),
            EngineExecutionError::Ingress(fln::IngressError::UnsupportedNode { .. })
        ));
    });
}

#[test]
fn a_stopped_force_returns_no_answer_and_a_fresh_execution_recovers() {
    fixture(|engine, compiler| {
        let source = r#"#eval let t := Thunk.mk (fun _ => dbg_trace "bounded"; (Nat.rec 0 (fun _ total => total + 1) 200 : Nat)); t.get"#;
        let root = engine.logical_root(&KVMap::new());
        let mut preparation_limit = limits();
        preparation_limit.ingress.max_nodes = 1;
        let (error, trace) = captured(|| {
            engine
                .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), preparation_limit)
                .unwrap_err()
        });
        assert!(matches!(
            cause(error),
            EngineExecutionError::Ingress(fln::IngressError::ResourceLimit { .. })
        ));
        assert!(trace.is_empty());
        assert_eq!(engine.logical_root(&KVMap::new()), root);
        let artifact = check(
            engine,
            compiler,
            source,
            "bounded\n",
            ClosedVmValue::Scalar(200),
            "200",
        );
        let (complete, trace) = captured(|| {
            fln::execute_flbc_artifact(&artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .unwrap()
        });
        assert_eq!(trace, "bounded\n");
        let fln::VmExit::Returned(complete) = complete else {
            panic!("completed force");
        };
        let mut limited = fln::FlbcExecutionLimits::default();
        limited.vm.max_steps = complete.usage.steps / 2;
        let (stopped, trace) =
            captured(|| fln::execute_flbc_artifact(&artifact, &KVMap::new(), limited).unwrap());
        assert!(matches!(stopped, Outcome::Inconclusive(_)), "{stopped:?}");
        assert_eq!(trace, "bounded\n", "stop occurs inside the forced callback");
        let (recovered, trace) = captured(|| {
            fln::execute_flbc_artifact(&artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .unwrap()
        });
        assert_eq!(trace, "bounded\n");
        assert_eq!(
            fln::closed_vm_value(&recovered).unwrap(),
            Some(ClosedVmValue::Scalar(200))
        );
    });
}

#[test]
fn function_valued_thunks_match_the_pinned_callback_telescope() {
    fixture(|engine, compiler| {
        for (source, expected_trace) in [
            (
                r#"#eval let t := Thunk.mk (fun _ => dbg_trace "function"; fun n : Nat => n + 20); t.get 0 + t.get 2"#,
                "function\nfunction\n",
            ),
            (
                r#"#eval let t := Thunk.mk (fun _ => dbg_trace "cached function"; fun n : Nat => n + 20); let f := t.get; f 0 + f 2"#,
                "cached function\ncached function\n",
            ),
            (
                r#"def existingFunction (n : Nat) : Nat := dbg_trace "existing"; n + 20
#eval let t := Thunk.mk (fun _ => existingFunction); t.get 0 + t.get 2"#,
                "existing\nexisting\n",
            ),
            (
                r#"#eval let t := Thunk.mk (fun _ => dbg_trace "two arguments"; fun a : Nat => fun b : Nat => a + b + 20); let f := t.get 0; f 0 + f 2"#,
                "two arguments\ntwo arguments\n",
            ),
            (
                r#"def functionPattern (t : Thunk (Nat -> Nat)) : Nat := match t with | .mk f => f () 0 + f () 2
#eval functionPattern (Thunk.mk (fun _ => dbg_trace "function pattern"; fun n : Nat => n + 20))"#,
                "function pattern\nfunction pattern\n",
            ),
        ] {
            check(
                engine,
                compiler,
                source,
                expected_trace,
                ClosedVmValue::Scalar(42),
                "42",
            );
        }
    });
}

#[test]
fn discarded_and_repeated_thunk_computations_keep_the_native_optimizer_contract() {
    fixture(|engine, compiler| {
        // Native FIR deliberately preserves every written computation and its
        // observable evaluation count (fir/optimize.rs, and the analogous
        // discarded/repeated panic regression). The pin's CSE and elimDead
        // have a different diagnostic trace here. Record both explicitly;
        // memoization within one cell and resulting values still agree.
        for (source, pin_trace, native_trace) in [
            (
                r#"#eval let t := Thunk.mk (fun _ => dbg_trace "unused force"; 21); let _x := t.get; 42"#,
                "",
                "unused force\n",
            ),
            (
                r#"#eval let _t := Thunk.pure (dbg_trace "unused pure"; 21); 42"#,
                "",
                "unused pure\n",
            ),
            (
                r#"#eval let f := (fun _ : Unit => dbg_trace "shared callback"; 21); let a := Thunk.mk f; let b := Thunk.mk f; a.get + b.get"#,
                "shared callback\n",
                "shared callback\nshared callback\n",
            ),
        ] {
            pin(compiler, source, pin_trace, "42");
            check_native(engine, source, native_trace, ClosedVmValue::Scalar(42));
        }
    });
}
