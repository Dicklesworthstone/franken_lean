//! Task execution over actual pinned declarations. Raw artifact installation
//! is not module admission; each new source definition is checked normally.
#![forbid(unsafe_code)]

use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionLimits, Environment, IoEvaluationOutcome, KVMap,
    Name, OleanDecodeLimits,
};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::OnceLock;

const STACK: usize = 256 * 1024 * 1024;
const ACTION: &str = r#"def taskAction : BaseIO Nat := fun world =>
  match @BaseIO.asTask Nat
      (fun next => @ST.Out.mk IO.RealWorld Nat 41 next) 0 world with
  | .mk task next => @IO.wait Nat task next
#eval taskAction
"#;

const CARRIERS: &str = r#"
structure TaskPayload where
  count : Nat
  call : Nat → Nat

def pureTask : Nat → Task Nat := @Task.pure Nat
def getTask : Task Nat → Nat := @Task.get Nat
#eval let task := pureTask 21; let alias := task;
  Nat.add (getTask task) (getTask alias)
#eval (Task.pure (Task.pure 42)).get.get
#eval let task := Task.pure (fun value : Nat => Nat.succ value);
  Nat.add (task.get 20) (task.get 21)
#eval match Task.pure 41 with | .pure value => Nat.succ value

def recordTaskAction : BaseIO Nat := fun world =>
  match @BaseIO.asTask TaskPayload
      (fun next => @ST.Out.mk IO.RealWorld TaskPayload
        (TaskPayload.mk 40 (fun value => value)) next) 0 world with
  | .mk task next =>
    match @IO.wait TaskPayload task next with
    | .mk payload final =>
      @ST.Out.mk IO.RealWorld Nat (Nat.add payload.count (payload.call 2)) final
#eval recordTaskAction
"#;

const EFFECTS: &str = r#"
def taskEffectAction : BaseIO Nat :=
  ST.bind (ST.Prim.mkRef (σ := IO.RealWorld) (α := Nat) 0) (fun counter =>
    let action : BaseIO (Nat → Nat) :=
      ST.bind (ST.Prim.Ref.get counter) (fun count =>
        ST.bind (ST.Prim.Ref.set counter (Nat.succ count)) (fun _ =>
          ST.pure (fun value : Nat => Nat.add count value)))
    let launch := @BaseIO.asTask (Nat → Nat) action 0
    ST.bind (ST.Prim.Ref.get counter) (fun before =>
      ST.bind launch (fun task =>
        ST.bind (@IO.wait (Nat → Nat) task) (fun first =>
          ST.bind (ST.Prim.Ref.get counter) (fun afterFirst =>
            ST.bind (@IO.wait (Nat → Nat) task) (fun again =>
              ST.bind (ST.Prim.Ref.get counter) (fun afterWait =>
                ST.bind launch (fun secondTask =>
                  ST.bind (@IO.wait (Nat → Nat) secondTask) (fun second =>
                    ST.bind (ST.Prim.Ref.get counter) (fun afterSecond =>
                      ST.pure (Nat.add (Nat.mul before 1000000)
                        (Nat.add (Nat.mul afterFirst 10000)
                          (Nat.add (Nat.mul afterWait 1000)
                            (Nat.add (Nat.mul afterSecond 100)
                              (Nat.add (first 5) (Nat.add (again 5) (second 5)))))))))))))))))
#eval taskEffectAction
"#;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn fixture(test: impl FnOnce(&Engine, &Path) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            static FIXTURE: OnceLock<Option<(Engine, PathBuf)>> = OnceLock::new();
            let fixture = FIXTURE.get_or_init(|| {
                let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
                    assert!(
                        std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                        "the actual pinned Reference library is required"
                    );
                    eprintln!("SKIP: pinned Reference lib/lean is absent");
                    return None;
                };
                let compiler = std::env::var_os("FLN_REFERENCE_BIN")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| {
                        library.parent().unwrap().parent().unwrap().join("bin/lean")
                    });
                let mut environment = Environment::new();
                for module in [
                    "Init/Prelude",
                    "Init/Core",
                    "Init/System/ST",
                    "Init/System/IOError",
                    "Init/System/IO",
                ] {
                    let path = library.join(module).with_extension("olean");
                    let public = std::fs::read(&path).unwrap();
                    let server = std::fs::read(path.with_extension("olean.server")).unwrap();
                    let private = std::fs::read(path.with_extension("olean.private")).unwrap();
                    let decoded = fln::decode_olean_module_artifacts(
                        &public,
                        &server,
                        &private,
                        OleanDecodeLimits::new(STACK),
                    )
                    .unwrap();
                    for info in decoded.constants {
                        if !environment.contains(info.name()) {
                            environment = environment.add_decl(info).unwrap();
                        }
                    }
                }
                for target in [
                    "Nat.add",
                    "Nat.mul",
                    "Task.pure",
                    "Task.get",
                    "BaseIO.asTask",
                    "IO.wait",
                    "Void.mk",
                    "ST.Prim.mkRef",
                    "ST.Prim.Ref.get",
                    "ST.Prim.Ref.set",
                ] {
                    let row = fln_vm::extern_table_generated::EXTERN_ROWS
                        .iter()
                        .find(|row| row.name == target)
                        .unwrap();
                    environment = fln_elab::externs::register(
                        &environment,
                        &name(target),
                        vec![fln_elab::externs::ExternEntry::Standard {
                            backend: name("all"),
                            symbol: row.symbol.to_owned(),
                        }],
                    )
                    .unwrap();
                }
                Some((Engine::from_environment(environment), compiler))
            });
            if let Some((engine, compiler)) = fixture {
                test(engine, compiler);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn reference(compiler: &Path, source: &str, expected: &str) {
    let mut child = Command::new(compiler)
        .arg("--stdin")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(format!("prelude\nimport Init.System.IO\n{source}").as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(String::from_utf8_lossy(&output.stdout), expected);
    assert!(output.stderr.is_empty(), "{output:?}");
}

fn run(engine: &Engine, source: &str, expected: &[usize]) {
    let batch = engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(batch.batch.source_evaluation_indices.len(), expected.len());
    for (index, expected) in batch.batch.source_evaluation_indices.iter().zip(expected) {
        let execution = &batch.batch.executions[*index];
        let io = execution.io_evaluation_outcome().unwrap_or_else(|error| {
            panic!(
                "{source}\nevaluation {index}: {error:?}\nVM exit: {:?}",
                execution.exit
            )
        });
        let exit = match &io {
            Some(IoEvaluationOutcome::Returned { exit, .. }) => exit,
            None => &execution.exit,
            Some(other) => panic!("the BaseIO action must return: {other:?}"),
        };
        assert_eq!(
            fln::closed_vm_value(exit).unwrap(),
            Some(ClosedVmValue::Scalar(*expected)),
            "{source}\nevaluation {index}"
        );
    }
}

#[test]
fn checked_base_io_task_runs_at_action_invocation() {
    fixture(|engine, compiler| {
        reference(compiler, ACTION, "41\n");
        run(engine, ACTION, &[41]);
    });
}

#[test]
fn checked_tasks_recover_shared_nested_callable_and_record_payloads() {
    fixture(|engine, compiler| {
        reference(compiler, CARRIERS, "42\n42\n43\n42\n42\n");
        run(engine, CARRIERS, &[42, 42, 43, 42, 42]);
    });
}

#[test]
fn task_actions_are_deferred_reusable_and_wait_does_not_repeat_effects() {
    fixture(|engine, compiler| {
        // This raw fixture must retain arithmetic's real extern contracts.
        // Otherwise the large checksum can test recursive Nat model execution
        // instead of Task effect order. Check the emitted code without forcing
        // the parameterized probe or increasing the VM's recursion budget.
        let arithmetic = engine
            .execute_source_commands_with_checks(
                b"def taskChecksumArithmetic (value : Nat) : Nat := Nat.add (Nat.mul value 1000000) 10000\n",
                &KVMap::new(),
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        let program = fln_comp::flbc::decode_canonical(
            &arithmetic.batch.executions.last().unwrap().flbc_artifact,
            fln_comp::flbc::CodecLimits::default(),
        )
        .unwrap();
        let rows: std::collections::BTreeSet<_> = program
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter_map(|instruction| match instruction {
                fln_comp::flbc::Instruction::Intrinsic { row, .. } => Some(row.as_str()),
                _ => None,
            })
            .collect();
        for expected in ["extern:Nat.add", "extern:Nat.mul"] {
            assert!(rows.contains(expected), "missing {expected}: {rows:?}");
        }
        // Before invocation: 0; after first wait: 1; repeated wait: 1;
        // second action invocation: 2. The returned callables retain the
        // snapshots 0, 0, and 1, so applying each to 5 contributes 5+5+6.
        // Reading before applying the functions catches accidental callback
        // eta expansion which would postpone the action until application.
        reference(compiler, EFFECTS, "11216\n");
        run(engine, EFFECTS, &[11216]);
    });
}
