//! Task execution over actual pinned declarations. Raw artifact installation
//! is not module admission; each new source definition is checked normally.
#![forbid(unsafe_code)]

use fln::{
    BinderInfo, Budget, CheckerAdmissionGround, ClosedVmValue, ConstantInfo, Declaration, Engine,
    EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits, Environment, Expr,
    IngressError, IoEvaluationOutcome, KVMap, Name, OleanDecodeLimits, VmExit,
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

const PURE_COMPOSITION: &str = r#"
#eval (Task.spawn (fun _ => 41)).get
#eval (Task.map (fun value : Nat => Nat.succ value) (Task.pure 41) 0 true).get
#eval (Task.bind (Task.pure 41) (fun value => Task.pure (Nat.succ value)) 0 true).get
#eval (Task.spawn (fun _ => fun value : Nat => Nat.succ value)).get 41
#eval let task := Task.map (fun value : Nat => fun extra : Nat => Nat.add value extra) (Task.pure 40) 0 true
  Nat.add (task.get 1) (task.get 1)
#eval (Task.bind (Task.pure 40) (fun value => Task.pure (fun extra : Nat => Nat.add value extra)) 0 true).get 2

"#;

const IO_COMPOSITION: &str = r#"def composedTask : BaseIO Nat := fun world =>
  match @BaseIO.mapTask Nat Nat
      (fun value next => @ST.Out.mk IO.RealWorld Nat (Nat.succ value) next)
      (Task.pure 40) 0 true world with
  | .mk first next =>
    match @BaseIO.bindTask Nat Nat first
        (fun value after => @ST.Out.mk IO.RealWorld (Task Nat)
          (Task.pure (Nat.succ value)) after) 0 true next with
    | .mk second final => @IO.wait Nat second final
#eval composedTask
"#;

const COMPOSITION_EFFECTS: &str = r#"
def taskMapBump (counter : ST.Ref IO.RealWorld Nat) (base : Nat) : BaseIO (Nat → Nat) :=
  ST.bind (ST.Prim.Ref.get counter) (fun count =>
    ST.bind (ST.Prim.Ref.set counter (Nat.succ count)) (fun _ =>
      ST.pure (fun extra : Nat => Nat.add base (Nat.add count extra))))

def taskBindBump (counter : ST.Ref IO.RealWorld Nat) (value : Nat → Nat) : BaseIO (Task (Nat → Nat)) :=
  ST.bind (ST.Prim.Ref.get counter) (fun count =>
    ST.bind (ST.Prim.Ref.set counter (Nat.succ count)) (fun _ =>
      ST.pure (Task.pure (fun extra : Nat => Nat.add (value extra) count))))

def taskCompositionEffects : BaseIO Nat := fun world =>
  match ST.Prim.mkRef (σ := IO.RealWorld) (α := Nat) 0 world with
  | .mk counter w1 =>
    let mapAction := @BaseIO.mapTask Nat (Nat → Nat)
      (taskMapBump counter) (Task.pure 10) 0 true
    match ST.Prim.Ref.get counter w1 with
    | .mk before w2 =>
      match mapAction w2 with
      | .mk mapped w3 =>
        match ST.Prim.Ref.get counter w3 with
        | .mk afterMap w4 =>
          match @IO.wait (Nat → Nat) mapped w4 with
          | .mk first w5 =>
            match @IO.wait (Nat → Nat) mapped w5 with
            | .mk again w6 =>
              match ST.Prim.Ref.get counter w6 with
              | .mk afterWait w7 =>
                let bindAction := @BaseIO.bindTask (Nat → Nat) (Nat → Nat)
                  mapped (taskBindBump counter) 0 true
                match ST.Prim.Ref.get counter w7 with
                | .mk beforeBind w8 =>
                  match bindAction w8 with
                  | .mk bound w9 =>
                    match ST.Prim.Ref.get counter w9 with
                    | .mk afterBind w10 =>
                      match @IO.wait (Nat → Nat) bound w10 with
                      | .mk second w11 =>
                        match @IO.wait (Nat → Nat) bound w11 with
                        | .mk secondAgain w12 =>
                          match bindAction w12 with
                          | .mk lastTask w13 =>
                            match ST.Prim.Ref.get counter w13 with
                            | .mk afterSecond w14 =>
                              match @IO.wait (Nat → Nat) lastTask w14 with
                              | .mk last final =>
                                let c0 := Nat.mul before 10000000
                                let c1 := Nat.add c0 (Nat.mul afterMap 1000000)
                                let c2 := Nat.add c1 (Nat.mul afterWait 100000)
                                let c3 := Nat.add c2 (Nat.mul beforeBind 10000)
                                let c4 := Nat.add c3 (Nat.mul afterBind 1000)
                                let c5 := Nat.add c4 (Nat.mul afterSecond 100)
                                let values := Nat.add (first 1) (Nat.add (again 1)
                                  (Nat.add (second 1) (Nat.add (secondAgain 1) (last 1))))
                                @ST.Out.mk IO.RealWorld Nat (Nat.add c5 values) final
#eval taskCompositionEffects
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
                    "Task.spawn",
                    "Task.map",
                    "Task.bind",
                    "BaseIO.asTask",
                    "BaseIO.mapTask",
                    "BaseIO.bindTask",
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

#[test]
fn checked_pure_task_combinators_retain_callable_payloads() {
    fixture(|engine, compiler| {
        reference(compiler, PURE_COMPOSITION, "41\n42\n42\n42\n82\n42\n");
        run(engine, PURE_COMPOSITION, &[41, 42, 42, 42, 82, 42]);
    });
}

#[test]
fn checked_base_io_tasks_map_and_bind_native_payloads() {
    fixture(|engine, compiler| {
        for source in [
            IO_COMPOSITION.to_owned(),
            IO_COMPOSITION.replace("0 true", "0 false"),
        ] {
            reference(compiler, &source, "42\n");
            run(engine, &source, &[42]);
        }
    });
}

#[test]
fn task_composition_actions_defer_effects_and_retain_completed_payloads() {
    fixture(|engine, compiler| {
        // Constructing map/bind actions leaves the counter alone. Running map
        // increments it once; waits reuse that result. Running the same bind
        // action twice advances it twice and snapshots each callback's result.
        // Read the counter before applying the returned functions, so moving
        // any action's work under the function payload cannot pass this test.
        reference(compiler, COMPOSITION_EFFECTS, "1112359\n");
        run(engine, COMPOSITION_EFFECTS, &[1112359]);
    });
}

fn task_contract_refusal(engine: &Engine, source: &str, expected: &'static str) {
    let mut error = match engine.execute_source_commands_with_checks(
        source.as_bytes(),
        &KVMap::new(),
        EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
    ) {
        Err(error) => error,
        Ok(_) => panic!("expected {expected:?} for {source}"),
    };
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    assert_eq!(
        error,
        EngineExecutionError::Ingress(IngressError::UnsupportedNode { kind: expected }),
        "{source}"
    );
}

fn changed_checked_task_body(engine: &Engine, target: &str) -> Engine {
    let target = name(target);
    let original = engine.environment();
    let mut candidate = original.find(&target).unwrap().clone();
    let wrap = |type_: &Expr, body: &Expr| {
        Expr::app(
            Expr::lam(
                name("retainTaskModel"),
                type_.clone(),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            body.clone(),
        )
    };
    let declaration = match &mut candidate {
        ConstantInfo::Opaque(value) => {
            value.value = wrap(&value.base.type_, &value.value);
            Declaration::Opaque(value.clone())
        }
        ConstantInfo::Defn(value) => {
            value.value = wrap(&value.base.type_, &value.value);
            Declaration::Defn(value.clone())
        }
        _ => unreachable!("an actual Task operation has a checked body"),
    };
    let mut environment = Environment::new();
    for (label, _) in original.constants() {
        if label != &target {
            environment = environment
                .with_entry(original.entry(label).unwrap())
                .unwrap();
        }
    }
    for (journal, state) in original.extensions() {
        environment = environment
            .register_extension(state.descriptor.clone())
            .unwrap();
        for entry in state.entries() {
            environment = environment
                .push_extension_entry(journal, entry.payload.clone())
                .unwrap();
        }
    }
    // Identity application changes serialization while preserving the entire
    // type and logical value. Both ordinary checkers must admit that change;
    // a checker rejection is not evidence for native contract authentication.
    let admitted = Engine::from_environment(environment)
        .admit_declaration(
            declaration,
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        admitted.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    admitted.engine
}

#[test]
fn public_task_execution_authenticates_externs_and_checked_model_bodies() {
    fixture(|engine, _| {
        const PURE: &str = "def taskContractProbe (value : Nat) : Task Nat := Task.pure value\n";
        const GET: &str = "def taskContractProbe (task : Task Nat) : Nat := Task.get task\n";
        const AS_TASK: &str = "def taskContractProbe (_ : Nat) : BaseIO (Task Nat) := @BaseIO.asTask Nat (fun world => @ST.Out.mk IO.RealWorld Nat 41 world) 0\n";
        const WAIT: &str =
            "def taskContractProbe (task : Task Nat) : BaseIO Nat := @IO.wait Nat task\n";
        const MAP: &str = "def taskContractProbe (task : Task Nat) : BaseIO (Task Nat) := @BaseIO.mapTask Nat Nat (fun value world => @ST.Out.mk IO.RealWorld Nat value world) task 0 true\n";
        const BIND: &str = "def taskContractProbe (task : Task Nat) : BaseIO (Task Nat) := @BaseIO.bindTask Nat Nat task (fun value world => @ST.Out.mk IO.RealWorld (Task Nat) (Task.pure value) world) 0 true\n";
        let operations = [
            ("Task.pure", PURE),
            ("Task.get", GET),
            ("BaseIO.asTask", AS_TASK),
            ("IO.wait", WAIT),
            ("BaseIO.mapTask", MAP),
            ("BaseIO.bindTask", BIND),
        ];
        // Every unchanged source is admitted and compiled before its negative
        // case. Definitions return closures; no action or task callback runs.
        for (_, source) in operations {
            let control = engine
                .execute_source_commands_with_checks(
                    source.as_bytes(),
                    &KVMap::new(),
                    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .unwrap_or_else(|error| panic!("{source}: {error:?}"))
                .into_complete()
                .unwrap();
            assert!(control.batch.source_evaluation_indices.is_empty());
            assert_eq!(control.batch.executions.len(), 1);
            let VmExit::Returned(value) = &control.batch.executions[0].exit else {
                panic!("the positive contract probe must return its closure")
            };
            assert!(value.value.closure_shell_parts().is_some(), "{source}");
        }
        for (target, source) in operations.into_iter().chain([
            ("Task.pure", GET),
            ("Task.Priority", AS_TASK),
            ("Task.Priority", MAP),
            ("Task.Priority", BIND),
            ("Task.get", WAIT),
            ("Task.get", MAP),
            ("Task.get", BIND),
        ]) {
            let decorated = Engine::from_environment(
                fln_elab::externs::register(
                    engine.environment(),
                    &name(target),
                    vec![fln_elab::externs::ExternEntry::Standard {
                        backend: name("all"),
                        symbol: "foreign_task_contract".to_owned(),
                    }],
                )
                .unwrap(),
            );
            task_contract_refusal(
                &decorated,
                source,
                "native extern attribute does not match the supported ABI",
            );
        }
        for (target, source) in [("BaseIO.mapTask", MAP), ("BaseIO.bindTask", BIND)] {
            task_contract_refusal(
                &changed_checked_task_body(engine, target),
                source,
                "native Task differs from its complete checked logical contract",
            );
        }
        let getter = changed_checked_task_body(engine, "Task.get");
        for source in [GET, WAIT, MAP, BIND] {
            task_contract_refusal(
                &getter,
                source,
                "native Task differs from its complete checked logical contract",
            );
        }
    });
}
