//! Native execution probes over four actual pinned artifacts. Raw dependency
//! installation is not module admission; every new source body still passes
//! both declaration checkers before runtime preparation and FLBC execution.

use super::*;
use fln_comp::flbc::{self, Instruction};
use fln_vm::interpreter::execute_cached;
use std::collections::BTreeSet;

const STACK: usize = 256 * 1024 * 1024;

fn run(engine: &Engine, source: &str) -> SourceCommandBatchExecution {
    engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn program(execution: &DefinitionExecution) -> flbc::ValidatedProgram {
    flbc::decode_canonical(&execution.flbc_artifact, flbc::CodecLimits::default()).unwrap()
}

fn assert_native_row(execution: &DefinitionExecution, operation: Operation) {
    let rows: BTreeSet<_> = program(execution)
        .functions()
        .iter()
        .flat_map(|function| &function.code)
        .filter_map(|instruction| match instruction {
            Instruction::Intrinsic { row, .. } if row.starts_with("extern:IO.") => {
                Some(row.clone())
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        rows,
        BTreeSet::from([format!(
            "extern:{}",
            operation.source_name().to_display_string()
        )]),
        "an opaque logical default cannot stand in for native execution"
    );
}

fn assert_native_invocations(
    execution: &DefinitionExecution,
    operation: Operation,
    expected_invocations: u64,
    check_exit: impl Fn(&VmExit),
) {
    let native = program(execution);
    let native_row = format!("extern:{}", operation.source_name().to_display_string());
    let mut control_functions = native.functions().to_vec();
    let mut replacements = 0;
    for function in &mut control_functions {
        for instruction in &mut function.code {
            if let Instruction::Intrinsic { dst, row, args, .. } = instruction
                && row == &native_row
            {
                assert!(args.is_empty(), "these observations take no ABI arguments");
                *instruction = Instruction::Nat {
                    dst: *dst,
                    value: 0,
                };
                replacements += 1;
            }
        }
    }
    assert!(replacements > 0, "the native artifact must contain the row");
    let control = flbc::validate(flbc::Program {
        schema_version: native.schema_version(),
        entry: native.entry(),
        functions: control_functions,
    })
    .expect("the false-valued control must pass the ordinary FLBC validator");

    // Both supported observations currently return false in Golem's entry
    // context. Replacing only their zero-argument instruction with that scalar
    // preserves control flow, instruction count, and all other cache lookups.
    // The difference therefore counts actual observation dispatches; merely
    // retaining an unused intrinsic row cannot satisfy an invocation check.
    let context = ExecutionCacheContext::new(
        ContentRoot::new(execution.base_logical_root.0.0),
        source_run_build_profile().0,
        execution.engine.mode(),
    );
    let mut native_caches = InlineCaches::try_new(256).unwrap();
    let mut control_caches = InlineCaches::try_new(256).unwrap();
    for replay in 1..=2 {
        let native_exit = execute_cached(
            &native,
            VmExecutionLimits::default(),
            None,
            context,
            &mut native_caches,
        )
        .into_complete()
        .unwrap();
        let control_exit = execute_cached(
            &control,
            VmExecutionLimits::default(),
            None,
            context,
            &mut control_caches,
        )
        .into_complete()
        .unwrap();
        check_exit(&native_exit);
        check_exit(&control_exit);
        let (VmExit::Returned(native_result), VmExit::Returned(control_result)) =
            (&native_exit, &control_exit)
        else {
            panic!("both validated artifacts must return");
        };
        assert_eq!(native_result.usage, control_result.usage);
        let native_stats = native_caches.stats();
        let control_stats = control_caches.stats();
        assert_eq!(native_stats.identity_fallbacks, 0);
        assert_eq!(control_stats.identity_fallbacks, 0);
        assert_eq!(native_stats.namespace_invalidations, 0);
        assert_eq!(control_stats.namespace_invalidations, 0);
        assert_eq!(
            native_stats.lookups.checked_sub(control_stats.lookups),
            Some(expected_invocations * replay),
            "cold and reused dispatch caches must execute each requested observation"
        );
    }
}

fn assert_deferred(execution: &DefinitionExecution, operation: Operation) {
    assert!(execution.io_evaluation_outcome().unwrap().is_none());
    let VmExit::Returned(returned) = &execution.exit else {
        panic!("an ordinary action definition must return a closure");
    };
    assert_eq!(vm_value_kind(&returned.value), VmValueKind::Closure);
    assert_native_row(execution, operation);
    assert_native_invocations(execution, operation, 0, |exit| {
        let VmExit::Returned(returned) = exit else {
            panic!("replaying an ordinary action definition must return a closure");
        };
        assert_eq!(vm_value_kind(&returned.value), VmValueKind::Closure);
    });
}

fn assert_result(execution: &DefinitionExecution, expected_type: &str, expected: usize) {
    assert_eq!(
        execution.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    let Some(IoEvaluationOutcome::Returned { runtime_type, exit }) =
        execution.io_evaluation_outcome().unwrap()
    else {
        panic!("an explicitly evaluated observation must return a logical IO result");
    };
    assert_eq!(runtime_type, c(expected_type));
    assert_eq!(
        closed_vm_value(&exit).unwrap(),
        Some(ClosedVmValue::Scalar(expected))
    );
}

fn assert_packet(exit: &VmExit, expected: usize) {
    let VmExit::Returned(returned) = exit else {
        panic!("the BaseIO adapter must return its logical ST/EST packet");
    };
    let packet = &returned.value;
    assert!(!packet.is_scalar());
    assert_eq!(packet.header().tag, 0);
    assert_eq!(packet.header().other, 2);
    let value = packet.try_ctor_child(0).expect("value field");
    let world = packet.try_ctor_child(1).expect("world field");
    assert!(value.is_scalar());
    assert_eq!(value.unbox(), expected);
    assert!(world.is_scalar());
    assert_eq!(world.unbox(), 0);
}

#[test]
fn native_base_io_observations_run_through_actions_aliases_and_io_lifting() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let environment = operations()
        .into_iter()
        .fold(raw, |environment, operation| {
            register(&environment, operation, false)
        });
    let engine = Engine::from_environment(environment);
    let root = engine.logical_root(&KVMap::new());
    for operation in operations() {
        let label = operation.source_name().to_display_string();
        let cases = [
            (format!("#eval {label}"), "Bool", 0, 1),
            (
                format!(
                    "def savedObservation : BaseIO Bool := {label}\n\
                     def observationAlias : BaseIO Bool := savedObservation\n\
                     #eval observationAlias"
                ),
                "Bool",
                0,
                1,
            ),
            (
                format!("#eval (show BaseIO Bool from fun world => {label} world)"),
                "Bool",
                0,
                1,
            ),
            (
                format!("#eval (show BaseIO Bool from let action := {label}; action)"),
                "Bool",
                0,
                1,
            ),
            (
                format!(
                    "#eval (show BaseIO Nat from fun world => \
                     let action := {label}; \
                     match action world with | .mk first next => \
                     match action next with | .mk second last => \
                     @ST.Out.mk IO.RealWorld Nat \
                     (match first with | true => 0 | false => \
                       match second with | true => 1 | false => 42) last)"
                ),
                "Nat",
                42,
                2,
            ),
            (format!("#eval (BaseIO.toIO {label})"), "Bool", 0, 1),
        ];
        for (source, expected_type, expected, invocations) in cases {
            let completed = run(&engine, &source);
            assert_eq!(completed.batch.source_evaluation_indices.len(), 1);
            let index = completed.batch.source_evaluation_indices[0];
            for deferred in &completed.batch.executions[..index] {
                assert_deferred(deferred, operation);
            }
            let execution = &completed.batch.executions[index];
            assert_result(execution, expected_type, expected);
            assert_packet(&execution.exit, expected);
            assert_native_row(execution, operation);

            let replay = execute_flbc_artifact(
                &execution.flbc_artifact,
                &KVMap::new(),
                FlbcExecutionLimits::default(),
            )
            .unwrap()
            .into_complete()
            .unwrap();
            assert_packet(&replay, expected);
            assert_native_invocations(execution, operation, invocations, |exit| {
                assert_packet(exit, expected)
            });
            let repeated = run(&engine, &source);
            let repeated_index = repeated.batch.source_evaluation_indices[0];
            assert_eq!(
                execution.flbc_artifact,
                repeated.batch.executions[repeated_index].flbc_artifact
            );
            assert_eq!(engine.logical_root(&KVMap::new()), root);
        }
    }
}

#[test]
fn native_observation_entrypoints_do_not_execute_missing_or_foreign_externs() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    for operation in operations() {
        let label = operation.source_name().to_display_string();
        for environment in [raw.clone(), register(&raw, operation, true)] {
            let engine = Engine::from_environment(environment);
            let root = engine.logical_root(&KVMap::new());
            for source in [
                format!("#eval {label}"),
                format!("#eval (show BaseIO Bool from fun world => {label} world)"),
            ] {
                let error = engine
                    .execute_source_commands_with_checks(
                        source.as_bytes(),
                        &KVMap::new(),
                        EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                    )
                    .expect_err("opaque defaults and foreign symbols have no native authority");
                let EngineExecutionError::BatchCommand { error, .. } = error else {
                    panic!("command-level native authority refusal");
                };
                assert!(matches!(*error, EngineExecutionError::Ingress(_)));
                assert_eq!(engine.logical_root(&KVMap::new()), root);
            }
        }
    }
}
