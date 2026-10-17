//! Bounded imported folds retain source authority and VM resource accounting.
use super::*;
use fln::{
    ClosedVmValue, EngineAdmissionLimits, EngineExecutionLimits, FlbcExecutionLimits,
    SourceCheckLimits, VmExit,
};

const ROLLBACK_PREFIX: &str = r#"
def foldPrepared (xs : Array Nat) : Id Nat :=
  Array.foldlM (m := Id)
    (fun (acc : Nat) (x : Nat) => Pure.pure (acc * 10 + x)) (4 : Nat) xs
"#;

const INVALID_CALLBACK: &str = r#"
def foldIllTyped (xs : Array Nat) : Id Nat :=
  Array.foldlM (m := Id)
    (fun (_acc : Nat) (_x : Nat) => Pure.pure Bool.true) (0 : Nat) xs
"#;

const BUDGET_DEFINITION: &str = r#"
def foldBudget (xs : Array Nat) : Id Nat :=
  Array.foldlM (m := Id)
    (fun (acc : Nat) (x : Nat) => Pure.pure (acc * 10 + x)) (0 : Nat) xs
"#;

pub(super) fn exact_model(engine: &Engine) {
    let environment = engine.environment();
    let implementations = fln_elab::implemented_by::ImplementedByTable::read(environment).unwrap();
    let externs = fln_elab::externs::ExternTable::read(environment).unwrap();
    let dependencies = dependencies_from_roots(
        environment,
        &implementations,
        &[
            "Array.foldlM",
            "Array.foldlMUnsafe",
            "List.foldlM",
            "List.extract",
            "Array",
            "List",
            "Monad",
        ],
    );
    // Derive the full closure from actual admitted bodies and journals,
    // independently of which rows the checked-in runtime model lists.
    let actual: BTreeMap<_, _> = dependencies
        .iter()
        .map(|label| {
            let encoded = encoded_name(label);
            let implementation = implementations
                .get(label)
                .map(encoded_name)
                .unwrap_or_else(|| "-".to_owned());
            let native = if externs.get(label).is_some() {
                "extern"
            } else {
                "-"
            };
            let companion = potential_companion(environment.find(label).unwrap())
                .filter(|candidate| environment.contains(candidate))
                .map(|candidate| encoded_name(&candidate))
                .unwrap_or_else(|| "-".to_owned());
            let digest = environment.entry(label).unwrap().digest().to_hex();
            let row = format!("{encoded}\t{digest}\t{implementation}\t{native}\t{companion}");
            (encoded, row)
        })
        .collect();
    assert_eq!(
        actual.len(),
        dependencies.len(),
        "dependency names are unique"
    );
    let mut expected = BTreeMap::new();
    for line in include_str!("../../src/source_intrinsics/array_fold/dependencies.txt").lines() {
        let columns: Vec<_> = line.split('\t').collect();
        assert_eq!(columns.len(), 5, "the complete runtime model row: {line}");
        assert!(
            expected
                .insert(columns[0].to_owned(), line.to_owned())
                .is_none(),
            "the runtime model must not repeat dependency {}",
            columns[0],
        );
    }
    assert_eq!(
        actual, expected,
        "every actual Array fold dependency, digest, replacement, extern and companion must be bound",
    );
}

pub(super) fn source_rollback(engine: &Engine) {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let source = format!("{ROLLBACK_PREFIX}{INVALID_CALLBACK}");
    let error = engine
        .check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))),
        )
        .expect_err("Array.foldlM must check the callback's actual return type");
    let diagnostic = format!("{error:?}");
    let fln::source_check::SourceCheckError::Command {
        command: 1,
        error: command_error,
        ..
    } = &error
    else {
        panic!("the valid prefix must check before the callback is refused: {diagnostic}");
    };
    let mut cause = command_error.as_ref();
    while let fln::EngineExecutionError::BatchCommand { error, .. } = cause {
        cause = error;
    }
    assert!(
        matches!(
            cause,
            fln::EngineExecutionError::Frontend(
                fln_elab::DefinitionFrontendError::Elaborate(
                    fln_elab::NatDefinitionElabError::Inference(
                        fln_elab::source::SourceInferenceError::TypeMismatch { actual, expected }
                    )
                )
            ) if actual.contains("Bool") && expected.contains("Nat")
        ),
        "the callback must fail specifically because Bool is not Nat: {diagnostic}",
    );
    assert_eq!(engine.logical_root(&options), before);
    for label in ["foldPrepared", "foldIllTyped"] {
        assert!(
            !engine.environment().contains(&name(label)),
            "the failed batch must not publish {label}",
        );
    }

    let recovery = format!(
        "{ROLLBACK_PREFIX}-- FLN_EXPECT_NAT 4123\n#eval foldPrepared (List.toArray [1, 2, 3])\n"
    );
    super::execution::program(engine, "Array fold source rollback recovery", &recovery, 1);
    assert_eq!(engine.logical_root(&options), before);
}

pub(super) fn execution_budget(engine: &Engine) {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let idle_source =
        format!("{BUDGET_DEFINITION}def foldAnswer : Nat := foldBudget (List.toArray [])\n");
    let full_source = format!(
        "{BUDGET_DEFINITION}def foldAnswer : Nat := foldBudget (List.toArray [1, 2, 3, 4, 5, 6, 7, 8])\n"
    );
    let idle = engine
        .execute_source_definitions(
            &[idle_source.as_bytes()],
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .expect("the imported fold checks before executing its empty interval")
        .into_complete()
        .expect("the empty interval finishes");
    let idle_exit = &idle.executions.last().expect("empty-fold execution").exit;
    assert_eq!(
        fln::closed_vm_value(idle_exit).expect("normal empty-fold VM exit"),
        Some(ClosedVmValue::Scalar(0)),
    );
    let VmExit::Returned(idle_result) = idle_exit else {
        panic!("the empty fold must return");
    };
    let idle_steps = idle_result.usage.steps;
    assert!(idle_steps > 0, "the control establishes a finite VM limit");

    let mut bounded = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
    bounded.vm.max_steps = idle_steps;
    let stopped = engine
        .execute_source_definitions(&[full_source.as_bytes()], &options, bounded)
        .expect("the fold and callback pass both checkers before the VM stops");
    assert!(matches!(
        stopped,
        fln::Outcome::Inconclusive(stop) if matches!(stop.cause,
            fln_core::outcome::InconclusiveCause::ResourceExhausted { ref usage }
                if usage.reason == fln_core::diag::ResourceReason::ExecutionSteps
                    && usage.allowed == idle_steps && usage.observed == idle_steps + 1)
    ));
    assert_eq!(engine.logical_root(&options), before);
    for label in ["foldBudget", "foldAnswer"] {
        assert!(
            !engine.environment().contains(&name(label)),
            "VM exhaustion must not publish {label}",
        );
    }

    let recovered = engine
        .execute_source_definitions(
            &[full_source.as_bytes()],
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .expect("a bounded stop leaves a clean retry")
        .into_complete()
        .expect("the same checked fold completes with the normal budget");
    let execution = recovered
        .executions
        .last()
        .expect("recovered fold execution");
    assert_eq!(
        fln::closed_vm_value(&execution.exit).expect("normal recovered VM exit"),
        Some(ClosedVmValue::Scalar(12_345_678)),
    );
    let VmExit::Returned(recovered_result) = &execution.exit else {
        panic!("the recovered fold must return");
    };
    assert!(recovered_result.usage.steps > idle_steps);

    let mut replay_limits = FlbcExecutionLimits::default();
    replay_limits.vm.max_steps = idle_steps;
    let replay_stopped =
        fln::execute_flbc_artifact(&execution.flbc_artifact, &options, replay_limits)
            .expect("the independent decoder accepts the exact checked artifact");
    assert!(matches!(
        replay_stopped,
        fln::Outcome::Inconclusive(stop) if matches!(stop.cause,
            fln_core::outcome::InconclusiveCause::ResourceExhausted { ref usage }
                if usage.reason == fln_core::diag::ResourceReason::ExecutionSteps
                    && usage.allowed == idle_steps && usage.observed == idle_steps + 1)
    ));
    let replay = fln::execute_flbc_artifact(
        &execution.flbc_artifact,
        &options,
        FlbcExecutionLimits::default(),
    )
    .expect("a stopped replay does not corrupt the serialized fold")
    .into_complete()
    .expect("the fresh independent replay completes with the normal budget");
    assert_eq!(
        fln::closed_vm_value(&replay).expect("normal recovered FLBC exit"),
        Some(ClosedVmValue::Scalar(12_345_678)),
    );
    let VmExit::Returned(replayed_result) = replay else {
        panic!("the independent replay must return");
    };
    assert_eq!(
        replayed_result.usage.steps, recovered_result.usage.steps,
        "the same artifact retains exact VM instruction accounting",
    );
    assert_eq!(engine.logical_root(&options), before);
}
