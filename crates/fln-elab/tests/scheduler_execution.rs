//! Real callback execution regressions for ordering, retries, and authority.
#![forbid(unsafe_code)]

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::time::Duration;

use fln_core::diag::ResourceReason;
use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_elab::dataflow::{CommandId, DataflowGraph, DataflowNode, ElabUnitProduct};
use fln_elab::effects::{CommandEffect, DeclAspect, EffectSummary};
use fln_elab::messages::Message;
use fln_elab::scheduler::{DeterministicScheduler, ExecutionConfig, SchedulerOutput};
use fln_env::constants::{ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::Environment;

type CommandOutcome = Outcome<Result<ElabUnitProduct, String>>;

fn name(value: &str) -> Name {
    Name::from_components([value])
}

fn effects(values: impl IntoIterator<Item = CommandEffect>) -> EffectSummary {
    let mut result = EffectSummary::new();
    for value in values {
        result.record(value);
    }
    result
}

fn read(value: &str) -> CommandEffect {
    CommandEffect::ReadsDecl { name: name(value), aspect: DeclAspect::All }
}

fn published(value: &str) -> ElabUnitProduct {
    let mut product = ElabUnitProduct::empty();
    product.admitted_decls.push(ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(value),
            level_params: Vec::new(),
            type_: Expr::sort(Level::succ(Level::zero()).unwrap()),
        },
        value: Expr::sort(Level::zero()),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: Vec::new(),
    }));
    product
}

fn counted(
    id: usize,
    calls: &Arc<AtomicUsize>,
    declared_effects: EffectSummary,
    body: impl Fn(&Environment, usize) -> CommandOutcome + Send + Sync + 'static,
) -> DataflowNode {
    let calls = Arc::clone(calls);
    DataflowNode {
        id: CommandId(id),
        name: None,
        declared_names: Vec::new(),
        referenced_names: Vec::new(),
        declared_effects,
        elab_fn: Arc::new(move |environment, _| {
            let attempt = calls.fetch_add(1, Ordering::SeqCst);
            body(environment, attempt)
        }),
    }
}

fn graph(nodes: Vec<DataflowNode>) -> DataflowGraph {
    let mut graph = DataflowGraph::new();
    for node in nodes {
        graph.add_node(node);
    }
    graph
}

fn config(worker_threads: usize) -> ExecutionConfig {
    ExecutionConfig { worker_threads, ..ExecutionConfig::default() }
}

fn run(graph: &DataflowGraph, workers: usize) -> SchedulerOutput {
    match DeterministicScheduler::execute(graph, &Environment::new(), &config(workers)) {
        Outcome::Complete(Ok(output)) => output,
        other => panic!("expected success, got {other:?}"),
    }
}

fn count(calls: &AtomicUsize) -> usize {
    calls.load(Ordering::SeqCst)
}

#[test]
fn declared_dependencies_execute_once_against_committed_predecessors() {
    for workers in [1, 8, 32] {
        let a_calls = Arc::new(AtomicUsize::new(0));
        let b_calls = Arc::new(AtomicUsize::new(0));
        let mut a = counted(0, &a_calls, EffectSummary::new(), |_, _| {
            Outcome::complete(Ok(published("A")))
        });
        a.name = Some(name("A"));
        let mut b = counted(1, &b_calls, effects([read("A")]), |environment, _| {
            if !environment.contains(&name("A")) {
                return Outcome::complete(Err("dependency ran too early".into()));
            }
            Outcome::complete(Ok(published("B")))
        });
        b.referenced_names.push(name("A"));
        let output = run(&graph(vec![a, b]), workers);
        assert!(output.final_environment.contains(&name("B")));
        assert_eq!(output.retry_count, 0);
        assert_eq!(count(&a_calls), 1);
        assert_eq!(count(&b_calls), 1);
    }
}

#[test]
fn barrier_runs_once_after_predecessors_and_before_successors() {
    let calls = (0..3).map(|_| Arc::new(AtomicUsize::new(0))).collect::<Vec<_>>();
    let state = Arc::new(AtomicUsize::new(0));
    let a = counted(0, &calls[0], EffectSummary::new(), |_, _| {
        Outcome::complete(Ok(published("A")))
    });
    let barrier_state = Arc::clone(&state);
    let barrier = counted(1, &calls[1], effects([CommandEffect::Opaque {
        reason: "ambient mutation".into(),
    }]), move |environment, _| {
        if !environment.contains(&name("A")) {
            return Outcome::complete(Err("barrier snapshot is stale".into()));
        }
        barrier_state.store(1, Ordering::SeqCst);
        Outcome::complete(Ok(ElabUnitProduct::empty()))
    });
    let after = counted(2, &calls[2], effects([CommandEffect::UsesCapability {
        capability_id: "ambient state".into(),
    }]), move |_, _| {
        if state.load(Ordering::SeqCst) != 1 {
            return Outcome::complete(Err("successor crossed barrier".into()));
        }
        Outcome::complete(Ok(ElabUnitProduct::empty()))
    });
    let output = run(&graph(vec![a, barrier, after]), 32);
    assert_eq!(output.committed_order, vec![CommandId(0), CommandId(1), CommandId(2)]);
    for calls in calls {
        assert_eq!(count(&calls), 1);
    }
}

#[test]
fn independent_commands_really_overlap_with_bounded_waits() {
    let (send_a, receive_a) = mpsc::channel();
    let (send_b, receive_b) = mpsc::channel();
    let receive_a = Mutex::new(receive_a);
    let receive_b = Mutex::new(receive_b);
    let calls = Arc::new(AtomicUsize::new(0));
    let a = counted(0, &calls, EffectSummary::new(), move |_, _| {
        send_a.send(()).unwrap();
        if receive_b.lock().unwrap().recv_timeout(Duration::from_secs(5)).is_err() {
            return Outcome::complete(Err("second worker never overlapped".into()));
        }
        Outcome::complete(Ok(ElabUnitProduct::empty()))
    });
    let b = counted(1, &calls, EffectSummary::new(), move |_, _| {
        send_b.send(()).unwrap();
        if receive_a.lock().unwrap().recv_timeout(Duration::from_secs(5)).is_err() {
            return Outcome::complete(Err("first worker never overlapped".into()));
        }
        Outcome::complete(Ok(ElabUnitProduct::empty()))
    });
    assert_eq!(run(&graph(vec![a, b]), 2).retry_count, 0);
    assert_eq!(count(&calls), 2);
}

#[test]
fn observed_read_rebases_against_actual_unlogged_publications() {
    let calls = Arc::new(AtomicUsize::new(0));
    let a = counted(0, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), |_, _| {
        // Neither name metadata nor dynamic WritesDecl advertises this write.
        Outcome::complete(Ok(published("A")))
    });
    let b = counted(1, &calls, EffectSummary::new(), |environment, _| {
        let mut product = ElabUnitProduct::empty();
        product.effects.record(read("A"));
        product.messages.push(Message::info(if environment.contains(&name("A")) {
            "present"
        } else {
            "absent"
        }));
        Outcome::complete(Ok(product))
    });
    let output = run(&graph(vec![a, b]), 8);
    assert_eq!(output.retry_count, 1);
    assert_eq!(count(&calls), 2);
    assert_eq!(output.messages[0].text, "present");
}

#[test]
fn unchanged_negative_query_does_not_force_a_retry() {
    let calls = Arc::new(AtomicUsize::new(0));
    let a = counted(0, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), |_, _| {
        Outcome::complete(Ok(ElabUnitProduct::empty()))
    });
    let b = counted(1, &calls, EffectSummary::new(), |environment, _| {
        assert!(!environment.contains(&name("missing")));
        let mut product = ElabUnitProduct::empty();
        product.effects.record(read("missing"));
        Outcome::complete(Ok(product))
    });
    let output = run(&graph(vec![a, b]), 8);
    assert_eq!(output.retry_count, 0);
    assert_eq!(count(&calls), 1);
}

#[test]
fn semantic_error_is_retried_only_after_snapshot_publications() {
    let calls = Arc::new(AtomicUsize::new(0));
    let a = counted(0, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), |_, _| {
        Outcome::complete(Ok(published("A")))
    });
    let b = counted(1, &calls, EffectSummary::new(), |environment, _| {
        if !environment.contains(&name("A")) {
            return Outcome::complete(Err("A not available".into()));
        }
        Outcome::complete(Ok(published("B")))
    });
    let output = run(&graph(vec![a, b]), 8);
    assert!(output.final_environment.contains(&name("B")));
    assert_eq!(output.retry_count, 1);
    assert_eq!(count(&calls), 2);
}

#[test]
fn stable_semantic_error_cannot_disappear_on_retry() {
    let calls = Arc::new(AtomicUsize::new(0));
    let a = counted(0, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), |_, _| {
        Outcome::complete(Ok(ElabUnitProduct::empty()))
    });
    let b = counted(1, &calls, EffectSummary::new(), |_, attempt| {
        if attempt == 0 {
            Outcome::complete(Err("original rejection".into()))
        } else {
            Outcome::complete(Ok(ElabUnitProduct::empty()))
        }
    });
    match DeterministicScheduler::execute(&graph(vec![a, b]), &Environment::new(), &config(8)) {
        Outcome::Complete(Err(error)) => assert_eq!(error, "original rejection"),
        other => panic!("rejection was lost: {other:?}"),
    }
    assert_eq!(count(&calls), 1);
}

#[test]
fn cancellation_resource_and_dependency_stops_are_preserved_without_retry() {
    let stops = [
        Inconclusive::cancelled("command B").with_progress("after type inference"),
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::ExecutionSteps,
            allowed: 10,
            observed: 11,
        }),
        Inconclusive::dependency_unavailable("imported authority"),
    ];
    for stop in stops {
        let calls = Arc::new(AtomicUsize::new(0));
        let a = counted(0, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), |_, _| {
            Outcome::complete(Ok(published("A")))
        });
        let expected = stop.clone();
        let b = counted(1, &calls, EffectSummary::new(), move |_, attempt| {
            if attempt == 0 {
                Outcome::Inconclusive(stop.clone())
            } else {
                Outcome::complete(Ok(ElabUnitProduct::empty()))
            }
        });
        match DeterministicScheduler::execute(&graph(vec![a, b]), &Environment::new(), &config(8)) {
            Outcome::Inconclusive(actual) => assert_eq!(actual, expected),
            other => panic!("non-answer was lost: {other:?}"),
        }
        assert_eq!(count(&calls), 1);
    }
}

#[test]
fn internal_fault_and_its_evidence_are_not_discarded() {
    let calls = Arc::new(AtomicUsize::new(0));
    let a = counted(0, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), |_, _| {
        Outcome::complete(Ok(published("A")))
    });
    let expected = InternalFault::new("FL-INV-01", "broken witness").with_evidence("witness.log");
    let fault = expected.clone();
    let b = counted(1, &calls, EffectSummary::new(), move |_, attempt| {
        if attempt == 0 {
            Outcome::InternalFault(fault.clone())
        } else {
            Outcome::complete(Ok(ElabUnitProduct::empty()))
        }
    });
    match DeterministicScheduler::execute(&graph(vec![a, b]), &Environment::new(), &config(8)) {
        Outcome::InternalFault(actual) => assert_eq!(actual, expected),
        other => panic!("internal fault was lost: {other:?}"),
    }
    assert_eq!(count(&calls), 1);
}

#[test]
fn callback_panics_remain_internal_faults_in_both_execution_modes() {
    for workers in [1, 8] {
        let calls = Arc::new(AtomicUsize::new(0));
        let a = counted(0, &calls, EffectSummary::new(), |_, _| panic!("callback probe"));
        let b = counted(1, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), |_, _| {
            Outcome::complete(Ok(ElabUnitProduct::empty()))
        });
        assert!(matches!(
            DeterministicScheduler::execute(&graph(vec![a, b]), &Environment::new(), &config(workers)),
            Outcome::InternalFault(_)
        ));
        assert_eq!(count(&calls), 1);
    }
}

#[test]
fn duplicate_command_ids_are_rejected_before_any_side_effects() {
    for workers in [1, 8] {
        let calls = Arc::new(AtomicUsize::new(0));
        let nodes = (0..2).map(|_| counted(7, &calls, EffectSummary::new(), |_, _| {
            Outcome::complete(Ok(ElabUnitProduct::empty()))
        })).collect();
        assert!(matches!(
            DeterministicScheduler::execute(&graph(nodes), &Environment::new(), &config(workers)),
            Outcome::Complete(Err(_))
        ));
        assert_eq!(count(&calls), 0);
    }
}

#[test]
fn undeclared_nonreplayable_effect_is_refused_instead_of_repeated() {
    let calls = Arc::new(AtomicUsize::new(0));
    let a = counted(0, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), |_, _| {
        Outcome::complete(Ok(published("A")))
    });
    let b = counted(1, &calls, EffectSummary::new(), |_, _| {
        let mut product = ElabUnitProduct::empty();
        product.effects.record(CommandEffect::UsesCapability { capability_id: "io".into() });
        Outcome::complete(Ok(product))
    });
    assert!(matches!(
        DeterministicScheduler::execute(&graph(vec![a, b]), &Environment::new(), &config(8)),
        Outcome::InternalFault(_)
    ));
    assert_eq!(count(&calls), 1);
}

#[test]
fn failed_barrier_does_not_launch_later_commands() {
    let calls = Arc::new(AtomicUsize::new(0));
    let barrier = counted(0, &Arc::new(AtomicUsize::new(0)), effects([CommandEffect::Opaque {
        reason: "barrier".into(),
    }]), |_, _| Outcome::complete(Err("stop here".into())));
    let after = counted(1, &calls, EffectSummary::new(), |_, _| {
        Outcome::complete(Ok(ElabUnitProduct::empty()))
    });
    assert!(matches!(
        DeterministicScheduler::execute(&graph(vec![barrier, after]), &Environment::new(), &config(8)),
        Outcome::Complete(Err(_))
    ));
    assert_eq!(count(&calls), 0);
}

#[test]
fn thread_matrix_preserves_canonical_results_and_source_order() {
    let nodes = [40, 3, 19].into_iter().map(|id| {
        counted(id, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), move |_, _| {
            let mut product = published(&format!("D{id}"));
            product.messages.push(Message::info(format!("command {id}")));
            Outcome::complete(Ok(product))
        })
    }).collect();
    let graph = graph(nodes);
    let sequential = run(&graph, 1);
    for workers in [2, 8, 32] {
        let output = run(&graph, workers);
        assert_eq!(output.committed_order, vec![CommandId(40), CommandId(3), CommandId(19)]);
        assert_eq!(output.messages, sequential.messages);
        assert_eq!(output.info_trees, sequential.info_trees);
        assert_eq!(output.decisions, sequential.decisions);
        assert_eq!(output.effects, sequential.effects);
        assert_eq!(output.final_environment.logical_root(&KVMap::new()),
            sequential.final_environment.logical_root(&KVMap::new()));
    }
}

#[test]
fn enormous_worker_request_is_bounded_by_actual_ready_work() {
    let calls = Arc::new(AtomicUsize::new(0));
    let nodes = (0..2).map(|id| counted(id, &calls, EffectSummary::new(), |_, _| {
        Outcome::complete(Ok(ElabUnitProduct::empty()))
    })).collect();
    assert_eq!(run(&graph(nodes), usize::MAX).committed_order.len(), 2);
    assert_eq!(count(&calls), 2);
}

#[test]
fn grammar_and_instance_writers_execute_once_without_speculation() {
    for effect in [
        CommandEffect::WritesGrammar { category: name("term") },
        CommandEffect::WritesInstance { class_head: name("C"), instance_name: name("i") },
    ] {
        let calls = Arc::new(AtomicUsize::new(0));
        let a = counted(0, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), |_, _| {
            Outcome::complete(Ok(published("A")))
        });
        let b = counted(1, &calls, effects([effect.clone()]), move |environment, _| {
            assert!(environment.contains(&name("A")));
            let mut product = ElabUnitProduct::empty();
            product.effects.record(effect.clone());
            Outcome::complete(Ok(product))
        });
        assert_eq!(run(&graph(vec![a, b]), 8).retry_count, 0);
        assert_eq!(count(&calls), 1);
    }
}
