//! Incremental reuse must have the same authority and outputs as a cold run.
#![forbid(unsafe_code)]

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
use fln_elab::dataflow::{CommandId, DataflowGraph, DataflowNode, ElabUnitProduct};
use fln_elab::effects::{CommandEffect, DeclAspect, EffectSummary};
use fln_elab::decision::DecisionRecord;
use fln_elab::info::{Info, InfoTree};
use fln_elab::messages::Message;
use fln_elab::scheduler::{DeterministicScheduler, IncrementalOutput, IncrementalScheduler};
use fln_elab::txn::ElabBudget;
use fln_env::constants::{ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::Environment;

type CommandOutcome = Outcome<Result<ElabUnitProduct, String>>;

fn name(value: &str) -> Name {
    Name::from_components([value])
}

fn effects(values: impl IntoIterator<Item = CommandEffect>) -> EffectSummary {
    let mut summary = EffectSummary::new();
    for value in values {
        summary.record(value);
    }
    summary
}

fn read(value: &str) -> CommandEffect {
    CommandEffect::ReadsDecl { name: name(value), aspect: DeclAspect::All }
}

fn published(value: &str, revision: usize) -> ElabUnitProduct {
    let mut level = Level::zero();
    for _ in 0..revision {
        level = Level::succ(level).unwrap();
    }
    let mut product = ElabUnitProduct::empty();
    product.admitted_decls.push(ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(value),
            level_params: Vec::new(),
            type_: Expr::sort(Level::succ(level.clone()).unwrap()),
        },
        value: Expr::sort(level),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: Vec::new(),
    }));
    product.messages.push(Message::info(format!("{value}:{revision}")));
    product.info_tree = Some(InfoTree::Node(
        Info::CommandInfo { name: name(value) },
        Vec::new(),
    ));
    product.decisions.push(DecisionRecord::OverloadChoice {
        candidate_name: name(value),
        index: 0,
        total_candidates: 1,
    });
    product
}

fn command(
    id: usize,
    calls: &Arc<AtomicUsize>,
    declared_effects: EffectSummary,
    body: impl Fn(&Environment) -> CommandOutcome + Send + Sync + 'static,
) -> DataflowNode {
    let calls = Arc::clone(calls);
    DataflowNode {
        id: CommandId(id),
        name: None,
        declared_names: Vec::new(),
        referenced_names: Vec::new(),
        declared_effects,
        elab_fn: Arc::new(move |environment, _| {
            calls.fetch_add(1, Ordering::SeqCst);
            body(environment)
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

fn execute(
    cache: &mut IncrementalScheduler,
    graph: &DataflowGraph,
    changed: &[CommandId],
) -> IncrementalOutput {
    match cache.execute(graph, changed, &ElabBudget::default()) {
        Outcome::Complete(Ok(output)) => output,
        other => panic!("expected complete incremental output: {other:?}"),
    }
}

fn counts(n: usize) -> Vec<Arc<AtomicUsize>> {
    (0..n).map(|_| Arc::new(AtomicUsize::new(0))).collect()
}

fn snapshot(calls: &[Arc<AtomicUsize>]) -> Vec<usize> {
    calls.iter().map(|counter| counter.load(Ordering::SeqCst)).collect()
}

fn simple_nodes(calls: &[Arc<AtomicUsize>]) -> Vec<DataflowNode> {
    ["A", "B", "C"].into_iter().enumerate().map(|(id, label)| {
        let mut node = command(id, &calls[id], EffectSummary::new(), move |_| {
            Outcome::complete(Ok(published(label, 0)))
        });
        node.name = Some(name(label));
        node
    }).collect()
}

#[test]
fn warm_run_reuses_every_product_and_replays_canonical_outputs() {
    let calls = counts(3);
    let graph = graph(simple_nodes(&calls));
    let mut cache = IncrementalScheduler::new(&Environment::new());
    let cold = execute(&mut cache, &graph, &[]);
    let warm = execute(&mut cache, &graph, &[]);
    assert_eq!(cold.executed_commands, vec![CommandId(0), CommandId(1), CommandId(2)]);
    assert!(warm.executed_commands.is_empty());
    assert_eq!(warm.reused_commands, cold.executed_commands);
    assert_eq!(snapshot(&calls), vec![1, 1, 1]);
    assert_eq!(warm.output.messages, cold.output.messages);
    assert_eq!(warm.output.effects, cold.output.effects);
    assert_eq!(warm.output.info_trees, cold.output.info_trees);
    assert_eq!(warm.output.decisions, cold.output.decisions);
    assert_eq!(warm.output.final_environment.logical_root(&KVMap::new()),
        cold.output.final_environment.logical_root(&KVMap::new()));
}

#[test]
fn explicit_edit_reexecutes_the_observed_dependency_cone_only() {
    let calls = counts(4);
    let revision = Arc::new(AtomicUsize::new(0));
    let source_revision = Arc::clone(&revision);
    let a = command(0, &calls[0], EffectSummary::new(), move |_| {
        Outcome::complete(Ok(published("A", source_revision.load(Ordering::SeqCst))))
    });
    let b = command(1, &calls[1], EffectSummary::new(), |environment| {
        assert!(environment.contains(&name("A")));
        let mut product = published("B", 0);
        product.effects.record(read("A"));
        Outcome::complete(Ok(product))
    });
    let c = command(2, &calls[2], EffectSummary::new(), |environment| {
        assert!(environment.contains(&name("B")));
        let mut product = published("C", 0);
        product.effects.record(read("B"));
        Outcome::complete(Ok(product))
    });
    let unrelated = command(3, &calls[3], EffectSummary::new(), |_| {
        Outcome::complete(Ok(published("D", 0)))
    });
    let graph = graph(vec![a, b, c, unrelated]);
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &graph, &[]);
    revision.store(1, Ordering::SeqCst);
    let updated = execute(&mut cache, &graph, &[CommandId(0)]);
    assert_eq!(updated.executed_commands, vec![CommandId(0), CommandId(1), CommandId(2)]);
    assert_eq!(updated.reused_commands, vec![CommandId(3)]);
    assert_eq!(snapshot(&calls), vec![2, 2, 2, 1]);
    let cold = match DeterministicScheduler::execute_sequential(
        &graph, &Environment::new(), &ElabBudget::default(),
    ) {
        Outcome::Complete(Ok(output)) => output,
        other => panic!("cold oracle failed: {other:?}"),
    };
    assert_eq!(updated.output.messages, cold.messages);
    assert_eq!(updated.output.final_environment.logical_root(&KVMap::new()),
        cold.final_environment.logical_root(&KVMap::new()));
}

#[test]
fn new_callback_identity_invalidates_without_an_explicit_edit_list() {
    let calls = counts(3);
    let mut nodes = simple_nodes(&calls);
    nodes[1].referenced_names.push(name("A"));
    let old = graph(nodes.clone());
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &old, &[]);
    let mut replacement = command(0, &calls[0], EffectSummary::new(), |_| {
        Outcome::complete(Ok(published("A", 1)))
    });
    replacement.name = Some(name("A"));
    nodes[0] = replacement;
    let updated = execute(&mut cache, &graph(nodes), &[]);
    assert_eq!(updated.executed_commands, vec![CommandId(0), CommandId(1)]);
    assert_eq!(updated.reused_commands, vec![CommandId(2)]);
    assert_eq!(snapshot(&calls), vec![2, 2, 1]);
}

#[test]
fn changed_prescan_metadata_invalidates_even_with_the_same_callback_arc() {
    let calls = counts(3);
    let mut nodes = simple_nodes(&calls);
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &graph(nodes.clone()), &[]);
    nodes[1].referenced_names.push(name("A"));
    let updated = execute(&mut cache, &graph(nodes), &[]);
    assert_eq!(updated.executed_commands, vec![CommandId(1)]);
    assert_eq!(updated.reused_commands, vec![CommandId(0), CommandId(2)]);
}

#[test]
fn new_dynamic_publication_invalidates_previously_negative_queries() {
    let calls = counts(3);
    let publish = Arc::new(AtomicUsize::new(0));
    let mode = Arc::clone(&publish);
    let a = command(0, &calls[0], EffectSummary::new(), move |_| {
        Outcome::complete(Ok(if mode.load(Ordering::SeqCst) == 0 {
            ElabUnitProduct::empty()
        } else {
            published("X", 0)
        }))
    });
    let b = command(1, &calls[1], EffectSummary::new(), |environment| {
        let mut product = published("Y", 0);
        product.effects.record(read("X"));
        product.messages.push(Message::info(if environment.contains(&name("X")) {
            "X present"
        } else {
            "X absent"
        }));
        Outcome::complete(Ok(product))
    });
    let c = command(2, &calls[2], effects([read("Y")]), |_| {
        Outcome::complete(Ok(ElabUnitProduct::empty()))
    });
    let graph = graph(vec![a, b, c]);
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &graph, &[]);
    publish.store(1, Ordering::SeqCst);
    let positive = execute(&mut cache, &graph, &[CommandId(0)]);
    assert_eq!(positive.executed_commands, vec![CommandId(0), CommandId(1), CommandId(2)]);
    assert!(positive.output.messages.iter().any(|message| message.text == "X present"));
    publish.store(0, Ordering::SeqCst);
    let negative = execute(&mut cache, &graph, &[CommandId(0)]);
    assert!(!negative.output.final_environment.contains(&name("X")));
    assert!(negative.output.messages.iter().any(|message| message.text == "X absent"));
    assert_eq!(snapshot(&calls), vec![3, 3, 3]);
}

#[test]
fn deleting_a_command_removes_its_declarations_and_messages() {
    let calls = counts(3);
    let nodes = simple_nodes(&calls);
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &graph(nodes.clone()), &[]);
    let remaining = graph(nodes.into_iter().skip(1).collect());
    let output = execute(&mut cache, &remaining, &[CommandId(0)]);
    assert!(!output.output.final_environment.contains(&name("A")));
    assert!(output.output.final_environment.contains(&name("B")));
    assert!(!output.output.messages.iter().any(|message| message.text.starts_with("A:")));
    assert!(output.reused_commands.is_empty());
    assert_eq!(snapshot(&calls), vec![1, 2, 2]);
}

#[test]
fn reorder_and_empty_module_rebuild_from_the_fixed_base() {
    let calls = counts(3);
    let mut nodes = simple_nodes(&calls);
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &graph(nodes.clone()), &[]);
    nodes.reverse();
    let reordered = execute(&mut cache, &graph(nodes), &[]);
    assert_eq!(reordered.output.committed_order, vec![CommandId(2), CommandId(1), CommandId(0)]);
    assert!(reordered.reused_commands.is_empty());
    let empty = execute(&mut cache, &DataflowGraph::new(), &[]);
    assert_eq!(empty.output.final_environment.len(), 0);
    assert!(empty.output.messages.is_empty());
}

#[test]
fn failed_rebuild_cannot_replace_the_last_successful_cache() {
    let calls = counts(3);
    let nodes = simple_nodes(&calls);
    let original = graph(nodes.clone());
    let mut cache = IncrementalScheduler::new(&Environment::new());
    let expected = execute(&mut cache, &original, &[]);
    let bad_calls = counts(2);
    let mut changed = nodes;
    changed[0] = command(0, &bad_calls[0], EffectSummary::new(), |_| {
        Outcome::complete(Ok(published("A", 1)))
    });
    changed[2] = command(2, &bad_calls[1], EffectSummary::new(), |_| {
        Outcome::complete(Err("rebuild rejected".into()))
    });
    assert!(matches!(cache.execute(&graph(changed), &[], &ElabBudget::default()),
        Outcome::Complete(Err(_))));
    let recovered = execute(&mut cache, &original, &[]);
    assert!(recovered.executed_commands.is_empty());
    assert_eq!(recovered.output.messages, expected.output.messages);
    assert_eq!(recovered.output.final_environment.logical_root(&KVMap::new()),
        expected.output.final_environment.logical_root(&KVMap::new()));
    assert_eq!(snapshot(&calls), vec![1, 1, 1]);
}

#[test]
fn nonanswers_are_never_cached_or_promoted() {
    for use_fault in [false, true] {
        let calls = counts(3);
        let nodes = simple_nodes(&calls);
        let original = graph(nodes.clone());
        let mut cache = IncrementalScheduler::new(&Environment::new());
        execute(&mut cache, &original, &[]);
        let stop_calls = Arc::new(AtomicUsize::new(0));
        let mut changed = nodes;
        changed[1] = command(1, &stop_calls, EffectSummary::new(), move |_| {
            if use_fault {
                Outcome::InternalFault(InternalFault::new("FL-INV-01", "cache probe"))
            } else {
                Outcome::Inconclusive(Inconclusive::cancelled("cache probe"))
            }
        });
        let outcome = cache.execute(&graph(changed), &[], &ElabBudget::default());
        if use_fault {
            assert!(matches!(outcome, Outcome::InternalFault(_)));
        } else {
            assert!(matches!(outcome, Outcome::Inconclusive(_)));
        }
        assert_eq!(stop_calls.load(Ordering::SeqCst), 1);
        assert!(execute(&mut cache, &original, &[]).executed_commands.is_empty());
        assert_eq!(snapshot(&calls), vec![1, 1, 1]);
    }
}

#[test]
fn unknown_edit_ids_fail_before_callbacks_and_leave_the_cache_intact() {
    let calls = counts(3);
    let graph = graph(simple_nodes(&calls));
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &graph, &[]);
    assert!(matches!(cache.execute(&graph, &[CommandId(999)], &ElabBudget::default()),
        Outcome::Complete(Err(_))));
    assert!(execute(&mut cache, &graph, &[]).executed_commands.is_empty());
    assert_eq!(snapshot(&calls), vec![1, 1, 1]);
}

#[test]
fn opaque_commands_run_each_time_and_invalidate_their_suffix() {
    let calls = counts(3);
    let mut nodes = simple_nodes(&calls);
    nodes[1].declared_effects.record(CommandEffect::Opaque { reason: "ambient".into() });
    let graph = graph(nodes);
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &graph, &[]);
    let output = execute(&mut cache, &graph, &[]);
    assert_eq!(output.executed_commands, vec![CommandId(1), CommandId(2)]);
    assert_eq!(output.reused_commands, vec![CommandId(0)]);
    assert_eq!(snapshot(&calls), vec![1, 2, 2]);
}

#[test]
fn typed_registry_writers_are_not_replayed_from_declaration_only_products() {
    let calls = counts(3);
    let mut nodes = simple_nodes(&calls);
    nodes[1].declared_effects.record(CommandEffect::WritesGrammar { category: name("term") });
    let graph = graph(nodes);
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &graph, &[]);
    let output = execute(&mut cache, &graph, &[]);
    assert_eq!(output.executed_commands, vec![CommandId(1)]);
    assert_eq!(output.reused_commands, vec![CommandId(0), CommandId(2)]);
}

#[test]
fn changed_budget_and_explicit_clear_discard_reuse() {
    let calls = counts(3);
    let graph = graph(simple_nodes(&calls));
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &graph, &[]);
    let budget = ElabBudget { max_heartbeats: 500, ..ElabBudget::default() };
    match cache.execute(&graph, &[], &budget) {
        Outcome::Complete(Ok(output)) => assert_eq!(output.executed_commands.len(), 3),
        other => panic!("changed budget run failed: {other:?}"),
    }
    cache.clear();
    assert_eq!(execute(&mut cache, &graph, &[]).executed_commands.len(), 3);
    assert_eq!(snapshot(&calls), vec![3, 3, 3]);
}

#[test]
fn replacing_the_base_environment_invalidates_import_sensitive_products() {
    let calls = counts(1);
    let observer = command(0, &calls[0], effects([read("Imported")]), |environment| {
        let mut product = ElabUnitProduct::empty();
        product.messages.push(Message::info(if environment.contains(&name("Imported")) {
            "imported"
        } else {
            "missing"
        }));
        Outcome::complete(Ok(product))
    });
    let observer_graph = graph(vec![observer]);
    let mut cache = IncrementalScheduler::new(&Environment::new());
    assert_eq!(execute(&mut cache, &observer_graph, &[]).output.messages[0].text, "missing");
    let import = command(0, &Arc::new(AtomicUsize::new(0)), EffectSummary::new(), |_| {
        Outcome::complete(Ok(published("Imported", 0)))
    });
    let base = match DeterministicScheduler::execute_sequential(
        &graph(vec![import]), &Environment::new(), &ElabBudget::default(),
    ) {
        Outcome::Complete(Ok(output)) => output.final_environment,
        other => panic!("base construction failed: {other:?}"),
    };
    cache.reset_base_environment(&base);
    let output = execute(&mut cache, &observer_graph, &[]);
    assert_eq!(output.output.messages[0].text, "imported");
    assert_eq!(output.executed_commands, vec![CommandId(0)]);
}

#[test]
fn duplicate_graph_ids_cannot_enter_the_incremental_cache() {
    let calls = counts(3);
    let mut nodes = simple_nodes(&calls);
    nodes[1].id = nodes[0].id;
    let mut cache = IncrementalScheduler::new(&Environment::new());
    assert!(matches!(cache.execute(&graph(nodes), &[], &ElabBudget::default()),
        Outcome::Complete(Err(_))));
    assert_eq!(snapshot(&calls), vec![0, 0, 0]);
}

#[test]
fn inserting_a_command_rebuilds_and_publishes_its_new_product() {
    let calls = counts(4);
    let mut nodes = simple_nodes(&calls);
    let mut cache = IncrementalScheduler::new(&Environment::new());
    execute(&mut cache, &graph(nodes.clone()), &[]);
    let added = command(90, &calls[3], EffectSummary::new(), |_| {
        Outcome::complete(Ok(published("Added", 0)))
    });
    nodes.insert(1, added);
    let output = execute(&mut cache, &graph(nodes), &[CommandId(90)]);
    assert!(output.output.final_environment.contains(&name("Added")));
    assert_eq!(output.output.committed_order,
        vec![CommandId(0), CommandId(90), CommandId(1), CommandId(2)]);
    assert!(output.reused_commands.is_empty());
    assert_eq!(snapshot(&calls), vec![2, 2, 2, 1]);
}
