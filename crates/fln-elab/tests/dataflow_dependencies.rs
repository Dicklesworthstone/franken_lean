//! Scheduling dependencies must cover state, not just positive name lookups.
#![forbid(unsafe_code)]

use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::dataflow::{CommandId, DataflowGraph, DataflowNode, ElabUnitProduct};
use fln_elab::effects::{CommandEffect, DeclAspect, EffectSummary};

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

fn node(id: usize, declared_effects: EffectSummary) -> DataflowNode {
    DataflowNode {
        id: CommandId(id),
        name: None,
        declared_names: Vec::new(),
        referenced_names: Vec::new(),
        declared_effects,
        elab_fn: Arc::new(|_, _| Outcome::complete(Ok(ElabUnitProduct::empty()))),
    }
}

fn read(value: &str) -> CommandEffect {
    CommandEffect::ReadsDecl {
        name: name(value),
        aspect: DeclAspect::Type,
    }
}

fn write(value: &str) -> CommandEffect {
    CommandEffect::WritesDecl { name: name(value) }
}

fn dependencies(graph: &DataflowGraph, id: usize) -> HashSet<CommandId> {
    graph.dependencies_of(CommandId(id)).unwrap().clone()
}

#[test]
fn barriers_order_both_predecessors_and_successors() {
    let mut graph = DataflowGraph::new();
    graph.add_node(node(0, EffectSummary::new()));
    graph.add_node(node(1, effects([CommandEffect::Opaque { reason: "syntax".into() }])));
    graph.add_node(node(2, EffectSummary::new()));
    assert_eq!(dependencies(&graph, 1), HashSet::from([CommandId(0)]));
    assert_eq!(dependencies(&graph, 2), HashSet::from([CommandId(1)]));
    assert_eq!(graph.affected_commands(&[CommandId(0)]).unwrap(),
        vec![CommandId(0), CommandId(1), CommandId(2)]);
}

#[test]
fn raw_war_and_waw_dependencies_are_bidirectionally_indexed() {
    let mut graph = DataflowGraph::new();
    graph.add_node(node(0, effects([read("absent")])));
    graph.add_node(node(1, effects([write("absent")])));
    graph.add_node(node(2, effects([read("absent")])));
    graph.add_node(node(3, effects([write("absent")])));
    assert_eq!(dependencies(&graph, 1), HashSet::from([CommandId(0)]));
    assert!(dependencies(&graph, 2).contains(&CommandId(1)));
    assert_eq!(dependencies(&graph, 3), HashSet::from([CommandId(0), CommandId(1), CommandId(2)]));
    for current in graph.nodes() {
        for predecessor in graph.dependencies_of(current.id).unwrap() {
            assert!(graph.dependents_of(*predecessor).unwrap().contains(&current.id));
        }
    }
}

#[test]
fn primary_and_secondary_names_join_typed_effects() {
    let mut producer = node(0, EffectSummary::new());
    producer.name = Some(name("primary"));
    producer.declared_names.push(name("auxiliary"));
    let mut consumer = node(1, EffectSummary::new());
    consumer.referenced_names.push(name("primary"));
    let mut graph = DataflowGraph::new();
    graph.add_node(producer);
    graph.add_node(consumer);
    graph.add_node(node(2, effects([read("auxiliary")])));
    assert_eq!(dependencies(&graph, 1), HashSet::from([CommandId(0)]));
    assert_eq!(dependencies(&graph, 2), HashSet::from([CommandId(0)]));
}

#[test]
fn instance_and_grammar_dependencies_do_not_require_name_references() {
    let pairs = [
        (CommandEffect::WritesInstance { class_head: name("C"), instance_name: name("i") },
         CommandEffect::ReadsInstances { class_head: name("C") }),
        (CommandEffect::WritesGrammar { category: name("term") },
         CommandEffect::ReadsGrammar { category: name("term") }),
    ];
    for (writer, reader) in pairs {
        for pair in [[writer.clone(), reader.clone()], [reader, writer]] {
            let mut graph = DataflowGraph::new();
            graph.add_node(node(0, effects([pair[0].clone()])));
            graph.add_node(node(1, effects([pair[1].clone()])));
            assert_eq!(dependencies(&graph, 1), HashSet::from([CommandId(0)]));
        }
    }
}

#[test]
fn ambient_capabilities_and_generic_extension_writes_are_barriers() {
    for effect in [
        CommandEffect::UsesCapability { capability_id: "filesystem".into() },
        CommandEffect::WritesEnvExtension { extension_name: name("unknown") },
    ] {
        let barrier = effects([effect]);
        assert!(barrier.is_barrier());
        assert!(!barrier.is_replay_safe());
        for observer in [
            EffectSummary::new(),
            effects([CommandEffect::ReadsOption { key: "trace".into() }]),
            effects([CommandEffect::ReadsSimpSet { simp_name: name("simp") }]),
        ] {
            assert!(!barrier.commutes_with(&observer));
            assert!(!observer.commutes_with(&barrier));
        }
    }
}

#[test]
fn registry_writes_cannot_be_replayed_without_their_deltas() {
    for effect in [
        CommandEffect::WritesInstance { class_head: name("C"), instance_name: name("i") },
        CommandEffect::WritesGrammar { category: name("term") },
    ] {
        assert!(!effects([effect]).is_replay_safe());
    }
    assert!(effects([read("a"), write("b")]).is_replay_safe());
}

#[test]
fn disjoint_commands_stay_independent() {
    let mut graph = DataflowGraph::new();
    graph.add_node(node(0, effects([read("a"), write("b")])));
    graph.add_node(node(1, effects([read("a"), write("c")])));
    assert!(dependencies(&graph, 1).is_empty());
    assert_eq!(graph.affected_commands(&[CommandId(0)]).unwrap(), vec![CommandId(0)]);
}

#[test]
fn transitive_diamond_invalidation_is_deduplicated_and_source_ordered() {
    let mut graph = DataflowGraph::new();
    graph.add_node(node(40, effects([write("a")])));
    graph.add_node(node(3, effects([read("a"), write("b")])));
    graph.add_node(node(90, effects([read("a"), write("c")])));
    graph.add_node(node(1, effects([read("b"), read("c")])));
    graph.add_node(node(8, effects([write("unrelated")])));
    assert_eq!(graph.affected_commands(&[CommandId(40), CommandId(40)]).unwrap(),
        vec![CommandId(40), CommandId(3), CommandId(90), CommandId(1)]);
}

#[test]
fn invalid_command_identities_fail_closed() {
    let mut graph = DataflowGraph::new();
    graph.add_node(node(2, EffectSummary::new()));
    assert!(graph.affected_commands(&[CommandId(99)]).is_err());
    graph.add_node(node(2, effects([write("a")])));
    assert!(graph.validate().unwrap_err().contains("duplicate command ID"));
    assert!(graph.affected_commands(&[]).is_err());
}

#[test]
fn observed_effects_add_edges_without_mutating_the_source_graph() {
    let mut graph = DataflowGraph::new();
    graph.add_node(node(0, effects([write("a")])));
    graph.add_node(node(1, effects([write("b")])));
    graph.add_node(node(2, effects([read("b")])));
    let observed = BTreeMap::from([(CommandId(1), effects([read("a")]))]);
    let refined = graph.with_observed_effects(&observed).unwrap();
    assert!(dependencies(&graph, 1).is_empty());
    assert_eq!(refined.affected_commands(&[CommandId(0)]).unwrap(),
        vec![CommandId(0), CommandId(1), CommandId(2)]);
    assert!(graph.with_observed_effects(&BTreeMap::from([
        (CommandId(99), EffectSummary::new())
    ])).is_err());
}

#[test]
fn footprint_join_preserves_demotions() {
    let mut opaque = EffectSummary::new();
    opaque.demote_to_opaque("untracked lookup".into());
    let mut joined = effects([read("a")]);
    joined.extend(&opaque);
    joined.extend(&opaque);
    assert!(joined.is_barrier());
    assert!(!joined.is_replay_safe());
    assert_eq!(joined.effects().len(), 2);
}

#[test]
fn commutativity_is_symmetric_for_the_effect_vocabulary() {
    let variants = [
        read("a"), write("a"), write("b"),
        CommandEffect::ReadsInstances { class_head: name("C") },
        CommandEffect::WritesInstance { class_head: name("C"), instance_name: name("i") },
        CommandEffect::ReadsGrammar { category: name("term") },
        CommandEffect::WritesGrammar { category: name("term") },
        CommandEffect::ReadsSimpSet { simp_name: name("simp") },
        CommandEffect::ReadsOption { key: "trace".into() },
        CommandEffect::WritesEnvExtension { extension_name: name("ext") },
        CommandEffect::UsesCapability { capability_id: "io".into() },
        CommandEffect::Opaque { reason: "unknown".into() },
    ];
    for a in &variants {
        for b in &variants {
            let a = effects([a.clone()]);
            let b = effects([b.clone()]);
            assert_eq!(a.commutes_with(&b), b.commutes_with(&a));
        }
    }
}

#[test]
fn indexed_dependencies_match_pairwise_effect_conflicts() {
    // Reproducible generated graphs, without a random-number dependency. This
    // tests the live Rust index against the public commutativity specification.
    let variants = [
        read("a"), write("a"), read("b"), write("b"),
        CommandEffect::ReadsInstances { class_head: name("a") },
        CommandEffect::WritesInstance { class_head: name("a"), instance_name: name("i") },
        CommandEffect::WritesInstance { class_head: name("b"), instance_name: name("i") },
        CommandEffect::ReadsGrammar { category: name("a") },
        CommandEffect::WritesGrammar { category: name("a") },
        CommandEffect::WritesGrammar { category: name("b") },
        CommandEffect::ReadsSimpSet { simp_name: name("a") },
        CommandEffect::ReadsOption { key: "a".into() },
        CommandEffect::WritesEnvExtension { extension_name: name("a") },
        CommandEffect::UsesCapability { capability_id: "io".into() },
        CommandEffect::Opaque { reason: "opaque".into() },
    ];
    let mut seed = 0x5eed_u64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        (seed >> 32) as usize
    };
    for _ in 0..256 {
        let mut graph = DataflowGraph::new();
        for index in 0..24 {
            let mut summary = EffectSummary::new();
            for _ in 0..next() % 5 {
                summary.record(variants[next() % variants.len()].clone());
            }
            if next() % 23 == 0 {
                summary.demote_to_opaque("perturbation".into());
            }
            let mut current = node(1000 - index * 7, summary);
            if next() % 3 == 0 {
                current.name = Some(name("a"));
            }
            if next() % 3 == 0 {
                current.declared_names.push(name("b"));
            }
            if next() % 3 == 0 {
                current.referenced_names.push(name("b"));
            }
            let current_effects = current.dependency_effects();
            let expected: HashSet<_> = graph.nodes().iter()
                .filter(|previous| {
                    !previous.dependency_effects().commutes_with(&current_effects)
                })
                .map(|previous| previous.id)
                .collect();
            let id = current.id;
            graph.add_node(current);
            assert_eq!(graph.dependencies_of(id).unwrap(), &expected);
        }
        graph.validate().unwrap();
        let mut expected = HashSet::from([graph.nodes()[0].id]);
        for current in graph.nodes() {
            if graph.dependencies_of(current.id).unwrap().iter()
                .any(|dependency| expected.contains(dependency))
            {
                expected.insert(current.id);
            }
        }
        let expected: Vec<_> = graph.nodes().iter()
            .filter(|current| expected.contains(&current.id))
            .map(|current| current.id)
            .collect();
        assert_eq!(graph.affected_commands(&[graph.nodes()[0].id]).unwrap(), expected);
    }
}

#[test]
fn large_disjoint_graph_has_no_accidental_edges_or_invalidation() {
    let mut graph = DataflowGraph::new();
    for id in 0..4096 {
        graph.add_node(node(id, effects([write(&format!("independent_{id}"))])));
    }
    graph.validate().unwrap();
    for current in graph.nodes() {
        assert!(graph.dependencies_of(current.id).unwrap().is_empty());
    }
    assert_eq!(graph.affected_commands(&[CommandId(2048)]).unwrap(), vec![CommandId(2048)]);
}
