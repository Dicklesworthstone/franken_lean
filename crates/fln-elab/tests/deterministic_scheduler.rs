//! Integration tests for the deterministic dataflow scheduler (Bet B4, Plan §10.6, FL-INV-01).

#![forbid(unsafe_code)]

use std::sync::Arc;

use fln_core::expr::Expr;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::dataflow::{CommandId, DataflowGraph, DataflowNode, ElabUnitProduct};
use fln_elab::decision::DecisionRecord;
use fln_elab::effects::{CommandEffect, DeclAspect, EffectSummary};
use fln_elab::info::{Info, InfoTree};
use fln_elab::messages::Message;
use fln_elab::perturbation::PerturbationValidator;
use fln_elab::scheduler::{DeterministicScheduler, ExecutionConfig};
use fln_elab::txn::ElabBudget;
use fln_env::constants::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_env::environment::Environment;

fn create_sample_def(name_str: &str) -> ConstantInfo {
    let components: Vec<&str> = name_str.split('.').collect();
    let name = Name::from_components(components);
    let val = ConstantVal {
        name,
        level_params: Vec::new(),
        type_: Expr::sort(fln_core::level::Level::zero()),
    };
    ConstantInfo::Defn(DefinitionVal {
        base: val,
        value: Expr::sort(fln_core::level::Level::zero()),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: Vec::new(),
    })
}

#[test]
fn test_thread_matrix_schedule_independence_1_8_32_threads() {
    let base_env = Environment::new();
    let budget = ElabBudget::default();
    let mut graph = DataflowGraph::new();

    // Node 0: Defines A
    let node0_decl = create_sample_def("Mod.A");
    let mut node0_eff = EffectSummary::new();
    node0_eff.record(CommandEffect::WritesDecl {
        name: Name::from_components(["Mod", "A"]),
    });
    let d0 = node0_decl.clone();
    graph.add_node(DataflowNode {
        id: CommandId(0),
        name: Some(Name::from_components(["Mod", "A"])),
        declared_names: vec![Name::from_components(["Mod", "A"])],
        referenced_names: vec![],
        declared_effects: node0_eff.clone(),
        elab_fn: Arc::new(move |_env, _budget| {
            let mut product = ElabUnitProduct::empty();
            product.admitted_decls.push(d0.clone());
            product
                .messages
                .push(Message::info("Elaborated Mod.A successfully"));
            product.info_tree = Some(InfoTree::Node(
                Info::CommandInfo {
                    name: Name::from_components(["Mod", "A"]),
                },
                Vec::new(),
            ));
            product.decisions.push(DecisionRecord::OverloadChoice {
                candidate_name: Name::from_components(["Mod", "A"]),
                index: 0,
                total_candidates: 1,
            });
            product.effects = node0_eff.clone();
            Outcome::complete(Ok(product))
        }),
    });

    // Node 1: Defines B, reads A
    let node1_decl = create_sample_def("Mod.B");
    let mut node1_eff = EffectSummary::new();
    node1_eff.record(CommandEffect::ReadsDecl {
        name: Name::from_components(["Mod", "A"]),
        aspect: DeclAspect::Type,
    });
    node1_eff.record(CommandEffect::WritesDecl {
        name: Name::from_components(["Mod", "B"]),
    });
    let d1 = node1_decl.clone();
    graph.add_node(DataflowNode {
        id: CommandId(1),
        name: Some(Name::from_components(["Mod", "B"])),
        declared_names: vec![Name::from_components(["Mod", "B"])],
        referenced_names: vec![Name::from_components(["Mod", "A"])],
        declared_effects: node1_eff.clone(),
        elab_fn: Arc::new(move |env, _budget| {
            let mut product = ElabUnitProduct::empty();
            if env.contains(&Name::from_components(["Mod", "A"])) {
                product.admitted_decls.push(d1.clone());
                product
                    .messages
                    .push(Message::info("Elaborated Mod.B with dependency Mod.A"));
            } else {
                // Speculative attempt before A was committed
                product
                    .messages
                    .push(Message::warning("Mod.A not found during speculative pass"));
            }
            product.info_tree = Some(InfoTree::Node(
                Info::CommandInfo {
                    name: Name::from_components(["Mod", "B"]),
                },
                Vec::new(),
            ));
            product.decisions.push(DecisionRecord::OverloadChoice {
                candidate_name: Name::from_components(["Mod", "B"]),
                index: 0,
                total_candidates: 1,
            });
            product.effects = node1_eff.clone();
            Outcome::complete(Ok(product))
        }),
    });

    // Node 2: Defines C, independent
    let node2_decl = create_sample_def("Mod.C");
    let mut node2_eff = EffectSummary::new();
    node2_eff.record(CommandEffect::WritesDecl {
        name: Name::from_components(["Mod", "C"]),
    });
    let d2 = node2_decl.clone();
    graph.add_node(DataflowNode {
        id: CommandId(2),
        name: Some(Name::from_components(["Mod", "C"])),
        declared_names: vec![Name::from_components(["Mod", "C"])],
        referenced_names: vec![],
        declared_effects: node2_eff.clone(),
        elab_fn: Arc::new(move |_env, _budget| {
            let mut product = ElabUnitProduct::empty();
            product.admitted_decls.push(d2.clone());
            product
                .messages
                .push(Message::info("Elaborated Mod.C independently"));
            product.info_tree = Some(InfoTree::Node(
                Info::CommandInfo {
                    name: Name::from_components(["Mod", "C"]),
                },
                Vec::new(),
            ));
            product.decisions.push(DecisionRecord::OverloadChoice {
                candidate_name: Name::from_components(["Mod", "C"]),
                index: 0,
                total_candidates: 1,
            });
            product.effects = node2_eff.clone();
            Outcome::complete(Ok(product))
        }),
    });

    // Node 3: Defines D, reads B and C
    let node3_decl = create_sample_def("Mod.D");
    let mut node3_eff = EffectSummary::new();
    node3_eff.record(CommandEffect::ReadsDecl {
        name: Name::from_components(["Mod", "B"]),
        aspect: DeclAspect::Type,
    });
    node3_eff.record(CommandEffect::ReadsDecl {
        name: Name::from_components(["Mod", "C"]),
        aspect: DeclAspect::Type,
    });
    node3_eff.record(CommandEffect::WritesDecl {
        name: Name::from_components(["Mod", "D"]),
    });
    let d3 = node3_decl.clone();
    graph.add_node(DataflowNode {
        id: CommandId(3),
        name: Some(Name::from_components(["Mod", "D"])),
        declared_names: vec![Name::from_components(["Mod", "D"])],
        referenced_names: vec![
            Name::from_components(["Mod", "B"]),
            Name::from_components(["Mod", "C"]),
        ],
        declared_effects: node3_eff.clone(),
        elab_fn: Arc::new(move |env, _budget| {
            let mut product = ElabUnitProduct::empty();
            if env.contains(&Name::from_components(["Mod", "B"]))
                && env.contains(&Name::from_components(["Mod", "C"]))
            {
                product.admitted_decls.push(d3.clone());
                product.messages.push(Message::info(
                    "Elaborated Mod.D with dependencies Mod.B and Mod.C",
                ));
            }
            product.info_tree = Some(InfoTree::Node(
                Info::CommandInfo {
                    name: Name::from_components(["Mod", "D"]),
                },
                Vec::new(),
            ));
            product.decisions.push(DecisionRecord::OverloadChoice {
                candidate_name: Name::from_components(["Mod", "D"]),
                index: 0,
                total_candidates: 1,
            });
            product.effects = node3_eff.clone();
            Outcome::complete(Ok(product))
        }),
    });

    // Run across thread matrix {1, 8, 32}
    let config_1 = ExecutionConfig {
        worker_threads: 1,
        enable_speculation: true,
        budget: budget.clone(),
    };
    let config_8 = ExecutionConfig {
        worker_threads: 8,
        enable_speculation: true,
        budget: budget.clone(),
    };
    let config_32 = ExecutionConfig {
        worker_threads: 32,
        enable_speculation: true,
        budget: budget.clone(),
    };

    let out_1 = match DeterministicScheduler::execute(&graph, &base_env, &config_1) {
        Outcome::Complete(Ok(out)) => out,
        other => panic!("Expected successful execution at 1 thread, got {other:?}"),
    };

    let out_8 = match DeterministicScheduler::execute(&graph, &base_env, &config_8) {
        Outcome::Complete(Ok(out)) => out,
        other => panic!("Expected successful execution at 8 threads, got {other:?}"),
    };

    let out_32 = match DeterministicScheduler::execute(&graph, &base_env, &config_32) {
        Outcome::Complete(Ok(out)) => out,
        other => panic!("Expected successful execution at 32 threads, got {other:?}"),
    };

    // Verify FL-INV-01: bit-for-bit identical environments across thread matrix
    let opts = KVMap::new();
    let root_1 = out_1.final_environment.logical_root(&opts);
    let root_8 = out_8.final_environment.logical_root(&opts);
    let root_32 = out_32.final_environment.logical_root(&opts);

    assert_eq!(
        root_1, root_8,
        "1 thread and 8 thread logical roots differ!"
    );
    assert_eq!(
        root_8, root_32,
        "8 thread and 32 thread logical roots differ!"
    );

    // Verify declaration counts
    assert_eq!(out_1.final_environment.len(), 4);
    assert_eq!(out_8.final_environment.len(), 4);
    assert_eq!(out_32.final_environment.len(), 4);

    // Verify messages identical and in source order
    assert_eq!(out_1.messages.len(), out_8.messages.len());
    assert_eq!(out_8.messages.len(), out_32.messages.len());
    for (m1, m8) in out_1.messages.iter().zip(&out_8.messages) {
        assert_eq!(m1.severity, m8.severity);
        assert_eq!(m1.text, m8.text);
    }

    // Verify committed order
    assert_eq!(
        out_1.committed_order,
        vec![CommandId(0), CommandId(1), CommandId(2), CommandId(3)]
    );
    assert_eq!(
        out_8.committed_order,
        vec![CommandId(0), CommandId(1), CommandId(2), CommandId(3)]
    );
    assert_eq!(
        out_32.committed_order,
        vec![CommandId(0), CommandId(1), CommandId(2), CommandId(3)]
    );
}

#[test]
fn test_effect_summary_commutativity_and_hazard_detection() {
    let mut eff_r_a = EffectSummary::new();
    eff_r_a.record(CommandEffect::ReadsDecl {
        name: Name::from_components(["A"]),
        aspect: DeclAspect::Type,
    });

    let mut eff_w_a = EffectSummary::new();
    eff_w_a.record(CommandEffect::WritesDecl {
        name: Name::from_components(["A"]),
    });

    let mut eff_w_b = EffectSummary::new();
    eff_w_b.record(CommandEffect::WritesDecl {
        name: Name::from_components(["B"]),
    });

    let mut eff_r_b = EffectSummary::new();
    eff_r_b.record(CommandEffect::ReadsDecl {
        name: Name::from_components(["B"]),
        aspect: DeclAspect::Value,
    });

    let mut eff_opaque = EffectSummary::new();
    eff_opaque.demote_to_opaque("Unanalyzed syntax extension".to_string());

    // Independent read and write commute
    assert!(eff_r_a.commutes_with(&eff_w_b));
    assert!(eff_w_b.commutes_with(&eff_r_a));

    // Disjoint writes commute
    assert!(eff_w_a.commutes_with(&eff_w_b));

    // RAW / WAR hazard does not commute
    assert!(!eff_w_a.commutes_with(&eff_r_a));
    assert!(!eff_r_a.commutes_with(&eff_w_a));

    // Barrier / Opaque effect never commutes
    assert!(!eff_opaque.commutes_with(&eff_r_a));
    assert!(!eff_opaque.commutes_with(&eff_w_b));
}

#[test]
fn test_perturbation_validator_detects_accurate_and_lying_summaries() {
    let base_env = Environment::new();
    let budget = ElabBudget::default();

    // 1. Truthful node: does not read unread declarations
    let decl_honest = create_sample_def("HonestDecl");
    let mut eff_honest = EffectSummary::new();
    eff_honest.record(CommandEffect::WritesDecl {
        name: Name::from_components(["HonestDecl"]),
    });
    let d_h = decl_honest.clone();
    let mut node_honest = DataflowNode {
        id: CommandId(0),
        name: Some(Name::from_components(["HonestDecl"])),
        declared_names: vec![Name::from_components(["HonestDecl"])],
        referenced_names: vec![],
        declared_effects: eff_honest.clone(),
        elab_fn: Arc::new(move |_env, _budget| {
            let mut product = ElabUnitProduct::empty();
            product.admitted_decls.push(d_h.clone());
            product.effects = eff_honest.clone();
            Outcome::complete(Ok(product))
        }),
    };

    let result_honest =
        match PerturbationValidator::validate_node_effects(&mut node_honest, &base_env, &budget) {
            Outcome::Complete(res) => res,
            other => panic!("Expected complete perturbation result, got {other:?}"),
        };
    assert!(matches!(
        result_honest,
        fln_elab::perturbation::PerturbationResult::Validated
    ));
    assert!(!node_honest.declared_effects.is_barrier());

    // 2. Lying node: secretly inspects all constants in environment but does not declare reads
    let decl_liar = create_sample_def("LyingDecl");
    let eff_liar = EffectSummary::new(); // Empty! Claims no reads!
    let d_l = decl_liar.clone();
    let mut node_liar = DataflowNode {
        id: CommandId(1),
        name: Some(Name::from_components(["LyingDecl"])),
        declared_names: vec![Name::from_components(["LyingDecl"])],
        referenced_names: vec![],
        declared_effects: eff_liar,
        elab_fn: Arc::new(move |env, _budget| {
            let mut product = ElabUnitProduct::empty();
            // Leaks environment declaration count into message text!
            product.admitted_decls.push(d_l.clone());
            product.messages.push(Message::info(format!(
                "Observed {} constants in environment",
                env.len()
            )));
            Outcome::complete(Ok(product))
        }),
    };

    let result_liar =
        match PerturbationValidator::validate_node_effects(&mut node_liar, &base_env, &budget) {
            Outcome::Complete(res) => res,
            other => panic!("Expected complete perturbation result, got {other:?}"),
        };

    // Verify perturbation caught the lie and demoted node to Opaque barrier!
    assert!(matches!(
        result_liar,
        fln_elab::perturbation::PerturbationResult::Failed { .. }
    ));
    assert!(
        node_liar.declared_effects.is_barrier(),
        "Lying node must be demoted to Opaque barrier!"
    );
}
