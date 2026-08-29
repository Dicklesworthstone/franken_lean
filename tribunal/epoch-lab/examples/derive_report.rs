//! The extraction driver for the derived inputs (bead `fln-8fwh`).
//!
//! ```text
//! cargo run --manifest-path tribunal/epoch-lab/Cargo.toml --example derive_report -- report
//! cargo run --manifest-path tribunal/epoch-lab/Cargo.toml --example derive_report -- emit-modules <toolchain> <pin>
//! ```
//!
//! **This is an `examples/` target on purpose.** The module scan touches the
//! pinned toolchain, and D8 permits that only as a checked-in extraction path
//! inside the Tribunal boundary — never from something shippable. An example is
//! not a shippable target, is not a gate, and is not linked into any release
//! artifact, so the extraction lives here while the *gate* reads only the
//! committed artifact through `verify_module_artifact`.
//!
//! Output is line-oriented and machine-first, per the agent-ergonomics rule.

#![forbid(unsafe_code)]

use fln_epoch_lab::derive::{
    Corroboration, TargetScan, classify, corroborate, corroboration_report,
    derive_dependency_closure, derive_epoch_tree, derive_g0_roster, derive_module_scan,
    derive_oracle_edges, derive_targets, derive_workspace_inventory, product_binary_roots,
    read_graph_edges, read_graph_kinds, read_shippability_policy, render_epoch_tree,
    render_module_artifact,
};
use fln_epoch_lab::poison::OracleEdge;
use std::path::{Path, PathBuf};

fn repo_root() -> Result<PathBuf, fln_conformance::tree_identity::CrossTreeFault> {
    Ok(fln_conformance::checked_manifest_dir!(try)?.join("../.."))
}

fn require_repo_root() -> Result<PathBuf, std::process::ExitCode> {
    repo_root().map_err(|fault| {
        eprintln!("derive: inconclusive {}", fault.robot_reason());
        std::process::ExitCode::from(2)
    })
}

fn main() -> std::process::ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("report") => report(),
        Some("emit-tree") => match (args.get(1), args.get(2)) {
            (Some(epoch), Some(head)) => emit_tree(epoch, head),
            _ => {
                eprintln!("usage: derive_report emit-tree <epoch-tag> <head-root>");
                std::process::ExitCode::from(2)
            }
        },
        Some("emit-modules") => match (args.get(1), args.get(2)) {
            (Some(toolchain), Some(pin)) => emit_modules(toolchain, pin),
            _ => {
                eprintln!("usage: derive_report emit-modules <toolchain-dir> <pin>");
                std::process::ExitCode::from(2)
            }
        },
        _ => {
            eprintln!("usage: derive_report <report|emit-modules>");
            std::process::ExitCode::from(2)
        }
    }
}

fn report_shippability(root: &Path, targets: &[TargetScan], oracle_edges: &[OracleEdge]) -> bool {
    let policy_path = root.join("tribunal/derived/SHIPPABILITY_POLICY.txt");
    let policy = match read_shippability_policy(&policy_path) {
        Ok(policy) => policy,
        Err(error) => {
            println!("derive: shippability verdict=fail reason={error}");
            return true;
        }
    };
    let (_, gaps) = classify(targets, &policy);
    if !gaps.is_empty() {
        println!(
            "derive: shippability verdict=fail unclassified_or_stale_crates={} detail={gaps:?}",
            gaps.len()
        );
        return true;
    }

    let graph_path = root.join("ci/WORKSPACE_GRAPH.txt");
    let graph_kinds = match read_graph_kinds(&graph_path) {
        Ok(graph) => graph,
        Err(error) => {
            println!("derive: shippability verdict=fail reason={error}");
            return true;
        }
    };
    let graph_edges = match read_graph_edges(&graph_path) {
        Ok(edges) => edges,
        Err(error) => {
            println!("derive: shippability verdict=fail reason={error}");
            return true;
        }
    };
    let roots = product_binary_roots(targets, &graph_kinds);
    let closure = derive_dependency_closure(&graph_edges, &roots);
    let oracle_edge_crates: Vec<String> = oracle_edges
        .iter()
        .filter_map(|edge| {
            targets
                .iter()
                .find(|target| target.name == edge.target)
                .map(|target| target.crate_name.clone())
        })
        .collect();
    let rows = corroborate(&policy, &graph_kinds, &closure, &oracle_edge_crates);
    print!("{}", corroboration_report(&rows));

    rows.iter()
        .any(|row| matches!(row.standing, Corroboration::Contradicted { .. }))
}

fn report() -> std::process::ExitCode {
    let root = match require_repo_root() {
        Ok(root) => root,
        Err(code) => return code,
    };
    let mut failed = false;

    match derive_workspace_inventory(&root) {
        Ok(d) => {
            let p = d.provenance();
            println!(
                "derive: rule={} verdict=pass members={} features={} digest={}",
                p.rule,
                p.item_count,
                d.value().feature_universe().len(),
                p.source_digest
            );
        }
        Err(e) => {
            println!("derive: rule=workspace-inventory verdict=fail reason={e}");
            failed = true;
        }
    }

    let plan = root.join("COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md");
    match derive_g0_roster(&plan) {
        Ok(d) => {
            let p = d.provenance();
            println!(
                "derive: rule={} verdict=pass spikes={} digest={}",
                p.rule, p.item_count, p.source_digest
            );
            for s in d.value() {
                println!("derive: spike id={} name={:?}", s.id, s.name);
            }
        }
        Err(e) => {
            println!("derive: rule=g0-roster verdict=fail reason={e}");
            failed = true;
        }
    }

    match derive_targets(&root) {
        Ok(d) => {
            let p = d.provenance();
            println!(
                "derive: rule={} verdict=pass targets={} digest={}",
                p.rule, p.item_count, p.source_digest
            );
            match derive_oracle_edges(&root, d.value()) {
                Ok(e) => {
                    println!(
                        "derive: rule={} verdict=pass edges={} digest={}",
                        e.provenance().rule,
                        e.provenance().item_count,
                        e.provenance().source_digest
                    );
                    for edge in e.value() {
                        println!(
                            "derive: oracle-edge target={} capability={}",
                            edge.target,
                            edge.capability.as_str()
                        );
                    }
                    failed |= report_shippability(&root, d.value(), e.value());
                }
                Err(err) => {
                    println!("derive: rule=oracle-edges verdict=fail reason={err}");
                    failed = true;
                }
            }
        }
        Err(e) => {
            println!("derive: rule=cargo-targets verdict=fail reason={e}");
            failed = true;
        }
    }

    if failed {
        std::process::ExitCode::FAILURE
    } else {
        std::process::ExitCode::SUCCESS
    }
}

fn emit_modules(toolchain: &str, pin: &str) -> std::process::ExitCode {
    match derive_module_scan(std::path::Path::new(toolchain), pin) {
        Ok(d) => {
            eprintln!(
                "derive: rule={} verdict=pass modules={} digest={}",
                d.provenance().rule,
                d.provenance().item_count,
                d.provenance().source_digest
            );
            print!("{}", render_module_artifact(&d));
            std::process::ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("derive: rule=module-scan verdict=fail reason={e}");
            std::process::ExitCode::FAILURE
        }
    }
}

fn emit_tree(epoch: &str, head_root: &str) -> std::process::ExitCode {
    let root = match require_repo_root() {
        Ok(root) => root,
        Err(code) => return code,
    };
    let dir = root.join("tribunal/epochs").join(epoch);
    match derive_epoch_tree(&dir, epoch, head_root) {
        Ok(d) => {
            eprintln!(
                "derive: rule={} verdict=pass files={} digest={}",
                d.provenance().rule,
                d.provenance().item_count,
                d.provenance().source_digest
            );
            print!("{}", render_epoch_tree(&d));
            std::process::ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("derive: rule=epoch-tree verdict=fail reason={e}");
            std::process::ExitCode::FAILURE
        }
    }
}
