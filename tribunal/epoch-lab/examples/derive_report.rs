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
    derive_g0_roster, derive_module_scan, derive_workspace_inventory, render_module_artifact,
};
use std::path::PathBuf;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn main() -> std::process::ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("report") => report(),
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

fn report() -> std::process::ExitCode {
    let root = repo_root();
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
