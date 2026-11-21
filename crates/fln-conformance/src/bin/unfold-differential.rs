//! Tribunal CLI probe for K1 vs pinned-Reference kernel unfold-count differential
//! (bead `fln-kernel-unfold-differential-tfvw`).
//!
//! Usage:
//!   unfold-differential scan [--max-steps N] --module Mod <root1> [root2...]
//!   unfold-differential diff [--max-steps N] [--top K] --pin-lean <bin> --workspace <dir> \
//!       --module Mod --decl Decl <root1> [root2...]
#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::ExitCode;

use fln_conformance::unfold_differential::{
    LoadedOleanModule, join_and_rank, run_pin_unfold_counts,
};
use fln_kernel::verdict::Budget;

const WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let handle = std::thread::Builder::new()
        .name("unfold-differential-main".to_owned())
        .stack_size(WORKER_STACK_BYTES)
        .spawn(move || run(&args))
        .expect("spawn unfold-differential worker");
    match handle.join() {
        Ok(Ok(())) => ExitCode::SUCCESS,
        Ok(Err(err)) => {
            eprintln!("error: {err}");
            ExitCode::FAILURE
        }
        Err(_) => {
            eprintln!("error: worker thread panicked");
            ExitCode::FAILURE
        }
    }
}

fn run(args: &[String]) -> Result<(), String> {
    let Some(mode) = args.first().map(String::as_str) else {
        return Err("expected subcommand `scan` or `diff`".to_owned());
    };
    let mut max_steps: Option<u64> = None;
    let mut top: usize = 15;
    let mut module: Option<String> = None;
    let mut decl: Option<String> = None;
    let mut pin_lean: Option<PathBuf> = None;
    let mut workspace = PathBuf::from(".");
    let mut force_left_delta = false;
    let mut roots: Vec<PathBuf> = Vec::new();

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--max-steps" => {
                i += 1;
                let raw = args.get(i).ok_or("--max-steps requires a value")?;
                max_steps = Some(
                    raw.parse::<u64>()
                        .map_err(|e| format!("bad --max-steps: {e}"))?,
                );
            }
            "--top" => {
                i += 1;
                let raw = args.get(i).ok_or("--top requires a value")?;
                top = raw
                    .parse::<usize>()
                    .map_err(|e| format!("bad --top: {e}"))?;
            }
            "--module" => {
                i += 1;
                module = Some(args.get(i).ok_or("--module requires a value")?.clone());
            }
            "--decl" => {
                i += 1;
                decl = Some(args.get(i).ok_or("--decl requires a value")?.clone());
            }
            "--pin-lean" => {
                i += 1;
                pin_lean = Some(PathBuf::from(
                    args.get(i).ok_or("--pin-lean requires a value")?,
                ));
            }
            "--workspace" => {
                i += 1;
                workspace = PathBuf::from(args.get(i).ok_or("--workspace requires a value")?);
            }
            "--force-left-delta" => force_left_delta = true,
            other if other.starts_with("--") => {
                return Err(format!("unknown option `{other}`"));
            }
            path => roots.push(PathBuf::from(path)),
        }
        i += 1;
    }

    let module = module.ok_or("--module is required")?;
    if roots.is_empty() {
        return Err("at least one .olean search root is required".to_owned());
    }
    let mut budget = Budget::for_stack_bytes(WORKER_STACK_BYTES);
    if let Some(steps) = max_steps {
        budget.steps = steps;
    }

    let loaded = LoadedOleanModule::load(&roots, &module)?;
    match mode {
        "scan" => {
            let rows = loaded.scan_declarations(budget)?;
            let stuck: Vec<_> = rows.iter().filter(|r| r.verdict != "accepted").collect();
            println!(
                "SCAN module={module} total_constants={} checked={} stuck={} max_steps={}",
                loaded.declaration_count(),
                rows.len(),
                stuck.len(),
                budget.steps
            );
            for row in rows.iter().take(top) {
                println!(
                    "  {:<13} steps={:<12} ms={:<9.2} {}",
                    row.verdict,
                    row.steps_used,
                    row.wall.as_secs_f64() * 1e3,
                    row.name
                );
            }
            Ok(())
        }
        "diff" => {
            let decl = decl.ok_or("--decl is required for `diff`")?;
            let pin_lean = pin_lean.ok_or("--pin-lean is required for `diff`")?;
            let lean_path = roots
                .iter()
                .map(|p| p.to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join(":");
            let pin_table =
                run_pin_unfold_counts(&workspace, &pin_lean, &lean_path, &module, &decl)?;
            let k1_run = loaded.observe_declaration(&decl, budget, force_left_delta)?;
            let k1_counts = k1_run.display_counts();
            let report = join_and_rank(&k1_counts, &pin_table.counts);
            println!(
                "DIFF module={module} decl={decl} k1_verdict={} k1_steps={} k1_ms={:.2} pin_verdict={} pin_ms={:.2} pin_rows={} k1_rows={}",
                k1_run.verdict_label(),
                k1_run.observation.steps_used,
                k1_run.wall.as_secs_f64() * 1e3,
                pin_table.verdict,
                (pin_table.wall_ns as f64) / 1e6,
                pin_table.counts.len(),
                k1_counts.len(),
            );
            if !k1_run.observation.cache_summary.is_empty() {
                println!("CACHES {}", k1_run.observation.cache_summary);
            }
            print!("{}", report.render_top(top));
            Ok(())
        }
        other => Err(format!(
            "unknown subcommand `{other}` (expected `scan` or `diff`)"
        )),
    }
}
