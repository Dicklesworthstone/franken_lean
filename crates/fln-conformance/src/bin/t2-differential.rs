//! Tribunal CLI for file-scale T2/T3 declaration-identity differential runs
//! against the pinned Reference `lean -o` (bead `fln-file-scale-t2-differential-5f1b`).
//!
//! Usage:
//!   t2-differential [--workspace DIR] [--pin-lean BIN] [--jobs N] [--write-ledger] [--log PATH]
#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use fln_conformance::t2_differential::T2NormalizerId;
use fln_conformance::t2_differential::runner::{RunOptions, run_file_scale_differential};

fn suite_lock_field(root: &Path, prefix: &str) -> Option<String> {
    let lock = fs::read_to_string(root.join("SUITE.lock")).ok()?;
    lock.lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))?
        .split_whitespace()
        .find_map(|field| field.strip_prefix(prefix).map(str::to_owned))
}

fn default_pin_lean(tag: &str) -> Option<PathBuf> {
    if let Ok(path) = std::env::var("FLN_REFERENCE_BIN") {
        let candidate = PathBuf::from(path);
        return candidate.is_file().then_some(candidate);
    }
    let home = std::env::var_os("HOME")?;
    let candidate = PathBuf::from(home)
        .join(".elan/toolchains")
        .join(format!("leanprover--lean4---{tag}"))
        .join("bin/lean");
    candidate.is_file().then_some(candidate)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut workspace: Option<PathBuf> = None;
    let mut pin_lean_override: Option<PathBuf> = None;
    let mut options = RunOptions::default();

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--workspace" => {
                i += 1;
                let Some(val) = args.get(i) else {
                    eprintln!("error: --workspace requires a path");
                    return ExitCode::from(2);
                };
                workspace = Some(PathBuf::from(val));
            }
            "--pin-lean" => {
                i += 1;
                let Some(val) = args.get(i) else {
                    eprintln!("error: --pin-lean requires a path");
                    return ExitCode::from(2);
                };
                pin_lean_override = Some(PathBuf::from(val));
            }
            "--jobs" => {
                i += 1;
                let Some(val) = args.get(i) else {
                    eprintln!("error: --jobs requires a positive integer");
                    return ExitCode::from(2);
                };
                match val.parse::<usize>().ok().filter(|n| *n > 0) {
                    Some(n) => options.workers = n,
                    None => {
                        eprintln!("error: invalid --jobs value {val:?}");
                        return ExitCode::from(2);
                    }
                }
            }
            "--write-ledger" => options.write_ledger = true,
            "--log" => {
                i += 1;
                let Some(val) = args.get(i) else {
                    eprintln!("error: --log requires a path");
                    return ExitCode::from(2);
                };
                options.log_path = Some(PathBuf::from(val));
            }
            other => {
                eprintln!("error: unknown option {other:?}");
                return ExitCode::from(2);
            }
        }
        i += 1;
    }

    let root =
        workspace.unwrap_or_else(|| std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")));
    let Some(pin_tag) = suite_lock_field(&root, "tag=") else {
        eprintln!(
            "error: SUITE.lock under {} has no reference tag",
            root.display()
        );
        return ExitCode::from(3);
    };
    let Some(pin_commit) = suite_lock_field(&root, "commit=") else {
        eprintln!(
            "error: SUITE.lock under {} has no reference commit",
            root.display()
        );
        return ExitCode::from(3);
    };
    let Some(pin_lean) = pin_lean_override.or_else(|| default_pin_lean(&pin_tag)) else {
        eprintln!("error: pinned Reference lean for {pin_tag} not found");
        return ExitCode::from(3);
    };

    match run_file_scale_differential(&root, &pin_lean, &pin_tag, &pin_commit, &options) {
        Ok(summary) => {
            println!(
                "t2-differential: pin={} commit={} binary={} normalizer={} total={}",
                summary.pin_tag,
                summary.pin_commit,
                &summary.binary_digest[..16],
                T2NormalizerId::V1.as_str(),
                summary.observed.len()
            );
            for (family, s) in &summary.per_family {
                println!(
                    "  family={family:<15} total={:<3} both_accept={:<3} both_reject={:<2} native_rejects={:<2} false_accept={} inconclusive={} primary_t2_id={:<3} full_t2_id={:<3} t3_id={:<3}",
                    s.total,
                    s.both_accept,
                    s.both_reject,
                    s.native_rejects,
                    s.false_accept,
                    s.inconclusive,
                    s.primary_t2_identical,
                    s.full_t2_identical,
                    s.t3_identical
                );
            }
            for imp in &summary.improvements {
                println!("  {imp}");
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}
