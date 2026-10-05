//! Compare a fresh stdlib frontier with the retained receipt (bead `franken_lean-z8j.1.16`).
//!
//! ```text
//! fln check-olean --continue --json ... ~/.elan/toolchains/<pin>/lib/lean \
//!   | stdlib-frontier-ratchet [--receipt PATH]
//! stdlib-frontier-ratchet [--receipt PATH] CURRENT.json
//! ```
//!
//! The receipt defaults to `crates/fln-conformance/evidence/stdlib_frontier/v4.32.0.json`,
//! relative to the working directory. The report goes to stdout. Exit codes: 0 when no
//! coverage dropped (improvements are reported, never fatal), 1 when any module was lost,
//! stopped being accepted or changed its declaration count, and 2 when either document
//! cannot be read or is not a self-consistent frontier.
#![forbid(unsafe_code)]

use std::io::Read;
use std::process::ExitCode;

use fln_conformance::stdlib_frontier::{RETAINED_RECEIPT, compare, parse};

const USAGE: &str = "usage: stdlib-frontier-ratchet [--receipt PATH] [CURRENT.json | -]\n";

fn main() -> ExitCode {
    let mut receipt_path = RETAINED_RECEIPT.to_owned();
    let mut current_path: Option<String> = None;
    let mut arguments = std::env::args().skip(1);
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--receipt" => match arguments.next() {
                Some(path) => receipt_path = path,
                None => return usage("--receipt needs a path"),
            },
            "-h" | "--help" => {
                print!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            _ if current_path.is_none() => current_path = Some(argument),
            _ => return usage("more than one current document"),
        }
    }

    let receipt = match std::fs::read_to_string(&receipt_path) {
        Ok(text) => text,
        Err(error) => return refuse(&format!("cannot read the receipt {receipt_path}: {error}")),
    };
    let current = match current_path.as_deref() {
        None | Some("-") => {
            let mut text = String::new();
            match std::io::stdin().read_to_string(&mut text) {
                Ok(_) => text,
                Err(error) => return refuse(&format!("cannot read stdin: {error}")),
            }
        }
        Some(path) => match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(error) => return refuse(&format!("cannot read {path}: {error}")),
        },
    };
    let receipt = match parse(&receipt) {
        Ok(frontier) => frontier,
        Err(error) => return refuse(&format!("receipt {receipt_path}: {error}")),
    };
    let current = match parse(&current) {
        Ok(frontier) => frontier,
        Err(error) => return refuse(&format!("current frontier: {error}")),
    };
    let comparison = compare(&receipt, &current);
    print!("{}", comparison.render());
    if comparison.dropped() {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}

fn usage(problem: &str) -> ExitCode {
    eprint!("stdlib-frontier-ratchet: {problem}\n{USAGE}");
    ExitCode::from(2)
}

fn refuse(problem: &str) -> ExitCode {
    eprintln!("stdlib-frontier-ratchet: {problem}");
    ExitCode::from(2)
}
