//! decode_olean — robot-lane driver for the declaration decoder (bead
//! franken_lean-z6c seed). Decodes every constant of each `.olean` argument
//! into FrankenLean term-plane values with stored-vs-recomputed cross-checks
//! (Name.hash / Level.Data / Expr.Data, bit-for-bit) and emits one line per
//! file:
//!
//!   `path <TAB> consts <TAB> axioms,defns,thms,opaques,quots,inducts,ctors,recs <TAB> status`
//!
//! Exit 0 iff every file decodes clean. stdout is data-only.

#![forbid(unsafe_code)]

use std::process::ExitCode;

use fln_env::constants::ConstantInfo;
use fln_olean::decl::DeclDecoder;
use fln_olean::region::{OleanView, WalkBudget};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("usage: decode_olean <file.olean> [...]");
        return ExitCode::from(2);
    }
    let mut failures = 0u32;
    for path in &args {
        match std::fs::read(path) {
            Err(e) => {
                println!("{path}\t-\t-\terror:io:{e}");
                failures += 1;
            }
            Ok(bytes) => match decode_one(&bytes) {
                Ok((n, kinds)) => {
                    let k = kinds.map(|c| c.to_string()).join(",");
                    println!("{path}\t{n}\t{k}\tok");
                }
                Err(e) => {
                    println!("{path}\t-\t-\terror:{e}");
                    failures += 1;
                }
            },
        }
    }
    if failures > 0 {
        eprintln!("decode_olean: {failures}/{} files failed", args.len());
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn decode_one(bytes: &[u8]) -> Result<(usize, [u64; 8]), String> {
    let view = OleanView::parse(bytes).map_err(|e| e.to_string())?;
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    let infos = decoder
        .decode_module_constants()
        .map_err(|e| e.to_string())?;
    let mut kinds = [0u64; 8];
    for info in &infos {
        let idx = match info {
            ConstantInfo::Axiom(_) => 0,
            ConstantInfo::Defn(_) => 1,
            ConstantInfo::Thm(_) => 2,
            ConstantInfo::Opaque(_) => 3,
            ConstantInfo::Quot(_) => 4,
            ConstantInfo::Induct(_) => 5,
            ConstantInfo::Ctor(_) => 6,
            ConstantInfo::Rec(_) => 7,
        };
        kinds[idx] += 1;
    }
    Ok((infos.len(), kinds))
}
