//! Publish or verify an epoch laboratory's revision chain (bead `fln-q3u4`).
//!
//! ```text
//! cargo run --manifest-path tribunal/epoch-lab/Cargo.toml -- verify  <epoch-tag>
//! cargo run --manifest-path tribunal/epoch-lab/Cargo.toml -- publish <epoch-tag>
//! ```
//!
//! `verify` is read-only and is the one a gate runs. `publish` appends a
//! revision for the manifest currently on disk, failure-atomically, and is a
//! no-op when the content already matches the head — the chain records content,
//! not invocations.
//!
//! Output is one line-oriented record so this is pipeable and diffable, per the
//! agent-ergonomics rule: machine fields, no decoration.

#![forbid(unsafe_code)]

use fln_epoch_lab::{CHAIN_FILE, publish, verify_epoch};

const MANIFEST: &str = "MANIFEST.txt";

fn main() -> std::process::ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (verb, epoch) = match args.as_slice() {
        [v, e] => (v.as_str(), e.as_str()),
        _ => {
            eprintln!("usage: epoch-lab <verify|publish> <epoch-tag>");
            return std::process::ExitCode::from(2);
        }
    };
    // Resolved from the crate, not the cwd, so the tool cannot be pointed at a
    // different tree by accident. `checked_manifest_dir!` also refuses a binary
    // compiled for another checkout (shared CARGO_TARGET_DIR). The documented
    // launch path is `cargo run`, which sets the invoking-package directory.
    let dir = fln_core::checked_manifest_dir!()
        .join("../epochs")
        .join(epoch);
    if !dir.is_dir() {
        eprintln!(
            "epoch-lab: inconclusive reason=absent_epoch dir={}",
            dir.display()
        );
        return std::process::ExitCode::from(2);
    }

    match verb {
        "verify" => match verify_epoch(&dir, epoch, MANIFEST) {
            Ok(chain) => {
                println!(
                    "epoch-lab: verdict=pass epoch={epoch} revisions={} head_index={} head_root={}",
                    chain.revisions().len(),
                    chain.head().index,
                    chain.head().root.to_hex()
                );
                std::process::ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("epoch-lab: verdict=fail epoch={epoch} reason={e}");
                std::process::ExitCode::FAILURE
            }
        },
        "publish" => match publish(&dir, epoch, MANIFEST) {
            Ok(r) => {
                println!(
                    "epoch-lab: verdict=pass epoch={epoch} action={} index={} root={} chain={}",
                    if r.already_current {
                        "already-current"
                    } else {
                        "appended"
                    },
                    r.index,
                    r.root,
                    dir.join(CHAIN_FILE).display()
                );
                std::process::ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("epoch-lab: verdict=fail epoch={epoch} reason={e}");
                std::process::ExitCode::FAILURE
            }
        },
        other => {
            eprintln!("epoch-lab: unknown verb {other:?}");
            std::process::ExitCode::from(2)
        }
    }
}
