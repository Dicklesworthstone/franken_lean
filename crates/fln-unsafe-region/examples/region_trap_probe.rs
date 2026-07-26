//! Hardened trap-on-write probe (bead fln-wgp slice 2 — region hygiene,
//! plan §6.4): after `seal`, a region mapping is immutable three ways, and
//! this probe proves each one as a separate mode for the e2e drill:
//!
//! * `no-write` — the sealed mapping stays fully readable (positive control);
//! * `safe-write` — the safe surface refuses mutation with the typed
//!   `MapError::Sealed`, never a fault (FL-INV-07 on the API plane);
//! * `raw-write` — a raw pointer write to the sealed page (the move a buggy
//!   plugin or JIT stub would make through the ABI membrane) dies by SIGSEGV.
//!   The parent harness asserts the signal; if the write *survives*, the probe
//!   reports the broken hardening and exits 5 so the lane fails loudly.
//!
//! Emits NDJSON facts (schema `fln-region-trap/1`) on stdout. Exit codes:
//! 0 = mode's law held (for `raw-write` the process must instead die by
//! signal), 2 = usage, 3 = setup failure, 4 = safe surface failed to refuse,
//! 5 = raw write did not trap.

#![deny(unsafe_code)]
#![deny(clippy::undocumented_unsafe_blocks)]

use fln_unsafe_region::mapping::{MapError, RegionMapping};

fn fact(kind: &str, body: &str) {
    // Stdout is line-buffered: each fact is flushed by its newline, so the
    // pre-write facts survive the SIGSEGV that ends the raw-write mode.
    println!("{{\"schema\":\"fln-region-trap/1\",\"{kind}\":{body}}}");
}

/// The deliberate invariant violation the drill exists to punish: one raw
/// byte store into the sealed mapping.
///
/// SAFETY: none claimed — this site deliberately breaks the sealed-region
/// immutability invariant to prove the hardware trap. It runs only inside
/// the Tribunal's trap lane, in a child process whose expected fate is
/// SIGSEGV; the store is volatile so it cannot be elided, and nothing after
/// it is trusted (a surviving write is reported and the lane fails).
// UNSAFE-LEDGER: FLN-UL-0063
#[allow(unsafe_code)]
fn raw_write(addr: usize) {
    // SAFETY: none claimed, deliberately — this is the invariant violation the drill
    // exists to punish, and the doc comment above states the full justification: the
    // probe runs only in the trap lane's child process, whose expected fate is SIGSEGV,
    // the store is volatile so it cannot be elided, and nothing after it is trusted.
    // The note is repeated here because `clippy::undocumented_unsafe_blocks` reads the
    // comment attached to the BLOCK, not the one attached to the function (bead
    // `franken_lean-d3-safety-note-unenforced-cdbg`).
    unsafe { std::ptr::write_volatile(addr as *mut u8, 0xFF) }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let (Some(file), Some(mode)) = (args.next(), args.next()) else {
        eprintln!("usage: region_trap_probe <region-file> <no-write|safe-write|raw-write>");
        std::process::exit(2);
    };

    let mut mapping = match RegionMapping::map_file_private(std::path::Path::new(&file)) {
        Ok(m) => m,
        Err(e) => {
            fact("setup", &format!("{{\"ok\":false,\"error\":\"{e}\"}}"));
            std::process::exit(3);
        }
    };
    // Touch the first page read-only so the drill faults on protection, not
    // on first-fault-in of an untouched page.
    let first = mapping.as_slice()[0];
    if let Err(e) = mapping.seal() {
        fact(
            "setup",
            &format!("{{\"ok\":false,\"error\":\"seal: {e}\"}}"),
        );
        std::process::exit(3);
    }
    fact(
        "sealed",
        &format!(
            "{{\"len\":{},\"first_byte\":{first},\"mode\":\"{mode}\"}}",
            mapping.len()
        ),
    );

    match mode.as_str() {
        "no-write" => {
            // Reads must keep working after seal — checksum the first pages.
            let sum: u64 = mapping
                .as_slice()
                .iter()
                .take(4096)
                .map(|b| u64::from(*b))
                .sum();
            fact(
                "verdict",
                &format!(
                    "{{\"ok\":true,\"law\":\"sealed region stays readable\",\"checksum\":{sum}}}"
                ),
            );
        }
        "safe-write" => match mapping.as_mut_slice() {
            Err(MapError::Sealed) => {
                fact(
                    "verdict",
                    "{\"ok\":true,\"law\":\"safe surface refuses sealed mutation typed\"}",
                );
            }
            Err(e) => {
                fact(
                    "verdict",
                    &format!("{{\"ok\":false,\"law\":\"wrong refusal type\",\"error\":\"{e}\"}}"),
                );
                std::process::exit(4);
            }
            Ok(_) => {
                fact(
                    "verdict",
                    "{\"ok\":false,\"law\":\"safe surface handed out a mutable view of a sealed region\"}",
                );
                std::process::exit(4);
            }
        },
        "raw-write" => {
            fact(
                "attempting_raw_write",
                "{\"expected\":\"SIGSEGV terminates this process before the next fact\"}",
            );
            raw_write(mapping.addr());
            // Reaching this line means the kernel let the write through:
            // the hardening is broken and the lane must fail.
            fact(
                "verdict",
                "{\"ok\":false,\"law\":\"raw write to a sealed region did not trap\"}",
            );
            std::process::exit(5);
        }
        other => {
            eprintln!("unknown mode {other}");
            std::process::exit(2);
        }
    }
}
