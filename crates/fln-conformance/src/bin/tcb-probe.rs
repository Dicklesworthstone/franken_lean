//! The TCB-inventory probe (bead `franken_lean-z8j.1.17`).
//!
//! Its only reference into the workspace is the kernel's one authority, `fln_kernel::check`,
//! taken as a function pointer and made opaque. The linker garbage-collects every function
//! section nothing reaches, so the functions this binary keeps from the `fln_*` crates are
//! exactly the code the linker sees as reachable from `check`. `tests/tcb_inventory.rs` reads
//! that set out of this binary's symbol table; see `fln_conformance::tcb_inventory` for what
//! the measurement does and does not establish.
//!
//! Do not reference anything else from the workspace here: every extra reference would be
//! counted as trusted code.
#![forbid(unsafe_code)]

use fln_core::outcome::Outcome;
use fln_env::environment::Environment;
use fln_kernel::Declaration;
use fln_kernel::verdict::{Budget, Verdict};

fn main() {
    let check: fn(&Environment, &Declaration, Budget) -> Outcome<Verdict> = fln_kernel::check;
    std::hint::black_box(check);
}
