//! The checker-reader probe (bead `franken_lean-z8j.1.14`).
//!
//! Its only reference into the workspace is `fln::independent_reading`, the independent
//! checker's whole `.olean` input path, taken as a function pointer and made opaque. As with
//! `tcb-probe`, the linker garbage-collects every function section nothing reaches, so the
//! `fln_*` functions this binary keeps are exactly what that path can call.
//! `tests/checker_reader_closure.rs` reads them back and refuses any that belong to the
//! primary's decode path.
//!
//! Do not reference anything else from the workspace here: every extra reference would be
//! counted as part of the checker's input path.
#![forbid(unsafe_code)]

use fln::{IndependentReading, OleanDecodeLimits};

fn main() {
    let read: fn(&[&[u8]], OleanDecodeLimits) -> IndependentReading = fln::independent_reading;
    std::hint::black_box(read);
}
