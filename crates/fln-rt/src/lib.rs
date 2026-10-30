//! **fln-rt** — Marrow's safe surface — object views, reference-counting discipline, and effects on asupersync (plan §6, §21).
//!
//! Two planes (bead fln-lld):
//!
//! * [`abi`] — the generated ABI contract tables (tags, layout constants,
//!   struct field specs, the full `lean_*` function census), extracted
//!   mechanically from the pinned `lean.h` (Rule D5/D9; regenerate with
//!   `scripts/extract/gen_abi_contract.py`).
//! * [`obj`] — the safe CompatHeap object API over `fln-unsafe-abi`'s
//!   membrane: RAII [`obj::Obj`] handles (linear owned references), the
//!   [`obj::Header`] view, and the ownership-shadow controls. Every item
//!   crossing the boundary crate's edge carries a reviewed row in
//!   `ci/BOUNDARY_API.txt` (D3 law b no-admission covenant).
//!
//! This crate is `forbid(unsafe_code)`: the safety of everything here rests
//! on the boundary crate's ledgered membrane plus the covenant, never on
//! local unsafe. The allocation-linked heartbeat state is exposed through
//! [`heartbeat`]; the remaining IO/Task semantics on asupersync arrive with
//! bead fln-3gv.

#![forbid(unsafe_code)]

pub mod abi;
pub mod convert;
pub mod native_heap;
pub mod region;
mod region_contract;
pub mod syntax_abi_generated;

/// The safe CompatHeap object surface (see the crate docs).
pub mod obj {
    pub use fln_unsafe_abi::handle::fs::{FileIoError, FileReadError};
    pub use fln_unsafe_abi::handle::stdout_capture::{
        CapturedStdout, StdoutCapture, StdoutCaptureError,
    };
    pub use fln_unsafe_abi::handle::{
        EXTERNAL_FINALIZED, Obj, StdioPutStrError, flush_native_stdout,
    };
    pub use fln_unsafe_abi::rc::Header;
    /// Ownership-shadow controls: deterministic replay events, quarantine
    /// discipline, and fault detection (plan §6.2 hardened builds).
    pub mod shadow {
        pub use fln_unsafe_abi::shadow::{
            EventKind, ShadowEvent, disable_and_drain, enable, enabled,
        };
    }
}

/// Allocation-linked runtime heartbeat state shared by Marrow, generated C,
/// and Golem's `IO.getNumHeartbeats` / `IO.setNumHeartbeats` intrinsic rows.
pub mod heartbeat {
    pub use fln_unsafe_abi::{allocation_heartbeats, set_allocation_heartbeats};
}

/// Language diagnostics shared by generated native code and Golem. These
/// report runtime effects only; no kernel or declaration authority crosses
/// this boundary. Panic reporting observes the existing runtime panic policy.
pub mod diagnostics {
    pub use fln_unsafe_abi::{report_panic, trace_message};
}
