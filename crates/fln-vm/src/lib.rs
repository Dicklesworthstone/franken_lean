//! **fln-vm** — Golem's VM — the FLBC register interpreter and the intrinsic table over the extern census; values are Marrow ABI objects (plan §11.2, §11.4).
//!
//! The crate's first landed layer is the W5 dispatch foundation (bead
//! `franken_lean-pw6t`): the canonical extern row contract
//! ([`extern_row`], [`extern_table_generated`], [`load`]) and the intrinsic
//! registry ([`dispatch`]). A retained G0-3 prototype now also provides a
//! validated, ABI-valued register interpreter ([`interpreter`]); it prices the
//! execution membrane without claiming the complete W5 production interpreter,
//! effects, plugins, or PG-7. The crate map and layering are governed by
//! `WORKSPACE_GRAPH.txt` (bead fln-8mj).

#![forbid(unsafe_code)]

pub mod dispatch;
pub mod extern_row;
pub mod extern_table_generated;
pub mod interpreter;
pub mod load;
pub mod parity;
