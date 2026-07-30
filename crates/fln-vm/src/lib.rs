//! **fln-vm** — Golem's VM — the FLBC register interpreter and the intrinsic table over the extern census; values are Marrow ABI objects (plan §11.2, §11.4).
//!
//! The crate's first landed layer is the W5 dispatch foundation (bead
//! `franken_lean-pw6t`): the canonical extern row contract
//! ([`extern_row`], [`extern_table_generated`], [`load`]) and the intrinsic
//! registry ([`dispatch`]). The interpreter and the value model arrive with
//! the workstream's execution beads; the crate map and layering are governed
//! by `WORKSPACE_GRAPH.txt` (bead fln-8mj).

#![forbid(unsafe_code)]

pub mod dispatch;
pub mod extern_row;
pub mod extern_table_generated;
pub mod load;
