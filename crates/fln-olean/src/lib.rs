//! **fln-olean** — Grimoire's module codec — byte-compatible `.olean` read and write, `.ilean`, and the olean-next frontier format (plan §7.2–7.4).
//!
//! Stub crate: charter only. Implementation arrives with its workstream beads;
//! the crate map and layering are governed by `WORKSPACE_GRAPH.txt` (bead fln-8mj).

#![forbid(unsafe_code)]

pub mod decl;
pub mod format;
pub mod region;
