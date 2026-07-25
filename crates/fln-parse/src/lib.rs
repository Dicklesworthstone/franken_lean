//! **fln-parse** — Vellum's engine — the extensible Pratt parser preserving parse/elaborate interleaving, byte-exact positions, and error recovery that never changes acceptance (plan §9).
//!
//! Stub crate: charter only. Implementation arrives with its workstream beads;
//! the crate map and layering are governed by `WORKSPACE_GRAPH.txt` (bead fln-8mj).

#![forbid(unsafe_code)]

pub mod state;
