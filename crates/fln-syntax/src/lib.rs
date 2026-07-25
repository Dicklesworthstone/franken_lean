//! **fln-syntax** — `Syntax`, `SourceInfo`, and hygiene structures shared by Vellum and user metaprograms (plan §9, §21).
//!
//! Implementation arrives by bead; the crate map and layering are governed by
//! `WORKSPACE_GRAPH.txt` (bead fln-8mj). This crate declares **no dependency edges**, and
//! [`source`] is written to need none — see its module docs for why the position
//! substrate is self-contained.

#![forbid(unsafe_code)]

pub mod attach;
pub mod rope;
pub mod source;
pub mod view;
