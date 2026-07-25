//! **fln-syntax** — `Syntax`, `SourceInfo`, and hygiene structures shared by Vellum and user metaprograms (plan §9, §21).
//!
//! Implementation arrives by bead; the crate map and layering are governed by
//! `WORKSPACE_GRAPH.txt` (bead fln-8mj). This crate declares **no dependency edges**, and
//! [`source`] is written to need none — see its module docs for why the position
//! substrate is self-contained.

#![forbid(unsafe_code)]

pub mod attach;
pub mod literal;
pub mod recover;
pub mod rope;
pub mod run;
pub mod source;
pub mod token;
pub mod tree;
pub mod trivia;
pub mod view;

#[cfg(test)]
mod edge_smoke {
    /// The edge declared in ci/WORKSPACE_GRAPH.txt is real: fln-core is reachable, which
    /// is what the Syntax forms need for SyntaxNodeKind and ident (bead franken_lean-vrmi).
    #[test]
    fn fln_core_is_reachable_from_fln_syntax() {
        let name = fln_core::name::Name::str(fln_core::name::Name::anonymous(), "Nat");
        assert_eq!(name.to_display_string(), "Nat");
    }
}
