//! The Reference's import-time identity rule for a name that more than one
//! module of an import set declares now lives in `fln_admission::olean_imports`
//! (bead `fln-import-reuse-composes-4ngt`), beside the council that applies it.
//! `fln`'s runtime still compares definitions with the same `Expr.eqv`.

pub(crate) use fln_admission::olean_imports::expr_eqv;
