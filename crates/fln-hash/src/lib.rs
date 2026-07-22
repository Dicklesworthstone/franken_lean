//! **fln-hash** — owned BLAKE3 hashing, the domain-separation registry, and canonical
//! serialization schemas (plan §7, §21; bead franken_lean-rps): the identity layer
//! beneath the Ledger (decl hashes, logical roots), Grimoire (semantic vs byte hash),
//! receipts, the transparency log, and every cache key in the program.
//!
//! The three laws this crate enforces structurally:
//! * **Domain separation is a registry, not a convention** — every digest is produced
//!   through a [`domain::Domain`] variant; raw hashing is `pub(crate)`-shaped so no
//!   call site outside this crate can hash without naming its registered domain.
//! * **Canonical serialization is versioned** — [`canon`] defines one schema-tagged
//!   byte encoding per durable value; re-encoding freedom is zero by construction.
//! * **Logical roots exclude the operational world** — [`root`] digests declarations,
//!   extension deltas, and options; wall-clock, paths, and scheduler traces have no
//!   API through which to enter (plan §7.1).
//!
//! The hash core is an owned, from-scratch BLAKE3 ([`blake3`]) verified against the
//! official public test vectors (fixtures carry provenance); D1's closed universe
//! means no external crate is involved anywhere.

#![forbid(unsafe_code)]

pub mod blake3;
pub mod canon;
pub mod domain;
pub mod root;
