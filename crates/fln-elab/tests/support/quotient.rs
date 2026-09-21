#![forbid(unsafe_code)]

//! Quotient tests use the same candidate as the production source seed.
//! It still enters each test environment through ordinary K1 block admission.
pub use fln_elab::seed::quotient_seed_declaration as quotient_declaration;
