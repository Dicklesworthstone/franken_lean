//! **fln-bignum** — kernel-grade arbitrary-precision natural-number arithmetic —
//! the owned replacement for GMP under every literal (plan §8.4, §21; bead
//! franken_lean-npl).
//!
//! The operation surface is exactly the kernel-accelerated set of
//! `KERNEL_CONTRACT.md` KR-313, with Lean's `Nat` semantics baked in: truncated
//! subtraction, `x / 0 = 0`, `x % 0 = x`. Ground truth is the generated golden
//! corpus (`fixtures/nat_vectors.txt`, 5 725 vectors from CPython bignums via
//! `scripts/extract/gen_bignum_vectors.py` — derived, never remembered).
//!
//! Layout note: [`nat::BigNat`] stores little-endian, normalized `u64` limbs —
//! deliberately identical to `fln_core::expr::NatLit`, so [`interop`] conversions
//! are loss-free and O(n) copies. The ABI-facing limb layout (the `lean_object`
//! scalar/bignum boundary) is a separate obligation pinned to the extracted ABI
//! contract (bead franken_lean-53v) and is NOT provided here yet.

#![forbid(unsafe_code)]

pub mod interop;
pub mod nat;
