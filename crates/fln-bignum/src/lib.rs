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
//! deliberately identical to `fln_core::expr::NatLit`. [`nat::BigNatView`]
//! borrows that representation without allocation, and Marrow's `Obj::mpz_view`
//! binds the same view to the lifetime of the ABI object. Arithmetic therefore
//! reads ABI operands in place and allocates only results; the runtime-private
//! mpz layout remains pinned by the G0-1/C4 evidence rather than by the public
//! `lean.h` tables.

#![forbid(unsafe_code)]

pub mod interop;
pub mod nat;
