//! Loss-free conversions between [`crate::nat::BigNat`] and the term-plane literal
//! value `fln_core::expr::NatLit` (bead franken_lean-npl).
//!
//! Both types are little-endian, normalized `u64` limb vectors, so conversion is a
//! straight limb copy in each direction — no arithmetic, no failure modes. The
//! Reference-observable literal hash (`NatLit::hash` = value mod 2^64 = low limb)
//! is preserved by construction; the consistency test pins it.

use fln_core::expr::NatLit;

use crate::nat::BigNat;

/// `NatLit` → `BigNat` (loss-free).
pub fn bignat_from_literal(lit: &NatLit) -> BigNat {
    BigNat::from_limbs_le(lit.limbs_le().to_vec())
}

/// `BigNat` → `NatLit` (loss-free).
pub fn literal_from_bignat(value: &BigNat) -> NatLit {
    NatLit::from_limbs_le(value.limbs_le().to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_are_identity_and_preserve_the_observable_hash() {
        let cases: Vec<Vec<u64>> = vec![
            vec![],
            vec![1],
            vec![u64::MAX],
            vec![0, 1],
            vec![5, 1 << 16],
            vec![u64::MAX, u64::MAX, 7],
        ];
        for limbs in cases {
            let lit = NatLit::from_limbs_le(limbs.clone());
            let big = bignat_from_literal(&lit);
            assert_eq!(big.limbs_le(), lit.limbs_le());
            let back = literal_from_bignat(&big);
            assert_eq!(back, lit);
            // The Reference-observable hash (value mod 2^64) survives the trip.
            assert_eq!(back.hash(), lit.hash());
            assert_eq!(big.limbs_le().first().copied().unwrap_or(0), lit.hash());
        }
    }

    #[test]
    fn arithmetic_results_feed_back_into_literals() {
        // The kernel path: literal -> BigNat -> accelerated op -> literal.
        let a = NatLit::from_limbs_le(vec![u64::MAX, 1]);
        let b = NatLit::from_u64(2);
        let sum = literal_from_bignat(&bignat_from_literal(&a).add(&bignat_from_literal(&b)));
        // (2^64 + (2^64 - 1)) + 2 = 2^65 + 1 → limbs [1, 2].
        assert_eq!(sum.limbs_le(), &[1, 2]);
    }
}
