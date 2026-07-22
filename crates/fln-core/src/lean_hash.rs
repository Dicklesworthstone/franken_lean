//! The Reference-observable hash primitives of the term plane.
//!
//! These are **compatibility observables**, not content addressing (that is fln-hash's
//! charter): `Name.hash`, `Level.hash`, and `Expr.hash` values are visible to user
//! metaprograms and must match the pin bit-for-bit.
//!
//! Semantics anchors (vendor/lean4-src at the SUITE.lock pin):
//! * `mix_hash` — `lean_uint64_mix_hash`, src/include/lean/lean.h:2055 (and the
//!   identical `lean::hash`, src/runtime/hash.h). Note the quirk faithfully kept:
//!   the second operand is XORed with the multiplier (`k ^= m`), not re-multiplied
//!   as in classic MurmurHash2 mixing.
//! * `string_hash` — `lean_string_hash`, src/runtime/object.cpp:2450: MurmurHash64A
//!   (src/runtime/hash.cpp) over the UTF-8 bytes *excluding* the trailing NUL, with
//!   seed 11.
//!
//! Golden vectors are generated from the pin's own C sources by
//! `scripts/gen_hash_fixtures.sh` into `tests/fixtures/hash_vectors.txt` (D5/D8-2:
//! derived, never remembered).

/// `mixHash` as the runtime implements it (`lean_uint64_mix_hash`).
#[inline]
pub const fn mix_hash(h: u64, mut k: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    (h ^ k).wrapping_mul(M)
}

/// MurmurHash64A exactly as src/runtime/hash.cpp compiles it on little-endian
/// targets (the pin reads 8-byte words with `memcpy`, i.e. host order; every
/// certified target is little-endian and the codec law pins that).
pub fn murmur_hash_64a(data: &[u8], seed: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;

    let len = data.len();
    let mut h: u64 = seed ^ (len as u64).wrapping_mul(M);

    let (chunks, tail) = data.as_chunks::<8>();
    for chunk in chunks {
        let mut k = u64::from_le_bytes(*chunk);
        k = k.wrapping_mul(M);
        k ^= k >> R;
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
    }

    if !tail.is_empty() {
        // The pin's switch fall-through, low byte last.
        for (i, byte) in tail.iter().enumerate().rev() {
            h ^= u64::from(*byte) << (8 * i as u64);
        }
        h = h.wrapping_mul(M);
    }

    h ^= h >> R;
    h = h.wrapping_mul(M);
    h ^= h >> R;
    h
}

/// `String.hash` (`lean_string_hash`): MurmurHash64A over the UTF-8 bytes with seed 11.
pub fn string_hash(s: &str) -> u64 {
    murmur_hash_64a(s.as_bytes(), 11)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mix_hash_matches_the_pins_quirk_not_classic_murmur() {
        // With k = 0: k*M = 0, k ^= k>>47 = 0, k ^= M = M, so
        // mix(h, 0) = (h ^ M) * M — a direct consequence of the `k ^= m` quirk.
        const M: u64 = 0xc6a4_a793_5bd1_e995;
        assert_eq!(mix_hash(0, 0), M.wrapping_mul(M));
        assert_eq!(mix_hash(5, 0), (5 ^ M).wrapping_mul(M));
    }

    #[test]
    fn murmur_empty_input_reduces_to_seed_finalization() {
        const M: u64 = 0xc6a4_a793_5bd1_e995;
        const R: u32 = 47;
        let mut h: u64 = 11; // seed ^ (0 * M)
        h ^= h >> R;
        h = h.wrapping_mul(M);
        h ^= h >> R;
        assert_eq!(string_hash(""), h);
    }

    #[test]
    fn murmur_covers_all_tail_lengths_deterministically() {
        // Structural determinism + tail coverage; exact values are locked by the
        // pin-derived golden vectors in tests/hash_vectors.rs.
        let data = b"abcdefghij";
        let mut seen = std::collections::BTreeSet::new();
        for len in 0..=data.len() {
            let h = murmur_hash_64a(&data[..len], 11);
            assert_eq!(h, murmur_hash_64a(&data[..len], 11));
            seen.insert(h);
        }
        assert_eq!(seen.len(), data.len() + 1, "distinct hashes per length");
    }
}
