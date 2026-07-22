//! BLAKE3 (spec: "BLAKE3: one function, fast everywhere", §2 "The BLAKE3
//! compression function" and §2.1 "Tree hashing and chunk processing").
//!
//! Owned, from-scratch, safe-Rust implementation of all three modes —
//! `hash`, `keyed_hash`, and `derive_key` — with incremental updating and
//! extendable output (XOF). Verified against the official upstream test
//! vectors in `fixtures/blake3_vectors.txt`.

/// Bytes in the default hash output.
pub const OUT_LEN: usize = 32;
/// Bytes in a `keyed_hash` key.
pub const KEY_LEN: usize = 32;

const BLOCK_LEN: usize = 64;
const CHUNK_LEN: usize = 1024;

/// Domain flags (spec §2.3 "Flags"; d-word inputs to the compression function).
const CHUNK_START: u32 = 1 << 0;
const CHUNK_END: u32 = 1 << 1;
const PARENT: u32 = 1 << 2;
const ROOT: u32 = 1 << 3;
const KEYED_HASH: u32 = 1 << 4;
const DERIVE_KEY_CONTEXT: u32 = 1 << 5;
const DERIVE_KEY_MATERIAL: u32 = 1 << 6;

/// Initialization vector (spec §2.2, table 1): the first eight SHA-256 IV words.
const IV: [u32; 8] = [
    0x6A09_E667,
    0xBB67_AE85,
    0x3C6E_F372,
    0xA54F_F53A,
    0x510E_527F,
    0x9B05_688C,
    0x1F83_D9AB,
    0x5BE0_CD19,
];

/// Message-word permutation applied between rounds (spec §2.2, table 2).
const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

/// The quarter-round mixing function G (spec §2.2, fig. 2).
fn g(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, mx: u32, my: u32) {
    state[a] = state[a].wrapping_add(state[b]).wrapping_add(mx);
    state[d] = (state[d] ^ state[a]).rotate_right(16);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_right(12);
    state[a] = state[a].wrapping_add(state[b]).wrapping_add(my);
    state[d] = (state[d] ^ state[a]).rotate_right(8);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_right(7);
}

/// One full round: G over the four columns, then the four diagonals.
fn round(state: &mut [u32; 16], m: &[u32; 16]) {
    g(state, 0, 4, 8, 12, m[0], m[1]);
    g(state, 1, 5, 9, 13, m[2], m[3]);
    g(state, 2, 6, 10, 14, m[4], m[5]);
    g(state, 3, 7, 11, 15, m[6], m[7]);
    g(state, 0, 5, 10, 15, m[8], m[9]);
    g(state, 1, 6, 11, 12, m[10], m[11]);
    g(state, 2, 7, 8, 13, m[12], m[13]);
    g(state, 3, 4, 9, 14, m[14], m[15]);
}

fn permute(m: &mut [u32; 16]) {
    let mut permuted = [0u32; 16];
    for (dst, &src) in permuted.iter_mut().zip(MSG_PERMUTATION.iter()) {
        *dst = m[src];
    }
    *m = permuted;
}

/// The 7-round compression function (spec §2.2), returning the full 16-word
/// output state (the low 8 words are the chaining value; all 16 feed the XOF).
fn compress(
    chaining_value: &[u32; 8],
    block_words: &[u32; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
) -> [u32; 16] {
    let mut state = [
        chaining_value[0],
        chaining_value[1],
        chaining_value[2],
        chaining_value[3],
        chaining_value[4],
        chaining_value[5],
        chaining_value[6],
        chaining_value[7],
        IV[0],
        IV[1],
        IV[2],
        IV[3],
        counter as u32,
        (counter >> 32) as u32,
        block_len,
        flags,
    ];
    let mut block = *block_words;

    round(&mut state, &block); // round 1
    permute(&mut block);
    round(&mut state, &block); // round 2
    permute(&mut block);
    round(&mut state, &block); // round 3
    permute(&mut block);
    round(&mut state, &block); // round 4
    permute(&mut block);
    round(&mut state, &block); // round 5
    permute(&mut block);
    round(&mut state, &block); // round 6
    permute(&mut block);
    round(&mut state, &block); // round 7

    for i in 0..8 {
        state[i] ^= state[i + 8];
        state[i + 8] ^= chaining_value[i];
    }
    state
}

fn first_8_words(compression_output: [u32; 16]) -> [u32; 8] {
    let mut cv = [0u32; 8];
    cv.copy_from_slice(&compression_output[..8]);
    cv
}

/// Interpret a 64-byte block as 16 little-endian message words (spec §2.2).
fn words_from_le_block(block: &[u8; BLOCK_LEN]) -> [u32; 16] {
    let mut words = [0u32; 16];
    for (word, chunk) in words.iter_mut().zip(block.chunks_exact(4)) {
        *word = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
    }
    words
}

/// Interpret a 32-byte key as 8 little-endian key words (spec §2.3).
fn words_from_le_key(key: &[u8; KEY_LEN]) -> [u32; 8] {
    let mut words = [0u32; 8];
    for (word, chunk) in words.iter_mut().zip(key.chunks_exact(4)) {
        *word = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
    }
    words
}

/// A pending compression whose ROOT-flagged evaluation drives the XOF
/// (spec §2.6 "Extendable output"): the root's final block is recompressed
/// with an incrementing output block counter to produce arbitrary output.
#[derive(Clone, Copy)]
struct Output {
    input_chaining_value: [u32; 8],
    block_words: [u32; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
}

impl Output {
    fn chaining_value(&self) -> [u32; 8] {
        first_8_words(compress(
            &self.input_chaining_value,
            &self.block_words,
            self.counter,
            self.block_len,
            self.flags,
        ))
    }

    fn root_output_bytes(&self, out: &mut [u8]) {
        for (output_block_counter, out_block) in out.chunks_mut(2 * OUT_LEN).enumerate() {
            let words = compress(
                &self.input_chaining_value,
                &self.block_words,
                output_block_counter as u64,
                self.block_len,
                self.flags | ROOT,
            );
            for (word, out_word) in words.iter().zip(out_block.chunks_mut(4)) {
                out_word.copy_from_slice(&word.to_le_bytes()[..out_word.len()]);
            }
        }
    }
}

/// Incremental state for one 1024-byte chunk (spec §2.1): sixteen 64-byte
/// blocks chained with CHUNK_START on the first and CHUNK_END on the last.
#[derive(Clone, Copy)]
struct ChunkState {
    chaining_value: [u32; 8],
    chunk_counter: u64,
    block: [u8; BLOCK_LEN],
    block_len: u8,
    blocks_compressed: u8,
    flags: u32,
}

impl ChunkState {
    fn new(key_words: &[u32; 8], chunk_counter: u64, flags: u32) -> ChunkState {
        ChunkState {
            chaining_value: *key_words,
            chunk_counter,
            block: [0; BLOCK_LEN],
            block_len: 0,
            blocks_compressed: 0,
            flags,
        }
    }

    fn len(&self) -> usize {
        BLOCK_LEN * self.blocks_compressed as usize + self.block_len as usize
    }

    fn start_flag(&self) -> u32 {
        if self.blocks_compressed == 0 { CHUNK_START } else { 0 }
    }

    fn update(&mut self, mut input: &[u8]) {
        while !input.is_empty() {
            // A full buffered block is compressed only once more input
            // arrives, so the final block always stays buffered for
            // CHUNK_END / ROOT finalization.
            if self.block_len as usize == BLOCK_LEN {
                let block_words = words_from_le_block(&self.block);
                self.chaining_value = first_8_words(compress(
                    &self.chaining_value,
                    &block_words,
                    self.chunk_counter,
                    BLOCK_LEN as u32,
                    self.flags | self.start_flag(),
                ));
                self.blocks_compressed += 1;
                self.block = [0; BLOCK_LEN];
                self.block_len = 0;
            }
            let want = BLOCK_LEN - self.block_len as usize;
            let take = want.min(input.len());
            self.block[self.block_len as usize..self.block_len as usize + take]
                .copy_from_slice(&input[..take]);
            self.block_len += take as u8;
            input = &input[take..];
        }
    }

    fn output(&self) -> Output {
        Output {
            input_chaining_value: self.chaining_value,
            block_words: words_from_le_block(&self.block),
            counter: self.chunk_counter,
            block_len: u32::from(self.block_len),
            flags: self.flags | self.start_flag() | CHUNK_END,
        }
    }
}

/// One parent-node compression (spec §2.1): two child chaining values form a
/// 64-byte block, counter 0, PARENT flag.
fn parent_output(
    left_child_cv: [u32; 8],
    right_child_cv: [u32; 8],
    key_words: &[u32; 8],
    flags: u32,
) -> Output {
    let mut block_words = [0u32; 16];
    block_words[..8].copy_from_slice(&left_child_cv);
    block_words[8..].copy_from_slice(&right_child_cv);
    Output {
        input_chaining_value: *key_words,
        block_words,
        counter: 0,
        block_len: BLOCK_LEN as u32,
        flags: PARENT | flags,
    }
}

fn parent_cv(
    left_child_cv: [u32; 8],
    right_child_cv: [u32; 8],
    key_words: &[u32; 8],
    flags: u32,
) -> [u32; 8] {
    parent_output(left_child_cv, right_child_cv, key_words, flags).chaining_value()
}

/// 2^54 chunk chaining values cover the full 2^64-byte input range
/// (spec §5.1.2 gives 54 as the maximum tree height at 1 KiB chunks).
const MAX_STACK_DEPTH: usize = 54;

/// An incremental BLAKE3 hasher for all three modes (spec §2.3–§2.6).
///
/// Maintains the current chunk state plus a stack of subtree chaining values;
/// the left-full merging rule (spec §2.1) merges a completed subtree exactly
/// when the total chunk count gains a trailing zero bit.
#[derive(Clone, Debug)]
pub struct Hasher {
    chunk_state: ChunkState,
    key_words: [u32; 8],
    cv_stack: [[u32; 8]; MAX_STACK_DEPTH],
    cv_stack_len: u8,
    flags: u32,
}

impl Hasher {
    fn new_internal(key_words: [u32; 8], flags: u32) -> Hasher {
        Hasher {
            chunk_state: ChunkState::new(&key_words, 0, flags),
            key_words,
            cv_stack: [[0; 8]; MAX_STACK_DEPTH],
            cv_stack_len: 0,
            flags,
        }
    }

    /// Regular hash mode: key words are the IV, no mode flag (spec §2.4).
    pub fn new() -> Hasher {
        Hasher::new_internal(IV, 0)
    }

    /// Keyed hash mode: the 32-byte key supplies the key words, KEYED_HASH
    /// flag on every compression (spec §2.5).
    pub fn new_keyed(key: &[u8; KEY_LEN]) -> Hasher {
        Hasher::new_internal(words_from_le_key(key), KEYED_HASH)
    }

    /// Key derivation mode (spec §2.6): hash the context string under
    /// DERIVE_KEY_CONTEXT with the IV key, then use its 32-byte output as the
    /// key words under DERIVE_KEY_MATERIAL.
    pub fn new_derive_key(context: &str) -> Hasher {
        let mut context_hasher = Hasher::new_internal(IV, DERIVE_KEY_CONTEXT);
        context_hasher.update(context.as_bytes());
        let context_key = context_hasher.finalize();
        Hasher::new_internal(words_from_le_key(&context_key), DERIVE_KEY_MATERIAL)
    }

    fn push_stack(&mut self, cv: [u32; 8]) {
        debug_assert!((self.cv_stack_len as usize) < MAX_STACK_DEPTH);
        self.cv_stack[self.cv_stack_len as usize] = cv;
        self.cv_stack_len += 1;
    }

    fn pop_stack(&mut self) -> [u32; 8] {
        debug_assert!(self.cv_stack_len > 0);
        self.cv_stack_len -= 1;
        self.cv_stack[self.cv_stack_len as usize]
    }

    /// Left-full subtree merging (spec §2.1): after completing chunk number
    /// `total_chunks - 1`, merge once per trailing one bit that turned into a
    /// carry — i.e. pop and merge while `total_chunks` is even after shifts.
    fn add_chunk_chaining_value(&mut self, mut new_cv: [u32; 8], mut total_chunks: u64) {
        while total_chunks & 1 == 0 {
            new_cv = parent_cv(self.pop_stack(), new_cv, &self.key_words, self.flags);
            total_chunks >>= 1;
        }
        self.push_stack(new_cv);
    }

    /// Absorb `input`; splitting input across calls at any byte boundaries
    /// yields the same digest as a single call.
    pub fn update(&mut self, mut input: &[u8]) -> &mut Hasher {
        while !input.is_empty() {
            // A completed chunk is folded into the tree only once more input
            // arrives, so the final chunk always stays current for ROOT
            // finalization.
            if self.chunk_state.len() == CHUNK_LEN {
                let chunk_cv = self.chunk_state.output().chaining_value();
                let total_chunks = self.chunk_state.chunk_counter + 1;
                self.add_chunk_chaining_value(chunk_cv, total_chunks);
                self.chunk_state = ChunkState::new(&self.key_words, total_chunks, self.flags);
            }
            let want = CHUNK_LEN - self.chunk_state.len();
            let take = want.min(input.len());
            self.chunk_state.update(&input[..take]);
            input = &input[take..];
        }
        self
    }

    /// Default-length (32-byte) digest. Does not consume the hasher.
    pub fn finalize(&self) -> [u8; OUT_LEN] {
        let mut out = [0u8; OUT_LEN];
        self.finalize_xof(&mut out);
        out
    }

    /// Extendable output (spec §2.6): fill `out` — of any length — with the
    /// XOF stream. A prefix of a longer output equals the shorter output.
    pub fn finalize_xof(&self, out: &mut [u8]) {
        // Fold the stack right-to-left into a chain of parent Outputs; the
        // topmost (final) Output gets the ROOT flag inside root_output_bytes.
        let mut output = self.chunk_state.output();
        let mut parent_nodes_remaining = self.cv_stack_len as usize;
        while parent_nodes_remaining > 0 {
            parent_nodes_remaining -= 1;
            output = parent_output(
                self.cv_stack[parent_nodes_remaining],
                output.chaining_value(),
                &self.key_words,
                self.flags,
            );
        }
        output.root_output_bytes(out);
    }
}

impl Default for Hasher {
    fn default() -> Hasher {
        Hasher::new()
    }
}

/// One-shot regular BLAKE3 hash of `input` (spec §2.4).
pub fn hash(input: &[u8]) -> [u8; OUT_LEN] {
    Hasher::new().update(input).finalize()
}

#[cfg(test)]
mod tests {
    use super::{Hasher, KEY_LEN, OUT_LEN, hash};

    /// Key and context constants from the official test-vector JSON header
    /// (mirrored in the fixture's `# provenance:` lines).
    const TEST_KEY: &[u8; KEY_LEN] = b"whats the Elvish word for friend";
    const TEST_CONTEXT: &str = "BLAKE3 2019-12-27 16:29:52 test vectors context";

    /// Extended output length used by every official vector.
    const XOF_LEN: usize = 131;

    const FIXTURE: &str = include_str!("../fixtures/blake3_vectors.txt");

    fn hex_encode(bytes: &[u8]) -> String {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";
        let mut s = String::with_capacity(bytes.len() * 2);
        for &b in bytes {
            s.push(DIGITS[(b >> 4) as usize] as char);
            s.push(DIGITS[(b & 0x0F) as usize] as char);
        }
        s
    }

    /// The official vectors' input: the repeating byte pattern 0,1,...,249.
    fn test_input(len: usize) -> Vec<u8> {
        (0..len).map(|i| (i % 251) as u8).collect()
    }

    struct Vector {
        input_len: usize,
        hash_hex: String,
        keyed_hash_hex: String,
        derive_key_hex: String,
    }

    fn parse_fixture() -> Vec<Vector> {
        let mut vectors = Vec::new();
        let mut saw_schema = false;
        for line in FIXTURE.lines() {
            let line = line.trim();
            if line == "# schema fln-blake3-vectors/1" {
                saw_schema = true;
            }
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let mut fields = line.split('|');
            let input_len = fields
                .next()
                .expect("split yields at least one field")
                .parse::<usize>()
                .expect("fixture input_len parses");
            let mut hex = || fields.next().expect("fixture row has 4 fields").to_owned();
            vectors.push(Vector {
                input_len,
                hash_hex: hex(),
                keyed_hash_hex: hex(),
                derive_key_hex: hex(),
            });
        }
        assert!(saw_schema, "fixture missing schema line");
        assert!(!vectors.is_empty(), "fixture has no vector rows");
        vectors
    }

    #[test]
    fn official_vectors_all_modes() {
        let vectors = parse_fixture();
        assert_eq!(vectors.len(), 35, "official set has 35 cases");
        for v in &vectors {
            let input = test_input(v.input_len);
            let mut xof = [0u8; XOF_LEN];

            let hasher = {
                let mut h = Hasher::new();
                h.update(&input);
                h
            };
            hasher.finalize_xof(&mut xof);
            assert_eq!(
                hex_encode(&xof),
                v.hash_hex,
                "hash xof mismatch at len {}",
                v.input_len
            );
            assert_eq!(
                hex_encode(&hasher.finalize()),
                v.hash_hex[..OUT_LEN * 2],
                "hash prefix mismatch at len {}",
                v.input_len
            );
            assert_eq!(
                hex_encode(&hash(&input)),
                v.hash_hex[..OUT_LEN * 2],
                "one-shot hash mismatch at len {}",
                v.input_len
            );

            let keyed = {
                let mut h = Hasher::new_keyed(TEST_KEY);
                h.update(&input);
                h
            };
            keyed.finalize_xof(&mut xof);
            assert_eq!(
                hex_encode(&xof),
                v.keyed_hash_hex,
                "keyed xof mismatch at len {}",
                v.input_len
            );
            assert_eq!(
                hex_encode(&keyed.finalize()),
                v.keyed_hash_hex[..OUT_LEN * 2],
                "keyed prefix mismatch at len {}",
                v.input_len
            );

            let derive = {
                let mut h = Hasher::new_derive_key(TEST_CONTEXT);
                h.update(&input);
                h
            };
            derive.finalize_xof(&mut xof);
            assert_eq!(
                hex_encode(&xof),
                v.derive_key_hex,
                "derive_key xof mismatch at len {}",
                v.input_len
            );
            assert_eq!(
                hex_encode(&derive.finalize()),
                v.derive_key_hex[..OUT_LEN * 2],
                "derive_key prefix mismatch at len {}",
                v.input_len
            );
        }
    }

    #[test]
    fn incremental_split_points_match_one_shot() {
        // Deterministic split sizes exercising sub-block, block, and chunk
        // boundaries; cycled until the input is consumed.
        const SPLITS: [usize; 12] = [1, 2, 3, 5, 7, 11, 13, 63, 64, 65, 127, 1000];
        for &len in &[0usize, 1, 1023, 1024, 1025, 3072, 5000] {
            let input = test_input(len);
            let one_shot = hash(&input);

            let mut h = Hasher::new();
            let mut offset = 0;
            let mut split_index = 0;
            while offset < input.len() {
                let take = SPLITS[split_index % SPLITS.len()].min(input.len() - offset);
                h.update(&input[offset..offset + take]);
                offset += take;
                split_index += 1;
            }
            assert_eq!(h.finalize(), one_shot, "split mismatch at len {len}");

            let mut byte_by_byte = Hasher::new();
            for &b in &input {
                byte_by_byte.update(&[b]);
            }
            assert_eq!(
                byte_by_byte.finalize(),
                one_shot,
                "byte-by-byte mismatch at len {len}"
            );
        }
    }

    #[test]
    fn xof_prefix_consistency() {
        let input = test_input(2049);
        let mut h = Hasher::new();
        h.update(&input);
        let mut long = [0u8; 301];
        h.finalize_xof(&mut long);
        for &prefix_len in &[0usize, 1, 31, 32, 33, 64, 65, 300] {
            let mut short = vec![0u8; prefix_len];
            h.finalize_xof(&mut short);
            assert_eq!(short[..], long[..prefix_len], "xof prefix {prefix_len}");
        }
    }
}
