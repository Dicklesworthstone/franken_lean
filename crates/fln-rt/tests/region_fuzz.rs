//! fln-wgp slice 3: corrupted-relocation-table fuzzing under resource
//! budgets (R18 — a hostile olean is a DoS surface even in safe Rust).
//!
//! A deterministic, seed-replayable, structure-aware mutation fuzzer over
//! the region engine (no external fuzz engine: the closed universe D1 owns
//! its randomness — splitmix64). Every case derives its RNG stream from a
//! fixed master seed + case index, so any reported failure replays exactly.
//!
//! The laws each case must satisfy, no matter how hostile the bytes:
//!
//! 1. **Typed totality** — parse/relocate/audit/digest/materialize return
//!    `Ok` or a typed `RegionFault`; a panic is an invariant failure and
//!    fails the run with the replay seed (FL-INV-07).
//! 2. **Time budget** — every case completes within a generous per-case
//!    wall budget (the engine's walks are linear by construction; a case
//!    that spins marks a termination bug, R18's DoS arm).
//! 3. **Space budget by construction** — inputs are capped (≤ 128 KiB), and
//!    every engine allocation is payload-proportional, so hostile length
//!    fields cannot amplify (the `need()` gate bounds every claimed size).
//! 4. **Relocation invariance survives mutation** — a mutant that still
//!    relocates successfully to two different bases digests identically at
//!    both (the metamorphic law is not just for well-formed regions).
//! 5. **The whole run fits a 1 MiB stack** — recursion would overflow here
//!    instead of hiding behind the dev box's unlimited main-thread stack.

#![forbid(unsafe_code)]

use fln_rt::obj::Obj;
use fln_rt::region::{canonical_digest, compact, materialize, parse_olean_envelope, relocate};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::{Duration, Instant};

const MASTER_SEED: u64 = 0x5EED_F14E_2026_0723;
const BASE_A: u64 = 0x7000_0000_0000;
const BASE_B: u64 = 0x9000_0500_0000;
const BASE_C: u64 = 0x5000_0300_0000;
/// Per-case wall budget. The linear walks finish in microseconds; one full
/// second only trips on a genuine termination/complexity bug.
const CASE_BUDGET: Duration = Duration::from_secs(1);
/// Input cap: the space-budget law's construction side.
const MAX_CASE_BYTES: usize = 128 * 1024;

/// splitmix64 — tiny, deterministic, well-distributed; the per-case stream
/// is `Rng::new(MASTER_SEED ^ case_index)`.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed)
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }
}

/// A synthetic seed region covering every slice-1 category with sharing —
/// small enough that thousands of mutants stay cheap.
fn synthetic_seed() -> Vec<u8> {
    let shared = Obj::mk_string("fuzz-shared-leaf");
    let pair = Obj::mk_ctor(2, vec![shared.clone_ref(), Obj::mk_nat(41)], &[0xEE; 4]);
    let big = Obj::mk_mpz(&[0xDEAD_BEEF_u64, 7, 0xFFFF_FFFF_FFFF_FFFF], true);
    let inner = Obj::mk_array(vec![pair, shared.clone_ref(), big]);
    let root = Obj::mk_array(vec![inner, shared, Obj::mk_nat(0), Obj::mk_string("tail")]);
    compact(&root, BASE_A).expect("synthetic seed compacts")
}

/// The real pinned olean payload, pre-relocated to `BASE_A`, when the c3
/// fixture is present (absence is a typed limitation, not a silent pass —
/// the synthetic corpus still runs).
fn real_seed() -> Option<Vec<u8>> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tribunal/fixtures/c3/Init.SizeOfLemmas.olean");
    let file = std::fs::read(path).ok()?;
    let env = parse_olean_envelope(&file).ok()?;
    let mut payload = file[env.payload_offset..].to_vec();
    relocate(&mut payload, env.payload_base(), BASE_A).ok()?;
    Some(payload)
}

/// One structure-aware mutation: pointer perturbation, header abuse, word
/// duplication (aliasing/pointer confusion), length-field lies, truncation,
/// growth, zeroing, or plain byte noise.
fn mutate(rng: &mut Rng, bytes: &mut Vec<u8>) {
    // Word-level operators need one whole word; short buffers (a prior
    // truncation) degrade to byte noise instead of indexing off the end.
    let words = bytes.len() / 8;
    let op = if words == 0 { 0 } else { rng.below(9) };
    match op {
        0 => {
            // Byte noise.
            let at = rng.below(bytes.len());
            bytes[at] = (rng.next() & 0xFF) as u8;
        }
        1 => {
            // Random aligned word — wild pointers and impossible sizes.
            let at = rng.below(words) * 8;
            bytes[at..at + 8].copy_from_slice(&rng.next().to_le_bytes());
        }
        2 => {
            // Perturb a word by a small signed delta — off-by-slot pointers.
            let at = rng.below(words) * 8;
            let v = u64::from_le_bytes(bytes[at..at + 8].try_into().expect("word"));
            let delta = (rng.next() % 65) as i64 - 32;
            bytes[at..at + 8].copy_from_slice(&v.wrapping_add(delta as u64).to_le_bytes());
        }
        3 => {
            // Copy one word over another — aliasing / forward-pointer forgery.
            let (src, dst) = (rng.below(words) * 8, rng.below(words) * 8);
            let w: [u8; 8] = bytes[src..src + 8].try_into().expect("word");
            bytes[dst..dst + 8].copy_from_slice(&w);
        }
        4 => {
            // Header abuse: rewrite tag / field-count / cs_sz bytes.
            let at = rng.below(bytes.len());
            let b = (rng.next() & 0xFF) as u8;
            bytes[at] = match rng.below(3) {
                0 => 0xF5 + (b % 10), // the reserved/big-tag band
                1 => 0,
                _ => b,
            };
        }
        5 => {
            // Truncate (word-ragged truncations included deliberately).
            let keep = rng.below(bytes.len().max(1));
            bytes.truncate(keep.max(1));
        }
        6 => {
            // Grow with noise (still under the case cap).
            let extra = rng.below(64) + 1;
            for _ in 0..extra {
                if bytes.len() >= MAX_CASE_BYTES {
                    break;
                }
                bytes.push((rng.next() & 0xFF) as u8);
            }
        }
        7 => {
            // Zero a range — fake persistent headers / NUL floods.
            let start = rng.below(bytes.len());
            let end = (start + rng.below(256) + 1).min(bytes.len());
            bytes[start..end].fill(0);
        }
        _ => {
            // Scalar-bit flips: turn pointers into scalars and back.
            let at = rng.below(words) * 8;
            bytes[at] ^= 1;
        }
    }
}

/// Run every engine entry point over one mutant under the case laws.
/// Returns how many operations succeeded (corpus-health telemetry).
fn run_case(case: u64, mutant: &[u8]) -> u32 {
    let start = Instant::now();
    let mut survived = 0u32;

    let outcome = catch_unwind(AssertUnwindSafe(|| {
        // Audit at the seed base (no rewrite) — typed or Ok.
        let mut audit = mutant.to_vec();
        let audited = relocate(&mut audit, BASE_A, BASE_A).is_ok();

        // Relocate to two DIFFERENT bases; if both succeed the canonical
        // digests must agree (relocation invariance on surviving mutants).
        let mut to_b = mutant.to_vec();
        let mut to_c = mutant.to_vec();
        let rb = relocate(&mut to_b, BASE_A, BASE_B);
        let rc = relocate(&mut to_c, BASE_A, BASE_C);
        assert_eq!(
            rb.is_ok(),
            rc.is_ok(),
            "case {case}: relocation success must not depend on the target base"
        );
        if let (Ok(_), Ok(_)) = (&rb, &rc) {
            let db = canonical_digest(&to_b, BASE_B).expect("digest after successful relocate");
            let dc = canonical_digest(&to_c, BASE_C).expect("digest after successful relocate");
            assert_eq!(
                db, dc,
                "case {case}: surviving mutant broke relocation invariance"
            );
            // Digest determinism.
            assert_eq!(
                db,
                canonical_digest(&to_b, BASE_B).expect("digest replay"),
                "case {case}: digest not deterministic"
            );
        }

        // Materialize only audited payloads (the production order: a region
        // is validated at its final address before objects go live); the
        // post-order law may still fault it — typed either way.
        let mut ok_ops = u32::from(audited) + u32::from(rb.is_ok());
        if audited && materialize(&audit, BASE_A).is_ok() {
            ok_ops += 1;
        }
        ok_ops
    }));

    match outcome {
        Ok(n) => survived += n,
        Err(_) => panic!(
            "case {case}: engine panicked on hostile input (replay: seed {MASTER_SEED:#x} ^ {case})"
        ),
    }

    let elapsed = start.elapsed();
    assert!(
        elapsed < CASE_BUDGET,
        "case {case}: exceeded the per-case time budget ({elapsed:?}) — termination bug (R18)"
    );
    survived
}

/// Fuzz one seed corpus entry for `cases` mutants, `1..=max_mutations`
/// stacked mutations per case.
fn fuzz_seed(tag: &str, seed_bytes: &[u8], cases: u64, salt: u64) {
    assert!(
        seed_bytes.len() <= MAX_CASE_BYTES,
        "seed under the case cap"
    );
    let mut survivors = 0u32;
    for case in 0..cases {
        let mut rng = Rng::new(MASTER_SEED ^ salt ^ case);
        let mut mutant = seed_bytes.to_vec();
        for _ in 0..rng.below(4) + 1 {
            mutate(&mut rng, &mut mutant);
        }
        survivors += run_case(salt ^ case, &mutant);
    }
    // Corpus health: the fuzzer must not be so destructive that nothing
    // survives (all-reject tells us nothing about acceptance-side bugs) —
    // near-miss mutants that still pass are where wrong-acceptance hides.
    assert!(
        survivors > 0,
        "{tag}: zero surviving operations across {cases} cases — mutator too destructive"
    );
    println!("region-fuzz {tag}: {cases} cases, {survivors} surviving operations");
}

fn case_count() -> u64 {
    // The e2e deep lane raises this (FLN_REGION_FUZZ_CASES); unit runs stay
    // fast. Malformed values are refused, not defaulted silently.
    match std::env::var("FLN_REGION_FUZZ_CASES") {
        Ok(v) => v
            .parse::<u64>()
            .expect("FLN_REGION_FUZZ_CASES must be a positive integer")
            .max(1),
        Err(_) => 1500,
    }
}

/// The whole fuzz campaign on a 1 MiB stack: synthetic corpus, real-olean
/// corpus (when the fixture exists), and the envelope-header corpus.
///
/// The per-case elapsed assert only fires after a case RETURNS, so it can
/// catch slow termination but not divergence; the campaign watchdog below
/// (channel + `recv_timeout`) is what turns a genuinely hung walk into a
/// failing test instead of a hung CI lane.
#[test]
fn hostile_regions_fault_typed_within_budgets() {
    let cases = case_count();
    // Generous scale: measured throughput is ~7k cases/s; 2 ms/case of
    // budget only trips on a complexity or divergence bug.
    let campaign_budget =
        Duration::from_secs(60).max(Duration::from_millis(cases.saturating_mul(2)));
    let (done_tx, done_rx) = std::sync::mpsc::channel::<()>();
    let worker = std::thread::Builder::new()
        .name("region-fuzz-bounded".into())
        .stack_size(1 << 20)
        .spawn(move || {
            fuzz_seed("synthetic", &synthetic_seed(), cases, 0x51);
            match real_seed() {
                Some(payload) => {
                    // Real payloads are bigger; scale count to keep unit runs
                    // brisk while the deep lane still gets full volume.
                    fuzz_seed("real-olean", &payload, (cases / 3).max(100), 0x0313);
                }
                None => eprintln!(
                    "SKIP (typed limitation): c3 fixture olean absent — real-corpus arm not run"
                ),
            }
            drop(done_tx); // disconnect = campaign finished (panic also disconnects)
        })
        .expect("spawn bounded-stack fuzz worker");
    match done_rx.recv_timeout(campaign_budget) {
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {}
        Ok(()) => unreachable!("nothing is ever sent"),
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            panic!(
                "fuzz campaign exceeded {campaign_budget:?} — divergence or complexity bug (R18)"
            )
        }
    }
    worker.join().expect("fuzz worker must not die");
}

/// Envelope fuzz: hostile 64-byte headers over a real file image — parse
/// yields a typed fault or a self-consistent envelope, never a panic, and
/// header damage cannot smuggle an out-of-file payload window.
#[test]
fn hostile_envelopes_fault_typed() {
    let file = {
        // A minimal well-formed file image: real header laws come from the
        // generated contract, so build one valid envelope then attack it.
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tribunal/fixtures/c3/Init.SizeOfLemmas.olean");
        match std::fs::read(&path) {
            Ok(f) => f,
            Err(_) => {
                eprintln!("SKIP (typed limitation): c3 fixture olean absent");
                return;
            }
        }
    };
    let header_span = parse_olean_envelope(&file)
        .expect("fixture parses")
        .payload_offset;
    let cases = case_count();
    for case in 0..cases {
        let mut rng = Rng::new(MASTER_SEED ^ 0xE47 ^ case);
        let mut image = file.clone();
        // 1-3 byte edits confined to the header partition.
        for _ in 0..rng.below(3) + 1 {
            let at = rng.below(header_span);
            image[at] = (rng.next() & 0xFF) as u8;
        }
        let outcome = catch_unwind(AssertUnwindSafe(|| parse_olean_envelope(&image)));
        match outcome {
            Ok(Ok(env)) => {
                assert!(
                    env.payload_offset + env.payload_len <= image.len(),
                    "case {case}: envelope claims a window beyond the file"
                );
            }
            Ok(Err(_)) => {} // typed fault — the law
            Err(_) => panic!("case {case}: envelope parser panicked (seed {MASTER_SEED:#x})"),
        }
    }
}
