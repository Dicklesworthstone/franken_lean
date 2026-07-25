//! fln-wgp slice 1: the compacted-region engine end to end — compact /
//! relocate / audit / materialize round-trips with sharing, the corruption
//! fault matrix, and the REAL-olean mmap path (G0-1 promoted to the
//! production machinery). Safe code throughout (`forbid(unsafe_code)`).

#![forbid(unsafe_code)]

use fln_rt::obj::Obj;
use fln_rt::region::{
    RegionFault, canonical_digest, compact, materialize, parse_olean_envelope, relocate,
};
use fln_unsafe_region::mapping::RegionMapping;
use std::sync::{Mutex, MutexGuard};

static TEST_LOCK: Mutex<()> = Mutex::new(());

fn lock() -> MutexGuard<'static, ()> {
    TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

/// A representative graph over every slice-1 category, with real sharing
/// (the string leaf is referenced from two parents).
fn sample_graph() -> Obj {
    let shared = Obj::mk_string("shared-leaf");
    let pair = Obj::mk_ctor(2, vec![shared.clone_ref(), Obj::mk_nat(41)], &[0xEE; 4]);
    let big = Obj::mk_mpz(&[0xDEAD_BEEF_u64, 7], true);
    Obj::mk_array(vec![pair, shared, big, Obj::mk_nat(0)])
}

const BASE_A: u64 = 0x7000_0000_0000;
const BASE_B: u64 = 0x9000_0500_0000;

#[test]
fn compact_relocate_materialize_fixpoint() {
    let _g = lock();
    let bytes1 = compact(&sample_graph(), BASE_A).expect("compact");

    // Audit at the stored base: zero pointer rewrites, every law checked.
    let mut audit_copy = bytes1.clone();
    let audit = relocate(&mut audit_copy, BASE_A, BASE_A).expect("audit");
    assert_eq!(audit.pointers_fixed, 0);
    assert_eq!(audit_copy, bytes1, "auditing must not rewrite anything");
    assert!(
        audit.objects >= 4,
        "graph has at least array+ctor+string+mpz"
    );

    // Relocate to a different base: digests are relocation-invariant.
    let mut moved = bytes1.clone();
    let report = relocate(&mut moved, BASE_A, BASE_B).expect("relocate");
    assert!(report.pointers_fixed > 0);
    assert_eq!(
        canonical_digest(&bytes1, BASE_A).expect("digest a"),
        canonical_digest(&moved, BASE_B).expect("digest b"),
        "canonical digest must not depend on the load address"
    );

    // Materialize from the moved image and re-compact: the fixpoint law.
    let rebuilt = materialize(&moved, BASE_B).expect("materialize");
    let bytes2 = compact(&rebuilt, BASE_A).expect("recompact");
    assert_eq!(
        bytes1, bytes2,
        "compact ∘ materialize is the identity on region bytes"
    );
}

#[test]
fn sharing_is_preserved_not_duplicated() {
    let _g = lock();
    // Two parents share one string; the region must contain the string once.
    let shared = Obj::mk_string("only-once");
    let root = Obj::mk_array(vec![
        Obj::mk_ctor(0, vec![shared.clone_ref()], &[]),
        Obj::mk_ctor(0, vec![shared.clone_ref()], &[]),
        shared,
    ]);
    let bytes = compact(&root, BASE_A).expect("compact");
    let needle = b"only-once";
    let count = bytes.windows(needle.len()).filter(|w| w == needle).count();
    assert_eq!(count, 1, "shared subgraphs are deduplicated by identity");
    // And the round trip keeps the dedup (fixpoint again).
    let rebuilt = {
        let mut moved = bytes.clone();
        relocate(&mut moved, BASE_A, BASE_B).expect("relocate");
        materialize(&moved, BASE_B).expect("materialize")
    };
    assert_eq!(compact(&rebuilt, BASE_A).expect("recompact"), bytes);
}

#[test]
fn scalar_root_region() {
    let _g = lock();
    let bytes = compact(&Obj::mk_nat(77), BASE_A).expect("compact scalar");
    assert_eq!(bytes.len(), 8, "a scalar root is just the root word");
    let m = materialize(&bytes, BASE_A).expect("materialize scalar");
    assert!(m.is_scalar());
    assert_eq!(m.unbox(), 77);
}

#[test]
fn corruption_fault_matrix() {
    let _g = lock();
    let bytes = compact(&sample_graph(), BASE_A).expect("compact");

    // Ragged payload.
    let mut ragged = bytes.clone();
    ragged.push(0);
    assert!(matches!(
        relocate(&mut ragged, BASE_A, BASE_B),
        Err(RegionFault::RaggedPayload { .. })
    ));

    // Truncation mid-object.
    let mut short = bytes.clone();
    short.truncate(bytes.len() - 8);
    assert!(relocate(&mut short, BASE_A, BASE_B).is_err());

    // Non-persistent rc in a compacted object (first object header at 8).
    let mut hot = bytes.clone();
    hot[8] = 1;
    assert!(matches!(
        relocate(&mut hot, BASE_A, BASE_B),
        Err(RegionFault::NonPersistentRc { .. })
    ));

    // Forbidden tag.
    let mut alien = bytes.clone();
    alien[8 + 7] = 254; // external
    assert!(matches!(
        relocate(&mut alien, BASE_A, BASE_B),
        Err(RegionFault::ForbiddenTag { .. })
    ));

    // Out-of-bounds root pointer.
    let mut wild = bytes.clone();
    wild[0..8].copy_from_slice(&(BASE_A + (1 << 40)).to_le_bytes());
    assert!(relocate(&mut wild, BASE_A, BASE_B).is_err());

    // Forward pointer: legal for the (order-free) relocator, but the
    // materializer enforces the writer's post-order law and must fault
    // rather than loop.
    let root_word = u64::from_le_bytes(bytes[0..8].try_into().expect("root"));
    let root_off = root_word - BASE_A;
    let mut forward = bytes.clone();
    // Point the root object's first child slot at the root itself (a cycle).
    let slot = usize::try_from(root_off).expect("off") + 24;
    if slot + 8 <= forward.len() {
        forward[slot..slot + 8].copy_from_slice(&root_word.to_le_bytes());
        if relocate(&mut forward.clone(), BASE_A, BASE_A).is_ok() {
            assert!(
                materialize(&forward, BASE_A).is_err(),
                "self/forward pointers must fault, never loop"
            );
        }
    }
}

#[test]
fn envelope_laws() {
    let _g = lock();
    // Short garbage is length-gated before the magic check.
    assert!(matches!(
        parse_olean_envelope(b"not-an-olean-file-at-all-padpadpad"),
        Err(RegionFault::Truncated { .. })
    ));
    let mut long_garbage = vec![0x5Au8; 128];
    long_garbage[0] = b'x';
    assert!(matches!(
        parse_olean_envelope(&long_garbage),
        Err(RegionFault::BadMagic)
    ));
    assert!(matches!(
        parse_olean_envelope(b"ol"),
        Err(RegionFault::Truncated { .. })
    ));
}

fn fixture(name: &str) -> Option<std::path::PathBuf> {
    let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tribunal/fixtures/c3")
        .join(name);
    p.exists().then_some(p)
}

/// The G0-1 promotion: a REAL pinned-toolchain olean loads via mmap, its
/// region relocates to the live mapping address, every object satisfies the
/// category laws at its final address, the graph materializes as live
/// CompatHeap objects, and the canonical digest is identical across two
/// mappings at different addresses.
#[test]
fn real_olean_mmap_relocate_materialize() {
    let _g = lock();
    let Some(path) = fixture("Init.SizeOfLemmas.olean") else {
        eprintln!("SKIP (typed limitation): c3 fixture olean not present");
        return;
    };

    let load = |target_tag: &str| -> (u64, u64, u64) {
        let mut m = RegionMapping::map_file_private(&path).expect("mmap olean");
        let env = parse_olean_envelope(m.as_slice()).expect("envelope");
        let target = (m.addr() + env.payload_offset) as u64;
        let buf = &mut m.as_mut_slice().expect("mut")[env.payload_offset..];
        let report = relocate(buf, env.payload_base(), target).expect("relocate");
        assert!(report.objects > 0, "{target_tag}: region walked");
        let digest = canonical_digest(buf, target).expect("digest");
        // Live traversal: materialize the whole module graph through the
        // handle layer (sharing preserved via region offsets).
        let root = materialize(buf, target).expect("materialize");
        assert!(!root.is_scalar(), "ModuleData root is a ctor");
        let sealed_ok = m.seal().is_ok();
        assert!(sealed_ok, "region hygiene: seal after relocation");
        (report.objects, report.pointers_fixed, digest)
    };

    let (objects_a, fixed_a, digest_a) = load("first mapping");
    let (objects_b, _fixed_b, digest_b) = load("second mapping");
    assert_eq!(objects_a, objects_b, "same file, same object count");
    assert!(fixed_a > 0, "relocation really rewrote pointers");
    assert_eq!(
        digest_a, digest_b,
        "two loads at different addresses are canonically identical"
    );
}

/// The real-olean fixpoint: materialize the module graph, compact it with
/// OUR writer, and prove the engine is self-consistent on real-world shapes
/// (compact ∘ materialize ∘ relocate ∘ compact = identity).
#[test]
fn real_olean_recompaction_fixpoint() {
    let _g = lock();
    let Some(path) = fixture("Init.SizeOfLemmas.olean") else {
        eprintln!("SKIP (typed limitation): c3 fixture olean not present");
        return;
    };
    let file = std::fs::read(&path).expect("read olean");
    let env = parse_olean_envelope(&file).expect("envelope");
    let mut payload = file[env.payload_offset..].to_vec();
    relocate(&mut payload, env.payload_base(), BASE_A).expect("relocate");
    let graph = materialize(&payload, BASE_A).expect("materialize");

    let ours1 = compact(&graph, BASE_B).expect("compact real graph");
    let again = {
        let mut moved = ours1.clone();
        relocate(&mut moved, BASE_B, BASE_A).expect("relocate ours");
        materialize(&moved, BASE_A).expect("materialize ours")
    };
    let ours2 = compact(&again, BASE_B).expect("recompact");
    assert_eq!(ours1, ours2, "fixpoint holds on a real module graph");
}

/// Extreme mpz header fields must be a TYPED fault, not a panic and not a
/// misfiled one (FL-INV-07; the module contract is "malformed input yields a
/// typed RegionFault, never a panic").
///
/// `_mp_size` and `_mp_alloc` are four attacker-controlled bytes each, and the
/// coherence law `_mp_alloc >= |_mp_size|` used to be checked with
/// `mp_size.abs()`. On `i32::MIN` that negation overflows: it PANICKED in a
/// debug build, and in release it silently stayed negative, so the comparison
/// was false, the object passed its integrity check, and the fault surfaced
/// later and wrongly as `Truncated` (from the absurd 17 GB size) instead of
/// `MpzIntegrity`. Checking in the unsigned domain fixes both.
///
/// `audit` is the entry the olean codec runs over shared/sealed mappings, so
/// the input here is exactly a corrupt `.olean` byte range.
#[test]
fn mpz_header_extremes_are_typed_faults_not_panics() {
    // A region is [root word][objects…]; the root is a scalar (odd) word so
    // the walk reaches the object at offset 8.
    let region_with = |alloc: i32, mp_size: i32| {
        let mut buf = vec![0u8; 32];
        buf[0..8].copy_from_slice(&1u64.to_le_bytes());
        buf[15] = fln_rt::abi::TAG_MPZ;
        buf[16..20].copy_from_slice(&alloc.to_le_bytes());
        buf[20..24].copy_from_slice(&mp_size.to_le_bytes());
        buf
    };

    for (alloc, mp_size, what) in [
        (0, i32::MIN, "the negation that overflowed"),
        (i32::MIN, i32::MIN, "both fields extreme"),
        (i32::MIN, 1, "negative _mp_alloc"),
        (-1, 1, "_mp_alloc below |_mp_size|"),
        (4, 0, "zero limb count"),
    ] {
        let buf = region_with(alloc, mp_size);
        assert_eq!(
            fln_rt::region::audit(&buf, 0),
            Err(RegionFault::MpzIntegrity { offset: 8 }),
            "{what}: must be MpzIntegrity at the offending object"
        );
    }

    // And the coherent shape still walks: 2 limbs, alloc >= |size|, limb
    // pointer inside this object's own inline block.
    // Object at 8 spans MPZ_FIXED(24) + 2 limbs * 8 = 40 bytes, so the region
    // is 8 + 40 = 48 and the inline limb block is [32, 48).
    let mut ok = vec![0u8; 48];
    ok[0..8].copy_from_slice(&1u64.to_le_bytes());
    ok[15] = fln_rt::abi::TAG_MPZ;
    ok[16..20].copy_from_slice(&2i32.to_le_bytes());
    ok[20..24].copy_from_slice(&(-2i32).to_le_bytes()); // negative size = sign, |size| = 2
    ok[24..32].copy_from_slice(&32u64.to_le_bytes()); // limb ptr -> the block start
    assert!(
        fln_rt::region::audit(&ok, 0).is_ok(),
        "a coherent mpz must still audit clean"
    );
}

/// Two threads publishing the SAME target must never produce a mixture.
///
/// The staging file used to be keyed on the process id alone, so two threads
/// publishing one target shared it: `File::create` truncates, so T1 could write
/// half its bytes, T2 truncate and write its own, and T1 then fsync and rename
/// the MIXTURE into place — a corrupt artifact published through the very path
/// whose job is to make publication atomic. Keying the staging name on
/// (process, thread, target) fixes it; `rename` does the rest.
///
/// The assertion is deliberately "equals one input exactly", not "is
/// non-empty": a torn publication is usually still a plausible-looking file,
/// which is exactly why it would survive a weaker check.
///
/// This test is part of the Miri concurrency guard and runs under it in ~2 s —
/// see `crates/fln-unsafe-abi/MIRI_CONCURRENCY_GUARD.md` for the command, the
/// flags each arm needs, and the proof that the guard fails on the real defect.
#[test]
fn concurrent_publication_of_one_target_never_yields_a_mixture() {
    let dir = std::env::temp_dir().join(format!("fln-rt-pubrace-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let target = dir.join("region.bin");

    // Distinct, equal-length payloads so a mixture is detectable but a
    // truncation-based tear would not change the length.
    let a = vec![0xAAu8; 64 * 1024];
    let b = vec![0xBBu8; 64 * 1024];

    for _round in 0..8 {
        std::thread::scope(|s| {
            for payload in [&a, &b] {
                let target = target.clone();
                s.spawn(move || {
                    let _ = fln_rt::region::write_region_file(payload, &target);
                });
            }
        });
        let got = std::fs::read(&target).expect("target published");
        assert!(
            got == a || got == b,
            "published region is a MIXTURE: len {}, first byte {:#x}, \
             distinct bytes {:?}",
            got.len(),
            got.first().copied().unwrap_or(0),
            {
                let mut seen: Vec<u8> = got.to_vec();
                seen.sort_unstable();
                seen.dedup();
                seen
            }
        );
    }

    // The staging names must actually differ per thread, which is the property
    // the fix rests on.
    let mine = fln_rt::region::staging_tmp_path(&target);
    let theirs = std::thread::scope(|s| {
        s.spawn(|| fln_rt::region::staging_tmp_path(&target))
            .join()
            .expect("thread")
    });
    assert_ne!(
        mine, theirs,
        "two threads must not share a staging file for the same target"
    );
    let _ = std::fs::remove_dir_all(&dir);
}
