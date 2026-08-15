//! fln-wgp slice 1: the compacted-region engine end to end — compact /
//! relocate / audit / materialize round-trips with sharing, the corruption
//! fault matrix, and the REAL-olean mmap path (G0-1 promoted to the
//! production machinery). Safe code throughout (`forbid(unsafe_code)`).

#![forbid(unsafe_code)]

use fln_rt::obj::Obj;
use fln_rt::region::{
    AtomicCreateError, AtomicCreateStep, AtomicWriteError, AtomicWriteStep, RegionFault,
    atomic_staging_path, canonical_digest, compact, materialize, parse_olean_envelope, relocate,
    write_file_atomic_controlled, write_file_atomic_new, write_file_atomic_new_controlled,
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
fn a_string_whose_m_length_drifted_from_the_payload_is_refused() {
    let _g = lock();
    let bytes = compact(&Obj::mk_string("m-length-probe"), BASE_A).expect("compact");
    assert!(
        fln_rt::region::audit(&bytes, BASE_A).is_ok(),
        "a freshly compacted string must audit clean"
    );

    let needle = b"m-length-probe";
    let payload = bytes
        .windows(needle.len())
        .position(|window| window == needle)
        .expect("compacted payload contains the string bytes");
    let length_field = payload
        .checked_sub(8)
        .expect("m_length sits immediately before the payload");
    let mut drifted = bytes.clone();
    drifted[length_field..length_field + 8].copy_from_slice(&99u64.to_le_bytes());

    assert!(
        matches!(
            fln_rt::region::audit(&drifted, BASE_A),
            Err(RegionFault::StringIntegrity {
                reason: "m_length is not the UTF-8 scalar count",
                ..
            })
        ),
        "audit must refuse a drifted m_length"
    );
    assert!(
        matches!(
            relocate(&mut drifted.clone(), BASE_A, BASE_B),
            Err(RegionFault::StringIntegrity {
                reason: "m_length is not the UTF-8 scalar count",
                ..
            })
        ),
        "relocate shares walk_step with audit"
    );
    assert!(
        matches!(
            materialize(&drifted, BASE_A),
            Err(RegionFault::StringIntegrity {
                reason: "m_length is not the UTF-8 scalar count",
                ..
            })
        ),
        "materialize must not heal a drifted m_length by recounting"
    );
}

/// A scalar-array whose `m_other` (element size) is 0 used to pass the
/// walk and then panic in `Obj::mk_sarray` on materialize (FL-INV-07).
#[test]
fn a_sarray_with_zero_element_size_is_a_typed_fault_not_a_panic() {
    let _g = lock();
    // [root word][sarray]: root points at the object at offset 8 so
    // materialize actually builds it instead of taking the scalar-root door.
    let mut buf = vec![0u8; 32];
    buf[0..8].copy_from_slice(&(BASE_A + 8).to_le_bytes());
    buf[12..14].copy_from_slice(&1u16.to_le_bytes()); // big-path cs_sz sentinel
    buf[14] = 0; // hostile element size
    buf[15] = fln_rt::abi::TAG_SCALAR_ARRAY;
    assert_eq!(
        fln_rt::region::audit(&buf, BASE_A),
        Err(RegionFault::BadObjectSize { offset: 8, size: 0 }),
        "audit must refuse a zero element size"
    );
    assert_eq!(
        relocate(&mut buf.clone(), BASE_A, BASE_B),
        Err(RegionFault::BadObjectSize { offset: 8, size: 0 }),
        "relocate shares walk_step with audit"
    );
    assert!(
        matches!(
            materialize(&buf, BASE_A),
            Err(RegionFault::BadObjectSize { offset: 8, size: 0 })
        ),
        "materialize must not reach mk_sarray's elem_size assert"
    );
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
        let payload_end = env.payload_offset + env.payload_len;
        let buf = &mut m.as_mut_slice().expect("mut")[env.payload_offset..payload_end];
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
    let payload_end = env.payload_offset + env.payload_len;
    let mut payload = file[env.payload_offset..payload_end].to_vec();
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

/// Audit already refused a limb pointer outside the inline block.
/// Materialize used to ignore the pointer and copy from `off + 24`,
/// so a foreign-limb mpz became a live number (FL-INV-07).
#[test]
fn a_mpz_with_foreign_or_midblock_limbs_is_refused_by_materialize() {
    let _g = lock();
    // Root points at the mpz so materialize actually builds it.
    let mut buf = vec![0u8; 48];
    buf[0..8].copy_from_slice(&8u64.to_le_bytes());
    buf[15] = fln_rt::abi::TAG_MPZ;
    buf[16..20].copy_from_slice(&2i32.to_le_bytes());
    buf[20..24].copy_from_slice(&2i32.to_le_bytes());
    // Inline block is [32, 48). Point at the root word.
    buf[24..32].copy_from_slice(&0u64.to_le_bytes());
    assert_eq!(
        fln_rt::region::audit(&buf, 0),
        Err(RegionFault::MpzIntegrity { offset: 8 }),
        "audit must refuse a foreign limb pointer"
    );
    assert!(
        matches!(
            materialize(&buf, 0),
            Err(RegionFault::MpzIntegrity { offset: 8 })
        ),
        "materialize must not mint a Nat from a foreign limb pointer"
    );

    // Mid-block: start is in the inline span, but reading 2 limbs from
    // there overruns the object into whatever follows.
    buf[24..32].copy_from_slice(&40u64.to_le_bytes());
    assert_eq!(
        fln_rt::region::audit(&buf, 0),
        Err(RegionFault::MpzIntegrity { offset: 8 }),
        "audit must refuse a mid-block limb pointer"
    );
    assert!(
        matches!(
            materialize(&buf, 0),
            Err(RegionFault::MpzIntegrity { offset: 8 })
        ),
        "materialize must not read past the minted mpz"
    );

    buf[24..32].copy_from_slice(&32u64.to_le_bytes());
    assert!(
        fln_rt::region::audit(&buf, 0).is_ok(),
        "the unmutated inline start still audits"
    );
    assert!(
        materialize(&buf, 0).is_ok(),
        "the unmutated inline start still materializes"
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
                    let _ = fln_rt::region::write_file_atomic(payload, &target);
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
    let mine = fln_rt::region::atomic_staging_path(&target);
    let theirs = std::thread::scope(|s| {
        s.spawn(|| fln_rt::region::atomic_staging_path(&target))
            .join()
            .expect("thread")
    });
    assert_ne!(
        mine, theirs,
        "two threads must not share a staging file for the same target"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn concurrent_no_clobber_publication_admits_exactly_one_complete_file() {
    let dir = std::env::temp_dir().join(format!(
        "fln-rt-pubnew-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let target = dir.join("new-region.bin");
    let a = vec![0xA5; 2 * 64 * 1024 + 17];
    let b = vec![0x5A; 2 * 64 * 1024 + 17];

    let outcomes = std::thread::scope(|scope| {
        let a_bytes = &a;
        let first_target = target.clone();
        let first = scope.spawn(move || write_file_atomic_new(a_bytes, &first_target));
        let b_bytes = &b;
        let second_target = target.clone();
        let second = scope.spawn(move || write_file_atomic_new(b_bytes, &second_target));
        [
            first.join().expect("first publisher"),
            second.join().expect("second publisher"),
        ]
    });
    assert_eq!(
        outcomes.iter().filter(|outcome| outcome.is_ok()).count(),
        1,
        "the atomic no-clobber link must elect exactly one publisher"
    );
    let loser = outcomes
        .iter()
        .find_map(|outcome| outcome.as_ref().err())
        .expect("one publisher loses the target-link race");
    assert!(!loser.target_created());
    assert_eq!(loser.step(), AtomicCreateStep::LinkTarget);
    assert!(matches!(
        loser,
        AtomicCreateError::Io { source, .. }
            if source.kind() == std::io::ErrorKind::AlreadyExists
    ));
    let published = std::fs::read(&target).expect("one complete target was published");
    assert!(
        published == a || published == b,
        "the winning target must equal one caller's bytes exactly"
    );
    let refused = write_file_atomic_new(b"replacement", &target)
        .expect_err("a later publisher must not replace the existing target");
    assert!(!refused.target_created());
    assert_eq!(refused.step(), AtomicCreateStep::LinkTarget);
    assert!(matches!(
        refused,
        AtomicCreateError::Io { ref source, .. }
            if source.kind() == std::io::ErrorKind::AlreadyExists
    ));
    assert_eq!(std::fs::read(&target).expect("retained winner"), published);
    assert!(
        std::fs::read_dir(&dir)
            .expect("list publication directory")
            .all(|entry| !entry
                .expect("directory entry")
                .file_name()
                .to_string_lossy()
                .contains(".new.")),
        "successful and losing publishers must both remove their staging links"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn controlled_no_clobber_publication_names_every_linearization_boundary() {
    const CHUNK: u64 = 64 * 1024;
    let dir = std::env::temp_dir().join(format!(
        "fln-rt-pubnew-fault-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let payload = vec![0xC3; (2 * CHUNK + 17) as usize];
    let cases = [
        ("create", AtomicCreateStep::CreateStaging, false, false),
        (
            "write",
            AtomicCreateStep::WriteChunk {
                offset: CHUNK,
                chunk_len: CHUNK,
                total_len: payload.len() as u64,
            },
            false,
            false,
        ),
        ("stage-sync", AtomicCreateStep::SyncStaging, false, false),
        ("link", AtomicCreateStep::LinkTarget, false, false),
        (
            "link-dir-sync",
            AtomicCreateStep::SyncDirectoryAfterLink,
            true,
            true,
        ),
        ("cleanup", AtomicCreateStep::RemoveStaging, true, true),
        (
            "cleanup-dir-sync",
            AtomicCreateStep::SyncDirectoryAfterCleanup,
            true,
            false,
        ),
    ];

    for (label, fault_step, target_created, staging_remains) in cases {
        let target = dir.join(format!("{label}.flbc"));
        let error = write_file_atomic_new_controlled(&payload, &target, &mut |step| {
            (step != fault_step)
                .then_some(())
                .ok_or(std::io::Error::from(std::io::ErrorKind::StorageFull))
        })
        .expect_err("the selected no-clobber boundary is refused");
        assert_eq!(error.step(), fault_step, "{label}");
        assert_eq!(error.target_created(), target_created, "{label}");
        assert!(matches!(error, AtomicCreateError::Control { .. }));
        match std::fs::read(&target) {
            Ok(bytes) => {
                assert!(target_created, "{label}: unexpected target");
                assert_eq!(bytes, payload, "{label}: target must already be complete");
            }
            Err(error) => {
                assert!(!target_created, "{label}: missing created target");
                assert_eq!(error.kind(), std::io::ErrorKind::NotFound, "{label}");
            }
        }
        let staging_count = std::fs::read_dir(&dir)
            .expect("list fault directory")
            .filter_map(Result::ok)
            .filter(|entry| {
                entry
                    .file_name()
                    .to_string_lossy()
                    .starts_with(&format!(".{label}.flbc.new."))
            })
            .count();
        assert_eq!(staging_count, usize::from(staging_remains), "{label}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn no_clobber_cleanup_failure_retains_the_primary_publication_cause() {
    let dir = std::env::temp_dir().join(format!(
        "fln-rt-pubnew-compound-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let target = dir.join("compound.flbc");
    let write_step = AtomicCreateStep::WriteChunk {
        offset: 0,
        chunk_len: 7,
        total_len: 7,
    };
    let mut primary_injected = false;
    let mut cleanup_injected = false;
    let error = write_file_atomic_new_controlled(b"payload", &target, &mut |step| {
        if step == write_step && !primary_injected {
            primary_injected = true;
            Err(std::io::Error::from(std::io::ErrorKind::StorageFull))
        } else if step == AtomicCreateStep::RemoveStaging && !cleanup_injected {
            cleanup_injected = true;
            Err(std::io::Error::from(std::io::ErrorKind::PermissionDenied))
        } else {
            Ok(())
        }
    })
    .expect_err("both the write and its staging cleanup are refused");

    assert!(primary_injected);
    assert!(cleanup_injected);
    assert_eq!(error.step(), write_step);
    assert!(!error.target_created());
    let rendered = error.to_string();
    assert!(rendered.contains("publication control refused at write"));
    assert!(rendered.contains("staging cleanup also failed"));
    let AtomicCreateError::Cleanup { primary, cleanup } = error else {
        panic!("cleanup failure must retain both typed causes");
    };
    assert!(matches!(
        primary.as_ref(),
        AtomicCreateError::Control { step, source, .. }
            if *step == write_step && source.kind() == std::io::ErrorKind::StorageFull
    ));
    assert!(matches!(
        cleanup.as_ref(),
        AtomicCreateError::Control {
            step: AtomicCreateStep::RemoveStaging,
            source,
            ..
        } if source.kind() == std::io::ErrorKind::PermissionDenied
    ));
    assert!(!target.exists());
    assert_eq!(
        std::fs::read_dir(&dir)
            .expect("list compound fault directory")
            .filter_map(Result::ok)
            .filter(|entry| entry.file_name().to_string_lossy().contains(".new."))
            .count(),
        1,
        "a refused cleanup must leave the exact staging entry visible"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn controlled_atomic_publication_distinguishes_pre_and_post_rename_faults() {
    const CHUNK: u64 = 64 * 1024;
    let dir = std::env::temp_dir().join(format!("fln-rt-pubfault-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let old = b"old-complete".to_vec();
    let payload = vec![0xA5; (2 * CHUNK + 17) as usize];
    let cases = [
        ("create", AtomicWriteStep::CreateStaging, false, false),
        (
            "second-chunk",
            AtomicWriteStep::WriteChunk {
                offset: CHUNK,
                chunk_len: CHUNK,
                total_len: payload.len() as u64,
            },
            false,
            true,
        ),
        ("file-sync", AtomicWriteStep::SyncStaging, false, true),
        ("rename", AtomicWriteStep::RenameTarget, false, true),
        (
            "directory-sync",
            AtomicWriteStep::SyncDirectory,
            true,
            false,
        ),
    ];

    for (label, fault_step, target_replaced, staging_remains) in cases {
        let target = dir.join(format!("{label}.bin"));
        std::fs::write(&target, &old).expect("seed prior complete target");
        let staging = atomic_staging_path(&target);
        let mut injected = false;
        let error = write_file_atomic_controlled(&payload, &target, &mut |step| {
            if step == fault_step {
                injected = true;
                Err(std::io::Error::from(std::io::ErrorKind::StorageFull))
            } else {
                Ok(())
            }
        })
        .expect_err("the selected atomic-write step is refused");

        assert!(injected, "{label}: selected step was not reached");
        assert_eq!(error.step(), fault_step, "{label}");
        assert_eq!(error.target_replaced(), target_replaced, "{label}");
        assert!(
            matches!(&error, AtomicWriteError::Control { .. }),
            "{label}: injected failure was misclassified"
        );
        if let AtomicWriteError::Control { source, .. } = error {
            assert_eq!(source.kind(), std::io::ErrorKind::StorageFull, "{label}");
        }

        let visible = std::fs::read(&target).expect("visible target remains complete");
        if target_replaced {
            assert_eq!(
                visible, payload,
                "{label}: renamed target is the new whole file"
            );
        } else {
            assert_eq!(visible, old, "{label}: prior target remains byte-identical");
        }
        assert_eq!(staging.exists(), staging_remains, "{label}");
    }

    let _ = std::fs::remove_dir_all(&dir);
}
