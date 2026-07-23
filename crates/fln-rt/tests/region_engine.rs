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
