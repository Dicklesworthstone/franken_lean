//! fln-wgp slice-1 verification for the mapping primitive: CoW isolation,
//! the at-base fast path, sealing, page facts, and typed failure paths.
//! Everything drives the public safe surface — no unsafe in tests.

use crate::mapping::{MapError, RegionMapping, page_size};
use std::io::Write;
use std::path::PathBuf;

fn scratch(name: &str, bytes: &[u8]) -> PathBuf {
    // Deliberately NOT std::env::temp_dir(): /tmp is a shared tmpfs that
    // other agents can fill; scratch lives next to the build artifacts.
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target_local/fln-unsafe-region-tests");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join(format!("{name}-{}", std::process::id()));
    let mut f = std::fs::File::create(&path).expect("create");
    f.write_all(bytes).expect("write");
    f.sync_all().expect("sync");
    path
}

#[test]
fn page_size_is_sane() {
    let p = page_size();
    assert!(p.is_power_of_two() && p >= 4096, "page size {p}");
}

#[test]
fn maps_and_reads_file_bytes() {
    let path = scratch("read", b"region-bytes-0123456789");
    let m = RegionMapping::map_file_private(&path).expect("map");
    assert_eq!(m.len(), 23);
    assert!(!m.is_empty());
    assert!(!m.is_sealed());
    assert_eq!(m.as_slice(), b"region-bytes-0123456789");
    assert!(m.addr().is_multiple_of(page_size()));
}

#[test]
fn cow_writes_never_reach_the_file_or_other_mappings() {
    let path = scratch("cow", &[7u8; 64]);
    let mut a = RegionMapping::map_file_private(&path).expect("map a");
    let b = RegionMapping::map_file_private(&path).expect("map b");
    a.as_mut_slice().expect("mut")[0] = 99;
    assert_eq!(a.as_slice()[0], 99);
    assert_eq!(
        b.as_slice()[0],
        7,
        "private CoW must not leak across mappings"
    );
    drop(a);
    assert_eq!(
        std::fs::read(&path).expect("reread")[0],
        7,
        "private CoW must never reach the file"
    );
}

#[test]
fn seal_refuses_mutation_and_double_seal() {
    let path = scratch("seal", &[1u8; 32]);
    let mut m = RegionMapping::map_file_private(&path).expect("map");
    m.as_mut_slice().expect("pre-seal mut")[1] = 2;
    m.seal().expect("seal");
    assert!(m.is_sealed());
    assert!(matches!(m.as_mut_slice(), Err(MapError::Sealed)));
    assert!(matches!(m.seal(), Err(MapError::Sealed)));
    // Reads stay valid after sealing.
    assert_eq!(m.as_slice()[1], 2);
}

#[test]
fn at_base_fast_path_and_occupied_fallback() {
    let path = scratch("atbase", &[3u8; 4096]);
    // Learn a plausibly-free page-aligned address by mapping and dropping.
    let probe = RegionMapping::map_file_private(&path).expect("probe");
    let base = probe.addr();
    drop(probe);
    // A racing thread may have taken the range; the typed None is the honest
    // fallback (the relocate-or-copy law), so only the Some arm asserts.
    if let Some(m) = RegionMapping::try_map_file_private_at(&path, base).expect("try at freed base")
    {
        assert_eq!(m.addr(), base, "fixed mapping lands at the requested base");
    }
    // An occupied range must come back None, never clobbered (NOREPLACE).
    let holder = RegionMapping::map_file_private(&path).expect("holder");
    let taken = holder.addr();
    assert!(
        RegionMapping::try_map_file_private_at(&path, taken)
            .expect("try at occupied base")
            .is_none(),
        "MAP_FIXED_NOREPLACE must refuse an occupied range"
    );
    assert_eq!(holder.as_slice()[0], 3, "holder mapping untouched");
    // Misaligned base is a typed error.
    assert!(matches!(
        RegionMapping::try_map_file_private_at(&path, taken + 1),
        Err(MapError::MisalignedBase { .. })
    ));
}

#[test]
fn typed_failures_for_bad_sources() {
    let empty = scratch("empty", b"");
    assert!(matches!(
        RegionMapping::map_file_private(&empty),
        Err(MapError::Empty)
    ));
    assert!(matches!(
        RegionMapping::map_file_private(std::path::Path::new("/nonexistent/fln-region-test-path")),
        Err(MapError::Io(_))
    ));
    assert!(matches!(
        RegionMapping::map_file_private(&std::env::temp_dir()),
        Err(MapError::Io(_))
    ));
}
