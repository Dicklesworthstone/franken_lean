//! `scratch_reclamation_census` — the workspace-wide half of the scratch fence's
//! binding (bead `franken_lean-eir2`).
//!
//! `fln_core::scratch` is the fence: one `ScratchRoot` guard, one `is_reclaimable`
//! predicate, one `SCRATCH_FAMILIES` table. `fln-core`'s own gate proves the machinery
//! and the table's internal consistency. What it cannot prove from rank 0 is the join
//! to the rest of the workspace, which is the half that rots:
//!
//! * a producer that stops naming its constant, or invents a prefix outside the table
//!   (its roots silently stop being reclaimed — the under-report direction);
//! * a remainder row whose producer was routed or deleted (a stale row keeping a slot
//!   warm — `fln-8zsq`'s disclosure-drift shape);
//! * a NEW `std::env::temp_dir()` call site appearing anywhere in the tree, which is
//!   how every one of the seven censused leaks started.
//!
//! So this file binds every family row to its declared source in both directions, and
//! classifies every `temp_dir` call site in the workspace — routed machinery, declared
//! remainder, self-cleaning, or non-producer — with conservation and floors so neither
//! direction can drift quietly. It walks sources only.
//!
//! It also hosts the both-directions retention proofs for the two families whose
//! producer surfaces are pin-dependent (`golden_vellum.rs`, `reference_differential.rs`):
//! those surfaces ask the pinned Reference, CI installs none, and the CI-execution join
//! (fln-rgha) reads any `test:` citation into them as "evidence CI never executed" —
//! surface-granular, so a pin-independent function is invisible to it (f2t9). The proofs
//! live here, in a pin-free surface, exercising the same family constructors directly; the
//! guard-owned roots they create reclaim exactly like the producer's own fixtures.

#![forbid(unsafe_code)]

use fln_core::scratch::{REFDIFF_PREFIX, SCRATCH_FAMILIES, ScratchRoot, VDI4_PREFIX};
use std::path::{Path, PathBuf};

/// The call every scratch-root producer that bypasses the fence must make.
const NEEDLE: &str = "std::env::temp_dir()";

/// This file, excluded from its own walk: a scan whose search space contains its own
/// declaration passes by reading itself (`fln-8zsq`'s lesson), so the walk asserts the
/// exclusion matched exactly once — a renamed census file cannot silently vacate the
/// walk that is supposed to find it.
const SELF_PATH: &str = "crates/fln-conformance/tests/scratch_reclamation_census.rs";

/// The one file allowed to call the needle for root creation: the fence itself.
const MACHINERY: &[&str] = &["crates/fln-core/src/scratch.rs"];

/// Files that call the needle but remove what they made on the passing path by hand.
/// Each carries the cleanup needle the file must still contain, so a file whose
/// cleanup is deleted stops matching its class instead of staying classified.
const SELF_CLEANING: &[(&str, &str)] = &[
    ("crates/fln-conformance/src/pin.rs", "remove_dir_all"),
    (
        "crates/fln-conformance/tests/agents_enforcement_census.rs",
        "remove_dir",
    ),
    ("crates/fln-rt/tests/region_engine.rs", "remove_dir_all"),
    // The G0-3 door test's per-pid plugin workdir, reclaimed on the passing path.
    ("crates/fln-unsafe-abi/src/tests.rs", "remove_dir_all"),
    // The attribute census cells' scratch vendor trees, reclaimed per cell.
    (
        "crates/fln-conformance/tests/attribute_state_census.rs",
        "remove_dir_all",
    ),
];

/// Files whose needle sites materialize nothing: fence probes building synthetic
/// paths to interrogate the predicate, and a doc comment plus an error-case input.
const NON_PRODUCER: &[&str] = &[
    "crates/fln-unsafe-region/src/tests.rs",
    "tools/structure-guard/src/scratch.rs",
    "tools/structure-guard/tests/common/mod.rs",
];

/// Directories the source walk refuses: build output is not source, and
/// `crates/fln-conformance/target/` is exactly where this suite's worker-refusal
/// fixtures live.
const SKIP_DIRS: &[&str] = &["target", "target_local", ".git"];

fn walk_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("walk must read {}: {error}", dir.display()));
    for entry in entries {
        let path = entry
            .unwrap_or_else(|error| panic!("walk entry under {}: {error}", dir.display()))
            .path();
        let file_type = path
            .symlink_metadata()
            .unwrap_or_else(|error| panic!("walk stat {}: {error}", path.display()))
            .file_type();
        if file_type.is_dir() {
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if !SKIP_DIRS.contains(&name) {
                walk_rs_files(&path, out);
            }
        } else if file_type.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

fn read(root: &Path, relative: &str) -> String {
    let path = root.join(relative);
    assert!(
        path.is_file(),
        "expected file is missing: {}",
        path.display()
    );
    std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("expected file is unreadable: {}: {error}", path.display()))
}

#[test]
fn every_temp_dir_call_site_is_classified() {
    let root = fln_conformance::checked_workspace_root!();
    let root = root.as_path();

    let mut files = Vec::new();
    for top in ["crates", "tools", "tribunal"] {
        walk_rs_files(&root.join(top), &mut files);
    }
    assert!(
        files.len() >= 200,
        "refusing a vacuous walk: only {} Rust files under crates/+tools/+tribunal/ \
         (262 at the census commit); a walk this small is broken, not clean",
        files.len()
    );

    let mut needle_files: Vec<String> = files
        .iter()
        .filter_map(|path| {
            let text = std::fs::read_to_string(path).ok()?;
            text.contains(NEEDLE).then(|| {
                path.strip_prefix(root)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned()
            })
        })
        .collect();
    needle_files.sort();

    // The exclusion must match exactly once, proving the walk can see this file before
    // it is trusted to see any other.
    let self_count = needle_files
        .iter()
        .filter(|f| f.as_str() == SELF_PATH)
        .count();
    assert_eq!(
        self_count, 1,
        "the walk must find this census exactly once before it is excluded; found \
         {self_count} — a renamed census file vacates the walk it asserts over"
    );
    needle_files.retain(|f| f != SELF_PATH);

    let remainder_files: Vec<&str> = SCRATCH_FAMILIES
        .iter()
        .filter(|family| !family.routed)
        .map(|family| family.producer)
        .collect();

    let mut unclassified = Vec::new();
    for found in &needle_files {
        let in_machinery = MACHINERY.contains(&found.as_str());
        let in_remainder = remainder_files.contains(&found.as_str());
        let in_self_cleaning = SELF_CLEANING.iter().any(|(path, _)| path == found);
        let in_non_producer = NON_PRODUCER.contains(&found.as_str());
        let classes = in_machinery as usize
            + in_remainder as usize
            + in_self_cleaning as usize
            + in_non_producer as usize;
        if classes != 1 {
            unclassified.push(format!("{found} (in {classes} classes)"));
        }
    }
    assert!(
        unclassified.is_empty(),
        "every {NEEDLE} call site must be in exactly one class — machinery, declared \
         remainder, self-cleaning, or non-producer. An entry here is either a new \
         scratch producer bypassing the fence (route it through ScratchRoot with a new \
         SCRATCH_FAMILIES row) or a class this census has not been told about:\n{}",
        unclassified.join("\n")
    );

    // Every class member must be present in the walk, so a deleted or renamed file
    // cannot leave its classification behind as a slot for a future mismatch.
    let mut missing = Vec::new();
    for path in MACHINERY
        .iter()
        .chain(NON_PRODUCER.iter())
        .chain(remainder_files.iter())
        .chain(SELF_CLEANING.iter().map(|(path, _)| path))
    {
        if !needle_files.iter().any(|found| found == path) {
            missing.push(*path);
        }
    }
    assert!(
        missing.is_empty(),
        "these classified files no longer carry {NEEDLE}; their classes are stale and \
         must be removed in the same edit that stopped the call:\n{}",
        missing.join("\n")
    );

    // Self-cleaning is only a class while the cleanup exists.
    for (path, cleanup) in SELF_CLEANING {
        let text = read(root, path);
        assert!(
            text.contains(cleanup),
            "{path} is classified self-cleaning but no longer carries `{cleanup}`: a \
             file that stops removing its own roots is a producer, not self-cleaning"
        );
    }

    assert!(
        needle_files.len() >= 9,
        "refusing a vacuous classification: only {} needle files (expected machinery + \
         remainders + self-cleaning + non-producers); a walk this small is broken, not \
         clean",
        needle_files.len()
    );
}

#[test]
fn every_family_row_is_bound_to_its_source() {
    let root = fln_conformance::checked_workspace_root!();
    let root = root.as_path();

    let mut routed = 0usize;
    let mut remainder_prefixes = Vec::new();
    for family in SCRATCH_FAMILIES {
        let text = read(root, family.producer);
        assert!(
            text.len() > 512,
            "refusing a vacuous scan: {} is implausibly small at {} bytes",
            family.producer,
            text.len()
        );

        if family.routed {
            // The constant must be the FIRST ARGUMENT of the construction, not merely
            // present in the file: bind the call site, which is the thing that could
            // actually drift (the fence probe in tests/common/mod.rs legitimately
            // carries the literal as test input, so a blanket literal ban is a wall
            // against a correct file).
            assert!(
                text.contains(&format!("ScratchRoot::create({}", family.constant)),
                "{} is routed but never calls ScratchRoot::create({}); the declared \
                 prefix {:?} therefore has no producer binding it",
                family.producer,
                family.constant,
                family.prefix
            );
            routed += 1;
        } else {
            // A remainder cannot name the constant — its producer has no dependency on
            // the fence's crate, which is the whole reason it is a remainder — so the
            // literal is the only spelling available, and its absence means the
            // disclosure names a producer that no longer produces it.
            assert!(
                text.contains(&format!("\"{}", family.prefix)),
                "{} is a declared remainder but does not carry the literal {:?}",
                family.producer,
                family.prefix
            );
            remainder_prefixes.push(family.prefix);
        }

        let constructs_guard = text.contains("ScratchRoot::create");
        assert_eq!(
            constructs_guard, family.routed,
            "{} routed={} but constructs_guard={}: a routed producer must build a \
             ScratchRoot and a declared remainder must not",
            family.producer, family.routed, constructs_guard
        );
    }

    // Conservation and exact membership, in both directions: the remainder cannot be
    // emptied by deleting a row instead of routing its producer, and neither side can
    // grow without a deliberate edit to this census.
    assert_eq!(
        SCRATCH_FAMILIES.len(),
        17,
        "the workspace declares exactly 17 scratch families; a change here is a \
         deliberate, disclosed act"
    );
    assert_eq!(routed, 14, "exactly 14 producers route through ScratchRoot");
    remainder_prefixes.sort_unstable();
    assert_eq!(
        remainder_prefixes,
        ["fln-derive-", "fln-epoch-lab-", "fln-ownership-publisher-"],
        "the declared remainder is exactly these three rows"
    );
}

/// `franken_lean-eir2` acceptance criterion 3 for the vdi4 family: retention on failure,
/// proved in BOTH directions through the family's own constructor. Lives here rather than
/// beside the producer because `golden_vellum.rs` is a pin-dependent surface and the
/// CI-execution join reads citations into it as unexecuted (see the file header).
#[test]
fn vdi4_workspaces_reclaim_on_pass_and_retain_on_failure() {
    let passing = {
        let root = ScratchRoot::create(VDI4_PREFIX, "golden-vellum", "reclaim-pass")
            .expect("create passing workspace");
        root.path().to_path_buf()
    };
    assert!(
        !passing.exists(),
        "a passing cell's workspace must be reclaimed: {}",
        passing.display()
    );

    let observed = std::cell::RefCell::new(None);
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let root = ScratchRoot::create(VDI4_PREFIX, "golden-vellum", "reclaim-fail")
            .expect("create failing workspace");
        *observed.borrow_mut() = Some(root.path().to_path_buf());
        panic!("deliberate failure so the fixture guard drops during an unwind");
    }));
    assert!(unwound.is_err(), "the failing cell must actually unwind");
    let retained = observed
        .into_inner()
        .expect("the failing cell materialized before it panicked");
    assert!(
        retained.exists(),
        "a failing cell's workspace must be retained: {}",
        retained.display()
    );
    std::fs::remove_dir_all(&retained).expect("the probe reclaims what it retained");
}

/// `franken_lean-eir2` acceptance criterion 3 for the refdiff family: retention on
/// failure, proved in BOTH directions through the family's own constructor. Lives here
/// rather than beside the producer because `reference_differential.rs` asks the pinned
/// Reference and the CI-execution join reads citations into it as unexecuted (see the
/// file header).
#[test]
fn reference_differential_roots_reclaim_on_pass_and_retain_on_failure() {
    let passing = {
        let root = ScratchRoot::create(REFDIFF_PREFIX, "reference-differential", "reclaim-pass")
            .expect("create passing workspace");
        root.path().to_path_buf()
    };
    assert!(
        !passing.exists(),
        "a passing cell's oracle workspace must be reclaimed: {}",
        passing.display()
    );

    let observed = std::cell::RefCell::new(None);
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let root = ScratchRoot::create(REFDIFF_PREFIX, "reference-differential", "reclaim-fail")
            .expect("create failing workspace");
        *observed.borrow_mut() = Some(root.path().to_path_buf());
        panic!("deliberate failure so the fixture guard drops during an unwind");
    }));
    assert!(unwound.is_err(), "the failing cell must actually unwind");
    let retained = observed
        .into_inner()
        .expect("the failing cell materialized before it panicked");
    assert!(
        retained.exists(),
        "a failing cell's oracle workspace must be retained: {}",
        retained.display()
    );
    std::fs::remove_dir_all(&retained).expect("the probe reclaims what it retained");
}
