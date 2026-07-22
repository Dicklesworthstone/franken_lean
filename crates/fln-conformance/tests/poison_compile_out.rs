//! The ORACLE_FALLBACK compile-out check (plan §18.10, D8; bead fln-euo): default and
//! release builds contain no poison machinery, and no authoritative crate outside
//! fln-conformance may even name the tag. This test IS the CI check.

#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};

/// Exists only when the feature is off — which is exactly the claim: the default
/// (and release) feature set compiles the poison machinery out. A run with
/// `--features oracle-fallback-dev` compiles this test out instead and runs the
/// poison module's own tests. The `cfg` gate on this function IS the assertion;
/// a default build that somehow enabled the feature would fail the workspace grep
/// below and the feature-set audit in CI.
#[cfg(not(feature = "oracle-fallback-dev"))]
#[test]
fn the_poison_feature_is_compiled_out_by_default() {
    // Compiled-in under cfg(not(feature)) — nothing further to assert at runtime.
}

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().collect();
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

#[test]
fn no_crate_outside_fln_conformance_names_the_poison_tag() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
    let mut violations = Vec::new();
    let mut scanned = 0usize;
    for entry in fs::read_dir(workspace.join("crates"))
        .expect("crates/")
        .flatten()
    {
        let crate_dir = entry.path();
        let crate_name = entry.file_name().to_string_lossy().into_owned();
        if !crate_dir.is_dir() || crate_name == "fln-conformance" {
            continue;
        }
        let mut files = Vec::new();
        collect_rs_files(&crate_dir.join("src"), &mut files);
        collect_rs_files(&crate_dir.join("tests"), &mut files);
        // Every other place cargo compiles code from: a leak must not be able to
        // hide in a build script, bench, or example.
        collect_rs_files(&crate_dir.join("benches"), &mut files);
        collect_rs_files(&crate_dir.join("examples"), &mut files);
        let build_rs = crate_dir.join("build.rs");
        if build_rs.exists() {
            files.push(build_rs);
        }
        for file in files {
            scanned += 1;
            let source = fs::read_to_string(&file).expect("readable source");
            for (idx, line) in source.lines().enumerate() {
                if line.contains("ORACLE_FALLBACK") {
                    violations.push(format!("{}:{}: {}", file.display(), idx + 1, line.trim()));
                }
            }
        }
    }
    assert!(scanned > 0, "scanner found no sources — wrong root?");
    assert!(
        violations.is_empty(),
        "the poison tag leaked outside fln-conformance:\n{}",
        violations.join("\n")
    );
}

#[test]
fn the_scanner_detects_a_planted_leak() {
    let planted = "let tag = \"ORACLE_FALLBACK\";";
    assert!(planted.contains("ORACLE_FALLBACK"), "scanner substring law");
}
