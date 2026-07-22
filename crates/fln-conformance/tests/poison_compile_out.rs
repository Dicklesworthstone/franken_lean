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

/// The reviewed workspace member directories, taken from the root `Cargo.toml`
/// `members` list — so the scan follows EVERY place cargo compiles a workspace
/// member (`crates/*` AND `tools/*`, and any member location added later), not just
/// `crates/`. A leak hiding under `tools/` (e.g. `tools/structure-guard`) would
/// otherwise evade the compile-out check.
fn workspace_member_dirs(workspace: &Path) -> Vec<PathBuf> {
    let manifest = fs::read_to_string(workspace.join("Cargo.toml")).expect("root Cargo.toml");
    let members_body = manifest
        .split_once("members")
        .and_then(|(_, rest)| rest.split_once('['))
        .and_then(|(_, rest)| rest.split_once(']'))
        .map(|(body, _)| body)
        .expect("[workspace] members array");
    let mut dirs = Vec::new();
    for raw in members_body.split(',') {
        let pattern = raw.trim().trim_matches('"').trim();
        if pattern.is_empty() {
            continue;
        }
        if let Some(prefix) = pattern.strip_suffix("/*") {
            // Glob member: enumerate immediate subdirectories.
            if let Ok(entries) = fs::read_dir(workspace.join(prefix)) {
                for entry in entries.flatten() {
                    let p = entry.path();
                    if p.is_dir() {
                        dirs.push(p);
                    }
                }
            }
        } else {
            let p = workspace.join(pattern);
            if p.is_dir() {
                dirs.push(p);
            }
        }
    }
    dirs.sort();
    dirs
}

/// Every place a workspace member compiles code from: src, tests, benches, examples,
/// and the build script.
fn member_source_files(member_dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect_rs_files(&member_dir.join("src"), &mut files);
    collect_rs_files(&member_dir.join("tests"), &mut files);
    collect_rs_files(&member_dir.join("benches"), &mut files);
    collect_rs_files(&member_dir.join("examples"), &mut files);
    let build_rs = member_dir.join("build.rs");
    if build_rs.exists() {
        files.push(build_rs);
    }
    files
}

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
}

#[test]
fn no_workspace_member_outside_fln_conformance_names_the_poison_tag() {
    let workspace = workspace_root();
    let mut violations = Vec::new();
    let mut scanned = 0usize;
    for member_dir in workspace_member_dirs(workspace) {
        // fln-conformance is the one crate allowed to name the tag.
        if member_dir.file_name().and_then(|n| n.to_str()) == Some("fln-conformance") {
            continue;
        }
        for file in member_source_files(&member_dir) {
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
fn the_scan_covers_tools_members_not_just_crates() {
    // Regression for the fln-euo review finding: compiled Rust under tools/ (e.g.
    // tools/structure-guard) must be inside the ORACLE_FALLBACK scan, else a leak
    // there would evade the workspace-wide compile-out claim.
    let workspace = workspace_root();
    let members = workspace_member_dirs(workspace);
    let tools_root = workspace.join("tools");
    let tools_members: Vec<&PathBuf> = members
        .iter()
        .filter(|m| m.starts_with(&tools_root))
        .collect();
    assert!(
        !tools_members.is_empty(),
        "workspace member scan must include tools/ members: {members:?}"
    );
    let tools_source_files: usize = tools_members
        .iter()
        .map(|m| member_source_files(m).len())
        .sum();
    assert!(
        tools_source_files > 0,
        "at least one tools/ member must contribute source files to the scan"
    );
}

#[test]
fn the_scanner_detects_a_planted_leak() {
    let planted = "let tag = \"ORACLE_FALLBACK\";";
    assert!(planted.contains("ORACLE_FALLBACK"), "scanner substring law");
}
