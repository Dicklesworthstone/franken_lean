//! Registry enforcement (bead franken_lean-rps, requirement a): **nothing in the
//! program hashes outside this crate.** The raw [`fln_hash::blake3`] surface may be
//! named only inside fln-hash itself; every other crate must go through the
//! domain registry ([`fln_hash::domain`]), which forces a registered [`Domain`]
//! at the type level. This test IS the CI grep — it walks every workspace crate's
//! sources and fails on an unregistered hashing reference; the planted-violation
//! case proves the scanner actually detects one.

#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};

/// Occurrences of a raw-hashing reference in one file: (line number, line text).
fn raw_hash_references(source: &str) -> Vec<(usize, String)> {
    let mut findings = Vec::new();
    for (idx, line) in source.lines().enumerate() {
        let code = match line.find("//") {
            Some(pos) => &line[..pos],
            None => line,
        };
        // The raw surface is reachable only by naming the module. The domain
        // registry path (`fln_hash::domain`, `Domain::`, `DomainHasher`) is the
        // sanctioned vocabulary and never names `blake3`.
        if code.contains("blake3") {
            findings.push((idx + 1, line.trim().to_string()));
        }
    }
    findings
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

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
}

/// The reviewed workspace member directories, from the root `Cargo.toml` `members`
/// list — so the scan follows EVERY place cargo compiles a member (`crates/*` AND
/// `tools/*`, and any member location added later), not just `crates/`. A raw-hasher
/// reference hiding under `tools/` (e.g. `tools/structure-guard`) would otherwise
/// evade the registry-enforcement check.
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

/// Every place a workspace member compiles code from.
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

#[test]
fn no_workspace_member_outside_fln_hash_names_the_raw_hasher() {
    let workspace = workspace_root();
    let mut violations = Vec::new();
    let mut scanned = 0usize;

    for member_dir in workspace_member_dirs(workspace) {
        if member_dir.file_name().and_then(|n| n.to_str()) == Some("fln-hash") {
            continue;
        }
        for file in member_source_files(&member_dir) {
            scanned += 1;
            let source = fs::read_to_string(&file).expect("readable source");
            for (line, text) in raw_hash_references(&source) {
                violations.push(format!("{}:{line}: {text}", file.display()));
            }
        }
    }

    assert!(scanned > 0, "scanner found no sources — wrong root?");
    assert!(
        violations.is_empty(),
        "unregistered hashing outside fln-hash (use fln_hash::domain instead):\n{}",
        violations.join("\n")
    );
}

#[test]
fn the_scan_covers_tools_members_not_just_crates() {
    // Same coverage law as the poison scan: compiled Rust under tools/ (e.g.
    // tools/structure-guard) must be inside the raw-hasher scan.
    let workspace = workspace_root();
    let tools_root = workspace.join("tools");
    let tools_members: Vec<PathBuf> = workspace_member_dirs(workspace)
        .into_iter()
        .filter(|m| m.starts_with(&tools_root))
        .collect();
    assert!(
        !tools_members.is_empty(),
        "workspace member scan must include tools/ members"
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
fn the_scanner_detects_a_planted_violation() {
    let planted = "use fln_hash::blake3::Hasher;\nfn f() { let _ = Hasher::new(); }\n";
    let findings = raw_hash_references(planted);
    assert_eq!(findings.len(), 1);
    assert_eq!(findings[0].0, 1);

    // Comment mentions are not code references.
    assert!(raw_hash_references("// blake3 is wrapped by the domain registry\n").is_empty());
    // The sanctioned vocabulary never trips it.
    assert!(raw_hash_references("use fln_hash::domain::{Domain, DomainHasher};\n").is_empty());
}
