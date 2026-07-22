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

#[test]
fn no_crate_outside_fln_hash_names_the_raw_hasher() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
    let crates_dir = workspace.join("crates");
    let mut violations = Vec::new();
    let mut scanned = 0usize;

    let crate_dirs = fs::read_dir(&crates_dir).expect("crates/ exists");
    for entry in crate_dirs.flatten() {
        let crate_dir = entry.path();
        let crate_name = entry.file_name().to_string_lossy().into_owned();
        if !crate_dir.is_dir() || crate_name == "fln-hash" {
            continue;
        }
        let mut files = Vec::new();
        collect_rs_files(&crate_dir.join("src"), &mut files);
        collect_rs_files(&crate_dir.join("tests"), &mut files);
        // Every other place cargo compiles code from: a violation must not be able
        // to hide in a build script, bench, or example.
        collect_rs_files(&crate_dir.join("benches"), &mut files);
        collect_rs_files(&crate_dir.join("examples"), &mut files);
        let build_rs = crate_dir.join("build.rs");
        if build_rs.exists() {
            files.push(build_rs);
        }
        for file in files {
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
