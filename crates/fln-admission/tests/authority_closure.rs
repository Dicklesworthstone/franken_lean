//! The admission authority's closure, re-derived independently of the build script.
//!
//! `build.rs` reads the dependency closure from the `Cargo.toml` files and digests every
//! crate in it (bead `fln-import-reuse-composes-4ngt`). An import-reuse record keyed by that
//! digest is sound only if the closure is exactly what the crate compiles against: a crate
//! left out of the digest could change an admission verdict without changing the identity.
//! This test derives the closure a second way, by reading each `[dependencies]` table as raw
//! lines and following every `fln-*` key to its crate directory, and requires the two to
//! agree exactly. A planted omission must be caught, and an empty walk refused as a broken
//! scan rather than read as agreement.
#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::path::PathBuf;

fn crates_root() -> PathBuf {
    // The tree this run was launched from, checked against the one the binary was built in.
    let manifest: PathBuf = fln_core::checked_manifest_dir!();
    manifest.parent().expect("crates/").to_path_buf()
}

/// Every workspace crate named in `name`'s `[dependencies]` table, by key.
fn direct(name: &str) -> BTreeSet<String> {
    let manifest = crates_root().join(name).join("Cargo.toml");
    let text = std::fs::read_to_string(&manifest).expect("manifest");
    let mut inside = false;
    let mut found = BTreeSet::new();
    for line in text.lines() {
        let line = line.trim();
        if line.starts_with('[') {
            inside = line == "[dependencies]";
            continue;
        }
        if !inside || line.starts_with('#') {
            continue;
        }
        if let Some(key) = line.split('=').next().map(str::trim)
            && key.starts_with("fln-")
        {
            found.insert(key.to_owned());
        }
    }
    found
}

fn walk(start: &str, omit: Option<&str>) -> BTreeSet<String> {
    let mut seen = BTreeSet::new();
    let mut pending = vec![start.to_owned()];
    while let Some(name) = pending.pop() {
        if Some(name.as_str()) == omit || !seen.insert(name.clone()) {
            continue;
        }
        pending.extend(direct(&name));
    }
    seen
}

fn built() -> BTreeSet<String> {
    fln_admission::AUTHORITY_CLOSURE
        .split(',')
        .map(str::to_owned)
        .collect()
}

#[test]
fn the_digested_closure_is_the_compiled_closure() {
    let derived = walk("fln-admission", None);
    assert!(
        derived.len() >= 6 && derived.contains("fln-kernel") && derived.contains("fln-checker"),
        "a broken scan, not a closure: {derived:?}"
    );
    assert_eq!(built(), derived, "build.rs digests a different closure");
    for excluded in ["fln-elab", "fln-parse", "fln-comp", "fln-vm", "fln"] {
        assert!(
            !derived.contains(excluded),
            "{excluded} reached the authority"
        );
    }
}

#[test]
fn an_omitted_dependency_is_caught() {
    // The mutant the comparison exists for: one crate missing from the digest.
    for omitted in ["fln-kernel", "fln-checker", "fln-olean"] {
        let mutant = walk("fln-admission", Some(omitted));
        assert_ne!(built(), mutant, "omitting {omitted} went unnoticed");
    }
}

/// The top-level directories `build.rs` leaves out of the digest.
const UNDIGESTED: [&str; 4] = ["tests", "benches", "examples", "target"];
const INCLUDES: [&str; 3] = ["include_str!(", "include_bytes!(", "include!("];

/// Every `.rs` file `build.rs` digests in one crate directory.
fn digested_sources(directory: &std::path::Path, root: &std::path::Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(directory).expect("crate directory") {
        let path = entry.expect("entry").path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if path.is_dir() {
            if !(directory == root && UNDIGESTED.contains(&name)) {
                digested_sources(&path, root, out);
            }
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

/// Why one include site in `file` would pull undigested bytes into the authority, if it
/// would: its argument must be a plain string literal naming a file inside `crate_dir`
/// and outside the directories the digest leaves out.
fn undigested_include(
    crate_dir: &std::path::Path,
    file: &std::path::Path,
    argument: &str,
) -> Option<String> {
    let Some(literal) = argument
        .trim_start()
        .strip_prefix('"')
        .and_then(|rest| rest.split_once('"'))
        .map(|(literal, _)| literal)
    else {
        return Some(format!(
            "{}: not a plain string literal: {argument:.40}",
            file.display()
        ));
    };
    let mut resolved = file.parent().expect("file directory").to_path_buf();
    for component in std::path::Path::new(literal).components() {
        match component {
            std::path::Component::ParentDir => {
                resolved.pop();
            }
            std::path::Component::Normal(part) => resolved.push(part),
            _ => return Some(format!("{}: `{literal}` is not relative", file.display())),
        }
    }
    let inside = resolved.strip_prefix(crate_dir).ok().and_then(|relative| {
        let first = relative
            .components()
            .next()?
            .as_os_str()
            .to_str()?
            .to_owned();
        (!UNDIGESTED.contains(&first.as_str())).then_some(())
    });
    inside
        .is_none()
        .then(|| format!("{}: `{literal}` leaves the digested tree", file.display()))
}

#[test]
fn every_include_in_the_digested_code_is_itself_digested() {
    let root = crates_root();
    let mut sites = 0usize;
    let mut findings = Vec::new();
    for name in built() {
        let crate_dir = root.join(&name);
        let mut files = Vec::new();
        digested_sources(&crate_dir, &crate_dir, &mut files);
        for file in files {
            let text = std::fs::read_to_string(&file).expect("source");
            for needle in INCLUDES {
                for (at, _) in text.match_indices(needle) {
                    sites += 1;
                    let argument = &text[at + needle.len()..];
                    findings.extend(undigested_include(&crate_dir, &file, argument));
                }
            }
        }
    }
    assert!(
        sites >= 1,
        "a broken scan: no include site in the whole closure"
    );
    assert!(findings.is_empty(), "{findings:#?}");
}

#[test]
fn an_include_outside_the_digest_is_caught() {
    let crate_dir = crates_root().join("fln-olean");
    let file = crate_dir.join("src/rebuild.rs");
    assert_eq!(
        undigested_include(&crate_dir, &file, "\"../fixtures/g05_pilot.olean\")"),
        None
    );
    for escaping in [
        "\"../../fln-elab/src/lib.rs\")",
        "\"../tests/fixture.olean\")",
        "\"/etc/hostname\")",
        "concat!(env!(\"OUT_DIR\"), \"/x\"))",
    ] {
        assert!(
            undigested_include(&crate_dir, &file, escaping).is_some(),
            "{escaping} went unnoticed"
        );
    }
}

#[test]
fn the_authority_is_a_digest_and_names_its_closure() {
    let authority = fln_admission::AUTHORITY;
    assert_eq!(authority.len(), 64, "{authority}");
    assert!(
        authority.bytes().all(|b| b.is_ascii_hexdigit()),
        "{authority}"
    );
}
