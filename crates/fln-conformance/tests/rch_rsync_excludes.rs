//! `rch_rsync_excludes` — regression and mutant gate for repo-scoped RCH transfer
//! configuration (bead `fln-rch-rsync-excludes-proofs-artifacts-445z`).
//!
//! Unanchored `artifacts/` and `proofs/` entries in RCH's rsync `exclude_patterns`
//! match directory segments anywhere in the tree, stripping tracked Rust modules under
//! `crates/fln-parse/src/{extensions/artifacts,proofs}/` and
//! `crates/fln/src/{runtime/proofs,source_check/modules/artifacts}/` on ordinary
//! `rch exec` transfers. `.rch/config.toml` overrides `[transfer].exclude_patterns`
//! with root-anchored `/artifacts/` and `/proofs/` rules while retaining every
//! build-output, agent-state, and credential exclusion from the fleet baseline.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};

const SKIP_DIRS: &[&str] = &["target", "target_local", ".git"];

const REQUIRED_ANCHORED_PATTERNS: &[&str] = &[
    "/artifacts/",
    "/artifacts/**",
    "/scripts/e2e/artifacts/",
    "/scripts/e2e/artifacts/**",
    "/proofs/",
    "/proofs/**",
];

const FORBIDDEN_UNANCHORED_PATTERNS: &[&str] =
    &["artifacts/", "artifacts/**", "proofs/", "proofs/**"];

const REQUIRED_SAFETY_PATTERNS: &[&str] = &[
    "*.rlib",
    "*.rmeta",
    ".beads/*.db",
    ".beads/*.db-*",
    ".beads/*.db.*",
    ".beads/*.db-wal*",
    ".git/objects/*",
    ".rch-target-*",
    ".rch-target-*/**",
    "target/",
    "target_local/",
    ".ntm/",
    ".beads-recovery/",
    ".env",
    ".env.*",
    "credentials.json",
    "secrets.json",
    "secrets.yaml",
    ".cargo/credentials",
    ".cargo/credentials.toml",
    "id_rsa",
    "id_ed25519",
    "id_ecdsa",
    "id_dsa",
    ".netrc",
];

fn parse_exclude_patterns(toml_text: &str) -> Vec<String> {
    let mut in_transfer = false;
    let mut in_array = false;
    let mut patterns = Vec::new();

    for raw_line in toml_text.lines() {
        let line = match raw_line.find('#') {
            Some(idx) => &raw_line[..idx],
            None => raw_line,
        }
        .trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') && !in_array {
            in_transfer = line == "[transfer]";
            continue;
        }
        if !in_transfer {
            continue;
        }
        if !in_array {
            if let Some(rest) = line.strip_prefix("exclude_patterns") {
                let rest = rest.trim_start();
                if let Some(after_eq) = rest.strip_prefix('=') {
                    let after_eq = after_eq.trim_start();
                    if let Some(after_open) = after_eq.strip_prefix('[') {
                        in_array = true;
                        if collect_quoted_strings(after_open, &mut patterns) {
                            break;
                        }
                    }
                }
            }
        } else if collect_quoted_strings(line, &mut patterns) {
            break;
        }
    }

    patterns
}

/// Extracts `"..."` literals from `segment`; returns `true` when `]` closes the array.
fn collect_quoted_strings(segment: &str, out: &mut Vec<String>) -> bool {
    let bytes = segment.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b']' => return true,
            b'"' => {
                i += 1;
                let start = i;
                while i < bytes.len() && bytes[i] != b'"' {
                    assert_ne!(
                        bytes[i], b'\\',
                        "unexpected escape in .rch/config.toml pattern literal: {segment}"
                    );
                    i += 1;
                }
                assert!(
                    i < bytes.len(),
                    "unterminated string literal in .rch/config.toml: {segment}"
                );
                out.push(segment[start..i].to_owned());
                i += 1;
            }
            _ => i += 1,
        }
    }
    false
}

fn parse_u32_key(toml_text: &str, section: &str, key: &str) -> Option<u32> {
    let mut in_section = false;
    for raw_line in toml_text.lines() {
        let line = match raw_line.find('#') {
            Some(idx) => &raw_line[..idx],
            None => raw_line,
        }
        .trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            in_section = line == section;
            continue;
        }
        if in_section
            && let Some(rest) = line.strip_prefix(key)
            && let Some(val) = rest.trim_start().strip_prefix('=')
        {
            return val.trim().parse::<u32>().ok();
        }
    }
    None
}

/// Evaluates the subset of rsync `--exclude` rules used by `.rch/config.toml` against a
/// repo-relative POSIX file path `rel_path` (no leading `/`), including every ancestor
/// directory of `rel_path` (since rsync prunes excluded directories before descending).
fn rsync_excludes_file(patterns: &[String], rel_path: &str) -> bool {
    let parts: Vec<&str> = rel_path.split('/').collect();
    // Check ancestor directories first (`dir/` rules prune the whole subtree in rsync).
    for prefix_len in 1..parts.len() {
        let dir_rel = parts[..prefix_len].join("/");
        let dir_name = parts[prefix_len - 1];
        if patterns
            .iter()
            .any(|p| rsync_pattern_matches(p, &dir_rel, dir_name, true))
        {
            return true;
        }
    }
    let file_name = parts.last().copied().unwrap_or(rel_path);
    patterns
        .iter()
        .any(|p| rsync_pattern_matches(p, rel_path, file_name, false))
}

fn rsync_pattern_matches(pattern: &str, rel_path: &str, basename: &str, is_dir: bool) -> bool {
    let (pat, dir_only) = match pattern.strip_suffix('/') {
        Some(stripped) => (stripped, true),
        None => (pattern, false),
    };
    if dir_only && !is_dir {
        return false;
    }
    if let Some(anchored) = pat.strip_prefix('/') {
        glob_match(anchored, rel_path)
    } else if pat.contains('/') {
        // In rsync, an unanchored pattern containing `/` (after stripping trailing `/`)
        // matches against the root-relative path unless it starts with `**/`.
        glob_match(pat, rel_path)
            || (!dir_only && {
                // e.g. `proofs/**` matches `crates/fln/src/runtime/proofs/foo.rs` because
                // rsync matches unanchored `proofs/**` against any suffix starting at a `/`
                // when `**` is present? Wait: in rsync filter rules:
                // "if the pattern contains a / (not counting a trailing /) or a **, then it
                // is matched against the full pathname, including any leading directories. If
                // the pattern doesn't contain a / or **, then it is matched only against the
                // final component of the filename."
                // Wait: `"proofs/"` has ONLY a trailing `/`, so `pat = "proofs"` has NO `/`
                // and NO `**`! Thus `"proofs/"` matches ANY directory named `proofs` at any
                // depth, which prunes the entire subtree!
                false
            })
    } else if pat.contains("**") {
        glob_match(pat, rel_path)
    } else {
        glob_match(pat, basename)
    }
}

fn glob_match(pat: &str, text: &str) -> bool {
    let pb = pat.as_bytes();
    let tb = text.as_bytes();
    glob_match_bytes(pb, tb)
}

fn glob_match_bytes(pat: &[u8], text: &[u8]) -> bool {
    if pat.is_empty() {
        return text.is_empty();
    }
    if pat.starts_with(b"**") {
        let rest = &pat[2..];
        if let Some(after_slash) = rest.strip_prefix(b"/")
            && glob_match_bytes(after_slash, text)
        {
            return true;
        }
        for idx in 0..=text.len() {
            if glob_match_bytes(rest, &text[idx..]) {
                return true;
            }
        }
        return false;
    }
    match pat[0] {
        b'*' => {
            for idx in 0..=text.len() {
                if idx > 0 && text[idx - 1] == b'/' {
                    break;
                }
                if glob_match_bytes(&pat[1..], &text[idx..]) {
                    return true;
                }
            }
            false
        }
        b'?' => !text.is_empty() && text[0] != b'/' && glob_match_bytes(&pat[1..], &text[1..]),
        ch => !text.is_empty() && text[0] == ch && glob_match_bytes(&pat[1..], &text[1..]),
    }
}

fn walk_crate_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("failed reading directory {}: {e}", dir.display()));
    for entry in entries {
        let path = entry
            .unwrap_or_else(|e| panic!("failed reading entry under {}: {e}", dir.display()))
            .path();
        let ft = path
            .symlink_metadata()
            .unwrap_or_else(|e| panic!("failed stating {}: {e}", path.display()))
            .file_type();
        if ft.is_dir() {
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if !SKIP_DIRS.contains(&name) && !name.starts_with(".rch-target") {
                walk_crate_rs_files(&path, out);
            }
        } else if ft.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

#[test]
fn repo_rch_config_anchors_proofs_and_artifacts_and_preserves_all_crate_sources() {
    let root = fln_conformance::checked_workspace_root!();
    let config_path = root.join(".rch/config.toml");
    let config_text = std::fs::read_to_string(&config_path)
        .unwrap_or_else(|e| panic!("missing repo RCH config {}: {e}", config_path.display()));

    for slot_key in ["build_slots", "test_slots", "check_slots"] {
        let slots = parse_u32_key(&config_text, "[compilation]", slot_key)
            .unwrap_or_else(|| panic!("[compilation].{slot_key} missing in .rch/config.toml"));
        assert!(
            (1..=2).contains(&slots),
            "[compilation].{slot_key} = {slots} exceeds 2-slot worker capacity"
        );
    }

    let patterns = parse_exclude_patterns(&config_text);
    assert!(
        patterns.len() >= 60,
        "refusing truncated exclude_patterns parse ({} entries)",
        patterns.len()
    );

    for required in REQUIRED_ANCHORED_PATTERNS {
        assert!(
            patterns.iter().any(|p| p == required),
            ".rch/config.toml must carry root-anchored pattern {required:?}"
        );
    }
    for forbidden in FORBIDDEN_UNANCHORED_PATTERNS {
        assert!(
            !patterns.iter().any(|p| p == forbidden),
            ".rch/config.toml must not carry unanchored pattern {forbidden:?} \
             (strips tracked crates/**/{forbidden} Rust modules)"
        );
    }
    for safety in REQUIRED_SAFETY_PATTERNS {
        assert!(
            patterns.iter().any(|p| p == safety),
            ".rch/config.toml dropped required safety/build exclusion {safety:?}"
        );
    }

    let mut rs_files = Vec::new();
    walk_crate_rs_files(&root.join("crates"), &mut rs_files);
    rs_files.sort();

    let mut proofs_rs = Vec::new();
    let mut artifacts_rs = Vec::new();
    let mut excluded_sources = Vec::new();
    for path in &rs_files {
        let rel = path
            .strip_prefix(&root)
            .expect("under workspace root")
            .to_string_lossy()
            .replace('\\', "/");
        if rel.split('/').any(|seg| seg == "proofs") {
            proofs_rs.push(rel.clone());
        }
        if rel.split('/').any(|seg| seg == "artifacts") {
            artifacts_rs.push(rel.clone());
        }
        if rsync_excludes_file(&patterns, &rel) {
            excluded_sources.push(rel);
        }
    }

    assert!(
        proofs_rs.len() >= 18,
        "expected >= 18 tracked Rust files under crates/**/proofs/**, found {}",
        proofs_rs.len()
    );
    assert!(
        artifacts_rs.len() >= 5,
        "expected >= 5 tracked Rust files under crates/**/artifacts/**, found {}",
        artifacts_rs.len()
    );
    assert!(
        excluded_sources.is_empty(),
        ".rch/config.toml excludes tracked crate Rust sources:\n{}",
        excluded_sources.join("\n")
    );

    // Positive controls: root-level output directories, build artifacts, and secrets stay excluded.
    for must_exclude in [
        "artifacts/summary.json",
        "proofs/certificate.bin",
        "scripts/e2e/artifacts/run.ndjson",
        "target/debug/fln",
        ".rch-target-vmi1149989-pool/debug/fln",
        ".beads/beads.db",
        ".env",
        ".env.production",
        "credentials.json",
        "id_ed25519",
    ] {
        assert!(
            rsync_excludes_file(&patterns, must_exclude),
            "expected {must_exclude:?} to be excluded by .rch/config.toml"
        );
    }
}

#[test]
fn unanchored_proofs_or_artifacts_mutants_strip_tracked_crate_modules_and_die() {
    let root = fln_conformance::checked_workspace_root!();
    let config_text =
        std::fs::read_to_string(root.join(".rch/config.toml")).expect("read .rch/config.toml");
    let baseline = parse_exclude_patterns(&config_text);

    let mut rs_files = Vec::new();
    walk_crate_rs_files(&root.join("crates"), &mut rs_files);
    let rel_files: Vec<String> = rs_files
        .iter()
        .map(|p| {
            p.strip_prefix(&root)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/")
        })
        .collect();

    // Mutant 1: regress `/proofs/` -> `proofs/` (the fleet config bug for fln-parse/fln proofs).
    let proofs_mutant: Vec<String> = baseline
        .iter()
        .map(|p| {
            if p == "/proofs/" {
                "proofs/".to_owned()
            } else {
                p.clone()
            }
        })
        .collect();
    let stripped_proofs: Vec<&String> = rel_files
        .iter()
        .filter(|rel| rsync_excludes_file(&proofs_mutant, rel))
        .collect();
    assert!(
        stripped_proofs.len() >= 18,
        "unanchored `proofs/` mutant must strip >= 18 tracked Rust files, stripped {}",
        stripped_proofs.len()
    );

    // Mutant 2: regress `/artifacts/` -> `artifacts/` (the fleet config bug for artifacts modules).
    let artifacts_mutant: Vec<String> = baseline
        .iter()
        .map(|p| {
            if p == "/artifacts/" {
                "artifacts/".to_owned()
            } else {
                p.clone()
            }
        })
        .collect();
    let stripped_artifacts: Vec<&String> = rel_files
        .iter()
        .filter(|rel| rsync_excludes_file(&artifacts_mutant, rel))
        .collect();
    assert!(
        stripped_artifacts.len() >= 5,
        "unanchored `artifacts/` mutant must strip >= 5 tracked Rust files, stripped {}",
        stripped_artifacts.len()
    );
}
