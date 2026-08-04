//! **Identity must be taken from the encoding, never the rendering** — as a mechanism.
//!
//! A rendering is lossy by design: it exists to be read by a human, and it is free to change
//! for that reason alone. A digest preimage is the opposite: it is the identity of a value, and
//! two distinct values that produce the same preimage are one value as far as every consumer
//! downstream is concerned. Feeding one into the other is a defect this program has now found
//! **six times, in four subsystems, every single time by somebody reading carefully**:
//!
//! | instance | the rendering that stood in for an encoding |
//! |---|---|
//! | `franken_lean-f6br` | the kernel-admission census witness keyed on `Name::to_display_string` |
//! | `bf9ef450` | the term-store intern key's five `Name` sites, same encoding |
//! | `franken_lean-oof9` | a lint pattern keyed on a method *name*, which does not separate two methods |
//! | `franken_lean-hv9m` | the intern key's `Sort` level, `Const` level list and `FVar`/`MVar` id sites |
//! | `franken_lean-oh1j` (5th) | the intern key's `MData` payload — the *same* `Name` type, encoded two ways in one function |
//! | `franken_lean-oh1j` (6th) | the intern key's `Lit` payload |
//!
//! Six found by reading is not a mechanism; it is luck with good people, and luck does not
//! survive a context restart. This file is the mechanism. It is a **source-reading guard**: it
//! walks every workspace member's production sources and refuses any statement that feeds a
//! rendered value into a digest preimage.
//!
//! # Why a source guard and not a type-level one
//!
//! The sound fix — a `Preimage` newtype that only canonical encoders can construct — is the
//! right long-term answer and is not this file's to build: the hashers live in `fln-hash`, the
//! preimages are built in a dozen crates, and a type that crosses all of them is an API change
//! across the workspace. A source guard buys the *falsification* property today at a fraction of
//! the cost, and it keeps buying it after the newtype lands.
//!
//! # What this guard deliberately does NOT claim
//!
//! It does not claim every digest preimage is canonical — only that none is built from the four
//! rendering forms below. A preimage assembled by hand from raw bytes without length prefixes is
//! just as non-injective (that is `fln-extension-history-checkpoint-identity-41s`'s rule, and it
//! is a *serialisation* rule this scanner cannot decide). Two rules, one family, and the general
//! form recorded on `ccde957f` covers both: **any projection used as an identity must be
//! injective over the values that must be told apart.**
//!
//! Bead `franken_lean-oh1j`.

#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};

use fln_conformance::pin::workspace_root;

/// Calls that build a digest preimage. Every one of these consumes bytes that stand for a
/// value's identity.
///
/// `.update(` is the broad one, and it was measured before being relied on rather than assumed
/// safe: every `.update(` receiver in workspace production code is a hasher (`hasher`, `h`,
/// `context_hasher`, `self.inner`, `self.chunk_state`). If a non-hashing `update` ever appears
/// and takes a rendered string, this guard fires — loudly, on a clean tree, which is the correct
/// direction for a check that cannot decide.
const DIGEST_SINKS: &[&str] = &[
    ".update(",
    "write_body",
    "DomainHasher",
    "CanonWriter",
    "hasher.",
];

/// Turning a value into text *for a reader*.
///
/// `.to_string()` and `.to_owned()` are here despite never having produced one of the six: the
/// family is about the shape, not about the four spellings that happened to occur, and all six
/// historical instances used only the first three. Including them costs nothing — the workspace
/// scans clean at this width — and it closes the two spellings a seventh would most naturally
/// reach for.
const RENDERINGS: &[&str] = &[
    "format!",
    ":?}",
    "to_display_string",
    ".to_string()",
    ".to_owned()",
];

/// One statement of source: the line it starts on, and its text with line breaks collapsed.
///
/// Statement-level rather than line-window, because a window of N lines is a guess that is wrong
/// in both directions — it misses `hasher.update(` and its argument N+1 lines apart, and it
/// reports two unrelated neighbours as one site. A statement is the unit the defect actually
/// lives in.
struct Statement {
    line: usize,
    text: String,
}

/// Collapse source into statements, dropping whole-line comments.
///
/// Whole-line comments must go: this crate's own prose quotes `format!("{:?}")` next to the word
/// `hasher` constantly — the doc comments on `update_name`, `update_level`, `update_kvmap` and
/// `update_literal_leaf` in `fln-env`'s interner exist precisely to explain this defect — and a
/// scanner that reads them reports the explanation as the crime.
///
/// A *trailing* comment on a code line is deliberately left in scope. Stripping it correctly
/// needs a string-literal-aware scan (a `//` inside `"https://…"` is not a comment), and getting
/// that subtly wrong produces silent **false negatives**, which is the one failure mode a guard
/// must not have. Left in, the worst case is a loud false positive on a comment that names both
/// a sink and a rendering on one line, fixed by moving the comment to its own line.
fn statements(source: &str) -> Vec<Statement> {
    let mut out = Vec::new();
    let mut buffer = String::new();
    let mut start = 0usize;
    for (index, raw) in source.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty()
            || line.starts_with("//")
            || line.starts_with('*')
            || line.starts_with("/*")
        {
            continue;
        }
        if buffer.is_empty() {
            start = index + 1;
        } else {
            buffer.push(' ');
        }
        buffer.push_str(line);
        if line.ends_with(';') || line.ends_with('{') || line.ends_with('}') {
            out.push(Statement {
                line: start,
                text: std::mem::take(&mut buffer),
            });
        }
    }
    if !buffer.is_empty() {
        out.push(Statement {
            line: start,
            text: buffer,
        });
    }
    out
}

/// Blank out `#[cfg(test)]` items by brace counting, so planted mutants are out of scope.
///
/// This project kills defects by planting them, and the natural mutant for *this* defect is
/// written in exactly the shape this guard refuses. `fln-env`'s interner already carries four
/// named mutants; a fifth spelled `hasher.update(format!("{x:?}").as_bytes())` would redden the
/// workspace for every pane while being exactly correct as a mutant.
///
/// The trap in a brace-counting exclusion is that it over-strips **silently**: `mod tests` is
/// conventionally last in a Rust file, so a runaway count blanks the tail of the file and every
/// production site after it, and the guard still reports a clean tree. That is why
/// [`production_code_after_a_cfg_test_module_stays_in_scope`] exists and why it puts the
/// violation *after* the excluded module.
///
/// Braces are counted **textually**, so a brace inside a string literal (`format!("{{")` is the
/// realistic one) unbalances the count and the region runs to end of file. Rather than teach the
/// scanner to parse Rust strings — a second place to be subtly wrong, in the direction of silent
/// false negatives — the region is additionally bounded by a `}` alone at column zero. That is
/// not a guess about formatting: `cargo fmt --check` is stage one of `scripts/check.sh`, so a
/// top-level item closing at column zero is an invariant this repository enforces on every
/// commit. The region ends at whichever bound comes first.
fn strip_cfg_test_items(source: &str) -> String {
    let lines: Vec<&str> = source.lines().collect();
    let mut kept: Vec<String> = lines.iter().map(|line| (*line).to_string()).collect();
    let mut index = 0usize;
    while index < lines.len() {
        if !lines[index].contains("#[cfg(test)]") {
            index += 1;
            continue;
        }
        let mut depth: i64 = 0;
        let mut opened = false;
        let mut cursor = index;
        while cursor < lines.len() {
            let line = lines[cursor];
            depth += line.matches('{').count() as i64;
            depth -= line.matches('}').count() as i64;
            if line.contains('{') {
                opened = true;
            }
            kept[cursor] = String::new();
            // Balanced: the item closed.
            if opened && depth <= 0 {
                break;
            }
            // A top-level item closes at column zero — the rustfmt bound above.
            if opened && line == "}" {
                break;
            }
            // An attribute on a brace-less item (`#[cfg(test)] use super::*;`) ends at its
            // semicolon. Without this, such an attribute would blank the rest of the file.
            if !opened && line.trim_end().ends_with(';') {
                break;
            }
            cursor += 1;
        }
        index = cursor + 1;
    }
    kept.join("\n")
}

/// Every statement in `source` that feeds a rendering into a digest preimage.
///
/// Pure over a `&str` on purpose: the controls below hand it fixtures, so the scanner that runs
/// against the workspace is byte-for-byte the scanner the controls validate. A guard whose real
/// path and whose tested path are two different code paths has tested the wrong one.
fn violations(source: &str) -> Vec<Statement> {
    statements(&strip_cfg_test_items(source))
        .into_iter()
        .filter(|statement| {
            DIGEST_SINKS
                .iter()
                .any(|sink| statement.text.contains(sink))
                && RENDERINGS
                    .iter()
                    .any(|render| statement.text.contains(render))
        })
        .collect()
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
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

/// The workspace member directories, **derived** from the root manifest's `members` list.
///
/// Derived rather than listed, and that is not tidiness: a hand-written scope rots silently and
/// takes the claim down with it. `tools/*` members compile Rust too, and a list written when the
/// workspace was `crates/*` would exclude them while still reporting a clean scan.
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
                let mut globbed: Vec<PathBuf> = entries
                    .flatten()
                    .map(|e| e.path())
                    .filter(|p| p.is_dir())
                    .collect();
                globbed.sort();
                dirs.extend(globbed);
            }
        } else {
            let path = workspace.join(pattern);
            if path.is_dir() {
                dirs.push(path);
            }
        }
    }
    dirs.sort();
    dirs
}

/// Production sources only: `src/**` and `build.rs`.
///
/// `tests/`, `benches/` and `examples/` are excluded by the same reasoning as `#[cfg(test)]`:
/// they hold planted mutants and fixtures, and a fixture that is deliberately non-injective is
/// evidence, not a defect. The claim this guard makes is about preimages that reach an artifact.
fn production_sources(member_dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect_rs_files(&member_dir.join("src"), &mut files);
    let build_rs = member_dir.join("build.rs");
    if build_rs.exists() {
        files.push(build_rs);
    }
    files
}

#[test]
fn no_production_digest_preimage_is_built_from_a_rendering() {
    let workspace = workspace_root();
    let mut findings = Vec::new();
    let mut scanned = 0usize;
    for member_dir in workspace_member_dirs(&workspace) {
        for file in production_sources(&member_dir) {
            scanned += 1;
            let source = fs::read_to_string(&file).expect("readable source");
            for statement in violations(&source) {
                findings.push(format!(
                    "{}:{}: {}",
                    file.strip_prefix(&workspace)
                        .unwrap_or(file.as_path())
                        .display(),
                    statement.line,
                    statement.text
                ));
            }
        }
    }
    assert!(
        scanned > 0,
        "the scanner found no production sources — wrong workspace root?"
    );
    assert!(
        findings.is_empty(),
        "a digest preimage is built from a RENDERING, which is lossy by design. Feed the value's \
         canonical encoding instead (see `fln-env`'s `update_name`/`update_level`/`update_kvmap` \
         for the shape: length prefix, then the encoded bytes).\n{}",
        findings.join("\n")
    );
}

/// The scope is derived from the manifest and reaches past `crates/`.
#[test]
fn the_scan_scope_is_derived_and_covers_every_workspace_member() {
    let workspace = workspace_root();
    let members = workspace_member_dirs(&workspace);
    assert!(
        members.len() > 20,
        "workspace member derivation looks wrong: {members:?}"
    );
    let tools_root = workspace.join("tools");
    assert!(
        members.iter().any(|member| member.starts_with(&tools_root)),
        "members must include tools/ — a scope that stops at crates/ silently under-claims: \
         {members:?}"
    );
    let scanned: usize = members.iter().map(|m| production_sources(m).len()).sum();
    assert!(
        scanned > 100,
        "expected the whole workspace in scope, got {scanned} files"
    );
}

/// **The positive control**: every one of the six historical instances, in the spelling it had
/// when it was live, must be found.
///
/// Taken verbatim from the pre-fix sources (`26bacb3e^` and `bf9ef450^` for the interner sites,
/// and the census witness's `to_display_string` shape). A guard that cannot find the defects that
/// motivated it is a guard that will report a clean tree forever.
#[test]
fn the_scanner_finds_every_historical_instance() {
    let historical = r#"
fn identity_digest(expr: &Expr) -> Digest {
    let mut hasher = DomainHasher::new(Domain::DeclContent);
    hasher.update(format!("{id:?}").as_bytes());
    hasher.update(format!("{level:?}").as_bytes());
    hasher.update(name.to_display_string().as_bytes());
    hasher.update(binder_name.to_display_string().as_bytes());
    hasher.update(decl_name.to_display_string().as_bytes());
    hasher.update(struct_name.to_display_string().as_bytes());
    hasher.update(format!("{literal:?}").as_bytes());
    hasher.update(format!("{data:?}").as_bytes());
    hasher.finalize()
}
"#;
    let found = violations(historical);
    assert_eq!(
        found.len(),
        8,
        "every historical site must be found, got: {:?}",
        found.iter().map(|s| &s.text).collect::<Vec<_>>()
    );
}

/// The defect split across lines is the same defect.
#[test]
fn the_scanner_finds_a_violation_split_across_lines() {
    let split = r#"
fn preimage(hasher: &mut DomainHasher, name: &Name) {
    hasher.update(
        name
            .to_display_string()
            .as_bytes(),
    );
}
"#;
    assert_eq!(
        violations(split).len(),
        1,
        "a multi-line statement is one statement"
    );
}

/// **The negative control that matters most**: the canonical encoders must not be reported.
///
/// This is the shape the repair produced, copied from `fln-env`'s interner. A guard that fires on
/// the fix is worse than no guard: it teaches the next author that the correct code is wrong.
#[test]
fn the_scanner_accepts_the_canonical_encoders() {
    let repaired = r#"
fn update_name(hasher: &mut DomainHasher, name: &Name) {
    let encoded = canonical_name_bytes(name);
    hasher.update(&(encoded.len() as u64).to_le_bytes());
    hasher.update(&encoded);
}
fn update_level(hasher: &mut DomainHasher, level: &Level) {
    let mut writer = CanonWriter::new();
    level.write_body(&mut writer);
    let encoded = writer.into_bytes();
    hasher.update(&(encoded.len() as u64).to_le_bytes());
    hasher.update(&encoded);
}
"#;
    let found = violations(repaired);
    assert!(
        found.is_empty(),
        "the canonical encoders are the FIX and must never be reported: {:?}",
        found.iter().map(|s| &s.text).collect::<Vec<_>>()
    );
}

/// A planted mutant is deliberately wrong code and must be out of scope.
#[test]
fn a_planted_mutant_in_cfg_test_is_not_a_finding() {
    let with_mutant = r#"
fn update_name(hasher: &mut DomainHasher, name: &Name) {
    let encoded = canonical_name_bytes(name);
    hasher.update(&encoded);
}
#[cfg(test)]
mod tests {
    use super::*;
    fn mutant_overmerge(hasher: &mut DomainHasher, name: &Name) {
        hasher.update(format!("{name:?}").as_bytes());
    }
}
"#;
    let found = violations(with_mutant);
    assert!(
        found.is_empty(),
        "a mutant is evidence, not a defect: {:?}",
        found.iter().map(|s| &s.text).collect::<Vec<_>>()
    );
}

/// **The over-strip trap.** A brace-counting exclusion that runs away blanks the rest of the
/// file, and because `mod tests` is conventionally last, the guard would report a clean tree
/// forever while seeing nothing. The violation here sits *after* the excluded module, so an
/// exclusion that does not stop is caught rather than rewarded.
#[test]
fn production_code_after_a_cfg_test_module_stays_in_scope() {
    let trailing = r#"
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn nested_braces() {
        let closure = || { let inner = || { 1 }; inner() };
        assert_eq!(closure(), 1);
    }
}
fn later_production_site(hasher: &mut DomainHasher, name: &Name) {
    hasher.update(name.to_display_string().as_bytes());
}
"#;
    let found = violations(trailing);
    assert_eq!(
        found.len(),
        1,
        "code after an excluded module must still be scanned, got: {:?}",
        found.iter().map(|s| &s.text).collect::<Vec<_>>()
    );
}

/// A brace inside a string literal must not carry the exclusion off the end of the file.
///
/// `format!("{{")` is textually unbalanced, so the brace count alone never returns to zero. The
/// column-zero bound is what stops it, and the violation after the module is what proves the stop
/// happened. Without the bound this fixture reports zero findings — a clean tree that saw nothing.
#[test]
fn an_unbalanced_brace_in_a_test_string_does_not_swallow_the_rest_of_the_file() {
    let unbalanced = r#"
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn braces_in_a_literal() {
        assert_eq!(format!("{{"), "{");
    }
}
fn later_production_site(hasher: &mut DomainHasher, name: &Name) {
    hasher.update(name.to_display_string().as_bytes());
}
"#;
    let found = violations(unbalanced);
    assert_eq!(
        found.len(),
        1,
        "an unbalanced literal must not blank the tail of the file, got: {:?}",
        found.iter().map(|s| &s.text).collect::<Vec<_>>()
    );
}

/// `#[cfg(test)]` on a brace-less item ends at its semicolon, not at the end of the file.
#[test]
fn a_brace_less_cfg_test_attribute_ends_at_its_semicolon() {
    let braceless = r#"
#[cfg(test)]
use std::collections::BTreeMap;
fn later_production_site(hasher: &mut DomainHasher, name: &Name) {
    hasher.update(name.to_display_string().as_bytes());
}
"#;
    let found = violations(braceless);
    assert_eq!(
        found.len(),
        1,
        "a brace-less cfg(test) item must not blank what follows it, got: {:?}",
        found.iter().map(|s| &s.text).collect::<Vec<_>>()
    );
}

/// Prose about the defect is not the defect — including this file's own prose and `fln-env`'s.
#[test]
fn documentation_that_describes_the_defect_is_not_a_finding() {
    let documented = r#"
/// Not `to_display_string`: `hasher.update(format!("{:?}"))` is the defect this exists to avoid.
// hasher.update(format!("{name:?}").as_bytes());
fn update_name(hasher: &mut DomainHasher, name: &Name) {
    hasher.update(&canonical_name_bytes(name));
}
"#;
    let found = violations(documented);
    assert!(
        found.is_empty(),
        "explaining the defect must not be reported as committing it: {:?}",
        found.iter().map(|s| &s.text).collect::<Vec<_>>()
    );
}
