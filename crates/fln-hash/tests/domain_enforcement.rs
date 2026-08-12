//! Registry enforcement (bead franken_lean-rps, requirement a): **nothing in the
//! program hashes outside this crate.** The raw `fln_hash::blake3` surface may be
//! named only inside fln-hash itself; every other crate must go through the
//! domain registry ([`fln_hash::domain`]), which forces a registered `Domain`
//! at the type level.
//!
//! The law is enforced at two different strengths, because one of them alone is a
//! convention:
//!
//! 1. **The workspace scan** — this test IS the CI grep. It walks every workspace
//!    member's sources and fails on an unregistered hashing reference; the planted
//!    violation proves the scanner detects one. Its reach ends at our own tree.
//! 2. **The public-API proof** — fln-hash is also shipped as an embeddable library
//!    (product shape 2), and an embedder's source is not ours to scan. So the raw
//!    module is `pub(crate)` and the boundary is the compiler's: the public module
//!    surface is frozen against re-publication, and `rustc` is made to refuse an
//!    out-of-crate reference to the raw hasher with E0603. A control probe that goes
//!    through the registry compiles in the same harness, so the refusal is
//!    attributable to privacy rather than to a broken harness.

#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};

/// Whether a byte can be part of a Rust identifier.
fn is_word_byte(b: &u8) -> bool {
    b.is_ascii_alphanumeric() || *b == b'_'
}

/// The *scannable* portion of a line: everything before the first `//` that is not inside
/// a string literal, with the **contents of every string literal blanked out**.
///
/// Two evasions pull in opposite directions and this function has to survive both.
///
/// **Truncating too early.** A naive `line.find("//")` truncates at a `//` inside a
/// string — a URL literal — and hides a raw-hasher reference later on the same line. That
/// is the evasion RubyForest flagged, and it is why this walks the line instead of
/// searching it.
///
/// **Reading a mention as a use.** A string literal is *data*. No `blake3` inside one can
/// resolve to the module, because Rust has no path from a string to a symbol. The guard
/// used to scan string contents anyway, and it turned the workspace red for a table of
/// file paths in another crate — `("crates/fln-hash/src/blake3.rs", 1)` — where the needle
/// sits between `/` and `.`, so it is a whole word by every test this file applies and
/// still not a reference to anything. That is the second time this class has fired here.
/// The first was `convert_blake3_vectors.py`, repaired by requiring a whole identifier;
/// the repair was right and incomplete, because it distinguished an identifier from a
/// fragment and never asked whether the text was code. **A filesystem path segment is not
/// a Rust path segment.** Scoping the search region to the code is the narrow repair, and
/// the same one AGENTS.md prescribes for `fln-8zsq`: scope the assertion to the site that
/// must carry the evidence. An exemption list would have been the wide one — it would let
/// any file that says the word off, rather than letting no file be judged on its data.
///
/// Blanking preserves byte length, so a blanked span reads as spaces and the
/// word-boundary test in [`names_raw_hasher`] behaves exactly as it does on real code.
/// Raw strings (`r"…"`, `r#"…"#`) are matched with their own hash count rather than by
/// quote counting: a naive toggle on `r#"say "hi""#` re-enters a string at the embedded
/// quote and blanks the *rest of the line*, which would hide a genuine reference after it.
/// That is the first evasion arriving through the second repair, and
/// `a_raw_string_with_embedded_quotes_does_not_hide_a_later_reference` is the control.
/// Char literals and lifetimes are deliberately not tracked — both spell `'` and a char
/// literal cannot hold `blake3`.
fn scannable_code(line: &str) -> String {
    let bytes = line.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0usize;
    while i < bytes.len() {
        let b = bytes[i];

        // A raw-string opener: `r`, `r#`, `r##`, … then `"`, and not preceded by a word
        // byte (so a raw identifier `r#foo` and any identifier ending in `r` are not it).
        if b == b'r'
            && !i
                .checked_sub(1)
                .and_then(|p| bytes.get(p))
                .is_some_and(is_word_byte)
        {
            let mut j = i + 1;
            while bytes.get(j) == Some(&b'#') {
                j += 1;
            }
            if bytes.get(j) == Some(&b'"') {
                let hashes = j - (i + 1);
                out.extend(std::iter::repeat_n(b' ', j - i + 1));
                let mut k = j + 1;
                while k < bytes.len() {
                    if bytes[k] == b'"' && (0..hashes).all(|h| bytes.get(k + 1 + h) == Some(&b'#'))
                    {
                        out.extend(std::iter::repeat_n(b' ', hashes + 1));
                        k += hashes + 1;
                        break;
                    }
                    out.push(b' ');
                    k += 1;
                }
                i = k;
                continue;
            }
        }

        if b == b'"' {
            out.push(b' ');
            let mut k = i + 1;
            let mut escaped = false;
            while k < bytes.len() {
                let c = bytes[k];
                out.push(b' ');
                k += 1;
                if escaped {
                    escaped = false;
                } else if c == b'\\' {
                    escaped = true;
                } else if c == b'"' {
                    break;
                }
            }
            i = k;
            continue;
        }

        if b == b'/' && bytes.get(i + 1) == Some(&b'/') {
            break;
        }

        out.push(b);
        i += 1;
    }
    String::from_utf8(out).expect("blanking ASCII spans of valid UTF-8 leaves it valid")
}

/// Whether `code` names the raw hasher as a Rust identifier rather than as part of a longer
/// word.
///
/// A path segment is bounded by non-word characters on both sides: `fln_hash::blake3`,
/// `blake3::hash`, `mod blake3`, `use ...::blake3 as _` all qualify; `convert_blake3_vectors`
/// does not, because a `_` on either side makes it one longer identifier and no such
/// identifier can resolve to the module.
fn names_raw_hasher(code: &str) -> bool {
    const NEEDLE: &str = "blake3";
    let bytes = code.as_bytes();
    let mut from = 0usize;
    while let Some(offset) = code[from..].find(NEEDLE) {
        let start = from + offset;
        let end = start + NEEDLE.len();
        let before_is_word = start
            .checked_sub(1)
            .and_then(|i| bytes.get(i))
            .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_');
        let after_is_word = bytes
            .get(end)
            .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_');
        if !before_is_word && !after_is_word {
            return true;
        }
        from = end;
    }
    false
}

/// Occurrences of a raw-hashing reference in one file: (line number, line text).
fn raw_hash_references(source: &str) -> Vec<(usize, String)> {
    let mut findings = Vec::new();
    for (idx, line) in source.lines().enumerate() {
        // The raw surface is reachable only by naming the module. The domain
        // registry path (`fln_hash::domain`, `Domain::`, `DomainHasher`) is the
        // sanctioned vocabulary and never names `blake3`. Scanning the code portion
        // (comment stripped string-aware) keeps genuine comment mentions exempt while
        // never letting a string-embedded `//` hide a real reference.
        //
        // The match must be on the WHOLE identifier. A substring match also fires on
        // `convert_blake3_vectors.py` — a *filename* naming the extraction script that
        // generates our fixtures, which is not a reference to the hasher at all. That
        // false positive turned the workspace red for everyone, and loosening the guard
        // to an exemption list would have been the wrong repair: the reference we are
        // hunting is always a path segment, so requiring a path segment is both narrower
        // and strictly more accurate than listing the files allowed to say the word.
        if names_raw_hasher(&scannable_code(line)) {
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

/// The scanner's own predicate, including the false positive that made this test fail and
/// the blind spot the narrowing leaves behind.
///
/// The blind spot is asserted rather than hidden: a name like `blake3_hash` would not be
/// caught by this text scan. That is acceptable *because this scan is the backstop, not the
/// enforcement* — `blake3` is `pub(crate)`, so no such path compiles out of crate, and
/// `rustc_refuses_an_out_of_crate_reference_to_the_raw_hasher` is what proves it. The text
/// scan exists to catch the day someone widens that visibility. Recording the limit here
/// keeps the two guards' division of labour explicit instead of implying this one is total.
#[test]
fn the_scanner_matches_a_path_segment_not_any_word_containing_it() {
    // Real references, all of them path segments.
    assert!(names_raw_hasher("use fln_hash::blake3;"));
    assert!(names_raw_hasher("    let h = blake3::hash(b\"x\");"));
    assert!(names_raw_hasher("pub(crate) mod blake3;"));
    assert!(names_raw_hasher("fln_hash::blake3::Hasher::new()"));

    // The false positive that turned the workspace red: a filename, not a reference.
    assert!(!names_raw_hasher(
        "\"scripts/extract/convert_blake3_vectors.py\","
    ));
    assert!(!names_raw_hasher("let convert_blake3_vectors = 1;"));

    // The recorded blind spot, and why it is tolerable — see this test's doc comment.
    assert!(
        !names_raw_hasher("blake3_hash(b\"x\")"),
        "a trailing word character is out of this scan's reach; the compile probe covers it"
    );

    assert!(!names_raw_hasher("DomainHasher::new(Domain::Fixture)"));
    assert!(!names_raw_hasher(""));
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

    // Bypass regression (RubyForest): a string literal containing `//` must NOT hide
    // a raw-hasher reference later on the same line. A naive first-`//` strip would
    // truncate at the URL's `//` and miss the `blake3` use.
    let bypass = "let _u = \"http://example\"; use fln_hash::blake3::hash;\n";
    assert_eq!(
        raw_hash_references(bypass).len(),
        1,
        "a `//` inside a string must not hide a raw-hasher reference"
    );
    // A blake3 mention that really is only in a trailing comment stays exempt even
    // when a string precedes it.
    assert!(raw_hash_references("let _u = \"ok\"; // blake3 note\n").is_empty());
}

/// A file path inside a string literal is data, not a reference.
///
/// The live instance: `crates/fln-conformance/src/tree_identity.rs` declares its
/// per-file residue as a table of `(path, count)` pairs, one of which names
/// `crates/fln-hash/src/blake3.rs`. The needle sits between `/` and `.`, so it is a
/// whole identifier by every test this file applies — and it is still a filesystem
/// path in a data table, reachable from nothing. It failed `check.sh` at stage 8 on
/// 2026-07-27 (`target/check/check-20260727T044815Z-2738056`).
#[test]
fn a_path_in_a_string_literal_is_not_a_raw_hasher_reference() {
    assert!(raw_hash_references("    (\"crates/fln-hash/src/blake3.rs\", 1),\n").is_empty());
    assert!(raw_hash_references("let p = \"src/blake3.rs\";\n").is_empty());
    assert!(raw_hash_references("expect(\"blake3 fixture missing\")\n").is_empty());
    // A raw string is data too.
    assert!(raw_hash_references("let p = r\"crates/fln-hash/src/blake3.rs\";\n").is_empty());
}

/// **The anti-widening control.** Every assertion above removes findings, so on its own
/// it cannot tell a narrowed guard from a broken one. A genuine reference must still be
/// refused *while sharing its line with a string that mentions the needle* — which is
/// only true if string CONTENTS are blanked rather than lines containing strings skipped.
#[test]
fn a_real_reference_is_still_refused_when_a_string_on_the_same_line_mentions_it() {
    let mixed = "let _ = fln_hash::blake3::hash(\"crates/fln-hash/src/blake3.rs\");\n";
    assert_eq!(
        raw_hash_references(mixed).len(),
        1,
        "blanking a string must not blank the code beside it"
    );
    let after = "let _p = \"blake3.rs\"; use fln_hash::blake3::Hasher;\n";
    assert_eq!(raw_hash_references(after).len(), 1);
    let before = "use fln_hash::blake3::Hasher; let _p = \"blake3.rs\";\n";
    assert_eq!(raw_hash_references(before).len(), 1);
}

/// The first evasion arriving through the second repair.
///
/// Quote-counting re-enters a string at the embedded `"` of `r#"say "hi""#`, and from
/// there blanks the rest of the line — hiding a real reference behind a raw string. The
/// hash count is what distinguishes the terminator from a quote inside the body.
#[test]
fn a_raw_string_with_embedded_quotes_does_not_hide_a_later_reference() {
    let evasion = "let _a = r#\"say \"hi\"\"#; use fln_hash::blake3::Hasher;\n";
    assert_eq!(
        raw_hash_references(evasion).len(),
        1,
        "a raw string's embedded quote must not swallow the code after it"
    );
    // And the raw string's own body is still data.
    assert!(raw_hash_references("let _a = r#\"blake3 \"x\"\"#;\n").is_empty());
    // An escaped quote inside an ordinary string must not end it early either.
    assert!(raw_hash_references("let _a = \"say \\\"blake3\\\"\";\n").is_empty());
}

/// Blanking preserves byte length, so the word-boundary test sees the same shape it
/// would see on code. A span that collapsed would let two identifiers become adjacent
/// and change a verdict.
#[test]
fn blanking_a_string_preserves_the_length_of_the_line() {
    let line = "let p = \"crates/fln-hash/src/blake3.rs\"; // note";
    let code = scannable_code(line);
    assert_eq!(code.len(), line.find("//").expect("has a comment"));
    assert!(!code.contains("blake3"), "{code:?}");
    assert!(code.starts_with("let p = "), "{code:?}");
}

// ---------------------------------------------------------------------------
// The public-API proof — the half the workspace scan structurally cannot do.
// ---------------------------------------------------------------------------

/// The frozen public module surface of fln-hash. `blake3` is deliberately absent:
/// publishing it would hand every external consumer an unregistered hash and reduce
/// the registry to a naming convention. Adding a module here is a reviewed act.
// `cartridge`, `certificate`, `product`, and `shadow` are reviewed candidate/codec surfaces.
// They hash only through the public domain registry and do not re-export or name the
// crate-private BLAKE3 core.
const PUBLIC_MODULES: [&str; 7] = [
    "canon",
    "cartridge",
    "certificate",
    "domain",
    "product",
    "root",
    "shadow",
];

/// The modules a crate root declares, each paired with whether it is reachable from
/// *outside* the crate. Only `pub mod` is: `pub(crate)`, `pub(super)`, and
/// `pub(in …)` all stop at the crate boundary, and a bare `mod` is private.
fn declared_modules(lib_source: &str) -> Vec<(String, bool)> {
    let mut modules = Vec::new();
    for line in lib_source.lines() {
        let code = scannable_code(line);
        let code = code.trim();
        // Only plain `… mod name;` declarations. An inline `mod name { … }` block and
        // a `pub use` re-export are not the crate's module-surface statement.
        let Some(head) = code.strip_suffix(';') else {
            continue;
        };
        let Some((prefix, name)) = head
            .rsplit_once(" mod ")
            .or_else(|| head.strip_prefix("mod ").map(|name| ("", name)))
        else {
            continue;
        };
        let name = name.trim();
        if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            continue;
        }
        modules.push((name.to_string(), prefix.trim() == "pub"));
    }
    modules
}

#[test]
fn the_public_module_surface_is_frozen_and_excludes_the_raw_hasher() {
    let lib = workspace_root().join("crates/fln-hash/src/lib.rs");
    let source = fs::read_to_string(&lib).expect("fln-hash lib.rs is readable");
    let modules = declared_modules(&source);
    assert!(
        !modules.is_empty(),
        "the module-surface parser found nothing in {} — wrong path or grammar drift",
        lib.display()
    );

    let mut public: Vec<&str> = modules
        .iter()
        .filter(|(_, external)| *external)
        .map(|(name, _)| name.as_str())
        .collect();
    public.sort_unstable();
    assert_eq!(
        public, PUBLIC_MODULES,
        "fln-hash's public module surface changed. Every module here is reachable by \
         any external embedder; if the new one can hash, the domain registry is no \
         longer enforced by the compiler. Update PUBLIC_MODULES only as a reviewed act."
    );

    let (_, raw_is_public) = modules
        .iter()
        .find(|(name, _)| name == "blake3")
        .expect("fln-hash still declares its raw BLAKE3 module");
    assert!(
        !raw_is_public,
        "`blake3` is public again — an external embedder can now hash without naming a \
         registered domain, which is exactly the law this crate exists to enforce"
    );
}

#[test]
fn the_surface_parser_tells_pub_from_crate_internal_visibility() {
    // The plant this guard exists for: re-publishing the raw hasher.
    assert_eq!(
        declared_modules("pub mod blake3;\n"),
        vec![("blake3".to_string(), true)]
    );
    // The shipped form, and every other spelling that stops at the crate boundary.
    for internal in [
        "pub(crate) mod blake3;",
        "pub(super) mod blake3;",
        "pub(in crate::inner) mod blake3;",
        "mod blake3;",
    ] {
        assert_eq!(
            declared_modules(internal),
            vec![("blake3".to_string(), false)],
            "{internal} is not an external surface"
        );
    }
    // Things that look close but are not module declarations. A `pub use` re-export of
    // a private module's contents would be a real bypass, but it is a *name* export
    // rather than a module declaration — the workspace scan and the rustc probe below
    // are what cover it, so the parser must not silently claim it did.
    assert!(declared_modules("pub use crate::blake3::Hasher;\n").is_empty());
    assert!(declared_modules("// pub mod blake3;\n").is_empty());
    assert!(declared_modules("pub mod inline { }\n").is_empty());
}

/// `<target>/<profile>/deps` — where cargo placed this test binary and the rlibs it
/// links against.
fn deps_dir() -> Option<PathBuf> {
    let exe = std::env::current_exe().ok()?;
    let dir = exe.parent()?;
    (dir.file_name()? == "deps").then(|| dir.to_path_buf())
}

/// Candidate `fln-hash` rlibs, newest first — a stale build can leave more than one.
fn fln_hash_rlibs(deps: &Path) -> Vec<PathBuf> {
    let mut found: Vec<(std::time::SystemTime, PathBuf)> = Vec::new();
    for entry in fs::read_dir(deps).into_iter().flatten().flatten() {
        let path = entry.path();
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if name.starts_with("libfln_hash-") && name.ends_with(".rlib") {
            let stamp = entry
                .metadata()
                .and_then(|m| m.modified())
                .unwrap_or(std::time::UNIX_EPOCH);
            found.push((stamp, path));
        }
    }
    found.sort_by_key(|(stamp, _)| std::cmp::Reverse(*stamp));
    found.into_iter().map(|(_, path)| path).collect()
}

/// Compile one probe source as a separate crate linked against the real fln-hash
/// rlib. Metadata-only: name resolution and type checking run, codegen does not.
fn compile_probe(
    rlib: &Path,
    deps: &Path,
    source: &Path,
    out: &Path,
) -> std::io::Result<std::process::Output> {
    std::process::Command::new("rustc")
        .arg("--edition=2024")
        .arg("--crate-type=lib")
        .arg("--crate-name=fln_hash_public_api_probe")
        .arg("--emit=metadata")
        .arg("-o")
        .arg(out)
        .arg("-L")
        .arg(format!("dependency={}", deps.display()))
        .arg("--extern")
        .arg(format!("fln_hash={}", rlib.display()))
        .arg(source)
        .output()
}

#[test]
fn rustc_refuses_an_out_of_crate_reference_to_the_raw_hasher() {
    // The registry path, from a crate that is not fln-hash. This MUST compile: it is
    // both the sanctioned way to hash and the harness's own control.
    const CONTROL: &str = "\
pub fn registered() -> String {
    fln_hash::domain::hash(fln_hash::domain::Domain::DeclContent, b\"probe\").to_hex()
}
";
    // Both spellings of the raw surface. Each body is otherwise valid code — it would
    // compile if the module were public — so the only thing left to refuse it is
    // privacy.
    const VIOLATIONS: [(&str, &str); 2] = [
        (
            "one_shot",
            "pub fn v() -> [u8; 32] { fln_hash::blake3::hash(b\"probe\") }\n",
        ),
        (
            "incremental",
            "\
pub fn v() -> [u8; 32] {
    let mut hasher = fln_hash::blake3::Hasher::new();
    hasher.update(b\"probe\");
    hasher.finalize()
}
",
        ),
    ];

    // Everything below can fail for reasons that are about the harness rather than
    // about the boundary (no deps dir, no rlib, no rustc). Those SKIP typed and say
    // why: an unattributable failure is not evidence, and it must not be laundered
    // into either a pass or a red workspace. A control that compiles while a
    // violation also compiles is the one outcome that is genuinely a regression.
    let Some(deps) = deps_dir() else {
        println!(
            "SKIP: no cargo deps directory beside the test binary ({:?})",
            std::env::current_exe()
        );
        return;
    };
    let scratch = deps.join(format!("fln-hash-public-api-probe-{}", std::process::id()));
    if let Err(error) = fs::create_dir_all(&scratch) {
        println!("SKIP: cannot create the probe scratch dir {scratch:?}: {error}");
        return;
    }

    let control_src = scratch.join("control.rs");
    if let Err(error) = fs::write(&control_src, CONTROL) {
        println!("SKIP: cannot write the control probe: {error}");
        return;
    }
    let mut usable = None;
    let mut last_stderr = String::new();
    for rlib in fln_hash_rlibs(&deps) {
        match compile_probe(&rlib, &deps, &control_src, &scratch.join("control.meta")) {
            Ok(output) if output.status.success() => {
                usable = Some(rlib);
                break;
            }
            Ok(output) => last_stderr = String::from_utf8_lossy(&output.stderr).into_owned(),
            Err(error) => {
                println!("SKIP: cannot run rustc for the probe: {error}");
                return;
            }
        }
    }
    let Some(rlib) = usable else {
        println!(
            "SKIP: no fln-hash rlib under {} compiles the control probe, so a failure on \
             the violation could not be attributed to privacy. Last rustc stderr:\n{last_stderr}",
            deps.display()
        );
        return;
    };

    for (label, source) in VIOLATIONS {
        let probe = scratch.join(format!("violation_{label}.rs"));
        fs::write(&probe, source).expect("the scratch dir already took the control probe");
        let output = compile_probe(
            &rlib,
            &deps,
            &probe,
            &scratch.join(format!("violation_{label}.meta")),
        )
        .expect("rustc already ran for the control");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "an out-of-crate crate compiled the `{label}` reference to fln_hash::blake3. \
             The raw hasher is reachable by any embedder again, so domain separation is \
             back to being a convention policed by a grep over our own tree."
        );
        assert!(
            stderr.contains("E0603"),
            "the `{label}` probe failed, but not with the private-module error E0603, so \
             this run proves nothing about privacy:\n{stderr}"
        );
        assert!(
            stderr.contains("blake3"),
            "the `{label}` probe's E0603 does not name `blake3` — it is refusing \
             something else:\n{stderr}"
        );
    }
}
