//! Seeded-violation tests (bead fln-8mj acceptance): each structural CI check must
//! demonstrably fail on a synthetic workspace carrying exactly the defect it exists to
//! catch, and pass once the defect is repaired. These are the permanent, in-tree form
//! of "add a test-only violation in CI to prove detection, then remove".

#![forbid(unsafe_code)]

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use structure_guard::checks::{self, RunOutcome};

/// An immutable workspace recipe. Every execution materializes a fresh, uniquely named
/// root and retains it for inspection, as required by the repository's no-deletion rule.
struct TempWs {
    tag: String,
    files: RefCell<BTreeMap<String, String>>,
}

impl TempWs {
    fn new(tag: &str) -> TempWs {
        TempWs {
            tag: tag.to_string(),
            files: RefCell::new(BTreeMap::new()),
        }
    }

    fn write(&self, rel: &str, content: &str) {
        self.files
            .borrow_mut()
            .insert(rel.to_string(), content.to_string());
    }

    fn materialize(&self) -> Result<PathBuf, String> {
        static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| format!("system clock precedes Unix epoch: {error}"))?
            .as_nanos();
        let root = loop {
            let sequence = NEXT_ROOT.fetch_add(1, Ordering::Relaxed);
            let candidate = std::env::temp_dir().join(format!(
                "structure-guard-test-{}-{stamp}-{sequence}-{}",
                std::process::id(),
                self.tag
            ));
            match fs::create_dir(&candidate) {
                Ok(()) => break candidate,
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(format!("create retained fixture root: {error}")),
            }
        };

        for (rel, content) in self.files.borrow().iter() {
            let path = root.join(rel);
            let parent = path
                .parent()
                .ok_or_else(|| format!("fixture path has no parent: {rel}"))?;
            fs::create_dir_all(parent)
                .map_err(|error| format!("create fixture directories for {rel}: {error}"))?;
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)
                .map_err(|error| format!("create fixture file {rel} without overwrite: {error}"))?;
            file.write_all(content.as_bytes())
                .map_err(|error| format!("write fixture file {rel}: {error}"))?;
        }
        eprintln!("retained structure-guard fixture: {}", root.display());
        Ok(root)
    }

    fn run(&self) -> RunOutcome {
        let root = self.materialize().expect("materialize retained fixture");
        checks::run(&root).expect("guard runs")
    }
}

const BASE_GRAPH: &str = "\
schema fln-workspace-graph/1
crate fln-core       rank=0  kind=ordinary
crate fln-hash       rank=1  kind=ordinary
crate fln-bignum     rank=1  kind=ordinary
crate fln-libm       rank=1  kind=ordinary
crate fln-unsafe-abi rank=2  kind=unsafe-boundary
crate fln-unsafe-region rank=2 kind=unsafe-boundary
crate fln-rt         rank=3  kind=ordinary
crate fln-env        rank=4  kind=ordinary
crate fln-olean      rank=5  kind=ordinary
crate fln-kernel     rank=6  kind=ordinary
crate fln-checker    rank=6  kind=ordinary
crate fln-syntax     rank=7  kind=ordinary
crate fln-parse      rank=8  kind=ordinary
crate fln-mid        rank=8  kind=ordinary
crate fln-elab       rank=9  kind=ordinary
crate fln-comp       rank=10 kind=ordinary
crate fln-vm         rank=11 kind=ordinary
crate fln-unsafe-jit rank=12 kind=unsafe-boundary
crate fln-verdict    rank=13 kind=ordinary
crate fln-anvil      rank=14 kind=ordinary
crate fln-ledger     rank=15 kind=ordinary
crate fln-lake       rank=16 kind=ordinary
crate fln-server     rank=17 kind=ordinary
crate fln-trace      rank=18 kind=ordinary
crate fln            rank=19 kind=ordinary
crate fln-hound      rank=20 kind=ordinary
crate fln-doc        rank=20 kind=ordinary
crate fln-mcp        rank=20 kind=ordinary
crate fln-tui        rank=20 kind=ordinary
crate fln-cli        rank=21 kind=ordinary
crate fln-wasm       rank=21 kind=ordinary
crate fln-conformance rank=22 kind=ordinary
prohibit fln-unsafe-* ->* fln-kernel
prohibit fln-unsafe-* ->* fln-checker
prohibit fln-kernel ->* fln-checker
prohibit fln-checker ->* fln-kernel
prohibit fln-checker ->* fln-olean
prohibit fln-checker ->* fln-rt
prohibit fln-checker ->* fln-unsafe-*
allow-direct fln-kernel = fln-core, fln-hash, fln-bignum, fln-env
allow-direct fln-checker = fln-core, fln-hash, fln-bignum
covenant fln-kernel max-loc=100
suite-dep asupersync
";

const EMPTY_LEDGER: &str = "schema fln-unsafe-ledger/1\n";

const TOOLCHAIN_PIN: &str = "[toolchain]\nchannel = \"nightly-2026-07-13\"\n";

const SUITE_LOCK_FIXTURE: &str = "\
schema fln-suite-lock/1
rust-nightly nightly-2026-07-13
target x86_64-unknown-linux-gnu
suite asupersync commit=e464a484cb65c1a55be0d9c925e6e9c20318edcb path=/dp/asupersync
crate asupersync repo=asupersync
reference leanprover/lean4 tag=v4.32.0 commit=8c9756b28d64dab099da31a4c09229a9e6a2ef35 tree=ba16913719a2f6a15a826918fbe6ba9dd5413e91
corpus leanprover-community/mathlib4 tag=v4.32.0 commit=81a5d257c8e410db227a6665ed08f64fea08e997
";

/// The crates every base fixture materializes (name, is-boundary) — must stay in
/// lockstep with BASE_GRAPH and base().
const FIXTURE_CRATES: [(&str, bool); 32] = [
    ("fln-core", false),
    ("fln-hash", false),
    ("fln-bignum", false),
    ("fln-libm", false),
    ("fln-unsafe-abi", true),
    ("fln-unsafe-region", true),
    ("fln-rt", false),
    ("fln-env", false),
    ("fln-olean", false),
    ("fln-kernel", false),
    ("fln-checker", false),
    ("fln-syntax", false),
    ("fln-parse", false),
    ("fln-mid", false),
    ("fln-elab", false),
    ("fln-comp", false),
    ("fln-vm", false),
    ("fln-unsafe-jit", true),
    ("fln-verdict", false),
    ("fln-anvil", false),
    ("fln-ledger", false),
    ("fln-lake", false),
    ("fln-server", false),
    ("fln-trace", false),
    ("fln", false),
    ("fln-hound", false),
    ("fln-doc", false),
    ("fln-mcp", false),
    ("fln-tui", false),
    ("fln-cli", false),
    ("fln-wasm", false),
    ("fln-conformance", false),
];

fn fixture_cargo_lock() -> String {
    let mut lock = String::from("version = 4\n");
    for (name, _) in FIXTURE_CRATES {
        lock.push_str(&format!(
            "\n[[package]]\nname = \"{name}\"\nversion = \"0.0.0\"\n"
        ));
    }
    lock
}

fn fixture_allowlist() -> String {
    let mut rows = String::from("schema fln-closure-allowlist/1\n");
    for (name, boundary) in FIXTURE_CRATES {
        let audit = if boundary { "deny-ledgered" } else { "forbid" };
        rows.push_str(&format!(
            "package {name} version=0.0.0 source=workspace checksum=- license=MIT build-script=no proc-macro=no native-link=no unsafe-audit={audit} policy=runtime owner=fl upgrade=workspace reason=fixture\n"
        ));
    }
    rows
}

fn manifest(name: &str, deps: &[&str]) -> String {
    let mut m = format!(
        "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\nlicense = \"MIT\"\npublish = false\n\n[dependencies]\n"
    );
    for dep in deps {
        m.push_str(&format!("{dep} = {{ path = \"../{dep}\" }}\n"));
    }
    m
}

fn lib_rs(boundary: bool) -> &'static str {
    if boundary {
        "//! boundary stub\n#![deny(unsafe_code)]\n"
    } else {
        "//! stub\n#![forbid(unsafe_code)]\n"
    }
}

/// Baseline clean fixture: the complete plan crate map plus one synthetic middle
/// crate used by transitive-path tests, no edges, plus the
/// closure-governance files (Cargo.lock ⇄ allowlist ⇄ SUITE.lock ⇄ toolchain pin)
/// the D1 audit requires on every root.
fn base(ws: &TempWs) {
    ws.write(
        "Cargo.toml",
        "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\", \"tools/*\"]\n",
    );
    ws.write("rust-toolchain.toml", TOOLCHAIN_PIN);
    ws.write("SUITE.lock", SUITE_LOCK_FIXTURE);
    ws.write("Cargo.lock", &fixture_cargo_lock());
    ws.write("ci/CLOSURE_ALLOWLIST.txt", &fixture_allowlist());
    ws.write("ci/WORKSPACE_GRAPH.txt", BASE_GRAPH);
    ws.write("ci/UNSAFE_LEDGER.txt", EMPTY_LEDGER);
    for (name, boundary) in FIXTURE_CRATES {
        ws.write(&format!("crates/{name}/Cargo.toml"), &manifest(name, &[]));
        ws.write(&format!("crates/{name}/src/lib.rs"), lib_rs(boundary));
    }
}

fn codes(outcome: &RunOutcome) -> Vec<&'static str> {
    outcome.findings.iter().map(|f| f.code).collect()
}

fn graph_with_edges(edges: &[&str]) -> String {
    let mut g = String::from(BASE_GRAPH);
    for e in edges {
        g.push_str(&format!("edge {e}\n"));
    }
    g
}

#[test]
fn clean_fixture_passes() {
    let ws = TempWs::new("clean");
    base(&ws);
    let out = ws.run();
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
    assert_eq!(out.crate_count, FIXTURE_CRATES.len());
}

#[test]
fn upward_edge_violates_layering() {
    let ws = TempWs::new("upward");
    base(&ws);
    ws.write(
        "crates/fln-core/Cargo.toml",
        &manifest("fln-core", &["fln-kernel"]),
    );
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-core -> fln-kernel"]),
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-007"]);
}

#[test]
fn unacknowledged_edge_is_flagged_and_recovers_when_acknowledged() {
    let ws = TempWs::new("unack-edge");
    base(&ws);
    ws.write(
        "crates/fln-hash/Cargo.toml",
        &manifest("fln-hash", &["fln-core"]),
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-005"]);

    // Recovery: acknowledge the edge in the reviewed file; the gate goes green.
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-hash -> fln-core"]),
    );
    assert!(ws.run().findings.is_empty());
}

#[test]
fn stale_acknowledged_edge_is_flagged() {
    let ws = TempWs::new("stale-edge");
    base(&ws);
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-hash -> fln-core"]),
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-006"]);
}

#[test]
fn undeclared_crate_on_disk_is_flagged() {
    let ws = TempWs::new("rogue");
    base(&ws);
    ws.write("crates/fln-rogue/Cargo.toml", &manifest("fln-rogue", &[]));
    ws.write("crates/fln-rogue/src/lib.rs", lib_rs(false));
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-001"]);
}

#[test]
fn declared_crate_missing_on_disk_is_flagged() {
    let ws = TempWs::new("ghost");
    base(&ws);
    let g = BASE_GRAPH.replacen(
        "prohibit",
        "crate fln-ghost rank=3 kind=ordinary\nprohibit",
        1,
    );
    ws.write("ci/WORKSPACE_GRAPH.txt", &g);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-002"]);
}

#[test]
fn prohibited_transitive_path_is_flagged() {
    let ws = TempWs::new("transitive");
    base(&ws);
    // Both hops are individually legal (12 > 8 > 6) — only the D3 transitive
    // prohibition fln-unsafe-* ->* fln-kernel catches the composition.
    ws.write(
        "crates/fln-unsafe-jit/Cargo.toml",
        &manifest("fln-unsafe-jit", &["fln-mid"]),
    );
    ws.write(
        "crates/fln-mid/Cargo.toml",
        &manifest("fln-mid", &["fln-kernel"]),
    );
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-unsafe-jit -> fln-mid", "fln-mid -> fln-kernel"]),
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec!["FLN-STRUCT-008"]);
    assert!(
        out.findings[0]
            .detail
            .contains("fln-unsafe-jit -> fln-mid -> fln-kernel"),
        "path missing from detail: {}",
        out.findings[0].detail
    );
}

#[test]
fn allow_direct_covenant_is_enforced() {
    let ws = TempWs::new("allow-direct");
    base(&ws);
    // fln-kernel -> fln-unsafe-abi is downward and acknowledged, but outside the
    // kernel's exhaustive direct-dependency allowlist.
    ws.write(
        "crates/fln-kernel/Cargo.toml",
        &manifest("fln-kernel", &["fln-unsafe-abi"]),
    );
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-kernel -> fln-unsafe-abi"]),
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-009"]);
}

#[test]
fn external_dep_outside_closed_universe_is_flagged() {
    let ws = TempWs::new("serde");
    base(&ws);
    let mut m = manifest("fln-hash", &[]);
    m.push_str("serde = \"1\"\n");
    ws.write("crates/fln-hash/Cargo.toml", &m);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-010"]);
}

#[test]
fn suite_dep_requires_path_form() {
    let ws = TempWs::new("suite-path");
    base(&ws);
    let mut m = manifest("fln-hash", &[]);
    m.push_str("asupersync = \"1\"\n");
    ws.write("crates/fln-hash/Cargo.toml", &m);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-010"]);

    // Recovery: the path form is the allowed shape (pin lands with SUITE.lock).
    let mut m = manifest("fln-hash", &[]);
    m.push_str("asupersync = { path = \"/dp/asupersync\" }\n");
    ws.write("crates/fln-hash/Cargo.toml", &m);
    assert!(ws.run().findings.is_empty());
}

#[test]
fn missing_forbid_pragma_is_flagged() {
    let ws = TempWs::new("no-forbid");
    base(&ws);
    ws.write(
        "crates/fln-hash/src/lib.rs",
        "//! stub without the pragma\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-011"]);
}

#[test]
fn boundary_crate_with_forbid_is_flagged() {
    let ws = TempWs::new("boundary-forbid");
    base(&ws);
    ws.write("crates/fln-unsafe-abi/src/lib.rs", lib_rs(false));
    let out = ws.run();
    assert!(!out.findings.is_empty());
    assert!(codes(&out).iter().all(|c| *c == "FLN-STRUCT-012"));
}

#[test]
fn unledgered_allow_site_is_flagged_and_ledgered_site_passes() {
    let ws = TempWs::new("unledgered");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n\n#[allow(unsafe_code)]\nfn peek() {}\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-013"]);

    // The authorization comment is a canonical marker, not free-form prose that merely
    // begins with an id.
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n\n// UNSAFE-LEDGER: FLN-UL-0001 extra words\n#[allow(unsafe_code)]\nfn peek() {}\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-013"]);

    // Recovery: marker + matching ledger row make the same site legal.
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n\n// UNSAFE-LEDGER: FLN-UL-0001\n#[allow(unsafe_code)]\nfn peek() {}\n",
    );
    ws.write(
        "ci/UNSAFE_LEDGER.txt",
        "schema fln-unsafe-ledger/1\nrow FLN-UL-0001 | crates/fln-unsafe-abi/src/lib.rs | layout law | rig T-1 | safe copy path | result never enters a checked declaration\n",
    );
    assert!(ws.run().findings.is_empty());
}

#[test]
fn stale_ledger_row_is_flagged() {
    let ws = TempWs::new("stale-row");
    base(&ws);
    ws.write(
        "ci/UNSAFE_LEDGER.txt",
        "schema fln-unsafe-ledger/1\nrow FLN-UL-0009 | crates/fln-unsafe-abi/src/lib.rs | inv | ev | fb | ncb\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-014"]);
}

#[test]
fn comment_mentions_of_allow_are_not_sites() {
    // Doc comments and comments may mention the attribute (the boundary stubs do, to
    // document the ledger discipline) without creating a ledgerable site.
    let ws = TempWs::new("comment-mention");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! docs may mention #[allow(unsafe_code)] freely\n#![deny(unsafe_code)]\n// a comment naming #[allow(unsafe_code)] is not a site either\n",
    );
    assert!(ws.run().findings.is_empty());
}

#[test]
fn kernel_line_covenant_is_enforced() {
    let ws = TempWs::new("covenant");
    base(&ws);
    let mut big = String::from("//! stub\n#![forbid(unsafe_code)]\n");
    for i in 0..100 {
        big.push_str(&format!("pub fn f{i}() {{}}\n"));
    }
    // Doc comment excluded; 1 pragma line + 100 fns = 101 covenant-relevant lines,
    // exceeding the fixture covenant max-loc=100 (kept small so the test stays fast).
    ws.write("crates/fln-kernel/src/lib.rs", &big);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-015"]);
}

#[test]
fn wrong_edition_is_flagged() {
    let ws = TempWs::new("edition");
    base(&ws);
    let m = manifest("fln-hash", &[]).replace("edition = \"2024\"", "edition = \"2021\"");
    ws.write("crates/fln-hash/Cargo.toml", &m);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-004"]);
}

#[test]
fn unsafe_prefix_and_kind_must_coincide() {
    let ws = TempWs::new("prefix-kind");
    base(&ws);
    let g = BASE_GRAPH.replace(
        "crate fln-unsafe-abi rank=2  kind=unsafe-boundary",
        "crate fln-unsafe-abi rank=2  kind=ordinary",
    );
    ws.write("ci/WORKSPACE_GRAPH.txt", &g);
    // The kind mismatch fires; the deny-rooted lib under an "ordinary" kind fires too.
    let out = ws.run();
    assert!(
        codes(&out).contains(&"FLN-STRUCT-017"),
        "got {:?}",
        out.findings
    );
}

#[test]
fn unparseable_manifest_is_a_finding_not_a_guess() {
    let ws = TempWs::new("bad-manifest");
    base(&ws);
    ws.write(
        "crates/fln-hash/Cargo.toml",
        "[package]\nname = \"fln-hash\"\nedition = \"2024\"\n[patch.crates-io]\nx = \"1\"\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-016"]);
}

/// The guard runs against a root missing the reviewed files -> setup failure (exit 2
/// path), never a silent pass.
#[test]
fn missing_reviewed_files_are_setup_failures() {
    let ws = TempWs::new("no-files");
    let root = ws.materialize().expect("materialize retained fixture");
    assert!(checks::run(Path::new(&root)).is_err());
}

#[test]
fn root_workspace_membership_is_enforced() {
    let ws = TempWs::new("root-members");
    base(&ws);
    ws.write(
        "Cargo.toml",
        "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\"]\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-021"]);
}

#[test]
fn dependency_path_must_resolve_to_acknowledged_crate() {
    let ws = TempWs::new("wrong-path");
    base(&ws);
    ws.write(
        "crates/fln-hash/Cargo.toml",
        "[package]\nname = \"fln-hash\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n[dependencies]\nfln-core = { path = \"../fln-kernel\" }\n",
    );
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-hash -> fln-core"]),
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-023"]);
}

#[test]
fn comments_and_raw_strings_cannot_spoof_root_lint() {
    let ws = TempWs::new("lint-spoof");
    base(&ws);
    ws.write(
        "crates/fln-hash/src/lib.rs",
        "/* #![forbid(unsafe_code)] */\nconst FAKE: &str = r#\"#![forbid(unsafe_code)]\"#;\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-011"]);
}

#[test]
fn conditional_cfg_attr_cannot_spoof_unsafe_posture() {
    let ordinary = TempWs::new("conditional-forbid");
    base(&ordinary);
    ordinary.write(
        "crates/fln-hash/src/lib.rs",
        "#![cfg_attr(any(), forbid(unsafe_code))]\n",
    );
    assert_eq!(codes(&ordinary.run()), vec!["FLN-STRUCT-011"]);

    let boundary = TempWs::new("conditional-deny");
    base(&boundary);
    boundary.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "#![cfg_attr(any(), deny(unsafe_code))]\n",
    );
    assert_eq!(codes(&boundary.run()), vec!["FLN-STRUCT-012"]);
}

#[test]
fn nested_inner_attribute_cannot_spoof_crate_root_posture() {
    let ordinary = TempWs::new("nested-forbid");
    base(&ordinary);
    ordinary.write(
        "crates/fln-hash/src/lib.rs",
        "mod decoy { #![forbid(unsafe_code)] }\n",
    );
    assert_eq!(codes(&ordinary.run()), vec!["FLN-STRUCT-011"]);

    let boundary = TempWs::new("nested-deny");
    base(&boundary);
    boundary.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "mod decoy { #![deny(unsafe_code)] }\n",
    );
    assert_eq!(codes(&boundary.run()), vec!["FLN-STRUCT-012"]);
}

#[cfg(unix)]
#[test]
fn symlinked_source_cannot_escape_or_cycle_around_scans() {
    use std::os::unix::fs::symlink;

    let escaped = TempWs::new("source-symlink");
    base(&escaped);
    escaped.write("outside.rs", "#[allow(unsafe_code)]\nfn hidden() {}\n");
    let root = escaped
        .materialize()
        .expect("materialize retained symlink fixture");
    symlink(
        "../../../outside.rs",
        root.join("crates/fln-kernel/src/linked.rs"),
    )
    .expect("create retained source symlink");
    let out = checks::run(&root).expect("guard reports symlink without following it");
    assert_eq!(codes(&out), vec!["FLN-STRUCT-016"]);
    assert!(out.findings[0].detail.contains("symlinks are forbidden"));

    let cycle = TempWs::new("directory-symlink-cycle");
    base(&cycle);
    let root = cycle
        .materialize()
        .expect("materialize retained symlink-cycle fixture");
    symlink("..", root.join("crates/fln-kernel/src/cycle"))
        .expect("create retained directory symlink");
    let out = checks::run(&root).expect("guard reports cycle without recursing into it");
    assert_eq!(codes(&out), vec!["FLN-STRUCT-016"]);
}

#[test]
fn all_structural_allow_variants_are_ledgered() {
    let ws = TempWs::new("allow-variants");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "#![deny(unsafe_code)]\n#[allow ( unsafe_code, dead_code )]\nfn one() {}\n#[cfg_attr(any(), allow(unsafe_code))]\nfn two() {}\n",
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec!["FLN-STRUCT-013", "FLN-STRUCT-013"]);
}

#[test]
fn alternate_lint_levels_cannot_lower_boundary_deny() {
    for (level, tag) in [("warn", "warn-lowering"), ("expect", "expect-lowering")] {
        let ws = TempWs::new(tag);
        base(&ws);
        ws.write(
            "crates/fln-unsafe-abi/src/lib.rs",
            &format!("#![deny(unsafe_code)]\n#[{level}(unsafe_code)]\nfn lowered() {{}}\n"),
        );
        let out = ws.run();
        assert_eq!(codes(&out), vec!["FLN-STRUCT-013"]);
        assert!(out.findings[0].detail.contains(level));
    }
}

#[test]
fn inner_unsafe_allow_is_never_narrowly_ledgerable() {
    let ws = TempWs::new("inner-allow");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "#![deny(unsafe_code)]\n#![allow(unsafe_code)]\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-013"]);
}

#[test]
fn unsafe_boundary_exports_fail_closed_until_type_aware_classification() {
    let ws = TempWs::new("unsafe-export");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "#![deny(unsafe_code)]\npub fn forge<T>() -> T { loop {} }\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-022"]);

    let local = TempWs::new("restricted-export");
    base(&local);
    local.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "#![deny(unsafe_code)]\npub(crate) fn local_only() {}\n",
    );
    assert!(local.run().findings.is_empty());

    let macro_expansion = TempWs::new("macro-expansion");
    base(&macro_expansion);
    macro_expansion.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "#![deny(unsafe_code)]\nmacro_rules! hidden_policy { () => {} }\n",
    );
    assert_eq!(codes(&macro_expansion.run()), vec!["FLN-STRUCT-022"]);
}

#[test]
fn constitutional_prohibition_cannot_be_removed() {
    let ws = TempWs::new("missing-prohibition");
    base(&ws);
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &BASE_GRAPH.replace("prohibit fln-unsafe-* ->* fln-checker\n", ""),
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-024"]);
}

#[test]
fn kernel_source_inclusion_cannot_escape_the_loc_covenant() {
    let ws = TempWs::new("kernel-include");
    base(&ws);
    ws.write(
        "crates/fln-kernel/src/lib.rs",
        "#![forbid(unsafe_code)]\ninclude!(\"../hidden.inc\");\n",
    );
    ws.write("crates/fln-kernel/hidden.inc", "fn hidden() {}\n");
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-015"]);

    let conditional = TempWs::new("kernel-conditional-path");
    base(&conditional);
    conditional.write(
        "crates/fln-kernel/src/lib.rs",
        "#![forbid(unsafe_code)]\n#[cfg_attr(not(any()), path = \"../hidden.rs\")]\nmod hidden;\n",
    );
    conditional.write("crates/fln-kernel/hidden.rs", "fn hidden() {}\n");
    assert_eq!(codes(&conditional.run()), vec!["FLN-STRUCT-015"]);
}

#[test]
fn plan_rank_and_trust_allowlist_cannot_be_weakened() {
    let rank = TempWs::new("rank-change");
    base(&rank);
    rank.write(
        "ci/WORKSPACE_GRAPH.txt",
        &BASE_GRAPH.replace(
            "crate fln-core       rank=0  kind=ordinary",
            "crate fln-core       rank=99 kind=ordinary",
        ),
    );
    assert_eq!(codes(&rank.run()), vec!["FLN-STRUCT-024"]);

    let allowlist = TempWs::new("trust-allowlist-change");
    base(&allowlist);
    allowlist.write(
        "ci/WORKSPACE_GRAPH.txt",
        &BASE_GRAPH.replace(
            "allow-direct fln-kernel = fln-core, fln-hash, fln-bignum, fln-env",
            "allow-direct fln-kernel = fln-core, fln-hash, fln-bignum",
        ),
    );
    assert_eq!(codes(&allowlist.run()), vec!["FLN-STRUCT-024"]);
}

#[test]
fn plan_defined_crate_cannot_disappear_from_graph_and_disk_together() {
    let ws = TempWs::new("missing-plan-crate");
    base(&ws);
    ws.files
        .borrow_mut()
        .retain(|path, _| !path.starts_with("crates/fln-doc/"));
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &BASE_GRAPH.replace("crate fln-doc        rank=20 kind=ordinary\n", ""),
    );
    ws.write(
        "Cargo.lock",
        &fixture_cargo_lock().replace(
            "\n[[package]]\nname = \"fln-doc\"\nversion = \"0.0.0\"\n",
            "",
        ),
    );
    ws.write(
        "ci/CLOSURE_ALLOWLIST.txt",
        &fixture_allowlist()
            .lines()
            .filter(|line| !line.starts_with("package fln-doc "))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec!["FLN-STRUCT-024"]);
    assert!(out.findings[0].detail.contains("fln-doc"));
}

#[test]
fn integration_targets_cannot_bypass_ordinary_unsafe_posture() {
    let ws = TempWs::new("integration-root-lint");
    base(&ws);
    ws.write(
        "crates/fln-hash/tests/bypass.rs",
        "fn integration_target_without_posture() {}\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-011"]);

    let boundary = TempWs::new("boundary-integration-allow");
    base(&boundary);
    boundary.write(
        "crates/fln-unsafe-abi/tests/bypass.rs",
        "#![deny(unsafe_code)]\n#[allow(unsafe_code)]\nfn bypass() {}\n",
    );
    assert_eq!(codes(&boundary.run()), vec!["FLN-STRUCT-013"]);
}
