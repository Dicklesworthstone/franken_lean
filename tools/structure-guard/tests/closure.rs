//! Seeded-violation tests for the dependency-closure audit (bead franken_lean-xwf):
//! Cargo.lock ⇄ CLOSURE_ALLOWLIST ⇄ SUITE.lock ⇄ rust-toolchain.toml, exercised through
//! the full `checks::run` gate exactly as CI runs it.

#![forbid(unsafe_code)]

use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use structure_guard::checks::{self, RunOutcome};

/// Materialized retained fixture root (mirrors the seeded.rs no-deletion policy).
fn materialize(tag: &str, files: &[(String, String)]) -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after epoch")
        .as_nanos();
    let root = loop {
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let candidate = std::env::temp_dir().join(format!(
            "structure-guard-closure-{}-{stamp}-{n}-{tag}",
            std::process::id()
        ));
        let created = fs::create_dir(&candidate);
        if created
            .as_ref()
            .is_err_and(|e| e.kind() == std::io::ErrorKind::AlreadyExists)
        {
            continue;
        }
        created.expect("create retained fixture root");
        break candidate;
    };
    for (rel, content) in files {
        let path = root.join(rel);
        fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
        let mut f = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .expect("create fixture file without overwrite");
        f.write_all(content.as_bytes()).expect("write");
    }
    eprintln!("retained closure fixture: {}", root.display());
    root
}

const GRAPH: &str = "\
	schema fln-workspace-graph/1
	crate fln-core rank=0 kind=ordinary
	crate fln-hash rank=1 kind=ordinary
	crate fln-bignum rank=1 kind=ordinary
	crate fln-libm rank=1 kind=ordinary
	crate fln-unsafe-abi rank=2 kind=unsafe-boundary
	crate fln-unsafe-region rank=2 kind=unsafe-boundary
	crate fln-rt rank=3 kind=ordinary
	crate fln-env rank=4 kind=ordinary
	crate fln-olean rank=5 kind=ordinary
	crate fln-kernel rank=6 kind=ordinary
	crate fln-checker rank=6 kind=ordinary
	crate fln-syntax rank=7 kind=ordinary
	crate fln-parse rank=8 kind=ordinary
	crate fln-elab rank=9 kind=ordinary
	crate fln-comp rank=10 kind=ordinary
	crate fln-vm rank=11 kind=ordinary
	crate fln-unsafe-jit rank=12 kind=unsafe-boundary
	crate fln-verdict rank=13 kind=ordinary
	crate fln-anvil rank=14 kind=ordinary
	crate fln-ledger rank=15 kind=ordinary
	crate fln-lake rank=16 kind=ordinary
	crate fln-server rank=17 kind=ordinary
	crate fln-trace rank=18 kind=ordinary
	crate fln rank=19 kind=ordinary
	crate fln-hound rank=20 kind=ordinary
	crate fln-doc rank=20 kind=ordinary
	crate fln-mcp rank=20 kind=ordinary
	crate fln-tui rank=20 kind=ordinary
	crate fln-cli rank=21 kind=ordinary
	crate fln-wasm rank=21 kind=ordinary
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
	covenant fln-kernel max-loc=12000
	suite-dep asupersync
	";

const LEDGER: &str = "schema fln-unsafe-ledger/1\n";

const LIB: &str = "//! stub\n#![forbid(unsafe_code)]\n";
const BOUNDARY_LIB: &str = "//! boundary stub\n#![deny(unsafe_code)]\n";

const SUITE_LOCK: &str = "\
schema fln-suite-lock/1
rust-nightly nightly-2026-07-13
target x86_64-unknown-linux-gnu
suite asupersync commit=e464a484cb65c1a55be0d9c925e6e9c20318edcb path=/dp/asupersync
crate asupersync repo=asupersync
reference leanprover/lean4 tag=v4.32.0 commit=8c9756b28d64dab099da31a4c09229a9e6a2ef35 tree=ba16913719a2f6a15a826918fbe6ba9dd5413e91
corpus leanprover-community/mathlib4 tag=v4.32.0 commit=81a5d257c8e410db227a6665ed08f64fea08e997
";

const TOOLCHAIN: &str =
    "[toolchain]\nchannel = \"nightly-2026-07-13\"\ncomponents = [\"rustfmt\", \"clippy\"]\n";

fn base_files() -> Vec<(String, String)> {
    let crates = [
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
    let mut files = vec![
        (
            "Cargo.toml".to_string(),
            "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\", \"tools/*\"]\n".to_string(),
        ),
        ("ci/WORKSPACE_GRAPH.txt".to_string(), GRAPH.to_string()),
        ("ci/UNSAFE_LEDGER.txt".to_string(), LEDGER.to_string()),
        ("SUITE.lock".to_string(), SUITE_LOCK.to_string()),
        ("rust-toolchain.toml".to_string(), TOOLCHAIN.to_string()),
    ];
    let mut cargo_lock = "version = 4\n".to_string();
    let mut allowlist = "schema fln-closure-allowlist/1\n".to_string();
    for (name, boundary) in crates {
        files.push((
            format!("crates/{name}/Cargo.toml"),
            format!(
                "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\nlicense = \"MIT\"\npublish = false\n\n[dependencies]\n"
            ),
        ));
        files.push((
            format!("crates/{name}/src/lib.rs"),
            if boundary { BOUNDARY_LIB } else { LIB }.to_string(),
        ));
        cargo_lock.push_str(&format!(
            "\n[[package]]\nname = \"{name}\"\nversion = \"0.0.0\"\n"
        ));
        allowlist.push_str(&format!(
            "package {name} version=0.0.0 source=workspace checksum=- license=MIT build-script=no proc-macro=no native-link=no unsafe-audit={} policy=runtime owner=fl upgrade=workspace reason=fixture\n",
            if boundary { "deny-ledgered" } else { "forbid" }
        ));
    }
    files.push(("Cargo.lock".to_string(), cargo_lock));
    files.push(("ci/CLOSURE_ALLOWLIST.txt".to_string(), allowlist));
    files
}

fn run_with(tag: &str, mutate: impl FnOnce(&mut Vec<(String, String)>)) -> RunOutcome {
    let mut files = base_files();
    mutate(&mut files);
    let root = materialize(tag, &files);
    checks::run(&root).expect("guard runs")
}

fn codes(outcome: &RunOutcome) -> Vec<&'static str> {
    outcome.findings.iter().map(|f| f.code).collect()
}

fn replace(files: &mut Vec<(String, String)>, rel: &str, content: &str) {
    files.retain(|(path, _)| path != rel);
    files.push((rel.to_string(), content.to_string()));
}

fn append(files: &mut [(String, String)], rel: &str, content: &str) {
    files
        .iter_mut()
        .find(|(path, _)| path == rel)
        .expect("fixture file exists")
        .1
        .push_str(content);
}

fn replace_fragment(files: &mut [(String, String)], rel: &str, before: &str, after: &str) {
    let content = &mut files
        .iter_mut()
        .find(|(path, _)| path == rel)
        .expect("fixture file exists")
        .1;
    assert!(content.contains(before), "fixture fragment exists");
    *content = content.replacen(before, after, 1);
}

#[test]
fn clean_closure_passes() {
    let out = run_with("clean", |_| {});
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
}

#[test]
fn unlisted_lock_package_is_flagged_and_recovers_when_allowlisted() {
    let out = run_with("unlisted", |files| {
        append(
            files,
            "Cargo.lock",
            "\n[[package]]\nname = \"rogue\"\nversion = \"0.1.0\"\n",
        );
    });
    assert_eq!(codes(&out), vec!["FLN-STRUCT-018"]);
    assert!(out.findings[0].detail.contains("rogue"));

    // Recovery: the same closure with a reviewed allowlist row goes green. The rogue
    // package must also be a declared workspace crate for source=workspace to hold.
    let out = run_with("unlisted-recovery", |files| {
        append(
            files,
            "Cargo.lock",
            "\n[[package]]\nname = \"rogue\"\nversion = \"0.1.0\"\n",
        );
        append(
            files,
            "ci/CLOSURE_ALLOWLIST.txt",
            "package rogue version=0.1.0 source=workspace checksum=- license=MIT build-script=no proc-macro=no native-link=no unsafe-audit=forbid policy=runtime owner=fl upgrade=workspace reason=fixture\n",
        );
        let graph = GRAPH.replace(
            "suite-dep asupersync\n",
            "crate rogue rank=1 kind=ordinary\nsuite-dep asupersync\n",
        );
        replace(files, "ci/WORKSPACE_GRAPH.txt", &graph);
        files.push((
            "crates/rogue/Cargo.toml".to_string(),
            "[package]\nname = \"rogue\"\nversion = \"0.1.0\"\nedition = \"2024\"\nlicense = \"MIT\"\npublish = false\n\n[dependencies]\n".to_string(),
        ));
        files.push(("crates/rogue/src/lib.rs".to_string(), LIB.to_string()));
    });
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
}

#[test]
fn registry_sourced_package_is_prohibited_outright() {
    let out = run_with("registry", |files| {
        append(
            files,
            "Cargo.lock",
            "\n[[package]]\nname = \"serde\"\nversion = \"1.0.219\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\nchecksum = \"5f0e2c6ed6606019b4e29e69dbaba95b11854410e5347d525002456dbbb786b6\"\n",
        );
    });
    assert_eq!(codes(&out), vec!["FLN-STRUCT-018"]);
    assert!(out.findings[0].detail.contains("registry"));
}

#[test]
fn stale_allowlist_row_is_flagged() {
    let out = run_with("stale-row", |files| {
        append(
            files,
            "ci/CLOSURE_ALLOWLIST.txt",
            "package ghost version=0.0.0 source=workspace checksum=- license=MIT build-script=no proc-macro=no native-link=no unsafe-audit=forbid policy=runtime owner=fl upgrade=workspace reason=fixture\n",
        );
    });
    assert_eq!(codes(&out), vec!["FLN-STRUCT-019"]);
}

#[test]
fn version_mismatch_is_flagged() {
    let out = run_with("version-mismatch", |files| {
        replace_fragment(
            files,
            "Cargo.lock",
            "name = \"fln-core\"\nversion = \"0.0.0\"",
            "name = \"fln-core\"\nversion = \"0.0.1\"",
        );
    });
    assert_eq!(codes(&out), vec!["FLN-STRUCT-018"]);
    assert!(out.findings[0].detail.contains("0.0.1"));
}

#[test]
fn nightly_pin_mismatch_is_flagged() {
    let out = run_with("nightly-mismatch", |files| {
        replace(
            files,
            "rust-toolchain.toml",
            "[toolchain]\nchannel = \"nightly-2026-01-01\"\n",
        );
    });
    assert_eq!(codes(&out), vec!["FLN-STRUCT-020"]);
}

#[test]
fn suite_dep_and_suite_lock_must_agree_bidirectionally() {
    // Graph allows atp but SUITE.lock has no crate row for it.
    let out = run_with("graph-without-lock", |files| {
        let graph = format!("{GRAPH}suite-dep atp\n");
        replace(files, "ci/WORKSPACE_GRAPH.txt", &graph);
    });
    assert_eq!(codes(&out), vec!["FLN-STRUCT-020"]);

    // SUITE.lock pins a crate row the graph does not allow.
    let out = run_with("lock-without-graph", |files| {
        let graph = GRAPH.replace("suite-dep asupersync\n", "");
        replace(files, "ci/WORKSPACE_GRAPH.txt", &graph);
    });
    assert_eq!(codes(&out), vec!["FLN-STRUCT-020"]);
}

#[test]
fn missing_governance_files_degrade_to_findings_not_silence() {
    let out = run_with("missing-suite-lock", |files| {
        files.retain(|(rel, _)| rel != "SUITE.lock");
    });
    assert_eq!(codes(&out), vec!["FLN-STRUCT-016"]);
    assert!(out.findings[0].path.contains("SUITE.lock"));

    let out = run_with("missing-allowlist", |files| {
        files.retain(|(rel, _)| rel != "ci/CLOSURE_ALLOWLIST.txt");
    });
    assert_eq!(codes(&out), vec!["FLN-STRUCT-016"]);
}

#[test]
fn undeclared_build_script_is_flagged() {
    let out = run_with("build-script", |files| {
        files.push((
            "crates/fln-core/build.rs".to_string(),
            "#![forbid(unsafe_code)]\nfn main() {}\n".to_string(),
        ));
    });
    assert!(
        codes(&out).contains(&"FLN-STRUCT-018"),
        "expected build-script finding, got {:?}",
        out.findings
    );
}
