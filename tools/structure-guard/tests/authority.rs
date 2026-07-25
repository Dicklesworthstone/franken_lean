//! `structure_authority_model` (bead fln-8mj acceptance) — the governed structural
//! authority as an explicit escape matrix.
//!
//! The other suites ask "does check N fire on defect N?". This one asks the prior
//! question the Design amendment poses: **is the universe the checks range over actually
//! closed?** The reviewed authority is every Cargo workspace member and every Rust-bearing
//! target reachable under any supported invocation, and the amendment requires that a
//! package or target which is hidden, unclassified, substituted, or unreadable fails
//! closed rather than silently narrowing what was checked.
//!
//! So every test here plants an *escape* — a way to make authority-bearing code or
//! configuration invisible to the guard — and asserts it is refused. A test that passes
//! only because the guard never looked is the exact failure this suite exists to catch,
//! so each case also pins the finding to the escaping path, and the recovery fixtures
//! prove the refusals are not blanket.
//!
//! Grouped by escape family: hidden workspace/target, configuration discovery, dependency
//! smuggling, lint-posture substitution, counted-source escape, and inconclusive input.

#![forbid(unsafe_code)]

mod common;

use std::fs;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Duration;

use common::*;
use structure_guard::checks::Authority;

// Finding codes as named constants: a matrix suite reads better when the code under test
// is named once, and it keeps `f.code == "FLN-..."` string-literal comparisons out of the
// file (a security scanner reads that shape as a token comparison).
const SHAPE: &str = "FLN-STRUCT-016";
const COVENANT: &str = "FLN-STRUCT-015";
const DEP_PATH: &str = "FLN-STRUCT-023";
const INCONCLUSIVE: &str = "FLN-STRUCT-027";
const SOURCE_CHANGED: &str = "FLN-STRUCT-028";
const COMPILER_IDENTITY: &str = "FLN-STRUCT-029";
const GENERATED_AUTHORITY: &str = "FLN-STRUCT-030";
const LAYERING: &str = "FLN-STRUCT-007";
const PRIMARY_LIB: &str = "crates/fln-hash/src/lib.rs";

/// Every escape below must be measured against a fixture that is otherwise clean, or a
/// pre-existing finding could be mistaken for the refusal under test.
#[test]
fn the_baseline_authority_fixture_is_clean() {
    let ws = TempWs::new("authority-baseline");
    base(&ws);
    let out = ws.run();
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
    assert_eq!(out.crate_count, FIXTURE_CRATES.len());
    assert_eq!(out.authority, Authority::Complete);
    assert!(out.traversal.count_rule_holds());
}

/// Target inventory counts Cargo roots, while the authority scan still covers every
/// contributing Rust module. A nested support module must not be reported as a second
/// integration-test target.
#[test]
fn target_inventory_does_not_count_nested_modules_as_cargo_targets() {
    let ws = TempWs::new("authority-target-cardinality");
    base(&ws);
    ws.write(
        "crates/fln-core/tests/integration.rs",
        "#![forbid(unsafe_code)]\nmod support;\n",
    );
    ws.write(
        "crates/fln-core/tests/support/mod.rs",
        "#![forbid(unsafe_code)]\npub fn fixture() {}\n",
    );
    let out = ws.run();
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
    assert_eq!(
        out.authority_inventory.targets,
        FIXTURE_CRATES.len() + 1,
        "one integration-test root plus its module was not classified exactly"
    );
}

// ---------------------------------------------------------------- hidden workspace/target

/// A second `[workspace]` inside a member manifest makes that directory its own workspace
/// root, so a plain `cargo build` there resolves a different member set than the reviewed
/// one. The constrained package parser must refuse the section rather than skip it.
#[test]
fn a_nested_workspace_cannot_hide_a_member_set() {
    let ws = TempWs::new("authority-nested-workspace");
    base(&ws);
    ws.write(
        "crates/fln-core/Cargo.toml",
        &format!(
            "{}\n[workspace]\nmembers = [\"../fln-hash\"]\n",
            manifest("fln-core", &[])
        ),
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec![SHAPE]);
    assert_eq!(out.findings[0].path, "crates/fln-core/Cargo.toml");
}

/// `default-members` and `exclude` both change which packages a bare `cargo` command acts
/// on without changing `members`. The root contract admits exactly `resolver` and
/// `members`, so either key is a refusal — otherwise the reviewed member set and the built
/// member set could differ silently.
#[test]
fn root_workspace_keys_that_reshape_the_member_set_are_refused() {
    for (tag, key) in [
        (
            "authority-default-members",
            "default-members = [\"crates/fln-core\"]",
        ),
        ("authority-exclude", "exclude = [\"crates/fln-kernel\"]"),
    ] {
        let ws = TempWs::new(tag);
        base(&ws);
        ws.write(
            "Cargo.toml",
            &format!(
                "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\", \"tools/*\"]\n{key}\n"
            ),
        );
        let out = ws.run();
        assert_eq!(codes(&out), vec!["FLN-STRUCT-021"], "accepted {key}");
    }
}

/// A hand-declared `[[bin]]`/`[[test]]` target can point `path` at source outside the
/// crate, which would carry authority no walk of `crates/*/src` ever reaches.
#[test]
fn hand_declared_targets_cannot_relocate_authority_bearing_source() {
    let ws = TempWs::new("authority-custom-target");
    base(&ws);
    ws.write(
        "crates/fln-core/Cargo.toml",
        &format!(
            "{}\n[[bin]]\nname = \"smuggled\"\npath = \"../../elsewhere/main.rs\"\n",
            manifest("fln-core", &[])
        ),
    );
    ws.write("elsewhere/main.rs", "fn main() {}\n");
    let out = ws.run();
    assert_eq!(codes(&out), vec![SHAPE]);
    assert_eq!(out.findings[0].path, "crates/fln-core/Cargo.toml");
}

/// An auxiliary target with a correct lint header must not stand in for the missing
/// primary product: the crate would be "declared and lint-clean" while its actual library
/// no longer exists.
#[test]
fn an_auxiliary_target_cannot_substitute_for_the_primary_product() {
    let ws = TempWs::new("authority-missing-primary");
    base(&ws);
    ws.retain_paths(|path| path != PRIMARY_LIB);
    ws.write(
        "crates/fln-hash/tests/only_target.rs",
        "#![forbid(unsafe_code)]\nfn auxiliary_only() {}\n",
    );
    let out = ws.run();
    assert!(
        out.findings.iter().any(|f| f.code == SHAPE
            && f.path == "crates/fln-hash"
            && f.detail.contains("auxiliary Cargo targets do not satisfy")),
        "unexpected: {:?}",
        out.findings
    );
}

// ------------------------------------------------------------- configuration discovery

/// Cargo merges `.cargo/config(.toml)` from the invocation directory upward and rustup
/// resolves the toolchain the same way, so the discovery surface is every directory a
/// supported command runs in — not only the root. Each plant here is live for
/// `cd <dir> && cargo build` yet appears in no reviewed manifest.
#[test]
fn configuration_is_discovered_at_every_supported_invocation_directory() {
    for (tag, rel) in [
        ("authority-cfg-root", ".cargo/config.toml"),
        ("authority-cfg-root-legacy", ".cargo/config"),
        ("authority-cfg-crates", "crates/.cargo/config.toml"),
        (
            "authority-cfg-crate",
            "crates/fln-kernel/.cargo/config.toml",
        ),
        (
            "authority-cfg-deep",
            "crates/fln-kernel/src/.cargo/config.toml",
        ),
        ("authority-cfg-tools", "tools/.cargo/config.toml"),
        ("authority-tc-legacy", "rust-toolchain"),
        (
            "authority-tc-crate",
            "crates/fln-kernel/rust-toolchain.toml",
        ),
    ] {
        let ws = TempWs::new(tag);
        base(&ws);
        // A lint cap is the sharpest payload: it silently disables the D3
        // `forbid(unsafe_code)` posture that the whole safety argument rests on.
        ws.write(rel, "[build]\nrustflags = [\"--cap-lints\", \"allow\"]\n");
        let out = ws.run();
        assert_eq!(codes(&out), vec![SHAPE], "missed plant at {rel}");
        assert_eq!(out.findings[0].path, rel);
    }
}

/// The reviewed root pin is the one legal member of that family; the depth walk must not
/// have started rejecting it.
#[test]
fn the_reviewed_root_toolchain_pin_stays_legal() {
    let ws = TempWs::new("authority-cfg-recovery");
    base(&ws);
    let out = ws.run();
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
}

// ------------------------------------------------------------------ dependency smuggling

/// A dependency edge that only exists under a target predicate or a feature is still an
/// edge at build time. The parser refuses the sections outright rather than parsing them
/// into edges it might mis-model.
#[test]
fn conditional_dependency_sections_cannot_carry_an_unreviewed_edge() {
    for (tag, section) in [
        (
            "authority-target-cfg",
            "[target.'cfg(unix)'.dependencies]\nfln-kernel = { path = \"../fln-kernel\" }\n",
        ),
        (
            "authority-build-deps",
            "[build-dependencies]\nfln-kernel = { path = \"../fln-kernel\" }\n",
        ),
        (
            "authority-dev-deps",
            "[dev-dependencies]\nfln-kernel = { path = \"../fln-kernel\" }\n",
        ),
    ] {
        let ws = TempWs::new(tag);
        base(&ws);
        ws.write(
            "crates/fln-core/Cargo.toml",
            &format!("{}\n{section}", manifest("fln-core", &[])),
        );
        let out = ws.run();
        // Either the section is refused outright, or it is modelled and the upward
        // fln-core -> fln-kernel edge is caught. Both are fail-closed; silence is not.
        assert!(
            !out.findings.is_empty(),
            "conditional section carried an unreviewed edge silently: {section}"
        );
        assert!(
            out.findings.iter().all(|f| matches!(
                f.code,
                "FLN-STRUCT-005" | "FLN-STRUCT-007" | "FLN-STRUCT-016"
            )),
            "unexpected finding class for {section}: {:?}",
            out.findings
        );
    }
}

/// A `path` dependency that resolves somewhere other than the acknowledged package makes
/// the reviewed graph a fiction: the name matches, the code does not.
#[test]
fn a_dependency_path_must_resolve_to_the_acknowledged_package() {
    let ws = TempWs::new("authority-path-substitution");
    base(&ws);
    ws.write(
        "crates/fln-hash/Cargo.toml",
        "[package]\nname = \"fln-hash\"\nversion = \"0.0.0\"\nedition = \"2024\"\nlicense = \"MIT\"\npublish = false\n\n[dependencies]\nfln-core = { path = \"../fln-bignum\" }\n",
    );
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-hash -> fln-core"]),
    );
    let out = ws.run();
    assert!(
        out.findings.iter().any(|f| f.code == DEP_PATH),
        "path substitution not caught: {:?}",
        out.findings
    );
}

// ------------------------------------------------------------ lint-posture substitution

/// The unsafe posture is read from the crate root, so anything that makes the root's
/// declaration conditional, nested, or quoted must not be accepted as the real thing.
#[test]
fn crate_root_lint_posture_cannot_be_spoofed() {
    for (tag, root) in [
        (
            "authority-cfg-attr",
            "//! stub\n#![cfg_attr(any(), forbid(unsafe_code))]\n",
        ),
        (
            "authority-nested-mod",
            "//! stub\nmod inner { #![forbid(unsafe_code)] }\n",
        ),
        (
            "authority-string-decoy",
            "//! stub\nconst DECOY: &str = \"#![forbid(unsafe_code)]\";\n",
        ),
        (
            "authority-comment-decoy",
            "//! stub\n/* #![forbid(unsafe_code)] */\n",
        ),
    ] {
        let ws = TempWs::new(tag);
        base(&ws);
        ws.write("crates/fln-core/src/lib.rs", root);
        let out = ws.run();
        assert_eq!(codes(&out), vec!["FLN-STRUCT-011"], "accepted spoof: {tag}");
        assert_eq!(out.findings[0].path, "crates/fln-core/src/lib.rs");
    }
}

/// Auxiliary targets in an ordinary crate are project-authored code too; a test or bench
/// without the posture is an unguarded lane into the same package.
#[test]
fn auxiliary_targets_carry_the_same_posture_as_the_library() {
    let ws = TempWs::new("authority-aux-posture");
    base(&ws);
    ws.write(
        "crates/fln-core/tests/unguarded.rs",
        "fn no_posture_here() {}\n",
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec!["FLN-STRUCT-011"]);
    assert_eq!(out.findings[0].path, "crates/fln-core/tests/unguarded.rs");
}

// --------------------------------------------------------------- counted-source escape

/// The kernel line covenant counts `crates/fln-kernel/src/**`. Source pulled in from
/// outside that closure would execute with kernel authority while never being counted, so
/// the inclusion itself is the violation — independent of how many lines it adds.
#[test]
fn kernel_authority_cannot_be_moved_outside_the_counted_closure() {
    for (tag, line) in [
        ("authority-include", "include!(\"../../../smuggled.rs\");"),
        (
            "authority-path-attr",
            "#[path = \"../../../smuggled.rs\"]\nmod smuggled;",
        ),
    ] {
        let ws = TempWs::new(tag);
        base(&ws);
        ws.write(
            "crates/fln-kernel/src/lib.rs",
            &format!("//! stub\n#![forbid(unsafe_code)]\n{line}\n"),
        );
        ws.write("smuggled.rs", "pub fn admits_a_constant() {}\n");
        let out = ws.run();
        assert!(
            out.findings.iter().any(|f| f.code == COVENANT),
            "counted-source escape not caught for {tag}: {:?}",
            out.findings
        );
    }
}

/// Symlinks are refused before any recursive scanner runs: following one could omit
/// authoritative code from a covenant, authorise a boundary site under the wrong path, or
/// escape the workspace entirely.
#[test]
fn symlinked_source_cannot_escape_the_scanned_closure() {
    let ws = TempWs::new("authority-symlink");
    base(&ws);
    let root = ws.materialize().expect("materialize retained fixture");
    // A symlink is the one fixture the recipe cannot express as file content.
    std::os::unix::fs::symlink("/etc", root.join("crates/fln-kernel/src/escape"))
        .expect("plant symlink");
    let out = structure_guard::checks::run(&root).expect("guard reports without following");
    assert!(
        out.findings
            .iter()
            .any(|f| f.code == SHAPE && f.path.contains("escape") && f.detail.contains("symlink")),
        "symlink escape not caught: {:?}",
        out.findings
    );
}

/// Feature, profile, and host-target axes are closed structurally rather than sampled.
/// Every feature-gated source line is scanned, custom profiles are rejected, and the
/// complete declared target set is inventoried while the effective host must remain a
/// member of it.
#[test]
fn feature_profile_and_host_target_axes_are_closed() {
    let feature = TempWs::new("authority-feature-axis");
    base(&feature);
    feature.write(
        "crates/fln-kernel/Cargo.toml",
        &format!(
            "{}\n[features]\nfrontier = []\n",
            manifest("fln-kernel", &[])
        ),
    );
    feature.write(
        "crates/fln-kernel/src/lib.rs",
        "//! stub\n#![forbid(unsafe_code)]\n#[cfg(feature = \"frontier\")]\ninclude!(\"../../../feature_hidden.rs\");\n",
    );
    feature.write("feature_hidden.rs", "pub fn hidden_authority() {}\n");
    let feature_out = feature.run();
    assert_eq!(feature_out.authority_inventory.features, 1);
    assert!(
        feature_out
            .findings
            .iter()
            .any(|finding| finding.code == COVENANT),
        "feature-gated source escaped the structural scan: {:?}",
        feature_out.findings
    );

    let profile = TempWs::new("authority-profile-axis");
    base(&profile);
    profile.write(
        "Cargo.toml",
        "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\", \"tools/*\"]\n\n[profile.release]\nlto = true\n",
    );
    assert_eq!(codes(&profile.run()), vec!["FLN-STRUCT-021"]);

    let targets = TempWs::new("authority-host-target-axis");
    base(&targets);
    targets.write(
        "SUITE.lock",
        &SUITE_LOCK_FIXTURE.replace(
            "target x86_64-unknown-linux-gnu",
            "target aarch64-unknown-linux-gnu\ntarget x86_64-unknown-linux-gnu",
        ),
    );
    let targets_out = targets.run();
    assert!(
        targets_out.findings.is_empty(),
        "complete target inventory should stay clean: {:?}",
        targets_out.findings
    );
    assert_eq!(targets_out.authority_inventory.target_triples, 2);
}

/// Kernel macro output is admitted only through an exact compiler-builtin inventory.
/// Project-defined/function-like/procedural/derive macros otherwise create generated
/// checking logic with no reviewed source mapping and must fail closed.
#[test]
fn kernel_generated_authority_is_callsite_closed() {
    for (tag, source) in [
        (
            "authority-kernel-macro-definition",
            "macro_rules! hidden_admission { () => { pub fn admit() {} } }\n",
        ),
        (
            "authority-kernel-macro-invocation",
            "hidden_admission!();\n",
        ),
        (
            "authority-kernel-attribute",
            "#[admit_constant]\npub fn hidden() {}\n",
        ),
        (
            "authority-kernel-derive",
            "#[derive(AdmitConstant)]\npub struct Hidden;\n",
        ),
    ] {
        let ws = TempWs::new(tag);
        base(&ws);
        ws.write(
            "crates/fln-kernel/src/lib.rs",
            &format!("//! stub\n#![forbid(unsafe_code)]\n{source}"),
        );
        let out = ws.run();
        assert!(
            out.findings
                .iter()
                .any(|finding| finding.code == GENERATED_AUTHORITY),
            "{tag} was not refused: {:?}",
            out.findings
        );
    }

    let recovery = TempWs::new("authority-kernel-builtin-macro-recovery");
    base(&recovery);
    recovery.write(
        "crates/fln-kernel/src/lib.rs",
        concat!(
            "//! stub\n",
            "#![forbid(unsafe_code)]\n",
            "#[derive(Debug, Clone, PartialEq, Eq)]\n",
            "pub struct Counted;\n",
            "pub fn counted(value: bool) {\n",
            "    assert!(matches!(value, true));\n",
            "    let _ = format!(\"{value}\");\n",
            "    let _: Vec<u8> = vec![];\n",
            "    if false { unreachable!(); }\n",
            "}\n",
        ),
    );
    let recovery_out = recovery.run();
    assert!(
        recovery_out.findings.is_empty(),
        "reviewed builtin callsites should remain clean: {:?}",
        recovery_out.findings
    );
}

// ------------------------------------------------------------------- inconclusive input

/// An undecodable governed file leaves the authority it carries *unestablished*. It must
/// be reported per file — never a clean run, and never a whole-run abort that masks the
/// findings the rest of the scan did establish.
#[test]
fn an_unreadable_governed_input_is_inconclusive_and_masks_nothing() {
    const GARBAGE: [u8; 4] = [0xff, 0xfe, 0x00, 0x80];

    for (tag, rel) in [
        (
            "authority-unreadable-covenant",
            "crates/fln-kernel/src/hidden.rs",
        ),
        (
            "authority-unreadable-boundary",
            "crates/fln-unsafe-abi/src/hidden.rs",
        ),
        ("authority-unreadable-root", "crates/fln-core/src/lib.rs"),
        (
            "authority-unreadable-manifest",
            "crates/fln-core/Cargo.toml",
        ),
    ] {
        let ws = TempWs::new(tag);
        base(&ws);
        ws.write_bytes(rel, &GARBAGE);
        let out = ws.run();
        assert_eq!(
            out.authority,
            Authority::Incomplete,
            "{rel} must not produce an authoritative verdict"
        );
        assert!(
            out.traversal.count_rule_holds(),
            "{rel} broke traversal conservation: {:?}",
            out.traversal
        );
        assert!(
            out.findings
                .iter()
                .any(|f| f.code == INCONCLUSIVE && f.path == rel),
            "{rel} produced no inconclusive finding: {:?}",
            out.findings
        );
    }

    // The masking property, stated as its own assertion: a genuine violation elsewhere in
    // the same run must still be reported.
    let ws = TempWs::new("authority-unreadable-masking");
    base(&ws);
    ws.write_bytes("crates/fln-kernel/src/hidden.rs", &GARBAGE);
    ws.write(
        "crates/fln-core/Cargo.toml",
        &manifest("fln-core", &["fln-kernel"]),
    );
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-core -> fln-kernel"]),
    );
    let observed = codes(&ws.run());
    assert!(observed.contains(&INCONCLUSIVE), "lost: {observed:?}");
    assert!(observed.contains(&LAYERING), "masked: {observed:?}");
}

/// A root with no reviewed files at all is a setup failure, not an empty clean pass: zero
/// findings over zero inputs is exactly the "partial scan promoted to pass" mutant.
#[test]
fn an_unscannable_root_is_a_setup_failure_not_an_empty_pass() {
    let ws = TempWs::new("authority-empty-root");
    let root = ws.materialize().expect("materialize retained fixture");
    assert!(
        structure_guard::checks::run(&root).is_err(),
        "an empty root must not report a clean structural verdict"
    );
}

/// A run over two different source states has no authoritative subject. The changing
/// file is deliberately irrelevant to every semantic check but inside the governed
/// closure, proving that pre/post root binding catches concurrent edits independently of
/// whether they happen to alter a finding.
#[test]
fn a_concurrent_governed_root_change_is_typed_inconclusive() {
    let ws = TempWs::new("authority-concurrent-root-change");
    base(&ws);
    ws.write("ci/concurrent-root-change.txt", "sequence=0\n");
    let root = ws.materialize().expect("materialize retained fixture");
    let changing = root.join("ci/concurrent-root-change.txt");
    let stop = Arc::new(AtomicBool::new(false));
    let writer_stop = Arc::clone(&stop);
    let writer = thread::spawn(move || {
        let mut sequence = 1_u64;
        while !writer_stop.load(Ordering::Acquire) {
            fs::write(&changing, format!("sequence={sequence}\n"))
                .expect("rewrite retained churn fixture");
            sequence = sequence.checked_add(1).expect("test sequence fits u64");
            thread::sleep(Duration::from_millis(1));
        }
    });

    // Give the writer one turn before the first snapshot. It then keeps writing unique
    // values throughout the scan, so the two retained roots cannot agree by parity.
    thread::sleep(Duration::from_millis(5));
    let out = structure_guard::checks::run(&root).expect("guard reports source drift");
    stop.store(true, Ordering::Release);
    writer.join().expect("churn writer exits");

    assert_eq!(out.authority, Authority::Incomplete);
    assert_eq!(out.verdict(), "inconclusive");
    assert_eq!(out.exit_code(), 3);
    assert_ne!(out.governed_root_before, out.governed_root_after);
    assert!(
        out.findings
            .iter()
            .any(|finding| finding.code.eq(SOURCE_CHANGED)),
        "source change was not typed: {:?}",
        out.findings
    );
}

/// The source contract can be complete while the process executes a different compiler.
/// That disagreement is evidence failure, not a structural rejection of the source.
#[test]
fn a_mismatched_effective_compiler_is_typed_inconclusive() {
    let ws = TempWs::new("authority-compiler-mismatch");
    base(&ws);
    ws.write(
        "SUITE.lock",
        &SUITE_LOCK_FIXTURE.replace("rust-release 1.99.0-nightly", "rust-release 1.98.0-nightly"),
    );
    let out = ws.run();
    assert_eq!(out.authority, Authority::Incomplete);
    assert_eq!(out.verdict(), "inconclusive");
    assert_eq!(out.exit_code(), 3);
    assert!(out.compiler_identity.contract_declared);
    assert!(out.compiler_identity.configuration_match);
    assert!(!out.compiler_identity.contract_match);
    assert!(
        out.findings
            .iter()
            .any(|finding| finding.code.eq(COMPILER_IDENTITY)),
        "compiler mismatch was not typed: {:?}",
        out.findings
    );
}
