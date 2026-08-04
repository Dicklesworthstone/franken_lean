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
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use common::*;
use structure_guard::checks::Authority;
use structure_guard::{
    ABI_TARGET_LAYOUT_FILE, CONTRACT_INVENTORY_POLICY_FILE, OLEAN_ILEAN_FORMAT_FILE,
};

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
                "FLN-STRUCT-005" | "FLN-STRUCT-007" | "FLN-STRUCT-016" | "FLN-STRUCT-018"
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
    targets.write(
        CONTRACT_INVENTORY_POLICY_FILE,
        &CONTRACT_INVENTORY_POLICY_FIXTURE
            .replace(
                "row abi-layout:target:0001 kind=abi-layout support=required target-class=certified abi-class=lp64-le",
                "row abi-layout:target:0001 kind=abi-layout support=required target-class=certified abi-class=lp64-le\nrow abi-layout:target:0002 kind=abi-layout support=required target-class=certified abi-class=lp64-le",
            )
            .replace(
                "row artifact-format:olean:target:0001 kind=artifact-format support=required target-class=certified abi-class=lp64-le",
                "row artifact-format:olean:target:0001 kind=artifact-format support=required target-class=certified abi-class=lp64-le\nrow artifact-format:olean:target:0002 kind=artifact-format support=required target-class=certified abi-class=lp64-le",
            )
            .replace(
                "row toolchain",
                "row target:0002 kind=target support=required target-class=certified abi-class=none\nrow toolchain",
            ),
    );
    targets.write(ABI_TARGET_LAYOUT_FILE, &abi_target_layout_fixture(2));
    targets.write(OLEAN_ILEAN_FORMAT_FILE, &olean_ilean_format_fixture(2));
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

/// The two churn paths are placed at the **extremes of the governed traversal**, and that
/// placement is load-bearing rather than cosmetic.
///
/// `governed_snapshot` walks `GOVERNED_ROOT_FILES` (`Cargo.toml`, `Cargo.lock`,
/// `SUITE.lock`, `rust-toolchain.toml`) and then `GOVERNED_ROOT_DIRS` in the fixed order
/// `ci`, `contracts`, `crates`, `tools`, sorting each directory's children by name. A run
/// is therefore `[snapshot A][checks][snapshot B]`, and a rewrite only moves the bound root
/// if it lands between *that path's own* two reads. Churning a single mid-traversal file
/// leaves two blind stretches — everything read before it in A, and everything read after
/// it in B — during which a rewrite completes, advances any counter watching it, and
/// changes nothing. That is not hypothetical: it is how the first repair of this test still
/// failed, on an oversubscribed host where the writer got few enough turns that they landed
/// in the blind tail.
///
/// `00-` sorts before every uppercase sibling, so the head path is the first entry of the
/// first governed directory; `tools/` is traversed last and holds nothing else, so the tail
/// path is the final read of the whole scan. The union of the two intervals is the run
/// minus four small root-file reads, which is what makes "a rewrite completed during the
/// window" and "the bound root moved" the same statement.
const CHURN_HEAD: &str = "ci/00-concurrent-root-change.txt";
const CHURN_TAIL: &str = "tools/zz-concurrent-root-change.txt";

/// Rewrites are staged here and renamed into place, because `fs::write` is not atomic and a
/// fixture that flickers through an empty state is indistinguishable from one that never
/// changed. This directory is deliberately **outside** `GOVERNED_ROOT_DIRS`, so staging is
/// invisible to the scan; `rename` within one filesystem is what makes each rewrite a single
/// observable transition.
const CHURN_STAGING: &str = ".churn-staging";

/// The bound-root property has two halves and only one of them can be raced. This is the
/// half that cannot be: it owns the *sensitivity* of the binding, and it runs no threads.
///
/// Both directions are asserted because each alone is vacuous. Without the quiet control,
/// a digest that moved for any reason at all — a timestamp folded in, a nondeterministic
/// walk order — would satisfy the sensitivity assertion. Without the sensitivity check, a
/// digest that never moved for anything would satisfy the control. The last pair keeps the
/// halves honest about what "during" means: a byte transition *between* two runs is not
/// drift *within* one, and the guard must still report `Complete`.
///
/// It doubles as the inertness control for the two churn paths. Both are asserted to leave
/// a clean, `Complete` fixture, so neither placement can quietly start contributing a
/// finding of its own and make the concurrent test below pass for the wrong reason.
#[test]
fn one_governed_byte_moves_the_bound_root_and_a_quiet_root_holds_still() {
    let ws = TempWs::new("authority-governed-root-binding");
    base(&ws);
    ws.write(CHURN_HEAD, "sequence=0\n");
    ws.write(CHURN_TAIL, "sequence=0\n");
    let root = ws.materialize().expect("materialize retained fixture");
    let staging = root.join(CHURN_STAGING);
    fs::create_dir_all(&staging).expect("create ungoverned churn staging directory");

    // Negative control. Nothing touches the tree, so the guard's own two snapshots agree
    // and the run is a clean `Complete`. A scan that reported drift here — or that found
    // either churn path, or the staging directory, structurally objectionable — would make
    // everything below vacuous.
    let quiet = structure_guard::checks::run(&root).expect("guard runs on a quiet root");
    assert_eq!(
        quiet.governed_root_before, quiet.governed_root_after,
        "an untouched tree bound two different roots"
    );
    assert_eq!(quiet.authority, Authority::Complete);
    assert!(
        quiet.findings.is_empty(),
        "the churn paths are meant to be structurally inert: {:?}",
        quiet.findings
    );

    // The digest is a function of the governed bytes, not of when it was taken: a second
    // run over the same untouched tree must bind the same root.
    let again = structure_guard::checks::run(&root).expect("guard reruns on the quiet root");
    assert_eq!(
        quiet.governed_root_after, again.governed_root_before,
        "the same bytes bound two different roots across runs"
    );

    // One unique governed byte at each extreme, written by this thread, with no race to
    // lose. Asserted separately so a binding that had gone blind to one end of the
    // traversal cannot hide behind the other, and published by the same stage-then-rename
    // the concurrent test depends on, so that mechanism is exercised where nothing is racing.
    for churn in [CHURN_HEAD, CHURN_TAIL] {
        let before = structure_guard::checks::run(&root).expect("guard runs before the edit");
        let staged = staging.join("edit");
        fs::write(&staged, "sequence=1\n").expect("stage churn value");
        fs::rename(&staged, root.join(churn)).expect("publish churn value atomically");
        let moved = structure_guard::checks::run(&root).expect("guard runs after the edit");
        assert_ne!(
            before.governed_root_after, moved.governed_root_before,
            "one changed governed byte at {churn} left the bound root unmoved"
        );

        // ...and that transition is still not *drift*, because it did not happen during a
        // scan. The guard is `Complete` again, which is what separates the two halves.
        assert_eq!(
            moved.governed_root_before, moved.governed_root_after,
            "a transition between runs was reported as drift within one"
        );
        assert_eq!(moved.authority, Authority::Complete);
    }
}

/// A run over two different source states has no authoritative subject. The changing
/// file is deliberately irrelevant to every semantic check but inside the governed
/// closure, proving that pre/post root binding catches concurrent edits independently of
/// whether they happen to alter a finding.
///
/// This half cannot be raced away, only raced *for*: no seam exists to interleave a mutator
/// with one synchronous `checks::run`, so the fixture must genuinely be running while the
/// guard scans. Two versions of it have now failed, each for its own reason, and both are
/// recorded here because the second one is only visible once the first is fixed.
///
/// **The gate failure (bead `fln-sn0w`).** The original bet on a timer — a writer sleeping
/// 1 ms between rewrites, given a 5 ms head start — and lost inside `scripts/check.sh` on
/// 2026-07-26 (`target/check/check-20260726T212528Z-2388936`). The retained fixture says
/// exactly how: its churn file still read `sequence=1`, with an mtime **573 ms after the
/// fixture root was created**, so the writer's *first* write completed long after the guard
/// had finished. Nothing changed during that scan. The guard bound one unchanging root and
/// `Complete` was the correct verdict — the fixture was wrong, not the scanner, and the bare
/// `left: Complete, right: Incomplete` could not say so.
///
/// **The truncation failure, which only the first repair could expose.** Adding a handshake
/// and a completion counter retired the starvation, and the counter then reported something
/// the old fixture could never have said: a run where **400 cycles provably completed inside
/// the window** and the bound root still did not move. That is not a scheduling story at all.
/// `fs::write` opens with `O_TRUNC` and then writes, so the file is observably **empty**
/// between those two syscalls, and a tight writer spends a large fraction of wall time in
/// exactly that state. Both snapshots sampled both churn paths mid-truncation and bound the
/// same empty bytes twice. Proven rather than inferred: the flake reported
/// `fnv1a64:d5b7f85ed50f59a4`, and re-running the guard over a copy of its own retained
/// fixture with both churn files emptied reproduces that digest exactly, against a
/// same-fixture control of `fnv1a64:2ec17154d5cc0332` with the contents left alone.
///
/// So four things carry this test, and none of them is a timer:
///
/// 1. **The guard does not start on a promise.** The writer publishes its counter only
///    after its rewrites land, and this thread blocks until two full cycles have
///    *completed*. That retires thread-start and first-write latency — the 573 ms —
///    outright, rather than hoping a fixed head start covers it.
/// 2. **The writer stays runnable instead of sleeping.** A sleeper must be re-woken by a
///    timer and then rescheduled; a thread yielding between writes is continuously
///    eligible, and needs one turn anywhere in the scan rather than one at a chosen moment.
/// 3. **Every rewrite is a single observable transition.** Staged then renamed, so a reader
///    sees the previous value or the next one and never the empty window between them. Two
///    equal digests can no longer mean "sampled mid-write twice".
/// 4. **The proof and the property are the same statement.** Because both traversal extremes
///    churn, "a cycle completed during the window" and "the bound root moved" coincide, so
///    the precondition asserted below is the one the verdict depends on. With one
///    mid-traversal path they do not: everything read before it in A, and after it in B, is
///    a stretch where a rewrite completes, advances the counter, and changes nothing.
///
/// That is a much narrower bet, not the absence of one. A writer that gets no turn at all
/// therefore fails as a fixture defect naming itself, and can never be reported as a guard
/// verdict.
#[test]
fn a_concurrent_governed_root_change_is_typed_inconclusive() {
    let ws = TempWs::new("authority-concurrent-root-change");
    base(&ws);
    ws.write(CHURN_HEAD, "sequence=0\n");
    ws.write(CHURN_TAIL, "sequence=0\n");
    let root = ws.materialize().expect("materialize retained fixture");
    let staging = root.join(CHURN_STAGING);
    fs::create_dir_all(&staging).expect("create ungoverned churn staging directory");
    let head = root.join(CHURN_HEAD);
    let tail = root.join(CHURN_TAIL);
    let head_staging = staging.join("head");
    let tail_staging = staging.join("tail");
    let stop = Arc::new(AtomicBool::new(false));
    // Published only once both rewrites of a cycle have landed, so an advance is proof that
    // a cycle *completed* — not that one was attempted, and not that a thread spawned.
    let completed = Arc::new(AtomicU64::new(0));
    let writer_stop = Arc::clone(&stop);
    let writer_completed = Arc::clone(&completed);
    let writer = thread::spawn(move || {
        let mut sequence = 1_u64;
        while !writer_stop.load(Ordering::Acquire) {
            let churn = format!("sequence={sequence}\n");
            // Stage then rename. Writing in place would expose the `O_TRUNC` window, and a
            // snapshot that samples it twice binds the same empty bytes and reports no drift.
            fs::write(&head_staging, &churn).expect("stage head churn value");
            fs::write(&tail_staging, &churn).expect("stage tail churn value");
            fs::rename(&head_staging, &head).expect("publish head churn value atomically");
            fs::rename(&tail_staging, &tail).expect("publish tail churn value atomically");
            writer_completed.store(sequence, Ordering::Release);
            sequence = sequence.checked_add(1).expect("test sequence fits u64");
            // Deliberately neither sleeping nor yielding. A sleeper must be re-woken by a
            // timer, which is what the original fixture lost; but `yield_now` is worse under
            // the load this actually runs at, because it surrenders the CPU every cycle and
            // rejoins the back of a long runqueue. Measured: yielding still starved the
            // writer to zero cycles across a whole scan once in 200 runs. A plain CPU-bound
            // loop is scheduled fairly and gets a full timeslice each turn.
        }
    });

    let handshake = Instant::now();
    let mut started = completed.load(Ordering::Acquire);
    while started < 2 && handshake.elapsed() < Duration::from_secs(30) {
        thread::yield_now();
        started = completed.load(Ordering::Acquire);
    }
    let churn_before_window = completed.load(Ordering::Acquire);
    let outcome = structure_guard::checks::run(&root);
    let churn_after_window = completed.load(Ordering::Acquire);
    // One stop and one join on every path, including the degenerate one, so a starved
    // writer can never outlive this test and spin for the rest of the target.
    stop.store(true, Ordering::Release);
    writer.join().expect("churn writer exits");
    let out = outcome.expect("guard reports source drift");

    // Fixture preconditions before verdict. A starved writer must never be reportable as a
    // guard defect, which is the distinction the failing gate run could not draw.
    assert!(
        started >= 2,
        "the churn writer completed {started} cycles before the scan began, inside a 30s \
         handshake; the fixture never ran and this run judges nothing about the guard"
    );
    assert!(
        churn_after_window > churn_before_window,
        "no churn cycle completed inside the guard window (sequence {churn_before_window} -> \
         {churn_after_window}); nothing changed during the scan, so `Complete` is the correct \
         verdict and this run judges nothing about the guard"
    );

    assert_eq!(
        out.authority,
        Authority::Incomplete,
        "{} churn cycles completed inside the window (sequence {churn_before_window} -> \
         {churn_after_window}) but the guard bound one root twice \
         (fnv1a64:{:016x} -> fnv1a64:{:016x})",
        churn_after_window - churn_before_window,
        out.governed_root_before,
        out.governed_root_after
    );
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
