//! Seeded-violation tests (bead fln-8mj acceptance): each structural CI check must
//! demonstrably fail on a synthetic workspace carrying exactly the defect it exists to
//! catch, and pass once the defect is repaired. These are the permanent, in-tree form
//! of "add a test-only violation in CI to prove detection, then remove".
//!
//! The fixture harness lives in `common/`, shared with `authority.rs`.

#![forbid(unsafe_code)]

mod common;

use std::path::Path;

use common::*;
use structure_guard::checks::{self, Authority};
use structure_guard::{
    BUILTIN_ENVIRONMENT_001_CANDIDATE_FILE, CONTRACT_INVENTORY_CANDIDATE_FILE,
    KERNEL_OWNERSHIP_CANDIDATE_FILE,
};

#[test]
fn clean_fixture_passes() {
    let ws = TempWs::new("clean");
    base(&ws);
    let out = ws.run();
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
    assert_eq!(out.crate_count, FIXTURE_CRATES.len());
}

#[test]
fn interrupted_contract_inventory_publication_is_typed_inconclusive() {
    let ws = TempWs::new("contract-inventory-candidate");
    base(&ws);
    ws.write(
        CONTRACT_INVENTORY_CANDIDATE_FILE,
        "planted interrupted candidate\n",
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec!["FLN-STRUCT-033"]);
    assert_eq!(out.authority, Authority::Incomplete);
    assert_eq!(out.verdict(), "inconclusive");
    assert_eq!(out.exit_code(), 3);
    assert!(out.findings[0].detail.contains("reason=stale_candidate"));
}

#[test]
fn interrupted_builtin_census_publication_is_typed_inconclusive() {
    let ws = TempWs::new("builtin-census-candidate");
    base(&ws);
    ws.write(
        BUILTIN_ENVIRONMENT_001_CANDIDATE_FILE,
        "planted interrupted candidate\n",
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec!["FLN-STRUCT-033"]);
    assert_eq!(out.authority, Authority::Incomplete);
    assert_eq!(out.verdict(), "inconclusive");
    assert_eq!(out.exit_code(), 3);
    assert!(
        out.findings[0]
            .detail
            .contains("reason=stale_source_candidate")
    );
}

#[test]
fn interrupted_kernel_ownership_publication_is_typed_inconclusive() {
    let ws = TempWs::new("kernel-ownership-candidate");
    base(&ws);
    ws.write(
        KERNEL_OWNERSHIP_CANDIDATE_FILE,
        "planted interrupted candidate\n",
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec!["FLN-STRUCT-034"]);
    assert_eq!(out.authority, Authority::Incomplete);
    assert_eq!(out.verdict(), "inconclusive");
    assert_eq!(out.exit_code(), 3);
    assert!(out.findings[0].detail.contains("reason=stale_candidate"));
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
        "Cargo.lock",
        &fixture_cargo_lock_with_dependencies(&[("fln-core", &["fln-kernel"])]),
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
    ws.write(
        "Cargo.lock",
        &fixture_cargo_lock_with_dependencies(&[("fln-hash", &["fln-core"])]),
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
fn fln_bench_snapshot_and_edge_laws_are_falsifiable() {
    let missing = TempWs::new("fln-bench-missing-snapshot");
    base(&missing);
    let graph_without_bench =
        BASE_GRAPH.replacen("crate fln-bench      rank=2  kind=ordinary\n", "", 1);
    assert_ne!(graph_without_bench, BASE_GRAPH);
    missing.write("ci/WORKSPACE_GRAPH.txt", &graph_without_bench);
    let missing_codes = codes(&missing.run());
    assert!(missing_codes.contains(&"FLN-STRUCT-001"));
    assert!(missing_codes.contains(&"FLN-STRUCT-024"));

    let undeclared = TempWs::new("fln-bench-undeclared-edge");
    base(&undeclared);
    undeclared.write(
        "crates/fln-bench/Cargo.toml",
        &manifest("fln-bench", &["fln-hash"]),
    );
    undeclared.write(
        "Cargo.lock",
        &fixture_cargo_lock_with_dependencies(&[("fln-bench", &["fln-hash"])]),
    );
    assert_eq!(codes(&undeclared.run()), vec!["FLN-STRUCT-005"]);
    undeclared.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-bench -> fln-hash"]),
    );
    assert!(undeclared.run().findings.is_empty());

    let upward = TempWs::new("fln-bench-upward-edge");
    base(&upward);
    upward.write(
        "crates/fln-bench/Cargo.toml",
        &manifest("fln-bench", &["fln-env"]),
    );
    upward.write(
        "Cargo.lock",
        &fixture_cargo_lock_with_dependencies(&[("fln-bench", &["fln-env"])]),
    );
    upward.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-bench -> fln-env"]),
    );
    assert_eq!(codes(&upward.run()), vec!["FLN-STRUCT-007"]);
}

#[test]
fn verdict_reflected_admission_edges_are_exact_and_falsifiable() {
    let ws = TempWs::new("fln-verdict-reflected-admission-edges");
    base(&ws);
    let dependencies = ["fln-core", "fln-env", "fln-kernel"];
    ws.write(
        "crates/fln-verdict/Cargo.toml",
        &manifest("fln-verdict", &dependencies),
    );
    ws.write(
        "Cargo.lock",
        &fixture_cargo_lock_with_dependencies(&[("fln-verdict", &dependencies)]),
    );

    let missing = ws.run();
    assert_eq!(
        codes(&missing),
        vec!["FLN-STRUCT-005", "FLN-STRUCT-005", "FLN-STRUCT-005"]
    );
    for dependency in dependencies {
        let expected = format!("dependency edge `fln-verdict -> {dependency}`");
        assert!(
            missing
                .findings
                .iter()
                .any(|finding| finding.detail.contains(&expected)),
            "missing exact reflected-admission finding for {dependency}: {:?}",
            missing.findings
        );
    }

    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&[
            "fln-verdict -> fln-core",
            "fln-verdict -> fln-env",
            "fln-verdict -> fln-kernel",
        ]),
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
    let mut lock = fixture_cargo_lock();
    lock.push_str("\n[[package]]\nname = \"fln-ghost\"\nversion = \"0.0.0\"\n");
    ws.write("Cargo.lock", &lock);
    let mut allowlist = fixture_allowlist();
    allowlist.push_str(
        "package fln-ghost version=0.0.0 source=workspace checksum=- license=MIT build-script=no proc-macro=no native-link=no unsafe-audit=forbid policy=runtime owner=franken_lean upgrade=workspace reason=missing fixture\n",
    );
    ws.write("ci/CLOSURE_ALLOWLIST.txt", &allowlist);
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
        "Cargo.lock",
        &fixture_cargo_lock_with_dependencies(&[
            ("fln-unsafe-jit", &["fln-mid"]),
            ("fln-mid", &["fln-kernel"]),
        ]),
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
        "Cargo.lock",
        &fixture_cargo_lock_with_dependencies(&[("fln-kernel", &["fln-unsafe-abi"])]),
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
    assert!(codes(&ws.run()).contains(&"FLN-STRUCT-010"));
}

#[test]
fn suite_dep_requires_path_form() {
    let ws = TempWs::new("suite-path");
    base(&ws);
    let mut m = manifest("fln-hash", &[]);
    m.push_str("asupersync = \"1\"\n");
    ws.write("crates/fln-hash/Cargo.toml", &m);
    assert!(codes(&ws.run()).contains(&"FLN-STRUCT-010"));

    // Recovery of this malformed declaration is removal. The complete positive suite
    // path/commit/allowlist recovery is exercised in closure.rs with a real retained
    // checkout; a path spelling by itself is no longer authority.
    ws.write("crates/fln-hash/Cargo.toml", &manifest("fln-hash", &[]));
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
    // The planted body is the non-boundary stub, so it trips FLN-STRUCT-012 (forbid where
    // deny belongs) and FLN-STRUCT-040 (no SAFETY-note posture) together. Both are correct;
    // this test owns the first.
    assert!(codes(&out).contains(&"FLN-STRUCT-012"));
    assert!(
        codes(&out)
            .iter()
            .all(|c| *c == "FLN-STRUCT-012" || *c == "FLN-STRUCT-040"),
        "unexpected finding beyond the two this plant provokes: {:?}",
        out.findings
    );
}

#[test]
fn unledgered_allow_site_is_flagged_and_ledgered_site_passes() {
    let ws = TempWs::new("unledgered");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n\n#[allow(unsafe_code)]\nfn peek() {}\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-013"]);

    // The authorization comment is a canonical marker, not free-form prose that merely
    // begins with an id.
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n\n// UNSAFE-LEDGER: FLN-UL-0001 extra words\n#[allow(unsafe_code)]\nfn peek() {}\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-013"]);

    // Recovery: marker + matching ledger row make the same site legal.
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n\n// UNSAFE-LEDGER: FLN-UL-0001\n#[allow(unsafe_code)]\nfn peek() {}\n",
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
        "//! docs may mention #[allow(unsafe_code)] freely\n#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n// a comment naming #[allow(unsafe_code)] is not a site either\n",
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
        "[package]\nname = \"fln-hash\"\nversion = \"0.0.0\"\nedition = \"2024\"\nlicense = \"MIT\"\n\n[dependencies]\nfln-core = { path = \"../fln-kernel\" }\n",
    );
    ws.write(
        "Cargo.lock",
        &fixture_cargo_lock_with_dependencies(&[("fln-hash", &["fln-core"])]),
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
        "#![cfg_attr(any(), forbid(unsafe_code))]\n#![deny(clippy::undocumented_unsafe_blocks)]\n",
    );
    assert_eq!(codes(&ordinary.run()), vec!["FLN-STRUCT-011"]);

    let boundary = TempWs::new("conditional-deny");
    base(&boundary);
    boundary.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "#![cfg_attr(any(), deny(unsafe_code))]\n#![deny(clippy::undocumented_unsafe_blocks)]\n",
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
        // The lint line is real and at the root; only the `deny(unsafe_code)` is the decoy,
        // so this plant provokes FLN-STRUCT-012 alone rather than 012 plus 040.
        "#![deny(clippy::undocumented_unsafe_blocks)]\nmod decoy { #![deny(unsafe_code)] }\n",
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
        "#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n#[allow ( unsafe_code, dead_code )]\nfn one() {}\n#[cfg_attr(any(), allow(unsafe_code))]\nfn two() {}\n",
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
            &format!(
                "#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n\
                 #[{level}(unsafe_code)]\nfn lowered() {{}}\n"
            ),
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
        "#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n#![allow(unsafe_code)]\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-013"]);
}

// Renamed at the ez07 repair: the classification is no longer deferred, so a name saying
// "until type-aware classification" would now be the false half of its own assertion. The
// planted `forge<T>` used to fire for ONE reason — it had no row — which ez07's coverage row
// recorded as the suite conceding the gap. It now fires for BOTH, and this asserts both,
// because a single-code assertion cannot tell the two apart.
#[test]
fn unsafe_boundary_exports_fail_closed_by_shape_and_by_caller_chosen_return() {
    let ws = TempWs::new("unsafe-export");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\npub fn forge<T>() -> T { loop {} }\n",
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec!["FLN-STRUCT-022", "FLN-STRUCT-022"]);
    assert!(
        out.findings[0].detail.contains("caller-chosen"),
        "{:?}",
        out.findings[0]
    );
    assert!(
        out.findings[1].detail.contains("undeclared public item"),
        "{:?}",
        out.findings[1]
    );

    let local = TempWs::new("restricted-export");
    base(&local);
    local.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\npub(crate) fn local_only() {}\n",
    );
    assert!(local.run().findings.is_empty());

    let macro_expansion = TempWs::new("macro-expansion");
    base(&macro_expansion);
    macro_expansion.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\nmacro_rules! hidden_policy { () => {} }\n",
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
    assert_eq!(
        codes(&conditional.run()),
        vec!["FLN-STRUCT-015", "FLN-STRUCT-030"]
    );
}

#[test]
fn plan_rank_and_trust_allowlists_cannot_be_weakened() {
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

    let checker_bignum = TempWs::new("checker-bignum-allowlist");
    base(&checker_bignum);
    checker_bignum.write(
        "ci/WORKSPACE_GRAPH.txt",
        &BASE_GRAPH.replace(
            "allow-direct fln-checker = fln-core, fln-hash",
            "allow-direct fln-checker = fln-core, fln-hash, fln-bignum",
        ),
    );
    assert_eq!(codes(&checker_bignum.run()), vec!["FLN-STRUCT-024"]);

    let checker_without_hash = TempWs::new("checker-without-shared-wire-schema");
    base(&checker_without_hash);
    checker_without_hash.write(
        "ci/WORKSPACE_GRAPH.txt",
        &BASE_GRAPH.replace(
            "allow-direct fln-checker = fln-core, fln-hash",
            "allow-direct fln-checker = fln-core",
        ),
    );
    assert_eq!(codes(&checker_without_hash.run()), vec!["FLN-STRUCT-024"]);
}

#[test]
fn plan_defined_crate_cannot_disappear_from_graph_and_disk_together() {
    let ws = TempWs::new("missing-plan-crate");
    base(&ws);
    ws.retain_paths(|path| !path.starts_with("crates/fln-doc/"));
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
        "#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n#[allow(unsafe_code)]\nfn bypass() {}\n",
    );
    assert_eq!(codes(&boundary.run()), vec!["FLN-STRUCT-013"]);
}

#[test]
fn auxiliary_target_cannot_replace_the_declared_product_crate() {
    let ws = TempWs::new("missing-primary-root");
    base(&ws);
    ws.retain_paths(|path| path != "crates/fln-hash/src/lib.rs");
    ws.write(
        "crates/fln-hash/tests/only_target.rs",
        "#![forbid(unsafe_code)]\nfn auxiliary_only() {}\n",
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec!["FLN-STRUCT-016"]);
    assert!(out.findings[0].detail.contains("auxiliary Cargo targets"));
}

#[test]
fn repository_cargo_config_cannot_bypass_the_reviewed_compilation_contract() {
    // Cargo merges `.cargo/config(.toml)` from the invocation directory *upward*, and
    // rustup resolves the toolchain the same way. A file that only the root check can see
    // is therefore not the whole surface: `cd crates/fln-kernel && cargo build` picks up
    // anything planted at or above that directory. Each of these plants a real lint cap
    // (or an alternate toolchain) at a depth the root-only check could not see.
    for (tag, rel) in [
        ("cargo-config-toml", ".cargo/config.toml"),
        ("cargo-config-legacy", ".cargo/config"),
        ("cargo-config-crates-dir", "crates/.cargo/config.toml"),
        (
            "cargo-config-nested-crate",
            "crates/fln-kernel/.cargo/config.toml",
        ),
        (
            "cargo-config-nested-legacy",
            "crates/fln-kernel/.cargo/config",
        ),
        (
            "cargo-config-nested-deep",
            "crates/fln-kernel/src/.cargo/config.toml",
        ),
        ("cargo-config-tools-dir", "tools/.cargo/config.toml"),
    ] {
        let ws = TempWs::new(tag);
        base(&ws);
        ws.write(rel, "[build]\nrustflags = [\"--cap-lints\", \"allow\"]\n");
        let out = ws.run();
        assert_eq!(codes(&out), vec!["FLN-STRUCT-016"], "missed plant at {rel}");
        assert_eq!(out.findings[0].path, rel);
        assert!(
            out.findings[0]
                .detail
                .contains("repository-local Cargo/toolchain configuration")
        );
    }

    // The toolchain half of the same family. `rust-toolchain.toml` at the ROOT is the
    // reviewed pin and must stay legal; its legacy no-suffix spelling is not, because
    // rustup prefers `.toml` when both exist, so the unreviewed file would sit there
    // undetected. Below the root every spelling is forbidden at every depth.
    for (tag, rel) in [
        ("toolchain-legacy-root", "rust-toolchain"),
        (
            "toolchain-nested-crate",
            "crates/fln-kernel/rust-toolchain.toml",
        ),
        (
            "toolchain-nested-legacy",
            "crates/fln-kernel/rust-toolchain",
        ),
        ("toolchain-tools-dir", "tools/rust-toolchain.toml"),
    ] {
        let ws = TempWs::new(tag);
        base(&ws);
        ws.write(rel, "[toolchain]\nchannel = \"stable\"\n");
        let out = ws.run();
        assert_eq!(codes(&out), vec!["FLN-STRUCT-016"], "missed plant at {rel}");
        assert_eq!(out.findings[0].path, rel);
    }

    // Recovery: the reviewed root pin alone is clean, proving the new depth-walk did not
    // start rejecting the one legal member of the family.
    let ws = TempWs::new("cargo-config-clean-recovery");
    base(&ws);
    let out = ws.run();
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
}

/// A governed file the guard cannot decode leaves its structural authority *unestablished*.
/// It must therefore be a typed per-file finding — never a clean run, and never a whole-run
/// abort that masks every other finding (one unreadable byte would otherwise suppress the
/// gate).
#[test]
fn unreadable_governed_source_is_inconclusive_not_clean_and_masks_nothing() {
    const GARBAGE: [u8; 4] = [0xff, 0xfe, 0x00, 0x80];

    // Each of these is a path the guard *does* derive authority from, and each is exactly
    // where a violation would hide behind an undecodable byte: the covenant's counted
    // source closure, the boundary crate's allow-site scan, an ordinary crate's root lint
    // posture, and a package manifest.
    for (tag, rel) in [
        (
            "unreadable-covenant-source",
            "crates/fln-kernel/src/hidden.rs",
        ),
        (
            "unreadable-boundary-source",
            "crates/fln-unsafe-abi/src/hidden.rs",
        ),
        ("unreadable-crate-root", "crates/fln-core/src/lib.rs"),
        ("unreadable-manifest", "crates/fln-core/Cargo.toml"),
    ] {
        let ws = TempWs::new(tag);
        base(&ws);
        ws.write_bytes(rel, &GARBAGE);
        let out = ws.run();
        assert!(
            out.findings
                .iter()
                .any(|f| f.code == "FLN-STRUCT-027" && f.path == rel),
            "{rel} produced no inconclusive finding: {:?}",
            out.findings
        );
        assert!(
            out.findings
                .iter()
                .find(|f| f.code == "FLN-STRUCT-027")
                .is_some_and(|f| f.detail.contains("inconclusive")),
            "finding for {rel} does not report itself as inconclusive: {:?}",
            out.findings
        );
    }

    // The masking property: an unreadable file must not suppress an unrelated, genuine
    // violation found elsewhere in the same run. Before this was localised, the read error
    // propagated to a whole-run exit 2 and the layering violation below was never reported.
    let ws = TempWs::new("unreadable-masks-nothing");
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
    assert!(
        observed.contains(&"FLN-STRUCT-027"),
        "lost the unreadable-input finding: {observed:?}"
    );
    assert!(
        observed.contains(&"FLN-STRUCT-007"),
        "unreadable input masked the upward-edge finding: {observed:?}"
    );

    // Recovery: once the same path decodes, the run is clean again.
    let ws = TempWs::new("unreadable-recovery");
    base(&ws);
    ws.write("crates/fln-kernel/src/hidden.rs", "// now valid UTF-8\n");
    let out = ws.run();
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
}

// ================================================================ FLN-STRUCT-026
// The C-ABI export covenant (bead franken_lean-83r): census ⇄ status-row ⇄
// export-site join, all directions seeded and killed.

fn census_fixture() -> &'static str {
    // The stable one-AbiFn-per-line rendering the covenant's extractor reads.
    "//! @generated fixture for the ABI census/export join.\n\
     pub static FUNCTION_CENSUS: &[AbiFn] = &[\n\
     \x20   AbiFn { name: \"lean_alloc_object\", linkage: Linkage::Export, line: 503 },\n\
     \x20   AbiFn { name: \"lean_apply_1\", linkage: Linkage::Export, line: 827 },\n\
     \x20   AbiFn { name: \"lean_align\", linkage: Linkage::Inline, line: 390 },\n\
     ];\n"
}

fn status_fixture(alloc_status: &str, with_apply_row: bool, with_support: bool) -> String {
    let mut s = String::from("schema fln-abi-export-status/1\n");
    s.push_str(&format!(
        "row lean_alloc_object | {alloc_status} | crates/fln-unsafe-abi/src/lib.rs | suite | membrane\n"
    ));
    if with_apply_row {
        s.push_str(
            "row lean_apply_1 | Unsupported | franken_lean-7xe | census | apply machinery\n",
        );
    }
    if with_support {
        s.push_str(
            "support mi_free | RawPlatform | crates/fln-unsafe-abi/src/lib.rs | suite | mimalloc twin\n",
        );
    }
    s
}

const EXPORTING_LIB: &str = "//! boundary stub\n#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n\n\
    #[unsafe(export_name = \"lean_alloc_object\")]\n\
    extern \"C\" fn export_alloc() {}\n";

#[test]
fn c_export_covenant_clean_join_passes() {
    let ws = TempWs::new("cexport-clean");
    base(&ws);
    ws.write("crates/fln-rt/src/abi.rs", census_fixture());
    ws.write(
        "ci/ABI_EXPORT_STATUS.txt",
        &status_fixture("CompatWrapper", true, false),
    );
    ws.write("crates/fln-unsafe-abi/src/lib.rs", EXPORTING_LIB);
    let out = ws.run();
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
}

#[test]
fn export_site_without_status_file_is_flagged() {
    let ws = TempWs::new("cexport-nofile");
    base(&ws);
    ws.write("crates/fln-rt/src/abi.rs", census_fixture());
    ws.write("crates/fln-unsafe-abi/src/lib.rs", EXPORTING_LIB);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-026"]);
}

#[test]
fn export_site_outside_the_exporting_crate_is_flagged() {
    let ws = TempWs::new("cexport-wrongcrate");
    base(&ws);
    ws.write("crates/fln-rt/src/abi.rs", census_fixture());
    ws.write(
        "ci/ABI_EXPORT_STATUS.txt",
        &status_fixture("CompatWrapper", true, false),
    );
    ws.write("crates/fln-unsafe-abi/src/lib.rs", EXPORTING_LIB);
    ws.write(
        "crates/fln-unsafe-region/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n\n\
         #[unsafe(export_name = \"lean_free_small\")]\n\
         extern \"C\" fn smuggled() {}\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-026"]);
}

#[test]
fn unclassified_census_symbol_is_flagged() {
    let ws = TempWs::new("cexport-unclassified");
    base(&ws);
    ws.write("crates/fln-rt/src/abi.rs", census_fixture());
    // lean_apply_1 has no row: §6.5's "no unclassified symbol" fails.
    ws.write(
        "ci/ABI_EXPORT_STATUS.txt",
        &status_fixture("CompatWrapper", false, false),
    );
    ws.write("crates/fln-unsafe-abi/src/lib.rs", EXPORTING_LIB);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-026"]);
}

#[test]
fn unsupported_row_with_live_site_is_flagged() {
    let ws = TempWs::new("cexport-lie");
    base(&ws);
    ws.write("crates/fln-rt/src/abi.rs", census_fixture());
    ws.write(
        "ci/ABI_EXPORT_STATUS.txt",
        &status_fixture("Unsupported", true, false),
    );
    ws.write("crates/fln-unsafe-abi/src/lib.rs", EXPORTING_LIB);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-026"]);
}

#[test]
fn stale_implemented_row_without_site_is_flagged() {
    let ws = TempWs::new("cexport-stale");
    base(&ws);
    ws.write("crates/fln-rt/src/abi.rs", census_fixture());
    ws.write(
        "ci/ABI_EXPORT_STATUS.txt",
        &status_fixture("CompatWrapper", true, false),
    );
    // Boundary crate carries no site: the CompatWrapper claim is stale.
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-026"]);
}

#[test]
fn unknown_row_symbol_and_shadowing_support_row_are_flagged() {
    let ws = TempWs::new("cexport-unknown");
    base(&ws);
    ws.write("crates/fln-rt/src/abi.rs", census_fixture());
    // (duplicate symbols are rejected at the parser layer — export_status
    // unit tests cover that; here every row symbol is unique.)
    let mut status = status_fixture("CompatWrapper", false, false);
    status.push_str("row lean_not_in_census | Unsupported | somewhere | census | ghost\n");
    status.push_str(
        "support lean_apply_1 | RawPlatform | crates/fln-unsafe-abi/src/lib.rs | suite | shadow\n",
    );
    ws.write("ci/ABI_EXPORT_STATUS.txt", &status);
    ws.write("crates/fln-unsafe-abi/src/lib.rs", EXPORTING_LIB);
    // Three findings, one defect family: the unknown row symbol, the support
    // row shadowing a census symbol, and that implemented support row having
    // no export site (stale claim).
    let out = ws.run();
    assert_eq!(out.findings.len(), 3, "unexpected: {:?}", out.findings);
    assert!(out.findings.iter().all(|f| f.code == "FLN-STRUCT-026"));
}

#[test]
fn no_mangle_stays_banned_and_split_symbol_fails_closed() {
    let ws = TempWs::new("cexport-nomangle");
    base(&ws);
    ws.write("crates/fln-rt/src/abi.rs", census_fixture());
    ws.write(
        "ci/ABI_EXPORT_STATUS.txt",
        &status_fixture("CompatWrapper", true, false),
    );
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n\n\
         #[unsafe(export_name = \"lean_alloc_object\")]\n\
         extern \"C\" fn export_alloc() {}\n\n\
         #[unsafe(no_mangle)]\n\
         extern \"C\" fn lean_smuggled() {}\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-022"]);

    // A symbol string the extractor cannot recover exactly fails closed.
    let ws2 = TempWs::new("cexport-split");
    base(&ws2);
    ws2.write("crates/fln-rt/src/abi.rs", census_fixture());
    ws2.write(
        "ci/ABI_EXPORT_STATUS.txt",
        &status_fixture("CompatWrapper", true, false),
    );
    ws2.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n\n\
         #[unsafe(export_name =\n\"lean_alloc_object\")]\n\
         extern \"C\" fn export_alloc() {}\n",
    );
    // The unextractable site fails closed AND the implemented row goes stale
    // (no joined site) — two findings, one defect.
    let out = ws2.run();
    assert_eq!(out.findings.len(), 2, "unexpected: {:?}", out.findings);
    assert!(out.findings.iter().all(|f| f.code == "FLN-STRUCT-026"));
}

#[test]
fn missing_census_fails_closed_when_status_exists() {
    let ws = TempWs::new("cexport-nocensus");
    base(&ws);
    // Status file present, census absent: the join cannot be verified.
    ws.write(
        "ci/ABI_EXPORT_STATUS.txt",
        &status_fixture("CompatWrapper", true, false),
    );
    ws.write("crates/fln-unsafe-abi/src/lib.rs", EXPORTING_LIB);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-026"]);
}

// ---------------------------------------------------------------- fln-checker boundary

/// The SAFETY-note posture rule (`FLN-STRUCT-040`, bead
/// `franken_lean-d3-safety-note-unenforced-cdbg`).
///
/// D3 requires a SAFETY note at every unsafe site. That half of the rule is decided by
/// `clippy::undocumented_unsafe_blocks` and by nothing else, and this guard does NOT
/// re-implement it — deciding whether a block is documented needs a parser, and a second
/// implementation of one property is how the two disagree. What it enforces is that a
/// boundary crate either turns the lint on or says out loud that it has not.
///
/// Three plants, because the rule has three outcomes and a guard that only ever fires one
/// way is an unenforced claim.
#[test]
fn a_boundary_root_silent_about_the_safety_note_lint_is_refused() {
    let ws = TempWs::new("safety-note-silent");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-jit/src/lib.rs",
        "//! stub\n#![deny(unsafe_code)]\n",
    );
    let out = ws.run();
    assert!(
        codes(&out).contains(&"FLN-STRUCT-040"),
        "a boundary root that neither enforces nor declares must be refused: {:?}",
        out.findings
    );
    assert!(
        out.findings
            .iter()
            .any(|f| f.code == "FLN-STRUCT-040" && f.detail.contains("fln-unsafe-jit")),
        "the finding must name the crate it refused: {:?}",
        out.findings
    );
}

/// PERMISSION HALF ONE: turning the lint on satisfies the rule.
#[test]
fn a_boundary_root_that_enables_the_lint_is_accepted() {
    let ws = TempWs::new("safety-note-enforced");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-jit/src/lib.rs",
        "//! stub\n#![deny(unsafe_code)]\n#![deny(clippy::undocumented_unsafe_blocks)]\n",
    );
    let out = ws.run();
    assert!(
        !codes(&out).contains(&"FLN-STRUCT-040"),
        "enforcing the lint must satisfy the rule: {:?}",
        out.findings
    );
}

/// PERMISSION HALF TWO: declaring that it is not yet on, with the bead, also satisfies it.
/// The waiver is the whole point — an unenforced rule is survivable, an unenforced rule
/// nobody can see is the defect.
#[test]
fn a_boundary_root_that_declares_the_gap_with_a_bead_is_accepted() {
    let ws = TempWs::new("safety-note-waived");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-jit/src/lib.rs",
        "//! stub\n#![deny(unsafe_code)]\n// UNSAFE-NOTE-WAIVER: franken_lean-some-bead-abcd\n",
    );
    let out = ws.run();
    assert!(
        !codes(&out).contains(&"FLN-STRUCT-040"),
        "a declared gap naming a bead must be accepted: {:?}",
        out.findings
    );
}

/// A waiver that names nothing is a shrug, not a declaration, and must not satisfy the
/// rule — otherwise the marker becomes a way to switch the guard off.
#[test]
fn a_waiver_naming_no_bead_does_not_satisfy_the_rule() {
    for bare in ["// UNSAFE-NOTE-WAIVER:", "// UNSAFE-NOTE-WAIVER: todo"] {
        let ws = TempWs::new("safety-note-bare-waiver");
        base(&ws);
        ws.write(
            "crates/fln-unsafe-jit/src/lib.rs",
            &format!("//! stub\n#![deny(unsafe_code)]\n{bare}\n"),
        );
        let out = ws.run();
        assert!(
            codes(&out).contains(&"FLN-STRUCT-040"),
            "a waiver naming no bead must not satisfy the rule ({bare:?}): {:?}",
            out.findings
        );
    }
}

/// The marker is comment-only, mirroring the UNSAFE-LEDGER discipline: a string literal
/// that happens to contain it must not waive a crate. Without this the rule would be
/// defeatable by a doc example.
#[test]
fn a_waiver_inside_a_string_literal_does_not_waive_the_crate() {
    let ws = TempWs::new("safety-note-string-waiver");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-jit/src/lib.rs",
        "//! stub\n#![deny(unsafe_code)]\npub const S: &str = \"UNSAFE-NOTE-WAIVER: franken_lean-not-real-abcd\";\n",
    );
    let out = ws.run();
    assert!(
        codes(&out).contains(&"FLN-STRUCT-040"),
        "a marker inside a string literal must not waive the crate: {:?}",
        out.findings
    );
}

/// The independence boundary (`FLN-STRUCT-037`, bead `franken_lean-r0xu`).
///
/// The rule is vacuous against the real tree today, because `fln-checker` is a
/// charter crate with no checking code. A guard that has only ever been observed
/// passing is an unenforced claim, which is the failure class this suite exists
/// to prevent — so every entry in the semantic inventory is planted here and
/// asserted to fire.
/// Read from the rule itself, never transcribed beside it.
///
/// This was a hand-written `[&str; 12]` until the inventory was made `pub`. The copy
/// agreed with `checks::CHECKER_SEMANTIC` on the day it was written and nothing joined
/// them, so a thirteenth item added to the rule would have left this campaign planting
/// twelve: the new item's violation would never have been attempted, and the suite
/// would have stayed green while covering less than it claims. The copy had already
/// begun to rot in the direction nothing checks — the doc comment above it called the
/// inventory "eleven items" after it had grown to twelve.
fn checker_semantic_inventory() -> Vec<&'static str> {
    checks::CHECKER_SEMANTIC
        .iter()
        .map(|(name, _)| *name)
        .collect()
}

#[test]
fn the_checker_boundary_baseline_is_clean() {
    let ws = TempWs::new("checker-boundary-baseline");
    base(&ws);
    let out = ws.run();
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
}

/// One planted violation per inventory item. Each must fire on its own, so a
/// single over-broad matcher cannot make the suite look green.
#[test]
fn every_semantic_item_is_refused_inside_fln_checker() {
    for item in checker_semantic_inventory() {
        let ws = TempWs::new(&format!("checker-boundary-{item}"));
        base(&ws);
        ws.write(
            "crates/fln-checker/src/lib.rs",
            &format!(
                "//! stub\n#![forbid(unsafe_code)]\n\npub fn probe() -> bool {{\n    {item}()\n}}\n"
            ),
        );
        let out = ws.run();
        assert_eq!(
            codes(&out),
            vec!["FLN-STRUCT-037"],
            "planting `{item}` inside fln-checker was not refused"
        );
        assert!(
            out.findings[0].detail.contains(item),
            "the finding must name the item it refused: {:?}",
            out.findings[0]
        );
    }
}

/// The property that makes the rule usable at all: the file that DEFINES the
/// boundary necessarily names every forbidden symbol in prose, so a substring
/// matcher would flag the boundary document itself. Lexing must see through
/// line comments, block comments and string literals.
///
/// Without this the rule would have been self-defeating — the real
/// `crates/fln-checker/src/lib.rs` names every item in the inventory in its doc
/// comments, and now carries a machine-readable registry of them besides. The count
/// is deliberately not written here: this comment said "eleven" for as long as the
/// inventory had twelve entries, which is the same rot in miniature.
#[test]
fn naming_a_semantic_item_in_prose_is_not_a_violation() {
    let ws = TempWs::new("checker-boundary-prose");
    base(&ws);
    let mut src = String::from("//! stub\n#![forbid(unsafe_code)]\n");
    for item in checker_semantic_inventory() {
        src.push_str(&format!("//! never call `{item}` from this crate.\n"));
        src.push_str(&format!("/* block: {item} is SEMANTIC */\n"));
    }
    src.push_str("pub fn doc() -> &'static str {\n    \"is_equiv fln_bignum read_body\"\n}\n");
    ws.write("crates/fln-checker/src/lib.rs", &src);
    let out = ws.run();
    assert!(
        out.findings.is_empty(),
        "prose and string literals must not trip the boundary: {:?}",
        out.findings
    );
}

/// The refusal is scoped to `fln-checker`. The same identifiers are ordinary
/// code elsewhere — `fln-kernel` calls `is_equiv` and `has_fvar` constantly —
/// so a rule that fired workspace-wide would be unusable.
#[test]
fn the_boundary_is_scoped_to_fln_checker_alone() {
    let ws = TempWs::new("checker-boundary-scope");
    base(&ws);
    ws.write(
        "crates/fln-env/src/lib.rs",
        "//! stub\n#![forbid(unsafe_code)]\n\npub fn probe() -> bool {\n    is_equiv()\n}\n",
    );
    let out = ws.run();
    assert!(
        out.findings.is_empty(),
        "the boundary must not fire outside fln-checker: {:?}",
        out.findings
    );
}

// ---- declaration-admission surface (bead franken_lean-oof9) ---------------------------
//
// D6 reserves admission to the kernel. `fln-yswb` and `ukzx` made that true by migrating
// every production caller off the raw surface; these tests make it true by CI, which is
// the strongest mechanism available at this boundary — fln-env sits BELOW fln-kernel and
// so can never name a kernel-bound capability type.

/// A crate that depends on fln-env and admits nothing is clean.
///
/// Without this, every test below could pass because the scan never ran.
#[test]
fn the_admission_surface_baseline_is_clean() {
    let ws = TempWs::new("admission-baseline");
    base(&ws);
    admission_dependent(&ws);
    ws.write(
        "crates/fln-kernel/src/lib.rs",
        "//! stub\n#![forbid(unsafe_code)]\n\npub fn probe() -> bool {\n    true\n}\n",
    );
    let out = ws.run();
    assert!(
        out.findings.is_empty(),
        "a dependent that admits nothing must be clean: {:?}",
        out.findings
    );
}

/// The raw surface has an EMPTY allowlist: a first production caller is the violation.
#[test]
fn raw_declaration_admission_is_refused_outside_fln_env() {
    let ws = TempWs::new("admission-raw");
    base(&ws);
    admission_dependent(&ws);
    ws.write(
        "crates/fln-kernel/src/lib.rs",
        "//! stub\n#![forbid(unsafe_code)]\n\npub fn admit(env: &Env, info: Info) -> Env {\n    \
         env.add_decl(info)\n}\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-038"]);
}

/// THE DISCRIMINATION TEST, and the reason this rule matches arity rather than a name.
///
/// `fln_hash::LogicalRootBuilder::add_decl(name, digest)` is an unrelated method that
/// happens to share a name, in a crate at rank 1 that cannot even depend on fln-env. It
/// has fifteen real call sites, and it coexists with the fln-env method inside one file
/// this guard scans, so crate-scoping cannot separate them. A name match reports every
/// one of them as a violation of a rule about a different crate.
#[test]
fn the_two_argument_add_decl_of_another_type_is_not_a_violation() {
    let ws = TempWs::new("admission-arity");
    base(&ws);
    admission_dependent(&ws);
    ws.write(
        "crates/fln-kernel/src/lib.rs",
        "//! stub\n#![forbid(unsafe_code)]\n\npub fn root(builder: &mut B, name: &N, digest: D) {\n    \
         builder.add_decl(name, digest);\n}\n",
    );
    let out = ws.run();
    assert!(
        out.findings.is_empty(),
        "a two-argument `add_decl` is another type's method: {:?}",
        out.findings
    );
}

/// The planned surface is allowlisted to two reviewed kernel files, by PATH. A call from
/// any other file in a dependent crate is the violation.
#[test]
fn planned_admission_is_refused_outside_the_allowlisted_kernel_files() {
    let ws = TempWs::new("admission-planned");
    base(&ws);
    admission_dependent(&ws);
    ws.write(
        "crates/fln-kernel/src/lib.rs",
        "//! stub\n#![forbid(unsafe_code)]\n\npub fn plan(env: &Env, info: Info) -> P {\n    \
         env.plan_add_decl(\n        info,\n        budget,\n        collisions,\n        cancellation,\n    )\n}\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-039"]);
}

/// Scoped to crates that declare an edge to fln-env. Everything else provably cannot
/// call these methods, and a rule that fired workspace-wide would be unusable.
#[test]
fn the_admission_surface_is_scoped_to_fln_env_dependents() {
    let ws = TempWs::new("admission-scope");
    base(&ws);
    ws.write(
        "crates/fln-kernel/src/lib.rs",
        "//! stub\n#![forbid(unsafe_code)]\n\npub fn admit(env: &Env, info: Info) -> Env {\n    \
         env.add_decl(info)\n}\n",
    );
    let out = ws.run();
    assert!(
        out.findings.is_empty(),
        "with no declared edge to fln-env the scan must not reach this crate: {:?}",
        out.findings
    );
}

/// Prose and string literals naming the method are not calls.
///
/// This is load-bearing rather than decorative: `fln-verdict` guards this very method by
/// asserting its own source lacks the text, and writes the literal split
/// (`concat!(".plan_", "add_decl(")`) precisely so a substring scanner does not match it.
/// A lexeme scanner does not need that workaround, and this pins that it does not.
#[test]
fn naming_the_admission_methods_in_prose_is_not_a_violation() {
    let ws = TempWs::new("admission-prose");
    base(&ws);
    admission_dependent(&ws);
    ws.write(
        "crates/fln-kernel/src/lib.rs",
        "//! stub\n#![forbid(unsafe_code)]\n//! never call `add_decl` or `plan_add_decl` here.\n\
         /* block: .add_decl(x) and .plan_add_decl(a, b) are forbidden */\n\
         pub fn doc() -> &'static str {\n    \".add_decl(info) .plan_add_decl(a, b, c, d)\"\n}\n",
    );
    let out = ws.run();
    assert!(
        out.findings.is_empty(),
        "prose and string literals must not trip the surface: {:?}",
        out.findings
    );
}

/// Declaring the edge, the manifest dependency and the lock entry that together put a
/// crate in the scan set. All three, because this guard cross-checks them against each
/// other and a fixture that declares only the edge fails on the disagreement instead of
/// on the thing under test.
fn admission_dependent(ws: &TempWs) {
    ws.write(
        "crates/fln-kernel/Cargo.toml",
        &manifest("fln-kernel", &["fln-env"]),
    );
    ws.write(
        "Cargo.lock",
        &fixture_cargo_lock_with_dependencies(&[("fln-kernel", &["fln-env"])]),
    );
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-kernel -> fln-env"]),
    );
}

// ---------------------------------------------------------------------------
// FLN-STRUCT-041 — Python import shadowing of the trusted evidence bootstrap
// (bead `franken_lean-h40t`)
// ---------------------------------------------------------------------------

/// THE PLANTED VIOLATION. `scripts/evidence.py` computes the governed tree
/// hashes and decides the verdicts every gate depends on, and Python resolves
/// the running script's OWN DIRECTORY before the standard library. So a file
/// named `scripts/hashlib.py` replaces the module that computes the digests.
///
/// This was invisible until the rule existed: `GOVERNED_ROOT_DIRS` is `ci`,
/// `contracts`, `crates`, `tools`, so `scripts/` was outside the guard's
/// universe entirely and nothing in `checks.rs` had ever looked at a `.py`.
///
/// The sibling defect was PROVEN live on the CI surface under `fln-8mj`: with a
/// shadow module on the path, `tomllib.loads("")` returned
/// `{"toolchain": {"channel": "attacker-chosen-toolchain"}}`.
#[test]
fn a_python_module_shadowing_a_trusted_import_is_refused() {
    let ws = TempWs::new("python-shadow");
    base(&ws);
    ws.write("scripts/evidence.py", "import hashlib\nimport json\n");
    ws.write("scripts/hashlib.py", "def sha256(*_a, **_k):\n    pass\n");
    let out = ws.run();
    assert!(
        codes(&out).contains(&"FLN-STRUCT-041"),
        "a module shadowing a trusted import must be refused: {:?}",
        out.findings
    );
    assert!(
        out.findings
            .iter()
            .any(|f| f.code == "FLN-STRUCT-041" && f.path.contains("scripts/hashlib.py")),
        "the finding must name the shadowing file: {:?}",
        out.findings
    );
}

/// THE DISCRIMINATION TEST, and the reason the shadowable set is DERIVED rather
/// than hand-listed. `scripts/helper.py` is not a module the bootstrap imports,
/// so it shadows nothing and must not be refused. A rule that flagged every
/// `.py` beside the runner would be refusing the runner's own toolbox, and the
/// first person it inconvenienced would widen it to nothing.
#[test]
fn a_python_module_that_shadows_nothing_is_not_a_violation() {
    let ws = TempWs::new("python-innocent");
    base(&ws);
    ws.write("scripts/evidence.py", "import hashlib\n");
    ws.write("scripts/helper.py", "VALUE = 1\n");
    let out = ws.run();
    assert!(
        !codes(&out).contains(&"FLN-STRUCT-041"),
        "a module that shadows no trusted import must be accepted: {:?}",
        out.findings
    );
}

/// THE SET TRACKS THE IMPORTS. The same shadow file becomes a violation the
/// moment the bootstrap starts importing that name — which is exactly what a
/// hand-written list of dangerous names would have missed, silently, while the
/// surface grew. FLN-STRUCT-039 made the same choice for the same reason.
#[test]
fn the_shadowable_set_follows_what_the_bootstrap_actually_imports() {
    let ws = TempWs::new("python-derived-set");
    base(&ws);
    ws.write("scripts/evidence.py", "import json\n");
    ws.write("scripts/tomllib.py", "def loads(*_a, **_k):\n    pass\n");
    assert!(
        !codes(&ws.run()).contains(&"FLN-STRUCT-041"),
        "tomllib is not imported yet, so nothing is shadowed"
    );

    let ws = TempWs::new("python-derived-set-grown");
    base(&ws);
    ws.write("scripts/evidence.py", "import json\nimport tomllib\n");
    ws.write("scripts/tomllib.py", "def loads(*_a, **_k):\n    pass\n");
    assert!(
        codes(&ws.run()).contains(&"FLN-STRUCT-041"),
        "once the bootstrap imports tomllib, the same file shadows it"
    );
}

/// THE CWD VECTOR. Inline `python3 -c` helpers in the shell lanes resolve from
/// the process working directory, so a module at the repository ROOT shadows
/// for them even though no trusted script lives beside it.
#[test]
fn a_repository_root_module_shadowing_a_trusted_import_is_refused() {
    let ws = TempWs::new("python-shadow-root");
    base(&ws);
    ws.write("scripts/evidence.py", "import hashlib\n");
    ws.write("hashlib.py", "def sha256(*_a, **_k):\n    pass\n");
    let out = ws.run();
    assert!(
        out.findings
            .iter()
            .any(|f| f.code == "FLN-STRUCT-041" && f.path == "hashlib.py"),
        "the cwd vector must be refused at the repository root: {:?}",
        out.findings
    );
}

/// THE BASELINE. Without it the four plants above could all be passing because
/// the rule refuses everything.
#[test]
fn the_python_shadow_baseline_is_clean() {
    let ws = TempWs::new("python-shadow-clean");
    base(&ws);
    ws.write("scripts/evidence.py", "import hashlib\nimport json\n");
    assert!(
        !codes(&ws.run()).contains(&"FLN-STRUCT-041"),
        "a bootstrap with no shadow beside it must scan clean"
    );
}

// ---------------------------------------------------------------------------
// D18 mode closure (bead franken_lean-r2st)
//
// The registration chain is real — ci.yml runs scripts/check.sh, whose
// `structure-guard` stage runs the guard binary, whose `checks::run` calls
// `mode_closure::audit_with_facts`, which calls `fln_core::mode::scan_mode_closure`.
// The unit tests in `mode_closure.rs` already drive that extractor over synthetic
// graph and manifest TEXT, and they are good tests.
//
// What none of them establish is the last link: that a planted D18 defect in a real
// on-disk workspace makes the REGISTERED GUARD RUN go red, with the core's stable
// code surviving translation and a non-zero exit code reaching check.sh. A check can
// be wired in and still return findings nobody acts on. That is the `pnav` shape from
// AGENTS.md item 7 one floor down — an assertion and the lane it delegates to — so it
// gets the same treatment: plant it, prove the run fails, repair it, prove recovery.
// ---------------------------------------------------------------------------

/// A Sound product root reaching a crate that declares a real frontier feature.
///
/// The dependency is backed at all three layers the guard cross-checks — governed graph
/// edge, manifest dependency, and `Cargo.lock` closure — so the only thing the plant
/// varies is the frontier surface itself. An edge backed at fewer layers trips
/// `FLN-STRUCT-006` or `FLN-STRUCT-018`, and a plant that trips two checks proves neither.
fn plant_frontier_into_sound(ws: &TempWs, frontier_feature: &str, jit_provenance: &str) {
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-cli -> fln-unsafe-jit"]),
    );
    ws.write(
        "Cargo.lock",
        &fixture_cargo_lock_with_dependencies(&[("fln-cli", &["fln-unsafe-jit"])]),
    );
    ws.write(
        "crates/fln-cli/Cargo.toml",
        &format!(
            "# fln-product-root: sound\n# fln-mode-provenance: sound\n{}",
            manifest("fln-cli", &["fln-unsafe-jit"])
        ),
    );
    ws.write(
        "crates/fln-unsafe-jit/Cargo.toml",
        &format!(
            "# fln-mode-provenance: {jit_provenance}\n{}{frontier_feature}",
            manifest("fln-unsafe-jit", &[])
        ),
    );
}

#[test]
fn planted_frontier_reaching_a_sound_product_root_fails_the_guard_run() {
    let ws = TempWs::new("d18-frontier-into-sound");
    base(&ws);
    plant_frontier_into_sound(&ws, "\n[features]\niron = []\n", "frontier");
    let out = ws.run();
    assert!(
        codes(&out).contains(&"FLN-D18-001"),
        "a frontier surface reachable from a Sound product root must be refused by the \
         REGISTERED guard, with the core's stable code surviving translation: {:?}",
        out.findings
    );
    assert_ne!(
        out.exit_code(),
        0,
        "a D18 refusal must make the guard run fail; a finding the run does not act on \
         is a check that is wired in and inert"
    );
}

/// The repair half. Without it the plant above could be failing for a reason unrelated
/// to the frontier feature — the edge, the product-root marker, or the manifest shape.
#[test]
fn removing_the_frontier_feature_recovers_the_sound_closure() {
    let ws = TempWs::new("d18-frontier-repaired");
    base(&ws);
    // Identical to the planted fixture except that the frontier feature is gone and the
    // marker no longer claims a frontier binding the structure does not support. Removing
    // only the feature leaves ModeBound(Frontier) contradicting a Neutral requirement,
    // which the scanner refuses as FLN-D18-004 — correctly, and it is a different defect
    // than the one under repair.
    plant_frontier_into_sound(&ws, "", "neutral");
    let out = ws.run();
    assert!(
        !codes(&out).iter().any(|code| code.starts_with("FLN-D18-")),
        "with the frontier feature removed the same closure must be admitted: {:?}",
        out.findings
    );
}

// ---- D3 law (b): the declared surface type is bound to the real signature --------------
// (bead `fln-boundary-api-no-admission-argument-discarded-ez07`)
//
// Field 4 of `ci/BOUNDARY_API.txt` — the surface type every no-admission argument of the
// form "value copy" or "plain-int snapshot" is a claim ABOUT — used to be checked non-empty
// and then discarded, so a row could declare `() -> bool` for a function returning anything
// at all. Measured before the repair, with a matching row so the inventory check passed:
// a laundering return hidden behind a private alias produced ZERO findings, while the same
// export naming an admission token was already refused by the tripwire. So the covenant
// refused laundering by NAMING and accepted a declared type that was simply false.
#[test]
fn boundary_api_surface_type_is_bound_to_the_signature() {
    let api = |surface: &str| {
        format!(
            "schema fln-boundary-api/1\n\
             row FLN-BX-0001 | crates/fln-unsafe-abi/src/lib.rs | fn mint | {surface} \
             | fixture | fixture\n"
        )
    };
    let stub = "//! boundary stub\n#![deny(unsafe_code)]\n\
                #![deny(clippy::undocumented_unsafe_blocks)]\n";
    let plant = |name: &str, surface: &str, body: &str| {
        let ws = TempWs::new(name);
        base(&ws);
        ws.write("ci/BOUNDARY_API.txt", &api(surface));
        ws.write("crates/fln-unsafe-abi/src/lib.rs", &format!("{stub}{body}"));
        ws.run()
    };

    // A — the defect itself: the row declares a plain-data surface, the signature does not.
    let a = plant(
        "ez07-lie",
        "() -> bool",
        "type Decl = u64;\npub fn mint() -> Decl { 0 }\n",
    );
    assert_eq!(codes(&a), vec!["FLN-STRUCT-022"]);
    // The refusal must name BOTH types. One side alone cannot be acted on.
    assert!(
        a.findings[0].detail.contains("`bool`"),
        "{:?}",
        a.findings[0]
    );
    assert!(
        a.findings[0].detail.contains("`Decl`"),
        "{:?}",
        a.findings[0]
    );

    // B — THE CORRECT REPAIR MUST STAY GREEN. This is the wall detector, and the only cell
    // that fails if `fn_return_type` silently stops recovering anything: the refusal cells
    // below would all still pass against an extractor that always returned `None`.
    let b = plant(
        "ez07-repaired",
        "() -> Decl",
        "type Decl = u64;\npub fn mint() -> Decl { 0 }\n",
    );
    assert!(
        b.findings.is_empty(),
        "a correct repair must not redden: {:?}",
        b.findings
    );

    // C — the row declares a return the signature does not have.
    let c = plant("ez07-phantom", "() -> bool", "pub fn mint() {}\n");
    assert_eq!(codes(&c), vec!["FLN-STRUCT-022"]);
    assert!(
        c.findings[0].detail.contains("no return type"),
        "{:?}",
        c.findings[0]
    );

    // D — the row understates: a real return, none declared.
    let d = plant("ez07-understated", "()", "pub fn mint() -> u64 { 0 }\n");
    assert_eq!(codes(&d), vec!["FLN-STRUCT-022"]);
    assert!(
        d.findings[0].detail.contains("`u64`"),
        "{:?}",
        d.findings[0]
    );

    // E — SCOPE. Non-`fn` rows carry prose rather than a signature and must stay unbound;
    // without this the 66 real rows redden, since `mod`/`struct`/`field` field-4 values are
    // descriptions. The bound half is field 4 of `fn` rows and nothing wider.
    let e = TempWs::new("ez07-prose-scope");
    base(&e);
    e.write(
        "ci/BOUNDARY_API.txt",
        "schema fln-boundary-api/1\n\
         row FLN-BX-0001 | crates/fln-unsafe-abi/src/lib.rs | struct Handle \
         | opaque owned reference, prose not a signature | fixture | fixture\n",
    );
    e.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        &format!("{stub}pub struct Handle(u8);\n"),
    );
    assert!(
        e.run().findings.is_empty(),
        "non-fn rows carry prose and must stay unbound"
    );
}

// ---- D3 law (b): a caller-chosen return type is refused, row or no row ------------------
// (bead `fln-boundary-api-no-admission-argument-discarded-ez07`)
//
// This is the negative control for the law as WRITTEN — "no unsafe crate exports any
// function whose return type can be laundered into a checked declaration". Binding the
// declared surface type to the signature (above) closes the ROT hole: the row can no
// longer lie. It does nothing about a declared type that is itself launderable, and
// `-> T` is the purest such signature, because the CALLER picks the type.
//
// It is also the one vector the dependency law cannot carry. AGENTS.md's D3 paragraph
// argued that FLN-STRUCT-008 does law (b)'s work "since a boundary crate that cannot
// depend on the kernel cannot name a kernel type" — true, and irrelevant here: a generic
// return names nothing. Measured before this check, with a matching row so the inventory
// dimension passed: ZERO findings.
#[test]
fn a_caller_chosen_return_type_is_refused_even_with_a_reviewed_row() {
    let stub = "//! boundary stub\n#![deny(unsafe_code)]\n\
                #![deny(clippy::undocumented_unsafe_blocks)]\n";
    let plant = |name: &str, rows: &str, body: &str| {
        let ws = TempWs::new(name);
        base(&ws);
        ws.write(
            "ci/BOUNDARY_API.txt",
            &format!("schema fln-boundary-api/1\n{rows}"),
        );
        ws.write("crates/fln-unsafe-abi/src/lib.rs", &format!("{stub}{body}"));
        ws.run()
    };
    let mint = |surface: &str| {
        format!(
            "row FLN-BX-0001 | crates/fln-unsafe-abi/src/lib.rs | fn mint | {surface} \
             | fixture | fixture\n"
        )
    };

    // A — THE CONTROL. A truthful row for a laundering export. Field 4 says exactly what
    // the signature says, so the surface-type binding is satisfied and cannot fire; only a
    // check that reads the type as launderable refuses this.
    let a = plant(
        "ez07-generic-return",
        &mint("() -> T"),
        "pub fn mint<T>() -> T { loop {} }\n",
    );
    assert_eq!(codes(&a), vec!["FLN-STRUCT-022"]);
    assert!(a.findings[0].detail.contains("`T`"), "{:?}", a.findings[0]);
    assert!(
        a.findings[0].detail.contains("caller-chosen"),
        "the refusal must say WHY, or the next author will add a row and move on: {:?}",
        a.findings[0]
    );

    // B — a wrapper launders too: the caller indexes the `Vec` and holds a `T`. Mention,
    // not equality, is the property.
    let b = plant(
        "ez07-generic-wrapper",
        &mint("() -> Vec<T>"),
        "pub fn mint<T>() -> Vec<T> { Vec::new() }\n",
    );
    assert_eq!(codes(&b), vec!["FLN-STRUCT-022"]);
    assert!(b.findings[0].detail.contains("`T`"), "{:?}", b.findings[0]);

    // C — the same signature written one level up. An enclosing `impl<T>` binds the
    // parameter for every method inside it, so scoping the rule to the fn's OWN generic
    // list would leave a one-line bypass.
    let c = plant(
        "ez07-impl-scope",
        "row FLN-BX-0001 | crates/fln-unsafe-abi/src/lib.rs | struct Holder \
         | opaque owned handle | fixture | fixture\n\
         row FLN-BX-0002 | crates/fln-unsafe-abi/src/lib.rs | fn get | (&self) -> T \
         | fixture | fixture\n",
        "pub struct Holder<T>(T);\nimpl<T> Holder<T> { pub fn get(self) -> T { self.0 } }\n",
    );
    assert_eq!(codes(&c), vec!["FLN-STRUCT-022"]);
    assert!(c.findings[0].detail.contains("`T`"), "{:?}", c.findings[0]);

    // D — THE WALL DETECTOR, and the cell that keeps the rule honest about what it
    // forbids. A generic export is not per se a violation: what is refused is a return
    // the caller chooses. `Tally` also CONTAINS `T`, so a substring test reddens here
    // while a token test does not.
    let d = plant(
        "ez07-concrete-return",
        &mint("(T) -> Tally"),
        "type Tally = u64;\npub fn mint<T>(seed: T) -> Tally { 0 }\n",
    );
    assert!(
        d.findings.is_empty(),
        "a generic fn with a concrete return must stay green: {:?}",
        d.findings
    );

    // E — `impl Holder<u8>` is a USE of `u8`, not a binder. Reading it as one would put
    // every concrete type argument in scope and redden the matching return.
    let e = plant(
        "ez07-impl-use-not-binder",
        "row FLN-BX-0001 | crates/fln-unsafe-abi/src/lib.rs | struct Holder \
         | opaque owned handle | fixture | fixture\n\
         row FLN-BX-0002 | crates/fln-unsafe-abi/src/lib.rs | fn get | (&self) -> u8 \
         | fixture | fixture\n",
        "pub struct Holder<T>(T);\nimpl Holder<u8> { pub fn get(&self) -> u8 { self.0 } }\n",
    );
    assert!(
        e.findings.is_empty(),
        "a concrete type argument is not a bound parameter: {:?}",
        e.findings
    );
}

/// `data_grade` must be `verified` EXACTLY when a contract-handoff root was established,
/// in both directions — and the fixture that supplies the negative direction is the krb0
/// defect itself, reproduced by moving one variable (bead
/// `fln-census-empty-referent-no-mock-krb0`; schema change routed to cc_2 and judged in
/// `/data/tmp/claude-1000/route-cc_2-to-cc_3-krb0-schema-verdict.md`).
///
/// The control is the whole point and it is asserted rather than described: the two runs
/// agree on `verdict`, on `authority` and on the finding count, so every field a reader
/// currently has to judge a tree by is byte-identical across an audited tree and an
/// unaudited one. Measured at `a0c9b1c8` in a real fresh clone; reproduced here in 0.2 s.
/// Without that equality this test would pass just as well against a grade wired to
/// `verdict`, which would carry no new information at all.
///
/// **This asserts the DERIVATION, not the artifact.** Neither field is rendered into the
/// `structure-guard/4` robot stream yet: `scripts/evidence.py`'s `require_guard_keys`
/// compares the terminal key set for exact equality, so emitting them is a `/5` bump that
/// must move the producer, the validator and its fixtures together, and two of those live
/// in another pane's uncommitted file. No record claims this grade today.
#[test]
fn the_data_grade_is_the_only_field_that_separates_an_unaudited_tree() {
    let audited = TempWs::new("krb0-grade-audited");
    base(&audited);
    let audited = audited.run();

    // One variable: a single census shard absent, exactly as on a fresh clone where the
    // shards are gitignored and unreachable from main (bead `fln-census-out-of-git-2ya9`).
    let unaudited = TempWs::new("krb0-grade-unaudited");
    base(&unaudited);
    unaudited.retain_paths(|rel| rel != "contracts/builtin_environment.tsv");
    let unaudited = unaudited.run();

    // THE CONTROL. If these three ever diverge, the fixture has stopped isolating the one
    // variable and the directions below prove nothing about this field's information.
    assert_eq!(
        audited.verdict(),
        unaudited.verdict(),
        "fixture no longer isolates one variable: the verdicts differ"
    );
    assert_eq!(
        audited.authority, unaudited.authority,
        "fixture no longer isolates one variable: the authorities differ"
    );
    assert_eq!(
        codes(&audited),
        codes(&unaudited),
        "fixture no longer isolates one variable: the findings differ"
    );
    assert_eq!(audited.verdict(), "pass");
    assert_eq!(audited.authority, Authority::Complete);
    assert!(codes(&audited).is_empty());

    // Direction 1 — a root was established, so the grade is `verified` and nothing is owed.
    assert!(
        audited.contract_handoff_root.is_some(),
        "the audited fixture established no handoff root; the positive direction is vacuous"
    );
    assert_eq!(audited.data_grade(), "verified");
    assert!(audited.unestablished().is_empty());

    // Direction 2 — no root, so the grade is `provisional` and it names what is owed. This
    // is the record a reader gets from a tree whose verdict says `pass`.
    assert!(
        unaudited.contract_handoff_root.is_none(),
        "the unaudited fixture established a handoff root; the negative direction is vacuous"
    );
    assert_eq!(unaudited.data_grade(), "provisional");
    assert_eq!(
        unaudited.unestablished(),
        vec!["contract_handoff".to_string()]
    );

    // `provisional` is not a failure, and a caller must never render it as one.
    assert_eq!(unaudited.exit_code(), 0);
}
