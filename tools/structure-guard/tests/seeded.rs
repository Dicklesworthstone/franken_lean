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
        "#![deny(unsafe_code)]\n#[allow(unsafe_code)]\nfn bypass() {}\n",
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

const EXPORTING_LIB: &str = "//! boundary stub\n#![deny(unsafe_code)]\n\n\
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
        "//! boundary stub\n#![deny(unsafe_code)]\n\n\
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
        "//! boundary stub\n#![deny(unsafe_code)]\n\n\
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
        "//! boundary stub\n#![deny(unsafe_code)]\n\n\
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

/// The independence boundary (`FLN-STRUCT-037`, bead `franken_lean-r0xu`).
///
/// The rule is vacuous against the real tree today, because `fln-checker` is a
/// charter crate with no checking code. A guard that has only ever been observed
/// passing is an unenforced claim, which is the failure class this suite exists
/// to prevent — so every entry in the semantic inventory is planted here and
/// asserted to fire.
const CHECKER_SEMANTIC_INVENTORY: [&str; 12] = [
    "is_equiv",
    "normalize_fixpoint",
    "loose_bvar_range",
    "has_fvar",
    "has_expr_mvar",
    "has_level_mvar",
    "has_level_param",
    "approx_depth",
    "read_body",
    "from_canonical_bytes",
    "from_canonical_bytes_budgeted",
    "fln_bignum",
];

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
    for item in CHECKER_SEMANTIC_INVENTORY {
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
/// `crates/fln-checker/src/lib.rs` names all eleven items in its doc comments.
#[test]
fn naming_a_semantic_item_in_prose_is_not_a_violation() {
    let ws = TempWs::new("checker-boundary-prose");
    base(&ws);
    let mut src = String::from("//! stub\n#![forbid(unsafe_code)]\n");
    for item in CHECKER_SEMANTIC_INVENTORY {
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
