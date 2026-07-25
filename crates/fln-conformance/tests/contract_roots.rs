//! Cross-artifact linkage for the extracted contracts (bead franken_lean-53v,
//! plan Appendix B/C). Every rendered surface — Markdown contract, generated
//! Rust module, canonical inventory — must name the SAME inventory root, and
//! the extern census must be internally coherent. A hand edit to any one
//! artifact breaks the linkage here; drift against the pin itself is caught by
//! the extractors' `--check` lanes (scripts/e2e/contract_drift.sh).
//!
//! ## What this suite does NOT verify, and why (bead `franken_lean-pnav`)
//!
//! [`assert_linked`] compares the inventory digest *labels* the Markdown and the
//! generated Rust each carry, and checks the inventory file is non-empty. It does
//! **not** recompute a digest from content, so a reader should not take a green
//! run here as "the contracts match the pin".
//!
//! That is not laziness, and it is worth recording why rather than leaving it as
//! an apparent oversight: `INVENTORY_DIGEST` is **sha256** of the inventory text
//! (`gen_abi_contract.py:1348`), and the closed dependency universe (D1) contains
//! **no sha256** — `fln-hash` implements BLAKE3. So no Rust in this workspace can
//! recompute that digest, and the only thing that can verify it is the Python
//! extractor that produced it. Implementing sha256 to satisfy a test would be the
//! wrong trade; recording that the verification is single-sourced is the honest
//! one.
//!
//! What this suite *can* do is refuse to let the delegation go silently missing —
//! see [`the_lane_this_suite_delegates_to_is_present_and_registered`]. The risk
//! `franken_lean-pnav` names is structural: if `contract_drift.sh` is ever removed
//! or unregistered, this shape-only cluster becomes the only remaining check on
//! the ABI and olean contracts, and nothing in these tests would change colour.
//! Now it would.

#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root")
}

fn find_digest(text: &str, marker: &str) -> Option<String> {
    // The first 64-hex-char token on the first line naming the marker.
    let line = text.lines().find(|l| l.contains(marker))?;
    line.split(|c: char| !c.is_ascii_hexdigit())
        .find(|tk| tk.len() == 64)
        .map(str::to_string)
}

fn assert_linked(md_rel: &str, rs_rel: &str, inv_rel: &str) {
    let root = root();
    let md = fs::read_to_string(root.join(md_rel));
    assert!(md.is_ok(), "{md_rel}: {:?}", md.as_ref().err());
    let md = md.expect("asserted above");
    let rs = fs::read_to_string(root.join(rs_rel));
    assert!(rs.is_ok(), "{rs_rel}: {:?}", rs.as_ref().err());
    let rs = rs.expect("asserted above");
    let inv = fs::read(root.join(inv_rel));
    assert!(inv.is_ok(), "{inv_rel}: {:?}", inv.as_ref().err());
    assert!(
        !inv.expect("asserted above").is_empty(),
        "{inv_rel} is empty"
    );
    let md_digest = find_digest(&md, "inventory");
    assert!(md_digest.is_some(), "{md_rel}: no inventory digest line");
    let rs_digest = find_digest(&rs, "INVENTORY_DIGEST");
    assert!(rs_digest.is_some(), "{rs_rel}: no INVENTORY_DIGEST line");
    assert_eq!(
        md_digest, rs_digest,
        "{md_rel} and {rs_rel} name different inventory roots"
    );
    assert!(
        md.contains("@generated") && rs.contains("@generated"),
        "rendered artifacts must carry the @generated marker"
    );
}

/// The delegation in this module's header must stay true.
///
/// Every shape-only assertion in this cluster — here, `fln-rt`'s
/// `pin_binding_is_present`, and `fln-olean`'s — points at one lane for the real
/// verification. A pointer to a lane that no longer exists, or exists but is no
/// longer wired into the gate, is worse than no pointer: it reads as coverage.
/// So the existence and the registration are both asserted, and the second is the
/// one that matters — a script can sit in the tree unrun for months.
#[test]
fn the_lane_this_suite_delegates_to_is_present_and_registered() {
    let root = root();
    const LANE: &str = "scripts/e2e/contract_drift.sh";

    let lane = fs::read_to_string(root.join(LANE));
    assert!(
        lane.is_ok(),
        "{LANE} is missing, and three test suites delegate their digest \
         verification to it. Either restore it or stop claiming the delegation in \
         those headers — a dangling pointer reads as coverage."
    );
    let lane = lane.expect("asserted above");
    assert!(
        lane.contains("--check"),
        "{LANE} no longer invokes an extractor --check lane, so the delegation it \
         receives is no longer honoured"
    );

    let gate = fs::read_to_string(root.join("scripts/check.sh"));
    assert!(gate.is_ok(), "scripts/check.sh: {:?}", gate.as_ref().err());
    let gate = gate.expect("asserted above");
    assert!(
        gate.contains(LANE),
        "{LANE} exists but scripts/check.sh no longer names it, so it is not run by \
         the gate. That is the exact failure franken_lean-pnav describes: the \
         shape-only assertions silently become the only remaining check."
    );

    // Negative control. A registration check whose `contains` is true for anything
    // proves nothing, and this suite exists precisely because a test can look like
    // verification without being it — so the discriminating power is demonstrated
    // here rather than assumed.
    assert!(
        !gate.contains("scripts/e2e/contract_drift_that_does_not_exist.sh"),
        "the registration check matches a lane that was never written, so it cannot \
         distinguish a registered lane from an absent one"
    );
}

#[test]
fn abi_artifacts_share_one_inventory_root() {
    assert_linked(
        "ABI_CONTRACT.md",
        "crates/fln-rt/src/abi.rs",
        "contracts/abi_inventory.json",
    );
}

#[test]
fn olean_artifacts_share_one_inventory_root() {
    assert_linked(
        "OLEAN_CONTRACT.md",
        "crates/fln-olean/src/format.rs",
        "contracts/olean_inventory.json",
    );
}

#[test]
fn extern_census_is_coherent() {
    let root = root();
    let text = fs::read_to_string(root.join("contracts/extern_census.tsv"))
        .expect("contracts/extern_census.tsv");
    let mut declared_extern: Option<usize> = None;
    let mut declared_constants: Option<usize> = None;
    let mut extern_rows: Vec<Vec<&str>> = Vec::new();
    let mut summary_total: usize = 0;
    let mut schema_seen = false;
    let mut unknown_rows: Vec<String> = Vec::new();
    for line in text.lines() {
        if line.starts_with('#') || line.is_empty() {
            continue;
        }
        let cols: Vec<&str> = line.split('\t').collect();
        match cols[0] {
            _ if line == "schema fln-extern-census/1" => schema_seen = true,
            "extern_count" => declared_extern = Some(cols[1].parse().expect("extern_count")),
            "constant_count" => declared_constants = Some(cols[1].parse().expect("constant_count")),
            "columns" | "columns_summary" => {}
            "extern" => extern_rows.push(cols),
            "summary" => {
                assert_eq!(cols.len(), 4, "summary row arity: {line:?}");
                summary_total += cols[3].parse::<usize>().expect("summary count");
            }
            other => unknown_rows.push(other.to_string()),
        }
    }
    assert!(
        unknown_rows.is_empty(),
        "unknown row kinds in extern census: {unknown_rows:?}"
    );
    assert!(schema_seen, "missing schema row");
    let declared_extern = declared_extern.expect("missing extern_count row");
    let declared_constants = declared_constants.expect("missing constant_count row");
    assert_eq!(
        extern_rows.len(),
        declared_extern,
        "extern row count differs from declared extern_count"
    );
    assert_eq!(
        summary_total, declared_constants,
        "totality summary must partition the entire constant surface (Appendix C)"
    );
    assert!(
        declared_extern > 500,
        "extern census implausibly small: {declared_extern}"
    );
    let mut prev = "";
    for row in &extern_rows {
        assert_eq!(row.len(), 7, "extern row arity: {row:?}");
        assert!(prev < row[1], "extern rows must be strictly sorted by name");
        prev = row[1];
        assert!(
            row[4].parse::<u32>().is_ok() && row[5].parse::<u32>().is_ok(),
            "arity/level_params must be numeric: {row:?}"
        );
        assert!(
            !row[6].is_empty(),
            "extern entries must be nonempty: {row:?}"
        );
    }
}
