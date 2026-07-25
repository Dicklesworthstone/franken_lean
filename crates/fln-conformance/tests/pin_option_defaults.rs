//! The pinned binary's own option table, asked at test time (bead
//! `fln-parity-ledger-l2-pinned-source-qydn`).
//!
//! # What this is for
//!
//! Eight rows in `ci/PARITY_LEDGER.txt` record option defaults at level **L2** with
//! oracle-kind **pinned-source**. The ledger's own tier note (`:41-48`) defines L2 as "the
//! pinned Reference binary produced the expected value" and L1 as "implemented against the
//! pinned SOURCE semantics ... no Reference-produced value is compared". Those eight are
//! earned by `crates/fln-core/tests/pin_inventory_census.rs`, which reads vendored upstream
//! `.lean` text — real evidence, and by the ledger's own definition L1, not L2.
//!
//! This asks the binary instead. `Lean.getOptionDeclsArray` is stock
//! (`vendor/lean4-src/src/Lean/Data/Options.lean:127`), so the whole registered option
//! table — name, default, description — prints from an unpatched pin through ordinary
//! metaprogramming. No patched Reference, no §18.3 instrumented oracle. That is bead
//! `franken_lean-c24a`'s finding (the pin is reachable through its own surface) applied to
//! a second surface.
//!
//! # Why there is no fixture here, deliberately
//!
//! The oracle runs *in this test*, so there is no capture that can go stale between runs.
//! That is not a stylistic preference: bead `franken_lean-ext-observable-fixture-drift-gap-vqnu`
//! records 28 rows resting on a 533-record capture that nothing re-derives, one directory
//! over. A live differential cannot acquire that defect. The cost is that this test is a
//! typed SKIP without the pinned toolchain, which is the same trade every pin-dependent rig
//! here already makes.
//!
//! # What a green run does and does not establish
//!
//! It establishes that every option default `fln-core` claims is the value the pinned
//! binary reports for that option, right now, on this host. It establishes nothing about
//! the 653 options in that table which `fln-core` does not implement: this is a differential
//! over OUR claims, not a census of upstream's surface. The count is reported on every run
//! so the ratio cannot be mistaken for coverage.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use fln_core::options::limits;

/// What `fln-core` claims, and the exact ledger row each claim backs.
///
/// Kept as data rather than a sequence of assertions so the planted-violation test below
/// can drive the same comparison the live test does. A test whose failure path is a
/// different code path from its success path has not been shown to fail.
const CLAIMED_DEFAULTS: [(&str, u64); 8] = [
    ("maxHeartbeats", limits::MAX_HEARTBEATS_DEFAULT),
    ("maxRecDepth", limits::MAX_REC_DEPTH_DEFAULT),
    (
        "synthInstance.maxHeartbeats",
        limits::SYNTH_INSTANCE_MAX_HEARTBEATS_DEFAULT,
    ),
    (
        "synthInstance.maxSize",
        limits::SYNTH_INSTANCE_MAX_SIZE_DEFAULT,
    ),
    (
        "maxSynthPendingDepth",
        limits::MAX_SYNTH_PENDING_DEPTH_DEFAULT,
    ),
    ("maxUniverseOffset", limits::MAX_UNIVERSE_OFFSET_DEFAULT),
    (
        "exponentiation.threshold",
        limits::EXPONENTIATION_THRESHOLD_DEFAULT,
    ),
    ("maxErrors", limits::MAX_ERRORS_DEFAULT),
];

/// The probe. `logInfo` on a command is the pin's ordinary reporting surface; nothing here
/// patches, links against, or otherwise executes upstream implementation code (D8) — the
/// binary is being *asked a question*, which is exactly the oracle role the Oracle-Only Law
/// reserves for it.
const PROBE: &str = r#"import Lean
open Lean
run_cmd do
  let decls ← Lean.getOptionDeclsArray
  let mut n : Nat := 0
  for (name, decl) in decls do
    n := n + 1
    logInfo m!"OPTION|{name}|{decl.defValue}"
  logInfo m!"TABLE_SIZE|{n}"
"#;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root is two levels above the crate manifest")
}

/// The Reference tag, read from `SUITE.lock` rather than hard-coded.
///
/// A hard-coded toolchain path can silently probe a toolchain the lock does not pin, and
/// the answer would look exactly as green. The lock is the single pin ceremony (D15), so
/// it is what this asks.
fn pinned_tag() -> Option<String> {
    let lock = std::fs::read_to_string(workspace_root().join("SUITE.lock")).ok()?;
    lock.lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))?
        .split_whitespace()
        .find_map(|field| field.strip_prefix("tag=").map(str::to_string))
}

/// Locate the pinned `lean`. `FLN_REFERENCE_BIN` overrides; the elan layout is the default.
/// Absent toolchain is a typed skip, never a silent pass.
fn pinned_lean() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("FLN_REFERENCE_BIN") {
        let p = PathBuf::from(path);
        return p.is_file().then_some(p);
    }
    let home = std::env::var("HOME").ok()?;
    let tag = pinned_tag()?;
    let p = PathBuf::from(home)
        .join(".elan/toolchains")
        .join(format!("leanprover--lean4---{tag}"))
        .join("bin/lean");
    p.is_file().then_some(p)
}

/// Parse `OPTION|<name>|<default>` out of whatever else the binary prints.
///
/// Marker-anchored rather than line-anchored on purpose: message rendering is not a
/// contract this test wants to depend on, and a prefix change should not be reported as an
/// option divergence.
fn parse_table(stdout: &str) -> (BTreeMap<String, String>, Option<usize>) {
    let mut table = BTreeMap::new();
    let mut size = None;
    for line in stdout.lines() {
        if let Some(rest) = line.split("OPTION|").nth(1) {
            let mut parts = rest.splitn(2, '|');
            if let (Some(name), Some(value)) = (parts.next(), parts.next()) {
                table.insert(name.trim().to_string(), value.trim().to_string());
            }
        } else if let Some(rest) = line.split("TABLE_SIZE|").nth(1) {
            size = rest.trim().parse::<usize>().ok();
        }
    }
    (table, size)
}

/// Every claim that the oracle does not corroborate, rendered for a human.
///
/// Absence and disagreement are separate findings: an option we implement that upstream
/// does not register at all is a different defect from one whose default moved, and
/// collapsing them would hide the first behind the second.
fn divergences(claimed: &[(&str, u64)], table: &BTreeMap<String, String>) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ours) in claimed {
        match table.get(*name) {
            None => out.push(format!(
                "{name}: fln-core claims a default of {ours}, and the pinned binary registers \
                 no option by that name — either the option was renamed upstream or ours is \
                 an invention"
            )),
            Some(theirs) if theirs != &ours.to_string() => out.push(format!(
                "{name}: fln-core says {ours}, the pinned binary says {theirs}"
            )),
            Some(_) => {}
        }
    }
    out
}

// ---------------------------------------------------------------------------
// The live differential
// ---------------------------------------------------------------------------

#[test]
fn every_option_default_fln_core_claims_is_the_one_the_pinned_binary_reports() {
    let Some(lean) = pinned_lean() else {
        eprintln!(
            "SKIP pin_option_defaults: pinned Reference toolchain not found (tag {:?}). \
             Install with `elan toolchain install leanprover/lean4:{}` or set \
             FLN_REFERENCE_BIN. This is a typed skip: nothing about the option defaults is \
             established by this run.",
            pinned_tag(),
            pinned_tag().unwrap_or_else(|| "<unreadable SUITE.lock>".into())
        );
        return;
    };

    let dir = std::env::temp_dir().join(format!("fln-pin-options-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("probe scratch directory");
    let probe = dir.join("options_probe.lean");
    std::fs::write(&probe, PROBE).expect("probe is writable");

    // A pin that is present but unrunnable fails the test rather than skipping it: the
    // toolchain was located, so this is a broken oracle, not an absent one.
    let out = Command::new(&lean)
        .arg(&probe)
        .output()
        .map_err(|error| format!("running {}: {error}", lean.display()))
        .expect("the located pinned binary is executable");
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let _ = std::fs::remove_dir_all(&dir);

    let (table, size) = parse_table(&stdout);
    assert!(
        out.status.success(),
        "the pinned binary refused the probe (exit {:?}).\nstdout:\n{stdout}\nstderr:\n{stderr}",
        out.status.code()
    );

    // A parse that quietly returned a handful of rows would make the comparison below
    // vacuous for everything it did not see. The pin registered 661 options at v4.32.0;
    // the floor is deliberately far below that, because this guards against a broken
    // parse, not against upstream adding options.
    let reported = size.unwrap_or(0);
    assert_eq!(
        reported,
        table.len(),
        "the binary reported {reported} options and the parse recovered {}; a partial parse \
         makes every absent-option finding below meaningless",
        table.len()
    );
    assert!(
        table.len() > 500,
        "only {} options parsed out of the pin's registered table — this is a parse failure \
         wearing the costume of a clean run",
        table.len()
    );

    let found = divergences(&CLAIMED_DEFAULTS, &table);
    assert!(
        found.is_empty(),
        "fln-core disagrees with the pinned binary about {} option default(s):\n  {}",
        found.len(),
        found.join("\n  ")
    );

    // Reported, never asserted as coverage: this is a differential over OUR claims.
    println!(
        "pin_option_defaults: {} of {} registered options implemented and corroborated \
         against the pinned binary; the remaining {} are NOT covered by this or any other \
         rig, and this ratio is not a compatibility figure",
        CLAIMED_DEFAULTS.len(),
        table.len(),
        table.len() - CLAIMED_DEFAULTS.len()
    );
}

// ---------------------------------------------------------------------------
// Planted violations — the comparison must be shown to fail
// ---------------------------------------------------------------------------

/// A differential that has only ever been observed agreeing is not evidence of agreement.
/// These drive the same `divergences` the live test does, over a synthetic table, so they
/// run with or without the pinned toolchain.
#[test]
fn the_comparison_catches_a_moved_default_a_renamed_option_and_nothing_else() {
    let honest: BTreeMap<String, String> = CLAIMED_DEFAULTS
        .iter()
        .map(|(name, value)| ((*name).to_string(), value.to_string()))
        .collect();
    assert!(
        divergences(&CLAIMED_DEFAULTS, &honest).is_empty(),
        "a table that agrees must produce no findings, or the guard is a wall"
    );

    // 1. The default moved upstream. This is the case the eight ledger rows exist to catch,
    //    and reading vendored source would catch it too — only later, and only if someone
    //    re-read the source.
    let mut moved = honest.clone();
    moved.insert("maxRecDepth".into(), "1024".into());
    let found = divergences(&CLAIMED_DEFAULTS, &moved);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].contains("fln-core says 512, the pinned binary says 1024"),
        "the finding must name both numbers, or it cannot be triaged: {found:?}"
    );

    // 2. The option is gone, or was never real. Distinct from a moved default: one is a
    //    value drifting, the other is a claim about a surface that does not exist.
    let mut renamed = honest.clone();
    renamed.remove("exponentiation.threshold");
    let found = divergences(&CLAIMED_DEFAULTS, &renamed);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].contains("registers no option by that name"),
        "an absent option must not be reported as a value disagreement: {found:?}"
    );

    // 3. Options we do not claim are not our business. A table full of upstream options we
    //    have never implemented must produce no findings, or this rig would grow into a
    //    census it has not earned and cannot maintain.
    let mut extra = honest;
    for i in 0..50 {
        extra.insert(format!("upstream.optionWeDoNotImplement{i}"), "7".into());
    }
    assert!(
        divergences(&CLAIMED_DEFAULTS, &extra).is_empty(),
        "unimplemented upstream options are not divergences"
    );
}

/// The parser must survive the binary's message decoration, and must not invent rows.
#[test]
fn the_parse_is_anchored_on_the_marker_not_on_the_line_shape() {
    let noisy = "probe.lean:4:2: information: OPTION|maxRecDepth|512\n\
                 some unrelated diagnostic text\n\
                 OPTION|maxErrors|100\n\
                 TABLE_SIZE|2\n";
    let (table, size) = parse_table(noisy);
    assert_eq!(size, Some(2));
    assert_eq!(table.get("maxRecDepth").map(String::as_str), Some("512"));
    assert_eq!(table.get("maxErrors").map(String::as_str), Some("100"));
    assert_eq!(
        table.len(),
        2,
        "no row may be invented from prose: {table:?}"
    );

    let (empty, no_size) = parse_table("nothing here\n");
    assert!(empty.is_empty() && no_size.is_none());
}

/// The pin this rig probes must be the pin the lock names. A rig that reads a toolchain
/// nobody pinned would be green against the wrong oracle.
#[test]
fn the_probed_toolchain_is_the_one_suite_lock_pins() {
    let tag = pinned_tag().expect("SUITE.lock names a reference tag");
    assert!(
        tag.starts_with('v'),
        "the reference tag should look like a version: {tag:?}"
    );
    if let Ok(explicit) = std::env::var("FLN_REFERENCE_BIN") {
        eprintln!("pin_option_defaults: FLN_REFERENCE_BIN overrides the elan layout ({explicit})");
        return;
    }
    if let Some(path) = pinned_lean() {
        let rendered = path.to_string_lossy().into_owned();
        assert!(
            rendered.contains(&tag),
            "the located toolchain {rendered} is not the {tag} the lock pins"
        );
    }
}
