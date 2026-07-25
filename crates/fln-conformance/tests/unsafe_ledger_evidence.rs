//! The unsafe ledger's EVIDENCE column must point at something that runs.
//!
//! # What is already enforced, and what is not
//!
//! `ci/UNSAFE_LEDGER.txt` carries one row per `#[allow(unsafe_code)]` site in the three
//! boundary crates, six fields wide: id, path, invariant, evidence, safe fallback, and the
//! no-claim boundary. `tools/structure-guard` enforces the id join in both directions — an
//! unledgered site fails, a row whose site vanished fails — and that half is well built.
//!
//! The other half is not enforced, and cannot be, because the information is discarded at
//! parse time. `tools/structure-guard/src/ledger.rs` validates all six fields as non-empty
//! and then constructs `LedgerRow { id, path }`, keeping two. The invariant, the evidence,
//! the fallback and the no-claim boundary are checked for *the presence of text* and thrown
//! away, so nothing downstream can ask whether any of them is still true. That is roughly
//! 180 rows times four statements about what unsafe code does and why it is sound, joined to
//! nothing.
//!
//! # What this suite checks, which is one slice of that
//!
//! The `evidence` field is a **delegation**, and delegations are the failure this program
//! has already been bitten by: `franken_lean-pnav` was shape-only assertions delegating to a
//! lane nobody had checked still existed. So this resolves the delegations that are
//! machine-resolvable — an e2e lane named in an evidence citation must actually be RUN by
//! `scripts/check.sh`. A lane that exists but is registered nowhere is the pnav defect
//! exactly: the script sits in the tree, the row cites it, and nothing executes it.
//!
//! # Why prose citations are deliberately NOT resolved
//!
//! The scope below was an aesthetic judgement until it nearly cost a false finding, so it is
//! now an evidenced one. Auditing this file (2026-07-25) I flagged `FLN-UL-0068` as citing
//! evidence that did not exist: its evidence reads `export_mk_string_lossy_vectors`, which
//! resolves to no test, no fixture and no symbol anywhere in the tree. It looks exactly like
//! an identifier. It is prose — the vectors it describes are real and live in
//! `crates/fln-unsafe-abi/src/tests.rs:886-907`, three of them, asserting recovered bytes and
//! codepoint counts, inside a test named `export_string_constructors_match_pin_semantics`.
//! I missed them because my search was case-sensitive and the comment above them reads
//! "Lossy recovery vectors".
//!
//! A check that resolved identifier-shaped citations would have reported that row, a human
//! would have investigated, found the vectors, and learned that this suite cries wolf. So it
//! resolves only what is mechanically resolvable — lane names, which are filenames — and
//! leaves the rest to a reader, visibly.
//!
//! **This is a floor, not coverage**, and the distinction matters more here than usual.
//! Most evidence citations are prose naming a test, a fixture or a C-level fact, and this
//! suite cannot resolve those without inviting false positives on ordinary English. It
//! resolves lane citations only. The invariant, fallback and no-claim columns remain
//! unchecked by anything, which is a bigger hole than the one this closes and is recorded
//! rather than implied.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// A ledger row with **every** field retained — the thing the production parser drops.
#[derive(Debug, Clone)]
struct Row {
    id: String,
    #[allow(dead_code)]
    path: String,
    #[allow(dead_code)]
    invariant: String,
    evidence: String,
    #[allow(dead_code)]
    fallback: String,
    #[allow(dead_code)]
    no_claim: String,
}

/// Evidence citations that name a lane `scripts/check.sh` does not run.
///
/// A declared remainder, not a grandfather clause — the same shape as
/// `SOURCE_READ_ABOVE_L1_ALLOWANCE` in [`fln_conformance::ledger`]. Landing this as a bare
/// assertion would fail the build on a row nobody can repair from inside this crate
/// (`ci/` belongs to another pane), and a gate that cannot be green is a gate people learn
/// to bypass. Declared, the SECOND unrun delegation fails.
///
/// Checked in both directions: an entry whose lane has since been registered is itself a
/// failure, so the remainder shrinks as part of the repair.
const UNRUN_LANE_ALLOWANCE: [(&str, &str); 1] = [("FLN-UL-0063", "marrow_region_load")];

const UNRUN_LANE_REASON: &str = "\
FLN-UL-0063 is the row whose invariant field reads `NONE (deliberate violation)': it plants \
one volatile store into a sealed mapping so the hardware trap is proven. Its evidence is \
scripts/e2e/marrow_region_load.sh lane 7, which exists and really does contain the \
trap-on-write drill with a positive control — and which appears in exactly two files in \
this repository: the row that cites it, and itself. It is in neither scripts/check.sh's \
lane list nor .github/workflows/ci.yml, so nothing runs it. Registering a lane is a ci/ and \
scripts/ change owned by another pane; this suite makes the gap visible and refuses the \
next one rather than reaching into their artifact.";

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root is two levels above the crate manifest")
}

/// Parse the ledger keeping all six fields. Deliberately a second reader rather than a call
/// into `tools/structure-guard`: `fln-conformance` cannot depend on `tools/`, and the point
/// of this suite is precisely the fields that parser does not keep.
fn parse(text: &str) -> Vec<Row> {
    let mut rows = Vec::new();
    for raw in text.lines() {
        let line = match raw.find('#') {
            Some(pos) => &raw[..pos],
            None => raw,
        }
        .trim();
        let Some(rest) = line.strip_prefix("row ") else {
            continue;
        };
        let f: Vec<&str> = rest.split('|').map(str::trim).collect();
        if f.len() != 6 {
            continue;
        }
        rows.push(Row {
            id: f[0].to_string(),
            path: f[1].to_string(),
            invariant: f[2].to_string(),
            evidence: f[3].to_string(),
            fallback: f[4].to_string(),
            no_claim: f[5].to_string(),
        });
    }
    rows
}

/// Every lane a row's evidence names, joined to whether `check.sh` runs it.
fn lane_citations(rows: &[Row], lanes: &[String], gate: &str) -> BTreeMap<String, (String, bool)> {
    let mut cited = BTreeMap::new();
    for row in rows {
        for lane in lanes {
            if row.evidence.contains(lane.as_str()) {
                cited.insert(row.id.clone(), (lane.clone(), gate.contains(lane.as_str())));
            }
        }
    }
    cited
}

fn lane_stems(root: &Path) -> Vec<String> {
    let mut stems: Vec<String> = std::fs::read_dir(root.join("scripts/e2e"))
        .expect("scripts/e2e is readable")
        .filter_map(Result::ok)
        .filter_map(|entry| {
            let path = entry.path();
            (path.extension().is_some_and(|e| e == "sh"))
                .then(|| path.file_stem()?.to_str().map(str::to_string))
                .flatten()
        })
        .collect();
    stems.sort();
    stems
}

// ---------------------------------------------------------------------------
// The live ledger
// ---------------------------------------------------------------------------

#[test]
fn every_lane_the_unsafe_ledger_cites_as_evidence_is_actually_run() {
    let root = workspace_root();
    let ledger = std::fs::read_to_string(root.join("ci/UNSAFE_LEDGER.txt"))
        .expect("the unsafe ledger exists");
    let gate = std::fs::read_to_string(root.join("scripts/check.sh")).expect("check.sh exists");
    let rows = parse(&ledger);

    // Guard the guard: a parse that silently returned nothing would make every assertion
    // below vacuously true.
    assert!(
        rows.len() > 100,
        "only {} ledger rows parsed; a comparison against an empty ledger proves nothing",
        rows.len()
    );

    let cited = lane_citations(&rows, &lane_stems(&root), &gate);
    let declared: BTreeMap<&str, &str> = UNRUN_LANE_ALLOWANCE.iter().copied().collect();

    let mut undeclared = Vec::new();
    for (id, (lane, registered)) in &cited {
        if !registered && declared.get(id.as_str()) != Some(&lane.as_str()) {
            undeclared.push(format!(
                "{id} cites scripts/e2e/{lane}.sh as its safety evidence, and \
                 scripts/check.sh does not run it. A lane that exists but is registered \
                 nowhere is a dangling delegation: the row reads as evidenced and nothing \
                 executes the evidence. Register the lane, or cite what actually runs."
            ));
        }
    }
    assert!(
        undeclared.is_empty(),
        "unsafe-ledger evidence delegates to lanes nothing runs:\n  {}\n\nDeclared \
         remainder:\n{UNRUN_LANE_REASON}",
        undeclared.join("\n  ")
    );

    // The remainder must not outlive the defect it records.
    for (id, lane) in UNRUN_LANE_ALLOWANCE {
        let entry = cited.get(id);
        assert!(
            entry.is_some(),
            "UNRUN_LANE_ALLOWANCE declares {id}, which no longer cites a lane at all. \
             Remove the entry in the change that removed the citation."
        );
        let (cited_lane, registered) = entry.expect("asserted Some immediately above");
        assert_eq!(
            cited_lane, lane,
            "{id} now cites {cited_lane} rather than the declared {lane}"
        );
        assert!(
            !registered,
            "{id}'s lane {lane} is now registered in check.sh, so its entry in \
             UNRUN_LANE_ALLOWANCE is stale — shrink the remainder in the same change that \
             registered it"
        );
    }
}

/// The column this suite exists because of: the production parser keeps two of six fields.
///
/// Stated as a test rather than a comment so that if `structure-guard` ever starts retaining
/// the evidence column, somebody is told that this suite's reason for existing has changed.
#[test]
fn the_production_parser_still_discards_the_columns_this_suite_reads() {
    let root = workspace_root();
    let parser = std::fs::read_to_string(root.join("tools/structure-guard/src/ledger.rs"))
        .expect("the structure-guard ledger parser exists");
    assert!(
        parser.contains("id: fields[0].to_string(),") && parser.contains("path: fields[1]"),
        "the production parser no longer builds LedgerRow from fields 0 and 1"
    );
    assert!(
        !parser.contains("evidence:"),
        "structure-guard now retains an `evidence` field. That is strictly better than this \
         suite reading the file a second time — move the lane-resolution check there and \
         delete this one rather than keeping two readers of the same artifact."
    );
}

// ---------------------------------------------------------------------------
// Planted violations
// ---------------------------------------------------------------------------

fn synthetic(id: &str, evidence: &str) -> Vec<Row> {
    parse(&format!(
        "schema fln-unsafe-ledger/1\nrow {id} | crates/x/src/y.rs | inv | {evidence} | fb | nc\n"
    ))
}

/// THE SECOND ONE. A new row citing an unrun lane is refused even though one exactly like it
/// is permitted — which is the whole value of a declared remainder over a blanket exemption.
#[test]
fn a_new_row_citing_an_unrun_lane_is_refused() {
    let rows = synthetic("FLN-UL-9001", "proved by the marrow_region_load lane");
    let lanes = vec!["marrow_region_load".to_string()];
    let cited = lane_citations(&rows, &lanes, "scripts/e2e/closure_audit.sh\n");
    let (lane, registered) = cited.get("FLN-UL-9001").expect("the citation is found");
    assert_eq!(lane, "marrow_region_load");
    assert!(
        !registered,
        "a lane absent from the gate text must not be reported as run"
    );
    assert!(
        !UNRUN_LANE_ALLOWANCE
            .iter()
            .any(|(id, _)| *id == "FLN-UL-9001"),
        "the plant must not be pre-declared, or it proves nothing"
    );
}

/// THE PERMISSION HALF. A row citing a lane the gate really runs must pass, or the check is
/// a wall that fires on every citation and gets deleted the first time someone adds one.
#[test]
fn a_row_citing_a_registered_lane_is_accepted() {
    let rows = synthetic("FLN-UL-9002", "closure_audit lane 3 asserts it");
    let lanes = vec!["closure_audit".to_string()];
    let cited = lane_citations(&rows, &lanes, "  scripts/e2e/closure_audit.sh \\\n");
    let (_, registered) = cited.get("FLN-UL-9002").expect("the citation is found");
    assert!(
        *registered,
        "a lane the gate names must be reported as run, or every honest citation fails"
    );
}

/// Evidence that names no lane at all is not a finding. Most rows cite tests, fixtures or
/// C-level facts, and a check that flagged them would be noise that trains people to ignore
/// it.
#[test]
fn evidence_naming_no_lane_is_not_reported() {
    let rows = synthetic(
        "FLN-UL-9003",
        "ctor_header_and_scalar_facts; C4 ctor.cs_sz facts",
    );
    let cited = lane_citations(&rows, &lane_stems(&workspace_root()), "");
    assert!(
        cited.is_empty(),
        "prose evidence must not be mistaken for a lane citation: {cited:?}"
    );
}

/// The parser must keep all six fields, since dropping them is the defect this file is
/// about and a regression here would silently make every check above vacuous.
#[test]
fn the_reader_retains_every_field_the_production_parser_drops() {
    let rows = parse(
        "schema fln-unsafe-ledger/1\n\
         row FLN-UL-9004 | p.rs | the invariant | the evidence | the fallback | the boundary\n",
    );
    assert_eq!(rows.len(), 1);
    let row = &rows[0];
    assert_eq!(row.id, "FLN-UL-9004");
    assert_eq!(row.path, "p.rs");
    assert_eq!(row.invariant, "the invariant");
    assert_eq!(row.evidence, "the evidence");
    assert_eq!(row.fallback, "the fallback");
    assert_eq!(row.no_claim, "the boundary");
}
