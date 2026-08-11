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
//! away, so nothing downstream can ask whether any of them is still true. At the current
//! ledger frontier that is 266 rows times four statements about what unsafe code does and
//! why it is sound, joined to nothing.
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

use std::collections::{BTreeMap, BTreeSet};
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
    fln_conformance::checked_workspace_root!()
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

// ---------------------------------------------------------------------------
// The evidence remainder, counted (bead `franken_lean-d3-safety-note-unenforced-cdbg`)
// ---------------------------------------------------------------------------

/// Rows whose evidence resolves to an e2e lane. Enforced above: the lane must be RUN.
const LANE_CITED_ROWS: usize = 1;

/// Rows whose evidence names a function that exists in the boundary crates.
///
/// These are the machine-resolvable ones. They are held by a **ratchet**: a row that
/// resolves today must keep resolving, because if the test it cites is renamed or deleted
/// the row reclassifies as prose and the counts below move, which fails.
///
/// 59 -> 58 at `c2f6f17a` (franken_lean-npl): FLN-UL-0033's evidence rewrite dropped the
/// `mpz_view` citation (the function still exists; the row no longer names it), moving the
/// row from symbol-resolved to prose.
///
/// 58 -> 59 at `7da31744` (the safe apply surface): FLN-UL-0181, the apply row itself,
/// cites boundary functions that now exist (`mk_closure_native`, `mk_closure_fn1`, the
/// closures-corpus test), so one prose-free row joins the resolvable class by its own
/// landing, measured.
///
/// 59 -> 63 at `c8c33d4a` (lean_string_append): the plugin demand list's one export gap
/// landed four new rows (FLN-UL-0182 through 0185), all four citing boundary-crate symbols
/// that now resolve (`alloc_string_cap`, `export_lean_string_append`,
/// `export_string_append_matches_upstream_arms`, `string_append_core`). The ledger is
/// 185 rows and the prose class is unchanged, so growth is symbol-side by measured
/// landing, not silent prose accretion — traced commit-by-commit.
///
/// 63 -> 70 at `8a78e4fd`/`55d75fc2`/`bc51f0c3` (the G0-3 door work): rows FLN-UL-0186
/// through 0192 land the dl* door, the end-to-end plugin test and lean_notify_assert,
/// each citing symbols its own landing creates; the ledger is 192 rows and the prose
/// class is unchanged at 121, so the growth is again symbol-side by measured landing.
///
/// 70 -> 77 in the retained FIR/FLBC integration: rows FLN-UL-0193 through 0199
/// expose the reviewed closure, reference, thunk, and task state transitions needed by
/// Golem. Each row cites the exact boundary function introduced with it; the ledger is
/// 199 rows and the prose class remains 121.
/// 77 -> 80 at `1312dfa2`/`5b9dd3db` (the same landings as the token row above records):
/// FLN-UL-0193 through 0201's ratchet rows minus their prose members, plus the bins row
/// FLN-UL-0202, resolve as symbol-resolved; the prose class is unchanged at 121.
///
/// 80 -> 82 at `2f4a3b18`: FLN-UL-0216 and FLN-UL-0217 cite the exact ST-ref and UTF-8
/// boundary test functions added with them; the other 13 slice-1 rows are prose.
/// 82 -> 83 at `c7a95255`: FLN-UL-0226 cites the exact task/promise boundary test; its
/// other eight slice-2 rows are prose.
/// 83 -> 85 at `f3a0c5c9`: FLN-UL-0251 and FLN-UL-0252 cite the exact task-manager test.
/// FLN-UL-0227 through 0250 say "manager" in ordinary prose and remain prose: the unrelated
/// helper named `manager` is not evidence for those rows.
/// 85 -> 86 at `eb6cf3c9`: FLN-UL-0264 cites the exact IO-wrapper boundary test; the other
/// eleven slice-3b rows are prose.
/// 86 -> 88 at `f882dd60`: both corpus rows, FLN-UL-0265 and FLN-UL-0266, cite the exact
/// task-plane corpus test added with them.
/// 88 -> 89 at `16512624` (the stdio plane): FLN-UL-0311 cites the exact io_println
/// swap-capture cell added with it; the slice's other 43 rows are prose.
/// 89 -> 90 in the read/write-prims slice (fln-3gv 5b, landed with this movement):
/// FLN-UL-0320 cites the exact io_file roundtrip cell added with it; the slice's other
/// six rows are prose.
/// 90 -> 95 at `19d47080`: the broad FLN-UL-0202 bins row was retired and its four
/// resolving citations were distributed across six exact owned-page unsafe-site rows
/// (FLN-UL-0321 through 0326). Each replacement row retains at least one exact boundary
/// test for its own bins/page lifecycle path, so this is a measured one-row-to-six-row
/// refinement, not five prose rows silently gaining a resolving spelling.
/// 95 -> 96 in the FLN-UL-0327 reentrant TLS fallback landing: the new test-only forcing
/// hook cites `small_heap_reentrant_tls_borrow_uses_individual_fallback`, which drives the
/// production individual-allocation fallback while its TLS bin is borrowed.
/// 96 -> 97 in the FLN-UL-0328 semantic reentrant landing: its helper calls `alloc_small` while
/// the TLS bin remains borrowed, so the named test pins the production fallback's one-tick law.
/// 97 -> 117 with the campaign's twenty audited native-cell resolvers (see the
/// RESOLVING_CITATION_TOKENS and PROSE_EVIDENCE_ROWS histories, this change).
/// 117 -> 120 after the apply tail: FLN-UL-0530, FLN-UL-0532, and FLN-UL-0533
/// each cite `export_stdio_routes_nonfatal_panic_through_the_current_stderr_stream`,
/// the exact boundary test their foreign-stream and environment-guard paths support.
/// 120 -> 121 in the signed-Int ABI recovery: FLN-UL-0559 cites
/// `export_int_big_arithmetic_division_and_truncation_match_pin_laws`, the exact boundary
/// test covering the new constructors, arithmetic, ownership, zero, and truncation arms.
/// 121 -> 171 in the deterministic generated-C Float bridge: FLN-UL-0569 through
/// FLN-UL-0618 all cite `deterministic_bare_float_exports_route_every_pinned_symbol`,
/// which calls every one of their binary64 and binary32 wrappers.
const SYMBOL_RESOLVED_ROWS: usize = 171;

/// Every citation token, across all rows, that resolves to a boundary-crate function.
///
/// Pinned SEPARATELY from the row count because the row count cannot see an isolated
/// citation loss: `FLN-UL-0007` cites two symbols, so renaming one leaves the row
/// symbol-resolved and the class totals unmoved. A planted rename survived exactly that way
/// before this constant existed. Counting tokens makes an isolated loss observable. This is
/// still a population ratchet, not an identity binding: a simultaneous gain can offset a
/// loss, so every intentional movement is audited row-by-row before this number changes.
///
/// 71 -> 70 at `c2f6f17a` (franken_lean-npl): the FLN-UL-0033 evidence rewrite dropped the
/// `mpz_view` citation — the function still exists in fln-unsafe-abi, and the row's checks
/// stand; what changed is that the row no longer names it. Measured by diffing the two
/// rows' resolving tokens across the edit.
///
/// 70 -> 71 at `7da31744` (the safe apply surface): its own FLN-UL-0181 row cites
/// `mk_closure_native`, `mk_closure_fn1`, and the closures-corpus test — all of which now
/// resolve as boundary-crate functions — so the resolving population grows by the row's
/// own landing, measured, not silent.
///
/// 71 -> 75 at `c8c33d4a` (lean_string_append): the plugin demand list's one export gap
/// landed `alloc_string_cap`, `export_lean_string_append`,
/// `export_string_append_matches_upstream_arms` and `string_append_core`, so four more
/// tokens resolve — growth by measured landing, traced commit-by-commit.
///
/// 75 -> 82 at `8a78e4fd`/`55d75fc2`/`bc51f0c3` (the G0-3 door work): seven new rows
/// (FLN-UL-0186 through 0192) cite symbols their own landings create —
/// `door_loads_a_reference_built_plugin_end_to_end` (five rows),
/// `export_assert_violation_format_matches_upstream`, `export_lean_notify_assert`,
/// `dlclose`, `dlerror` and `take_dlerror` — measured by replaying the guard's own
/// parse over both revisions: 75 -> 82 with zero removals.
///
/// 82 -> 89 in the retained FIR/FLBC integration: FLN-UL-0193 through 0199 each add one
/// resolving boundary symbol and remove none.
/// 89 -> 92 at `1312dfa2`/`5b9dd3db`: rows FLN-UL-0193 through 0201 (the evidence-ratchet
/// binding) and FLN-UL-0202 (the bounded small-object bins' own row, citing
/// `small_heap_bins_are_bounded_lifo_and_cross_thread_adoptable`) each cite symbols their
/// landings create — measured by replaying the guard's parse across the range.
///
/// 92 -> 94 at `2f4a3b18`, 94 -> 95 at `c7a95255`, 95 -> 97 at `f3a0c5c9`,
/// 97 -> 98 at `eb6cf3c9`, and 98 -> 100 at `f882dd60`: the exact function citations named
/// on the symbol-row history above add two, one, two, one, and two tokens respectively.
/// Replaying the classifier at every one of those commits found no removal from a
/// pre-existing row. The apparent extra 26 tokens from `closure` and `manager` were plain
/// English collisions and are deliberately excluded by the explicit-single-word rule.
/// 100 -> 101 at `16512624`: the io_println cell's citation on FLN-UL-0311 is the one new
/// resolving token; no pre-existing row lost one across the edit.
/// 101 -> 102 in the read/write-prims slice: FLN-UL-0320's io_file cell citation, again
/// with no removal from any pre-existing row.
/// 102 -> 113 across the owned-page series: FLN-UL-0202 first gained the two page-lifecycle
/// citations at `b22adfdf`, then the width-matrix citation at `e10428f0`; `19d47080` replaced
/// that one broad row's four tokens with twelve site-specific tokens on FLN-UL-0321 through
/// 0326. The one-to-many replacement is net +8, and every replacement token names the exact
/// bins, page-allocation, page-block-release, page-owner-release, page-free, or block-release
/// test for its ledgered unsafe site.
/// 113 -> 119 at `cba2a1dc`: FLN-UL-0321 through 0326 each add
/// `small_heap_pages_reclaim_across_every_size_class`, the test introduced by `2f688b0a`.
/// It allocates, frees, and drains one block in every 8-byte class through 4096, then requires
/// all 512 pages to be reclaimed. The six rows respectively name the bins, page construction,
/// page block release, owner release, page free, and block-release paths that this exact
/// all-class lifecycle covers; no pre-existing resolving token was removed in that refresh.
/// 119 -> 120 in the FLN-UL-0327 reentrant TLS fallback landing: its one exact test-function
/// citation is a new symbol token and no existing row lost a resolving citation.
/// 120 -> 121 in the FLN-UL-0328 semantic reentrant landing: its one exact test-function
/// citation is a new symbol token and no existing row lost a resolving citation.
/// 121 -> 122 in the all-class semantic reentrant matrix: FLN-UL-0328 gains the exact
/// all-class test citation, while its row remains symbol-resolved and no row is added.
/// 122 -> 142 across the 83r/3gv export campaign (e34bc583..f738e96a, rows
/// FLN-UL-0411..0512): twenty new tokens, each the named native cell in the
/// row's suite column (the error-string, stdin, panic-stream, once/task,
/// decoder, dbg/mk, and string-tail cells) — audited row by row, all
/// resolving to #[test] fns that run under plain cargo test.
/// 142 -> 145 at `e4625801` and `73826919`: the three symbol-resolved rows
/// named above each add the same exact panic-stream test citation; no existing
/// resolving token was removed or renamed.
/// 145 -> 146 in the signed-Int ABI recovery: FLN-UL-0559 adds the exact boundary-test
/// citation named in the row history above; no existing resolving token moved.
/// 146 -> 196 in the deterministic generated-C Float bridge: each of its 50 site rows
/// gains the exact test-function citation named in the row history above.
const RESOLVING_CITATION_TOKENS: usize = 196;

/// Rows whose evidence is prose — the permanent, named remainder.
///
/// This is a NUMBER rather than a caveat, deliberately. A remainder nobody counts is the
/// same defect one level up: it can grow without anyone noticing, which is precisely what
/// "declared, not silent" is supposed to prevent. Pinned exactly and in both directions, so
/// a new prose row fails and a prose row converted to a resolvable citation ALSO fails until
/// the numbers move — the remainder shrinks deliberately or not at all.
///
/// 120 -> 121 at `c2f6f17a` (franken_lean-npl): FLN-UL-0033 moved here from symbol-resolved
/// when its evidence stopped naming `mpz_view` — a citation removal by the row's own author,
/// measured, not silent.
///
/// 121 -> 134 at `2f4a3b18`, 134 -> 142 at `c7a95255`, 142 -> 166 at `f3a0c5c9`,
/// and 166 -> 177 at `eb6cf3c9`: those landings add 13, eight, 24, and eleven prose rows.
/// `f882dd60` adds only the two symbol-resolved corpus rows, so prose stays 177. The 24
/// task-manager rows remain here because an evidence phrase containing the ordinary word
/// "manager" is not a citation to a same-named helper.
/// 177 -> 220 at `16512624`: the stdio plane's 43 prose rows — the platform seam, handle
/// class, error decoder, prims, stream fields, thread-current trio, init twin, and the
/// mark-walk closure targets — land as suite-phrase prose exactly as the task manager's did.
/// 220 -> 226 in the read/write-prims slice: six prose rows (the two prims, the two live
/// stream fields, and the two export attributes).
/// 226 -> 388 and symbol-resolved 97 -> 117 across the fln-3gv slices 5c-8e and the
/// franken_lean-83r batches 1-7 (2142a7d4..f738e96a) plus peer rows in the same span —
/// caught by the first workspace sweep since the 226-era, because this suite runs only
/// workspace-wide, never in the per-slice gauntlet lane. The twenty new resolvers are
/// the campaign's named native cells (audited in RESOLVING_CITATION_TOKENS above); the
/// prose growth is the getLine/handle-ctl/fs/uv/temp/metadata/env/exit/errstr/float/
/// string-plane rows whose evidence is suite-phrase prose exactly as the stdio plane's.
/// 388 -> 405 across `a183a7aa`, `dcb65dcf`, and `73826919`: fourteen apply-tail
/// export rows, the timeit and allocprof rows, and the backtrace implementation row
/// carry suite-phrase or corpus-fact evidence. The separately landed foreign-stream
/// cell and its two environment guards are the three symbol-side rows above.
/// 405 -> 430 in the signed-Int ABI recovery: FLN-UL-0534 through FLN-UL-0558 add 25
/// implementation-site rows whose evidence is deliberately the export-suite/C4 corpus
/// phrase. FLN-UL-0559 is the one symbol-side test-apparatus row, and the FLN-UL-0498
/// evidence rewrite remains prose, so no pre-existing row changed class.
/// 430 -> 439 in the remaining Nat ABI wiring: FLN-UL-0560 through FLN-UL-0568
/// add nine implementation-site rows backed by the existing export suite and C4 lane.
/// The 50 deterministic Float bridge rows are all symbol-resolved, so this remainder
/// stays 439 rather than growing with the implementation surface.
const PROSE_EVIDENCE_ROWS: usize = 439;

/// Why prose stays prose, and what that costs.
const EVIDENCE_REMAINDER_REASON: &str = "\
Decided 2026-07-26 (option (b) on the parked question in \
franken_lean-d3-safety-note-unenforced-cdbg). 611 rows: 1 cites an e2e lane, 171 carry \
symbol-resolved evidence, and 439 remain prose; 196 individual tokens resolve. The exact \
counts live in the constants above and move only with a named, commit-anchored cause. The \
resolvable ones are ratcheted; the prose is a \
declared, COUNTED remainder rather than a rewrite.\n\
The trade: a full rewrite of the TCB's paperwork into a citation grammar is a large cost. \
Option (a), the rewrite, stays available and is strictly easier once the count is visible. \
What is bought here is that the remainder cannot GROW unnoticed.\n\
What this does NOT establish: nothing verifies that a prose invariant is TRUE, or that a \
resolvable citation's test actually exercises the invariant it is cited for. The ratchet \
only holds the declared resolving population; it does not bind citation identities.";

/// Every evidence field's class, decided the same way on every run.
///
/// Resolution is deliberately a RATCHET rather than a predicate on shape. Bead
/// `FLN-UL-0068`'s evidence reads `export_mk_string_lossy_vectors`, which looks exactly like
/// an identifier and is prose — the vectors are real but unnamed. A check that demanded
/// identifier-shaped citations resolve would have reported that row, a human would have
/// found the vectors, and this suite would have taught everyone it cries wolf. So nothing
/// here asserts that a prose citation OUGHT to resolve; it only counts, and holds the rows
/// that already do.
///
/// There is one extra disambiguation rule. An underscored function name is identifier-like
/// enough to resolve unquoted under the ledger's existing convention. A single-component
/// name such as `manager` or `closure` is also ordinary English, so it resolves only when
/// the evidence field writes it explicitly as inline code. This keeps a newly added helper
/// from silently converting unrelated old prose into purported evidence.
fn resolving_function_citations<'a>(
    evidence: &'a str,
    fn_names: &BTreeSet<String>,
) -> BTreeSet<&'a str> {
    let explicit_plain_names: BTreeSet<&str> = evidence
        .split('`')
        .enumerate()
        .filter_map(|(index, candidate)| {
            (index % 2 == 1
                && candidate.len() >= 7
                && candidate
                    .chars()
                    .all(|character| character.is_ascii_alphanumeric() || character == '_'))
            .then_some(candidate)
        })
        .collect();

    evidence
        .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .filter(|token| {
            token.len() >= 7
                && fn_names.contains(*token)
                && (token.contains('_') || explicit_plain_names.contains(*token))
        })
        .collect()
}

fn classify(
    rows: &[Row],
    lanes: &[String],
    fn_names: &BTreeSet<String>,
) -> (usize, usize, usize, usize) {
    let (mut lane, mut symbol, mut prose, mut tokens) = (0, 0, 0, 0);
    for row in rows {
        let resolving = resolving_function_citations(&row.evidence, fn_names);
        tokens += resolving.len();
        if lanes.iter().any(|l| row.evidence.contains(l.as_str())) {
            lane += 1;
        } else if !resolving.is_empty() {
            symbol += 1;
        } else {
            prose += 1;
        }
    }
    (lane, symbol, prose, tokens)
}

fn boundary_fn_names(root: &Path) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for krate in ["fln-unsafe-abi", "fln-unsafe-region", "fln-unsafe-jit"] {
        let mut stack = vec![root.join("crates").join(krate)];
        while let Some(dir) = stack.pop() {
            let Ok(entries) = std::fs::read_dir(&dir) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    stack.push(path);
                } else if path.extension().is_some_and(|e| e == "rs")
                    && let Ok(text) = std::fs::read_to_string(&path)
                {
                    for (i, _) in text.match_indices("fn ") {
                        let rest = &text[i + 3..];
                        let end = rest
                            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                            .unwrap_or(rest.len());
                        if end > 0 {
                            names.insert(rest[..end].to_string());
                        }
                    }
                }
            }
        }
    }
    names
}

#[test]
fn ordinary_prose_does_not_resolve_through_a_plain_name_collision() {
    let fn_names = BTreeSet::from(["closure".to_string(), "manager".to_string()]);
    let evidence = "string/array/closure facts; export task manager suite";

    assert!(
        resolving_function_citations(evidence, &fn_names).is_empty(),
        "ordinary English must not become machine-resolved evidence merely because a later \
         boundary helper has the same single-component name"
    );
}

#[test]
fn underscored_and_explicit_plain_function_citations_resolve_exactly() {
    let fn_names = BTreeSet::from([
        "export_task_manager_family_matches_upstream_arms".to_string(),
        "manager".to_string(),
        "managerial".to_string(),
    ]);
    let evidence = "export_task_manager_family_matches_upstream_arms; exact `manager`; \
                    managerial prose";

    assert_eq!(
        resolving_function_citations(evidence, &fn_names),
        BTreeSet::from([
            "export_task_manager_family_matches_upstream_arms",
            "manager",
        ]),
        "underscored names retain the ledger's existing convention, while an ordinary \
         single-component name needs exact inline-code syntax"
    );
}

/// The remainder is a number this run reports, and it cannot move without saying so.
#[test]
fn the_unsafe_ledger_evidence_remainder_is_counted_not_merely_disclosed() {
    let root = workspace_root();
    let ledger = std::fs::read_to_string(root.join("ci/UNSAFE_LEDGER.txt"))
        .expect("the unsafe ledger exists");
    let rows = parse(&ledger);
    assert!(
        rows.len() > 100,
        "only {} rows parsed; counting an empty ledger proves nothing",
        rows.len()
    );

    let fn_names = boundary_fn_names(&root);
    assert!(
        fn_names.len() > 100,
        "only {} function names recovered from the boundary crates, so every citation would \
         reclassify as prose and this count would be an artefact of a broken scan",
        fn_names.len()
    );

    let (lane, symbol, prose, tokens) = classify(&rows, &lane_stems(&root), &fn_names);
    assert_eq!(
        tokens, RESOLVING_CITATION_TOKENS,
        "{tokens} citation tokens resolve, against the declared \
         {RESOLVING_CITATION_TOKENS}. An isolated renamed or deleted function drops this \
         count even when its row still cites something else and the class totals below do \
         not move; intentional population changes require a row-by-row audit.\n\n\
         {EVIDENCE_REMAINDER_REASON}"
    );
    assert_eq!(
        (lane, symbol, prose),
        (LANE_CITED_ROWS, SYMBOL_RESOLVED_ROWS, PROSE_EVIDENCE_ROWS),
        "the unsafe-ledger evidence classes moved: {lane} lane-cited, {symbol} \
         symbol-resolved, {prose} prose, against the declared \
         {LANE_CITED_ROWS}/{SYMBOL_RESOLVED_ROWS}/{PROSE_EVIDENCE_ROWS}. Movement in EITHER \
         direction fails: a new prose row must be counted, and a row whose citation stopped \
         resolving must not be able to slip into the remainder silently. Update the \
         constants in the same change, and say which rows moved and why.\n\n{EVIDENCE_REMAINDER_REASON}"
    );
    assert_eq!(
        lane + symbol + prose,
        rows.len(),
        "the classes must partition the ledger; {} rows went unclassified",
        rows.len() - (lane + symbol + prose)
    );

    println!(
        "unsafe_ledger_evidence: {} rows — {lane} lane-cited (enforced: the lane must run), \
         {symbol} symbol-resolved (ratcheted: a citation that resolves must keep resolving), \
         {prose} PROSE REMAINDER; {tokens} individual citation tokens resolve. The \
         remainder is declared and counted, NOT verified: nothing here says a prose \
         invariant is true.",
        rows.len()
    );
}
