//! The join between AGENTS.md's Build Gate governed-set table and the lane scripts it describes.
//!
//! `franken_lean-build-gate-lane-governed-set-98np` R4. R1 derived every lane's governed set once,
//! at one commit, and wrote the result into AGENTS.md. That table is a **measurement written
//! down**, which is the shape the section itself warns about: nothing re-derives it, so it rots
//! exactly like the prose it replaced. This binds it to the scripts, in **both directions**.
//!
//! Equality both ways is the right shape here and one-way-plus-a-floor is not. AGENTS.md's own
//! shrinking-allowance rule distinguishes a declared remainder of *permitted violations*, which
//! shrinks as people repair it, from a disclosure of a *measured population*, which does not. A
//! lane's governed set is the second: it moves when someone edits a lane, in either direction, and
//! both movements must be deliberate.
//!
//! # What is bound
//!
//! * every named row's count against that lane's derived set;
//! * the `| 0 | the other N |` row's **cardinality** against the number of lanes that derive to
//!   nothing — those lanes have no identity in the table, so the claim is bound to how many there
//!   are, the technique `fln-bench-apparatus-empty-referent-bkw6` arrived at;
//! * the **partition**: named lanes + zero lanes must be every lane under `scripts/e2e/`, so a new
//!   lane cannot appear unnoticed in either class;
//! * the **prose** above the table — "Eight lanes declare a governed set; thirteen declare none at
//!   all" — against both. AGENTS.md item 7 records a day spent with that sentence and its own
//!   table disagreeing, because a row was added and only two of the three places stating the
//!   cardinality were moved. That is this guard's own failure mode, so it is checked.
//!
//! # Two traps this guard is built against, both paid for once already
//!
//! The first extractor for R1 matched `^[A-Z_]*INPUT_PATHS=(` and reported `kernel_replay.sh` as
//! governing **zero** paths: it declares `AP6_INPUT_PATHS`, and the character class excluded the
//! digit. Nothing about that failure was loud — a derived zero looks exactly like a lane that
//! governs nothing. So the derivation is reconciled against a **cheap independent signal** (a
//! count of governance references), and a lane that derives to zero while referring to governance
//! is a **broken scan**, not a clean lane.
//!
//! And a scan that returns nothing must fail rather than pass. A guard that reports "no rows
//! disagree" because it parsed no rows goes green forever the day its anchor moves, which is why
//! the anchor is `expect`ed and the row count floored.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};

// ---------------------------------------------------------------------------
// The derivation — the same rule the R1 measurement used, digit and all
// ---------------------------------------------------------------------------

/// Every path declared by any `*INPUT_PATHS=( … )` array in one lane script.
///
/// The identifier prefix admits digits deliberately: `AP6_INPUT_PATHS` is the case that made an
/// earlier version of this rule report a false zero.
fn governed_paths(script: &str) -> BTreeSet<String> {
    let mut paths = BTreeSet::new();
    let mut lines = script.lines();
    while let Some(line) = lines.next() {
        let Some(name) = line.trim_end().strip_suffix("INPUT_PATHS=(") else {
            continue;
        };
        if !name
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        {
            continue;
        }
        for body in lines.by_ref() {
            if body.trim() == ")" {
                break;
            }
            let body = body.split('#').next().unwrap_or_default();
            paths.extend(body.split_whitespace().map(str::to_string));
        }
    }
    paths
}

/// A cheap signal, computed a different way, that this lane governs *something*.
///
/// Its only job is to disagree with [`governed_paths`] when the extractor stops matching.
fn governance_signal(script: &str) -> usize {
    const NEEDLES: [&str; 5] = [
        "INPUT_PATHS",
        "hash_governed",
        "require_unchanged",
        "--governed-path",
        "governed-root",
    ];
    NEEDLES
        .iter()
        .map(|needle| script.matches(needle).count())
        .sum()
}

/// A derived zero that the independent signal contradicts is a broken scan, never a clean lane.
fn reconcile(lane: &str, derived: usize, signal: usize) -> Option<String> {
    (derived == 0 && signal > 0).then(|| {
        format!(
            "BROKEN SCAN: `{lane}` derives 0 governed paths but refers to governance {signal} \
             times. The extractor stopped matching this lane's declaration — a false zero reads \
             as a lane that governs nothing, which is the `AP6_INPUT_PATHS` failure again."
        )
    })
}

// ---------------------------------------------------------------------------
// The claim — AGENTS.md's table, read rather than transcribed
// ---------------------------------------------------------------------------

const TABLE_ANCHOR: &str = "| governed paths | lane | relative to";
const PROSE_ANCHOR: &str = "lanes declare a governed set;";

#[derive(Debug)]
struct Declared {
    /// Lane script name -> the count the table states for it.
    named: BTreeMap<String, usize>,
    /// The `| 0 | the other N |` row's N.
    zero_lanes: usize,
    /// "**Eight** lanes declare a governed set; **thirteen** declare none at all".
    prose_declaring: usize,
    prose_zero: usize,
}

fn english(word: &str) -> Option<usize> {
    const WORDS: [(&str, usize); 22] = [
        ("zero", 0),
        ("one", 1),
        ("two", 2),
        ("three", 3),
        ("four", 4),
        ("five", 5),
        ("six", 6),
        ("seven", 7),
        ("eight", 8),
        ("nine", 9),
        ("ten", 10),
        ("eleven", 11),
        ("twelve", 12),
        ("thirteen", 13),
        ("fourteen", 14),
        ("fifteen", 15),
        ("sixteen", 16),
        ("seventeen", 17),
        ("eighteen", 18),
        ("nineteen", 19),
        ("twenty", 20),
        ("twenty-one", 21),
    ];
    let word = word
        .trim_matches(|c: char| !c.is_ascii_alphanumeric() && c != '-')
        .to_ascii_lowercase();
    WORDS.iter().find(|(w, _)| *w == word).map(|(_, n)| *n)
}

fn declared(agents_md: &str) -> Declared {
    let start = agents_md.find(TABLE_ANCHOR).expect(
        "AGENTS.md must carry the Build Gate governed-set table; if that table moved or was \
         removed, this guard is enforcing a claim that no longer exists and must be updated \
         rather than quietly passing",
    );
    let mut named = BTreeMap::new();
    let mut zero_lanes = None;

    for row in agents_md[start..].lines().skip(2) {
        if !row.trim_start().starts_with('|') {
            break;
        }
        let cells: Vec<&str> = row.trim().trim_matches('|').split('|').collect();
        if cells.len() < 2 {
            continue;
        }
        let Ok(count) = cells[0].trim().parse::<usize>() else {
            continue;
        };
        // Lane names are the backticked cells ending in `.sh`. The parenthetical
        // (`AP6_INPUT_PATHS`) in the same cell is not a lane and is excluded by that suffix.
        let lanes: Vec<&str> = cells[1]
            .split('`')
            .map(str::trim)
            .filter(|token| token.ends_with(".sh"))
            .collect();
        if lanes.is_empty() {
            // The zero row names no lane; it states a cardinality instead.
            if count == 0 {
                zero_lanes = cells[1]
                    .split_whitespace()
                    .find_map(|token| token.parse::<usize>().ok());
            }
            continue;
        }
        for lane in lanes {
            named.insert(lane.to_string(), count);
        }
    }

    let prose_at = agents_md.find(PROSE_ANCHOR).expect(
        "AGENTS.md must state how many lanes declare a governed set; item 7 records this \
         sentence and its own table disagreeing for a day",
    );
    let before: Vec<&str> = agents_md[..prose_at].split_whitespace().collect();
    let after: Vec<&str> = agents_md[prose_at + PROSE_ANCHOR.len()..]
        .split_whitespace()
        .take(4)
        .collect();

    Declared {
        named,
        zero_lanes: zero_lanes.expect("the table's zero row must state how many lanes it covers"),
        prose_declaring: before
            .last()
            .and_then(|w| english(w))
            .expect("the sentence must name the declaring-lane count in words"),
        prose_zero: after
            .iter()
            .find_map(|w| english(w))
            .expect("the sentence must name the zero-governed-lane count in words"),
    }
}

// ---------------------------------------------------------------------------
// The comparison — both directions, over the same data
// ---------------------------------------------------------------------------

/// Every way the table and the scripts can disagree, as human-readable lines.
///
/// `measured` is lane script name -> derived governed-path count, for *every* lane.
fn disagreements(table: &Declared, measured: &BTreeMap<String, usize>) -> Vec<String> {
    let mut out = Vec::new();

    // Direction 1: a row whose lane moved, or which names a lane that no longer exists.
    for (lane, stated) in &table.named {
        match measured.get(lane) {
            None => out.push(format!(
                "AGENTS.md's table names `{lane}`, which is not a lane script under scripts/e2e/"
            )),
            Some(actual) if actual != stated => out.push(format!(
                "`{lane}`: AGENTS.md says {stated} governed paths, the script declares {actual}"
            )),
            Some(_) => {}
        }
    }

    // Direction 2: a lane that gained a governed set, or lost one, without the table moving.
    for (lane, actual) in measured {
        if *actual > 0 && !table.named.contains_key(lane) {
            out.push(format!(
                "`{lane}` declares {actual} governed paths and AGENTS.md's table does not name it"
            ));
        }
    }

    // The zero row is bound to its cardinality, since it names no lane.
    let zero_measured = measured.values().filter(|count| **count == 0).count();
    if zero_measured != table.zero_lanes {
        out.push(format!(
            "AGENTS.md's table says {} lanes govern nothing; {zero_measured} do",
            table.zero_lanes
        ));
    }

    // There was a partition check here — `named.len() + zero_measured == measured.len()` — and
    // the mutation campaign could not kill it: every membership change is already caught by
    // direction 1, direction 2, or the zero-row cardinality, so the arithmetic can only restate
    // a complaint one of them has already made. An unfalsifiable check reads as extra safety and
    // supplies none, which is `fln-inert-declaration-shape`. Removed rather than kept and
    // disclosed, and recorded here so it is not re-added as an improvement.

    // The prose above the table must agree with the table and with the measurement.
    let declaring_measured = measured.values().filter(|count| **count > 0).count();
    if table.prose_declaring != declaring_measured {
        out.push(format!(
            "AGENTS.md's sentence says {} lanes declare a governed set; {declaring_measured} do",
            table.prose_declaring
        ));
    }
    if table.prose_zero != zero_measured {
        out.push(format!(
            "AGENTS.md's sentence says {} lanes declare none; {zero_measured} do",
            table.prose_zero
        ));
    }

    out
}

// ---------------------------------------------------------------------------
// Reading the real tree
// ---------------------------------------------------------------------------

fn workspace_root() -> std::path::PathBuf {
    fln_conformance::pin::workspace_root()
}

/// Every lane script, as (file name, source).
fn lane_sources() -> Vec<(String, String)> {
    let dir = workspace_root().join("scripts/e2e");
    let mut lanes: Vec<(String, String)> = std::fs::read_dir(&dir)
        .expect("scripts/e2e is readable")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "sh"))
        .map(|path| {
            let name = path
                .file_name()
                .expect("lane has a file name")
                .to_string_lossy()
                .into_owned();
            let source = std::fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("{} is readable: {error}", path.display()));
            (name, source)
        })
        .collect();
    lanes.sort();
    lanes
}

fn agents_md() -> String {
    std::fs::read_to_string(workspace_root().join("AGENTS.md")).expect("AGENTS.md is readable")
}

/// A `check.sh` governing fewer paths than this is a broken extractor, not a small gate.
/// The array carried 53 when this landed; the floor sits well below so an ordinary
/// deregistration does not wall anyone, while a scan that came back near-empty still fails.
const CHECK_SH_GOVERNED_FLOOR: usize = 30;

/// Bare directories in `check.sh`'s `INPUT_PATHS`, which is the claim the sentence beneath the
/// governed-set table makes. Equality both ways: this is a measured population, not a declared
/// remainder that shrinks as it is repaired.
const CHECK_SH_BARE_DIRECTORY_ENTRIES: usize = 5;

/// **The reference number every row of the governed-set table is stated relative to, joined to
/// the array it counts** (bead `fln-tlbo`).
///
/// The table's per-lane counts have been held per commit and in both directions since 98np R4.
/// The number in its *header* — the one each row's third cell is measured against — was the one
/// figure in that table with no producer, and `fln-tlbo` filed it as accurate-but-unjoined.
///
/// **It was falsified twice before anything noticed, which is why this is a guard and not a
/// correction.** At the bead's own measurement it read 50. `scripts/lib/gate_lock.sh` took the
/// array to 51 and the header was moved to match by hand; the two `.github/workflows/` entries
/// then took it to **53** and nothing moved. Meanwhile the prose beneath the table still said
/// "fifty", so AGENTS.md stated one number two ways and disagreed with itself as well as with
/// the array — and a comment in this very file quoted the header as 50, a third value. Three
/// statements, three numbers, none of them right. Registering a script edits `INPUT_PATHS`, so
/// the falsifying event is *routine*.
///
/// The repair is the one this file already applies to the rows: derive, then bind in **both**
/// directions, so registering a script obliges its author to move the number and a table edit
/// cannot invent one. The duplicate statement in the prose was **removed** rather than bound —
/// two copies that must move together is the defect, not the fix, and `word_to_number` above
/// stops at twenty-one so the word form was unbindable anyway.
///
/// **The floor is what stops a broken extractor reading as a repair.** `governed_paths` is
/// reused rather than reimplemented — a second copy would be free to drift from the one the
/// rows are judged by — and it is the extractor whose earlier version reported a false zero for
/// `AP6_INPUT_PATHS`. A zero here would silently satisfy nothing at all.
///
/// **What this does not earn.** It counts `INPUT_PATHS` *entries*, not the files they expand to:
/// five of them are bare directories covering most of the repository, which is exactly what the
/// sentence beneath the table says and what no count can capture. It does not check that the
/// entries are the *right* ones. One host, one commit, class `bounded_model`.
#[test]
fn the_governed_set_table_states_check_sh_s_own_cardinality() {
    let script = std::fs::read_to_string(workspace_root().join("scripts/check.sh"))
        .expect("scripts/check.sh is readable");
    let paths = governed_paths(&script);

    assert!(
        paths.len() >= CHECK_SH_GOVERNED_FLOOR,
        "derived only {} governed paths from scripts/check.sh against a floor of \
         {CHECK_SH_GOVERNED_FLOOR}. That is a BROKEN EXTRACTOR, not a small gate — and a broken \
         extractor that returns few paths reads exactly like a repair. This is the \
         `AP6_INPUT_PATHS` false zero one file over.",
        paths.len(),
    );

    let stated = agents_md()
        .lines()
        .find_map(|line| {
            line.split_once(TABLE_ANCHOR)?
                .1
                .split_whitespace()
                .find_map(|word| {
                    word.trim_matches(|c: char| !c.is_ascii_digit())
                        .parse::<usize>()
                        .ok()
                })
        })
        .expect(
            "the governed-set table header must state the number its rows are relative to; if \
             that cell lost its number this guard is enforcing a claim that no longer exists",
        );

    assert_eq!(
        stated,
        paths.len(),
        "AGENTS.md's governed-set table is stated relative to {stated} `check.sh` entries, but \
         `INPUT_PATHS` declares {}. BOTH directions are a real event. If a script was just \
         REGISTERED, move the header cell to {} in the same commit — every row's third cell is \
         measured against it, so a stale header silently restates every row. If the header moved \
         without the array, it invented a number. This figure was falsified twice before anything \
         noticed (50 -> 51 -> 53) and that is what this guard exists to end.",
        paths.len(),
        paths.len(),
    );

    let bare = paths
        .iter()
        .filter(|entry| workspace_root().join(entry).is_dir())
        .count();
    assert_eq!(
        bare, CHECK_SH_BARE_DIRECTORY_ENTRIES,
        "the sentence beneath the table says {CHECK_SH_BARE_DIRECTORY_ENTRIES} of check.sh's \
         entries are bare directories; {bare} of them are. That sentence is the whole reason the \
         path COUNT does not tell you whether your write voids a lane, so it may not drift: a \
         bare directory covers every file beneath it."
    );
}

// ---------------------------------------------------------------------------
// The law
// ---------------------------------------------------------------------------

/// The whole law over injected inputs, so its **anti-vacuity floors are reachable from a test**.
///
/// An earlier version inlined this in the `#[test]` and read the tree directly. A mutation
/// campaign against that version killed the comparison mutants and left both floors **alive**:
/// with 21 real lanes and a real table present, `lanes.len() >= 20` and `!named.is_empty()` can
/// never fire, so nothing distinguished them from `>= 0` and `true`. The checks that exist
/// precisely for the day the scan breaks were the two nothing could prove. Injecting the inputs
/// is what makes them killable.
fn audit(lanes: &[(String, String)], agents_md: &str) -> Vec<String> {
    let mut complaints = Vec::new();

    if lanes.len() < 20 {
        complaints.push(format!(
            "found only {} lane scripts; a scan that returns few or none would report agreement \
             it never checked",
            lanes.len()
        ));
    }

    let mut measured = BTreeMap::new();
    for (name, source) in lanes {
        let derived = governed_paths(source).len();
        complaints.extend(reconcile(name, derived, governance_signal(source)));
        measured.insert(name.clone(), derived);
    }

    let table = declared(agents_md);
    if table.named.is_empty() {
        complaints.push(
            "parsed no named rows out of AGENTS.md's governed-set table; an empty parse would \
             report agreement it never checked"
                .to_string(),
        );
    }

    complaints.extend(disagreements(&table, &measured));
    complaints
}

/// AGENTS.md's governed-set table describes the lane scripts as they are, in both directions.
#[test]
fn the_governed_set_table_matches_the_lane_scripts() {
    let complaints = audit(&lane_sources(), &agents_md());
    assert!(
        complaints.is_empty(),
        "AGENTS.md's Build Gate governed-set table no longer describes scripts/e2e/. \
         Re-derive it (98np R1) and move the table, the zero-row count and the sentence above \
         it together:\n  {}",
        complaints.join("\n  ")
    );
}

/// Both anti-vacuity floors fire. Neither is reachable through the real tree, which is exactly
/// why they are driven here instead of trusted.
#[test]
fn an_empty_or_short_scan_is_refused_rather_than_reported_clean() {
    let real = agents_md();

    // No lanes at all — the case a moved directory or a broken glob produces.
    let complaints = audit(&[], &real);
    assert!(
        complaints
            .iter()
            .any(|line| line.contains("found only 0 lane scripts")),
        "an empty lane scan was not refused: {complaints:?}"
    );

    // A handful of lanes: enough to parse, far too few to be the tree.
    let few: Vec<(String, String)> = lane_sources().into_iter().take(3).collect();
    assert!(
        audit(&few, &real)
            .iter()
            .any(|line| line.contains("found only 3 lane scripts")),
        "a short lane scan was not refused"
    );

    // A table whose NAMED rows stopped parsing while its header and zero row survive — the case
    // a changed row format produces, and the one `declared`'s own `expect`s do not catch because
    // every anchor it looks for is still there. The named-row floor is the only thing between
    // that and a green run.
    //
    // Isolating it took a correction: deleting the whole table made `declared` panic on the
    // zero row first, so the assertion passed for a reason that had nothing to do with the floor.
    // The predicate must be the same shape the parser uses — a leading cell that is a NUMBER —
    // not "contains a .sh name". The header cell reads ``relative to `check.sh`'s 50``, so a
    // substring test deleted the anchor itself and the guard panicked for the wrong reason.
    let rowless: String = real
        .lines()
        .filter(|line| {
            let counted_row = line
                .trim()
                .strip_prefix('|')
                .and_then(|rest| rest.split('|').next())
                .is_some_and(|cell| cell.trim().parse::<usize>().is_ok_and(|n| n > 0));
            !counted_row
        })
        .collect::<Vec<_>>()
        .join("\n");
    let table = declared(&rowless);
    assert!(
        table.named.is_empty() && table.zero_lanes > 0,
        "the fixture must remove the named rows and keep the zero row, or it tests the wrong \
         refusal: {table:?}"
    );
    assert!(
        audit(&lane_sources(), &rowless)
            .iter()
            .any(|line| line.contains("parsed no named rows")),
        "a table that parsed to zero named rows was reported clean"
    );
}

/// The derivation admits the identifier that once made it report a false zero.
#[test]
fn the_extractor_admits_a_digit_in_the_array_name() {
    let script = "AP6_INPUT_PATHS=(\n  a b\n  c\n)\n";
    assert_eq!(governed_paths(script).len(), 3);
    // The union across several arrays, which `env_snapshots.sh` needs.
    let two = "INPUT_PATHS=(\n  a\n)\nCOLLISION_INPUT_PATHS=(\n  a b\n)\n";
    assert_eq!(
        governed_paths(two),
        BTreeSet::from(["a".into(), "b".into()])
    );
    // Comments are not paths.
    assert_eq!(governed_paths("INPUT_PATHS=(\n  a # b c\n)\n").len(), 1);
    // A lowercase prefix is not one of these arrays.
    assert!(governed_paths("my_INPUT_PATHS=(\n  a\n)\n").is_empty());
}

/// A narrowed extractor is caught by the independent signal rather than passing as a clean lane.
#[test]
fn a_derived_zero_that_the_control_signal_contradicts_is_a_broken_scan() {
    // What a lane looks like to an extractor that stopped matching its declaration.
    let complaint = reconcile(
        "kernel_replay.sh",
        0,
        governance_signal("AP6_INPUT_PATHS=(\n)\n"),
    );
    assert!(
        complaint.is_some_and(|text| text.contains("BROKEN SCAN")),
        "a derived zero contradicted by the signal must be refused"
    );
    // A lane that genuinely governs nothing is not a broken scan.
    assert!(reconcile("bignum_vectors.sh", 0, 0).is_none());
    // And a lane that derives paths is never one either.
    assert!(reconcile("env_snapshots.sh", 13, 27).is_none());
}

/// Both directions fire, each on a planted decoy that the real tree does not contain.
#[test]
fn the_comparison_catches_movement_in_both_directions() {
    let table = declared(&agents_md());
    let mut measured: BTreeMap<String, usize> = table.named.clone();
    let zero_lane = |n: usize| (0..n).map(|i| (format!("zero{i}.sh"), 0));
    measured.extend(zero_lane(table.zero_lanes));

    // The honest baseline must be clean, or every decoy below proves nothing.
    assert!(
        disagreements(&table, &measured).is_empty(),
        "the negative control is not clean: {:?}",
        disagreements(&table, &measured)
    );

    // Decoy 1 — a lane gains a governed path and the table does not move.
    let mut moved = measured.clone();
    let victim = table
        .named
        .keys()
        .next()
        .expect("the table names a lane")
        .clone();
    *moved.get_mut(&victim).expect("victim is measured") += 1;
    assert!(
        disagreements(&table, &moved)
            .iter()
            .any(|line| line.contains(&victim)),
        "a lane whose governed set grew was not caught"
    );

    // Decoy 2 — a brand-new governed lane the table has never heard of.
    let mut added = measured.clone();
    added.insert("planted_lane.sh".into(), 7);
    assert!(
        disagreements(&table, &added)
            .iter()
            .any(|line| line.contains("planted_lane.sh") && line.contains("does not name it")),
        "a new governed lane absent from the table was not caught"
    );

    // Decoy 3 — a lane the table names disappears from the tree.
    let mut removed = measured.clone();
    removed.remove(&victim);
    assert!(
        disagreements(&table, &removed)
            .iter()
            .any(|line| line.contains("not a lane script")),
        "a table row naming a lane that no longer exists was not caught"
    );

    // Decoy 4 — one of the zero-governed lanes quietly gains a governed set.
    let mut promoted = measured.clone();
    promoted.insert("zero0.sh".into(), 4);
    let lines = disagreements(&table, &promoted);
    assert!(
        lines.iter().any(|line| line.contains("govern nothing"))
            && lines.iter().any(|line| line.contains("zero0.sh")),
        "a zero-governed lane that gained a set must move both the cardinality and the \
         membership complaint: {lines:?}"
    );
}

/// The sentence above the table is bound to the table and to the measurement.
///
/// Item 7 records a day in which this section's prose and its own table disagreed, because a row
/// was added and only two of the three places stating the cardinality were moved.
#[test]
fn the_prose_counts_are_bound_to_the_table_and_the_measurement() {
    let table = declared(&agents_md());
    assert_eq!(
        table.prose_declaring,
        table.named.len(),
        "AGENTS.md's sentence and its own table disagree about how many lanes declare a \
         governed set"
    );

    // A sentence that drifts from the measurement is caught even when the table is right.
    // BOTH halves are driven: a campaign against an earlier version gutted the
    // `prose_declaring` branch and survived, because only the `prose_zero` half was exercised.
    let mut measured: BTreeMap<String, usize> = table.named.clone();
    measured.extend((0..table.zero_lanes).map(|i| (format!("zero{i}.sh"), 0)));

    let zero_drift = Declared {
        prose_zero: table.prose_zero + 1,
        ..declared(&agents_md())
    };
    assert!(
        disagreements(&zero_drift, &measured)
            .iter()
            .any(|line| line.contains("declare none")),
        "prose drifting about the zero-governed count was not caught"
    );

    let declaring_drift = Declared {
        prose_declaring: table.prose_declaring + 1,
        ..declared(&agents_md())
    };
    assert!(
        disagreements(&declaring_drift, &measured)
            .iter()
            .any(|line| line.contains("declare a governed set")),
        "prose drifting about the declaring-lane count was not caught"
    );
}

/// The mutants below are planted in the **real** AGENTS.md text and the **real** lane sources,
/// mutated in memory rather than on disk.
///
/// A fixture proves the comparison *fires*; it never proves the production text is what the
/// comparison is reading — AGENTS.md says so at length about `BOUNDARY_API.txt`'s `TempWs` cells.
/// Mutating the bytes in memory keeps the production path and the production content while
/// changing exactly one token, and writes nothing into a tree other panes are parked on.
#[test]
fn the_real_table_and_the_real_lanes_each_fail_when_mutated() {
    let lanes = lane_sources();
    let measured: BTreeMap<String, usize> = lanes
        .iter()
        .map(|(name, source)| (name.clone(), governed_paths(source).len()))
        .collect();

    // Baseline: the tree as it stands is clean. Without this the mutants prove nothing.
    let honest = declared(&agents_md());
    assert!(
        disagreements(&honest, &measured).is_empty(),
        "the negative control is not clean, so nothing below is attributable"
    );

    // Mutant A — one real table row's count is off by one. The row is chosen from the table
    // itself, so this cannot rot into targeting a row that no longer exists.
    let (victim, stated) = honest.named.iter().next().expect("the table names a lane");
    let real = agents_md();
    let row = format!("| {stated} | `{victim}`");
    assert!(
        real.contains(&row),
        "the table row for `{victim}` is not in the form this mutant edits: {row:?}"
    );
    let mutated = real.replacen(&row, &format!("| {} | `{victim}`", stated + 1), 1);
    let complaints = disagreements(&declared(&mutated), &measured);
    assert!(
        complaints.iter().any(|line| line.contains(victim.as_str())),
        "editing `{victim}`'s count in the real AGENTS.md table did not fail: {complaints:?}"
    );

    // Mutant B — a real lane script gains a governed path and the real table does not move.
    let (lane, source) = lanes
        .iter()
        .find(|(_, source)| source.contains("\nINPUT_PATHS=(\n"))
        .expect("some lane declares INPUT_PATHS");
    let grown = source.replacen(
        "\nINPUT_PATHS=(\n",
        "\nINPUT_PATHS=(\n  planted/decoy.path\n",
        1,
    );
    assert_eq!(
        governed_paths(&grown).len(),
        governed_paths(source).len() + 1,
        "the planted path was not picked up, so mutant B tests nothing"
    );
    let mut with_growth = measured.clone();
    with_growth.insert(lane.clone(), governed_paths(&grown).len());
    let complaints = disagreements(&honest, &with_growth);
    assert!(
        complaints.iter().any(|line| line.contains(lane.as_str())),
        "growing `{lane}`'s real governed set did not fail: {complaints:?}"
    );

    // Mutant C — the decoy that proves the *scan* is live rather than the comparison. Deleting
    // the array header from a real lane must not read as "this lane governs nothing".
    let gutted = source.replacen("\nINPUT_PATHS=(\n", "\nINPUT_PATHS_DISABLED=(\n", 1);
    assert!(
        reconcile(
            lane,
            governed_paths(&gutted).len(),
            governance_signal(&gutted)
        )
        .is_some()
            || !governed_paths(&gutted).is_empty(),
        "a lane whose declaration was renamed away must be refused as a broken scan, not \
         silently counted as governing nothing"
    );
}

/// A parse that finds nothing must fail loudly rather than report agreement it never checked.
#[test]
fn a_scan_that_returns_nothing_is_a_failure_not_a_clean_tree() {
    // The anchor is `expect`ed, so a table that moved takes the guard down with it.
    let moved = std::panic::catch_unwind(|| declared("no table here"));
    assert!(
        moved.is_err(),
        "a missing table must panic, not parse to an empty agreement"
    );

    // An empty table parses to no rows, and the law refuses that separately.
    let table = Declared {
        named: BTreeMap::new(),
        zero_lanes: 0,
        prose_declaring: 0,
        prose_zero: 0,
    };
    assert!(
        disagreements(&table, &BTreeMap::new()).is_empty(),
        "an empty comparison is trivially clean — which is exactly why the law floors the row \
         count instead of trusting this"
    );
}
