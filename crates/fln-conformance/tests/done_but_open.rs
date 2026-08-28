//! `done_but_open` — the mechanism bead `fln-db39` asks for: nothing joined
//! "the tree contains this bead's deliverable" to "the bead is still open", so
//! the pattern (atgf, z6c, y24, lld, and then fln-wgp for a fifth instance)
//! cost a pane a session of archaeology each time it recurred.
//!
//! The signal, measured before this was built: 748 of 1479 commit subjects on
//! `refs/heads/main` carry a bead-shaped token, and `fln-lld` — the founding
//! instance — appears in 11 of them, so joining SUBJECT tokens against the
//! tracker's open unclaimed beads carries the pattern. Bodies are deliberately
//! not scanned: they cite neighbouring beads ("blocks fln-x"), so a body join
//! reports work that merely mentions a bead. Subjects are a FLOOR, not a
//! census — a slice landed under a subject that names no bead is invisible
//! here, and that is disclosed rather than repaired, because precision is what
//! makes a red actionable.
//!
//! A finding means "landed work names this bead, nobody is driving it, and it
//! has been quiet for longer than every historical rescue took to notice" —
//! never "close it". The remainder below is ONE-WAY with floors, not equality:
//! a peer who claims, closes, or lands fresh work on a seeded bead removes the
//! finding and their commit must not go red for doing the right thing (the
//! shrinking-allowance direction law). A seeded entry whose bead recovered is
//! dead weight, printed for tidying, never a wall.
//!
//! The `updated_at` staleness class was measured UNINFORMATIVE before landing
//! (0 in-progress beads quiet for 7 days, because tracker churn refreshes
//! `updated_at` on export and comment alike — `fln-ysvo`'s data-model limit)
//! and is deliberately absent rather than present-and-vacuous.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fs;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

/// Days of subject-silence before an unclaimed open bead with landed work is a
/// finding. Calibration: the historical rescues surfaced at 3 (atgf), 7 (z6c),
/// 7 (y24), 8 (lld) and 10 (wgp) days of exactly this silence.
const STALE_DAYS: i64 = 3;

/// The declared remainder: findings present at the mechanism's landing,
/// seeded UNADJUDICATED so the population is disclosed and any new instance
/// reddens immediately. An entry records the finding's existence at first
/// scan, not a legitimacy ruling; it retires when its bead is closed, claimed,
/// or receives fresh landed work — silently, by the one-way rule.
const SEEDED_REMAINDER: &[(&str, &str)] = &[
    (
        "fln-20n",
        "codec read levels; partial work landed via the fln-wgp seam",
    ),
    ("fln-amv", "env epic; sub-slices landed under fln-amv.* ids"),
    ("fln-h1k", "verdict follow-on; seeded unadjudicated"),
    ("fln-lst4", "seeded unadjudicated at mechanism landing"),
    ("fln-msou", "seeded unadjudicated at mechanism landing"),
    (
        "fln-yihl",
        "rch staleness finding; external-tool half stays open",
    ),
    (
        "franken_lean-83r",
        "adjudicated: multi-slice epic, slices 1-5 landed (stage0 executes on Marrow \
         incl. the 5-TU module DAG); runtime-suite half legitimately open on \
         fln-3gv's IO plane",
    ),
    (
        "franken_lean-d17i",
        "seeded unadjudicated at mechanism landing",
    ),
    (
        "franken_lean-d3-safety-note-unenforced-cdbg",
        "seeded unadjudicated",
    ),
    (
        "franken_lean-gii",
        "fln-checker independent checker in-progress; Prelude items 0..10 passing, indexed Eq ongoing",
    ),
    (
        "franken_lean-n8hw",
        "seeded unadjudicated at mechanism landing",
    ),
    (
        "franken_lean-timy",
        "seeded unadjudicated at mechanism landing",
    ),
    (
        "franken_lean-zht",
        "kernel coverage follow-up; bc7 carried part of it",
    ),
];

/// Growth cap: a fourteenth deliberate entry is a decision this constant makes
/// visible in review; raising it must move with the disclosure above.
const SEEDED_CEILING: usize = 13;

#[derive(Debug, Clone, PartialEq, Eq)]
struct BeadRec {
    id: String,
    status: String,
    assignee: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Finding {
    bead: String,
    newest_commit_age_days: i64,
    landed_subjects: usize,
}

#[derive(Debug, PartialEq, Eq)]
enum ScanRefusal {
    NoBeads,
    NoCommits,
    /// The token join found implausibly few subject hits for this repository:
    /// a broken tokenizer and a clean tree are the same green otherwise.
    JoinBelowFloor {
        joined: usize,
        floor: usize,
    },
}

/// Bead-shaped tokens in one commit subject, joined later against real ids.
/// Hand-rolled because the dependency universe is closed (D1): no regex crate.
fn subject_tokens(subject: &str) -> Vec<String> {
    let bytes = subject.as_bytes();
    let mut out = Vec::new();
    for prefix in ["fln-", "franken_lean-"] {
        let mut from = 0;
        while let Some(pos) = subject[from..].find(prefix) {
            let start = from + pos;
            // Reject a longer identifier bleeding into the prefix (e.g. the
            // crate token in "myfln-x"): the char before must not be a word
            // char. "franken_lean-" contains "fln-"? It does not, but "_" and
            // alphanumerics before the prefix are still rejected.
            if start > 0 {
                let prev = bytes[start - 1];
                if prev.is_ascii_alphanumeric() || prev == b'_' {
                    from = start + prefix.len();
                    continue;
                }
            }
            let tail = &subject[start + prefix.len()..];
            let end = tail
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '.' || c == '-' || c == '_'))
                .unwrap_or(tail.len());
            let token = format!("{prefix}{}", &tail[..end]);
            let token = token.trim_end_matches(['.', '-']).to_string();
            if token.len() > prefix.len() {
                out.push(token);
            }
            from = start + prefix.len();
        }
    }
    out
}

/// The classifier: open, unclaimed, named by at least one landed subject, and
/// silent for longer than [`STALE_DAYS`]. Pure over its inputs so every cell
/// below injects rather than mocks.
fn stale_unclaimed_findings(
    beads: &[BeadRec],
    commits: &[(i64, String)],
    now_unix: i64,
    join_floor: usize,
) -> Result<Vec<Finding>, ScanRefusal> {
    if beads.is_empty() {
        return Err(ScanRefusal::NoBeads);
    }
    if commits.is_empty() {
        return Err(ScanRefusal::NoCommits);
    }
    let by_id: BTreeMap<&str, &BeadRec> = beads.iter().map(|b| (b.id.as_str(), b)).collect();
    let mut newest: BTreeMap<&str, i64> = BTreeMap::new();
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    let mut joined = 0usize;
    for (ct, subject) in commits {
        for token in subject_tokens(subject) {
            if let Some((id, _)) = by_id.get_key_value(token.as_str()) {
                joined += 1;
                let slot = newest.entry(id).or_insert(i64::MIN);
                *slot = (*slot).max(*ct);
                *counts.entry(id).or_insert(0) += 1;
            }
        }
    }
    if joined < join_floor {
        return Err(ScanRefusal::JoinBelowFloor {
            joined,
            floor: join_floor,
        });
    }
    let stale_secs = STALE_DAYS * 86_400;
    let mut findings = Vec::new();
    for (id, ts) in &newest {
        let bead = by_id[id];
        let unclaimed = bead
            .assignee
            .as_deref()
            .map(|a| a.trim().is_empty())
            .unwrap_or(true);
        if bead.status == "open" && unclaimed && now_unix - ts > stale_secs {
            findings.push(Finding {
                bead: (*id).to_string(),
                newest_commit_age_days: (now_unix - ts) / 86_400,
                landed_subjects: counts[id],
            });
        }
    }
    Ok(findings)
}

fn rec(id: &str, status: &str, assignee: Option<&str>) -> BeadRec {
    BeadRec {
        id: id.to_string(),
        status: status.to_string(),
        assignee: assignee.map(str::to_string),
    }
}

const DAY: i64 = 86_400;
const NOW: i64 = 1_900_000_000;

#[test]
fn a_stale_unclaimed_bead_with_landed_subjects_is_a_finding() {
    let beads = [rec("fln-xx1", "open", None)];
    let commits = [(NOW - 5 * DAY, "feat(core): fln-xx1 slice 1".to_string())];
    let found = stale_unclaimed_findings(&beads, &commits, NOW, 0).expect("scan runs");
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].bead, "fln-xx1");
    assert_eq!(found[0].newest_commit_age_days, 5);
}

#[test]
fn a_claimed_or_closed_bead_is_never_a_finding() {
    let beads = [
        rec("fln-xx1", "open", Some("SomePane")),
        rec("fln-xx2", "in_progress", None),
        rec("fln-xx3", "closed", None),
    ];
    let commits = [
        (NOW - 9 * DAY, "fln-xx1: landed".to_string()),
        (NOW - 9 * DAY, "fln-xx2: landed".to_string()),
        (NOW - 9 * DAY, "fln-xx3: landed".to_string()),
    ];
    let found = stale_unclaimed_findings(&beads, &commits, NOW, 0).expect("scan runs");
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_recent_landing_is_not_stale_and_the_newest_commit_governs() {
    let beads = [rec("fln-xx1", "open", None)];
    let commits = [
        (NOW - 30 * DAY, "fln-xx1: old slice".to_string()),
        (NOW - DAY, "fln-xx1: fresh slice".to_string()),
    ];
    let found = stale_unclaimed_findings(&beads, &commits, NOW, 0).expect("scan runs");
    assert!(
        found.is_empty(),
        "a fresh landing must reset the clock: {found:?}"
    );
}

#[test]
fn a_token_matching_no_bead_is_ignored_and_crate_names_do_not_join() {
    // "fln-kernel" is a crate, not a bead: with no such bead id the subject
    // must contribute nothing, which is what keeps the join's precision.
    let beads = [rec("fln-xx1", "open", None)];
    let commits = [(NOW - 9 * DAY, "feat(fln-kernel): admission".to_string())];
    let found = stale_unclaimed_findings(&beads, &commits, NOW, 0).expect("scan runs");
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn an_empty_scan_refuses_rather_than_reporting_clean() {
    let beads = [rec("fln-xx1", "open", None)];
    let commits = [(NOW, "fln-xx1: x".to_string())];
    assert_eq!(
        stale_unclaimed_findings(&[], &commits, NOW, 0),
        Err(ScanRefusal::NoBeads)
    );
    assert_eq!(
        stale_unclaimed_findings(&beads, &[], NOW, 0),
        Err(ScanRefusal::NoCommits)
    );
    let starved = stale_unclaimed_findings(&beads, &[(NOW, "no tokens here".to_string())], NOW, 1);
    assert_eq!(
        starved,
        Err(ScanRefusal::JoinBelowFloor {
            joined: 0,
            floor: 1
        }),
        "a tokenizer that stops matching must refuse, not report a clean tree"
    );
}

#[test]
fn the_prefix_is_matched_at_a_word_boundary() {
    let beads = [rec("fln-xx1", "open", None)];
    let commits = [(
        NOW - 9 * DAY,
        "prefln-xx1 is not a bead reference".to_string(),
    )];
    let found = stale_unclaimed_findings(&beads, &commits, NOW, 0).expect("scan runs");
    assert!(found.is_empty(), "{found:?}");
}

/// The real-tree binding: every finding over the actual repository must be a
/// seeded entry (one-way), the scan must clear its anti-vacuity floors, and
/// the seeded table must respect its ceiling. Entries whose beads recovered
/// are printed for tidying and are deliberately NOT a failure.
#[test]
fn the_done_but_open_population_is_declared_one_way_with_floors() {
    let root = fln_conformance::checked_workspace_root!();

    let raw = fs::read_to_string(root.join(".beads/issues.jsonl"))
        .expect("the tracker export must be readable (absent on rch workers; run locally)");
    let mut beads = Vec::new();
    for line in raw.lines() {
        let id = json_str_field(line, "id");
        let status = json_str_field(line, "status");
        if let (Some(id), Some(status)) = (id, status) {
            beads.push(BeadRec {
                id,
                status,
                assignee: json_str_field(line, "assignee"),
            });
        }
    }
    assert!(
        beads.len() >= 50,
        "beads parse floor: {} records is a broken parse, not a small tracker",
        beads.len()
    );

    let log = Command::new("git")
        .arg("-C")
        .arg(&root)
        .args(["log", "--format=%ct%x00%s", "refs/heads/main"])
        .output()
        .expect("git must be invocable (absent on rch workers; run locally)");
    assert!(
        log.status.success(),
        "git log must succeed: {}",
        String::from_utf8_lossy(&log.stderr)
    );
    let mut commits = Vec::new();
    for line in String::from_utf8_lossy(&log.stdout).lines() {
        if let Some((ct, subject)) = line.split_once('\0')
            && let Ok(ct) = ct.parse::<i64>()
        {
            commits.push((ct, subject.to_string()));
        }
    }
    assert!(
        commits.len() >= 500,
        "commit parse floor: {} subjects is a broken parse for this repository",
        commits.len()
    );

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after epoch")
        .as_secs() as i64;

    // Join floor 100 against a measured 748: a tokenizer regression loses an
    // order of magnitude before it loses the floor, and the floor still stops
    // the zero-join green.
    let findings = stale_unclaimed_findings(&beads, &commits, now, 100)
        .unwrap_or_else(|refusal| panic!("the real-tree scan refused: {refusal:?}"));

    assert!(
        SEEDED_REMAINDER.len() <= SEEDED_CEILING,
        "the seeded remainder outgrew its ceiling: {} > {SEEDED_CEILING}",
        SEEDED_REMAINDER.len()
    );
    let mut seeded_ids: Vec<&str> = SEEDED_REMAINDER.iter().map(|(id, _)| *id).collect();
    let seeded_sorted = {
        let mut s = seeded_ids.clone();
        s.sort_unstable();
        s.dedup();
        s
    };
    assert_eq!(
        seeded_ids.len(),
        seeded_sorted.len(),
        "seeded entries must be unique"
    );
    seeded_ids.sort_unstable();

    let undeclared: Vec<&Finding> = findings
        .iter()
        .filter(|f| seeded_ids.binary_search(&f.bead.as_str()).is_err())
        .collect();
    assert!(
        undeclared.is_empty(),
        "DONE-BUT-OPEN (bead fln-db39): landed commits name these open unclaimed \
         beads and nothing has moved for over {STALE_DAYS} days. For each: CLAIM \
         it if you are driving it, CLOSE it with its judgement row if the work is \
         done, or add a deliberate entry to SEEDED_REMAINDER in this file naming \
         why it legitimately stays open. Do not silence the scan.\n{:#?}",
        undeclared
    );

    let finding_ids: Vec<&str> = findings.iter().map(|f| f.bead.as_str()).collect();
    for (id, reason) in SEEDED_REMAINDER {
        if !finding_ids.contains(id) {
            // One-way by design: a recovered bead must never redden the pane
            // that claimed, closed, or landed fresh work on it.
            println!(
                "done_but_open: seeded entry retired-in-fact, tidy when convenient: {id} ({reason})"
            );
        }
    }
}

/// Minimal JSON string-field reader for the flat tracker export: finds
/// `"field":"value"` or `"field": "value"` at top level.
fn json_str_field(line: &str, field: &str) -> Option<String> {
    let needle_no_space = format!("\"{field}\":\"");
    let needle_with_space = format!("\"{field}\": \"");
    let (start, needle_len) = if let Some(pos) = line.find(&needle_no_space) {
        (pos + needle_no_space.len(), needle_no_space.len())
    } else {
        let pos = line.find(&needle_with_space)?;
        (pos + needle_with_space.len(), needle_with_space.len())
    };
    let _ = needle_len;
    let rest = &line[start..];
    let mut out = String::new();
    let mut chars = rest.chars();
    while let Some(c) = chars.next() {
        match c {
            '"' => return Some(out),
            '\\' => {
                if let Some(escaped) = chars.next() {
                    out.push(escaped);
                }
            }
            _ => out.push(c),
        }
    }
    None
}
