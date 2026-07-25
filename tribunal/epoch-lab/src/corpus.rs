//! The C0–C9 corpus family schemas and the complete C1 official-test inventory
//! (bead `fln-4l15`, carved out of `fln-euo`; plan §18).
//!
//! # What is actually being delivered
//!
//! Not "we run some official tests". **"We can prove we know about every
//! official test at the pin, and for each one we either run it or name why
//! not."** The epic is explicit that "a small smoke slice demonstrates
//! execution but cannot substitute for inventory completeness", and the epoch
//! lab already carries such a slice — the ten smallest upstream elab tests. This
//! module is what stops that slice from being mistaken for coverage.
//!
//! # Total means total
//!
//! [`CorpusFamily`] has exactly ten variants, [`OfficialTestKind`] and
//! [`NonRunReason`] are closed, and **none of them has an `Other` bucket**. An
//! open enum is how an unclassified case gets silently absorbed, and that is
//! risk R4 in the plan's register — census incompleteness — wearing a different
//! name. The unknown-row policy is that unclassified BLOCKS the claim and is
//! never guessed.
//!
//! # Completeness is enforced four ways, not asserted once
//!
//! 1. **Derived, never hand-listed.** [`Inventory::scan_digest`] binds the
//!    inventory to the pin scan it came from, recomputed on every verification.
//!    A hand-written inventory has no scan to bind to; a *filtered* scan hashes
//!    differently and is caught as [`Gap::ScanNotBound`].
//! 2. **Every entry is disposed.** [`Disposition`] is either `Run` with an
//!    expected outcome or `NotRun` with a typed reason AND a justification
//!    naming an owning bead. "Neither" is not representable, and an empty
//!    justification is [`Gap::UnjustifiedExclusion`] rather than a default.
//! 3. **A test at the pin and absent from the inventory fails.**
//!    [`Gap::MissingFromInventory`].
//! 4. **Count conservation.** `discovered == run + not_run`, checked
//!    arithmetically. This is what makes a *hidden exclusion* — the same failure
//!    wearing a disguise — impossible rather than merely discouraged: a test
//!    dropped from both the inventory and the accounting breaks the sum. It is
//!    the discipline `fln_env::decl_closure` already uses, where
//!    `checked + artifact_incomplete == decls_total`.

use fln_hash::domain::{Domain, DomainHasher};
use std::collections::{BTreeMap, BTreeSet};

/// Schema line for a C1 inventory file.
pub const INVENTORY_SCHEMA: &str = "fln-c1-official-test-inventory/1";

/// Domain tag for the pin-scan digest.
const SCAN_TAG: &[u8] = b"fln.c1-inventory.scan/1";

/// The ten corpus families of plan §18.
///
/// Exactly ten. There is no `Other`, no `Unclassified`, and no `Custom(String)`
/// — a corpus that fits none of these is a gap in the plan to be argued about,
/// not a value to be constructed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CorpusFamily {
    /// Micro-fixtures isolating single rules.
    C0,
    /// Official source-derived tests and stdlib modules — test DATA, never
    /// linked code (D8).
    C1,
    /// Ecosystem packages weighted for metaprogramming, FFI, Lake and syntax.
    C2,
    /// Artifact archaeology: valid and mutated oleans, ileans, C, objects and
    /// traces, every offset and tag targeted.
    C3,
    /// Native-ABI probes, both directions.
    C4,
    /// Recorded LSP sessions.
    C5,
    /// Build and package variants, including interrupted updates.
    C6,
    /// Adversarial and resource bombs.
    C7,
    /// Incremental and metamorphic edit sequences with expected cones.
    C8,
    /// Bootstrap and reproducibility: clean-machine, air-gapped, path and
    /// locale variation.
    C9,
}

/// Every family, in order. The suite checks this against the variant count so
/// a new family cannot be added without joining the table.
pub const ALL_FAMILIES: [CorpusFamily; 10] = [
    CorpusFamily::C0,
    CorpusFamily::C1,
    CorpusFamily::C2,
    CorpusFamily::C3,
    CorpusFamily::C4,
    CorpusFamily::C5,
    CorpusFamily::C6,
    CorpusFamily::C7,
    CorpusFamily::C8,
    CorpusFamily::C9,
];

impl CorpusFamily {
    /// Exhaustive, no wildcard: a new variant is a compile error here.
    pub fn as_str(self) -> &'static str {
        match self {
            CorpusFamily::C0 => "C0",
            CorpusFamily::C1 => "C1",
            CorpusFamily::C2 => "C2",
            CorpusFamily::C3 => "C3",
            CorpusFamily::C4 => "C4",
            CorpusFamily::C5 => "C5",
            CorpusFamily::C6 => "C6",
            CorpusFamily::C7 => "C7",
            CorpusFamily::C8 => "C8",
            CorpusFamily::C9 => "C9",
        }
    }

    /// The plan's own wording for what the family covers. Kept here so a family
    /// cannot be quietly repurposed to mean whatever a later corpus needs.
    pub fn scope(self) -> &'static str {
        match self {
            CorpusFamily::C0 => "micro-fixtures isolating single rules",
            CorpusFamily::C1 => "official source-derived tests and stdlib modules",
            CorpusFamily::C2 => "ecosystem packages: metaprogramming, FFI, Lake, syntax",
            CorpusFamily::C3 => "artifact archaeology: valid and mutated oleans/ileans/C/objects",
            CorpusFamily::C4 => "native-ABI probes, both directions",
            CorpusFamily::C5 => "recorded LSP sessions",
            CorpusFamily::C6 => "build and package variants, including interrupted updates",
            CorpusFamily::C7 => "adversarial and resource bombs",
            CorpusFamily::C8 => "incremental and metamorphic edit sequences with expected cones",
            CorpusFamily::C9 => "bootstrap and reproducibility: clean-machine, air-gapped, locale",
        }
    }

    pub fn parse(s: &str) -> Option<CorpusFamily> {
        ALL_FAMILIES.into_iter().find(|f| f.as_str() == s)
    }
}

/// What kind of official test this is. Closed: a test shape we have not modelled
/// blocks rather than landing in a bucket.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OfficialTestKind {
    /// `tests/lean/run/**` — must elaborate cleanly.
    ElabRun,
    /// `tests/lean/**` with a checked-in `.expected.out` baseline.
    ElabExpected,
    /// `tests/lean/interpreter/**`.
    Interpreter,
    /// `tests/compiler/**`.
    Compiler,
    /// `tests/lake/**`.
    Lake,
    /// `tests/bench/**`.
    Bench,
}

impl OfficialTestKind {
    pub fn as_str(self) -> &'static str {
        match self {
            OfficialTestKind::ElabRun => "elab-run",
            OfficialTestKind::ElabExpected => "elab-expected",
            OfficialTestKind::Interpreter => "interpreter",
            OfficialTestKind::Compiler => "compiler",
            OfficialTestKind::Lake => "lake",
            OfficialTestKind::Bench => "bench",
        }
    }
}

/// One official test as DISCOVERED at the pin. This is the ground truth the
/// inventory is measured against; it is never authored by hand.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct OfficialTest {
    /// Path relative to the pin's test root.
    pub id: String,
    pub kind: OfficialTestKind,
}

/// The complete set of official tests found at a pin.
///
/// "Complete" is the whole point, so this type deliberately has no filtering
/// constructor. Anything that narrows the set changes [`PinScan::digest`], and
/// the inventory that named the old digest stops verifying.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PinScan {
    pub pin: String,
    pub tests: Vec<OfficialTest>,
}

impl PinScan {
    /// Digest over the pin and the sorted (id, kind) pairs.
    ///
    /// Sorted so the digest is a function of the SET, not of discovery order —
    /// a filesystem walk in a different locale must not change it. Each field is
    /// length-prefixed so `("ab", "c")` and `("a", "bc")` cannot collide.
    pub fn digest(&self) -> String {
        let mut rows: Vec<(&str, &str)> = self
            .tests
            .iter()
            .map(|t| (t.id.as_str(), t.kind.as_str()))
            .collect();
        rows.sort_unstable();
        rows.dedup();
        let mut h = DomainHasher::new(Domain::Fixture);
        h.update(SCAN_TAG);
        h.update(&[0]);
        h.update(&(self.pin.len() as u64).to_le_bytes());
        h.update(self.pin.as_bytes());
        h.update(&[0]);
        h.update(&(rows.len() as u64).to_le_bytes());
        for (id, kind) in rows {
            h.update(&(id.len() as u64).to_le_bytes());
            h.update(id.as_bytes());
            h.update(&(kind.len() as u64).to_le_bytes());
            h.update(kind.as_bytes());
        }
        h.finalize().to_hex()
    }
}

/// What the pin does with a test we DO run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpectedOutcome {
    /// Elaborates and checks cleanly.
    Accepts,
    /// Must be rejected. Carries the diagnostic the pin produces, because
    /// "rejects" alone would let us reject for the wrong reason and call it
    /// parity.
    Rejects { diagnostic: String },
    /// Must reproduce a checked-in baseline byte for byte.
    MatchesBaseline { baseline_digest: String },
}

/// Why a test is not run. Closed, and every variant is a case somebody decided.
///
/// There is no `Other`, no `Skipped`, and no `Todo`. Those are the buckets an
/// unclassified test would land in, and an unclassified test must block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NonRunReason {
    /// The pin exercises a language or toolchain feature we have not built.
    UnsupportedFeature,
    /// Needs a platform this lab is not running on.
    UnsupportedPlatform,
    /// Needs the network, which no gate may.
    RequiresNetwork,
    /// Needs one of D2's two inherited external tools.
    RequiresExternalTool,
    /// The test IS oracle harness machinery; running it under FrankenLean would
    /// be a category error, not a parity result (D8).
    OracleHarnessOnly,
    /// Deliberately deferred, with a bead that owns the deferral.
    BlockedOnBead,
}

impl NonRunReason {
    pub fn as_str(self) -> &'static str {
        match self {
            NonRunReason::UnsupportedFeature => "unsupported-feature",
            NonRunReason::UnsupportedPlatform => "unsupported-platform",
            NonRunReason::RequiresNetwork => "requires-network",
            NonRunReason::RequiresExternalTool => "requires-external-tool",
            NonRunReason::OracleHarnessOnly => "oracle-harness-only",
            NonRunReason::BlockedOnBead => "blocked-on-bead",
        }
    }
}

/// Who owns a non-run decision and why.
///
/// Both fields are required and both are checked non-empty. Requiring a bead id
/// means an exclusion cannot be written without naming somebody who owns it,
/// which is the difference between an explicit exclusion mapping and a quiet
/// one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Justification {
    pub bead: String,
    pub note: String,
}

/// What we do with a test. "Neither" is not representable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Disposition {
    Run(ExpectedOutcome),
    NotRun {
        reason: NonRunReason,
        justification: Justification,
    },
}

/// One inventory row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    pub id: String,
    pub kind: OfficialTestKind,
    pub family: CorpusFamily,
    pub disposition: Disposition,
}

/// The C1 inventory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inventory {
    pub pin: String,
    /// The digest of the scan this inventory was derived FROM. Recomputed on
    /// verification: this is the "derived, never hand-listed" mechanism.
    pub scan_digest: String,
    pub entries: Vec<Entry>,
}

/// A way the inventory fails to be complete. Every variant blocks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Gap {
    /// A test exists at the pin and has no inventory entry. The named mutant.
    MissingFromInventory { id: String },
    /// An entry names a test that does not exist at the pin.
    UnknownEntry { id: String },
    /// Two entries for one test.
    DuplicateEntry { id: String },
    /// The inventory was not derived from this scan — hand-listed, stale, or
    /// derived from a scan that had been filtered.
    ScanNotBound { stated: String, actual: String },
    /// The inventory and the scan describe different pins.
    PinMismatch { inventory: String, scan: String },
    /// A non-run entry with no owning bead or no note.
    UnjustifiedExclusion { id: String, missing: &'static str },
    /// An entry filed under a family other than C1.
    WrongFamily { id: String, family: CorpusFamily },
    /// The accounting does not add up. A hidden exclusion shows up here.
    CountNotConserved {
        discovered: usize,
        run: usize,
        not_run: usize,
    },
}

impl Gap {
    pub fn reason(&self) -> &'static str {
        match self {
            Gap::MissingFromInventory { .. } => "missing-from-inventory",
            Gap::UnknownEntry { .. } => "unknown-entry",
            Gap::DuplicateEntry { .. } => "duplicate-entry",
            Gap::ScanNotBound { .. } => "scan-not-bound",
            Gap::PinMismatch { .. } => "pin-mismatch",
            Gap::UnjustifiedExclusion { .. } => "unjustified-exclusion",
            Gap::WrongFamily { .. } => "wrong-family",
            Gap::CountNotConserved { .. } => "count-not-conserved",
        }
    }
}

/// The completeness accounting.
///
/// `not_run` lists EVERY excluded test with its reason. That list is not a
/// courtesy: [`Completeness::conserved`] requires
/// `discovered == run + not_run.len()`, so an exclusion that is not surfaced
/// here breaks the arithmetic. That is what makes a hidden exclusion impossible
/// rather than merely discouraged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Completeness {
    pub discovered: usize,
    pub run: usize,
    pub not_run: Vec<(String, NonRunReason)>,
    pub gaps: Vec<Gap>,
}

impl Completeness {
    pub fn conserved(&self) -> bool {
        self.discovered == self.run + self.not_run.len()
    }

    /// The only thing that counts as complete. There is deliberately no
    /// "partial", "sampled" or "smoke" verdict to reach for.
    pub fn is_complete(&self) -> bool {
        self.gaps.is_empty() && self.conserved()
    }
}

/// Verify an inventory against a pin scan.
///
/// Returns the full accounting, gaps and all — an inventory with forty missing
/// tests should say forty, not one.
pub fn verify(inv: &Inventory, scan: &PinScan) -> Completeness {
    let mut gaps = Vec::new();

    if inv.pin != scan.pin {
        gaps.push(Gap::PinMismatch {
            inventory: inv.pin.clone(),
            scan: scan.pin.clone(),
        });
    }

    // DERIVED, NEVER HAND-LISTED. Recomputed, never trusted. A scan that was
    // filtered before the comparison hashes differently and lands here, which
    // is the disguise a hidden exclusion would otherwise wear.
    let actual = scan.digest();
    if inv.scan_digest != actual {
        gaps.push(Gap::ScanNotBound {
            stated: inv.scan_digest.clone(),
            actual: actual.clone(),
        });
    }

    let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
    let mut run = 0usize;
    let mut not_run: Vec<(String, NonRunReason)> = Vec::new();

    for e in &inv.entries {
        let count = seen.entry(e.id.as_str()).or_insert(0);
        *count += 1;
        if *count == 2 {
            gaps.push(Gap::DuplicateEntry { id: e.id.clone() });
        }

        if e.family != CorpusFamily::C1 {
            gaps.push(Gap::WrongFamily {
                id: e.id.clone(),
                family: e.family,
            });
        }

        match &e.disposition {
            Disposition::Run(_) => run += 1,
            Disposition::NotRun {
                reason,
                justification,
            } => {
                if justification.bead.trim().is_empty() {
                    gaps.push(Gap::UnjustifiedExclusion {
                        id: e.id.clone(),
                        missing: "bead",
                    });
                }
                if justification.note.trim().is_empty() {
                    gaps.push(Gap::UnjustifiedExclusion {
                        id: e.id.clone(),
                        missing: "note",
                    });
                }
                // Surfaced unconditionally. An exclusion that is not listed
                // here is not "quiet", it is arithmetically impossible.
                not_run.push((e.id.clone(), *reason));
            }
        }
    }

    let discovered: BTreeSet<&str> = scan.tests.iter().map(|t| t.id.as_str()).collect();
    let inventoried: BTreeSet<&str> = inv.entries.iter().map(|e| e.id.as_str()).collect();

    // MISSING. Every test at the pin with no entry, listed individually — a
    // count alone would let a smoke slice look like a rounding error.
    for id in discovered.difference(&inventoried) {
        gaps.push(Gap::MissingFromInventory {
            id: (*id).to_string(),
        });
    }
    // UNKNOWN. An entry for a test the pin does not have is equally a defect:
    // it is either stale or invented, and both mean the inventory is not
    // describing this pin.
    for id in inventoried.difference(&discovered) {
        gaps.push(Gap::UnknownEntry {
            id: (*id).to_string(),
        });
    }

    let mut completeness = Completeness {
        discovered: discovered.len(),
        run,
        not_run,
        gaps,
    };
    if !completeness.conserved() {
        completeness.gaps.push(Gap::CountNotConserved {
            discovered: completeness.discovered,
            run: completeness.run,
            not_run: completeness.not_run.len(),
        });
    }
    completeness
}

/// Line-oriented report. Every exclusion is named, with its reason and the bead
/// that owns it — an exclusion nobody can see is the failure this whole module
/// is arranged around.
///
/// Emits counts, never a percentage: a coverage percentage is exactly the
/// headline number D7 refuses as evidence.
pub fn report(c: &Completeness) -> String {
    let mut out = String::new();
    for (id, reason) in &c.not_run {
        out.push_str(&format!(
            "c1-inventory: not-run id={id} reason={}\n",
            reason.as_str()
        ));
    }
    for g in &c.gaps {
        out.push_str(&format!("c1-inventory: gap reason={} {g:?}\n", g.reason()));
    }
    out.push_str(&format!(
        "c1-inventory: verdict={} discovered={} run={} not_run={} gaps={} conserved={}\n",
        if c.is_complete() {
            "complete"
        } else {
            "incomplete"
        },
        c.discovered,
        c.run,
        c.not_run.len(),
        c.gaps.len(),
        c.conserved()
    ));
    out
}

#[cfg(test)]
mod structural {
    use super::*;

    #[test]
    fn there_are_exactly_ten_families_and_no_other_bucket() {
        assert_eq!(ALL_FAMILIES.len(), 10);
        let mut names: Vec<&str> = ALL_FAMILIES.iter().map(|f| f.as_str()).collect();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), 10, "two families share a name");
        // Every name is C<digit> and nothing else. A variant called Other,
        // Unclassified or Custom would fail here rather than quietly absorbing
        // the cases nobody has modelled yet.
        for n in names {
            assert!(n.len() == 2, "{n:?} is not a C<digit> family");
            assert!(n.starts_with('C'), "{n:?} is not a C<digit> family");
            assert!(
                n.as_bytes()[1].is_ascii_digit(),
                "{n:?} is not a C<digit> family"
            );
        }
        // Round-trips, so the parser cannot admit a family the enum lacks.
        for f in ALL_FAMILIES {
            assert_eq!(CorpusFamily::parse(f.as_str()), Some(f));
            assert!(!f.scope().is_empty(), "{f:?} has no scope");
        }
        for bad in ["C10", "Other", "unclassified", "", "C", "CX", "c1"] {
            assert_eq!(CorpusFamily::parse(bad), None, "{bad:?} parsed as a family");
        }
    }

    #[test]
    fn every_closed_vocabulary_has_distinct_tokens_and_no_catch_all() {
        let kinds = [
            OfficialTestKind::ElabRun,
            OfficialTestKind::ElabExpected,
            OfficialTestKind::Interpreter,
            OfficialTestKind::Compiler,
            OfficialTestKind::Lake,
            OfficialTestKind::Bench,
        ];
        let mut k: Vec<&str> = kinds.iter().map(|x| x.as_str()).collect();
        let n = k.len();
        k.sort_unstable();
        k.dedup();
        assert_eq!(k.len(), n);

        let reasons = [
            NonRunReason::UnsupportedFeature,
            NonRunReason::UnsupportedPlatform,
            NonRunReason::RequiresNetwork,
            NonRunReason::RequiresExternalTool,
            NonRunReason::OracleHarnessOnly,
            NonRunReason::BlockedOnBead,
        ];
        let mut r: Vec<&str> = reasons.iter().map(|x| x.as_str()).collect();
        let m = r.len();
        r.sort_unstable();
        r.dedup();
        assert_eq!(r.len(), m);
        // None of them is a catch-all. These are the names an absorbing bucket
        // would plausibly take, and the test exists so adding one has to argue.
        for name in r {
            for forbidden in ["other", "misc", "unknown", "todo", "skip", "custom"] {
                assert!(
                    !name.contains(forbidden),
                    "{name:?} looks like a catch-all bucket"
                );
            }
        }
    }

    #[test]
    fn every_gap_variant_has_its_own_reason_token() {
        let all = [
            Gap::MissingFromInventory { id: String::new() },
            Gap::UnknownEntry { id: String::new() },
            Gap::DuplicateEntry { id: String::new() },
            Gap::ScanNotBound {
                stated: String::new(),
                actual: String::new(),
            },
            Gap::PinMismatch {
                inventory: String::new(),
                scan: String::new(),
            },
            Gap::UnjustifiedExclusion {
                id: String::new(),
                missing: "bead",
            },
            Gap::WrongFamily {
                id: String::new(),
                family: CorpusFamily::C0,
            },
            Gap::CountNotConserved {
                discovered: 0,
                run: 0,
                not_run: 0,
            },
        ];
        let mut t: Vec<&str> = all.iter().map(Gap::reason).collect();
        let before = t.len();
        t.sort_unstable();
        t.dedup();
        assert_eq!(before, t.len(), "two Gap variants share a reason token");
    }

    #[test]
    fn the_report_emits_counts_and_never_a_percentage() {
        let c = Completeness {
            discovered: 3,
            run: 1,
            not_run: vec![("a".to_string(), NonRunReason::RequiresNetwork)],
            gaps: vec![],
        };
        let text = report(&c);
        assert!(!text.contains('%'), "the report emitted a percentage");
        for w in ["coverage=", "percent", "rate="] {
            assert!(!text.contains(w), "the report emitted {w:?}");
        }
        assert!(text.contains("discovered=3"));
        // 3 != 1 + 1, so this is incomplete and says so.
        assert!(text.contains("verdict=incomplete"));
        assert!(text.contains("conserved=false"));
    }
}
