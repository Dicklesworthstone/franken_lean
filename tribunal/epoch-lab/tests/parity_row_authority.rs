//! Suite `parity_row_authority` (bead `franken_lean-9pnc`; plan §18, doctrine D7).
//!
//! The name is the one `fln-euo` enumerates in its closure criteria, alongside
//! `epoch_lab_hash_chain`, `oracle_outcome_authority` and `typed_normalizer_model`.
//! The epic's coverage phrase for it — "row freshness/roots/claims" — is exactly
//! what is tested here.
//!
//! # What is under test
//!
//! **The Parity Ledger is row-per-symbol or it is marketing.** So: a row cannot
//! exist without naming a real fixture, exact roots, its oracle and comparison
//! class, its D7 claim type, its evidence state, its L-level, mode and platform,
//! its stated limitations, and its freshness. And the epic's acceptance
//! criteria — missing, duplicate, stale, unknown, root-mismatched, mock-only,
//! overclaimed — are encoded as refusals rather than lint.
//!
//! # Every refusal fires for its own reason
//!
//! Each test asserts the specific [`Block::reason`] token, never merely that the
//! ledger was refused. A suite that only checked "some block fired" would let a
//! mutant that breaks the duplicate rule be silently covered by the unknown
//! rule, and the mutation campaign would prove nothing.
//!
//! # Mutants planted and killed
//!
//! One per blocking condition, each proven to fail for its own reason. The
//! "killed by" column is the MEASURED result of running each mutant, not the
//! test that was expected to catch it:
//!
//! | mutant | edit | killed by |
//! |---|---|---|
//! | missing not blocked | the `MissingSymbol` loop is skipped | `a_missing_symbol_blocks`, `a_ledger_reports_every_block_it_finds_not_the_first` |
//! | duplicate not blocked | duplicate detection fires at `count == 3` | `a_duplicate_row_blocks` |
//! | stale not blocked | revision compared with `starts_with` instead of `!=` | `a_revision_that_merely_prefixes_the_head_is_still_stale` **only** |
//! | unknown not blocked | unknown-symbol check replaced by `expected.is_empty()` | `an_unknown_symbol_blocks`, `a_ledger_reports_every_block_it_finds_not_the_first` |
//! | root mismatch not blocked | `ByteIdentical` accepts differing roots | `a_root_mismatch_blocks` |
//! | mock-only not blocked | mock check requires `level_rank > 4` | `a_mock_backed_row_cannot_close_an_l_level`, `the_mock_rule_reads_backing_and_level_and_nothing_else`, and 2 more |
//! | overclaim not blocked | `level_ceiling` returns `L4` for every state | `an_unearned_level_blocks` |
//! | claim/level conflation | the level rule also requires a strong claim type | `the_level_rule_does_not_read_the_claim_type`, `an_unearned_level_blocks` |
//! | aggregate admitted | `is_aggregate_symbol` returns `false` | `an_aggregate_row_blocks` |
//!
//! Schema 2 (`fln-fei1`) added five rules, each planted and measured the same
//! way:
//!
//! | mutant | edit | killed by |
//! |---|---|---|
//! | misscored not blocked | the `derived != stated` push is skipped | `a_row_whose_assessment_its_own_sides_do_not_support_is_refused`, `a_non_answer_from_either_side_is_never_a_divergence_in_a_row`, `an_oracle_silent_symbol_is_expressible_and_the_old_lie_is_refused` |
//! | disposition not blocked | the `(divergence, NotADivergence)` arm is dropped | `a_divergence_must_say_whether_it_was_called` **only** |
//! | uncompared not blocked | both arms guarded `if false` | `a_comparison_class_is_named_exactly_when_something_was_compared`, `an_oracle_silent_symbol_is_expressible_and_the_old_lie_is_refused` |
//! | identical roots under a divergence admitted | the `a == b` check inside the divergence arm is dropped | `a_divergence_whose_roots_are_identical_is_refused` **only** |
//! | silent oracle's root admitted | the uncompared arm stops reading `oracle_root` | `a_silent_oracle_cannot_have_its_root_cited` **only** |
//! | level closed without a comparison | the rule requires `level_rank > 4` | `an_unassessed_symbol_cannot_carry_a_compatibility_level` **only** |
//! | scoring rule copied instead of shared | the verifier re-implements the table, mapping every non-answer to `Agree` | `an_oracle_silent_symbol_is_expressible_and_the_old_lie_is_refused`, `an_unassessed_symbol_is_expressible_and_is_not_a_missing_symbol`, `an_unassessed_symbol_cannot_carry_a_compatibility_level`, `a_silent_oracle_cannot_have_its_root_cited`, `the_report_verdicts_on_the_schema_and_says_so` |
//!
//! **The copied-scoring-rule row is the one worth reading here.**
//! `the_scoring_rule_the_ledger_uses_is_the_one_the_rigs_use` did NOT kill it —
//! that test asserts on `score_verdicts` itself, so a private copy inside the
//! verifier leaves it green. What actually catches the copy is the set of rows
//! where a side did not answer: every one of them scores `Agree` under the
//! mutant and the ledger starts agreeing with itself. So the anti-drift
//! property is carried by the non-answer rows, not by the function test, and
//! deleting them to "reduce duplication" would silently restore the hole.
//!
//! **The stale row is the one worth reading.** `a_stale_revision_blocks` did
//! NOT kill the `starts_with` mutant — it uses a revision that is not a prefix
//! of the head, so a prefix-accepting comparison still refuses it and the test
//! still passes. Only `a_revision_that_merely_prefixes_the_head_is_still_stale`
//! catches it. An abbreviated or truncated revision is exactly the shape a
//! real ledger would carry by accident, so without that second test the
//! freshness check could have been weakened to a prefix match and the suite
//! would have stayed green.

#![forbid(unsafe_code)]

use fln_epoch_lab::oracle::{
    ClaimType, EvidenceState, LLevel, Mode, NonAuthoritative, OracleVerdict, OurVerdict, Platform,
    score_verdicts,
};
use fln_epoch_lab::parity::{
    Assessment, Block, Ledger, OUTCOME_SCHEMA, ROW_FIELDS, census, is_aggregate_symbol, parse,
    report, verify, verify_with_fixtures,
};
use std::path::PathBuf;

/// The chain every fixture's freshness is judged against — a REAL genesis
/// chain, not a hex literal, because `VerifiedHead`'s only constructor is
/// `From<&Chain>` (bead `fln-8fwh`): the API change this suite absorbs is that
/// a caller can no longer write a head down, and a schema test pays the same
/// price as a gate on purpose.
static CHAIN: std::sync::LazyLock<fln_epoch_lab::Chain> = std::sync::LazyLock::new(|| {
    fln_epoch_lab::Chain::genesis(
        "v4.32.0",
        fln_epoch_lab::content_digest(b"parity schema fixture manifest"),
    )
});
static HEAD: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| CHAIN.head_root_hex());

fn vh() -> fln_epoch_lab::parity::VerifiedHead {
    fln_epoch_lab::parity::VerifiedHead::from(&*CHAIN)
}
const ROOT_A: &str = "1111111111111111111111111111111111111111111111111111111111111111";
const ROOT_B: &str = "2222222222222222222222222222222222222222222222222222222222222222";
const FIXTURE_DIGEST: &str = "3333333333333333333333333333333333333333333333333333333333333333";

/// A row builder that starts from a fully valid row, so every test changes
/// exactly one thing and the reason a ledger was refused is unambiguous.
#[derive(Clone)]
struct Row {
    symbol: String,
    ours_root: String,
    oracle_root: String,
    ours_verdict: String,
    oracle_verdict: String,
    assessment: String,
    disposition: String,
    comparison: String,
    normalizer: String,
    claim: String,
    state: String,
    level: String,
    mode: String,
    platform: String,
    backing: String,
    limits: String,
}

impl Row {
    fn valid(symbol: &str) -> Row {
        Row {
            symbol: symbol.to_string(),
            ours_root: ROOT_A.to_string(),
            oracle_root: ROOT_A.to_string(),
            ours_verdict: "accepted".to_string(),
            oracle_verdict: "accepted".to_string(),
            assessment: "agree".to_string(),
            disposition: "-".to_string(),
            comparison: "byte-identical".to_string(),
            normalizer: "-".to_string(),
            claim: "bounded_model".to_string(),
            state: "observed".to_string(),
            level: "L2".to_string(),
            mode: "sound".to_string(),
            platform: "linux-x86_64".to_string(),
            backing: "real-reference".to_string(),
            limits: "no-known-limitations".to_string(),
        }
    }

    /// The row a restrictive divergence produces: we rejected, the oracle
    /// accepted, the two artifacts necessarily differ, and the cause has not
    /// been called. Under schema 1 this row could not be written at all.
    fn restrictive_uncalled(symbol: &str) -> Row {
        Row {
            oracle_root: ROOT_B.to_string(),
            ours_verdict: "rejected".to_string(),
            oracle_verdict: "accepted".to_string(),
            assessment: "restrictive".to_string(),
            disposition: "uncalled".to_string(),
            // A divergence closes no compatibility level for its symbol.
            level: "L0".to_string(),
            limits: "root-cause deliberately unclassified".to_string(),
            ..Row::valid(symbol)
        }
    }

    /// The row a symbol the oracle does not judge produces: our answer stands,
    /// the oracle never spoke, nothing was compared.
    fn oracle_silent(symbol: &str) -> Row {
        Row {
            oracle_root: "-".to_string(),
            ours_verdict: "accepted".to_string(),
            oracle_verdict: "no-answer:out-of-scope".to_string(),
            assessment: "unscorable".to_string(),
            disposition: "-".to_string(),
            comparison: "-".to_string(),
            level: "L0".to_string(),
            limits: "the pinned checker does not submit this constant".to_string(),
            ..Row::valid(symbol)
        }
    }

    /// The row an unassessed symbol produces: nobody asked either side.
    fn unassessed(symbol: &str) -> Row {
        Row {
            ours_root: "-".to_string(),
            oracle_root: "-".to_string(),
            ours_verdict: "inconclusive:not-assessed-at-this-scope".to_string(),
            oracle_verdict: "no-answer:not-assessed".to_string(),
            assessment: "unscorable".to_string(),
            disposition: "-".to_string(),
            comparison: "-".to_string(),
            level: "L0".to_string(),
            limits: "outside the scope of this run".to_string(),
            ..Row::valid(symbol)
        }
    }

    fn render(&self) -> String {
        format!(
            "row {} fixture=fixtures/nat.lean fixture_digest={FIXTURE_DIGEST} \
             ours_root={} oracle_root={} ours_verdict={} oracle_verdict={} \
             assessment={} disposition={} oracle=reference-binary comparison={} \
             normalizer={} claim={} evidence=differential state={} level={} \
             mode={} platform={} backing={} freshness=current limits={}",
            self.symbol,
            self.ours_root,
            self.oracle_root,
            self.ours_verdict,
            self.oracle_verdict,
            self.assessment,
            self.disposition,
            self.comparison,
            self.normalizer,
            self.claim,
            self.state,
            self.level,
            self.mode,
            self.platform,
            self.backing,
            self.limits,
        )
    }
}

fn ledger_text(revision: &str, rows: &[Row]) -> String {
    let mut s = format!("{OUTCOME_SCHEMA}\nepoch v4.32.0\nrevision {revision}\n");
    for r in rows {
        s.push_str(&r.render());
        s.push('\n');
    }
    s
}

fn parsed(revision: &str, rows: &[Row]) -> Ledger {
    match parse(&ledger_text(revision, rows)) {
        Ok(l) => l,
        Err(b) => panic!("fixture ledger did not parse: {b:?}"),
    }
}

/// The reason tokens a verification produced, in order.
fn reasons(blocks: &[Block]) -> Vec<&'static str> {
    blocks.iter().map(Block::reason).collect()
}

// ---------------------------------------------------------------------------
// The baseline. Everything else is one deviation from this.
// ---------------------------------------------------------------------------

#[test]
fn a_complete_and_current_ledger_passes() {
    // Without this, every refusal test below could be passing because the
    // fixture is broken rather than because the rule works.
    let l = parsed(&HEAD, &[Row::valid("Nat.succ_le_of_lt")]);
    let blocks = verify(&l, &["Nat.succ_le_of_lt"], &vh());
    assert!(blocks.is_empty(), "a valid ledger was refused: {blocks:?}");
    assert!(report(&blocks).contains("verdict=pass"));
}

// ---------------------------------------------------------------------------
// A row cannot exist without naming everything
// ---------------------------------------------------------------------------

#[test]
fn a_row_missing_any_required_field_does_not_parse() {
    // Absence is a refusal, not a default. Drop each field in turn from an
    // otherwise valid row and require that the row does not come into
    // existence — not that it parses with a hole in it.
    let full = Row::valid("Nat.succ_le_of_lt").render();
    let mut dropped = 0usize;
    for field in ROW_FIELDS {
        let needle = format!(" {field}=");
        let Some(at) = full.find(&needle) else {
            panic!("field {field:?} is not in the rendered row");
        };
        let rest = &full[at + 1..];
        let end = rest.find(' ').map_or(full.len(), |e| at + 1 + e);
        let mutilated = format!("{}{}", &full[..at], &full[end..]);
        let head = HEAD.as_str();
        let text = format!("{OUTCOME_SCHEMA}\nepoch v4.32.0\nrevision {head}\n{mutilated}\n");
        assert!(
            parse(&text).is_err(),
            "a row without {field:?} parsed anyway"
        );
        dropped += 1;
    }
    assert_eq!(dropped, ROW_FIELDS.len(), "not every field was exercised");
}

#[test]
fn stated_limitations_must_be_stated() {
    // A row with nothing to say has to write it down. Silence must be an
    // assertion somebody made, not a field somebody forgot.
    let mut r = Row::valid("Nat.succ_le_of_lt");
    r.limits = String::new();
    let text = ledger_text(&HEAD, &[r]);
    match parse(&text) {
        Err(b) => assert_eq!(reasons(&b), vec!["malformed"]),
        Ok(_) => panic!("a row with empty limits= parsed"),
    }
}

#[test]
fn a_reordered_or_repeated_field_does_not_parse() {
    // Fixed field order keeps the file diffable and makes a reordered row a
    // refusal rather than a silent acceptance.
    let head = HEAD.as_str();
    let reordered = format!(
        "{OUTCOME_SCHEMA}\nepoch v4.32.0\nrevision {head}\n\
         row Nat.foo fixture_digest={FIXTURE_DIGEST} fixture=fixtures/nat.lean \
         ours_root={ROOT_A} oracle_root={ROOT_A} oracle=reference-binary \
         comparison=byte-identical normalizer=- claim=bounded_model \
         evidence=differential state=observed level=L2 mode=sound \
         platform=linux-x86_64 backing=real-reference freshness=current \
         limits=none\n"
    );
    assert!(parse(&reordered).is_err(), "a reordered row parsed");

    let repeated = ledger_text(&HEAD, &[Row::valid("Nat.foo")]).replace(
        "oracle=reference-binary",
        "oracle=reference-binary oracle=reference-checker",
    );
    match parse(&repeated) {
        Err(b) => assert_eq!(reasons(&b), vec!["malformed"]),
        Ok(_) => panic!("a row with a repeated field parsed"),
    }
}

#[test]
fn hostile_input_is_refused_and_never_panics() {
    // Totality. Malformed input must not panic (FL-INV-07), and must not
    // become a partially-valid ledger either.
    let head = HEAD.as_str();
    for text in [
        "",
        "not-a-schema",
        OUTCOME_SCHEMA,
        &format!("{OUTCOME_SCHEMA}\n"),
        &format!("{OUTCOME_SCHEMA}\nepoch v4.32.0\n"),
        &format!("{OUTCOME_SCHEMA}\nrevision {head}\n"),
        &format!("{OUTCOME_SCHEMA}\nepoch v\nrevision r\nrow\n"),
        &format!("{OUTCOME_SCHEMA}\nepoch v\nrevision r\nrow x limits=\n"),
        &format!("{OUTCOME_SCHEMA}\nepoch v\nrevision r\nnonsense verb here\n"),
        &format!("{OUTCOME_SCHEMA}\nepoch v\nrevision r\nrow x y z limits=q\n"),
    ] {
        assert!(parse(text).is_err(), "hostile input parsed: {text:?}");
    }
}

// ---------------------------------------------------------------------------
// The seven blocking conditions, each for its own reason
// ---------------------------------------------------------------------------

#[test]
fn a_missing_symbol_blocks() {
    let l = parsed(&HEAD, &[Row::valid("Nat.a")]);
    let blocks = verify(&l, &["Nat.a", "Nat.b"], &vh());
    assert_eq!(reasons(&blocks), vec!["missing"]);
    assert!(matches!(&blocks[0], Block::MissingSymbol { symbol } if symbol == "Nat.b"));
}

#[test]
fn a_duplicate_row_blocks() {
    let l = parsed(&HEAD, &[Row::valid("Nat.a"), Row::valid("Nat.a")]);
    let blocks = verify(&l, &["Nat.a"], &vh());
    assert_eq!(reasons(&blocks), vec!["duplicate"]);
    match &blocks[0] {
        Block::DuplicateRow { key } => {
            assert_eq!(key.symbol, "Nat.a");
            assert_eq!(key.platform, Platform::LinuxX86_64);
            assert_eq!(key.mode, Mode::Sound);
        }
        other => panic!("expected DuplicateRow, got {other:?}"),
    }
}

#[test]
fn the_same_symbol_on_two_platforms_or_modes_is_not_a_duplicate() {
    // The other side of the duplicate rule. Collapsing the key to the symbol
    // alone would manufacture false duplicates and hide real per-platform rows,
    // which is how a ledger stops being row-per-symbol-per-surface.
    let mut other_platform = Row::valid("Nat.a");
    other_platform.platform = "macos-aarch64".to_string();
    let mut other_mode = Row::valid("Nat.a");
    other_mode.mode = "faithful".to_string();
    let l = parsed(&HEAD, &[Row::valid("Nat.a"), other_platform, other_mode]);
    let blocks = verify(&l, &["Nat.a"], &vh());
    assert!(blocks.is_empty(), "false duplicate reported: {blocks:?}");
}

#[test]
fn a_stale_revision_blocks() {
    let l = parsed(ROOT_B, &[Row::valid("Nat.a")]);
    let blocks = verify(&l, &["Nat.a"], &vh());
    assert_eq!(reasons(&blocks), vec!["stale"]);
    match &blocks[0] {
        Block::StaleRevision { stated, head } => {
            assert_eq!(stated, ROOT_B);
            assert_eq!(head, &*HEAD);
        }
        other => panic!("expected StaleRevision, got {other:?}"),
    }
}

#[test]
fn a_revision_that_merely_prefixes_the_head_is_still_stale() {
    // Guards the comparison itself. A truncated or abbreviated revision must
    // not satisfy the freshness check by being a prefix of the real head.
    let l = parsed(&HEAD[..16], &[Row::valid("Nat.a")]);
    assert_eq!(reasons(&verify(&l, &["Nat.a"], &vh())), vec!["stale"]);
}

#[test]
fn an_unknown_symbol_blocks() {
    let l = parsed(&HEAD, &[Row::valid("Nat.a"), Row::valid("Nat.ghost")]);
    let blocks = verify(&l, &["Nat.a"], &vh());
    assert_eq!(reasons(&blocks), vec!["unknown"]);
    assert!(matches!(&blocks[0], Block::UnknownSymbol { symbol } if symbol == "Nat.ghost"));
}

#[test]
fn a_root_mismatch_blocks() {
    // byte-identical declared, but the two roots differ: the row asserts a
    // parity its own digests contradict.
    let mut r = Row::valid("Nat.a");
    r.oracle_root = ROOT_B.to_string();
    let l = parsed(&HEAD, &[r]);
    let blocks = verify(&l, &["Nat.a"], &vh());
    assert_eq!(reasons(&blocks), vec!["root-mismatch"]);
}

#[test]
fn the_comparison_class_decides_what_the_roots_must_say() {
    // acceptance-only compared no artifacts, so citing roots claims a
    // comparison that did not happen...
    let mut cited = Row::valid("Nat.a");
    cited.comparison = "acceptance-only".to_string();
    assert_eq!(
        reasons(&verify(&parsed(&HEAD, &[cited]), &["Nat.a"], &vh())),
        vec!["root-mismatch"]
    );

    // ...and with the roots declared absent, it is a legitimate row.
    let mut honest = Row::valid("Nat.a");
    honest.comparison = "acceptance-only".to_string();
    honest.ours_root = "-".to_string();
    honest.oracle_root = "-".to_string();
    assert!(verify(&parsed(&HEAD, &[honest]), &["Nat.a"], &vh()).is_empty());

    // A normalized comparison must cite both roots.
    let mut normalized = Row::valid("Nat.a");
    normalized.comparison = "normalized-identical".to_string();
    normalized.normalizer = "diagnostic-text/1".to_string();
    normalized.ours_root = "-".to_string();
    assert_eq!(
        reasons(&verify(&parsed(&HEAD, &[normalized]), &["Nat.a"], &vh())),
        vec!["root-mismatch"]
    );
}

#[test]
fn a_comparison_class_and_a_normalizer_that_disagree_block() {
    // A normalized comparison that names no normalizer cannot say what it
    // normalized with; a byte-identical comparison that names one is lying
    // about what was compared. Both are incoherent, for their own reason.
    let mut unnamed = Row::valid("Nat.a");
    unnamed.comparison = "normalized-identical".to_string();
    unnamed.oracle_root = ROOT_B.to_string();
    assert!(
        reasons(&verify(&parsed(&HEAD, &[unnamed]), &["Nat.a"], &vh()))
            .contains(&"incoherent-comparison")
    );

    let mut spurious = Row::valid("Nat.a");
    spurious.normalizer = "diagnostic-text/1".to_string();
    assert_eq!(
        reasons(&verify(&parsed(&HEAD, &[spurious]), &["Nat.a"], &vh())),
        vec!["incoherent-comparison"]
    );
}

#[test]
fn a_mock_backed_row_cannot_close_an_l_level() {
    // A mock may support a unit test and may NOT close a public claim.
    let mut r = Row::valid("Nat.a");
    r.backing = "mock".to_string();
    let blocks = verify(&parsed(&HEAD, &[r]), &["Nat.a"], &vh());
    assert_eq!(reasons(&blocks), vec!["mock-only"]);
    match &blocks[0] {
        Block::MockOnlyClosure { symbol, level } => {
            assert_eq!(symbol, "Nat.a");
            assert_eq!(*level, LLevel::L2);
        }
        other => panic!("expected MockOnlyClosure, got {other:?}"),
    }

    // ...and at L0 — closing nothing — a mock-backed row is legitimate. The
    // rule bans the closure, not the mock.
    let mut l0 = Row::valid("Nat.a");
    l0.backing = "mock".to_string();
    l0.level = "L0".to_string();
    assert!(verify(&parsed(&HEAD, &[l0]), &["Nat.a"], &vh()).is_empty());
}

#[test]
fn an_unearned_level_blocks() {
    // Evidence that is not established closes nothing above L0.
    for state in ["targeted", "hypothesis", "blocked"] {
        let mut r = Row::valid("Nat.a");
        r.state = state.to_string();
        // A non-established state also caps the claim, so keep the claim at the
        // floor to isolate the LEVEL rule from the CLAIM rule.
        r.claim = "benchmark".to_string();
        let blocks = verify(&parsed(&HEAD, &[r]), &["Nat.a"], &vh());
        assert!(
            reasons(&blocks).contains(&"overclaimed-level"),
            "state {state} at L2 did not block the level: {blocks:?}"
        );
    }
}

#[test]
fn an_observation_is_not_a_proof() {
    // D7's weaker-never-justifies-stronger rule, applied to the ledger. An
    // observed row may carry bounded_model; it may not carry proof or
    // invariant, whatever its L-level says.
    for claim in ["proof", "invariant"] {
        let mut r = Row::valid("Nat.a");
        r.claim = claim.to_string();
        let blocks = verify(&parsed(&HEAD, &[r]), &["Nat.a"], &vh());
        assert_eq!(
            reasons(&blocks),
            vec!["overclaimed-claim"],
            "an observed row carried a {claim} claim"
        );
    }
    // Proven earns them.
    let mut proven = Row::valid("Nat.a");
    proven.state = "proven".to_string();
    proven.claim = "invariant".to_string();
    assert!(verify(&parsed(&HEAD, &[proven]), &["Nat.a"], &vh()).is_empty());
}

// ---------------------------------------------------------------------------
// The three fields stay three fields
// ---------------------------------------------------------------------------

#[test]
fn the_level_rule_does_not_read_the_claim_type() {
    // Claim type, evidence state and L-level are three fields and none may
    // stand in for another. Vary the claim across its whole vocabulary while
    // holding state and level fixed, and require the LEVEL verdict not to move.
    for state in ["proven", "observed", "targeted", "hypothesis", "blocked"] {
        for level in ["L0", "L1", "L2", "L3", "L4"] {
            let mut baseline = Row::valid("Nat.a");
            baseline.state = state.to_string();
            baseline.level = level.to_string();
            baseline.claim = "benchmark".to_string();
            let want = reasons(&verify(&parsed(&HEAD, &[baseline]), &["Nat.a"], &vh()))
                .contains(&"overclaimed-level");

            for claim in [
                "invariant",
                "proof",
                "bounded_model",
                "statistical",
                "slo",
                "benchmark",
            ] {
                let mut r = Row::valid("Nat.a");
                r.state = state.to_string();
                r.level = level.to_string();
                r.claim = claim.to_string();
                let got = reasons(&verify(&parsed(&HEAD, &[r]), &["Nat.a"], &vh()))
                    .contains(&"overclaimed-level");
                assert!(
                    got == want,
                    "the level verdict moved with the claim type \
                     (state {state}, level {level}, claim {claim})"
                );
            }
        }
    }
}

#[test]
fn the_claim_rule_does_not_read_the_l_level() {
    // The symmetric guard. An L-level must not confer a claim type.
    for state in ["proven", "observed", "targeted", "hypothesis", "blocked"] {
        for claim in ["invariant", "proof", "bounded_model", "benchmark"] {
            let mut baseline = Row::valid("Nat.a");
            baseline.state = state.to_string();
            baseline.claim = claim.to_string();
            baseline.level = "L0".to_string();
            let want = reasons(&verify(&parsed(&HEAD, &[baseline]), &["Nat.a"], &vh()))
                .contains(&"overclaimed-claim");

            for level in ["L0", "L1", "L2", "L3", "L4"] {
                let mut r = Row::valid("Nat.a");
                r.state = state.to_string();
                r.claim = claim.to_string();
                r.level = level.to_string();
                let got = reasons(&verify(&parsed(&HEAD, &[r]), &["Nat.a"], &vh()))
                    .contains(&"overclaimed-claim");
                assert!(
                    got == want,
                    "the claim verdict moved with the L-level \
                     (state {state}, claim {claim}, level {level})"
                );
            }
        }
    }
}

#[test]
fn the_mock_rule_reads_backing_and_level_and_nothing_else() {
    // Three separate failures: "the run was mocked", "the evidence is not
    // established", and "the claim is too strong". A row can have any one
    // without the others, so the mock rule must not move with state or claim.
    for state in ["proven", "observed"] {
        for claim in ["bounded_model", "benchmark"] {
            let mut r = Row::valid("Nat.a");
            r.backing = "mock".to_string();
            r.state = state.to_string();
            r.claim = claim.to_string();
            assert!(
                reasons(&verify(&parsed(&HEAD, &[r]), &["Nat.a"], &vh())).contains(&"mock-only"),
                "the mock rule moved with state {state} / claim {claim}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// No aggregates, no percentages
// ---------------------------------------------------------------------------

#[test]
fn an_aggregate_row_blocks() {
    // A headline number is never evidence under D7. The struct has no field to
    // put one in, so an aggregate would have to arrive disguised as a symbol.
    for symbol in [
        "TOTAL", "ALL", "SUMMARY", "OVERALL", "AVERAGE", "Nat.*", "97%", "0.97", "12", "42ms",
    ] {
        let l = parsed(&HEAD, &[Row::valid(symbol)]);
        let blocks = verify(&l, &[symbol], &vh());
        assert!(
            reasons(&blocks).contains(&"aggregate"),
            "{symbol:?} was admitted as a row: {blocks:?}"
        );
    }
    // And real symbols are not caught by it.
    for symbol in [
        "Nat.succ_le_of_lt",
        "List.all",
        "Total.order",
        "Score.mk",
        "Fin.val",
    ] {
        assert!(
            !is_aggregate_symbol(symbol),
            "{symbol:?} was misread as an aggregate"
        );
    }
}

#[test]
fn a_ledger_reports_every_block_it_finds_not_the_first() {
    // A ledger with four problems should report four. Reporting only the first
    // turns one fix-and-rerun cycle into four.
    let mut mock = Row::valid("Nat.a");
    mock.backing = "mock".to_string();
    let l = parsed(ROOT_B, &[mock, Row::valid("Nat.ghost")]);
    let blocks = verify(&l, &["Nat.a", "Nat.b"], &vh());
    let r = reasons(&blocks);
    for want in ["stale", "mock-only", "unknown", "missing"] {
        assert!(r.contains(&want), "{want} was not reported: {blocks:?}");
    }
    assert!(report(&blocks).contains("verdict=fail"));
}

#[test]
fn a_block_is_never_downgraded_to_a_warning() {
    // There is no warning level: the epic's acceptance criteria ARE the
    // blocking conditions. Any non-empty verification fails.
    let mut r = Row::valid("Nat.a");
    r.backing = "mock".to_string();
    let blocks = verify(&parsed(&HEAD, &[r]), &["Nat.a"], &vh());
    assert!(!blocks.is_empty());
    let text = report(&blocks);
    assert!(text.contains("verdict=fail"));
    assert!(
        !text.contains("warning"),
        "a block was rendered as a warning"
    );
}

#[test]
fn evidence_state_and_claim_type_survive_a_round_trip_unconflated() {
    // A last direct check that the parser puts each token in its own field
    // rather than deriving one from another.
    let mut r = Row::valid("Nat.a");
    r.state = "proven".to_string();
    r.claim = "invariant".to_string();
    r.level = "L4".to_string();
    let l = parsed(&HEAD, &[r]);
    let row = &l.rows[0];
    assert_eq!(row.state, EvidenceState::Proven);
    assert_eq!(row.claim, ClaimType::Invariant);
    assert_eq!(row.level, LLevel::L4);
}

// ---------------------------------------------------------------------------
// The fixture a row names must exist and must hash to what the row states
// (bead fln-8fwh)
// ---------------------------------------------------------------------------

fn repo_root() -> PathBuf {
    fln_conformance::checked_manifest_dir!().join("../..")
}

#[test]
fn a_row_that_invents_a_fixture_digest_is_refused() {
    // THE GAP THIS BEAD CLOSED. Every field is well-formed: the fixture path
    // exists, the digest is sixty-four valid hex characters, the roots agree,
    // the claim is within its ceiling. It is simply not that file's digest, and
    // before fln-8fwh the schema had no way to know.
    let mut r = Row::valid("Nat.a");
    r.symbol = "Nat.a".to_string();
    let l = parsed(&HEAD, &[r]);
    // The row's fixture path is fixtures/nat.lean, which does not exist; point
    // the check at a real file to isolate the DIGEST failure from the missing
    // -file failure.
    let blocks = verify_with_fixtures(&l, &["Nat.a"], &vh(), &repo_root());
    assert!(
        blocks.iter().any(|b| b.reason() == "fixture-unverified"),
        "an invented fixture digest was recorded: {blocks:?}"
    );
}

#[test]
fn a_row_whose_fixture_verifies_is_accepted() {
    // The counterweight: the check must be satisfiable, or it is a gate nobody
    // can pass. Name a file that really exists and state its real digest.
    let root = repo_root();
    let fixture = "AGENTS.md";
    let digest = fln_epoch_lab::derive::derive_fixture_digest(&root.join(fixture))
        .expect("AGENTS.md is readable")
        .into_parts()
        .0;
    let head = HEAD.as_str();
    let text = format!(
        "{OUTCOME_SCHEMA}\nepoch v4.32.0\nrevision {head}\n\
         row Nat.a fixture={fixture} fixture_digest={digest} \
         ours_root={ROOT_A} oracle_root={ROOT_A} ours_verdict=accepted \
         oracle_verdict=accepted assessment=agree disposition=- \
         oracle=reference-binary \
         comparison=byte-identical normalizer=- claim=bounded_model \
         evidence=differential state=observed level=L2 mode=sound \
         platform=linux-x86_64 backing=real-reference freshness=current \
         limits=no-known-limitations\n"
    );
    let l = parse(&text).expect("the ledger parses");
    let blocks = verify_with_fixtures(&l, &["Nat.a"], &vh(), &root);
    assert!(
        blocks.is_empty(),
        "a verifiable row was refused: {blocks:?}"
    );
}

#[test]
fn a_row_naming_a_fixture_that_does_not_exist_is_refused() {
    let l = parsed(&HEAD, &[Row::valid("Nat.a")]);
    let blocks = verify_with_fixtures(&l, &["Nat.a"], &vh(), &repo_root());
    let found = blocks.iter().any(|b| match b {
        Block::FixtureUnverified { detail, .. } => detail.contains("cannot read"),
        _ => false,
    });
    assert!(found, "a nonexistent fixture was accepted: {blocks:?}");
}

// ---------------------------------------------------------------------------
// Dogfooding: can this schema carry the corpus result it was built for?
// (bead franken_lean-9pnc meets franken_lean-d17i / kxbj / fln-7odd, settled by
// fln-fei1)
// ---------------------------------------------------------------------------
//
// The four things a real corpus run produces, attempted as rows. This is the
// honest test of a schema: not whether it accepts a well-formed row, but
// whether the project's strongest real result can be written down in it without
// bending anything.
//
// Under schema 1 exactly one of the four could be. The three that could not are
// re-derived below against schema 2, and each one now asserts the SAME fact
// from the other side: that the honest encoding is accepted, and that the
// dishonest encoding version 1 forced on it is refused. Both halves matter. A
// schema that merely admits the new row while still admitting the old lie has
// not fixed anything.

#[test]
fn an_agreeing_symbol_is_expressible() {
    // The compared declarations that agreed. This is the case schema 1 was
    // designed around and it still works unchanged — the extension is additive
    // for the row kind that already fit.
    let l = parsed(&HEAD, &[Row::valid("Nat.succ_le_of_lt")]);
    assert!(verify(&l, &["Nat.succ_le_of_lt"], &vh()).is_empty());
}

#[test]
fn a_restrictive_divergence_is_expressible_and_reads_as_uncalled() {
    // DEFECT 1, CLOSED. A restrictive divergence — we reject, the Reference
    // accepts — is the single most load-bearing row a Parity Ledger can carry,
    // and schema 1 refused it: the two roots necessarily differ, so
    // byte-identical blocked it as a root mismatch, and no ComparisonClass
    // meant "compared, and they disagreed".
    let l = parsed(&HEAD, &[Row::restrictive_uncalled("Lean.Arrow")]);
    let blocks = verify(&l, &["Lean.Arrow"], &vh());
    assert!(
        blocks.is_empty(),
        "a restrictive divergence was refused: {blocks:?}"
    );

    // And it reads as neither a pass nor a finding. The census gives it its own
    // class; nothing folds it into either.
    let text = census(&l);
    assert!(
        text.contains("assessment=restrictive disposition=uncalled n=1"),
        "an uncalled divergence lost its own class: {text}"
    );
    assert!(
        !text.contains("assessment=agree"),
        "counted as a pass: {text}"
    );
}

#[test]
fn an_uncalled_divergence_is_not_the_same_row_as_a_called_one() {
    // The disposition is a real axis, not decoration: the same measurement with
    // its cause called reads differently, and both are legal rows. If these two
    // collapsed to one, "we measured a difference" and "we know why" would be
    // the same claim again.
    let mut called = Row::restrictive_uncalled("Lean.Arrow");
    called.disposition = "harness".to_string();
    called.limits = "our decoder truncates extended imports at this scope".to_string();
    let l = parsed(&HEAD, &[called]);
    assert!(verify(&l, &["Lean.Arrow"], &vh()).is_empty());
    assert!(census(&l).contains("assessment=restrictive disposition=harness n=1"));
}

#[test]
fn an_oracle_silent_symbol_is_expressible_and_the_old_lie_is_refused() {
    // DEFECT 2, CLOSED. fln-7odd's 1,425 declarations are ones the pinned
    // checker legitimately cannot judge — unsafe or partial constants its own
    // replay never submits. That is a real bound on the oracle and belongs in
    // the report as a stated limit on a row, not as an absence from the file.
    let l = parsed(&HEAD, &[Row::oracle_silent("Nat.unsafeCast")]);
    let blocks = verify(&l, &["Nat.unsafeCast"], &vh());
    assert!(
        blocks.is_empty(),
        "an oracle-silent row was refused: {blocks:?}"
    );
    assert!(census(&l).contains("assessment=unscorable"));

    // The other half, and the half that matters more. Schema 1's nearest
    // encoding — acceptance-only with both roots absent — PARSED AND PASSED
    // while asserting "we compared acceptance and agreed", which is false: the
    // oracle never spoke. That encoding must now be refused, and for its own
    // reason, not incidentally.
    // Written out literally — an oracle that said nothing, under a row that
    // claims the two sides agreed — it is refused as misscored: the stated
    // conclusion is not what the row's own sides produce.
    let mut lie = Row::valid("Nat.unsafeCast");
    lie.comparison = "acceptance-only".to_string();
    lie.ours_root = "-".to_string();
    lie.oracle_root = "-".to_string();
    lie.oracle_verdict = "no-answer:out-of-scope".to_string();
    let blocks = verify(&parsed(&HEAD, &[lie.clone()]), &["Nat.unsafeCast"], &vh());
    assert!(
        reasons(&blocks).contains(&"misscored"),
        "the version-1 encoding of an oracle-silent symbol still passes: {blocks:?}"
    );

    // And once the conclusion is corrected, the borrowed comparison class is
    // still refused on its own — for its own reason. Two separate defects in
    // that one old row, and each has to fail by itself or a mutant that revives
    // either is covered by the other.
    let mut honest_score = lie;
    honest_score.assessment = "unscorable".to_string();
    honest_score.level = "L0".to_string(); // isolate: an uncompared row closes no level either
    let blocks = verify(&parsed(&HEAD, &[honest_score]), &["Nat.unsafeCast"], &vh());
    assert_eq!(reasons(&blocks), vec!["uncompared"]);
}

#[test]
fn an_unassessed_symbol_is_expressible_and_is_not_a_missing_symbol() {
    // DEFECT 3, CLOSED, and the largest by volume: most of a decoded corpus is
    // never compared. Schema 1 offered a row asserting comparison, or no row at
    // all and then Block::MissingSymbol — and "we have no row for this symbol"
    // and "we have a row saying nobody looked" are different facts.
    let scan = ["A", "B"];
    let l = parsed(&HEAD, &[Row::valid("A"), Row::unassessed("B")]);
    let blocks = verify(&l, &scan, &vh());
    assert!(
        blocks.is_empty(),
        "an unassessed row was refused: {blocks:?}"
    );
    assert!(
        !reasons(&blocks).contains(&"missing"),
        "an assessed-nobody-looked row was still reported as missing: {blocks:?}"
    );

    // MissingSymbol survives, and is now a sharper refusal than it was: it means
    // the ledger does not mention the symbol AT ALL, which after schema 2 is a
    // publication defect rather than the only way to say "not assessed".
    let thin = parsed(&HEAD, &[Row::valid("A")]);
    assert!(reasons(&verify(&thin, &scan, &vh())).contains(&"missing"));
}

#[test]
fn an_unassessed_symbol_cannot_carry_a_compatibility_level() {
    // The trap the level rule alone does not catch. "We observed that nobody
    // assessed this" is an honest thing to say, and state=observed carries an L4
    // ceiling — so without a rule that reads the assessment, a symbol nobody
    // checked could be published as attested by a row that lies about nothing.
    let mut r = Row::unassessed("B");
    r.level = "L3".to_string();
    let blocks = verify(&parsed(&HEAD, &[r]), &["B"], &vh());
    assert_eq!(reasons(&blocks), vec!["level-without-comparison"]);
}

// ---------------------------------------------------------------------------
// The refusals schema 2 adds. Each fires for its own reason.
// ---------------------------------------------------------------------------

#[test]
fn a_row_whose_assessment_its_own_sides_do_not_support_is_refused() {
    // The most dangerous row this file can contain, and one schema 1 could not
    // even express: a stated conclusion that the two recorded verdicts do not
    // produce. The verifier re-derives it with the live scoring function rather
    // than trusting the field.
    let mut lying = Row::valid("Nat.a");
    lying.ours_verdict = "rejected".to_string();
    lying.oracle_verdict = "accepted".to_string();
    // ...but the row still claims they agreed.
    let blocks = verify(&parsed(&HEAD, &[lying]), &["Nat.a"], &vh());
    assert!(
        reasons(&blocks).contains(&"misscored"),
        "a misscored row was not refused: {blocks:?}"
    );
    let found = blocks.iter().any(|b| {
        matches!(
            b,
            Block::Misscored {
                stated: Assessment::Agree,
                derived: Assessment::Restrictive,
                ..
            }
        )
    });
    assert!(found, "the refusal did not name both readings: {blocks:?}");
}

#[test]
fn the_scoring_rule_the_ledger_uses_is_the_one_the_rigs_use() {
    // The anti-drift device. If the ledger scored with its own copy of the rule,
    // the copy could diverge from `oracle::score` and every row would still
    // verify — a ledger agreeing with itself. It must be the same function, so
    // this asserts on the function rather than on a transcribed table.
    for (ours, oracle, want) in [
        (
            OurVerdict::Accepted,
            OracleVerdict::Accepted,
            Assessment::Agree,
        ),
        (
            OurVerdict::Rejected {
                diagnostic: String::new(),
            },
            OracleVerdict::Accepted,
            Assessment::Restrictive,
        ),
        (
            OurVerdict::Accepted,
            OracleVerdict::Rejected {
                diagnostic: String::new(),
            },
            Assessment::UnsoundlyPermissive,
        ),
        (
            OurVerdict::Accepted,
            OracleVerdict::NoAnswer(NonAuthoritative::not_judged("out-of-scope")),
            Assessment::Unscorable,
        ),
        (
            OurVerdict::Inconclusive {
                what: "depth-bound".to_string(),
            },
            OracleVerdict::Accepted,
            Assessment::Unscorable,
        ),
    ] {
        let got = Assessment::of(&score_verdicts(&ours, &oracle));
        assert_eq!(got, want, "{ours:?} vs {oracle:?}");
    }
}

#[test]
fn a_non_answer_from_either_side_is_never_a_divergence_in_a_row() {
    // FL-INV-07 at the ledger layer. A row where either side did not answer
    // cannot be recorded as a finding, however it is spelled: the assessment is
    // re-derived, so `restrictive` over a non-answer is refused as misscored
    // rather than published as a divergence.
    for mut r in [Row::oracle_silent("Nat.a"), Row::unassessed("Nat.a")] {
        r.assessment = "restrictive".to_string();
        r.disposition = "semantic".to_string();
        let blocks = verify(&parsed(&HEAD, &[r]), &["Nat.a"], &vh());
        assert!(
            reasons(&blocks).contains(&"misscored"),
            "a non-answer was published as a divergence: {blocks:?}"
        );
    }
}

#[test]
fn a_divergence_must_say_whether_it_was_called() {
    // A divergence with nothing said about its cause is not a legal row: the
    // schema will take `uncalled` and will not take silence, because silence is
    // what let an unclassified divergence be filed as a clean pass.
    let mut silent = Row::restrictive_uncalled("Lean.Arrow");
    silent.disposition = "-".to_string();
    let blocks = verify(&parsed(&HEAD, &[silent]), &["Lean.Arrow"], &vh());
    assert_eq!(reasons(&blocks), vec!["incoherent-disposition"]);

    // And the converse: a row with nothing to call must not name a cause.
    let mut spurious = Row::valid("Nat.a");
    spurious.disposition = "semantic".to_string();
    let blocks = verify(&parsed(&HEAD, &[spurious]), &["Nat.a"], &vh());
    assert_eq!(reasons(&blocks), vec!["incoherent-disposition"]);
}

#[test]
fn a_divergence_whose_roots_are_identical_is_refused() {
    // The sharper half of the re-derived root rule, and a row schema 1 could
    // not express at all. Under version 1 the rule read the comparison class
    // alone and any two differing roots were the defect; now the roots have to
    // agree with the ASSESSMENT, so a declared divergence whose two artifacts
    // are the same bytes is a row contradicting its own evidence.
    let mut r = Row::restrictive_uncalled("Lean.Arrow");
    r.oracle_root = ROOT_A.to_string(); // same as ours: nothing actually differs
    let blocks = verify(&parsed(&HEAD, &[r]), &["Lean.Arrow"], &vh());
    assert_eq!(reasons(&blocks), vec!["root-mismatch"]);
}

#[test]
fn a_silent_oracle_cannot_have_its_root_cited() {
    // An oracle that gave no answer produced nothing to cite. A digest there is
    // a fabrication, and it is the shape a copy-pasted row takes.
    let mut r = Row::oracle_silent("Nat.unsafeCast");
    r.oracle_root = ROOT_B.to_string();
    let blocks = verify(&parsed(&HEAD, &[r]), &["Nat.unsafeCast"], &vh());
    assert_eq!(reasons(&blocks), vec!["root-mismatch"]);
}

#[test]
fn a_comparison_class_is_named_exactly_when_something_was_compared() {
    // Both directions, because either alone leaves a lie expressible.
    let mut classed = Row::oracle_silent("Nat.a");
    classed.comparison = "acceptance-only".to_string();
    classed.ours_root = "-".to_string();
    assert!(
        reasons(&verify(&parsed(&HEAD, &[classed]), &["Nat.a"], &vh())).contains(&"uncompared")
    );

    let mut classless = Row::valid("Nat.a");
    classless.comparison = "-".to_string();
    assert!(
        reasons(&verify(&parsed(&HEAD, &[classless]), &["Nat.a"], &vh())).contains(&"uncompared")
    );
}

#[test]
fn an_inconclusive_must_name_what_was_inconclusive() {
    // FL-INV-07 says a non-answer is typed, not silent. A bare `inconclusive`
    // does not parse: the row has to say what it could not conclude, which is
    // how kxbj's depth bound stays distinguishable from a scope decision.
    let mut bare = Row::unassessed("B");
    bare.ours_verdict = "inconclusive:".to_string();
    let err = parse(&ledger_text(&HEAD, &[bare])).expect_err("a bare inconclusive parsed");
    assert!(reasons(&err).contains(&"malformed"), "{err:?}");
}

// ---------------------------------------------------------------------------
// The report says what it verdicts on.
// ---------------------------------------------------------------------------

#[test]
fn the_report_verdicts_on_the_schema_and_says_so() {
    // `verdict=pass` over a ledger of unassessed rows is exactly the sentence
    // that gets quoted as "we match the Reference". What `report` decides is
    // whether the FILE is admissible, and after schema 2 — where a well-formed
    // ledger can be 90% not-assessed — the word has to carry its own scope.
    let l = parsed(&HEAD, &[Row::unassessed("A")]);
    let blocks = verify(&l, &["A"], &vh());
    assert!(blocks.is_empty(), "the fixture ledger is admissible");
    let text = report(&blocks);
    assert!(text.contains("schema-verdict=pass"), "{text}");
    assert!(
        !text.contains("parity=") && !text.contains('%'),
        "the report implied a parity result: {text}"
    );
}

#[test]
fn the_census_disaggregates_and_never_totals() {
    // The census is the opposite of a headline number: one line per class, no
    // grand total and no percentage to quote. D7 forbids the aggregate, not the
    // disaggregation — and a report that printed only blocks would satisfy the
    // "no aggregates" rule by saying nothing about the corpus at all.
    let l = parsed(
        &HEAD,
        &[
            Row::valid("A"),
            Row::restrictive_uncalled("B"),
            Row::oracle_silent("C"),
            Row::unassessed("D"),
        ],
    );
    let text = census(&l);
    for want in [
        "assessment=agree disposition=- n=1",
        "assessment=restrictive disposition=uncalled n=1",
        "assessment=unscorable disposition=- n=2",
    ] {
        assert!(text.contains(want), "census lost {want:?}: {text}");
    }
    for forbidden in ["total", "percent", "%", "score=", "rate="] {
        assert!(
            !text.contains(forbidden),
            "the census emitted {forbidden:?}: {text}"
        );
    }
    // Four rows, three classes: the classes are what is reported, and the count
    // of rows is never printed as one number.
    assert_eq!(text.lines().count(), 3, "{text}");
}

// ---------------------------------------------------------------------------
// The gate path: the head comes from the PUBLISHED chain, not from anyone's
// hand (bead fln-8fwh, remainder item 1)
// ---------------------------------------------------------------------------

#[test]
fn freshness_is_judged_against_the_head_verify_epoch_returns() {
    // Before this bead's repair, staleness was a DECLARATION: verify() took a
    // &str and compared the ledger against whatever the caller wrote down, so
    // a gate holding a stale or invented hex passed with full confidence. Now
    // the only path to a VerifiedHead is From<&Chain>, and the only honest
    // Chain is the one verify_epoch parses AND verifies against the committed
    // manifest. This test walks that exact path over the REAL published epoch:
    // tribunal/epochs/v4.32.0, the chain the program actually ships.
    let epoch_dir = repo_root().join("tribunal/epochs/v4.32.0");
    let chain = fln_epoch_lab::verify_epoch(&epoch_dir, "v4.32.0", "MANIFEST.txt")
        .expect("the committed epoch chain verifies against its committed manifest");
    let real_head = fln_epoch_lab::parity::VerifiedHead::from(&chain);

    // Fresh: a ledger written against the head the chain actually published.
    let fresh = parsed(real_head.as_hex(), &[Row::valid("Nat.a")]);
    assert!(
        verify(&fresh, &["Nat.a"], &real_head).is_empty(),
        "a ledger at the published head must be fresh"
    );

    // Stale: the same ledger judged after the chain has moved on. The head is
    // still obtained from a real Chain — the API leaves no other way — so this
    // cell is the honest form of "the world advanced and the ledger did not".
    let advanced = chain.appended(fln_epoch_lab::content_digest(b"a newer manifest"));
    let newer_head = fln_epoch_lab::parity::VerifiedHead::from(&advanced);
    let blocks = verify(&fresh, &["Nat.a"], &newer_head);
    assert_eq!(
        reasons(&blocks),
        vec!["stale"],
        "a ledger left behind by the chain must block as stale"
    );
    match &blocks[0] {
        Block::StaleRevision { stated, head } => {
            assert_eq!(stated, real_head.as_hex());
            assert_eq!(head, newer_head.as_hex());
        }
        other => panic!("expected StaleRevision, got {other:?}"),
    }
}
