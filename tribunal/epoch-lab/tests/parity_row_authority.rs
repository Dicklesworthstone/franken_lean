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
//! **The stale row is the one worth reading.** `a_stale_revision_blocks` did
//! NOT kill the `starts_with` mutant — it uses a revision that is not a prefix
//! of the head, so a prefix-accepting comparison still refuses it and the test
//! still passes. Only `a_revision_that_merely_prefixes_the_head_is_still_stale`
//! catches it. An abbreviated or truncated revision is exactly the shape a
//! real ledger would carry by accident, so without that second test the
//! freshness check could have been weakened to a prefix match and the suite
//! would have stayed green.

#![forbid(unsafe_code)]

use fln_epoch_lab::oracle::{ClaimType, EvidenceState, LLevel, Mode, Platform};
use fln_epoch_lab::parity::{
    Block, LEDGER_SCHEMA, Ledger, ROW_FIELDS, is_aggregate_symbol, parse, report, verify,
};

const HEAD: &str = "7e554b20907d81a272d10718c26da2c25e2e6d70b2e962dc87516bb24dc18a75";
const ROOT_A: &str = "1111111111111111111111111111111111111111111111111111111111111111";
const ROOT_B: &str = "2222222222222222222222222222222222222222222222222222222222222222";
const FIXTURE_DIGEST: &str = "3333333333333333333333333333333333333333333333333333333333333333";

/// A row builder that starts from a fully valid row, so every test changes
/// exactly one thing and the reason a ledger was refused is unambiguous.
struct Row {
    symbol: String,
    ours_root: String,
    oracle_root: String,
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

    fn render(&self) -> String {
        format!(
            "row {} fixture=fixtures/nat.lean fixture_digest={FIXTURE_DIGEST} \
             ours_root={} oracle_root={} oracle=reference-binary comparison={} \
             normalizer={} claim={} evidence=differential state={} level={} \
             mode={} platform={} backing={} freshness=current limits={}",
            self.symbol,
            self.ours_root,
            self.oracle_root,
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
    let mut s = format!("{LEDGER_SCHEMA}\nepoch v4.32.0\nrevision {revision}\n");
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
    let l = parsed(HEAD, &[Row::valid("Nat.succ_le_of_lt")]);
    let blocks = verify(&l, &["Nat.succ_le_of_lt"], HEAD);
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
        let text = format!("{LEDGER_SCHEMA}\nepoch v4.32.0\nrevision {HEAD}\n{mutilated}\n");
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
    let text = ledger_text(HEAD, &[r]);
    match parse(&text) {
        Err(b) => assert_eq!(reasons(&b), vec!["malformed"]),
        Ok(_) => panic!("a row with empty limits= parsed"),
    }
}

#[test]
fn a_reordered_or_repeated_field_does_not_parse() {
    // Fixed field order keeps the file diffable and makes a reordered row a
    // refusal rather than a silent acceptance.
    let reordered = format!(
        "{LEDGER_SCHEMA}\nepoch v4.32.0\nrevision {HEAD}\n\
         row Nat.foo fixture_digest={FIXTURE_DIGEST} fixture=fixtures/nat.lean \
         ours_root={ROOT_A} oracle_root={ROOT_A} oracle=reference-binary \
         comparison=byte-identical normalizer=- claim=bounded_model \
         evidence=differential state=observed level=L2 mode=sound \
         platform=linux-x86_64 backing=real-reference freshness=current \
         limits=none\n"
    );
    assert!(parse(&reordered).is_err(), "a reordered row parsed");

    let repeated = ledger_text(HEAD, &[Row::valid("Nat.foo")]).replace(
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
    for text in [
        "",
        "not-a-schema",
        LEDGER_SCHEMA,
        &format!("{LEDGER_SCHEMA}\n"),
        &format!("{LEDGER_SCHEMA}\nepoch v4.32.0\n"),
        &format!("{LEDGER_SCHEMA}\nrevision {HEAD}\n"),
        &format!("{LEDGER_SCHEMA}\nepoch v\nrevision r\nrow\n"),
        &format!("{LEDGER_SCHEMA}\nepoch v\nrevision r\nrow x limits=\n"),
        &format!("{LEDGER_SCHEMA}\nepoch v\nrevision r\nnonsense verb here\n"),
        &format!("{LEDGER_SCHEMA}\nepoch v\nrevision r\nrow x y z limits=q\n"),
    ] {
        assert!(parse(text).is_err(), "hostile input parsed: {text:?}");
    }
}

// ---------------------------------------------------------------------------
// The seven blocking conditions, each for its own reason
// ---------------------------------------------------------------------------

#[test]
fn a_missing_symbol_blocks() {
    let l = parsed(HEAD, &[Row::valid("Nat.a")]);
    let blocks = verify(&l, &["Nat.a", "Nat.b"], HEAD);
    assert_eq!(reasons(&blocks), vec!["missing"]);
    assert!(matches!(&blocks[0], Block::MissingSymbol { symbol } if symbol == "Nat.b"));
}

#[test]
fn a_duplicate_row_blocks() {
    let l = parsed(HEAD, &[Row::valid("Nat.a"), Row::valid("Nat.a")]);
    let blocks = verify(&l, &["Nat.a"], HEAD);
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
    let l = parsed(HEAD, &[Row::valid("Nat.a"), other_platform, other_mode]);
    let blocks = verify(&l, &["Nat.a"], HEAD);
    assert!(blocks.is_empty(), "false duplicate reported: {blocks:?}");
}

#[test]
fn a_stale_revision_blocks() {
    let l = parsed(ROOT_B, &[Row::valid("Nat.a")]);
    let blocks = verify(&l, &["Nat.a"], HEAD);
    assert_eq!(reasons(&blocks), vec!["stale"]);
    match &blocks[0] {
        Block::StaleRevision { stated, head } => {
            assert_eq!(stated, ROOT_B);
            assert_eq!(head, HEAD);
        }
        other => panic!("expected StaleRevision, got {other:?}"),
    }
}

#[test]
fn a_revision_that_merely_prefixes_the_head_is_still_stale() {
    // Guards the comparison itself. A truncated or abbreviated revision must
    // not satisfy the freshness check by being a prefix of the real head.
    let l = parsed(&HEAD[..16], &[Row::valid("Nat.a")]);
    assert_eq!(reasons(&verify(&l, &["Nat.a"], HEAD)), vec!["stale"]);
}

#[test]
fn an_unknown_symbol_blocks() {
    let l = parsed(HEAD, &[Row::valid("Nat.a"), Row::valid("Nat.ghost")]);
    let blocks = verify(&l, &["Nat.a"], HEAD);
    assert_eq!(reasons(&blocks), vec!["unknown"]);
    assert!(matches!(&blocks[0], Block::UnknownSymbol { symbol } if symbol == "Nat.ghost"));
}

#[test]
fn a_root_mismatch_blocks() {
    // byte-identical declared, but the two roots differ: the row asserts a
    // parity its own digests contradict.
    let mut r = Row::valid("Nat.a");
    r.oracle_root = ROOT_B.to_string();
    let l = parsed(HEAD, &[r]);
    let blocks = verify(&l, &["Nat.a"], HEAD);
    assert_eq!(reasons(&blocks), vec!["root-mismatch"]);
}

#[test]
fn the_comparison_class_decides_what_the_roots_must_say() {
    // acceptance-only compared no artifacts, so citing roots claims a
    // comparison that did not happen...
    let mut cited = Row::valid("Nat.a");
    cited.comparison = "acceptance-only".to_string();
    assert_eq!(
        reasons(&verify(&parsed(HEAD, &[cited]), &["Nat.a"], HEAD)),
        vec!["root-mismatch"]
    );

    // ...and with the roots declared absent, it is a legitimate row.
    let mut honest = Row::valid("Nat.a");
    honest.comparison = "acceptance-only".to_string();
    honest.ours_root = "-".to_string();
    honest.oracle_root = "-".to_string();
    assert!(verify(&parsed(HEAD, &[honest]), &["Nat.a"], HEAD).is_empty());

    // A normalized comparison must cite both roots.
    let mut normalized = Row::valid("Nat.a");
    normalized.comparison = "normalized-identical".to_string();
    normalized.normalizer = "diagnostic-text/1".to_string();
    normalized.ours_root = "-".to_string();
    assert_eq!(
        reasons(&verify(&parsed(HEAD, &[normalized]), &["Nat.a"], HEAD)),
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
        reasons(&verify(&parsed(HEAD, &[unnamed]), &["Nat.a"], HEAD))
            .contains(&"incoherent-comparison")
    );

    let mut spurious = Row::valid("Nat.a");
    spurious.normalizer = "diagnostic-text/1".to_string();
    assert_eq!(
        reasons(&verify(&parsed(HEAD, &[spurious]), &["Nat.a"], HEAD)),
        vec!["incoherent-comparison"]
    );
}

#[test]
fn a_mock_backed_row_cannot_close_an_l_level() {
    // A mock may support a unit test and may NOT close a public claim.
    let mut r = Row::valid("Nat.a");
    r.backing = "mock".to_string();
    let blocks = verify(&parsed(HEAD, &[r]), &["Nat.a"], HEAD);
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
    assert!(verify(&parsed(HEAD, &[l0]), &["Nat.a"], HEAD).is_empty());
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
        let blocks = verify(&parsed(HEAD, &[r]), &["Nat.a"], HEAD);
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
        let blocks = verify(&parsed(HEAD, &[r]), &["Nat.a"], HEAD);
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
    assert!(verify(&parsed(HEAD, &[proven]), &["Nat.a"], HEAD).is_empty());
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
            let want = reasons(&verify(&parsed(HEAD, &[baseline]), &["Nat.a"], HEAD))
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
                let got = reasons(&verify(&parsed(HEAD, &[r]), &["Nat.a"], HEAD))
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
            let want = reasons(&verify(&parsed(HEAD, &[baseline]), &["Nat.a"], HEAD))
                .contains(&"overclaimed-claim");

            for level in ["L0", "L1", "L2", "L3", "L4"] {
                let mut r = Row::valid("Nat.a");
                r.state = state.to_string();
                r.claim = claim.to_string();
                r.level = level.to_string();
                let got = reasons(&verify(&parsed(HEAD, &[r]), &["Nat.a"], HEAD))
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
                reasons(&verify(&parsed(HEAD, &[r]), &["Nat.a"], HEAD)).contains(&"mock-only"),
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
        let l = parsed(HEAD, &[Row::valid(symbol)]);
        let blocks = verify(&l, &[symbol], HEAD);
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
    let blocks = verify(&l, &["Nat.a", "Nat.b"], HEAD);
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
    let blocks = verify(&parsed(HEAD, &[r]), &["Nat.a"], HEAD);
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
    let l = parsed(HEAD, &[r]);
    let row = &l.rows[0];
    assert_eq!(row.state, EvidenceState::Proven);
    assert_eq!(row.claim, ClaimType::Invariant);
    assert_eq!(row.level, LLevel::L4);
}
