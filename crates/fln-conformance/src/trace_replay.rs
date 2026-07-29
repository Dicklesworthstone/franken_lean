//! The golden-trace replay rig, seeded (bead `franken_lean-foo`, G0-9; plan §18.3).
//!
//! # What this is, and what it deliberately is not
//!
//! G0-9's acceptance (d): *"a replay rig prototype diffs a hand-written toy unifier
//! against traces to prove the comparison machinery."* This module is that prototype —
//! the **comparison machinery**, proven end to end over a real committed trace from the
//! pinned Reference: parse the trace into typed events, replay each defeq query through
//! a deliberately naive toy unifier, diff the toy's decisions against the oracle's, and
//! report every divergence with its payload. The toy unifier is *supposed* to diverge on
//! real cases (it knows nothing of delta or eta); the rig's job is to catch and name
//! those divergences exactly, because catching-and-naming is what the production rig
//! will do to Athanor.
//!
//! # The fixture, and why `include_str!`
//!
//! `fixtures/g09_pilot_trace.txt` is the pinned binary's own `trace.Meta.isDefEq`
//! output over `fixtures/g09_pilot.lean` — measured **byte-identical across repeated
//! runs** (the determinism property the whole golden-trace bet rests on) and containing
//! **zero host paths** (the telemetry separation law applied to a committed artifact).
//! It is compiled in with `include_str!`, so this rig resolves no path at runtime and a
//! test binary built in one worktree cannot read another's fixture — the k60n class,
//! closed by construction rather than by the checked macro.
//!
//! Regeneration is a deliberate act against the pin (the command is in the fixture's
//! sibling `.lean` header's history on bead `franken_lean-foo`); nothing regenerates it
//! per commit, exactly as the C1 module inventory works.
//!
//! # What the production rig adds that the toy does not
//!
//! Measured on the bead (comments 1654/1655): `--json` wraps every trace message with
//! deterministic source anchors (`pos`/`endPos`), so the production parser reads message
//! envelopes rather than bare text; six of seven event families flow from the stock
//! binary; heartbeat ticks are the one confirmed absence. None of that changes the
//! comparison machinery this module proves.

use std::fmt;

/// The oracle's verdict on one traced event, read from the trace's own marks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TracedVerdict {
    /// `✅️` — the query succeeded.
    Accepted,
    /// `❌️` — the query failed.
    Rejected,
    /// `💥️` — the query aborted.
    Panicked,
    /// An informational sub-line (assignability annotations and similar) with no mark.
    Unmarked,
}

/// One parsed trace event.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceEvent {
    /// 1-based line in the trace fixture.
    pub line: usize,
    /// Nesting depth: leading indent / 2. Depth is the causal structure.
    pub depth: usize,
    /// The trace class, e.g. `Meta.isDefEq`.
    pub class: String,
    pub verdict: TracedVerdict,
    /// The event body after class and verdict mark.
    pub body: String,
}

/// A typed parse refusal. The parser is total: hostile input refuses, never panics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraceParseError {
    /// Indentation not a multiple of two spaces: the causal depth is unreadable.
    OddIndent { line: usize },
    /// No `[class]` tag opens the event.
    NoClass { line: usize },
    /// A child event with no parent (depth jumps by more than one).
    OrphanDepth {
        line: usize,
        depth: usize,
        previous: usize,
    },
}

impl fmt::Display for TraceParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TraceParseError::OddIndent { line } => {
                write!(f, "trace line {line}: indentation is not a multiple of two")
            }
            TraceParseError::NoClass { line } => {
                write!(f, "trace line {line}: no [class] tag opens the event")
            }
            TraceParseError::OrphanDepth {
                line,
                depth,
                previous,
            } => write!(
                f,
                "trace line {line}: depth {depth} follows depth {previous}; a child \
                 without a parent is a broken causal tree"
            ),
        }
    }
}

impl std::error::Error for TraceParseError {}

/// Parse a plain-text trace (the `-D trace.Meta.isDefEq=true` stderr form) into events.
pub fn parse_trace(text: &str) -> Result<Vec<TraceEvent>, TraceParseError> {
    let mut events = Vec::new();
    let mut previous_depth = 0usize;
    for (index, raw) in text.lines().enumerate() {
        let line = index + 1;
        if raw.trim().is_empty() {
            continue;
        }
        let indent = raw.len() - raw.trim_start_matches(' ').len();
        if indent % 2 != 0 {
            return Err(TraceParseError::OddIndent { line });
        }
        let depth = indent / 2;
        if depth > previous_depth + 1 {
            return Err(TraceParseError::OrphanDepth {
                line,
                depth,
                previous: previous_depth,
            });
        }
        let rest = raw.trim_start();
        let Some(close) = rest.strip_prefix('[').and_then(|r| r.find(']')) else {
            return Err(TraceParseError::NoClass { line });
        };
        let class = rest[1..=close].to_string();
        let mut body = rest[close + 2..].trim_start().to_string();
        // The verdict mark, if present, leads the body; `\u{fe0f}` is the emoji
        // variation selector the Reference emits after each mark.
        let verdict = if let Some(stripped) = body.strip_prefix('✅') {
            body = stripped
                .trim_start_matches('\u{fe0f}')
                .trim_start()
                .to_string();
            TracedVerdict::Accepted
        } else if let Some(stripped) = body.strip_prefix('❌') {
            body = stripped
                .trim_start_matches('\u{fe0f}')
                .trim_start()
                .to_string();
            TracedVerdict::Rejected
        } else if let Some(stripped) = body.strip_prefix('💥') {
            body = stripped
                .trim_start_matches('\u{fe0f}')
                .trim_start()
                .to_string();
            TracedVerdict::Panicked
        } else {
            TracedVerdict::Unmarked
        };
        events.push(TraceEvent {
            line,
            depth,
            class,
            verdict,
            body,
        });
        previous_depth = depth;
    }
    Ok(events)
}

/// The toy unifier's answer to a defeq query.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ToyVerdict {
    Yes,
    No,
}

/// The hand-written toy unifier: syntactic equality plus "a bare metavariable side is
/// assignable". It knows nothing of delta, eta, universes, or instances — on purpose.
/// Every divergence it produces against the oracle is the rig demonstrating that it
/// catches a unifier whose approximation ladder is missing, which is precisely the
/// defect class the production rig must catch in Athanor.
pub fn toy_unify(lhs: &str, rhs: &str) -> ToyVerdict {
    let lhs = lhs.trim();
    let rhs = rhs.trim();
    if lhs == rhs {
        return ToyVerdict::Yes;
    }
    let is_bare_mvar = |s: &str| (s.starts_with("?m.") || s.starts_with("?u.")) && !s.contains(' ');
    if is_bare_mvar(lhs) || is_bare_mvar(rhs) {
        return ToyVerdict::Yes;
    }
    ToyVerdict::No
}

/// One replayed query and both sides' answers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Replayed {
    pub line: usize,
    pub lhs: String,
    pub rhs: String,
    pub oracle: TracedVerdict,
    pub toy: ToyVerdict,
}

impl Replayed {
    /// Whether the toy agrees with the oracle. A `Panicked` oracle event is a
    /// non-answer and never agrees or diverges — FL-INV-07 one layer down: the rig
    /// must not score a query the oracle did not answer.
    pub fn agreement(&self) -> Option<bool> {
        let oracle_yes = match self.oracle {
            TracedVerdict::Accepted => true,
            TracedVerdict::Rejected => false,
            TracedVerdict::Panicked | TracedVerdict::Unmarked => return None,
        };
        Some(oracle_yes == (self.toy == ToyVerdict::Yes))
    }
}

/// The replay report: every query, every divergence named.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReplayReport {
    pub queries: usize,
    pub agreements: usize,
    pub divergences: Vec<Replayed>,
    pub unscored: usize,
}

/// Replay every marked defeq query in a parsed trace through the toy unifier.
///
/// Queries are events of class `Meta.isDefEq` whose body carries ` =?= ` and whose
/// verdict is a real answer. Sub-events (deeper nesting) are replayed too: each marked
/// defeq node is a decision the oracle recorded, and the production rig replays the
/// full tree, so the toy does as well.
pub fn replay(events: &[TraceEvent]) -> ReplayReport {
    let mut report = ReplayReport::default();
    for event in events {
        if event.class != "Meta.isDefEq" {
            continue;
        }
        let Some((lhs, rhs)) = event.body.split_once(" =?= ") else {
            continue;
        };
        let replayed = Replayed {
            line: event.line,
            lhs: lhs.to_string(),
            rhs: rhs.to_string(),
            oracle: event.verdict,
            toy: toy_unify(lhs, rhs),
        };
        report.queries += 1;
        match replayed.agreement() {
            Some(true) => report.agreements += 1,
            Some(false) => report.divergences.push(replayed),
            None => report.unscored += 1,
        }
    }
    report
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pinned Reference's own trace over `fixtures/g09_pilot.lean`, byte-identical
    /// across repeated runs at generation time.
    const PILOT_TRACE: &str = include_str!("../fixtures/g09_pilot_trace.txt");

    #[test]
    fn the_pilot_trace_parses_totally_into_the_pinned_census() {
        let events = parse_trace(PILOT_TRACE).expect("the committed trace parses");
        // Anti-vacuity floor plus exact census: the fixture is committed, so its
        // numbers are pinned rather than floored. A regenerated fixture moves them
        // WITH the fixture, in one commit, which is the point of pinning.
        assert_eq!(events.len(), 343, "event census");
        assert!(
            events.iter().all(|e| e.class.starts_with("Meta.isDefEq")),
            "the pilot enables exactly one family"
        );
        let marked = events
            .iter()
            .filter(|e| e.verdict != TracedVerdict::Unmarked)
            .count();
        assert_eq!(marked, 278, "marked-verdict census");
        assert!(
            events.iter().any(|e| e.depth > 0),
            "the causal tree has depth; a flat parse lost the nesting"
        );
    }

    #[test]
    fn the_toy_unifier_diverges_where_it_should_and_the_rig_names_every_case() {
        // The POINT of the prototype: the toy knows no delta, so the oracle's
        // accepted `wrapped 3 =?= 3 + 1` class of queries must show up as named
        // divergences — proving the machinery that will catch a broken Athanor.
        let events = parse_trace(PILOT_TRACE).expect("parses");
        let report = replay(&events);
        assert_eq!(report.queries, 342, "replayed-query census");
        assert_eq!(
            report.queries,
            report.agreements + report.divergences.len() + report.unscored,
            "conservation: every query is agreed, diverged, or unscored"
        );
        assert!(
            !report.divergences.is_empty(),
            "a toy unifier that never diverges from the real one is not a toy; \
             the comparison machinery was never exercised"
        );
        // Every divergence carries its payload — a divergence without both sides
        // is not triageable.
        for d in &report.divergences {
            assert!(
                !d.lhs.is_empty() && !d.rhs.is_empty(),
                "payload lost at {d:?}"
            );
        }
        // And the known delta-blindness shows up by name.
        assert!(
            report
                .divergences
                .iter()
                .any(|d| d.lhs.contains("wrapped") || d.rhs.contains("wrapped")),
            "the delta case the pilot plants must be among the divergences"
        );
    }

    #[test]
    fn a_flipped_oracle_verdict_moves_the_diff() {
        // The comparison machinery must detect TRACE-side changes too: flip one
        // accepted mark to rejected and the census must move. A rig blind to this
        // would also be blind to a regenerated trace that silently changed.
        let flipped = PILOT_TRACE.replacen('✅', "❌", 1);
        assert_ne!(flipped, PILOT_TRACE, "the plant did not change anything");
        let before = replay(&parse_trace(PILOT_TRACE).expect("parses"));
        let after = replay(&parse_trace(&flipped).expect("still parses"));
        assert_eq!(
            before.queries, after.queries,
            "the plant is a verdict, not a query"
        );
        assert_ne!(
            (before.agreements, before.divergences.len()),
            (after.agreements, after.divergences.len()),
            "a flipped oracle verdict must move the agreement census"
        );
    }

    #[test]
    fn hostile_input_refuses_typed_and_never_panics() {
        for (text, want_odd, want_class, want_orphan) in [
            (" [Meta.isDefEq] x =?= y", true, false, false),
            ("no class tag here", false, true, false),
            (
                "[Meta.isDefEq] a =?= b\n    [Meta.isDefEq] child too deep",
                false,
                false,
                true,
            ),
        ] {
            match parse_trace(text) {
                Err(TraceParseError::OddIndent { .. }) => assert!(want_odd, "{text:?}"),
                Err(TraceParseError::NoClass { .. }) => assert!(want_class, "{text:?}"),
                Err(TraceParseError::OrphanDepth { .. }) => assert!(want_orphan, "{text:?}"),
                Ok(events) => panic!("hostile input parsed: {text:?} -> {events:?}"),
            }
        }
        // And total on arbitrary junk: refuse or parse, never panic.
        for junk in [
            "\u{0}\u{fe0f}[]",
            "[]",
            "[a]",
            "[a] ✅",
            "  ",
            "[a] b\n[c] d",
        ] {
            let _ = parse_trace(junk);
        }
    }

    #[test]
    fn a_panicked_oracle_event_is_unscored_never_a_divergence() {
        // FL-INV-07 one layer down: the oracle aborting a query is a non-answer.
        // Scoring it as agreement would launder; scoring it as divergence would
        // manufacture. It is neither.
        let text = "[Meta.isDefEq] 💥️ a =?= b";
        let report = replay(&parse_trace(text).expect("parses"));
        assert_eq!(report.queries, 1);
        assert_eq!(report.unscored, 1);
        assert_eq!(report.agreements, 0);
        assert!(report.divergences.is_empty());
    }
}
