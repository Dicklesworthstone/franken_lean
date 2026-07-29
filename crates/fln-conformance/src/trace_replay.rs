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
///
/// A line not opening with `[class]` is a **continuation** of the previous event's
/// body — the Reference wraps long terms onto follow-on lines (measured in the
/// multi-family fixture: `simp.rewrite` payloads carry their terms this way). A
/// continuation with no previous event is the real `NoClass` refusal. The known
/// limit, stated rather than discovered: a wrapped term that happens to begin a
/// line with `[` is indistinguishable from an event here; the production parser
/// reads `--json` message envelopes, where the boundary is explicit.
pub fn parse_trace(text: &str) -> Result<Vec<TraceEvent>, TraceParseError> {
    let mut events: Vec<TraceEvent> = Vec::new();
    let mut previous_depth = 0usize;
    for (index, raw) in text.lines().enumerate() {
        let line = index + 1;
        if raw.trim().is_empty() {
            continue;
        }
        let rest = raw.trim_start();
        if !rest.starts_with('[') {
            let Some(prev) = events.last_mut() else {
                return Err(TraceParseError::NoClass { line });
            };
            prev.body.push('\n');
            prev.body.push_str(rest.trim_end());
            continue;
        }
        let indent = raw.len() - rest.len();
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

/// The stock event families of TraceContractV1, classified from the pin's own
/// class names. `Diagnostics` is the heartbeat/depth family at the **amended**
/// granularity increment 5 measured: per-declaration counter blocks, since zero
/// of the pin's 399 trace classes emit per-event ticks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventFamily {
    Unifier,
    InstanceSearch,
    Simp,
    ElabStep,
    Postponement,
    Diagnostics,
    Unknown,
}

/// Classify a trace class into its family. Prefix-based, deliberately: the
/// subclass tree (`.foApprox`, `.answer`, `.rewrite`, …) rides with its family.
pub fn classify(class: &str) -> EventFamily {
    if class.starts_with("Meta.isDefEq") || class.starts_with("Meta.whnf") {
        EventFamily::Unifier
    } else if class.starts_with("Meta.synthInstance") {
        EventFamily::InstanceSearch
    } else if class.starts_with("Meta.Tactic.simp") || class.starts_with("Debug.Meta.Tactic.simp") {
        EventFamily::Simp
    } else if class.starts_with("Elab.postpone") {
        EventFamily::Postponement
    } else if class.starts_with("Elab.step") {
        EventFamily::ElabStep
    } else if matches!(class, "diag" | "reduction" | "type_class" | "kernel") {
        EventFamily::Diagnostics
    } else {
        EventFamily::Unknown
    }
}

/// A family checker's typed refusal. Each variant names the line it fired on,
/// because a violation without a location is not triageable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FamilyViolation {
    /// An instance-search `.answer` arrived before any `.apply`/`.tryResolve`
    /// attempt anywhere earlier in the stream — the candidate machinery cannot
    /// have produced it.
    AnswerBeforeAnyAttempt { line: usize },
    /// A `.instances` candidate-order payload does not open a `#[` vector.
    MalformedCandidateList { line: usize },
    /// A simp `.rewrite` payload does not open with `name:priority:`.
    MalformedRewrite { line: usize },
    /// An `Elab.step.result` with no `Elab.step` anywhere before it.
    ResultBeforeStep { line: usize },
    /// A postponement body outside the pinned shape census
    /// (`not ready yet` / `resuming ?…`) — extended deliberately when a
    /// regenerated fixture teaches a new shape, never silently.
    MalformedPostponement { line: usize },
    /// A diagnostics counter line whose count is not a positive integer.
    MalformedCounter { line: usize },
    /// The checker found nothing of its family to check. Anti-vacuity: a green
    /// from a checker that checked nothing is the vacuous green this project
    /// refuses everywhere else.
    EmptyFamily { family: &'static str },
}

/// Minimal independent consumer for the instance-search family: candidate lists
/// are well-formed vectors, and no answer precedes every attempt.
pub fn check_instance_search(events: &[TraceEvent]) -> Result<usize, FamilyViolation> {
    let mut attempts = 0usize;
    let mut answers = 0usize;
    let mut checked = 0usize;
    for e in events {
        if classify(&e.class) != EventFamily::InstanceSearch {
            continue;
        }
        checked += 1;
        match e.class.as_str() {
            "Meta.synthInstance.apply" | "Meta.synthInstance.tryResolve" => attempts += 1,
            "Meta.synthInstance.instances" => {
                if !e.body.starts_with("#[") {
                    return Err(FamilyViolation::MalformedCandidateList { line: e.line });
                }
            }
            "Meta.synthInstance.answer" => {
                if attempts == 0 {
                    return Err(FamilyViolation::AnswerBeforeAnyAttempt { line: e.line });
                }
                answers += 1;
            }
            _ => {}
        }
    }
    if checked == 0 || answers == 0 {
        return Err(FamilyViolation::EmptyFamily {
            family: "instance-search",
        });
    }
    Ok(checked)
}

/// Minimal independent consumer for simp firings: every rewrite names its lemma
/// and priority (`Nat.add_zero:1000:` …), which is the payload Athanor's simp
/// must be implemented against.
pub fn check_simp(events: &[TraceEvent]) -> Result<usize, FamilyViolation> {
    let mut rewrites = 0usize;
    for e in events {
        if e.class != "Meta.Tactic.simp.rewrite" {
            continue;
        }
        let well_formed = e
            .body
            .split_once(':')
            .and_then(|(name, rest)| {
                let (prio, _) = rest.split_once(':')?;
                Some(
                    !name.is_empty()
                        && !prio.is_empty()
                        && prio.bytes().all(|b| b.is_ascii_digit()),
                )
            })
            .unwrap_or(false);
        if !well_formed {
            return Err(FamilyViolation::MalformedRewrite { line: e.line });
        }
        rewrites += 1;
    }
    if rewrites == 0 {
        return Err(FamilyViolation::EmptyFamily { family: "simp" });
    }
    Ok(rewrites)
}

/// Minimal independent consumer for macro-expansion/elaboration steps: a
/// `.result` event cannot precede every `.step`.
pub fn check_elab_steps(events: &[TraceEvent]) -> Result<usize, FamilyViolation> {
    let mut steps = 0usize;
    let mut results = 0usize;
    for e in events {
        if e.class == "Elab.step" {
            steps += 1;
        } else if e.class == "Elab.step.result" {
            if steps == 0 {
                return Err(FamilyViolation::ResultBeforeStep { line: e.line });
            }
            results += 1;
        }
    }
    if steps == 0 || results == 0 {
        return Err(FamilyViolation::EmptyFamily {
            family: "elab-step",
        });
    }
    Ok(steps + results)
}

/// Minimal independent consumer for postponements. The body shapes are the
/// pinned fixture's own census; a new shape refuses rather than passing unseen.
pub fn check_postponements(events: &[TraceEvent]) -> Result<usize, FamilyViolation> {
    let mut seen = 0usize;
    for e in events {
        if classify(&e.class) != EventFamily::Postponement {
            continue;
        }
        // The complete body-shape census of the pinned fixture, derived rather
        // than sampled: 31 `not ready yet`, 38 `resuming ?<id>`, 7 `succeeded`.
        if e.body != "not ready yet" && e.body != "succeeded" && !e.body.starts_with("resuming ?") {
            return Err(FamilyViolation::MalformedPostponement { line: e.line });
        }
        seen += 1;
    }
    if seen == 0 {
        return Err(FamilyViolation::EmptyFamily {
            family: "postponement",
        });
    }
    Ok(seen)
}

/// Minimal independent consumer for the heartbeat/depth family at the amended
/// granularity: `[diag]` counter blocks, every counter `name ↦ N` a positive
/// integer. Increment 5's measurement is why this reads counters and not ticks.
pub fn check_diagnostics(events: &[TraceEvent]) -> Result<usize, FamilyViolation> {
    let mut counters = 0usize;
    for e in events {
        if classify(&e.class) != EventFamily::Diagnostics {
            continue;
        }
        if let Some((_, count)) = e.body.split_once('\u{21a6}') {
            let count = count.trim();
            let count = count.split('\n').next().unwrap_or(count).trim();
            if count.is_empty() || !count.bytes().all(|b| b.is_ascii_digit()) {
                return Err(FamilyViolation::MalformedCounter { line: e.line });
            }
            counters += 1;
        }
    }
    if counters == 0 {
        return Err(FamilyViolation::EmptyFamily {
            family: "diagnostics",
        });
    }
    Ok(counters)
}

/// The order-sensitive semantic root of one family's event stream: FNV-1a over
/// (class, verdict, body) in stream order. Line numbers are deliberately
/// excluded — a pure line shift is telemetry — while ORDER is deliberately
/// included, because emission order is decision order and a reordering must
/// move the root.
pub fn family_root(events: &[TraceEvent], family: EventFamily) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    let mut fold = |bytes: &[u8]| {
        for &b in bytes {
            hash ^= u64::from(b);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    };
    for e in events {
        if classify(&e.class) != family {
            continue;
        }
        fold(e.class.as_bytes());
        fold(&[0xff]);
        fold(e.verdict.status_byte());
        fold(e.body.as_bytes());
        fold(&[0xfe]);
    }
    hash
}

impl TracedVerdict {
    fn status_byte(self) -> &'static [u8] {
        match self {
            TracedVerdict::Accepted => b"A",
            TracedVerdict::Rejected => b"R",
            TracedVerdict::Panicked => b"P",
            TracedVerdict::Unmarked => b"U",
        }
    }
}

/// The earliest divergence between two event streams — index plus both sides'
/// rendering — or `None` when they agree completely. This is the report shape
/// the design clause names: earliest causal divergence, no over-normalization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Divergence {
    pub index: usize,
    pub left: String,
    pub right: String,
}

pub fn earliest_divergence(a: &[TraceEvent], b: &[TraceEvent]) -> Option<Divergence> {
    let render =
        |e: &TraceEvent| format!("[{}] {:?} depth={} {}", e.class, e.verdict, e.depth, e.body);
    for (i, (x, y)) in a.iter().zip(b.iter()).enumerate() {
        if (x.depth, &x.class, x.verdict, &x.body) != (y.depth, &y.class, y.verdict, &y.body) {
            return Some(Divergence {
                index: i,
                left: render(x),
                right: render(y),
            });
        }
    }
    match a.len().cmp(&b.len()) {
        std::cmp::Ordering::Equal => None,
        std::cmp::Ordering::Less => Some(Divergence {
            index: a.len(),
            left: "<absent>".to_string(),
            right: render(&b[a.len()]),
        }),
        std::cmp::Ordering::Greater => Some(Divergence {
            index: b.len(),
            left: render(&a[b.len()]),
            right: "<absent>".to_string(),
        }),
    }
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

    /// The pinned Reference's five-family trace over `fixtures/g09_multi_family.lean`,
    /// byte-identical across repeated runs at generation time, zero host paths.
    const MULTI_TRACE: &str = include_str!("../fixtures/g09_multi_family_trace.txt");
    /// The pinned Reference's `[diag]` counter blocks over `fixtures/g09_diag.lean` —
    /// the heartbeat/depth family at the amended (per-declaration) granularity.
    const DIAG_TRACE: &str = include_str!("../fixtures/g09_diag_trace.txt");

    #[test]
    fn every_stock_family_is_present_and_its_checker_is_not_vacuous() {
        let events = parse_trace(MULTI_TRACE).expect("the multi-family trace parses");
        // Census by family — pinned, and every family nonempty, so no checker
        // below can green vacuously.
        let count = |f: EventFamily| events.iter().filter(|e| classify(&e.class) == f).count();
        assert_eq!(count(EventFamily::Unifier), 1862, "unifier census");
        assert_eq!(count(EventFamily::InstanceSearch), 655, "instance census");
        assert_eq!(count(EventFamily::Simp), 2, "simp census");
        assert_eq!(count(EventFamily::ElabStep), 261, "elab-step census");
        assert_eq!(count(EventFamily::Postponement), 76, "postponement census");
        assert_eq!(
            count(EventFamily::Unknown),
            0,
            "no event escapes classification"
        );
        // foApprox events ride inside the unifier family — the approximation
        // ladder is observable in this fixture, which increment 3 verified live.
        assert_eq!(
            events
                .iter()
                .filter(|e| e.class == "Meta.isDefEq.foApprox")
                .count(),
            10,
            "foApprox census"
        );
        assert_eq!(check_instance_search(&events), Ok(655));
        assert_eq!(check_simp(&events), Ok(2));
        assert_eq!(check_elab_steps(&events), Ok(261));
        assert_eq!(check_postponements(&events), Ok(76));
        let diag = parse_trace(DIAG_TRACE).expect("the diag trace parses");
        assert_eq!(check_diagnostics(&diag), Ok(22), "diag counter census");
        // And the anti-vacuity direction: an empty stream refuses, never greens.
        for refusal in [
            check_instance_search(&[]),
            check_simp(&[]),
            check_elab_steps(&[]),
            check_postponements(&[]),
            check_diagnostics(&[]),
        ] {
            assert!(
                matches!(refusal, Err(FamilyViolation::EmptyFamily { .. })),
                "an empty stream must refuse: {refusal:?}"
            );
        }
    }

    #[test]
    fn a_planted_omission_moves_the_family_root_and_is_located() {
        let events = parse_trace(MULTI_TRACE).expect("parses");
        let victim = events
            .iter()
            .position(|e| e.class == "Meta.synthInstance.answer")
            .expect("an answer exists");
        let mut mutated = events.clone();
        mutated.remove(victim);
        assert_ne!(
            family_root(&events, EventFamily::InstanceSearch),
            family_root(&mutated, EventFamily::InstanceSearch),
            "dropping an event must move its family's root"
        );
        let d = earliest_divergence(&events, &mutated).expect("divergence is reported");
        assert_eq!(
            d.index, victim,
            "the earliest divergence is the omission site"
        );
        assert!(
            d.left.contains("synthInstance.answer"),
            "and it names the victim: {d:?}"
        );
    }

    #[test]
    fn a_planted_reordering_is_refused_by_the_family_checker() {
        let events = parse_trace(MULTI_TRACE).expect("parses");
        let victim = events
            .iter()
            .position(|e| e.class == "Meta.synthInstance.answer")
            .expect("an answer exists");
        let mut mutated = events.clone();
        let moved = mutated.remove(victim);
        mutated.insert(0, moved);
        assert_eq!(
            check_instance_search(&mutated),
            Err(FamilyViolation::AnswerBeforeAnyAttempt {
                line: events[victim].line
            }),
            "an answer hoisted before every attempt must refuse by name"
        );
        // The root moves too — order is decision order.
        assert_ne!(
            family_root(&events, EventFamily::InstanceSearch),
            family_root(&mutated, EventFamily::InstanceSearch)
        );
    }

    #[test]
    fn a_planted_payload_mangle_is_refused_by_the_family_checker() {
        let events = parse_trace(MULTI_TRACE).expect("parses");
        let mut mutated = events.clone();
        let rw = mutated
            .iter_mut()
            .find(|e| e.class == "Meta.Tactic.simp.rewrite")
            .expect("a rewrite exists");
        rw.body = rw.body.replace(':', ";");
        let line = rw.line;
        assert_eq!(
            check_simp(&mutated),
            Err(FamilyViolation::MalformedRewrite { line }),
            "a rewrite stripped of its name:priority payload must refuse"
        );
        // Diagnostics: a counter mangled to a non-integer refuses.
        let diag = parse_trace(DIAG_TRACE).expect("parses");
        let mut bad = diag.clone();
        let victim = bad
            .iter_mut()
            .find(|e| e.body.contains('\u{21a6}'))
            .expect("a counter exists");
        victim.body = victim.body.replace('9', "nine");
        let line = victim.line;
        assert_eq!(
            check_diagnostics(&bad),
            Err(FamilyViolation::MalformedCounter { line })
        );
    }

    #[test]
    fn a_planted_outcome_flip_moves_exactly_the_touched_family_root() {
        let events = parse_trace(MULTI_TRACE).expect("parses");
        let mut mutated = events.clone();
        let victim = mutated
            .iter_mut()
            .find(|e| e.class == "Meta.synthInstance.answer")
            .expect("an answer exists");
        assert_eq!(victim.verdict, TracedVerdict::Accepted);
        victim.verdict = TracedVerdict::Rejected;
        assert_ne!(
            family_root(&events, EventFamily::InstanceSearch),
            family_root(&mutated, EventFamily::InstanceSearch),
            "an outcome flip must move the touched family's root"
        );
        // And ONLY the touched family — the other roots are unmoved, so a
        // divergence report can attribute the family rather than shrugging.
        for untouched in [
            EventFamily::Unifier,
            EventFamily::Simp,
            EventFamily::ElabStep,
            EventFamily::Postponement,
        ] {
            assert_eq!(
                family_root(&events, untouched),
                family_root(&mutated, untouched),
                "{untouched:?} must be unmoved"
            );
        }
    }

    #[test]
    fn identical_streams_report_no_divergence_and_a_tail_loss_is_located() {
        let events = parse_trace(MULTI_TRACE).expect("parses");
        assert_eq!(earliest_divergence(&events, &events), None);
        let truncated = &events[..events.len() - 1];
        let d = earliest_divergence(&events, truncated).expect("tail loss reported");
        assert_eq!(d.index, truncated.len());
        assert_eq!(d.right, "<absent>");
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
