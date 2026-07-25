//! A whole-text lexical run, and its incremental re-lex (plan §9; bead franken_lean-81oq).
//!
//! ## What a run is, and what it is not
//!
//! [`lex_run`] alternates [`scan_trivia`] and [`lex_token`] across a text, recovering past
//! refusals, and records every trivia span, token and refusal in order. It is **total**: any
//! `SourceText` produces a run.
//!
//! It is deliberately **not** a claim to be a faithful Lean tokenizer, and the distinction
//! matters enough to state in the type's own docs. Lean's lexing is parser-driven in places —
//! `docComment := "/--" >> ppSpace >> commentBody >> ppLine` (`Lean/Parser/Term.lean:91`)
//! consumes its body with a dedicated parser the token table knows nothing about — so no
//! total "next token" function can be faithful on its own. A run is a *driver over the
//! lexical primitives*, and its purpose here is to be the subject of differentials:
//!
//! * [`relex_incremental`] must equal [`lex_run`] for every edit. That property is about the
//!   two agreeing with each other, and holds regardless of whether the driver is faithful.
//! * the thread matrix must produce the identical run at every thread count (FL-INV-01).
//!
//! When the category parser (bead `fln-ffam`) drives token consumption for real, it should
//! replace this driver and re-run both differentials over itself unchanged.
//!
//! ## Why the incremental result must be compared, not trusted
//!
//! An incremental relexer that simply re-lexes everything satisfies "incremental equals
//! from-scratch" perfectly and is worth nothing. So [`Damage`] reports how much was redone,
//! and the property suite asserts *both*: that the results are identical, and that the work
//! was actually bounded. The equality says the answer is right; the bound says the answer was
//! cheap. Neither implies the other, and only asserting the first is the trap.
//!
//! The restart rule is inherited from the attachment damage bound established in bead
//! `franken_lean-tkr2`: **overlapped, plus at most one**. Lexing needs the "plus one" for the
//! same reason attachment does — an edit at a token's leading edge can change what the
//! *previous* event was, as when typing a `-` before an existing `-` turns two tokens into a
//! line comment.

use crate::source::{BytePos, ByteSpan, SourceText};
use crate::token::{LexedToken, TokenError, TokenTable, lex_token};
use crate::trivia::scan_trivia;

/// One event in a lexical run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    /// A trivia span. Recorded even when empty at a position, because *where* trivia is
    /// absent is as much a part of the run as where it is present.
    Trivia(ByteSpan),
    /// A token, with its extent.
    Token(LexedToken),
    /// A refusal that was recovered past, with the region skipped.
    Refused { error: RunError, skipped: ByteSpan },
}

impl Event {
    /// The bytes this event occupies.
    pub fn extent(&self) -> ByteSpan {
        match self {
            Event::Trivia(span) => *span,
            Event::Token(token) => token.extent,
            Event::Refused { skipped, .. } => *skipped,
        }
    }

    /// Where this event begins — the offset a re-lex would restart from.
    pub fn start(&self) -> BytePos {
        self.extent().start()
    }
}

/// A refusal in a run: either trivia lexing or token lexing said no.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunError {
    Trivia(crate::trivia::TriviaError),
    Token(TokenError),
}

impl RunError {
    /// The same refusal with its offset moved, delegating to the error's own shift.
    pub fn shifted(&self, delta: isize) -> RunError {
        match self {
            RunError::Trivia(error) => RunError::Trivia(error.shifted(delta)),
            RunError::Token(error) => RunError::Token(error.shifted(delta)),
        }
    }

    pub fn message(&self) -> &'static str {
        match self {
            RunError::Trivia(error) => error.message(),
            RunError::Token(error) => error.message(),
        }
    }

    pub fn at(&self) -> BytePos {
        match self {
            RunError::Trivia(error) => error.at(),
            RunError::Token(error) => error.at(),
        }
    }
}

/// A whole-text lexical run.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LexRun {
    pub events: Vec<Event>,
}

impl LexRun {
    /// Whether the run found no refusals. Recovery only ever appends refusals, so this can
    /// move from true to false and never back — the same law [`crate::recover`] establishes,
    /// preserved here because the driver must not become a way around it.
    pub fn accepted(&self) -> bool {
        !self
            .events
            .iter()
            .any(|event| matches!(event, Event::Refused { .. }))
    }

    /// Every refusal as (message, offset), which is what a diagnostic renderer consumes.
    ///
    /// Compared directly in the thread matrix: FL-INV-01 requires identical *diagnostics*,
    /// not merely the same count of them.
    pub fn diagnostics(&self) -> Vec<(&'static str, BytePos)> {
        self.events
            .iter()
            .filter_map(|event| match event {
                Event::Refused { error, .. } => Some((error.message(), error.at())),
                _ => None,
            })
            .collect()
    }

    /// The token extents, in order — what [`crate::attach`] consumes.
    pub fn token_extents(&self) -> Vec<ByteSpan> {
        self.events
            .iter()
            .filter_map(|event| match event {
                Event::Token(token) => Some(token.extent),
                _ => None,
            })
            .collect()
    }
}

/// Lex a whole text from scratch, recovering past refusals.
pub fn lex_run(text: &SourceText, table: &TokenTable) -> LexRun {
    LexRun {
        events: lex_from(text, table, BytePos(0)),
    }
}

/// The driver, from an arbitrary offset. Shared by the full and incremental paths so there is
/// exactly one definition of what a run is — two drivers would be two things to drift, which
/// is the same argument that keeps recovery from having its own lexer.
fn lex_from(text: &SourceText, table: &TokenTable, from: BytePos) -> Vec<Event> {
    let mut events = Vec::new();
    let mut at = from;
    let end = text.len_bytes();
    while at.0 < end {
        match scan_trivia(text, at) {
            Ok(stop) => {
                events.push(Event::Trivia(span(at, stop)));
                if stop.0 >= end {
                    break;
                }
                match lex_token(text, table, stop) {
                    Ok(token) => {
                        let next = token.extent.end();
                        // A zero-width token would spin any driver forever. The lexer cannot
                        // produce one, and this guard is what makes that structural rather
                        // than argued — the fuzz suite asserts the same invariant directly.
                        if next.0 <= stop.0 {
                            events.push(Event::Refused {
                                error: RunError::Token(TokenError::NotAToken { at: stop }),
                                skipped: span(stop, BytePos(stop.0 + 1)),
                            });
                            at = BytePos(stop.0 + 1);
                            continue;
                        }
                        events.push(Event::Token(token));
                        at = next;
                    }
                    Err(error) => {
                        let resume = resume_after_token_error(text, stop);
                        events.push(Event::Refused {
                            error: RunError::Token(error),
                            skipped: span(stop, resume),
                        });
                        at = resume;
                    }
                }
            }
            Err(error) => {
                let resume = crate::recover::resume_after_trivia_error(text, error);
                events.push(Event::Refused {
                    error: RunError::Trivia(error),
                    // The event's extent starts where the SCAN started, not where the error
                    // points. Those are different things, and conflating them left a hole in
                    // the run: an unterminated comment reports `opened_at`, so in `x /- oops`
                    // the refusal pointed at offset 2 while the scan began at 1, and the byte
                    // between them belonged to no event at all. A run with a hole cannot be
                    // re-lexed incrementally, because realignment walks event starts — which
                    // is how the incremental property found this.
                    skipped: span(at, resume),
                });
                if resume.0 <= at.0 {
                    break;
                }
                at = resume;
            }
        }
    }
    events
}

/// Skip one scalar past a token refusal, so the driver always advances.
fn resume_after_token_error(text: &SourceText, at: BytePos) -> BytePos {
    let s = text.as_str();
    let step = s[at.0..].chars().next().map_or(1, char::len_utf8);
    BytePos((at.0 + step).min(text.len_bytes()))
}

/// How much of an incremental re-lex was reused, and how much was redone.
///
/// Reported rather than asserted-as-correctness: the bound says how much work was needed, and
/// the equality against a from-scratch run is what says the answer is right. Conflating them
/// is how a relexer that redoes everything passes for incremental.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Damage {
    /// Events reused unchanged from before the edit.
    pub reused_prefix: usize,
    /// Events produced by re-lexing.
    pub relexed: usize,
    /// Events reused from after the edit, with their spans shifted.
    pub reused_suffix: usize,
}

impl Damage {
    pub fn total_events(self) -> usize {
        self.reused_prefix + self.relexed + self.reused_suffix
    }

    /// Whether any reuse happened at all. A relexer that redoes the whole text still returns
    /// the right answer, so this is the only thing that distinguishes incremental from
    /// correct-but-pointless.
    pub fn reused_anything(self) -> bool {
        self.reused_prefix > 0 || self.reused_suffix > 0
    }
}

/// Re-lex after one edit, reusing what the edit could not have changed.
///
/// `edited` is the span **in the old text** that was replaced, and `inserted_len` the byte
/// length of what replaced it. `new_text` is the text after the edit.
pub fn relex_incremental(
    old: &LexRun,
    edited: ByteSpan,
    inserted_len: usize,
    new_text: &SourceText,
    table: &TokenTable,
) -> (LexRun, Damage) {
    // The restart point. "Overlapped, plus one" — the attachment bound from
    // franken_lean-tkr2 — is NOT sufficient here, and finding out why is the substance of
    // this function.
    //
    // Attachment's bound holds because an attachment entry is determined by the token spans
    // around it. A lexical decision is not: `match_prefix` walks the trie as far as it has
    // children, which can run past the token it emits. With `<`, `<=` and `<==>` in the
    // table, `<==x` emits a one-byte `<` after reading four bytes — so editing the `x` into
    // a `>` changes the token at offset 0, three events away. Backing up one event would
    // never revisit that decision, and the re-lex would silently disagree with a full one.
    //
    // So the restart backs up by the lexer's actual lookahead bound:
    //   * `max_token_len`, covering every trie walk;
    //   * `LITERAL_LOOKAHEAD`, covering the fixed two-character probes — the `..` after a
    //     numeral, the `''` that is not a char literal, `--` and `/-`, the backtick's
    //     following character;
    //   * a backward walk over `#`* and an `r`, the one *unbounded* probe in the lexer
    //     (`isRawStrLitStart` reads arbitrarily many `#`s before deciding), so an `r###x`
    //     whose `x` becomes a quote is re-lexed from the `r`.
    // Then it backs up to an event boundary, because a run must start on one.
    //
    // The bound is a claim, and the property suite is what makes it falsifiable: an
    // insufficient bound shows up as `incremental != from-scratch` on the targeted inputs.
    let first_touched = old
        .events
        .iter()
        .position(|event| event.extent().end().0 >= edited.start().0)
        .unwrap_or(old.events.len());

    const LITERAL_LOOKAHEAD: usize = 2;
    let lookback = table.max_token_len().max(LITERAL_LOOKAHEAD);
    let mut safe_before = edited.start().0.saturating_sub(lookback);
    safe_before = extend_back_over_raw_string_opener(new_text, safe_before);

    // Two events can share a start offset: an empty trivia span sits at the same offset as
    // the token after it. So take the last event starting at or before the safe point, then
    // back up to the FIRST event with that same start — otherwise the reused prefix keeps an
    // event the re-lex is about to produce again, and the run gains a duplicate. The property
    // found exactly that, as a doubled empty `Trivia(0..0)` at the head of the run.
    let by_lookback = old
        .events
        .iter()
        .rposition(|event| event.start().0 <= safe_before)
        .unwrap_or(0);
    let lookback_offset = old.events.get(by_lookback).map_or(BytePos(0), Event::start);
    let by_lookback = old
        .events
        .iter()
        .position(|event| event.start().0 >= lookback_offset.0)
        .unwrap_or(by_lookback);

    // The SECOND term, and the one that makes the rule correct for delimited constructs.
    //
    // A string, block comment or raw string scans forward until it finds its closing
    // delimiter, which can be arbitrarily far away — so the lexer's lookahead is **not**
    // bounded by `max_token_len` at all. Deleting a closing quote forty bytes to the right
    // turns a finished string token into one that swallows the rest of the file, changing the
    // event at its opening quote.
    //
    // What saves it is that such a construct's *extent covers everything it read*. So "the
    // first event whose extent reaches the edit, minus one" — the overlapped-plus-one shape
    // from franken_lean-tkr2 — catches precisely the unbounded cases, while the lookback term
    // above catches the cases where a decision read PAST its own extent (a trie walk, the
    // numeral's `..`, the raw-string opener probe). Neither term subsumes the other, and the
    // restart is the earlier of the two.
    //
    // I had only the lookback term at first. The property suite failed with an incremental run
    // of 24 events against a from-scratch run of 7, because a deleted quote let one token
    // swallow a region the incremental path had already carved into events.
    let by_overlap = first_touched.saturating_sub(1);

    // The THIRD term, and the one that took a differential to find.
    //
    // A *failed* unbounded scan reads to end of text but consumes almost nothing. An
    // unterminated `«` at offset 4 scans the whole file looking for `»`, finds none, and emits
    // a two-byte refusal. So the region it READ is the file, while the region its event
    // COVERS is two bytes — and the overlap term, which reasons about extents, cannot see it.
    //
    // Inserting a `»` forty bytes to the right then closes that escape and turns twelve events
    // into one identifier. The property suite caught exactly that: incremental produced 24
    // events where a full re-lex produced 7.
    //
    // Every unbounded scan in the lexer — the `«` escape, strings, raw strings, block
    // comments — reports its failure as a refusal, and a successful one's extent covers what
    // it read. So restarting at or before the earliest refusal that begins at or before the
    // edit covers all of them, with no need to thread a read-reach through every literal
    // function. It is conservative: a file with an early unterminated construct gets less
    // reuse. That is the honest answer rather than a cheap one, because in such a file a
    // later edit genuinely can change everything to its left.
    let by_refusal = old
        .events
        .iter()
        .position(|event| {
            matches!(event, Event::Refused { .. }) && event.start().0 <= edited.start().0
        })
        .unwrap_or(usize::MAX);

    let mut restart_index = by_lookback.min(by_overlap).min(by_refusal);

    // A restart point must be a TRIVIA event, and it must still be a boundary in the NEW text.
    //
    // Trivia events are the driver's loop head: `lex_from` scans trivia first and emits the
    // span it found, empty or not, so restarting at a *token's* offset emits a spurious
    // `Trivia(at, at)` that a full run never produces there. That much is a fact about the
    // driver.
    //
    // The second condition is the one that is easy to miss, and it is not a bound at all.
    // A restart point valid in the OLD text can be *inside a construct* in the new one:
    // delete a closing quote forty bytes to the right and offset 45 stops being a boundary and
    // becomes the middle of a string. Lexing from there is then simply not what a full run does
    // there, and no lookahead bound can express that, because the construct is unbounded.
    //
    // So the point is verified rather than assumed: probe a run from the previous candidate and
    // require it to reproduce a boundary at this offset. If it does not, this offset is inside
    // something, and the search backs up. Offset 0 is always valid, so the loop terminates —
    // in the worst case as a full re-lex, which is correct and merely not cheap.
    let is_head = |index: usize| matches!(old.events[index], Event::Trivia(_));
    loop {
        while restart_index > 0 && !is_head(restart_index) {
            restart_index -= 1;
        }
        if restart_index == 0 {
            break;
        }
        let restart_at = old.events[restart_index].start();
        let Some(previous) = (0..restart_index).rev().find(|index| is_head(*index)) else {
            restart_index = 0;
            break;
        };
        let probe = lex_from(new_text, table, old.events[previous].start());
        let reproduced = probe
            .iter()
            .any(|event| event.start() == restart_at && matches!(event, Event::Trivia(_)));
        if reproduced {
            break;
        }
        restart_index = previous;
    }
    let restart_offset = old
        .events
        .get(restart_index)
        .map_or(BytePos(0), Event::start);
    let reused_prefix = restart_index;
    let restart_at = restart_offset;

    // Old events wholly after the edit can be reused, shifted. Their offsets move by the
    // signed delta, computed in isize so a deletion cannot wrap.
    let delta = inserted_len as isize - edited.len_bytes() as isize;
    let tail_from = edited.end().0;

    let mut events: Vec<Event> = old.events[..reused_prefix].to_vec();
    let relexed_all = lex_from(new_text, table, restart_at);

    // Realign, and here the soundness argument runs the other way — it is a theorem rather
    // than a bound.
    //
    // `lex_from` reads only forward: `scan_trivia` and `lex_token` both consume from their
    // start offset and never consult a byte before it. So the run from any offset is a
    // function of the text suffix at that offset. If a re-lexed event begins at `at` and an
    // old event begins at `at - delta` where that old offset is at or after the edit's end,
    // then the two suffixes are byte-identical, and therefore so is every event from there
    // on. That is what makes splicing the old tail sound rather than optimistic — and it is
    // also why the reused tail's offsets must be shifted, including the offsets inside
    // reused diagnostics.
    //
    // If nothing aligns, the re-lex simply runs to the end and nothing is reused: correct,
    // just not cheap. The Damage report is what distinguishes those two outcomes.
    let mut relexed_count = relexed_all.len();
    let mut suffix_index = old.events.len();
    'outer: for (produced, event) in relexed_all.iter().enumerate() {
        // Only a trivia event is a resumable point, on both sides, for the same reason the
        // restart is: it is the driver's loop head. Splicing a tail that begins at a token
        // drops the trivia event the driver emits before it — which the property found as a
        // missing empty `Trivia` after a recovered refusal.
        if !matches!(event, Event::Trivia(_)) {
            continue;
        }
        let at = event.start().0;
        for (index, candidate) in old.events.iter().enumerate().skip(first_touched) {
            if candidate.start().0 < tail_from || !matches!(candidate, Event::Trivia(_)) {
                continue;
            }
            let shifted = candidate.start().0 as isize + delta;
            if shifted == at as isize && produced > 0 {
                relexed_count = produced;
                suffix_index = index;
                break 'outer;
            }
        }
    }

    events.extend(relexed_all[..relexed_count].iter().cloned());
    let mut reused_suffix = 0usize;
    for candidate in &old.events[suffix_index.min(old.events.len())..] {
        events.push(shift_event(candidate, delta));
        reused_suffix += 1;
    }

    (
        LexRun { events },
        Damage {
            reused_prefix,
            relexed: relexed_count,
            reused_suffix,
        },
    )
}

/// Walk back over `#`* and an `r` immediately before `at`.
///
/// `isRawStrLitStart` is the lexer's only unbounded probe: it reads arbitrarily many `#`s
/// after an `r` before deciding whether a raw string starts. Everything else the lexer looks
/// ahead at is bounded by the longest token or by two characters. Without this walk, editing
/// the byte after `r###` from `x` to `"` would turn four events into one and the re-lex would
/// never revisit the `r`.
fn extend_back_over_raw_string_opener(text: &SourceText, at: usize) -> usize {
    let bytes = text.as_bytes();
    let mut at = at.min(bytes.len());
    while at > 0 && bytes[at - 1] == b'#' {
        at -= 1;
    }
    if at > 0 && bytes[at - 1] == b'r' {
        at -= 1;
    }
    at
}

fn shift_event(event: &Event, delta: isize) -> Event {
    let shift = |span: ByteSpan| {
        let start = (span.start().0 as isize + delta).max(0) as usize;
        let end = (span.end().0 as isize + delta).max(0) as usize;
        ByteSpan::new(BytePos(start), BytePos(end)).unwrap_or(ByteSpan::empty_at(BytePos(start)))
    };
    match event {
        Event::Trivia(span) => Event::Trivia(shift(*span)),
        Event::Token(token) => Event::Token(LexedToken {
            kind: token.kind.clone(),
            extent: shift(token.extent),
        }),
        Event::Refused { error, skipped } => Event::Refused {
            // A reused refusal's offset moves with the text, or it would point at the file the
            // user had before the edit. Each error type shifts itself, exhaustively, so a
            // variant added later cannot silently keep a stale position.
            error: error.shifted(delta),
            skipped: shift(*skipped),
        },
    }
}

fn span(start: BytePos, end: BytePos) -> ByteSpan {
    ByteSpan::new(start, end).unwrap_or(ByteSpan::empty_at(start))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text_of(raw: &str) -> SourceText {
        SourceText::from_utf8(raw.as_bytes()).expect("valid UTF-8")
    }

    fn table() -> TokenTable {
        TokenTable::from_tokens(["def", "fun", "theorem", ":=", "=>", "(", ")", "+", "-", "→"])
    }

    /// A run covers the whole text: every byte belongs to exactly one event, in order. If it
    /// did not, an incremental re-lex could not realign on event starts.
    #[test]
    fn a_run_covers_every_byte_exactly_once_in_order() {
        for raw in [
            "def f := fun x => x + 1",
            "-- c\ndef f := 1",
            "/- a /- b -/ -/ def",
            "",
            "x",
            "\t",
            "def\tf",
            // Refusals whose diagnostic offset is AHEAD of where the scan started. Each of
            // these has content before the refusal, which is exactly what exposes a hole.
            "x /- unterminated",
            "def f := /- oops",
            "  /- oops",
            "a\tb",
            "a /- x /- y -/",
        ] {
            let text = text_of(raw);
            let run = lex_run(&text, &table());
            let mut at = 0usize;
            for event in &run.events {
                assert_eq!(
                    event.extent().start().0,
                    at,
                    "{raw:?}: event starts at {} but the previous ended at {at}",
                    event.extent().start().0
                );
                at = event.extent().end().0;
            }
            assert_eq!(at, text.len_bytes(), "{raw:?}: run stopped short");
        }
    }

    /// The driver always advances, so no input makes it loop. Asserted over the inputs most
    /// likely to stall it: refusals at the very last byte.
    #[test]
    fn the_driver_advances_on_every_refusal() {
        for raw in ["\t", "\r", "/-", "#", "def\t", "x\r", "«", "0x", "\"", "'"] {
            let text = text_of(raw);
            let run = lex_run(&text, &table());
            assert!(!run.events.is_empty(), "{raw:?}: produced nothing");
            assert!(!run.accepted(), "{raw:?}: should have refused");
            let covered = run.events.last().expect("nonempty").extent().end().0;
            assert_eq!(covered, text.len_bytes(), "{raw:?}: did not reach the end");
        }
    }

    /// Diagnostics are (message, offset) pairs and every offset is inside the text. A
    /// diagnostic pointing outside the file crashes the renderer, not the lexer, which is
    /// why the invariant belongs here rather than there.
    #[test]
    fn every_diagnostic_offset_is_inside_the_text() {
        for raw in ["a\tb\tc", "/- x", "x\ry", "«a", "0x", "1e", "\"a"] {
            let text = text_of(raw);
            let run = lex_run(&text, &table());
            for (message, at) in run.diagnostics() {
                assert!(
                    at.0 <= text.len_bytes(),
                    "{raw:?}: {message:?} points at {} past the end {}",
                    at.0,
                    text.len_bytes()
                );
                assert!(!message.is_empty(), "{raw:?}: empty diagnostic message");
            }
        }
    }
}
