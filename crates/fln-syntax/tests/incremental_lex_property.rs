//! `incremental_lex_property` — the incremental re-lex must equal a from-scratch re-lex for
//! every edit (bead franken_lean-81oq).
//!
//! ## Two assertions, and neither implies the other
//!
//! **Correctness:** `relex_incremental(...) == lex_run(new_text)`, for every edit, event for
//! event, including every diagnostic offset. Equality of the whole run, not of a summary.
//!
//! **Boundedness:** the re-lex actually reused work. This is a separate assertion because an
//! incremental relexer that throws everything away and re-lexes the file satisfies the
//! correctness property perfectly and is worth nothing. Asserting only correctness is the same
//! vacuity trap the recovery differential had to close with its accepted-inputs count, in a
//! new place: a test can be fully green while the thing it is testing does nothing.
//!
//! The damage bound says *how much had to be redone*. It does not say whether the answer was
//! right — that is the equality's job, and the two are kept apart deliberately.
//!
//! ## Why this is the second, independent test of the tkr2 bound
//!
//! Bead `franken_lean-tkr2` established that attachment damage is *overlapped, plus at most
//! one*. Lexing inherits the shape but **not** the constant, and this suite is where that
//! difference was found: a lexical decision can depend on bytes outside the event it produces,
//! because the trie walks as far as it has children. With `<`, `<=` and `<==>` in the table,
//! `<==x` emits a one-byte token after reading four bytes, so editing that `x` changes a
//! decision three events to the left. "Plus one" would never revisit it.
//!
//! `relex_incremental` therefore backs up by the lexer's real lookahead bound, and the
//! targeted cases below are what make that bound falsifiable rather than asserted.

#![forbid(unsafe_code)]

mod common;

use common::{BASES, Rng, random_insert, random_span, table, text_of};
use fln_syntax::rope::Rope;
use fln_syntax::run::{Damage, lex_run, relex_incremental};
use fln_syntax::source::{BytePos, ByteSpan};
use fln_syntax::token::TokenTable;

/// Report the first place two runs diverge, with a little context.
///
/// Comparing whole runs with `assert_eq!` produces a several-thousand-line diff in which the
/// one differing event is invisible. A property suite whose failure output cannot be read is a
/// property suite that gets muted, so locating the divergence is part of the test, not a
/// debugging convenience.
fn first_divergence(left: &fln_syntax::run::LexRun, right: &fln_syntax::run::LexRun) -> String {
    for (index, (a, b)) in left.events.iter().zip(right.events.iter()).enumerate() {
        if a != b {
            let from = index.saturating_sub(2);
            return format!(
                "diverge at event {index} of {}/{}\n  context before:\n{}\n  incremental: \
                 {a:?}\n  from-scratch: {b:?}",
                left.events.len(),
                right.events.len(),
                left.events[from..index]
                    .iter()
                    .map(|event| format!("    {event:?}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }
    }
    format!(
        "same events for {} steps, then lengths differ: incremental {} vs from-scratch {}\n           incremental tail: {:?}\n  from-scratch tail: {:?}",
        left.events.len().min(right.events.len()),
        left.events.len(),
        right.events.len(),
        left.events
            .iter()
            .skip(right.events.len())
            .take(3)
            .collect::<Vec<_>>(),
        right
            .events
            .iter()
            .skip(left.events.len())
            .take(3)
            .collect::<Vec<_>>()
    )
}

/// Apply one edit and assert the two ways of lexing the result agree exactly.
fn check_one_edit(
    table: &TokenTable,
    base: &str,
    span: ByteSpan,
    insert: &str,
    context: &str,
) -> Damage {
    let mut rope = Rope::from_utf8(base.as_bytes()).expect("valid base");
    let before = rope.source_text().clone();
    let old_run = lex_run(&before, table);

    rope.replace(span, insert).expect("edit is in range");
    let after = rope.source_text().clone();

    let (incremental, damage) = relex_incremental(&old_run, span, insert.len(), &after, table);
    let from_scratch = lex_run(&after, table);

    assert!(
        incremental == from_scratch,
        "{context}: incremental re-lex disagrees with a full re-lex\n  base={base:?}\n  \
         span={}..{} insert={insert:?}\n  after={:?}\n{}",
        span.start().0,
        span.end().0,
        after.as_str(),
        first_divergence(&incremental, &from_scratch)
    );
    assert_eq!(
        damage.total_events(),
        from_scratch.events.len(),
        "{context}: damage accounting does not add up to the run it produced"
    );
    damage
}

/// **THE PROPERTY**, over seeded random edit sequences on realistic bases.
///
/// Sequences rather than single edits, because the interesting failures are the ones where a
/// reused prefix from edit N is wrong by edit N+1. Each step feeds the *incremental* result
/// forward, so an error that survives one step compounds instead of being washed out by a
/// fresh full lex.
#[test]
fn an_incremental_relex_equals_a_full_relex_for_every_edit() {
    let table = table();
    let mut checked = 0usize;
    let mut reused_at_least_once = 0usize;

    for (base_index, base) in BASES.iter().enumerate() {
        for seed in 0..24u64 {
            let mut rng = Rng::new(seed * 1_000_003 + base_index as u64);
            let mut rope = Rope::from_utf8(base.as_bytes()).expect("valid base");
            let mut text = rope.source_text().clone();
            let mut run = lex_run(&text, &table);

            for step in 0..8 {
                let span = random_span(&mut rng, &text);
                let insert = random_insert(&mut rng);
                if rope.replace(span, &insert).is_err() {
                    continue;
                }
                let after = rope.source_text().clone();

                let (incremental, damage) =
                    relex_incremental(&run, span, insert.len(), &after, &table);
                let from_scratch = lex_run(&after, &table);

                assert!(
                    incremental == from_scratch,
                    "seed={seed} base={base_index} step={step}: incremental disagrees with full\
                     \n  span={}..{} insert={insert:?}\n  text={:?}\n{}",
                    span.start().0,
                    span.end().0,
                    after.as_str(),
                    first_divergence(&incremental, &from_scratch)
                );
                assert_eq!(
                    damage.total_events(),
                    from_scratch.events.len(),
                    "seed={seed} base={base_index} step={step}: damage accounting"
                );

                checked += 1;
                if damage.reused_anything() {
                    reused_at_least_once += 1;
                }
                run = incremental;
                text = after;
            }
        }
    }

    assert!(
        checked > 1_000,
        "only {checked} edits exercised the property"
    );
    // Anti-vacuity: if nothing were ever reused, the property above would hold trivially
    // because the "incremental" path would just be the full path wearing a different name.
    assert!(
        reused_at_least_once * 4 > checked,
        "reuse happened in only {reused_at_least_once} of {checked} edits — the incremental \
         path is not actually incremental"
    );
}

/// The lookahead cases that break a naive restart rule, each one hand-built so the failure is
/// legible rather than buried in a seed.
///
/// Every one of these is an edit whose effect reaches *backwards* past the event containing it.
#[test]
fn an_edit_can_change_a_decision_events_to_its_left() {
    let table = table();

    // The trie walks past what it emits. `<==x` emits `<`; turning the `x` into `>` makes the
    // whole thing one `<==>` token, three events to the left of the edit.
    let damage = check_one_edit(
        &table,
        "a <==x b",
        ByteSpan::new(BytePos(5), BytePos(6)).expect("span"),
        ">",
        "trie lookahead past the emitted token",
    );
    assert!(damage.total_events() > 0);

    // The raw-string opener is the lexer's one unbounded probe: `r###x` reads every `#` before
    // deciding. Turning the `x` into a quote makes five events into one.
    check_one_edit(
        &table,
        "a r###x b",
        ByteSpan::new(BytePos(6), BytePos(7)).expect("span"),
        "\"a\"###",
        "raw-string opener probe",
    );

    // The numeral's two-character `..` lookahead: `1..5` is `1` then `..`. Deleting one dot
    // makes `1.5`, a single scientific literal, changing the event at offset 0.
    check_one_edit(
        &table,
        "x 1..5 y",
        ByteSpan::new(BytePos(3), BytePos(4)).expect("span"),
        "",
        "numeral dot lookahead",
    );

    // A keyword's identity depends on what follows it: `in x` -> `intx` is one identifier.
    check_one_edit(
        &table,
        "in x",
        ByteSpan::new(BytePos(2), BytePos(3)).expect("span"),
        "t",
        "keyword extended into an identifier",
    );

    // Typing a second `-` turns two tokens into a line comment, swallowing the rest of the
    // line — the case that motivated attachment's plus-one, here at lexical scale.
    check_one_edit(
        &table,
        "a - b\nc",
        ByteSpan::new(BytePos(3), BytePos(3)).expect("span"),
        "-",
        "a dash becoming a line comment",
    );

    // And the reverse: deleting a `-` from `--` un-comments the rest of the line.
    check_one_edit(
        &table,
        "a -- b\nc",
        ByteSpan::new(BytePos(2), BytePos(3)).expect("span"),
        "",
        "un-commenting a line",
    );

    // Closing an unterminated block comment changes every event after it.
    check_one_edit(
        &table,
        "/- a\nb\nc",
        ByteSpan::new(BytePos(8), BytePos(8)).expect("span"),
        "-/",
        "terminating a block comment",
    );

    // Opening a string swallows the rest of the file.
    check_one_edit(
        &table,
        "a b c",
        ByteSpan::new(BytePos(2), BytePos(2)).expect("span"),
        "\"",
        "an opening quote swallowing the file",
    );
}

/// Boundedness, on the shape where it is easiest to state: a one-byte insertion at the end of
/// a long file must not re-lex the file.
///
/// This is the assertion that would catch a "correct" relexer that quietly redoes everything.
#[test]
fn a_small_edit_at_the_end_of_a_long_file_reuses_the_prefix() {
    let table = table();
    let mut base = String::new();
    for index in 0..200 {
        base.push_str(&format!("def f{index} := {index} + 1\n"));
    }
    let text = text_of(&base);
    let total = lex_run(&text, &table).events.len();
    assert!(total > 1_000, "the fixture needs to be big: {total} events");

    let at = BytePos(base.len());
    let damage = check_one_edit(
        &table,
        &base,
        ByteSpan::new(at, at).expect("span"),
        "x",
        "one byte appended to a long file",
    );

    assert!(
        damage.reused_prefix > total - 20,
        "appending one byte re-lexed {} of {total} events; the prefix should have been reused",
        damage.relexed
    );
    assert!(
        damage.relexed < 20,
        "appending one byte re-lexed {} events",
        damage.relexed
    );
}

/// An edit in the middle reuses on *both* sides. The suffix reuse is the half that needs the
/// offsets shifted, so it is the half where a stale diagnostic position would show up.
#[test]
fn an_edit_in_the_middle_reuses_a_shifted_suffix() {
    let table = table();
    let mut base = String::new();
    for index in 0..120 {
        base.push_str(&format!("def g{index} := \"s{index}\"\n"));
    }
    let midpoint = BytePos(common::boundary_at_or_before(
        &text_of(&base),
        base.len() / 2,
    ));
    let damage = check_one_edit(
        &table,
        &base,
        ByteSpan::new(midpoint, midpoint).expect("span"),
        " ",
        "one space inserted mid-file",
    );

    assert!(
        damage.reused_prefix > 0,
        "nothing before the edit was reused"
    );
    assert!(
        damage.reused_suffix > 0,
        "nothing after the edit was reused, so the shifted-suffix path is untested"
    );
}

/// A reused diagnostic must move with the text. If the suffix were spliced without shifting,
/// a refusal after the edit would point at the file the user had *before* it — the class of bug
/// that makes an editor underline the wrong character.
#[test]
fn a_reused_diagnostic_after_the_edit_moves_with_the_text() {
    let table = table();
    // A tab refusal near the end, and an insertion before it.
    let base = "def a := 1\ndef b :=\tc\n";
    let tab_at = base.find('\t').expect("fixture has a tab");
    let before = text_of(base);
    let old = lex_run(&before, &table);
    let old_tab = old
        .diagnostics()
        .iter()
        .find(|(message, _)| message.starts_with("tabs"))
        .map(|(_, at)| at.0)
        .expect("the base already refuses the tab");
    assert_eq!(old_tab, tab_at, "the refusal starts where the tab is");

    let insert = "xyz";
    let at = BytePos(4);
    check_one_edit(
        &table,
        base,
        ByteSpan::new(at, at).expect("span"),
        insert,
        "insertion before an existing refusal",
    );

    // And directly: the diagnostic offset moved by exactly the inserted length.
    let mut rope = Rope::from_utf8(base.as_bytes()).expect("valid base");
    rope.replace(ByteSpan::new(at, at).expect("span"), insert)
        .expect("in range");
    let after = rope.source_text().clone();
    let (incremental, _) = relex_incremental(
        &old,
        ByteSpan::new(at, at).expect("span"),
        insert.len(),
        &after,
        &table,
    );
    let new_tab = incremental
        .diagnostics()
        .iter()
        .find(|(message, _)| message.starts_with("tabs"))
        .map(|(_, at)| at.0)
        .expect("the refusal survives the edit");
    assert_eq!(
        new_tab,
        old_tab + insert.len(),
        "the tab refusal must point at the tab's NEW offset"
    );
}
