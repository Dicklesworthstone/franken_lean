//! `token_table_totality` — the token table is total, and its longest-match agrees with the
//! naive implementation (bead franken_lean-81oq).
//!
//! ## Why a differential and not examples
//!
//! `TokenTable::match_prefix` is a trie walk carrying the last value it saw. The obvious
//! alternative is to test it on hand-picked inputs — but the property it must have is
//! "returns the longest table token that is a prefix here", and that property has an
//! implementation so simple it needs no test of its own: check every token in the table,
//! keep the longest that matches. So the trie is checked against *that*, over generated
//! tables and generated inputs.
//!
//! This is the same discipline the incremental suite uses. A structure that exists only to be
//! fast is verified against the slow thing it replaced, because a bespoke test can only check
//! the cases its author thought of, and the trie's failure modes are precisely the ones an
//! author does not think of — a shared prefix with no token at the branch point, a token that
//! is a prefix of another, a walk that runs past the last match and has to fall back.
//!
//! ## Totality
//!
//! Every operation answers for every input: any offset including the end and interior bytes of
//! a multi-byte scalar, any token string including the empty one, any text including empty. The
//! table is consulted on arbitrary bytes long before anything has validated them as a program,
//! so a panic here is reached by every caller.

//! `max_token_len` gets its own assertions because the incremental lexer's restart bound is
//! derived from it: understate it and `relex_incremental` silently stops revisiting decisions
//! it must revisit. It is a lookahead bound masquerading as a convenience accessor.
//!
//! Its depth walk is also a totality boundary. Tokens are installed by user syntax
//! declarations, so one byte must not become one host-stack frame. Compiler-generated clone,
//! equality, debug, and drop glue traverse the same recursive representation, so the deep-token
//! regression exercises the table as a unit. It uses a bounded-stack thread in an isolated
//! child process, allowing the parent to report a depth-safety regression without losing the
//! rest of the test run (bead `franken_lean-36di`).

#![forbid(unsafe_code)]

mod common;

use common::Rng;
use fln_syntax::run::{lex_run, relex_incremental};
use fln_syntax::source::ByteSpan;
use fln_syntax::source::{BytePos, SourceText};
use fln_syntax::token::TokenTable;
use std::process::Command;

const DEEP_STACK_CHILD: &str = "FLN_TOKEN_TABLE_DEEP_STACK_CHILD";
const DEEP_TOKEN_BYTES: usize = 16 * 1024;
const DEEP_THREAD_STACK_BYTES: usize = 64 * 1024;

/// The naive implementation: try every token, keep the longest prefix match.
///
/// Deliberately as dumb as possible — a linear scan over a slice of strings, no shared state,
/// nothing to get wrong. Its only job is to be obviously correct.
fn naive_match_prefix<'a>(tokens: &[&'a str], text: &str, from: usize) -> Option<&'a str> {
    // Byte slicing, not `str` slicing: `from` may land inside a scalar, where `&text[from..]`
    // panics. The trie walks raw bytes and answers there, so the naive side has to reach the
    // same bytes or the two would not be comparable at every offset.
    let bytes = &text.as_bytes()[from.min(text.len())..];
    let mut best: Option<&str> = None;
    for token in tokens {
        if bytes.starts_with(token.as_bytes())
            && best.is_none_or(|current| token.len() > current.len())
        {
            best = Some(token);
        }
    }
    best
}

/// Token strings a generated table can be built from. Includes tokens that are prefixes of
/// other tokens, tokens sharing long prefixes, multi-byte tokens, and tokens that are also
/// valid identifiers — every shape that makes the trie's fallback matter.
const TOKENS: &[&str] = &[
    "<",
    "<=",
    "<==",
    "<==>",
    "=",
    "==",
    "=>",
    ":",
    ":=",
    "::",
    ".",
    "..",
    "...",
    "-",
    "--",
    "->",
    "/",
    "/-",
    "/--",
    "/-!",
    "(",
    ")",
    "def",
    "definition",
    "d",
    "in",
    "int",
    "instance",
    "λ",
    "→",
    "↔",
    "∀",
    "theorem",
    "the",
    "#",
    "##",
    "«",
    "»",
    "!",
    "?",
    "_",
];

fn table_of(tokens: &[&str]) -> TokenTable {
    TokenTable::from_tokens(tokens.iter().copied())
}

/// **THE DIFFERENTIAL.** The trie agrees with the naive longest-prefix scan, at every offset of
/// every generated input, for every generated table.
#[test]
fn the_trie_agrees_with_a_naive_longest_prefix_scan() {
    let mut comparisons = 0usize;
    let mut nonempty_answers = 0usize;

    for seed in 0..12_000u64 {
        let mut rng = Rng::new(seed);

        // A random subset of the token vocabulary, so the trie shape varies: sometimes a
        // branch point has a token, sometimes it does not.
        let count = 1 + rng.below(TOKENS.len());
        let mut chosen: Vec<&str> = Vec::new();
        for _ in 0..count {
            let token = *rng.pick(TOKENS);
            if !chosen.contains(&token) {
                chosen.push(token);
            }
        }
        let table = table_of(&chosen);

        // A random input built from the same alphabet, so matches actually happen — an input
        // of unrelated bytes would make the differential trivially agree on None.
        let pieces = 1 + rng.below(6);
        let mut raw = String::new();
        for _ in 0..pieces {
            raw.push_str(rng.pick(TOKENS));
            if rng.below(3) == 0 {
                raw.push_str(rng.pick(&["x", " ", "1", "😀", ""]));
            }
        }
        let text = SourceText::from_utf8(raw.as_bytes()).expect("built from valid UTF-8");

        for offset in 0..=raw.len() {
            let trie = table.match_prefix(&text, BytePos(offset));
            let naive = naive_match_prefix(&chosen, &raw, offset);
            assert_eq!(
                trie, naive,
                "seed={seed} offset={offset}: trie says {trie:?}, naive says {naive:?}\n  \
                 tokens={chosen:?}\n  input={raw:?}"
            );
            comparisons += 1;
            if trie.is_some() {
                nonempty_answers += 1;
            }
        }
    }

    assert!(comparisons > 100_000, "only {comparisons} comparisons");
    // Anti-vacuity: if every answer were None the differential would agree on nothing useful.
    assert!(
        nonempty_answers * 10 > comparisons,
        "only {nonempty_answers} of {comparisons} comparisons matched a token — the generated \
         inputs are not exercising the table"
    );
}

/// Longest match, not first match, stated directly against the shape that distinguishes them.
#[test]
fn the_answer_is_the_longest_match_not_the_first() {
    let table = table_of(&["<", "<=", "<==", "<==>"]);
    let cases = [
        ("<", Some("<")),
        ("<=", Some("<=")),
        ("<==", Some("<==")),
        ("<==>", Some("<==>")),
        ("<==>>", Some("<==>")),
        ("<=x", Some("<=")),
        ("<==x", Some("<==")),
        ("x", None),
        ("", None),
    ];
    for (raw, want) in cases {
        let text = SourceText::from_utf8(raw.as_bytes()).expect("valid");
        assert_eq!(table.match_prefix(&text, BytePos(0)), want, "input {raw:?}");
    }
}

/// A table is a **set** of tokens: the order they were inserted in cannot change what it
/// matches, or what it is.
///
/// Both directions, because only one of them is obvious. Insertion order must not matter —
/// and the *token strings themselves* must matter, so the test also shows that a table built
/// from a different set is a different table. An equality that held regardless would satisfy
/// the first assertion vacuously.
#[test]
fn insertion_order_does_not_change_the_table_but_the_token_set_does() {
    let forward = table_of(&["def", "definition", "d", "in", "int"]);
    let reversed = table_of(&["int", "in", "d", "definition", "def"]);
    let shuffled = table_of(&["in", "definition", "int", "def", "d"]);

    assert_eq!(forward, reversed, "insertion order must not matter");
    assert_eq!(forward, shuffled, "insertion order must not matter");

    // And the same answers, not merely the same structure.
    for raw in [
        "def",
        "definition",
        "defx",
        "d",
        "in",
        "int",
        "instance",
        "x",
    ] {
        let text = SourceText::from_utf8(raw.as_bytes()).expect("valid");
        let a = forward.match_prefix(&text, BytePos(0));
        let b = reversed.match_prefix(&text, BytePos(0));
        assert_eq!(
            a, b,
            "input {raw:?} answered differently by insertion order"
        );
    }

    // The other direction: content DOES matter, so the equality above is not vacuous.
    let different = table_of(&["def", "definition", "d", "in"]);
    assert_ne!(forward, different, "dropping a token must change the table");
    let text = SourceText::from_utf8(b"int").expect("valid");
    assert_eq!(forward.match_prefix(&text, BytePos(0)), Some("int"));
    assert_eq!(different.match_prefix(&text, BytePos(0)), Some("in"));
}

/// Duplicates are idempotent — a token is its own value, so inserting it twice cannot mean two
/// different things.
#[test]
fn inserting_a_token_twice_changes_nothing() {
    let once = table_of(&["fun", "in"]);
    let mut twice = TokenTable::new();
    for _ in 0..3 {
        twice.insert("fun");
        twice.insert("in");
    }
    assert_eq!(once, twice);
}

/// The empty token is refused, because a zero-length match would succeed everywhere and make
/// `isToken`'s length comparison — the whole keyword rule — vacuous.
#[test]
fn the_empty_token_is_refused_and_cannot_match() {
    let mut table = TokenTable::new();
    table.insert("");
    assert!(!table.contains(""));
    assert_eq!(table.max_token_len(), 0);
    for raw in ["", "x", "def"] {
        let text = SourceText::from_utf8(raw.as_bytes()).expect("valid");
        assert_eq!(
            table.match_prefix(&text, BytePos(0)),
            None,
            "an empty token must not match {raw:?}"
        );
    }
}

/// `max_token_len` is the lookahead bound the incremental restart is derived from, so it must
/// be the true maximum — understated, `relex_incremental` stops revisiting decisions it must.
#[test]
fn max_token_len_is_the_true_maximum_in_bytes() {
    assert_eq!(TokenTable::new().max_token_len(), 0);
    assert_eq!(table_of(&["a"]).max_token_len(), 1);
    assert_eq!(table_of(&["a", "abc", "ab"]).max_token_len(), 3);
    // Bytes, not characters: `→` is one char and three bytes, and the restart bound is in
    // bytes. Measuring characters here would understate the bound on every unicode token.
    assert_eq!(table_of(&["→"]).max_token_len(), 3);
    assert_eq!(table_of(&["λ", "abcd"]).max_token_len(), 4);
    assert_eq!(table_of(&["∀"]).max_token_len(), 3);

    // Over generated tables: never less than the longest token, and never more.
    for seed in 0..500u64 {
        let mut rng = Rng::new(seed ^ 0xAAAA);
        let count = 1 + rng.below(12);
        let chosen: Vec<&str> = (0..count).map(|_| *rng.pick(TOKENS)).collect();
        let expected = chosen.iter().map(|token| token.len()).max().unwrap_or(0);
        assert_eq!(
            table_of(&chosen).max_token_len(),
            expected,
            "seed={seed} tokens={chosen:?}"
        );
    }
}

/// The production incremental path can measure, use, clone, compare, render, and dispose a
/// user-controlled deep token without making trie depth host-stack depth.
///
/// The subprocess is load-bearing: host-stack exhaustion terminates the process rather than
/// unwinding to `join`, so running the bounded-stack discriminator in this test process would
/// make the regression incapable of reporting its own failure. The completion marker prevents
/// an accidentally misspelled `--exact` filter from turning zero executed child tests into
/// green.
#[test]
fn deep_token_operations_are_stack_safe() {
    if std::env::var_os(DEEP_STACK_CHILD).is_some() {
        std::thread::Builder::new()
            .name("fln-token-depth-discriminator".to_string())
            .stack_size(DEEP_THREAD_STACK_BYTES)
            .spawn(|| {
                let token = "<".repeat(DEEP_TOKEN_BYTES);
                let mut branch = "<".repeat(DEEP_TOKEN_BYTES - 1);
                branch.push('>');
                let table = TokenTable::from_tokens(["<", "→", token.as_str(), branch.as_str()]);

                assert_eq!(table.max_token_len(), DEEP_TOKEN_BYTES);
                assert!(table.contains(&token));
                assert!(table.contains(&branch));

                let old_raw = format!("{token} x");
                let old_text = SourceText::from_utf8(old_raw.as_bytes()).expect("valid old text");
                assert_eq!(
                    table.match_prefix(&old_text, BytePos(0)),
                    Some(token.as_str())
                );

                let cloned = table.clone();
                assert_eq!(cloned, table);
                let rendered = format!("{cloned:?}");
                assert!(rendered.starts_with("TokenTable"));
                assert!(rendered.len() >= token.len());

                let edited_at = token.len() + 1;
                let edited = ByteSpan::new(BytePos(edited_at), BytePos(edited_at + 1))
                    .expect("forward one-byte edit");
                let new_raw = format!("{token} y");
                let new_text = SourceText::from_utf8(new_raw.as_bytes()).expect("valid new text");
                let old_run = lex_run(&old_text, &table);
                let (incremental, _) = relex_incremental(&old_run, edited, 1, &new_text, &table);
                assert_eq!(incremental, lex_run(&new_text, &table));

                // Both tables drop on this deliberately small stack. This catches recursive
                // compiler-generated drop glue separately from the explicit depth walk.
                drop(cloned);
                drop(table);
            })
            .expect("small-stack discriminator thread starts")
            .join()
            .expect("deep-token operations complete on the bounded host stack");
        println!("fln-token-depth-child: pass bytes={DEEP_TOKEN_BYTES}");
        return;
    }

    let output = Command::new(std::env::current_exe().expect("current test executable"))
        .args([
            "--exact",
            "deep_token_operations_are_stack_safe",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(DEEP_STACK_CHILD, "1")
        .output()
        .expect("deep-token child process starts");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "deep-token child failed with {}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        output.status
    );
    assert!(
        stdout.contains("fln-token-depth-child: pass bytes=16384"),
        "deep-token child exited without executing the discriminator\nstdout:\n{stdout}\n\
         stderr:\n{stderr}"
    );
}

/// `contains` is exact: a prefix of a token is not a token, and an extension is not either.
#[test]
fn contains_is_exact_and_not_a_prefix_test() {
    let table = table_of(&["def", "definition", "→"]);
    for token in ["def", "definition", "→"] {
        assert!(table.contains(token), "{token:?} was inserted");
    }
    for absent in [
        "",
        "d",
        "de",
        "defi",
        "defin",
        "defs",
        "definitions",
        "→→",
        "x",
    ] {
        assert!(!table.contains(absent), "{absent:?} was never inserted");
    }
}

/// **Totality.** Every offset answers, including the end of the text and offsets *inside* a
/// multi-byte scalar.
///
/// Interior offsets are reachable in practice: the lexer's restart arithmetic and any caller
/// holding a stale position can land there, and the trie walks raw bytes, so it must answer
/// rather than panic. What it answers is unconstrained — a continuation byte matches no token
/// unless a token was spelled with one — but it must answer.
#[test]
fn every_offset_answers_including_inside_a_scalar_and_at_the_end() {
    let table = table_of(TOKENS);
    for raw in [
        "",
        "x",
        "😀",
        "→→→",
        "def 😀 <==>",
        "«odd»",
        "\u{0}\u{1}\u{7f}",
    ] {
        let text = SourceText::from_utf8(raw.as_bytes()).expect("valid");
        // Past the end too: one past, and far past.
        for offset in 0..=(raw.len() + 8) {
            let answer = table.match_prefix(&text, BytePos(offset));
            if let Some(token) = answer {
                assert!(
                    table.contains(token),
                    "{raw:?}@{offset}: answered with {token:?}, which is not in the table"
                );
                assert!(
                    offset + token.len() <= raw.len(),
                    "{raw:?}@{offset}: answered {token:?} which would run past the end"
                );
            }
        }
    }
}

/// Byte-keying and char-keying coincide for every token anyone can write, and this is where
/// that is checked rather than argued.
///
/// The trie is keyed by bytes because `Trie.matchPrefix` upstream walks `getUTF8Byte`. The
/// worry that invites is a token matching a *partial* scalar — but a token is a `&str`, and the
/// middle of a scalar is not valid UTF-8, so no such token can be spelled. What remains to
/// check is the behaviour at offsets that do land mid-scalar: the walk must simply fail to
/// match, not match something adjacent.
#[test]
fn byte_keying_matches_whole_scalars_and_nothing_mid_scalar() {
    let table = table_of(&["😀", "😀😀", "→"]);
    let text = SourceText::from_utf8("😀😀→x".as_bytes()).expect("valid");

    // Longest match wins across multi-byte tokens.
    assert_eq!(table.match_prefix(&text, BytePos(0)), Some("😀😀"));
    assert_eq!(table.match_prefix(&text, BytePos(4)), Some("😀"));
    assert_eq!(table.match_prefix(&text, BytePos(8)), Some("→"));

    // Every offset inside a scalar answers None: no token begins with a continuation byte,
    // because no token can be spelled with one.
    for offset in [1, 2, 3, 5, 6, 7, 9, 10] {
        assert_eq!(
            table.match_prefix(&text, BytePos(offset)),
            None,
            "offset {offset} is inside a scalar and must match nothing"
        );
    }
}
