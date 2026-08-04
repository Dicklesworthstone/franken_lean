//! Metamorphic laws for Vellum (plan §18 "Metamorphic laws"; bead pending).
//!
//! How this suite composes with the other Vellum test mechanisms — and the measured gap
//! between them — is written up in `crates/fln-syntax/TESTING_COMPOSITION.md`. Read it before
//! adding a suite here: the two mechanisms do NOT back each other up in the direction one
//! would assume, and their blind spots overlap.
//!
//! ## What these establish, and what they do not
//!
//! **These are self-differentials.** Every law compares my parser to my parser under a
//! transformation of the input. They establish *internal consistency*, not fidelity to the
//! Reference. A metamorphic suite passing does not make a rule right — only stable. If the lexer
//! attaches trivia by a rule the pin does not use, every law below still holds, because both sides
//! of each comparison use the same wrong rule.
//!
//! Graded accordingly on the bead. Fidelity comes from elsewhere: `token_table_totality`'s
//! differential against a naive scan, `pratt_precedence_model`'s comparison against values the
//! pinned binary printed, and the pin observations recorded across franken_lean-81oq, fln-ffam and
//! fln-okfb. This suite is the stability layer on top of those, not a substitute for them.
//!
//! ## Why the laws are exact rather than statistical
//!
//! A parser is unusual among metamorphic subjects: there is no epsilon. "The parse is preserved"
//! means the token stream is identical in kind and order, not mostly identical. So every assertion
//! here is an equality, and any tolerance would be hiding a defect.
//!
//! ## The MR strength matrix
//!
//! | MR | Category | Fault sensitivity | Independence | Cost | Score |
//! |---|---|---|---|---|---|
//! | MR1 churn preserves the parse modulo trivia | equivalence | 5 | 5 | 1 | 25 |
//! | MR2 churn moves attachment only at the edit | equivalence | 5 | 4 | 1 | 20 |
//! | MR3 independent reordering preserves the result | permutative | 4 | 5 | 1 | 20 |
//! | MR4 alpha-renaming preserves structure | equivalence | 4 | 4 | 1 | 16 |
//! | MR5 churn is invertible byte-exactly | invertive | 3 | 3 | 1 | 9 |
//! | MR6 churn ∘ rename (composite) | equivalence | 5 | 3 | 1 | 15 |
//!
//! MR1 and MR2 are scored separately on purpose and are **not** redundant: MR1 is about the token
//! stream, MR2 about trivia ownership, and bead franken_lean-tkr2 measured that a misattachment is
//! invisible to a stream comparison. Collapsing them would lose the second entirely.

#![forbid(unsafe_code)]

use fln_syntax::attach::{Attached, TokenExtent, attach};
use fln_syntax::run::{Event, lex_run};
use fln_syntax::source::{SourceInfo, SourceText};
use fln_syntax::token::{TokenKind, TokenTable};
use fln_syntax::view::SourceView;

fn table() -> TokenTable {
    TokenTable::from_tokens([
        "def", "theorem", "fun", "=>", ":=", "+", "*", "(", ")", "λ", "→", "/--", "/-!",
    ])
}

/// The token stream **modulo trivia and offsets**: kind and spelling only.
///
/// Offsets are excluded deliberately — inserting a comment shifts every later token, so a law
/// stated over offsets would be false for the very transformation it is meant to test. What must be
/// preserved is the sequence of tokens, not where they sit.
fn stream_modulo_trivia(raw: &str) -> Vec<String> {
    let original = SourceText::from_utf8(raw.as_bytes()).expect("valid UTF-8");
    let view = SourceView::of(&original);
    lex_run(view.normalized(), &table())
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Token(token) => Some(match &token.kind {
                TokenKind::Symbol(symbol) => format!("sym:{symbol}"),
                TokenKind::Ident(name) => format!("ident:{}", name.to_display_string()),
                TokenKind::Literal(kind) => format!("lit:{kind:?}"),
            }),
            Event::Refused { error, .. } => Some(format!("refused:{}", error.message())),
            Event::Trivia(_) => None,
        })
        .collect()
}

/// The same, with identifier names erased — structure up to renaming.
fn stream_modulo_names(raw: &str) -> Vec<String> {
    stream_modulo_trivia(raw)
        .into_iter()
        .map(|entry| {
            if entry.starts_with("ident:") {
                "ident:_".to_string()
            } else {
                entry
            }
        })
        .collect()
}

/// Trivia ownership per token: (leading length, trailing length), in token order.
fn attachment_shape(raw: &str) -> Vec<(usize, usize)> {
    let original = SourceText::from_utf8(raw.as_bytes()).expect("valid UTF-8");
    let view = SourceView::of(&original);
    let text = view.normalized();
    let run = lex_run(text, &table());
    let extents: Vec<TokenExtent> = run
        .token_extents()
        .into_iter()
        .map(TokenExtent::Present)
        .collect();
    let Ok(attachment) = attach(text, &extents) else {
        return Vec::new();
    };
    attachment
        .entries()
        .iter()
        .map(|entry| match entry {
            Attached::Token(SourceInfo::Original {
                leading, trailing, ..
            }) => (leading.len_bytes(), trailing.len_bytes()),
            _ => (usize::MAX, usize::MAX),
        })
        .collect()
}

/// The corpus. Includes every input the goldens freeze — see
/// [`the_metamorphic_corpus_covers_every_golden_input`] for why that matters.
fn corpus() -> Vec<&'static str> {
    vec![
        "def f := 1\n",
        "def f := 1\r\n",
        "def f := 1\r\ndef g := 2\r\n",
        "def f := 1\rdef g := 2\n",
        "-- c\r\ndef f := (1 + 2)\r\n",
        "/-- d -/\ndef α := λ x => x\n",
        "def f := 1\ndef g := 2\ndef h := 3\n",
        "def outer := fun x => (x + 1) * 2\n",
        "x",
    ]
}

/// Whitespace and comment insertions the laws must tolerate. Each is trivia by the pin's rules.
///
/// **No tabs.** My first version included `"\t\t"` and MR1 failed on it — correctly. A tab in
/// trivia position is a lexical REFUSAL carrying the pin's wording, not neutral whitespace
/// (bead franken_lean-81oq), so inserting one genuinely changes the parse. The law was right and the
/// churn set was wrong; the validation test below asserts the tab refusal explicitly so the
/// exclusion is a recorded fact rather than a gap.
const CHURN: &[&str] = &[
    " ",
    "  ",
    "-- inserted\n",
    "/- block -/",
    "/- a /- nested -/ -/",
    "\n",
    "\n\n",
];

/// Insert `churn` after the first newline, which is a trivia position in every corpus entry that
/// has one — chosen rather than a random offset so the transformation is guaranteed valid rather
/// than accidentally splitting a token.
fn churn_after_first_line(raw: &str, churn: &str) -> Option<String> {
    let at = raw.find('\n')? + 1;
    let mut out = String::with_capacity(raw.len() + churn.len());
    out.push_str(&raw[..at]);
    out.push_str(churn);
    out.push_str(&raw[at..]);
    Some(out)
}

/// **MR1 (equivalence).** Comment and whitespace churn preserves the parse modulo trivia.
///
/// Not "mostly" — the token stream is *identical* in kind and order. A parser is unusual among
/// metamorphic subjects in having no epsilon available, so any tolerance here would be hiding a
/// defect rather than accommodating one.
#[test]
fn mr1_comment_and_whitespace_churn_preserves_the_parse() {
    let mut checked = 0usize;
    for raw in corpus() {
        let before = stream_modulo_trivia(raw);
        for churn in CHURN {
            let Some(churned) = churn_after_first_line(raw, churn) else {
                continue;
            };
            let after = stream_modulo_trivia(&churned);
            assert_eq!(
                before, after,
                "churn {churn:?} changed the token stream\n  input={raw:?}\n  churned={churned:?}"
            );
            checked += 1;
        }
    }
    assert!(checked > 40, "only {checked} churn cases exercised");
}

/// **MR2 (equivalence).** Churn moves trivia attachment **only where the edit is**.
///
/// Scored separately from MR1 and not redundant with it: bead franken_lean-tkr2 measured that a
/// misattachment reconstructs the file perfectly and is invisible to a stream comparison. MR1 would
/// pass for a lexer that reassigned every token's trivia on every edit.
///
/// The bound is the one tkr2 proved — damage is *overlapped, plus at most one*. Stated here as: the
/// attachment shape is unchanged except within a bounded window around the edit, and unchanged
/// entirely before it.
#[test]
fn mr2_churn_moves_attachment_only_where_the_edit_is() {
    let mut checked = 0usize;
    let mut windows = Vec::new();
    for raw in corpus() {
        let before = attachment_shape(raw);
        if before.len() < 3 {
            continue;
        }
        for churn in CHURN {
            let Some(churned) = churn_after_first_line(raw, churn) else {
                continue;
            };
            let after = attachment_shape(&churned);
            assert_eq!(
                before.len(),
                after.len(),
                "churn {churn:?} changed the TOKEN COUNT, so MR1 should have caught it first"
            );

            let differing: Vec<usize> = (0..before.len())
                .filter(|index| before[*index] != after[*index])
                .collect();

            // NOTE, and this was a premise error of mine that MR2 caught: I first asserted that
            // index 0 is never affected, on the grounds that the edit lands after the first newline
            // and the first token precedes it. That is false for an input whose first line is a
            // comment — there the edit lands exactly at the first TOKEN's leading trivia, so index 0
            // legitimately changes. The real bound is about the WIDTH of the damaged window, not
            // about which index it starts at, so that is what is asserted.

            // The differing set is a bounded window, not a suffix.
            if let (Some(first), Some(last)) = (differing.first(), differing.last()) {
                let width = last - first + 1;
                assert!(
                    width <= 3,
                    "churn {churn:?} spread attachment damage across {width} entries \
                     ({differing:?}); tkr2's bound is overlapped plus at most one\n  input={raw:?}"
                );
                windows.push(width);
            }
            checked += 1;
        }
    }
    assert!(checked > 20, "only {checked} attachment cases exercised");
    assert!(
        !windows.is_empty(),
        "no churn changed attachment at all, so the bound is untested — the corpus needs inputs \
         where inserted trivia actually changes ownership"
    );
}

/// **MR3 (permutative).** Reordering independent declarations preserves the result.
///
/// At Vellum's level "the result" is the per-declaration token subsequences: the parser has no
/// environment, so the honest statement of the plan's law here is that reordering permutes the
/// output the same way it permuted the input, and loses nothing. The environment-level form belongs
/// to fln-env.
#[test]
fn mr3_reordering_independent_declarations_permutes_the_result() {
    // Three independent declarations, split on lines so a swap is well defined.
    let decls = ["def f := 1", "def g := 2", "def h := 3"];
    let joined = |order: &[usize]| -> String {
        let mut out = String::new();
        for index in order {
            out.push_str(decls[*index]);
            out.push('\n');
        }
        out
    };

    let base = joined(&[0, 1, 2]);
    let base_stream = stream_modulo_trivia(&base);

    // Every permutation must yield the base stream permuted the same way — checked by comparing
    // per-declaration slices rather than the whole stream, since the whole stream is order
    // sensitive by construction.
    let per_decl: Vec<Vec<String>> = decls
        .iter()
        .map(|decl| stream_modulo_trivia(&format!("{decl}\n")))
        .collect();

    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let permuted = joined(&order);
        let stream = stream_modulo_trivia(&permuted);

        let expected: Vec<String> = order
            .iter()
            .flat_map(|index| per_decl[*index].clone())
            .collect();
        assert_eq!(
            stream, expected,
            "reordering to {order:?} did not permute the result correspondingly"
        );
        // And nothing is lost: the multiset is invariant.
        let mut sorted_stream = stream.clone();
        let mut sorted_base = base_stream.clone();
        sorted_stream.sort();
        sorted_base.sort();
        assert_eq!(
            sorted_stream, sorted_base,
            "reordering to {order:?} changed the multiset of tokens"
        );
    }
}

/// **MR4 (equivalence).** Alpha-renaming preserves structure up to the renaming.
///
/// The token stream with identifier names erased is invariant, and the renamed positions are
/// *exactly* the positions that changed — so a rename that also perturbed the shape would fail even
/// though the erased streams matched.
#[test]
fn mr4_alpha_renaming_preserves_structure_up_to_the_renaming() {
    let cases = [
        ("def f := fun x => x + 1\n", "x", "renamed"),
        ("def f := fun x => (x * x)\n", "x", "y"),
        ("def α := λ x => x\n", "x", "β"),
        ("def f := 1\ndef g := 2\n", "g", "gg"),
    ];
    for (raw, from, to) in cases {
        let renamed = raw.replace(from, to);
        assert_ne!(renamed, raw, "the fixture must actually rename something");

        assert_eq!(
            stream_modulo_names(raw),
            stream_modulo_names(&renamed),
            "renaming {from:?} to {to:?} changed the STRUCTURE, not just the names\n  input={raw:?}"
        );

        // And the names differ in exactly the renamed positions — so this is a rename, not a
        // coincidence of two structurally similar programs.
        let before = stream_modulo_trivia(raw);
        let after = stream_modulo_trivia(&renamed);
        assert_eq!(before.len(), after.len());
        let changed: Vec<usize> = (0..before.len())
            .filter(|index| before[*index] != after[*index])
            .collect();
        assert!(
            !changed.is_empty(),
            "the rename changed no token at all, so the law is vacuous here"
        );
        for index in changed {
            assert!(
                before[index].starts_with("ident:") && after[index].starts_with("ident:"),
                "renaming changed a NON-identifier token at {index}: {:?} -> {:?}",
                before[index],
                after[index]
            );
        }
    }
}

/// **MR5 (invertive).** Churn is byte-exactly invertible, so the law is about the transformation
/// and not about the corpus happening to be churn-insensitive.
#[test]
fn mr5_removing_the_inserted_churn_restores_the_exact_stream() {
    for raw in corpus() {
        for churn in CHURN {
            let Some(churned) = churn_after_first_line(raw, churn) else {
                continue;
            };
            // Remove exactly what was inserted, at the position it was inserted.
            let at = raw.find('\n').expect("has a newline") + 1;
            let mut restored = String::new();
            restored.push_str(&churned[..at]);
            restored.push_str(&churned[at + churn.len()..]);
            assert_eq!(
                restored, raw,
                "un-churning must restore the exact input for churn {churn:?}"
            );
            assert_eq!(
                stream_modulo_trivia(&restored),
                stream_modulo_trivia(raw),
                "and the stream with it"
            );
        }
    }
}

/// **MR6 (composite: MR1 ∘ MR4).** Churn and renaming together preserve structure.
///
/// Composition is where metamorphic power multiplies: a defect that only manifests when trivia has
/// shifted *and* an identifier has changed length is invisible to either law alone.
#[test]
fn mr6_churn_composed_with_renaming_preserves_structure() {
    let mut actually_renamed = 0usize;
    for raw in corpus() {
        let structure = stream_modulo_names(raw);
        for churn in CHURN {
            let Some(churned) = churn_after_first_line(raw, churn) else {
                continue;
            };
            // Rename after churning, deliberately to a LONGER name so offsets move again.
            //
            // `x` and not `f`: my first version renamed `f`, which is a SUBSTRING of the keyword
            // `def`, so the transformation silently rewrote keywords and the law failed. It was
            // right to fail. No keyword in this table contains `x`, so this rename touches only
            // identifiers — the same substring trap that bit the fixtures in fln-ffam slice D.
            let both = churned.replace('x', "xLonger");
            assert_eq!(
                stream_modulo_names(&both),
                structure,
                "churn {churn:?} composed with renaming changed the structure\n  input={raw:?}"
            );
            if both != churned {
                actually_renamed += 1;
            }
        }
    }
    assert!(
        actually_renamed > 10,
        "only {actually_renamed} composite cases actually renamed anything; a no-op rename makes \
         the composition vacuous"
    );
}

/// **MR VALIDATION.** The suite catches planted transformations that a correct parser must reject.
///
/// The skill's rule: an MR suite nobody has shown to detect anything is a suite of opinions. These
/// are *invalid* transformations — ones that genuinely change the program — and each must be caught
/// by at least one law above, or that law is too weak.
#[test]
fn the_laws_reject_transformations_that_actually_change_the_program() {
    let raw = "def f := 1 + 2\n";
    let base_stream = stream_modulo_trivia(raw);
    let base_structure = stream_modulo_names(raw);

    // Not trivia: removing a token changes the parse, and MR1 must see it.
    let token_removed = raw.replace(" + 2", "");
    assert_ne!(
        stream_modulo_trivia(&token_removed),
        base_stream,
        "removing a token must change the stream, or MR1 is too weak"
    );

    // Not trivia: a tab in trivia position is a REFUSAL, not whitespace. This is why CHURN contains
    // no tabs at all — my first version did, and MR1 failed on it correctly.
    let illegal = "def\tf := 1\n";
    assert_ne!(
        stream_modulo_trivia(illegal),
        base_stream,
        "a tab is a lexical refusal, not neutral whitespace"
    );
    assert!(
        stream_modulo_trivia(illegal)
            .iter()
            .any(|entry| entry.starts_with("refused:")),
        "and it must appear as a refusal"
    );

    // Renaming a KEYWORD is not alpha-renaming — it changes the structure, and MR4 must reject it.
    let keyword_renamed = raw.replace("def", "theorem");
    assert_ne!(
        stream_modulo_names(&keyword_renamed),
        base_structure,
        "renaming a keyword changes the structure, so MR4 must not tolerate it"
    );

    // Reordering DEPENDENT lines is outside MR3's premise; asserted so the premise is explicit.
    let dependent = "def f := 1\ndef g := f\n";
    let swapped = "def g := f\ndef f := 1\n";
    assert_eq!(
        stream_modulo_names(dependent).len(),
        stream_modulo_names(swapped).len(),
        "the parser is order-insensitive at the token level even for dependent decls; MR3's \
         independence premise is about the ENVIRONMENT, which is fln-env's law, not Vellum's"
    );
}

/// **COMPOSITION WITH THE GOLDENS — and it is ONE-WAY, which I measured rather than assumed.**
///
/// I planted one real change in `chooseNiceTrailStop` (trailing trivia stopping at CR instead of
/// newline) and ran both suites:
///
/// ```text
/// golden_vellum        FAILED
/// metamorphic_vellum   ok
/// ```
///
/// So the laws in this file are **blind** to that change, and the goldens caught it. The reason is
/// the defining limitation of a metamorphic law: the change is *uniform*. It alters attachment the
/// same way on both sides of every comparison, so "churn preserves the parse" remains true — of a
/// different attachment rule. A self-differential cannot see a change to the rule it is comparing
/// against itself.
///
/// The useful conclusion is that the two suites are complementary in one direction only:
/// * the GOLDENS catch uniform rule changes, which these laws cannot;
/// * these LAWS catch input-dependent inconsistency, which a fixed golden corpus would miss on any
///   input it does not contain.
///
/// Neither subsumes the other, and the naive expectation — "a metamorphic failure will surface as a
/// golden mismatch" — is the wrong way round. It is the golden failure that surfaces first, and
/// there is no quiet drift only because the goldens have no update mode.
///
/// What this test still does, and it is worth keeping: it makes the *shared input set* structural,
/// so the laws are at least exercised on everything the goldens freeze. Read from the frozen corpus
/// at test time rather than kept in step by hand, so adding a golden row without adding it here
/// fails immediately.
#[test]
fn the_metamorphic_corpus_covers_every_golden_input() {
    const GOLDENS: &str = include_str!("corpus/vellum_goldens.hex");
    let mine = corpus();
    let mut checked = 0usize;

    for line in GOLDENS.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('|').collect();
        let (name, raw_hex) = (fields[0], fields[1]);
        // Decode the frozen raw bytes and look for that exact input in this suite's corpus.
        let bytes: Vec<u8> = raw_hex
            .as_bytes()
            .chunks(2)
            .filter_map(|pair| {
                let hi = (pair[0] as char).to_digit(16)?;
                let lo = (*pair.get(1)? as char).to_digit(16)?;
                Some((hi * 16 + lo) as u8)
            })
            .collect();
        let raw = String::from_utf8(bytes).expect("golden inputs are valid UTF-8");
        if raw.is_empty() {
            // The `empty` row has no tokens and no trivia to churn; excluded by construction and
            // named here so the exclusion is deliberate rather than an oversight.
            continue;
        }
        assert!(
            mine.contains(&raw.as_str()),
            "golden row {name:?} has input {raw:?}, which the metamorphic corpus does not cover. \
             The laws must at least be exercised on everything the goldens freeze; see this \
             test's doc comment for why the two suites are complementary rather than nested."
        );
        checked += 1;
    }
    assert!(checked >= 7, "only {checked} golden inputs cross-checked");
}
