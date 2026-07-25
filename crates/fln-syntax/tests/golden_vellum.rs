//! Byte-exact goldens for Vellum's green trees and token streams (bead pending; plan §9).
//!
//! How this suite composes with the other Vellum test mechanisms — and the measured gap
//! between them — is written up in `crates/fln-syntax/TESTING_COMPOSITION.md`. Read it before
//! adding a suite here: the two mechanisms do NOT back each other up in the direction one
//! would assume, and their blind spots overlap.
//!
//! ## No update mode, by construction
//!
//! These tests **never write** the corpus or its provenance. There is no `UPDATE_GOLDENS`
//! environment variable to set, because a golden that can regenerate its own expectation is not a
//! golden — it is a mirror. A tree-shape change must FAIL here and stay failed until a human reads
//! the diff and edits the corpus deliberately.
//!
//! The regeneration path is [`emit_corpus_for_review`], which is `#[ignore]`d and only ever prints
//! to stdout. A human runs it, reads what it produced, and pastes the rows in. That is the ceremony,
//! and it is the same one `fln-verdict`'s certificate goldens use.
//!
//! ## The golden is of the RECOVERABLE form, not the raw bytes
//!
//! Inherited from bead franken_lean-tkr2 and held literally. The lexer runs on the crlfToLf-
//! normalized *view*, so a tree reconstructs the **view**, and recovering the file is
//! `SourceView::reconstruct_original`'s job. A golden frozen against raw bytes would either fail on
//! every CRLF row or be quietly relaxed until it passed.
//!
//! So each row freezes **both** forms and the chain between them:
//!
//! ```text
//! raw_hex   the input bytes, CRLF and all
//! view_hex  the normalized bytes the lexer consumed and the tree reconstructs
//! tokens    the token stream, one entry per token, with view offsets
//! tree      the green tree's shape and spans
//! ```
//!
//! and the tests assert `tree.reconstruct(view) == view_hex` **and**
//! `view.reconstruct_original() == raw_hex`. Freezing only one form would leave the map untested;
//! freezing both makes the recoverability itself part of the artifact.
//!
//! ## Why hand-rolled and not `insta`
//!
//! The dependency universe is closed (D1): `std` plus the FrankenSuite. No snapshot crate, no regex
//! crate. The comparison is therefore a byte loop that reports the first differing offset, which is
//! what a reviewer needs anyway — "mismatch" is not a diff.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_syntax::attach::{TokenExtent, attach};
use fln_syntax::run::{Event, lex_run};
use fln_syntax::source::{ByteSpan, SourceInfo, SourceText};
use fln_syntax::token::{TokenKind, TokenTable};
use fln_syntax::tree::Syntax;
use fln_syntax::view::SourceView;

const CORPUS: &str = include_str!("corpus/vellum_goldens.hex");
const PROVENANCE: &str = include_str!("corpus/VELLUM_GOLDENS_PROVENANCE.md");
const PRODUCER: &str = "fln-syntax@0.0.0";
const LEXER_SCHEMA: &str = "fln.vellum.token-stream/1";
const TREE_SCHEMA: &str = "fln.vellum.green-tree/1";
const GOLDEN_ROWS: usize = 8;

/// The token table the goldens were produced with. Frozen here because the table is a *parameter*
/// of the lexer — the same source lexes differently under a different table, so a golden without
/// its table is not reproducible.
fn table() -> TokenTable {
    TokenTable::from_tokens([
        "def", "theorem", "fun", "=>", ":=", "+", "*", "(", ")", "λ", "→", "/--", "/-!",
    ])
}

/// The corpus inputs, by name. The raw bytes live here rather than in the golden file so a reviewer
/// can see what was fed in without decoding hex.
fn inputs() -> Vec<(&'static str, &'static str)> {
    vec![
        ("empty", ""),
        ("bare-ident", "x"),
        ("lf-simple", "def f := 1\n"),
        ("crlf-simple", "def f := 1\r\n"),
        ("crlf-two-lines", "def f := 1\r\ndef g := 2\r\n"),
        ("lone-cr-preserved", "def f := 1\rdef g := 2\n"),
        ("comment-and-trivia", "-- c\r\ndef f := (1 + 2)\r\n"),
        ("unicode-and-doc", "/-- d -/\ndef α := λ x => x\n"),
    ]
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    name: String,
    raw_hex: String,
    view_hex: String,
    tokens: String,
    tree: String,
    producer: String,
    producer_commit: String,
    lexer_schema: String,
    tree_schema: String,
}

/// Where two byte strings first differ — a reviewer needs the offset, not the word "mismatch".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mismatch {
    Byte { at: usize, expected: u8, actual: u8 },
    Length { expected: usize, actual: usize },
}

fn first_difference(expected: &[u8], actual: &[u8]) -> Option<Mismatch> {
    for (at, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
        if e != a {
            return Some(Mismatch::Byte {
                at,
                expected: *e,
                actual: *a,
            });
        }
    }
    if expected.len() != actual.len() {
        return Some(Mismatch::Length {
            expected: expected.len(),
            actual: actual.len(),
        });
    }
    None
}

fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn from_hex(text: &str) -> Vec<u8> {
    text.as_bytes()
        .chunks(2)
        .filter_map(|pair| {
            let hi = (pair[0] as char).to_digit(16)?;
            let lo = (*pair.get(1)? as char).to_digit(16)?;
            Some((hi * 16 + lo) as u8)
        })
        .collect()
}

/// What the lexer produced, rendered one token per entry with **view** offsets.
fn render_tokens(text: &SourceText, table: &TokenTable) -> String {
    let run = lex_run(text, table);
    let mut out = Vec::new();
    for event in &run.events {
        match event {
            Event::Token(token) => {
                let kind = match &token.kind {
                    TokenKind::Symbol(symbol) => format!("sym({symbol})"),
                    TokenKind::Ident(name) => format!("ident({})", name.to_display_string()),
                    TokenKind::Literal(kind) => format!("lit({kind:?})"),
                };
                out.push(format!(
                    "{}:{}..{}",
                    kind,
                    token.extent.start().0,
                    token.extent.end().0
                ));
            }
            Event::Refused { error, .. } => {
                out.push(format!("refused({}):{}", error.message(), error.at().0));
            }
            Event::Trivia(_) => {}
        }
    }
    out.join(" ")
}

/// The green tree's shape and spans, rendered so a shape change is a text change.
///
/// Includes each leaf's `pos..end_pos` and the byte length of its leading and trailing trivia, so a
/// misattachment shows up here even though it would not change a reconstruction.
fn render_tree(text: &SourceText, table: &TokenTable) -> (String, Option<Syntax>, ByteSpan) {
    let run = lex_run(text, table);
    let extents: Vec<TokenExtent> = run
        .token_extents()
        .into_iter()
        .map(TokenExtent::Present)
        .collect();
    let Ok(attachment) = attach(text, &extents) else {
        return (
            "<attach refused>".to_string(),
            None,
            ByteSpan::empty_at(fln_syntax::source::BytePos(0)),
        );
    };

    let leaves: Vec<Syntax> = attachment
        .entries()
        .iter()
        .zip(run.token_extents())
        .map(|(entry, extent)| match entry {
            fln_syntax::attach::Attached::Token(info) => {
                Syntax::atom(*info, format!("t{}", extent.start().0))
            }
            fln_syntax::attach::Attached::Missing { .. } => Syntax::Missing,
        })
        .collect();

    let tree = Syntax::node(Name::str(Name::anonymous(), "file"), leaves);
    let mut out = vec![format!("file[{}]", tree_child_count(&tree))];
    for leaf in tree_children(&tree) {
        match leaf.info() {
            SourceInfo::Original {
                leading,
                pos,
                trailing,
                end_pos,
            } => out.push(format!(
                "leaf {}..{} lead{} trail{}",
                pos.0,
                end_pos.0,
                leading.len_bytes(),
                trailing.len_bytes()
            )),
            other => out.push(format!("leaf {other:?}")),
        }
    }
    out.push(format!("epilogue{}", attachment.epilogue().len_bytes()));
    (out.join(" "), Some(tree), attachment.epilogue())
}

fn tree_children(tree: &Syntax) -> Vec<Syntax> {
    match tree {
        Syntax::Node { args, .. } => args.clone(),
        _ => Vec::new(),
    }
}

fn tree_child_count(tree: &Syntax) -> usize {
    tree_children(tree).len()
}

/// Produce the row for one input.
fn produce(name: &str, raw: &str, commit: &str) -> Row {
    let original = SourceText::from_utf8(raw.as_bytes()).expect("corpus inputs are valid UTF-8");
    let view = SourceView::of(&original);
    let table = table();
    let (tree, _, _) = render_tree(view.normalized(), &table);
    Row {
        name: name.to_string(),
        raw_hex: to_hex(raw.as_bytes()),
        view_hex: to_hex(view.normalized().as_bytes()),
        tokens: render_tokens(view.normalized(), &table),
        tree,
        producer: PRODUCER.to_string(),
        producer_commit: commit.to_string(),
        lexer_schema: LEXER_SCHEMA.to_string(),
        tree_schema: TREE_SCHEMA.to_string(),
    }
}

fn frozen_rows() -> Vec<Row> {
    CORPUS
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let f: Vec<&str> = line.split('|').collect();
            assert_eq!(
                f.len(),
                9,
                "a golden row has nine fields; found {} in {line:?}",
                f.len()
            );
            Row {
                name: f[0].to_string(),
                raw_hex: f[1].to_string(),
                view_hex: f[2].to_string(),
                tokens: f[3].to_string(),
                tree: f[4].to_string(),
                producer: f[5].to_string(),
                producer_commit: f[6].to_string(),
                lexer_schema: f[7].to_string(),
                tree_schema: f[8].to_string(),
            }
        })
        .collect()
}

/// **THE GOLDEN COMPARISON.** Every frozen row must be reproduced exactly.
///
/// No update path. A difference fails and keeps failing until a human edits the corpus.
#[test]
fn every_frozen_golden_is_reproduced_byte_for_byte() {
    let frozen = frozen_rows();
    assert_eq!(
        frozen.len(),
        GOLDEN_ROWS,
        "the corpus must hold exactly {GOLDEN_ROWS} reviewed rows"
    );

    for row in &frozen {
        let found = inputs().into_iter().find(|(name, _)| *name == row.name);
        assert!(
            found.is_some(),
            "frozen row {:?} has no matching input; the corpus has drifted from the input set",
            row.name
        );
        let (_, raw) = found.unwrap_or(("", ""));
        let produced = produce(&row.name, raw, &row.producer_commit);

        // The raw bytes, and the VIEW bytes — both frozen, because the recoverable form is what
        // losslessness is defined against.
        assert_eq!(
            first_difference(&from_hex(&row.raw_hex), &from_hex(&produced.raw_hex)),
            None,
            "{}: raw bytes differ from the golden",
            row.name
        );
        assert_eq!(
            first_difference(&from_hex(&row.view_hex), &from_hex(&produced.view_hex)),
            None,
            "{}: the normalized VIEW differs from the golden. The view is what the lexer consumed \
             and what the tree reconstructs, so this is the form losslessness is defined against.",
            row.name
        );
        assert_eq!(
            first_difference(row.tokens.as_bytes(), produced.tokens.as_bytes()),
            None,
            "{}: the TOKEN STREAM differs.\n  golden:   {}\n  produced: {}",
            row.name,
            row.tokens,
            produced.tokens
        );
        assert_eq!(
            first_difference(row.tree.as_bytes(), produced.tree.as_bytes()),
            None,
            "{}: the GREEN TREE SHAPE differs. This is the assertion that must never be quietly \
             regenerated.\n  golden:   {}\n  produced: {}",
            row.name,
            row.tree,
            produced.tree
        );
        assert_eq!(row.lexer_schema, LEXER_SCHEMA, "{}: lexer schema", row.name);
        assert_eq!(row.tree_schema, TREE_SCHEMA, "{}: tree schema", row.name);
        assert_eq!(row.producer, PRODUCER, "{}: producer", row.name);
    }
}

/// **THE RECOVERABILITY CHAIN**, frozen alongside the artifacts rather than assumed.
///
/// The tree reconstructs the VIEW; the view reconstructs the FILE. And for any row the view actually
/// normalized, the tree's reconstruction is asserted to DIFFER from the raw bytes — so a golden
/// frozen against raw bytes could not pass, which is what keeps tkr2's constraint from being
/// quietly relaxed.
#[test]
fn every_golden_row_recovers_its_file_through_the_map() {
    let mut normalized_rows = 0usize;
    for row in frozen_rows() {
        let (_, raw) = inputs()
            .into_iter()
            .find(|(name, _)| *name == row.name)
            .expect("row has an input");
        let original = SourceText::from_utf8(raw.as_bytes()).expect("valid");
        let view = SourceView::of(&original);
        let table = table();
        let (_, tree, epilogue) = render_tree(view.normalized(), &table);

        assert_eq!(
            view.reconstruct_original(),
            raw.as_bytes(),
            "{}: the view must recover the file",
            row.name
        );
        if let Some(tree) = tree {
            let reconstructed = tree
                .reconstruct(view.normalized(), epilogue)
                .unwrap_or_default();
            assert_eq!(
                first_difference(view.normalized().as_bytes(), &reconstructed),
                None,
                "{}: the tree must reconstruct the view",
                row.name
            );
            if view.normalized_anything() {
                normalized_rows += 1;
                assert_ne!(
                    reconstructed,
                    raw.as_bytes(),
                    "{}: this row WAS normalized, so the tree's reconstruction must differ from the \
                     raw bytes. A golden frozen against raw bytes would be wrong here.",
                    row.name
                );
            }
        }
    }
    assert!(
        normalized_rows >= 3,
        "only {normalized_rows} rows exercise the crlfToLf map; the corpus needs CRLF inputs or \
         the recoverability half is untested"
    );
}

/// **The golden FAILS on a tree-shape change.** Demonstrated, not asserted in prose.
///
/// A shape change is simulated by perturbing the produced rendering — one leaf's trivia length —
/// and confirming the comparison rejects it. Without this the suite could be a mirror and nobody
/// would know.
#[test]
fn a_changed_tree_shape_fails_the_comparison() {
    let row = frozen_rows()
        .into_iter()
        .find(|row| row.name == "crlf-two-lines")
        .expect("the corpus has a CRLF row");

    // Perturb exactly one character of the frozen shape, the way a real attachment change would.
    let mut perturbed = row.tree.clone();
    let at = perturbed
        .find("lead0")
        .expect("the row has a zero-length leading trivia to perturb");
    perturbed.replace_range(at..at + 5, "lead9");

    assert_ne!(perturbed, row.tree, "the perturbation must change the text");
    assert!(
        first_difference(row.tree.as_bytes(), perturbed.as_bytes()).is_some(),
        "a changed tree shape MUST be reported as a difference. If this passed, the golden would \
         accept any shape and the suite would be decorative."
    );

    // And the mismatch names the offset, which is what a reviewer needs.
    let difference = first_difference(row.tree.as_bytes(), perturbed.as_bytes());
    assert!(
        matches!(difference, Some(Mismatch::Byte { at, .. }) if at > 0),
        "the mismatch must name a byte offset, which is what a reviewer needs: {difference:?}"
    );
}

/// The provenance document exists, names the producer and the ceremony, and states that the tests
/// never write it. A golden suite without recorded provenance cannot be reproduced once it goes
/// stale.
#[test]
fn the_provenance_document_records_what_a_reviewer_needs() {
    for required in [
        "no update mode",
        PRODUCER,
        LEXER_SCHEMA,
        TREE_SCHEMA,
        "crlfToLf",
        "recoverable",
    ] {
        assert!(
            PROVENANCE.contains(required),
            "the provenance must mention {required:?}"
        );
    }
    // Every frozen row is named in the provenance table, so a reviewer can see the set at a glance.
    for row in frozen_rows() {
        assert!(
            PROVENANCE.contains(&row.name),
            "row {:?} is not listed in the provenance",
            row.name
        );
    }
}

/// Every input has a frozen row and every frozen row has an input — a corpus that drifted from its
/// inputs would silently stop testing whatever fell out.
#[test]
fn the_corpus_and_the_input_set_agree() {
    let frozen: Vec<String> = frozen_rows().into_iter().map(|row| row.name).collect();
    let declared: Vec<String> = inputs()
        .into_iter()
        .map(|(name, _)| name.to_string())
        .collect();
    assert_eq!(frozen.len(), declared.len(), "row count vs input count");
    for name in &declared {
        assert!(frozen.contains(name), "input {name:?} has no frozen row");
    }
    for name in &frozen {
        assert!(declared.contains(name), "frozen row {name:?} has no input");
    }
}

/// The regeneration ceremony. `#[ignore]`d, and it **only prints** — it never writes the corpus or
/// the provenance.
///
/// Run it deliberately, read what it produced, and paste the rows in by hand:
///
/// ```text
/// cargo test -p fln-syntax --test golden_vellum -- --ignored --nocapture emit_corpus
/// ```
///
/// Printing rather than writing is the whole point. A suite that can rewrite its own expectation
/// will eventually do so on a run nobody read, and the first bug it accepts will be invisible.
#[test]
#[ignore = "regeneration ceremony: prints rows for a human to review and paste"]
fn emit_corpus_for_review() {
    println!("# Frozen Vellum goldens. Tests compile this file in and never rewrite it.");
    println!("# Provenance and the reviewed change ceremony live in VELLUM_GOLDENS_PROVENANCE.md.");
    println!(
        "# fields: name|raw_hex|view_hex|tokens|tree|producer|producer_commit|lexer_schema|tree_schema"
    );
    let commit = std::env::var("GOLDEN_COMMIT").unwrap_or_else(|_| "UNSET".to_string());
    for (name, raw) in inputs() {
        let row = produce(name, raw, &commit);
        println!(
            "{}|{}|{}|{}|{}|{}|{}|{}|{}",
            row.name,
            row.raw_hex,
            row.view_hex,
            row.tokens,
            row.tree,
            row.producer,
            row.producer_commit,
            row.lexer_schema,
            row.tree_schema
        );
    }
}
