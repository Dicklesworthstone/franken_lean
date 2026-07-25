//! `parse_roundtrip_property` — a constructed tree reproduces the file, through the crlfToLf map
//! (bead fln-ffam).
//!
//! ## The chain, and why it is not byte-equality with the raw input
//!
//! Inherited literally from franken_lean-tkr2: **lossless means recoverable through the map**, not
//! byte-equal to the raw file. The lexer runs on the normalized view, so a tree's reconstruction
//! reproduces the *view*; recovering the file is `SourceView::reconstruct_original`'s job. The
//! asserted chain is
//!
//! ```text
//! raw -> view -> lex -> attach -> build leaves -> tree
//!     -> tree.reconstruct(view)  == view bytes
//!     -> view.reconstruct_original() == raw bytes
//! ```
//!
//! and for any input the view actually normalized, the direct raw comparison is asserted to
//! **fail**. Without that half, a suite written against raw bytes either breaks on every CRLF file
//! or gets quietly relaxed until it passes, and neither outcome tells a reader the map is
//! load-bearing.
//!
//! ## What this property does NOT establish
//!
//! Stated here because slice D measured it rather than argued it: **the round trip cannot see a
//! rebuilt span.** Spans recomputed from a consumption cursor are internally consistent, tile the
//! file, and reproduce every byte, so this suite is green with the caret on the wrong side of every
//! token. The exactness assertion below — each leaf against the lexer's own extents — is what
//! catches that, and it is included here rather than left to the unit tests so the property suite
//! is not the weakest evidence in the bead.

#![forbid(unsafe_code)]

mod common;

use common::{Rng, generate, table, text_of};
use fln_core::name::Name;
use fln_parse::build::{Leaves, node};
use fln_syntax::run::{Event, lex_run};
use fln_syntax::source::SourceInfo;
use fln_syntax::view::SourceView;

/// Lex through the view and build, returning everything the assertions need.
fn build(raw: &str) -> Option<(SourceView, Vec<fln_syntax::token::LexedToken>, Leaves)> {
    let original = text_of(raw)?;
    let view = SourceView::of(&original);
    let run = lex_run(view.normalized(), &table());
    let tokens: Vec<_> = run
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Token(token) => Some(token.clone()),
            _ => None,
        })
        .collect();
    let leaves = Leaves::build(view.normalized(), &tokens).ok()?;
    Some((view, tokens, leaves))
}

/// **THE PROPERTY**, over a seeded corpus: the tree reconstructs the view, the view reconstructs
/// the file, and for a normalized file the raw comparison fails.
#[test]
fn every_constructed_tree_reconstructs_its_file_through_the_map() {
    let mut checked = 0usize;
    let mut normalized_seen = 0usize;
    let mut with_tokens = 0usize;

    for seed in 0..6_000u64 {
        let mut rng = Rng::new(seed);
        let raw = generate(&mut rng);
        let Some((view, tokens, leaves)) = build(&raw) else {
            continue;
        };

        let tree = node(Name::str(Name::anonymous(), "file"), leaves.all().to_vec());
        let reconstructed = tree.reconstruct(view.normalized(), leaves.attachment().epilogue());

        assert!(
            reconstructed.is_some(),
            "seed={seed}: the tree failed to reconstruct the view it was built from\n  raw={raw:?}"
        );
        let view_bytes = reconstructed.unwrap_or_default();
        assert_eq!(
            view_bytes,
            view.normalized().as_bytes(),
            "seed={seed}: the tree must reproduce the VIEW byte for byte\n  raw={raw:?}"
        );
        assert_eq!(
            view.reconstruct_original(),
            raw.as_bytes(),
            "seed={seed}: the view must reproduce the FILE byte for byte\n  raw={raw:?}"
        );

        if view.normalized_anything() {
            normalized_seen += 1;
            assert_ne!(
                view_bytes,
                raw.as_bytes(),
                "seed={seed}: this input WAS normalized, so the tree's reconstruction must differ \
                 from the raw bytes. Equal here would mean the map does nothing and the property \
                 proves nothing.\n  raw={raw:?}"
            );
        }
        if !tokens.is_empty() {
            with_tokens += 1;
        }
        checked += 1;
    }

    assert!(checked > 4_000, "only {checked} inputs round-tripped");
    // Anti-vacuity, both kinds: the corpus must contain files that were normalized (or the
    // map-is-load-bearing half never runs) and files with actual tokens (or every tree is empty).
    assert!(
        normalized_seen > 200,
        "only {normalized_seen} of {checked} inputs were normalized; the CRLF half is barely tested"
    );
    assert!(
        with_tokens > 3_000,
        "only {with_tokens} of {checked} inputs produced tokens; the trees are mostly empty"
    );
}

/// **Exactness under the same corpus.** Every leaf carries the lexer's extent.
///
/// Included in the property suite deliberately: the round trip above is green for rebuilt spans, as
/// slice D measured, so without this the strongest-looking suite in the bead would be its weakest
/// evidence.
#[test]
fn every_leaf_in_the_corpus_carries_the_lexers_extent() {
    let mut leaves_checked = 0usize;
    for seed in 0..6_000u64 {
        let mut rng = Rng::new(seed ^ 0x5EED);
        let raw = generate(&mut rng);
        let Some((_, tokens, leaves)) = build(&raw) else {
            continue;
        };
        for (index, token) in tokens.iter().enumerate() {
            let info = leaves.leaf(index).expect("leaf").info();
            let SourceInfo::Original { pos, end_pos, .. } = info else {
                // Reported as a comparison rather than a panic, matching the lexer suites.
                assert_eq!(
                    format!("{info:?}"),
                    "Original",
                    "seed={seed}: leaf {index} must carry Original source info\n  raw={raw:?}"
                );
                continue;
            };
            assert_eq!(
                (pos, end_pos),
                (token.extent.start(), token.extent.end()),
                "seed={seed}: leaf {index} must carry the lexer's extent\n  raw={raw:?}"
            );
            leaves_checked += 1;
        }
    }
    assert!(
        leaves_checked > 10_000,
        "only {leaves_checked} leaves checked; the corpus is not producing tokens"
    );
}

/// The corpus contains CRLF inputs whose view and file offsets genuinely differ, and a leaf's
/// position maps back onto the right raw byte. This is the case the map exists for.
#[test]
fn leaf_positions_map_back_onto_the_original_bytes() {
    let mut diverged = 0usize;
    for seed in 0..3_000u64 {
        let mut rng = Rng::new(seed ^ 0xC12F);
        let raw = generate(&mut rng);
        let Some((view, tokens, leaves)) = build(&raw) else {
            continue;
        };
        if !view.normalized_anything() {
            continue;
        }
        for index in 0..tokens.len() {
            let SourceInfo::Original { pos, .. } = leaves.leaf(index).expect("leaf").info() else {
                continue;
            };
            let in_file = view.to_original(pos);
            assert!(
                in_file.0 <= raw.len(),
                "seed={seed}: a mapped position must be inside the file"
            );
            // The mapped position must land on the same byte the view position sees.
            let view_byte = view.normalized().as_bytes().get(pos.0).copied();
            let file_byte = raw.as_bytes().get(in_file.0).copied();
            if let (Some(a), Some(b)) = (view_byte, file_byte) {
                assert_eq!(
                    a, b,
                    "seed={seed}: leaf {index} view byte and mapped file byte must agree\n  raw={raw:?}"
                );
            }
            if in_file.0 != pos.0 {
                diverged += 1;
            }
        }
    }
    assert!(
        diverged > 50,
        "only {diverged} positions actually diverged between view and file; the mapping is \
         barely exercised, so this suite would pass on an identity map"
    );
}
