//! Suite `typed_normalizer_model` (bead `fln-1dxv`; plan §18).
//!
//! Every normalizer obligation from the epic, discharged as a checked property
//! rather than a sentence in a doc comment:
//!
//! | obligation | test |
//! |---|---|
//! | total | `normalizing_arbitrary_bytes_never_panics_and_always_yields_utf8` |
//! | bounded | `output_never_exceeds_the_budget` |
//! | deterministic | `normalization_is_deterministic_across_repeated_calls` |
//! | idempotent | `normalization_is_idempotent_on_adversarial_input`, `idempotence_survives_every_clamp_boundary` |
//! | versioned | `values_from_different_normalizer_versions_refuse_to_compare` |
//! | preserves distinct semantic errors | `distinct_semantic_errors_stay_distinct` |
//! | preserves ordered diagnostics | `a_diagnostic_sequence_keeps_its_order_length_and_duplicates` |
//! | non-expanding | `output_is_never_longer_than_input`, `ten_thousand_short_tokens_cannot_inflate_the_output` |
//!
//! Idempotence and non-expansion are the two most likely to be quietly false, so
//! neither is asserted on a hand-picked example. Both run against a deterministic
//! adversarial generator, and idempotence additionally gets a full boundary
//! sweep over clamp positions — the lesson from `crates/fln-rt/tests/region_fuzz.rs`
//! is that uniform random sampling does not reach a boundary that enumeration
//! walks straight into.
//!
//! # Mutants planted and killed
//!
//! | mutant | edit | killed by |
//! |---|---|---|
//! | normalizer expansion past budget | `hex-address` rule `min_match: 8` → `3` | `output_is_never_longer_than_input`, `ten_thousand_short_tokens_cannot_inflate_the_output`, `output_never_exceeds_the_budget` |
//! | an error normalized away | `rewrite`'s valid-UTF-8 arm emits one `?` instead of copying the sequence | `distinct_semantic_errors_stay_distinct`, `a_truncated_multibyte_sequence_costs_one_byte_per_bad_byte` |
//!
//! The two are killed by disjoint sets, which is the point. The expansion
//! mutant is perfectly idempotent and preserves every semantic distinction; it
//! measured `40000 bytes in, 70000 bytes out` and nothing else noticed. The
//! erasure mutant is perfectly bounded and non-expanding; it collapsed
//! `expected a ≠ b` and `expected a ≤ b` — two different Lean errors — into one
//! normalized string, and only the corpus noticed.
//!
//! The erasure mutant additionally broke idempotence, which was not predicted
//! and is worth recording: [`Normalizer::clamp`] appends the truncation marker
//! *after* the rewrite, so the marker must be a fixed point of the rewrite, and
//! the marker contains a multi-byte character. That invariant was only
//! incidentally true, so it is now stated outright by
//! `normalize::structural::the_marker_and_every_placeholder_are_fixed_points_of_normalization`.
//!
//! [`Normalizer::clamp`]: fln_epoch_lab::normalize::Normalizer

#![forbid(unsafe_code)]

use fln_epoch_lab::normalize::{
    CompareError, DEFAULT_BUDGET, Normalizer, NormalizerId, NormalizerVersion, TRUNCATION_MARKER,
    compare,
};
use fln_epoch_lab::oracle::ComparisonClass;

// ---------------------------------------------------------------------------
// A deterministic generator. No clock, no entropy: a failing run is replayable
// from the seed printed in the assertion.
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            return 0;
        }
        (self.next_u64() % n as u64) as usize
    }
}

/// Fragments chosen to attack the normalizer where it is weakest: short tokens
/// that a naive rule would expand, tokens that sit one byte either side of a
/// rule's minimum, bytes that are not valid UTF-8, sequences truncated
/// mid-character, and text that already looks like the normalizer's own output.
fn fragment(rng: &mut Rng, out: &mut Vec<u8>) {
    match rng.below(16) {
        // Just below and just above the hex rule's minimum.
        0 => out.extend_from_slice(b"0x1"),
        1 => out.extend_from_slice(b"0xab"),
        2 => out.extend_from_slice(b"0xdead"),
        3 => out.extend_from_slice(b"0xdeadbeef"),
        // Paths of every length around the minimum.
        4 => out.extend_from_slice(b"/a"),
        5 => out.extend_from_slice(b"/a/b/c/d"),
        6 => out.extend_from_slice(b"/home/ubuntu/.elan/toolchains/x/lib/lean/Init.olean"),
        7 => {
            let n = rng.below(40);
            out.extend(std::iter::repeat_n(b'/', n));
        }
        // Durations and pids either side of their minimums.
        8 => out.extend_from_slice(b"7ms"),
        9 => out.extend_from_slice(b"4500ms"),
        10 => out.extend_from_slice(b"pid=7"),
        11 => out.extend_from_slice(b"pid=31337"),
        // The normalizer's own output, fed back in.
        12 => out.extend_from_slice(b"<ADDR><PATH><TIME><PID>"),
        13 => out.extend_from_slice(TRUNCATION_MARKER.as_bytes()),
        // Invalid UTF-8, and a multi-byte sequence cut short.
        14 => {
            let n = 1 + rng.below(6);
            for _ in 0..n {
                out.push(0x80u8.wrapping_add((rng.below(0x60)) as u8));
            }
        }
        // Real Lean diagnostic text, Unicode included.
        _ => {
            let bits: [&str; 6] = [
                "error: type mismatch\n  expected a ≠ b\n",
                "error: unknown identifier 'Nat.succ_le_of_lt'\n",
                "error: unsolved goals\n⊢ ∀ n : ℕ, n ≤ n\n",
                " warning: declaration uses 'sorry'\n",
                "\u{0}\u{1}\u{7f}",
                "λ x ↦ x",
            ];
            out.extend_from_slice(bits[rng.below(bits.len())].as_bytes());
        }
    }
}

fn adversarial(rng: &mut Rng, max_fragments: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let n = rng.below(max_fragments);
    for _ in 0..n {
        fragment(rng, &mut out);
    }
    out
}

// ---------------------------------------------------------------------------
// Totality, boundedness, determinism
// ---------------------------------------------------------------------------

#[test]
fn normalizing_arbitrary_bytes_never_panics_and_always_yields_utf8() {
    let n = Normalizer::default();
    // Every single byte on its own, including the ones that start no valid
    // UTF-8 sequence.
    for b in 0u8..=255 {
        let out = n.normalize(&[b]);
        assert!(out.text.len() <= 1, "byte {b:#04x} expanded");
    }
    // Every two-byte pair of lead/continuation shapes.
    for lead in [0xC2u8, 0xDF, 0xE0, 0xEF, 0xF0, 0xF4, 0xF5, 0xFF, 0x80] {
        for tail in [0x00u8, 0x7F, 0x80, 0xBF, 0xC0, 0xFF] {
            let out = n.normalize(&[lead, tail]);
            assert!(out.text.len() <= 2);
        }
    }
    // The empty input, and a large hostile one.
    assert!(n.normalize(b"").text.is_empty());
    let mut rng = Rng(0x5EED_0001);
    for _ in 0..500 {
        let input = adversarial(&mut rng, 60);
        let out = n.normalize(&input);
        // `text` being a String is the totality receipt: the function returned,
        // and what it returned is valid UTF-8 whatever went in.
        assert!(out.text.is_char_boundary(out.text.len()));
    }
}

#[test]
fn a_truncated_multibyte_sequence_costs_one_byte_per_bad_byte() {
    // The specific expansion hazard this design exists to avoid: lossy UTF-8
    // conversion turns one invalid byte into U+FFFD, three bytes, and an
    // adversary controls how many invalid bytes to send.
    let n = Normalizer::default();
    for bad in [
        vec![0xE2u8, 0x89],           // "≠" cut short
        vec![0xF0, 0x9F, 0x92],       // 4-byte sequence cut short
        vec![0xFF, 0xFE, 0xFD],       // never valid at all
        vec![0x80, 0x80, 0x80, 0x80], // bare continuations
    ] {
        let out = n.normalize(&bad);
        assert!(
            out.text.len() == bad.len(),
            "{bad:?} became {} bytes",
            out.text.len()
        );
        assert!(out.text.bytes().all(|b| b == b'?'));
    }
    // A complete sequence is copied verbatim, not substituted.
    assert_eq!(n.normalize("≠".as_bytes()).text, "≠");
}

#[test]
fn output_never_exceeds_the_budget() {
    let mut rng = Rng(0x5EED_0002);
    for budget in [
        TRUNCATION_MARKER.len(),
        TRUNCATION_MARKER.len() + 1,
        32,
        64,
        DEFAULT_BUDGET,
    ] {
        let n = Normalizer::with_budget(budget);
        for _ in 0..400 {
            let input = adversarial(&mut rng, 80);
            let out = n.normalize(&input);
            assert!(
                out.text.len() <= budget,
                "budget {budget} exceeded: {} bytes from {} in",
                out.text.len(),
                input.len()
            );
            // A clamp is always announced in the text, and never happens to an
            // input that already fitted — a silent clamp is a lost diagnostic.
            if out.truncated {
                assert!(out.text.ends_with(TRUNCATION_MARKER), "silent clamp");
                assert!(input.len() > budget, "clamped an input that fitted");
            }
        }
    }
}

#[test]
fn normalization_is_deterministic_across_repeated_calls() {
    let n = Normalizer::default();
    let mut rng = Rng(0x5EED_0003);
    for _ in 0..500 {
        let input = adversarial(&mut rng, 50);
        let a = n.normalize(&input);
        let b = n.normalize(&input);
        let c = Normalizer::default().normalize(&input);
        assert!(a == b && b == c, "nondeterministic on {input:?}");
    }
}

// ---------------------------------------------------------------------------
// Non-expansion
// ---------------------------------------------------------------------------

#[test]
fn output_is_never_longer_than_input() {
    // Stated on the rewrite alone, with a budget far above anything generated,
    // so that the clamp cannot mask an expanding rule.
    let n = Normalizer::with_budget(1 << 20);
    let mut rng = Rng(0x5EED_0004);
    for i in 0..4000 {
        let input = adversarial(&mut rng, 40);
        let out = n.normalize(&input);
        assert!(
            out.text.len() <= input.len(),
            "case {i}: {} bytes in, {} bytes out\n  input: {:?}\n  output: {:?}",
            input.len(),
            out.text.len(),
            String::from_utf8_lossy(&input),
            out.text
        );
    }
}

#[test]
fn ten_thousand_short_tokens_cannot_inflate_the_output() {
    // The adversary's best move against a naive rewriter: pay three bytes per
    // token, receive six. Ten thousand of them would double a 30 KB input.
    let n = Normalizer::with_budget(1 << 20);
    let mut input = Vec::new();
    for _ in 0..10_000 {
        input.extend_from_slice(b"0x1 ");
    }
    let out = n.normalize(&input);
    assert!(
        out.text.len() <= input.len(),
        "{} bytes in, {} bytes out",
        input.len(),
        out.text.len()
    );
    // And the short tokens are left ALONE rather than rewritten, because a
    // three-byte hex literal is a number in a diagnostic, not an address.
    assert!(!out.text.contains("<ADDR>"));
    assert!(out.text.starts_with("0x1 0x1"));
}

#[test]
fn a_long_address_is_still_normalized() {
    // The non-expansion guard must not have been bought by disabling the rules.
    let n = Normalizer::default();
    assert_eq!(
        n.normalize(b"at 0xdeadbeef12 in frame").text,
        "at <ADDR> in frame"
    );
    assert_eq!(
        n.normalize(b"reading /home/ubuntu/x/Init.olean now").text,
        "reading <PATH> now"
    );
    assert_eq!(n.normalize(b"took 4500ms").text, "took <TIME>");
    assert_eq!(n.normalize(b"pid=31337 died").text, "<PID> died");
}

// ---------------------------------------------------------------------------
// Idempotence
// ---------------------------------------------------------------------------

#[test]
fn normalization_is_idempotent_on_adversarial_input() {
    for (seed, budget) in [
        (0x5EED_0005u64, 1usize << 20),
        (0x5EED_0006, DEFAULT_BUDGET),
        (0x5EED_0007, 48),
        (0x5EED_0008, TRUNCATION_MARKER.len() + 2),
    ] {
        let n = Normalizer::with_budget(budget);
        let mut rng = Rng(seed);
        for i in 0..1500 {
            let input = adversarial(&mut rng, 40);
            let once = n.normalize(&input);
            let twice = n.normalize(once.text.as_bytes());
            assert!(
                twice.text == once.text,
                "seed {seed:#x} budget {budget} case {i}: not idempotent\n  \
                 once:  {:?}\n  twice: {:?}",
                once.text,
                twice.text
            );
        }
    }
}

#[test]
fn idempotence_survives_every_clamp_boundary() {
    // The region_fuzz lesson: uniform sampling does not land on the one byte
    // offset where a clamp cuts a placeholder or a multi-byte character in
    // half. Enumeration does. Sweep every budget across a crafted input whose
    // rewritten form has placeholders, Unicode, and raw text interleaved, so
    // the cut lands inside each of them in turn.
    let source =
        b"a\xE2\x89\xA0b 0xdeadbeef12 /home/ubuntu/x/Init.olean 4500ms pid=31337 \xE2\x8A\xA2 tail";
    let mut cuts_inside_placeholder = 0usize;
    let mut cuts_inside_multibyte = 0usize;
    for budget in TRUNCATION_MARKER.len()..(source.len() + 8) {
        let n = Normalizer::with_budget(budget);
        let once = n.normalize(source);
        let twice = n.normalize(once.text.as_bytes());
        assert!(
            twice.text == once.text,
            "budget {budget}: not idempotent\n  once:  {:?}\n  twice: {:?}",
            once.text,
            twice.text
        );
        assert!(once.text.len() <= budget, "budget {budget} exceeded");
        // Re-normalizing an already-clamped text clamps nothing further. This
        // pins the documented scope of idempotence: it is a property of the
        // TEXT, and `truncated` records what happened to a particular input.
        if once.truncated {
            assert!(
                !twice.truncated,
                "budget {budget}: re-normalizing a clamped text clamped again"
            );
        }
        let body = once
            .text
            .strip_suffix(TRUNCATION_MARKER)
            .unwrap_or(&once.text);
        for p in ["<ADDR>", "<PATH>", "<TIME>", "<PID>"] {
            for k in 1..p.len() {
                if body.ends_with(&p[..k]) {
                    cuts_inside_placeholder += 1;
                }
            }
        }
        if once.truncated && !body.is_empty() && !body.is_ascii() {
            cuts_inside_multibyte += 1;
        }
    }
    // Coverage is reported as a number, not asserted as a feeling: if a rewrite
    // to the rule table stops the sweep from reaching these boundaries, this
    // test stops being evidence and says so.
    assert!(
        cuts_inside_placeholder > 0,
        "the sweep never cut inside a placeholder; it is no longer covering the boundary"
    );
    assert!(
        cuts_inside_multibyte > 0,
        "the sweep never clamped a body containing multi-byte text"
    );
}

// ---------------------------------------------------------------------------
// Error preservation and ordering
// ---------------------------------------------------------------------------

/// One semantic error kind, with several volatile renderings of it. Everything
/// that differs between renderings is noise a normalizer is *supposed* to erase;
/// everything that differs between kinds is signal it must not.
struct ErrorKind {
    name: &'static str,
    renderings: &'static [&'static str],
}

const ERROR_CORPUS: &[ErrorKind] = &[
    ErrorKind {
        name: "type-mismatch-neq",
        renderings: &[
            "/home/ubuntu/build/A.lean:12:5: error: type mismatch, expected a ≠ b [0xdeadbeef12]",
            "/tmp/fln-run-9/A.lean:12:5: error: type mismatch, expected a ≠ b [0xfeedface99]",
            "/var/lib/ci/w3/A.lean:12:5: error: type mismatch, expected a ≠ b [0x0011223344]",
        ],
    },
    ErrorKind {
        name: "type-mismatch-leq",
        renderings: &[
            "/home/ubuntu/build/A.lean:12:5: error: type mismatch, expected a ≤ b [0xdeadbeef12]",
            "/tmp/fln-run-9/A.lean:12:5: error: type mismatch, expected a ≤ b [0xfeedface99]",
        ],
    },
    ErrorKind {
        name: "unknown-identifier",
        renderings: &[
            "/home/ubuntu/build/A.lean:3:1: error: unknown identifier 'Nat.succ_le_of_lt' pid=31337",
            "/tmp/fln-run-9/A.lean:3:1: error: unknown identifier 'Nat.succ_le_of_lt' pid=42",
        ],
    },
    ErrorKind {
        name: "unknown-constant",
        renderings: &[
            "/home/ubuntu/build/A.lean:3:1: error: unknown constant 'Nat.succ_le_of_lt' pid=31337",
            "/tmp/fln-run-9/A.lean:3:1: error: unknown constant 'Nat.succ_le_of_lt' pid=42",
        ],
    },
    ErrorKind {
        name: "unsolved-goals",
        renderings: &[
            "/home/ubuntu/build/A.lean:7:2: error: unsolved goals\n⊢ ∀ n : ℕ, n ≤ n (4500ms)",
            "/tmp/fln-run-9/A.lean:7:2: error: unsolved goals\n⊢ ∀ n : ℕ, n ≤ n (9912ms)",
        ],
    },
    ErrorKind {
        name: "deterministic-timeout",
        renderings: &[
            "/home/ubuntu/build/A.lean:7:2: error: (deterministic) timeout at 'whnf' (4500ms)",
            "/tmp/fln-run-9/A.lean:7:2: error: (deterministic) timeout at 'whnf' (9912ms)",
        ],
    },
    ErrorKind {
        name: "sorry-warning",
        renderings: &[
            "/home/ubuntu/build/A.lean:9:0: warning: declaration uses 'sorry' pid=31337",
            "/tmp/fln-run-9/A.lean:9:0: warning: declaration uses 'sorry' pid=42",
        ],
    },
];

#[test]
fn volatile_decoration_within_one_error_kind_is_erased() {
    let n = Normalizer::default();
    for kind in ERROR_CORPUS {
        let first = n.normalize(kind.renderings[0].as_bytes()).text;
        for r in kind.renderings {
            assert_eq!(
                n.normalize(r.as_bytes()).text,
                first,
                "{}: two renderings of one error did not converge\n  {r:?}",
                kind.name
            );
        }
    }
}

#[test]
fn distinct_semantic_errors_stay_distinct() {
    // The other half, and the one that catches over-eager normalization. Note
    // `type-mismatch-neq` vs `type-mismatch-leq`: they differ in exactly one
    // multi-byte character, so a normalizer that folds Unicode down to a byte
    // erases a real distinction while remaining perfectly bounded and perfectly
    // idempotent. Likewise unknown-identifier vs unknown-constant, which are
    // different Lean errors one word apart.
    let n = Normalizer::default();
    let mut normalized: Vec<(&str, String)> = Vec::new();
    for kind in ERROR_CORPUS {
        for r in kind.renderings {
            normalized.push((kind.name, n.normalize(r.as_bytes()).text));
        }
    }
    for (a_name, a_text) in &normalized {
        for (b_name, b_text) in &normalized {
            if a_name != b_name {
                assert!(
                    a_text != b_text,
                    "{a_name} and {b_name} normalized to the same text: {a_text:?}"
                );
            }
        }
    }
}

#[test]
fn a_diagnostic_sequence_keeps_its_order_length_and_duplicates() {
    // Diagnostic order is semantic: the Reference emits errors in source order,
    // and a rig that sorts or deduplicates them is comparing a different object
    // than the one it names.
    let n = Normalizer::default();
    let seq: Vec<&[u8]> = vec![
        b"error: c",
        b"error: a",
        b"error: b",
        b"error: a",
        b"error: a",
    ];
    let out = n.normalize_all(&seq);
    assert_eq!(out.len(), seq.len(), "length changed");
    let texts: Vec<&str> = out.iter().map(|d| d.text.as_str()).collect();
    assert_eq!(
        texts,
        vec!["error: c", "error: a", "error: b", "error: a", "error: a"],
        "the sequence was reordered or deduplicated"
    );
    // Index-wise correspondence with the single-input function.
    for (i, item) in seq.iter().enumerate() {
        assert_eq!(out[i].text, n.normalize(item).text, "index {i} drifted");
    }
    assert!(n.normalize_all(&[]).is_empty());
}

// ---------------------------------------------------------------------------
// Versioning
// ---------------------------------------------------------------------------

#[test]
fn values_from_different_normalizer_versions_refuse_to_compare() {
    // The teeth on "versioned". Without a refusal, a version field is something
    // nobody reads, and a rule-table change silently reinterprets every
    // normalized value ever recorded.
    let n = Normalizer::default();
    let mut a = n.normalize(b"error: x");
    let b = n.normalize(b"error: x");
    assert_eq!(
        compare(&a, &b, ComparisonClass::NormalizedIdentical),
        Ok(true)
    );

    a.version = NormalizerVersion(a.version.0 + 1);
    match compare(&a, &b, ComparisonClass::NormalizedIdentical) {
        Err(CompareError::NormalizerMismatch { left, right }) => {
            assert!(left.1 != right.1);
            assert_eq!(left.0, NormalizerId::DiagnosticText);
        }
        other => panic!("a cross-version comparison returned {other:?}"),
    }
}

#[test]
fn an_acceptance_only_comparison_does_not_pretend_to_have_read_the_text() {
    // Vacuously true by design: the class says the diagnostic was not part of
    // the comparison, so reporting a text difference under it would be a claim
    // about something that was never checked.
    let n = Normalizer::default();
    let a = n.normalize(b"error: entirely different");
    let b = n.normalize(b"error: also different");
    assert_eq!(compare(&a, &b, ComparisonClass::AcceptanceOnly), Ok(true));
    assert_eq!(
        compare(&a, &b, ComparisonClass::NormalizedIdentical),
        Ok(false)
    );
    assert_eq!(compare(&a, &b, ComparisonClass::ByteIdentical), Ok(false));
}
