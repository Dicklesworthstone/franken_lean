//! The typed normalizer model — diagnostic normalization stated as provable
//! properties rather than prose (bead `fln-1dxv`; plan §18).
//!
//! # The obligations
//!
//! A normalizer that the Tribunal may use for a [`ComparisonClass::NormalizedIdentical`]
//! comparison must be:
//!
//! | obligation | where it is discharged |
//! |---|---|
//! | **total** — defined on every byte string, including invalid UTF-8 | [`Normalizer::normalize`] takes `&[u8]`, returns a value, and has no panicking path |
//! | **bounded** — output never exceeds a declared budget | [`Normalizer::budget`], enforced by clamping |
//! | **deterministic** — same input, same output, always | no clock, no allocator address, no map iteration order |
//! | **idempotent** — `f(f(x)) == f(x)` on the text | property-tested, see the scope note below |
//! | **versioned** — outputs from different normalizers are not comparable | [`Normalized`] carries id+version; [`compare`] refuses a mismatch |
//! | **error-preserving** — distinct semantic errors stay distinct | corpus test over kinds × renderings |
//! | **order-preserving** — a diagnostic sequence keeps its order | [`Normalizer::normalize_all`] is index-wise |
//! | **non-expanding** — adversarial input cannot grow past the budget | true by construction (see below) AND property-tested |
//!
//! Idempotence and non-expansion are the two most likely to be quietly false,
//! so neither is asserted here; both are property-tested against adversarial
//! generators in `tests/typed_normalizer_model.rs`.
//!
//! # Why non-expansion is true by construction
//!
//! The obvious way to write a normalizer expands. Rewriting `0x1` to `<ADDR>`
//! doubles it, and an adversary who sends ten thousand three-byte tokens gets an
//! output twice the size of the input it paid for. Two structural rules remove
//! the hazard rather than clamping it after the fact:
//!
//! 1. **Every rule declares a minimum match length ≥ its placeholder length**,
//!    the scanner refuses a shorter match, and [`RULES`] is checked for that
//!    property by a test. So every individual rewrite is non-expanding.
//! 2. **Invalid UTF-8 is replaced byte-for-byte with `?`**, not with the
//!    replacement character. `String::from_utf8_lossy` turns one bad byte into
//!    three (U+FFFD), which is an expansion of exactly the kind an adversary
//!    controls; a one-byte substitute is not.
//!
//! With both, `output.len() <= input.len()` before the budget is consulted at
//! all, so the budget bites only on inputs that were already over it.
//!
//! # Why idempotence is true by construction
//!
//! Rules are prefix-anchored maximal munches over a byte class with a minimum
//! length, so truncating a suffix can only *shorten* a candidate match, never
//! create one. Placeholders contain no byte that starts a rule. Therefore a
//! second pass over a normalized string finds nothing left to rewrite, including
//! over the ragged edge left by clamping.
//!
//! **Scope note.** Idempotence is a property of the normalized *text*.
//! [`Normalized::truncated`] deliberately does not participate: it records what
//! happened to the input that produced this value, and re-normalizing an
//! already-clamped text truncates nothing, so the flag is `false` the second
//! time. That is correct and is pinned by a test, so that nobody later "fixes"
//! the flag into stickiness and quietly turns it into a comparison field.
//!
//! [`ComparisonClass::NormalizedIdentical`]: crate::oracle::ComparisonClass::NormalizedIdentical

use crate::oracle::ComparisonClass;

/// Which normalizer produced a value. A closed vocabulary, separate from every
/// other vocabulary in [`crate::oracle`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NormalizerId {
    /// Oracle diagnostic text: volatile spans out, semantics in.
    DiagnosticText,
}

impl NormalizerId {
    pub fn as_str(self) -> &'static str {
        match self {
            NormalizerId::DiagnosticText => "diagnostic-text",
        }
    }
}

/// The normalizer's version. Bumped whenever the rule table changes in a way
/// that could move an output — which makes previously recorded normalized
/// values incomparable rather than silently reinterpreted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NormalizerVersion(pub u32);

/// The current diagnostic-text normalizer version.
pub const DIAGNOSTIC_TEXT_V1: NormalizerVersion = NormalizerVersion(1);

/// Default output budget in bytes.
pub const DEFAULT_BUDGET: usize = 4096;

/// Appended when the budget clamps an output. Chosen to contain no byte that
/// starts a rule, so a second pass leaves it alone.
pub const TRUNCATION_MARKER: &str = "…[truncated]";

/// One rewrite rule.
pub struct Rule {
    /// Stable name, used in the structural tests and in failure output.
    pub name: &'static str,
    /// What the matched span becomes.
    pub placeholder: &'static str,
    /// Shortest span this rule will rewrite. MUST be ≥ `placeholder.len()`;
    /// the scanner enforces it at runtime and a test enforces the relation.
    pub min_match: usize,
    /// Maximal munch from `at`. Returns the match length, or `None`.
    pub match_len: fn(&[u8], usize) -> Option<usize>,
}

/// The rule table. Order is significant: the first rule that matches at a
/// position wins, so this is part of the versioned behaviour.
pub const RULES: &[Rule] = &[
    Rule {
        name: "hex-address",
        placeholder: "<ADDR>",
        // "0x" plus at least six hex digits. A shorter hex literal is a number
        // in a diagnostic, not an address, and rewriting it would erase content.
        min_match: 8,
        match_len: match_hex_address,
    },
    Rule {
        name: "absolute-path",
        placeholder: "<PATH>",
        min_match: 8,
        match_len: match_absolute_path,
    },
    Rule {
        name: "duration-ms",
        placeholder: "<TIME>",
        // At least four digits then "ms": sub-second timings are volatile,
        // small integers in a message are not.
        min_match: 6,
        match_len: match_duration_ms,
    },
    Rule {
        name: "process-id",
        placeholder: "<PID>",
        min_match: 6,
        match_len: match_process_id,
    },
];

fn match_hex_address(b: &[u8], at: usize) -> Option<usize> {
    if b.len() < at + 2 || b[at] != b'0' || b[at + 1] != b'x' {
        return None;
    }
    let mut end = at + 2;
    while end < b.len() && b[end].is_ascii_hexdigit() {
        end += 1;
    }
    Some(end - at)
}

fn is_path_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, b'/' | b'.' | b'_' | b'-' | b'+')
}

fn match_absolute_path(b: &[u8], at: usize) -> Option<usize> {
    if b.get(at) != Some(&b'/') {
        return None;
    }
    let mut end = at + 1;
    while end < b.len() && is_path_byte(b[end]) {
        end += 1;
    }
    Some(end - at)
}

fn match_duration_ms(b: &[u8], at: usize) -> Option<usize> {
    if !b.get(at).is_some_and(u8::is_ascii_digit) {
        return None;
    }
    let mut end = at;
    while end < b.len() && b[end].is_ascii_digit() {
        end += 1;
    }
    if b.len() < end + 2 || &b[end..end + 2] != b"ms" {
        return None;
    }
    Some(end + 2 - at)
}

fn match_process_id(b: &[u8], at: usize) -> Option<usize> {
    const PREFIX: &[u8] = b"pid=";
    if b.len() < at + PREFIX.len() || &b[at..at + PREFIX.len()] != PREFIX {
        return None;
    }
    let mut end = at + PREFIX.len();
    while end < b.len() && b[end].is_ascii_digit() {
        end += 1;
    }
    Some(end - at)
}

/// A normalized diagnostic, tagged with what produced it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Normalized {
    pub id: NormalizerId,
    pub version: NormalizerVersion,
    /// Always valid UTF-8, whatever the input was.
    pub text: String,
    /// Whether the budget clamped THIS normalization. Not part of the
    /// idempotence statement — see the module scope note.
    pub truncated: bool,
}

/// Why two normalized values could not be compared.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompareError {
    /// Different normalizers, or different versions of one. Refused rather
    /// than resolved: a comparison across versions is not a comparison.
    NormalizerMismatch {
        left: (NormalizerId, NormalizerVersion),
        right: (NormalizerId, NormalizerVersion),
    },
}

/// Compare two normalized values under a declared comparison class.
///
/// Refuses across normalizer id or version. This is the teeth on the "versioned"
/// obligation: without it, "versioned" means a field nobody reads.
pub fn compare(
    left: &Normalized,
    right: &Normalized,
    class: ComparisonClass,
) -> Result<bool, CompareError> {
    if left.id != right.id || left.version != right.version {
        return Err(CompareError::NormalizerMismatch {
            left: (left.id, left.version),
            right: (right.id, right.version),
        });
    }
    Ok(match class {
        ComparisonClass::ByteIdentical | ComparisonClass::NormalizedIdentical => {
            left.text == right.text
        }
        // Acceptance-only comparison does not look at diagnostic text at all;
        // saying "equal" here would be a lie about what was checked, so it is
        // vacuously true and the caller is expected not to ask.
        ComparisonClass::AcceptanceOnly => true,
        ComparisonClass::DiagnosticEquivalent => left.text == right.text,
    })
}

/// The diagnostic-text normalizer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Normalizer {
    pub id: NormalizerId,
    pub version: NormalizerVersion,
    pub budget: usize,
}

impl Default for Normalizer {
    fn default() -> Self {
        Normalizer {
            id: NormalizerId::DiagnosticText,
            version: DIAGNOSTIC_TEXT_V1,
            budget: DEFAULT_BUDGET,
        }
    }
}

impl Normalizer {
    /// A normalizer with a smaller budget, for tests and for callers that must
    /// bound a hostile oracle's stderr.
    pub fn with_budget(budget: usize) -> Normalizer {
        Normalizer {
            budget,
            ..Normalizer::default()
        }
    }

    /// Normalize one diagnostic.
    ///
    /// Total: every `&[u8]` has an image, including invalid UTF-8, embedded
    /// NULs, and a stderr that a crashing Reference truncated mid-character.
    pub fn normalize(&self, input: &[u8]) -> Normalized {
        let rewritten = self.rewrite(input);
        // `rewrite` emits only verbatim-copied valid UTF-8 sequences, ASCII
        // placeholders and ASCII '?', so this cannot fail. The fallback keeps
        // the function total anyway rather than resting totality on a proof
        // that lives in a comment.
        let text = String::from_utf8(rewritten).unwrap_or_default();
        let (text, truncated) = self.clamp(text);
        Normalized {
            id: self.id,
            version: self.version,
            text,
            truncated,
        }
    }

    /// Normalize a sequence, preserving order and length exactly.
    ///
    /// Not sorted, not deduplicated, not filtered. Diagnostic order is
    /// semantic — the Reference emits errors in source order and a rig that
    /// reorders them is comparing a different object than the one it names.
    pub fn normalize_all(&self, inputs: &[&[u8]]) -> Vec<Normalized> {
        inputs.iter().map(|i| self.normalize(i)).collect()
    }

    fn rewrite(&self, input: &[u8]) -> Vec<u8> {
        let mut out: Vec<u8> = Vec::with_capacity(input.len());
        let mut i = 0usize;
        while i < input.len() {
            if let Some((rule, len)) = first_match(input, i) {
                out.extend_from_slice(rule.placeholder.as_bytes());
                i += len;
                continue;
            }
            let b = input[i];
            if b.is_ascii() {
                out.push(b);
                i += 1;
                continue;
            }
            // Non-ASCII: copy a whole valid UTF-8 sequence verbatim (Lean
            // diagnostics are full of real Unicode and erasing it would be
            // "an error normalized away"), or substitute ONE byte per invalid
            // byte. Never U+FFFD, which expands 1 byte into 3.
            match utf8_sequence_len(input, i) {
                Some(n) => {
                    out.extend_from_slice(&input[i..i + n]);
                    i += n;
                }
                None => {
                    out.push(b'?');
                    i += 1;
                }
            }
        }
        out
    }

    fn clamp(&self, text: String) -> (String, bool) {
        if text.len() <= self.budget {
            return (text, false);
        }
        let room = self.budget.saturating_sub(TRUNCATION_MARKER.len());
        let mut cut = room.min(text.len());
        while cut > 0 && !text.is_char_boundary(cut) {
            cut -= 1;
        }
        let mut clamped = String::with_capacity(cut + TRUNCATION_MARKER.len());
        clamped.push_str(&text[..cut]);
        clamped.push_str(TRUNCATION_MARKER);
        (clamped, true)
    }
}

/// The first rule that matches at `at`, honouring each rule's declared minimum.
///
/// The `len >= rule.min_match` check is what makes non-expansion structural: a
/// rule cannot rewrite a span shorter than its own placeholder even if its
/// matcher is willing to.
fn first_match(input: &[u8], at: usize) -> Option<(&'static Rule, usize)> {
    RULES.iter().find_map(|rule| {
        (rule.match_len)(input, at)
            .filter(|len| *len >= rule.min_match)
            .map(|len| (rule, len))
    })
}

/// Length of the valid UTF-8 sequence starting at `at`, or `None` if the bytes
/// there are not a valid sequence.
fn utf8_sequence_len(input: &[u8], at: usize) -> Option<usize> {
    let b = input[at];
    let n = match b {
        0x00..=0x7F => 1,
        0xC2..=0xDF => 2,
        0xE0..=0xEF => 3,
        0xF0..=0xF4 => 4,
        _ => return None,
    };
    let end = at.checked_add(n)?;
    let slice = input.get(at..end)?;
    std::str::from_utf8(slice).ok().map(|_| n)
}

#[cfg(test)]
mod structural {
    use super::*;

    #[test]
    fn every_rule_declares_a_minimum_at_least_its_placeholder_length() {
        for rule in RULES {
            assert!(
                rule.min_match >= rule.placeholder.len(),
                "rule {} can expand: min_match {} < placeholder {} bytes",
                rule.name,
                rule.min_match,
                rule.placeholder.len()
            );
        }
    }

    #[test]
    fn no_placeholder_or_pair_of_placeholders_starts_a_match() {
        // If a placeholder could be rewritten, or if two adjacent placeholders
        // could combine into a match, idempotence would fail on exactly the
        // inputs an adversary would send.
        for a in RULES {
            for b in RULES {
                let joined = format!("{}{}", a.placeholder, b.placeholder);
                let bytes = joined.as_bytes();
                for at in 0..bytes.len() {
                    assert!(
                        first_match(bytes, at).is_none(),
                        "placeholders {} + {} produce a match at {at}",
                        a.name,
                        b.name
                    );
                }
            }
        }
    }

    #[test]
    fn the_truncation_marker_starts_no_match() {
        let bytes = TRUNCATION_MARKER.as_bytes();
        for at in 0..bytes.len() {
            assert!(first_match(bytes, at).is_none());
        }
    }

    #[test]
    fn the_marker_and_every_placeholder_are_fixed_points_of_normalization() {
        // [`Normalizer::clamp`] appends the marker AFTER the rewrite, so
        // anything the rewrite would do to the marker happens only on the
        // SECOND pass — and idempotence dies at exactly the budgets where a
        // clamp fires. The marker contains a multi-byte character, so this is
        // not implied by `the_truncation_marker_starts_no_match`: it also
        // depends on the rewrite copying valid UTF-8 verbatim. Stating it
        // directly means a mutation to the UTF-8 arm fails here, where the
        // cause is named, and not only in a distant clamp-boundary sweep.
        let n = Normalizer::with_budget(usize::MAX);
        assert_eq!(
            n.normalize(TRUNCATION_MARKER.as_bytes()).text,
            TRUNCATION_MARKER
        );
        for rule in RULES {
            assert_eq!(
                n.normalize(rule.placeholder.as_bytes()).text,
                rule.placeholder,
                "placeholder for {} is not a fixed point",
                rule.name
            );
        }
    }
}
