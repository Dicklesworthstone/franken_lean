//! The operation-outcome algebra (bead fln-171x, invariant FL-INV-07).
//!
//! Every authoritative operation in the program answers exactly one of three things,
//! and this module is where that is said once:
//!
//! * [`Outcome::Complete`] — the operation ran to completion and produced its domain
//!   result. A legitimate **rejection lives inside that result**, where the domain
//!   defines one: the kernel's `Rejected` is a real negative judgment about a term,
//!   and a decoder's "malformed" is a real statement about bytes. Neither is an
//!   outcome-level concept.
//! * [`Outcome::Inconclusive`] — the operation did not complete. Cancellation, an
//!   exhausted budget, an unavailable dependency, or authority we could not
//!   establish. **Nothing was learned about the domain question.**
//! * [`Outcome::InternalFault`] — one of our own invariants broke. Also not an
//!   answer to the domain question, and never a user diagnostic.
//!
//! ## Why this exists as one type
//!
//! Before this module, five hand-rolled lattices carried the same invariant:
//! `fln_kernel::verdict::Verdict` fused accept/reject/inconclusive into one enum,
//! `fln_env::decl_closure` grew its own cancellation-and-resource pair,
//! `fln_hash::canon::Decoded` grew a third, and the artifact-incomplete family a
//! fourth. Each was right on its own and none of them could be checked against the
//! others. Five copies of an invariant are five chances to drift.
//!
//! ## Outcome and cause are orthogonal axes
//!
//! The *what* is this module; the *why* is [`crate::diag::ErrorValue`], the D8
//! diagnostic vocabulary. A resource refusal is an `Inconclusive` **outcome**
//! carrying a resource **cause**; it is not a rejected theorem and not a malformed
//! user program. Conflating the two is precisely how an inconclusive starts being
//! rendered, cached, or promoted as a verdict — the FL-INV-07 violation itself. The
//! two axes are therefore never nested inside one another here: an [`Inconclusive`]
//! carries a cause, and a cause never carries an authority.
//!
//! ## What this module deliberately does not do
//!
//! It owns values and pure rules only. There is no byte codec: fln-core is rank 0 in
//! `ci/WORKSPACE_GRAPH.txt` with zero dependencies, and canonical serialization lives
//! in fln-hash, which depends on *this* crate. So the compatibility rules
//! ([`SchemaCompat`]) are stated here and the encoder that obeys them is downstream —
//! the layering runs one way and this module does not bend it.

use crate::diag::{ErrorValue, ResourceReason};

/// Schema version of the outcome algebra. A consumer that meets a version it does not
/// know must fail typed ([`SchemaCompat::Unsupported`]) rather than default.
pub const OUTCOME_SCHEMA: &str = "fln.outcome/1";
/// Numeric form of [`OUTCOME_SCHEMA`], for codecs that carry a version word.
pub const OUTCOME_SCHEMA_VERSION: u16 = 1;

/// How a decoder must treat a version word it reads.
///
/// There is no "assume current" arm on purpose: an unknown version is a typed refusal
/// at the boundary, never a silent default that reinterprets someone else's bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchemaCompat {
    /// Exactly the version this build speaks.
    Current,
    /// Anything else. The value is carried so the refusal can say what it saw.
    Unsupported { seen: u16 },
}

impl SchemaCompat {
    pub const fn classify(version: u16) -> SchemaCompat {
        if version == OUTCOME_SCHEMA_VERSION {
            SchemaCompat::Current
        } else {
            SchemaCompat::Unsupported { seen: version }
        }
    }

    pub const fn is_current(self) -> bool {
        matches!(self, SchemaCompat::Current)
    }
}

/// Free-text detail with a hard ceiling and an explicit truncation marker.
///
/// Details reach logs, transcripts and, eventually, other processes. An unbounded one
/// is a denial-of-service channel for adversarial input, and a silently shortened one
/// is worse than a marked one because a reader cannot tell evidence from an artifact
/// of the limit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundedText {
    text: String,
    truncated: bool,
}

impl BoundedText {
    /// Bytes retained before truncation. Generous enough for a real message, small
    /// enough that a hostile one cannot fill a transcript.
    pub const LIMIT: usize = 4096;

    pub fn new(text: impl Into<String>) -> BoundedText {
        let text = text.into();
        if text.len() <= BoundedText::LIMIT {
            return BoundedText {
                text,
                truncated: false,
            };
        }
        // Truncate on a character boundary so the retained prefix stays valid UTF-8.
        let mut end = BoundedText::LIMIT;
        while end > 0 && !text.is_char_boundary(end) {
            end -= 1;
        }
        BoundedText {
            text: text[..end].to_string(),
            truncated: true,
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    /// Whether content was dropped. Renderers must surface this; a reader has to be
    /// able to tell "this is all of it" from "this is what fit".
    pub const fn truncated(&self) -> bool {
        self.truncated
    }
}

/// Which budget an operation ran out of, and what it had spent.
///
/// Distinct from [`ResourceReason`] on purpose: that enum is the *diagnostic*
/// vocabulary a renderer prints, this is the structured fact a scheduler or a caller
/// reasons over when deciding whether to retry with a larger allowance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourceUsage {
    /// The registered resource, in the diagnostic vocabulary.
    pub reason: ResourceReason,
    /// What the caller allowed, in that resource's own units.
    pub allowed: u64,
    /// What had been spent when the budget tripped. Always greater than `allowed`
    /// for a genuine exhaustion; an equal pair means the limit was never exceeded and
    /// the outcome is misreported.
    pub observed: u64,
}

impl ResourceUsage {
    /// A stop must report spending past its allowance, or it is not a stop.
    pub const fn is_genuine_exhaustion(&self) -> bool {
        self.observed > self.allowed
    }
}

/// Why an operation did not complete. Never why a domain answer came out negative —
/// that is [`ErrorValue`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InconclusiveCause {
    /// Cooperative cancellation was observed. The work is abandoned, not answered.
    Cancelled { at: BoundedText },
    /// A caller-supplied budget was exhausted.
    ResourceExhausted { usage: ResourceUsage },
    /// Something the operation needed was not available — an artifact, a peer, a
    /// dependency whose own outcome was not authoritative.
    DependencyUnavailable { what: BoundedText },
    /// The operation could not establish authority over its own inputs: an unreadable
    /// governed file, an incomplete traversal, a source that changed underfoot. The
    /// scan is not clean; it is unfinished.
    AuthorityIncomplete { what: BoundedText },
}

/// An operation that did not complete, with the cause and the diagnostic vocabulary
/// entry a renderer would use.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inconclusive {
    pub cause: InconclusiveCause,
    /// The *diagnostic* projection, if this outcome is user-visible. Optional because
    /// the outcome is authoritative-by-absence: an inconclusive with no diagnostic is
    /// still an inconclusive, and a missing diagnostic must never upgrade it.
    pub diagnostic: Option<ErrorValue>,
}

impl Inconclusive {
    pub fn cancelled(at: impl Into<String>) -> Inconclusive {
        Inconclusive {
            cause: InconclusiveCause::Cancelled {
                at: BoundedText::new(at),
            },
            diagnostic: None,
        }
    }

    pub fn resource(usage: ResourceUsage) -> Inconclusive {
        Inconclusive {
            cause: InconclusiveCause::ResourceExhausted { usage },
            diagnostic: None,
        }
    }

    pub fn dependency_unavailable(what: impl Into<String>) -> Inconclusive {
        Inconclusive {
            cause: InconclusiveCause::DependencyUnavailable {
                what: BoundedText::new(what),
            },
            diagnostic: None,
        }
    }

    pub fn authority_incomplete(what: impl Into<String>) -> Inconclusive {
        Inconclusive {
            cause: InconclusiveCause::AuthorityIncomplete {
                what: BoundedText::new(what),
            },
            diagnostic: None,
        }
    }

    pub fn with_diagnostic(mut self, cause: ErrorValue) -> Inconclusive {
        self.diagnostic = Some(cause);
        self
    }
}

/// One of our invariants broke. Not a domain answer and not a user diagnostic: a
/// panic would be the same event with less information, which is why this type exists
/// (FL-INV-07 — panics are invariant failures, never user diagnostics).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InternalFault {
    /// The registered invariant that failed, e.g. `FL-INV-07`.
    pub invariant: &'static str,
    pub detail: BoundedText,
    /// Where the evidence lives — an artifact path, a receipt id, a run id.
    pub evidence: Option<BoundedText>,
}

impl InternalFault {
    pub fn new(invariant: &'static str, detail: impl Into<String>) -> InternalFault {
        InternalFault {
            invariant,
            detail: BoundedText::new(detail),
            evidence: None,
        }
    }

    pub fn with_evidence(mut self, evidence: impl Into<String>) -> InternalFault {
        self.evidence = Some(BoundedText::new(evidence));
        self
    }
}

/// Whether a result may be treated as an answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Authority {
    /// The operation completed; its domain result stands.
    Authoritative,
    /// It did not. Nothing may be concluded, cached, or published from this.
    NonAuthoritative,
}

impl Authority {
    /// The `authority` field every structured log carries.
    pub const fn as_bool(self) -> bool {
        matches!(self, Authority::Authoritative)
    }
}

/// The non-answer arms, as a value a caller must handle.
///
/// [`Outcome::into_complete`] returns this in its error position rather than an
/// `Option`, so a caller cannot turn "we do not know" into "there is nothing here"
/// with a `?` or an `unwrap_or_default`. Successful absence is a different claim, and
/// the type refuses to make it for you.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NonAuthoritative {
    Inconclusive(Inconclusive),
    InternalFault(InternalFault),
}

/// Whether a cache, a ledger, or a published artifact may take this result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CacheAdmission {
    /// The run was authoritative; its result may be stored.
    Admissible,
    /// It was not. The reason travels with the refusal so a log can say which.
    Refused { authority: Authority },
}

/// The outcome of an authoritative operation.
///
/// `#[must_use]` because dropping one on the floor is how a non-answer becomes a
/// silent success.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub enum Outcome<T> {
    /// Ran to completion. `T` is the domain result, and carries the domain's own
    /// rejection where it has one.
    Complete(T),
    Inconclusive(Inconclusive),
    InternalFault(InternalFault),
}

impl<T> Outcome<T> {
    pub fn complete(value: T) -> Outcome<T> {
        Outcome::Complete(value)
    }

    pub const fn authority(&self) -> Authority {
        match self {
            Outcome::Complete(_) => Authority::Authoritative,
            Outcome::Inconclusive(_) | Outcome::InternalFault(_) => Authority::NonAuthoritative,
        }
    }

    /// Whether a cache or ledger may store what this produced.
    ///
    /// This lives here, once, because both fln-env and fln-hash had to enforce it
    /// separately before this type existed — and an invariant enforced in two places
    /// is an invariant that will hold in one of them.
    pub const fn cache_admission(&self) -> CacheAdmission {
        match self {
            Outcome::Complete(_) => CacheAdmission::Admissible,
            Outcome::Inconclusive(_) | Outcome::InternalFault(_) => CacheAdmission::Refused {
                authority: Authority::NonAuthoritative,
            },
        }
    }

    /// The only way to get at the domain result.
    ///
    /// Note the error type: a caller that writes `?` receives a typed
    /// [`NonAuthoritative`] and must decide what to do with it. There is deliberately
    /// no `Option` accessor, no `Default`, no `From<Outcome<T>> for Result<T, E>`,
    /// and no `unwrap_or` — each of those is a way to spell "treat not-knowing as an
    /// answer", which is the invariant this module exists to prevent.
    pub fn into_complete(self) -> Result<T, NonAuthoritative> {
        match self {
            Outcome::Complete(value) => Ok(value),
            Outcome::Inconclusive(inconclusive) => {
                Err(NonAuthoritative::Inconclusive(inconclusive))
            }
            Outcome::InternalFault(fault) => Err(NonAuthoritative::InternalFault(fault)),
        }
    }

    /// Borrowed view of the domain result, for inspection that must not consume.
    pub const fn as_complete(&self) -> Option<&T> {
        match self {
            Outcome::Complete(value) => Some(value),
            Outcome::Inconclusive(_) | Outcome::InternalFault(_) => None,
        }
    }

    /// Map the domain result, leaving a non-answer untouched.
    ///
    /// The one transformation that is always sound: it cannot turn a non-answer into
    /// an answer, because the closure never runs for one.
    pub fn map_complete<U>(self, f: impl FnOnce(T) -> U) -> Outcome<U> {
        match self {
            Outcome::Complete(value) => Outcome::Complete(f(value)),
            Outcome::Inconclusive(inconclusive) => Outcome::Inconclusive(inconclusive),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name::Name;

    fn usage(allowed: u64, observed: u64) -> ResourceUsage {
        ResourceUsage {
            reason: ResourceReason::Heartbeats {
                consumed: observed,
                limit: allowed,
            },
            allowed,
            observed,
        }
    }

    /// A stand-in for a domain result that has its own rejection — the shape the
    /// kernel's verdict and the decoder's malformed-input answer both have.
    #[derive(Debug, Clone, PartialEq, Eq)]
    enum DomainVerdict {
        Accepted,
        Rejected { why: &'static str },
    }

    /// Suite: operation_outcome_authority_model.
    ///
    /// Every arm reports the authority it must, and the domain's own rejection stays
    /// inside the complete arm rather than becoming an outcome-level concept.
    #[test]
    fn operation_outcome_authority_model() {
        let accepted: Outcome<DomainVerdict> = Outcome::complete(DomainVerdict::Accepted);
        let rejected: Outcome<DomainVerdict> = Outcome::complete(DomainVerdict::Rejected {
            why: "a real negative judgment",
        });
        let stopped: Outcome<DomainVerdict> =
            Outcome::Inconclusive(Inconclusive::resource(usage(10, 11)));
        let faulted: Outcome<DomainVerdict> = Outcome::InternalFault(InternalFault::new(
            "FL-INV-07",
            "meter disagreed with itself",
        ));

        // A rejection is an ANSWER: the run completed and said no.
        for authoritative in [&accepted, &rejected] {
            assert_eq!(authoritative.authority(), Authority::Authoritative);
            assert!(authoritative.authority().as_bool());
            assert_eq!(authoritative.cache_admission(), CacheAdmission::Admissible);
            assert!(authoritative.as_complete().is_some());
        }

        // A stop and a fault are NOT answers, and say so identically.
        for non_authoritative in [&stopped, &faulted] {
            assert_eq!(non_authoritative.authority(), Authority::NonAuthoritative);
            assert!(!non_authoritative.authority().as_bool());
            assert_eq!(
                non_authoritative.cache_admission(),
                CacheAdmission::Refused {
                    authority: Authority::NonAuthoritative
                }
            );
            assert!(non_authoritative.as_complete().is_none());
        }

        // The domain's rejection survives extraction intact — it was never lifted out
        // of the domain into the algebra.
        assert_eq!(
            rejected.into_complete().expect("a rejection is complete"),
            DomainVerdict::Rejected {
                why: "a real negative judgment"
            }
        );
        // And a non-answer extracts as a typed non-authority, never as absence.
        match stopped.into_complete() {
            Err(NonAuthoritative::Inconclusive(inconclusive)) => {
                assert!(matches!(
                    inconclusive.cause,
                    InconclusiveCause::ResourceExhausted { .. }
                ));
            }
            other => panic!("expected a typed non-authority, got {other:?}"),
        }
    }

    /// Suite: outcome_cause_orthogonality.
    ///
    /// The same diagnostic cause can accompany either axis, and attaching one never
    /// changes authority. This is the property whose absence lets an inconclusive be
    /// rendered as a rejection.
    #[test]
    fn outcome_cause_orthogonality() {
        let decl = Name::str(Name::anonymous(), "Thm");
        let cause = ErrorValue::KernelRejection {
            decl: decl.clone(),
            stable_error_class: "type-mismatch".to_string(),
            message: "expected Nat".to_string(),
        };

        // A rejection is a COMPLETE outcome whose domain result carries the cause.
        let rejected: Outcome<ErrorValue> = Outcome::complete(cause.clone());
        assert_eq!(rejected.authority(), Authority::Authoritative);

        // The very same cause attached to a stop does not make the stop an answer.
        let stopped: Outcome<ErrorValue> = Outcome::Inconclusive(
            Inconclusive::resource(usage(1, 2)).with_diagnostic(cause.clone()),
        );
        assert_eq!(stopped.authority(), Authority::NonAuthoritative);
        assert_eq!(
            stopped.cache_admission(),
            CacheAdmission::Refused {
                authority: Authority::NonAuthoritative
            }
        );

        // The cause axis has its own predicates (ErrorValue::is_rejection /
        // is_inconclusive). They describe the WHY and must never be read as the
        // authority: here a rejection-classed cause sits on a non-authoritative
        // outcome, and an inconclusive-classed cause sits on an authoritative one.
        // Both are legitimate, which is exactly what orthogonal means.
        assert!(cause.is_rejection());
        assert_eq!(stopped.authority(), Authority::NonAuthoritative);
        let reported: Outcome<ErrorValue> = Outcome::complete(ErrorValue::KernelInconclusive {
            decl,
            resource: ResourceReason::Cancelled,
        });
        assert!(
            reported.as_complete().expect("complete").is_inconclusive(),
            "the cause says the kernel run was inconclusive"
        );
        assert_eq!(
            reported.authority(),
            Authority::Authoritative,
            "yet REPORTING that fact is itself a completed operation — the axes do \
             not collapse into one another"
        );

        // And an inconclusive with NO diagnostic is still non-authoritative: a missing
        // cause must never upgrade an outcome.
        let bare: Outcome<ErrorValue> = Outcome::Inconclusive(Inconclusive::cancelled("mid-scan"));
        assert_eq!(bare.authority(), Authority::NonAuthoritative);
        assert!(matches!(
            bare,
            Outcome::Inconclusive(Inconclusive {
                diagnostic: None,
                ..
            })
        ));
    }

    /// `map_complete` is the only transformation offered, and it cannot manufacture
    /// authority: the closure never runs for a non-answer, so a mapped stop is still
    /// a stop with its cause intact.
    #[test]
    fn mapping_cannot_manufacture_authority() {
        let mut ran = false;
        let stopped: Outcome<u8> = Outcome::Inconclusive(Inconclusive::cancelled("here"));
        let mapped = stopped.map_complete(|value| {
            ran = true;
            u32::from(value)
        });
        assert!(!ran, "the mapper must not run for a non-answer");
        assert_eq!(mapped.authority(), Authority::NonAuthoritative);
        assert!(matches!(
            mapped,
            Outcome::Inconclusive(Inconclusive {
                cause: InconclusiveCause::Cancelled { .. },
                ..
            })
        ));

        let mapped = Outcome::complete(7u8).map_complete(u32::from);
        assert_eq!(mapped.as_complete(), Some(&7u32));
    }

    /// Every cause variant round-trips through the constructors with its facts
    /// intact, and a resource stop must report spending past its allowance.
    #[test]
    fn every_inconclusive_cause_carries_its_facts() {
        let cancelled = Inconclusive::cancelled("declaration 41");
        let InconclusiveCause::Cancelled { at } = &cancelled.cause else {
            panic!("cancelled");
        };
        assert_eq!(at.text(), "declaration 41");

        let exhausted = Inconclusive::resource(usage(200_000, 200_001));
        let InconclusiveCause::ResourceExhausted { usage } = &exhausted.cause else {
            panic!("exhausted");
        };
        assert!(usage.is_genuine_exhaustion());
        assert!(
            !ResourceUsage {
                reason: ResourceReason::Cancelled,
                allowed: 5,
                observed: 5,
            }
            .is_genuine_exhaustion()
        );

        let unavailable = Inconclusive::dependency_unavailable("olean for Init.Core");
        assert!(matches!(
            unavailable.cause,
            InconclusiveCause::DependencyUnavailable { .. }
        ));

        let incomplete = Inconclusive::authority_incomplete("crates/x/src/y.rs unreadable");
        assert!(matches!(
            incomplete.cause,
            InconclusiveCause::AuthorityIncomplete { .. }
        ));
    }

    /// Details are bounded and truncation is explicit — a reader must be able to tell
    /// evidence from an artifact of the limit.
    #[test]
    fn bounded_details_mark_their_truncation() {
        let short = BoundedText::new("fits");
        assert!(!short.truncated());
        assert_eq!(short.text(), "fits");

        let long = BoundedText::new("x".repeat(BoundedText::LIMIT + 100));
        assert!(long.truncated(), "an oversized detail must say it was cut");
        assert_eq!(long.text().len(), BoundedText::LIMIT);

        // Multi-byte input is cut on a character boundary, never mid-character.
        let multibyte = BoundedText::new("é".repeat(BoundedText::LIMIT));
        assert!(multibyte.truncated());
        assert!(multibyte.text().len() <= BoundedText::LIMIT);
        assert!(std::str::from_utf8(multibyte.text().as_bytes()).is_ok());
    }

    /// An unknown version is a typed refusal, never a default. A decoder that treats
    /// an unrecognised word as "probably current" reinterprets someone else's bytes.
    #[test]
    fn unknown_schema_versions_fail_typed() {
        assert_eq!(
            SchemaCompat::classify(OUTCOME_SCHEMA_VERSION),
            SchemaCompat::Current
        );
        assert!(SchemaCompat::classify(OUTCOME_SCHEMA_VERSION).is_current());
        for unknown in [0u16, 2, 7, u16::MAX] {
            assert_eq!(
                SchemaCompat::classify(unknown),
                SchemaCompat::Unsupported { seen: unknown },
                "version {unknown} must be refused with what was seen"
            );
            assert!(!SchemaCompat::classify(unknown).is_current());
        }
    }

    /// Model check over the join every cache, ledger and published artifact performs:
    /// across every outcome shape, admission and authority agree, and a non-answer
    /// never yields a value to store.
    #[test]
    fn no_non_authoritative_result_crosses_a_cache_join() {
        let name = Name::str(Name::anonymous(), "decl");
        let population: Vec<Outcome<DomainVerdict>> = vec![
            Outcome::complete(DomainVerdict::Accepted),
            Outcome::complete(DomainVerdict::Rejected { why: "universe" }),
            Outcome::Inconclusive(Inconclusive::cancelled("during whnf")),
            Outcome::Inconclusive(Inconclusive::resource(usage(1, 9))),
            Outcome::Inconclusive(Inconclusive::dependency_unavailable(
                name.to_display_string(),
            )),
            Outcome::Inconclusive(Inconclusive::authority_incomplete("unreadable input")),
            Outcome::Inconclusive(Inconclusive::resource(usage(3, 4)).with_diagnostic(
                ErrorValue::ProtocolFailure {
                    detail: "peer closed".to_string(),
                },
            )),
            Outcome::InternalFault(InternalFault::new("FL-INV-01", "schedule dependence")),
            Outcome::InternalFault(
                InternalFault::new("FL-INV-06", "engine output bypassed the kernel")
                    .with_evidence("receipt://abc"),
            ),
        ];

        for outcome in &population {
            let admissible = outcome.cache_admission() == CacheAdmission::Admissible;
            let authoritative = outcome.authority() == Authority::Authoritative;
            assert_eq!(
                admissible, authoritative,
                "admission and authority must be the same predicate"
            );
            assert_eq!(
                outcome.as_complete().is_some(),
                authoritative,
                "a value is available exactly when the run was authoritative"
            );
        }

        // Exactly the two complete arms are admissible — no cause, diagnostic, or
        // evidence field moves anything across the join.
        assert_eq!(
            population
                .iter()
                .filter(|o| o.cache_admission() == CacheAdmission::Admissible)
                .count(),
            2
        );
    }
}
