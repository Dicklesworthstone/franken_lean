//! The consensus seat (bead `fln-uc44`; plan §8.3c, B3).
//!
//! # What this is
//!
//! B3 promises that kernel disagreement **halts, and never outvotes**. That
//! sentence had no mechanism behind it: before this module the word "consensus"
//! appeared in `fln-kernel` and `fln-checker` exactly once, in a stub's charter
//! line. This is the mechanism, built while there is still nothing to vote —
//! which is the only moment it can be built honestly. A veto seat added *after*
//! a working second engine exists is added under standing pressure to let that
//! engine's verdict count for something, and every such concession is a
//! widening of the TCB wearing the costume of an optimization.
//!
//! # The two properties, and how each is obtained
//!
//! 1. **A seat can halt publication.** [`convene`] consumes the
//!    [`Admitted`](crate::capability::Admitted) value produced by
//!    [`admit`](crate::capability::admit). The publication right *is* the
//!    [`CheckedDecl`](crate::capability::CheckedDecl) it contains, that value is
//!    not `Clone`, and on a halt this function simply does not hand it back —
//!    it is dropped. Halting is therefore not a flag anyone can ignore; the
//!    capability ceases to exist.
//!
//! 2. **A seat can never construct the capability.** This needs no new
//!    machinery: `CheckedDecl` has a private field of a private type
//!    (`capability::Seal`), so no crate outside `fln-kernel` can name it, and
//!    there is no constructor, no `Default`, no `From`, and no deserialisation.
//!    A [`SeatVerdict`] is ordinary data that anyone may build — and that is
//!    exactly the point: it is *evidence*, and evidence must be forgeable in
//!    the sense that anyone can state it, precisely because stating it grants
//!    nothing. A seat that could manufacture the thing it is supposed to
//!    witness would not be a witness.
//!
//! # There is no vote
//!
//! Agreement is **required, not tallied**. There is no quorum, no majority, and
//! no seat count anywhere in this module. Three agreeing seats cannot carry one
//! dissenter, because nothing here counts. That is not an oversight to be
//! optimized later; a design in which agreement can be outweighed is the exact
//! failure this module exists to make unrepresentable.
//!
//! # A non-answer is not agreement
//!
//! A seat that is absent, errored, timed out, or simply was not run reports
//! [`SeatVerdict::NoAnswer`], and a no-answer halts. This is FL-INV-07 applied
//! to the council: a missing opinion is a missing opinion, and silently reading
//! it as assent is how a witness lane decays into a rubber stamp.
//!
//! # Zero I/O, deliberately
//!
//! `fln-kernel` is zero-I/O by covenant (§8.1), so this module cannot read a
//! witness's output. It takes seat verdicts as **values**. Feeding it the real
//! foreign witness — `scripts/tribunal/leanchecker_witness.sh`, which already
//! runs in `scripts/check.sh` and emits `"verdict":"accepted"` / `"rejected"`
//! per module with an anti-rubber-stamp discriminate lane — is a job for a
//! layer that is allowed to do I/O. [`SeatVerdict`] is shaped to accept exactly
//! that vocabulary, including its third case: the witness that did not run.
//!
//! # What this does NOT claim
//!
//! It does not claim a second in-repo engine exists. `fln-checker` is still a
//! charter crate and there is still no NbE anywhere; that remains
//! `franken_lean-gii` and `franken_lean-g3k`. It also does not rescue
//! FL-INV-02, which is kernel soundness *locality* and is already supported by
//! [`crate::capability`]. This is the defense-in-depth layer B3 promises on top
//! of that, and nothing more.

use crate::capability::{Admitted, CheckedDecl};
use crate::verdict::{Consumption, RejectClass};

/// Who is speaking. An identity for the record, never a trust level — nothing
/// in this module treats one seat as weightier than another.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeatId(String);

impl SeatId {
    pub fn new(id: impl Into<String>) -> SeatId {
        SeatId(id.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// What one seat said about one declaration.
///
/// Ordinary data with public constructors: anyone may *state* a verdict,
/// because stating one grants nothing. See the module docs on why forgeability
/// here is the design rather than a hole in it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeatVerdict {
    /// The seat checked this declaration and agrees it is acceptable.
    Agrees,
    /// The seat checked this declaration and disagrees. The detail is retained
    /// and reported on the halt — a disagreement whose reason is discarded
    /// cannot be investigated, and an uninvestigable disagreement is the one
    /// most likely to be dismissed.
    Disagrees { detail: String },
    /// The seat could not answer: absent, errored, cancelled, timed out, or
    /// never run. **Not agreement** (FL-INV-07).
    NoAnswer { reason: String },
}

/// One seat's contribution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Seat {
    pub id: SeatId,
    pub verdict: SeatVerdict,
}

impl Seat {
    pub fn new(id: impl Into<String>, verdict: SeatVerdict) -> Seat {
        Seat {
            id: SeatId::new(id),
            verdict,
        }
    }
}

/// The seats consulted for one declaration.
///
/// An empty council is the *no policy configured* case and agrees vacuously.
/// That is honest rather than lax: it makes "nobody was asked" a visible state
/// at the call site instead of a silent default, and §8.3c's policies (standard
/// sampling, release full-closure, paranoid everywhere) are exactly the rules
/// that decide which declarations get a non-empty council.
#[derive(Debug, Clone, Default)]
pub struct Council {
    seats: Vec<Seat>,
}

impl Council {
    /// No seats: nobody was asked. Spelled explicitly so call sites that have
    /// no council yet say so rather than appearing to have passed one.
    pub fn nobody_was_asked() -> Council {
        Council { seats: Vec::new() }
    }

    pub fn of(seats: Vec<Seat>) -> Council {
        Council { seats }
    }

    pub fn seats(&self) -> &[Seat] {
        &self.seats
    }

    /// Every seat that did not agree, in the order they were supplied.
    /// Deterministic: no sorting by a schedule-dependent key, no set iteration.
    fn objections(&self) -> Vec<Seat> {
        self.seats
            .iter()
            .filter(|seat| !matches!(seat.verdict, SeatVerdict::Agrees))
            .cloned()
            .collect()
    }
}

/// Why publication was refused, with every objection retained.
///
/// A halt is never an acceptance and never a rejection: the kernel's own
/// judgment is reported separately from the council's, because collapsing them
/// would lose which one objected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Halt {
    /// What the kernel concluded, retained so a halt cannot be misread as the
    /// kernel having rejected.
    pub kernel_accepted: bool,
    /// Every seat that did not agree, with its reason.
    pub objections: Vec<Seat>,
}

impl Halt {
    /// A one-line summary for logs. The structured `objections` remain the
    /// authoritative record; this never replaces them.
    pub fn summary(&self) -> String {
        let mut parts = Vec::with_capacity(self.objections.len());
        for seat in &self.objections {
            let what = match &seat.verdict {
                SeatVerdict::Agrees => "agrees".to_string(),
                SeatVerdict::Disagrees { detail } => format!("disagrees: {detail}"),
                SeatVerdict::NoAnswer { reason } => format!("no answer: {reason}"),
            };
            parts.push(format!("{}={what}", seat.id.as_str()));
        }
        format!(
            "publication halted (kernel_accepted={}); {}",
            self.kernel_accepted,
            parts.join("; ")
        )
    }
}

/// What convening the council concluded.
///
/// The `Agreed` arm is the only one that carries a
/// [`CheckedDecl`](crate::capability::CheckedDecl), so it is the only one from
/// which anything can be published.
pub enum CouncilOutcome<'env> {
    /// Unanimous. The publication right survives.
    Agreed(CheckedDecl<'env>),
    /// The kernel accepted, but at least one seat did not agree. The capability
    /// was dropped; nothing can publish.
    Halted(Halt),
    /// The kernel itself rejected. The council is not consulted — there is no
    /// publication right to withhold, and asking seats to ratify a rejection
    /// would invite the reading that enough agreement could overturn it.
    KernelRejected {
        class: RejectClass,
        message: String,
        consumption: Consumption,
    },
}

/// Convene the council over an admission result.
///
/// Consumes the [`Admitted`](crate::capability::Admitted) value, so on a halt
/// the capability inside it is dropped rather than returned. There is no
/// variant of this function that reports a halt while handing the capability
/// back, because that function would be a suggestion rather than a veto.
pub fn convene<'env>(council: &Council, admitted: Admitted<'env>) -> CouncilOutcome<'env> {
    match admitted {
        Admitted::Rejected {
            class,
            message,
            consumption,
        } => CouncilOutcome::KernelRejected {
            class,
            message,
            consumption,
        },
        Admitted::Accepted(checked) => {
            let objections = council.objections();
            if objections.is_empty() {
                CouncilOutcome::Agreed(checked)
            } else {
                // `checked` is not returned and not stored: dropping it here is
                // the halt. Nothing downstream can reconstruct it.
                drop(checked);
                CouncilOutcome::Halted(Halt {
                    kernel_accepted: true,
                    objections,
                })
            }
        }
    }
}
