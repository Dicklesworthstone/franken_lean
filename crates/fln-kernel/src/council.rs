//! The consensus seat (beads `fln-uc44` and `franken_lean-4o3n`; plan §8.3c, B3).
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
//! # Ran out is not disagreed — and may not even be comparable
//!
//! The pressure this seat will actually face is not a forged agreement. It is
//! *noise*. A second engine running under a bound asymmetric to the kernel's
//! turns every declaration it cannot finish into a halt — correctly on the
//! seat's own terms, and constantly, on artifacts rather than on
//! disagreements. Someone competent then proposes, on performance grounds,
//! treating the second engine's inconclusive as agreement. That is the
//! FL-INV-07 promotion this module forbids, it will be argued well, and it will
//! sound reasonable because the halts really are noise.
//!
//! The defence is not a stronger prohibition; it is making the noise legible
//! before there is any of it (bead `franken_lean-4o3n`):
//!
//! * [`SeatVerdict::Exhausted`] is a **distinct arm** from `Disagrees` and from
//!   `NoAnswer`, carrying which [`Bound`] was hit. "Ran out" and "disagreed"
//!   stop being the same event in the record.
//! * Every seat states the bound it answered under ([`SeatBounds`]), so a
//!   resource stop can be read against the kernel's own bound instead of
//!   against a guess.
//! * When two bounds cannot be established comparable
//!   ([`Comparability`](crate::verdict::Comparability)), the seat says
//!   so as a **typed refusal** — [`ObjectionKind::ExhaustionNotComparable`] —
//!   rather than quietly reading the stop as a disagreement or as noise. Two
//!   engines can report identical fuel while neither measured it in the
//!   configuration it runs in, and agreement between those two numbers
//!   certifies nothing.
//! * [`Halt::is_purely_resource`] gives the honest half of the concession —
//!   "nothing here is evidence the declaration is bad" — **without** the
//!   unsound half. It still halts. All three objection kinds halt; the typing
//!   exists so a reader can tell them apart, never so that one of them can be
//!   waived.
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
use crate::verdict::{Bound, Budget, Comparability, ComparabilityDefect, Consumption, RejectClass};

/// Who is speaking. An identity for the record, never a trust level — nothing
/// in this module treats one seat as weightier than another.
///
/// Distinct from [`crate::verdict::EngineId`]: this names a *participant*, and
/// two seats can be two runs of one engine or a lane with no engine behind it
/// at all. The engine identity that matters for comparability travels on the
/// seat's [`SeatBounds`], where it is a claim about measured code rather than a
/// label.
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

/// The resource contract a seat answered under.
///
/// Required of every seat, including the ones that have nothing to declare —
/// which is why the second arm exists and is spelled out rather than left as an
/// `Option`. A subprocess witness with only a wall clock genuinely has no
/// bound this process derived, and saying so is a statement about **what we
/// know**, not an accusation about the witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeatBounds {
    /// Derived in this process from a stated [`crate::verdict::StackMeasurement`]
    /// of this seat's own engine. The only form that can be established
    /// comparable with the kernel's.
    Derived(Budget),
    /// No bound was established here: a foreign process, a lane with no
    /// resource contract, or a number stated without a measurement behind it.
    /// Perfectly fine for a seat that completes — a completed check is a
    /// completed check under any bound, because a budget can stop a check but
    /// cannot make one finish falsely. It is only a seat's *resource stop* that
    /// this leaves unreadable.
    NotEstablished { note: String },
}

impl SeatBounds {
    pub fn not_established(note: impl Into<String>) -> SeatBounds {
        SeatBounds::NotEstablished { note: note.into() }
    }

    pub fn budget(&self) -> Option<&Budget> {
        match self {
            SeatBounds::Derived(budget) => Some(budget),
            SeatBounds::NotEstablished { .. } => None,
        }
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
    /// The seat hit its own resource bound: it neither agreed nor disagreed,
    /// and it did not merely fall silent — it *stopped*, on a named limit.
    ///
    /// Separated from [`SeatVerdict::NoAnswer`] because the two decay
    /// differently. Silence is an operational problem someone fixes. A resource
    /// stop is a *systematic* one that recurs on the same declarations every
    /// run, and its volume is the argument that will be used to reclassify it
    /// as agreement. Naming it is what lets that volume be reported honestly
    /// instead of being laundered.
    Exhausted { bound: Bound },
    /// The seat could not answer: absent, errored, cancelled, timed out, or
    /// never run. **Not agreement** (FL-INV-07).
    NoAnswer { reason: String },
}

/// One seat's contribution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Seat {
    pub id: SeatId,
    /// What the seat answered under. See [`SeatBounds`].
    pub bounds: SeatBounds,
    pub verdict: SeatVerdict,
}

impl Seat {
    pub fn new(id: impl Into<String>, bounds: SeatBounds, verdict: SeatVerdict) -> Seat {
        Seat {
            id: SeatId::new(id),
            bounds,
            verdict,
        }
    }
}

/// Why a seat's resource stop could not be read against the kernel's bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Incomparability {
    /// The seat declared no derived bound at all.
    NoBoundEstablished { note: String },
    /// It declared one, and the two could not be established comparable.
    Defect(ComparabilityDefect),
}

impl Incomparability {
    pub fn describe(&self) -> String {
        match self {
            Incomparability::NoBoundEstablished { note } => {
                format!("no bound was established for this seat ({note})")
            }
            Incomparability::Defect(defect) => defect.describe(),
        }
    }
}

/// What kind of objection a seat raised — the three-way distinction bead
/// `franken_lean-4o3n` requires, with exhaustion split by whether it can be
/// read at all.
///
/// Every kind halts. The distinction is for the reader of the record, and its
/// purpose is to make the *second* and *third* kinds impossible to confuse with
/// the first when someone argues that the halts are noise.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectionKind {
    /// A real negative judgment about the term. The only kind that is evidence
    /// the declaration might be bad.
    Disagreement,
    /// A resource stop under a bound established comparable with the kernel's.
    /// A genuine fact about two comparable engines: this one ran out where the
    /// kernel did not. Still a non-answer, and still a halt.
    Exhaustion { bound: Bound },
    /// A resource stop under a bound that could NOT be established comparable.
    ///
    /// Nothing may be concluded from it — not that the engines disagree, and
    /// not that the stop is a spurious artifact of asymmetric bounds. Both
    /// readings are claims about a comparison that did not happen. This is the
    /// typed refusal, and it is deliberately not collapsible into the arm
    /// above: the whole failure mode is that an unreadable stop gets read.
    ExhaustionNotComparable { bound: Bound, why: Incomparability },
    /// The seat said nothing.
    Silence,
}

impl ObjectionKind {
    /// Whether this objection is evidence about the *declaration* rather than
    /// about the run.
    pub fn is_about_the_declaration(&self) -> bool {
        matches!(self, ObjectionKind::Disagreement)
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
    /// The bound the kernel's own check ran under, with its calibration. Kept
    /// on the halt because every judgement about a seat's resource stop is a
    /// judgement *relative to this*, and a record that omits it cannot be
    /// re-read later.
    pub kernel_budget: Budget,
    /// Every seat that did not agree, with its reason and its bounds.
    pub objections: Vec<Seat>,
}

impl Halt {
    /// Classify every objection against the kernel's own bound.
    ///
    /// Order is the supplied order (FL-INV-01). The classification is computed
    /// rather than stored so it cannot drift from the seats it describes.
    pub fn classify(&self) -> Vec<(SeatId, ObjectionKind)> {
        self.objections
            .iter()
            .map(|seat| (seat.id.clone(), self.classify_seat(seat)))
            .collect()
    }

    fn classify_seat(&self, seat: &Seat) -> ObjectionKind {
        match &seat.verdict {
            // Not an objection; `objections` never contains one, and a total
            // match here is better than an unreachable arm.
            SeatVerdict::Agrees => ObjectionKind::Silence,
            SeatVerdict::Disagrees { .. } => ObjectionKind::Disagreement,
            SeatVerdict::NoAnswer { .. } => ObjectionKind::Silence,
            SeatVerdict::Exhausted { bound } => match &seat.bounds {
                SeatBounds::NotEstablished { note } => ObjectionKind::ExhaustionNotComparable {
                    bound: bound.clone(),
                    why: Incomparability::NoBoundEstablished { note: note.clone() },
                },
                SeatBounds::Derived(budget) => {
                    match Comparability::establish(&self.kernel_budget, budget) {
                        Comparability::Established => ObjectionKind::Exhaustion {
                            bound: bound.clone(),
                        },
                        Comparability::NotEstablished(defect) => {
                            ObjectionKind::ExhaustionNotComparable {
                                bound: bound.clone(),
                                why: Incomparability::Defect(defect),
                            }
                        }
                    }
                }
            },
        }
    }

    /// True when **no** objection is evidence about the declaration — every one
    /// is a resource stop or a silence.
    ///
    /// This is the honest half of the concession the noise argument asks for,
    /// and it is deliberately all of it. A caller may report "these halts say
    /// nothing bad about this declaration" and be exactly right. What no caller
    /// may do is turn that into publication: the capability is already gone,
    /// and this predicate cannot bring it back. Legible is not waivable.
    pub fn is_purely_resource(&self) -> bool {
        !self
            .objections
            .iter()
            .any(|seat| matches!(seat.verdict, SeatVerdict::Disagrees { .. }))
    }

    /// A one-line summary for logs. The structured `objections` and
    /// [`Halt::classify`] remain the authoritative record; this never replaces
    /// them.
    pub fn summary(&self) -> String {
        let mut parts = Vec::with_capacity(self.objections.len());
        for seat in &self.objections {
            let what = match &seat.verdict {
                SeatVerdict::Agrees => "agrees".to_string(),
                SeatVerdict::Disagrees { detail } => format!("disagrees: {detail}"),
                SeatVerdict::NoAnswer { reason } => format!("no answer: {reason}"),
                SeatVerdict::Exhausted { bound } => match self.classify_seat(seat) {
                    ObjectionKind::ExhaustionNotComparable { why, .. } => format!(
                        "ran out of {} under a bound not comparable to the kernel's: {}",
                        bound.describe(),
                        why.describe()
                    ),
                    _ => format!("ran out of {}", bound.describe()),
                },
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
                // Read the kernel's bound BEFORE the drop: the halt has to
                // record what the seats were being compared against, and after
                // this line the capability — and everything it knows — is gone.
                let kernel_budget = checked.budget();
                // `checked` is not returned and not stored: dropping it here is
                // the halt. Nothing downstream can reconstruct it.
                drop(checked);
                CouncilOutcome::Halted(Halt {
                    kernel_accepted: true,
                    kernel_budget,
                    objections,
                })
            }
        }
    }
}
