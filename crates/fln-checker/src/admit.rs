//! KR-970 … KR-973 — the declaration-admission preamble, and the first surface in
//! this crate that turns inference into a **verdict**.
//!
//! Every earlier `franken_lean-gii` slice built a component: terms, universes,
//! weak-head reduction, quick and slow definitional equality, the constant
//! environment, Nat and String reduction, eta, and inference KR-100 … KR-112.
//! Each of the three inference slices named declaration admission as the thing
//! outside its scope. This module is that thing, for the four rules that need no
//! body checked:
//!
//! * **KR-970**, one name one constant — a declaration whose name already exists
//!   in the environment is refused, naming it.
//! * **KR-971**, distinct level parameters — a declaration whose own
//!   level-parameter list repeats a name is refused, naming the duplicate and
//!   both positions. The check is on the declaration's list, independent of any
//!   instantiation.
//! * **KR-972**, the well-formed constant preamble — the declaration's *type* is
//!   itself inferred and forced through checker-owned WHNF to a `Sort`. A
//!   declaration whose type is not a type is refused at the declaration rather
//!   than at first use.
//! * **KR-973**, axioms — an axiom whose preamble passes is admitted by rule,
//!   there being no body to check.
//!
//! # FL-INV-02 shapes this surface, and the shape is the design decision
//!
//! `fln-checker` is an independent veto and evidence seat, **never an alternative
//! admission authority**. So [`Verdict`] is an *observation a council may
//! consult*, and three properties keep it from becoming anything else:
//!
//! 1. [`Admission`] has no public constructor and no public field, so the only
//!    way to obtain one is to call [`admit`] and have it say yes.
//! 2. Neither [`Admission`] nor [`Verdict`] is `Clone` or `Copy`. A verdict
//!    cannot be duplicated, stored as a token and presented later; the honest
//!    thing to do with an observation is to read it. This is deliberate and
//!    costs ergonomics on purpose.
//! 3. There is no conversion out of either type — no `From`, no `Into`, no
//!    accessor yielding a `ConstantEntry`, a `ConstantDeclaration` or anything
//!    else an environment consumes. `admit` takes a `&ConstantEntry` and gives
//!    back a judgement *about* it; it never hands one back.
//!
//! Underneath all three sits the structural fact that makes them worth stating:
//! this crate does not depend on `fln-kernel` and must not, so no type
//! `fln-kernel`'s admission path consumes is even nameable here.
//! `the_admission_verdict_is_not_a_capability` in `tests/admit.rs` binds the
//! dependency half to the manifest and the surface half to this file.
//!
//! # FL-INV-07 is why there are five verdicts and not two
//!
//! Accepted and Rejected are *decisions*. Resource exhaustion, cancellation, a
//! nested WHNF refusal, a requirement this slice has not built, and an internal
//! fault are **not decisions**, and rendering any of them as acceptance or
//! rejection would be the failure that invariant exists to prevent. Each gets
//! its own arm, and none is cached or promoted.
//!
//! The deferral arm is the load-bearing one for a slice this narrow. A
//! definition, theorem, opaque, inductive, constructor, recursor or quotient has
//! a preamble this module can check and a body it cannot, so a preamble-passing
//! non-axiom is [`Verdict::Deferred`] — **not** rejected, which would be a false
//! verdict, and not admitted, which would be a worse one.
//!
//! # The stack budget is shared, so this module stays off the inference frame
//!
//! `franken_lean-gii.20` cost a red when three match arms grew `InferenceEngine::run`'s
//! single frame past the 64 KiB budget. This module therefore adds no
//! `InferenceProgress` counter, widens nothing on the inference path, and lives
//! *outside* the engine: it calls the public [`infer_with`] and [`whnf_with`]
//! entry points and never joins their recursion.

use crate::defeq::{
    DefEqBudget, DefEqDeferred, DefEqFault, DefEqMismatch, DefEqOutcome, DefEqSide, DefEqStop,
    def_eq_with,
};
use crate::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, ConstantSafety,
    DefinitionBody, DefinitionSafety,
};
use crate::infer::{
    InferenceBudget, InferenceContext, InferenceContextRefusal, InferenceDeferred, InferenceFault,
    InferenceMode, InferenceOutcome, InferenceRefusal, InferenceStop, infer_with,
};
use crate::universe::{NormalNode, normalize};
use crate::whnf::{WhnfBudget, WhnfFault, WhnfOutcome, WhnfRefusal, WhnfStop, whnf_with};
use crate::wire::{ExprNode, WireExpr, WireLevel, WireName};

/// The schema tag a council quotes when it records one of these observations.
pub const ADMISSION_SCHEMA: &str = "fln.checker-admission/1";

/// Where in the preamble a run was when it stopped.
///
/// Carried by the inconclusive arm only, because a decision names its own rule
/// and does not need a position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdmissionPhase {
    /// KR-970 — the environment lookup.
    UniqueName,
    /// KR-971 — the declaration's own level-parameter list.
    LevelParameters,
    /// KR-972 — inferring the declared type.
    DeclaredType,
    /// KR-972 — forcing that type's own type to a `Sort`.
    DeclaredTypeSort,
    /// KR-973 — the terminal rule for the declaration's kind.
    Terminal,
    /// KR-974 — inferring the definition body's type.
    Body,
    /// KR-974 — converting the body's type against the declared type.
    BodyConversion,
}

/// The four preamble rules' decisions, each on its own variant.
///
/// A rejection is a *decision about the declaration*, so every variant names the
/// declaration it judged. Nothing here folds into a generic "rejected": a caller
/// that wants to know which law refused can ask, and a test that asserts on the
/// wrong variant fails rather than passing on a coincidence.
#[derive(Debug, PartialEq, Eq)]
pub enum AdmissionRejection {
    /// KR-970 — the environment already holds a constant under this name.
    NameAlreadyDeclared { name: WireName },
    /// KR-971 — the declaration's own level-parameter list repeats a name.
    ///
    /// Both positions are carried, because "duplicate" is a fact about a *pair*
    /// and naming one index leaves the reader to find the other.
    DuplicateLevelParameter {
        name: WireName,
        parameter: WireName,
        first: usize,
        second: usize,
    },
    /// KR-972 — inferring the declared type refused on its own terms.
    DeclaredTypeRefused {
        name: WireName,
        refusal: Box<InferenceRefusal>,
    },
    /// KR-972 — the declared type's own type does not reduce to a `Sort`, so the
    /// declared type is not a type.
    DeclaredTypeIsNotASort { name: WireName },
    /// KR-972 — reduction of the declared type's own type REFUSED, which is a
    /// different event from that type not being a sort.
    ///
    /// **This variant is a repair.** gii.23 mapped `WhnfOutcome::Refused` onto
    /// `DeclaredTypeIsNotASort` and discarded the refusal, so a malformed
    /// reduction context — a duplicate free binding, a free-binding cycle, a
    /// projection index overflow — was reported as a statement about the
    /// declaration's type. Every `WhnfRefusal` variant is malformed *reduction
    /// input*; none of them means "not a sort". `infer.rs` already keeps the two
    /// apart (`SortReductionRefusal` beside `SortExpected`), and admission
    /// disagreeing with inference about the same event is worse than either
    /// choice. The refusal is carried rather than summarised.
    DeclaredTypeReductionRefused {
        name: WireName,
        refusal: Box<WhnfRefusal>,
    },
    /// KR-974 — inferring the definition body's type refused on its own terms.
    BodyTypeRefused {
        name: WireName,
        refusal: Box<InferenceRefusal>,
    },
    /// KR-974 — the body's inferred type is not definitionally equal to the
    /// DECLARED type. The nested mismatch is carried, not flattened.
    BodyTypeMismatch {
        name: WireName,
        mismatch: Box<DefEqMismatch>,
    },
    /// KR-974 — conversion REFUSED while comparing the two types, which is not the
    /// same event as the two types differing. Same distinction as
    /// `DeclaredTypeReductionRefused`, made once rather than rediscovered.
    BodyConversionRefused {
        name: WireName,
        side: DefEqSide,
        refusal: Box<WhnfRefusal>,
    },
    /// KR-974 — a body-carrying kind was declared with NO body.
    ///
    /// A REJECTION rather than an internal fault, and the classification was
    /// measured rather than assumed: `ConstantDeclaration::header` accepts any
    /// `ConstantKind` and hardcodes `definition: None`, so a caller can build a
    /// bodyless `Definition`, `Theorem` or `Opaque`. That is malformed
    /// caller-supplied input, and FL-INV-07 reserves the fault arm for invariant
    /// failures, never user diagnostics.
    DeclarationCarriesNoBody { name: WireName, kind: ConstantKind },
    /// KR-974 — a theorem's declared type is not a proposition.
    ///
    /// A theorem proves a Prop. The preamble already reduced the declared type's
    /// own type to a `Sort`; a theorem additionally requires that universe to
    /// normalize to zero. Without this, `theorem` and `def` are the same rule.
    TheoremTypeIsNotAProposition { name: WireName },
}

/// A requirement this slice has not built. Never a rejection.
#[derive(Debug, PartialEq, Eq)]
pub enum AdmissionDeferred {
    /// KR-974 (definitions, theorems, opaques), KR-977 (mutual blocks), and the
    /// inductive family: the preamble passed and the *body* is unchecked, which
    /// is a different slice.
    BodyNotChecked { name: WireName, kind: ConstantKind },
    /// Inference itself deferred while checking the declared type.
    DeclaredTypeInference {
        name: WireName,
        requirement: Box<InferenceDeferred>,
    },
    /// KR-974 — inference deferred while checking the body's type.
    BodyTypeInference {
        name: WireName,
        requirement: Box<InferenceDeferred>,
    },
    /// KR-974 — conversion deferred. NOT a mismatch: the comparison did not
    /// finish, so nothing is known about whether the two types agree.
    BodyConversion {
        name: WireName,
        need: Box<DefEqDeferred>,
    },
}

/// FL-INV-07 resource and cancellation outcomes. Never a decision.
#[derive(Debug, PartialEq, Eq)]
pub enum AdmissionStop {
    /// Cancellation observed at a preamble checkpoint, before any nested engine
    /// was entered.
    Cancelled {
        name: WireName,
        phase: AdmissionPhase,
    },
    DeclaredTypeInference {
        name: WireName,
        stop: Box<InferenceStop>,
    },
    DeclaredTypeSortWhnf {
        name: WireName,
        stop: Box<WhnfStop>,
    },
    BodyTypeInference {
        name: WireName,
        stop: Box<InferenceStop>,
    },
    /// A conversion that ran out of budget is INCONCLUSIVE. It is never a
    /// mismatch — a body check that could not finish looks exactly like a body
    /// check that failed, and this is the arm where that confusion would land.
    BodyConversion {
        name: WireName,
        stop: Box<DefEqStop>,
    },
}

/// An invariant failure. Never a user diagnostic.
#[derive(Debug, PartialEq, Eq)]
pub enum AdmissionFault {
    DeclaredTypeInference {
        name: WireName,
        fault: Box<InferenceFault>,
    },
    DeclaredTypeSortWhnf {
        name: WireName,
        fault: Box<WhnfFault>,
    },
    /// The inference context could not be built. KR-971 has already excluded the
    /// only refusal this call site can provoke — a repeated level parameter —
    /// and the candidate contributes no locals and no projection rules, so
    /// reaching this is a defect in this module rather than bad input.
    ContextUnbuildable {
        name: WireName,
        refusal: Box<InferenceContextRefusal>,
    },
    /// The reduced type had no node at its own root.
    MissingSortRoot { name: WireName },
    BodyTypeInference {
        name: WireName,
        fault: Box<InferenceFault>,
    },
    BodyConversion {
        name: WireName,
        fault: Box<DefEqFault>,
    },
    /// The declared type reduced to a `Sort` whose universe could not be
    /// normalized, so KR-974b cannot decide whether it is a proposition.
    UniverseNotNormalizable { name: WireName },
}

/// KR-975 / KR-976 — which quarantine a declaration lands in.
///
/// # The decision this slice was filed to make, and its argument
///
/// A declaration carries TWO safety marks: the header's `ConstantSafety` and, if
/// it has a body, that body's `DefinitionSafety`. They can disagree, and
/// `franken_lean-gii.25` was filed with that case explicitly undecided.
///
/// **The quarantine is keyed on the WEAKEST of the two.** A `Safe` header over an
/// `Unsafe` body is admitted into the *unsafe* quarantine, not the safe world.
/// The argument is consistency rather than taste: two mechanisms already treat
/// that declaration as unsafe — `ConstantDeclaration::delta_body` returns `None`
/// unless the kind, the constant AND the body are all safe, so it is already
/// non-unfoldable; and `infer.rs`'s reference gate already raises
/// `InferenceRefusal::UnsafeConstant` when *either* mark is unsafe. Admission
/// keying on the header alone would be a third behaviour disagreeing with both,
/// and the disagreement would be silent.
///
/// **The reference GATE stays keyed on the header, and that is deliberate and
/// separate.** `admit` passes `InferenceMode::Checking { declaration_safety }`
/// from the header, so a `Safe`-header declaration is checked with the gate ON
/// even when its body marks it unsafe — otherwise a caller could unlock unsafe
/// references by marking only the body, which is the mark the header does not
/// advertise. So both keys are conservative, in opposite directions: the gate
/// takes the STRONGER claim about what the declaration may reference, and the
/// quarantine takes the WEAKER claim about what may reference it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quarantine {
    /// Neither mark is weakened.
    None,
    /// KR-976 — the body is `DefinitionSafety::Partial`.
    Partial,
    /// KR-975 — either mark is unsafe.
    Unsafe,
}

/// Why a declaration was admitted.
///
/// One variant today, and it is an enum rather than a unit so that KR-974's
/// grounds arrive as a *new variant* — a caller matching exhaustively fails to
/// compile rather than silently treating a body-checked admission as this one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdmissionGround {
    /// KR-973 — an axiom whose KR-970/971/972 preamble passed. There is no body,
    /// so nothing else was owed.
    AxiomPreamble,
    /// KR-974 — the preamble passed AND the body's inferred type was found
    /// definitionally equal to the declared type.
    ///
    /// A separate variant rather than a reuse of `AxiomPreamble`, so a caller
    /// matching exhaustively fails to COMPILE rather than silently treating a
    /// body-checked admission as a preamble-only one. The two are different
    /// claims and an enum is the cheapest place to keep them apart.
    BodyCheckedAgainstDeclaredType,
    /// KR-975 — admitted INTO THE UNSAFE QUARANTINE. Everything the ordinary
    /// grounds claim, plus the fact that this declaration is not safe: a council
    /// reading this ground must not treat it as an ordinary admission, and the
    /// separate variant is what stops that being a matter of remembering.
    UnsafeQuarantine,
    /// KR-976 — admitted into the PARTIAL quarantine. Distinct from the unsafe
    /// one because they are different quarantines, and one variant for both
    /// would leave the verdict unable to say which.
    PartialQuarantine,
}

/// The observation that a declaration passed every rule this module implements.
///
/// **This is not a capability and must never become one.** It has no public
/// constructor, no public field, and no conversion out. It is deliberately not
/// `Clone`, so it cannot be duplicated into something stored and presented later
/// as authority. What a council may do with it is read it.
#[derive(Debug, PartialEq, Eq)]
pub struct Admission {
    name: WireName,
    ground: AdmissionGround,
}

impl Admission {
    /// The declaration this observation is about.
    ///
    /// Borrowed, never moved out: a caller receives the name it already supplied,
    /// not a fresh object carrying the checker's blessing.
    pub fn name(&self) -> &WireName {
        &self.name
    }

    /// Which rule admitted it.
    pub const fn ground(&self) -> AdmissionGround {
        self.ground
    }

    /// The schema tag under which this observation is recorded.
    pub const fn schema(&self) -> &'static str {
        ADMISSION_SCHEMA
    }
}

/// What this checker observed about one candidate declaration.
///
/// Five arms, not two, because FL-INV-07 says so: the last three are *not*
/// answers, and none of them may be cached, promoted, or rendered as either
/// decision.
#[derive(Debug, PartialEq, Eq)]
pub enum Verdict {
    Admitted(Admission),
    Rejected(AdmissionRejection),
    Deferred(AdmissionDeferred),
    Inconclusive(AdmissionStop),
    InternalFault(AdmissionFault),
}

impl Verdict {
    /// True only for [`Verdict::Admitted`].
    ///
    /// Provided so that no caller has to write `!matches!(v, Rejected(_))` and
    /// thereby fold the three non-answers into acceptance — the exact FL-INV-07
    /// failure this enum's shape exists to prevent.
    pub const fn is_admitted(&self) -> bool {
        matches!(self, Verdict::Admitted(_))
    }

    /// True for the three arms that are not decisions.
    pub const fn is_inconclusive_family(&self) -> bool {
        matches!(
            self,
            Verdict::Deferred(_) | Verdict::Inconclusive(_) | Verdict::InternalFault(_)
        )
    }
}

/// Bounds for one admission run.
///
/// Separate from [`InferenceBudget`] because the KR-972 sort reduction is a
/// second, independently accounted descent: a declared type may infer cheaply
/// and reduce expensively, and one number cannot express both.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AdmissionBudget {
    pub inference: InferenceBudget,
    pub sort_whnf: WhnfBudget,
    /// KR-974's conversion bound. Separate again, and for the same reason the
    /// sort reduction is: a body may infer cheaply and convert expensively.
    pub conversion: DefEqBudget,
}

impl AdmissionBudget {
    pub const fn new(
        inference: InferenceBudget,
        sort_whnf: WhnfBudget,
        conversion: DefEqBudget,
    ) -> AdmissionBudget {
        AdmissionBudget {
            inference,
            sort_whnf,
            conversion,
        }
    }

    pub const fn unlimited() -> AdmissionBudget {
        AdmissionBudget::new(
            InferenceBudget::unlimited(),
            WhnfBudget::unlimited(),
            InferenceBudget::unlimited().defeq,
        )
    }
}

/// Run KR-970 … KR-973 over one candidate declaration.
pub fn admit(
    environment: &ConstantEnvironment,
    candidate: &ConstantEntry,
    budget: AdmissionBudget,
) -> Verdict {
    admit_with(environment, candidate, budget, || false)
}

/// [`admit`], with a cancellation poll.
///
/// The poll is consulted at each preamble checkpoint *and* handed to both nested
/// engines, so a cancellation during a long declared-type inference is observed
/// by inference rather than waited out.
pub fn admit_with(
    environment: &ConstantEnvironment,
    candidate: &ConstantEntry,
    budget: AdmissionBudget,
    mut cancelled: impl FnMut() -> bool,
) -> Verdict {
    let name = candidate.name();
    let declaration = candidate.declaration();

    // KR-970 — one name, one constant.
    if cancelled() {
        return stopped(name, AdmissionPhase::UniqueName);
    }
    if environment.find(name).is_some() {
        return Verdict::Rejected(AdmissionRejection::NameAlreadyDeclared { name: name.clone() });
    }

    // KR-971 — the declaration's own level parameters are distinct.
    if cancelled() {
        return stopped(name, AdmissionPhase::LevelParameters);
    }
    if let Some((parameter, first, second)) = first_repeated_level_parameter(declaration) {
        return Verdict::Rejected(AdmissionRejection::DuplicateLevelParameter {
            name: name.clone(),
            parameter,
            first,
            second,
        });
    }

    // KR-972 — the declared type is inferred and forced to a Sort.
    if cancelled() {
        return stopped(name, AdmissionPhase::DeclaredType);
    }
    let declared =
        match declared_type_is_a_type(environment, name, declaration, &budget, &mut cancelled) {
            Ok(facts) => facts,
            Err(verdict) => return verdict,
        };

    // KR-973 and KR-974 — the terminal rule for this declaration's kind.
    if cancelled() {
        return stopped(name, AdmissionPhase::Terminal);
    }
    terminal_rule(
        environment,
        name,
        declaration,
        &declared,
        &budget,
        &mut cancelled,
    )
}

/// What KR-972 learned about the declared type, carried forward instead of
/// recomputed.
///
/// KR-974b needs to know whether the declared type is a proposition, and the
/// preamble has already reduced its type to a `Sort`. Re-deriving that in the
/// terminal rule would be a second reduction that could disagree with the first.
struct DeclaredTypeFacts {
    /// The declared type's own type reduced to `Sort u` with `u` normalizing to
    /// zero — i.e. the declared type is a `Prop`.
    is_proposition: bool,
}

fn stopped(name: &WireName, phase: AdmissionPhase) -> Verdict {
    Verdict::Inconclusive(AdmissionStop::Cancelled {
        name: name.clone(),
        phase,
    })
}

/// KR-971's predicate, separated so it is one thing that can be wrong.
///
/// Returns the first repeat in declaration order together with **both**
/// positions. Quadratic on purpose: a level-parameter list is a handful of names
/// on every real declaration, and a `BTreeSet` here would report *that* there is
/// a duplicate while losing the earlier index the caller needs to name it.
fn first_repeated_level_parameter(
    declaration: &ConstantDeclaration,
) -> Option<(WireName, usize, usize)> {
    let parameters = declaration.level_parameters();
    for (second, parameter) in parameters.iter().enumerate() {
        for (first, earlier) in parameters.iter().enumerate().take(second) {
            if earlier == parameter {
                return Some((parameter.clone(), first, second));
            }
        }
    }
    None
}

/// KR-972 — infer the declared type, then force *its* type to a `Sort`.
///
/// Two descents, not one. Inference gives the declared type's type; that result
/// is a term like `Sort 1` only after weak-head reduction, so a type whose
/// well-formedness is hidden behind an unreduced application is judged on what it
/// reduces to rather than on how it was written.
fn declared_type_is_a_type(
    environment: &ConstantEnvironment,
    name: &WireName,
    declaration: &ConstantDeclaration,
    budget: &AdmissionBudget,
    cancelled: &mut impl FnMut() -> bool,
) -> Result<DeclaredTypeFacts, Verdict> {
    // The candidate is not yet in the environment, so this context is exactly the
    // one KR-970 just proved does not already hold the name: a declaration cannot
    // use itself to justify its own type.
    let context = match InferenceContext::new(
        Vec::new(),
        declaration.level_parameters().to_vec(),
        environment.clone(),
    ) {
        Ok(context) => context,
        Err(refusal) => {
            return Err(Verdict::InternalFault(AdmissionFault::ContextUnbuildable {
                name: name.clone(),
                refusal: Box::new(refusal),
            }));
        }
    };

    let type_of_type = match infer_with(
        declaration.type_(),
        &context,
        InferenceMode::Checking {
            declaration_safety: declaration.safety(),
        },
        budget.inference,
        &mut *cancelled,
    ) {
        InferenceOutcome::Complete(result) => result.type_,
        InferenceOutcome::Refused { refusal, .. } => {
            return Err(Verdict::Rejected(AdmissionRejection::DeclaredTypeRefused {
                name: name.clone(),
                refusal: Box::new(refusal),
            }));
        }
        InferenceOutcome::Deferred { requirement, .. } => {
            return Err(Verdict::Deferred(
                AdmissionDeferred::DeclaredTypeInference {
                    name: name.clone(),
                    requirement: Box::new(requirement),
                },
            ));
        }
        InferenceOutcome::Inconclusive(stop) => {
            return Err(Verdict::Inconclusive(
                AdmissionStop::DeclaredTypeInference {
                    name: name.clone(),
                    stop: Box::new(stop),
                },
            ));
        }
        InferenceOutcome::InternalFault { fault, .. } => {
            return Err(Verdict::InternalFault(
                AdmissionFault::DeclaredTypeInference {
                    name: name.clone(),
                    fault: Box::new(fault),
                },
            ));
        }
    };

    reduces_to_a_sort(name, &type_of_type, &context, budget, cancelled)
}

fn reduces_to_a_sort(
    name: &WireName,
    type_of_type: &WireExpr,
    context: &InferenceContext,
    budget: &AdmissionBudget,
    cancelled: &mut impl FnMut() -> bool,
) -> Result<DeclaredTypeFacts, Verdict> {
    if cancelled() {
        return Err(stopped(name, AdmissionPhase::DeclaredTypeSort));
    }
    let reduced = match whnf_with(
        type_of_type,
        // The context that INFERRED the type, not one rebuilt from the same
        // inputs: a second construction is free to drift from the real one, and
        // reducing under a different environment than we inferred under is
        // exactly the incoherence KR-972 exists to rule out.
        context.reduction(),
        budget.sort_whnf,
        &mut *cancelled,
    ) {
        WhnfOutcome::Complete(result) => result.term,
        // REPAIRED. This arm used to discard the refusal and report
        // DeclaredTypeIsNotASort -- a false statement about the declaration for a
        // cause that is actually malformed reduction input. See
        // AdmissionRejection::DeclaredTypeReductionRefused.
        WhnfOutcome::Refused(refusal) => {
            return Err(Verdict::Rejected(
                AdmissionRejection::DeclaredTypeReductionRefused {
                    name: name.clone(),
                    refusal: Box::new(refusal),
                },
            ));
        }
        WhnfOutcome::Inconclusive(stop) => {
            return Err(Verdict::Inconclusive(AdmissionStop::DeclaredTypeSortWhnf {
                name: name.clone(),
                stop: Box::new(stop),
            }));
        }
        WhnfOutcome::InternalFault(fault) => {
            return Err(Verdict::InternalFault(
                AdmissionFault::DeclaredTypeSortWhnf {
                    name: name.clone(),
                    fault: Box::new(fault),
                },
            ));
        }
    };

    match reduced.node(reduced.root()) {
        Some(ExprNode::Sort { level }) => {
            // KR-974b needs the universe, and it must be NORMALIZED rather than
            // matched syntactically: `Sort (max 0 0)` is `Prop` and a check that
            // only recognises a literal `Zero` node would call it a type. The
            // normalizer is the crate's one producer for that question.
            let level = *level;
            let carrier = WireLevel::from_parts(reduced.levels().to_vec(), level);
            match normalize(&carrier) {
                Ok(normal) => Ok(DeclaredTypeFacts {
                    is_proposition: matches!(
                        normal.nodes().get(normal.root().index()),
                        Some(NormalNode::Zero)
                    ),
                }),
                Err(_) => Err(Verdict::InternalFault(
                    AdmissionFault::UniverseNotNormalizable { name: name.clone() },
                )),
            }
        }
        Some(_) => Err(Verdict::Rejected(
            AdmissionRejection::DeclaredTypeIsNotASort { name: name.clone() },
        )),
        None => Err(Verdict::InternalFault(AdmissionFault::MissingSortRoot {
            name: name.clone(),
        })),
    }
}

/// KR-973 and the boundary of this slice.
///
/// The `match` is exhaustive over `ConstantKind` on purpose. When KR-974 lands,
/// moving `Theorem` out of the deferral arm is a compile error here rather than a
/// silent behaviour change somewhere else.
fn terminal_rule(
    environment: &ConstantEnvironment,
    name: &WireName,
    declaration: &ConstantDeclaration,
    declared: &DeclaredTypeFacts,
    budget: &AdmissionBudget,
    cancelled: &mut impl FnMut() -> bool,
) -> Verdict {
    // KR-975 / KR-976. This used to DEFER every unsafe declaration before the
    // kind was even examined, so the checker could say nothing at all about one.
    // It now runs the same rules and records the quarantine in the ground.
    let quarantine = quarantine_of(declaration);

    match declaration.kind() {
        // KR-973. There is deliberately no "an axiom must not carry a body"
        // check, because that state is UNCONSTRUCTIBLE and a branch nothing can
        // reach is a branch no mutation can kill. Measured at this commit:
        // `ConstantDeclaration` has exactly two constructors and no public
        // field; `header` hardcodes `definition: None`, and `definition`
        // hardcodes `kind: ConstantKind::Definition`. So no caller can hand this
        // rule an axiom with a body. The type already holds the law, and writing
        // it again here would read as diligence while testing nothing.
        // `an_axiom_cannot_be_constructed_with_a_body` binds that measurement,
        // so the day a third constructor lands, this comment fails rather than
        // quietly becoming false.
        ConstantKind::Axiom => Verdict::Admitted(Admission {
            name: name.clone(),
            ground: ground_for(quarantine, AdmissionGround::AxiomPreamble),
        }),
        // KR-974. These three carry a body, and the body is what this rule
        // checks. The inductive family below does not, so folding it in here
        // would be scope creep wearing a match arm.
        kind @ (ConstantKind::Theorem | ConstantKind::Opaque | ConstantKind::Definition) => {
            // KR-974b, checked BEFORE the body: a theorem whose statement is not
            // a proposition is not a theorem, whatever its body proves. Checking
            // it after would spend a full conversion to reach the same refusal
            // and report the more expensive cause.
            if kind == ConstantKind::Theorem && !declared.is_proposition {
                return Verdict::Rejected(AdmissionRejection::TheoremTypeIsNotAProposition {
                    name: name.clone(),
                });
            }
            let Some(body) = declaration.definition_body() else {
                return Verdict::Rejected(AdmissionRejection::DeclarationCarriesNoBody {
                    name: name.clone(),
                    kind,
                });
            };
            match body_matches_declared_type(
                environment,
                name,
                declaration,
                body.value(),
                budget,
                cancelled,
            ) {
                Ok(()) => Verdict::Admitted(Admission {
                    name: name.clone(),
                    ground: ground_for(quarantine, AdmissionGround::BodyCheckedAgainstDeclaredType),
                }),
                Err(verdict) => verdict,
            }
        }
        kind @ (ConstantKind::Inductive
        | ConstantKind::Constructor
        | ConstantKind::Recursor
        | ConstantKind::Quotient) => Verdict::Deferred(AdmissionDeferred::BodyNotChecked {
            name: name.clone(),
            kind,
        }),
    }
}

/// KR-975 / KR-976 — classify a declaration's quarantine from BOTH safety marks.
///
/// Unsafe dominates Partial dominates None, which is the "weakest of the two"
/// rule argued at [`Quarantine`]. Written as an explicit match rather than an
/// ordering trick so that a fourth `DefinitionSafety` variant fails to compile
/// here instead of silently landing in whichever arm a `>=` put it in.
fn quarantine_of(declaration: &ConstantDeclaration) -> Quarantine {
    if declaration.safety() == ConstantSafety::Unsafe {
        return Quarantine::Unsafe;
    }
    match declaration.definition_body().map(DefinitionBody::safety) {
        Some(DefinitionSafety::Unsafe) => Quarantine::Unsafe,
        Some(DefinitionSafety::Partial) => Quarantine::Partial,
        Some(DefinitionSafety::Safe) | None => Quarantine::None,
    }
}

/// The ground a quarantined admission reports.
///
/// A quarantine REPLACES the ordinary ground rather than annotating it, so there
/// is no way to read a quarantined admission as an ordinary one by ignoring a
/// field — the only thing a caller can match on already carries the quarantine.
const fn ground_for(quarantine: Quarantine, ordinary: AdmissionGround) -> AdmissionGround {
    match quarantine {
        Quarantine::None => ordinary,
        Quarantine::Partial => AdmissionGround::PartialQuarantine,
        Quarantine::Unsafe => AdmissionGround::UnsafeQuarantine,
    }
}

/// KR-974a — the body's inferred type is checked definitionally equal to the
/// DECLARED type.
///
/// Two descents again, and the FL-INV-07 discipline is sharpest here: a
/// conversion that runs out of budget, is cancelled, or faults is INCONCLUSIVE,
/// never a mismatch. A body check that could not finish looks exactly like a
/// body check that failed, and only this function decides which one a caller is
/// told about.
#[allow(clippy::too_many_arguments)]
fn body_matches_declared_type(
    environment: &ConstantEnvironment,
    name: &WireName,
    declaration: &ConstantDeclaration,
    body: &WireExpr,
    budget: &AdmissionBudget,
    cancelled: &mut impl FnMut() -> bool,
) -> Result<(), Verdict> {
    let context = match InferenceContext::new(
        Vec::new(),
        declaration.level_parameters().to_vec(),
        environment.clone(),
    ) {
        Ok(context) => context,
        Err(refusal) => {
            return Err(Verdict::InternalFault(AdmissionFault::ContextUnbuildable {
                name: name.clone(),
                refusal: Box::new(refusal),
            }));
        }
    };

    let body_type = match infer_with(
        body,
        &context,
        InferenceMode::Checking {
            declaration_safety: declaration.safety(),
        },
        budget.inference,
        &mut *cancelled,
    ) {
        InferenceOutcome::Complete(result) => result.type_,
        InferenceOutcome::Refused { refusal, .. } => {
            return Err(Verdict::Rejected(AdmissionRejection::BodyTypeRefused {
                name: name.clone(),
                refusal: Box::new(refusal),
            }));
        }
        InferenceOutcome::Deferred { requirement, .. } => {
            return Err(Verdict::Deferred(AdmissionDeferred::BodyTypeInference {
                name: name.clone(),
                requirement: Box::new(requirement),
            }));
        }
        InferenceOutcome::Inconclusive(stop) => {
            return Err(Verdict::Inconclusive(AdmissionStop::BodyTypeInference {
                name: name.clone(),
                stop: Box::new(stop),
            }));
        }
        InferenceOutcome::InternalFault { fault, .. } => {
            return Err(Verdict::InternalFault(AdmissionFault::BodyTypeInference {
                name: name.clone(),
                fault: Box::new(fault),
            }));
        }
    };

    if cancelled() {
        return Err(stopped_err(name, AdmissionPhase::BodyConversion));
    }
    match def_eq_with(
        &body_type,
        declaration.type_(),
        // Again the context that INFERRED, not one rebuilt from the same inputs.
        context.reduction(),
        budget.conversion,
        &mut *cancelled,
    ) {
        DefEqOutcome::Equal(_) => Ok(()),
        DefEqOutcome::NotEqual { mismatch, .. } => {
            Err(Verdict::Rejected(AdmissionRejection::BodyTypeMismatch {
                name: name.clone(),
                mismatch: Box::new(mismatch),
            }))
        }
        // A conversion REFUSAL is malformed reduction input, not a disagreement
        // between the two types -- the same distinction the declared-type path
        // makes, and made here rather than rediscovered later.
        DefEqOutcome::Refused { side, refusal, .. } => Err(Verdict::Rejected(
            AdmissionRejection::BodyConversionRefused {
                name: name.clone(),
                side,
                refusal: Box::new(refusal),
            },
        )),
        DefEqOutcome::Deferred { need, .. } => {
            Err(Verdict::Deferred(AdmissionDeferred::BodyConversion {
                name: name.clone(),
                need: Box::new(need),
            }))
        }
        DefEqOutcome::Inconclusive(stop) => {
            Err(Verdict::Inconclusive(AdmissionStop::BodyConversion {
                name: name.clone(),
                stop: Box::new(stop),
            }))
        }
        DefEqOutcome::InternalFault(fault) => {
            Err(Verdict::InternalFault(AdmissionFault::BodyConversion {
                name: name.clone(),
                fault: Box::new(fault),
            }))
        }
    }
}

fn stopped_err(name: &WireName, phase: AdmissionPhase) -> Verdict {
    stopped(name, phase)
}
