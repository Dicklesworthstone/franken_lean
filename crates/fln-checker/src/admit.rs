//! KR-970 … KR-973 — the declaration-admission preamble, and the first surface in
//! this crate that turns inference into a **verdict**.
//!
//! Every earlier `franken_lean-gii` slice built a component: terms, universes,
//! weak-head reduction, quick and slow definitional equality, the constant
//! environment, Nat and String reduction, eta, and inference KR-100 … KR-112.
//! Each of the three inference slices named declaration admission as the thing
//! outside its scope. This module is that thing: first for the common preamble
//! and body rules, then for atomic non-safe mutual definitions and the fixed
//! four-row quotient initializer:
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
//! # KR-978 — the unchecked door, and why this crate satisfies it INVERTED
//!
//! The judgment inventory states KR-978 as a negative: *every admitted
//! declaration passed the one authority; nothing entered unchecked.* For
//! `fln-kernel` that is a claim about a GATE — its environment can only be
//! extended through `check`, so the door is guarded.
//!
//! **This crate has no such gate and must not have one.**
//! `ConstantEnvironment::build` takes declarations and a budget. It does not
//! take a [`Verdict`], an [`Admission`], or anything `admit` produces, and
//! `environment.rs` does not name those types at all. So a caller may build a
//! checker environment containing declarations this checker would REJECT, and
//! nothing here stops them.
//!
//! That is FL-INV-02 and not an oversight. If `build` required a verdict, this
//! crate would become a second admission authority — the precise thing the
//! invariant forbids. **KR-978 holds here not because the door is guarded but
//! because there is no door: this crate has no admission authority to leave
//! unchecked.**
//!
//! The direction matters and is easy to get backwards. `the_admission_verdict_is_not_a_capability`
//! covers a verdict being laundered OUT; `kr978_the_environment_does_not_require_a_verdict`
//! covers the converse, which is the half KR-978 names — nothing fails on the day
//! someone "improves" `build` to demand an `Admission`, which would read like
//! tightening a safety property while actually violating the invariant.
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
//! standalone inductive, constructor, recursor, or quotient row has a preamble
//! this entry point can check but belongs to a block it cannot reconstruct, so
//! a preamble-passing row is [`Verdict::Deferred`] — **not** rejected, which
//! would be a false verdict, and not admitted, which would be a worse one.
//! [`admit_quotient`] is the distinct complete-unit entry point for quotient
//! initialization.
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
    QuickDefEqBudget, QuickDefEqFault, QuickDefEqLimit, QuickDefEqSide, QuickDefEqStop,
    def_eq_with,
};
use crate::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, ConstantSafety,
    DefinitionBody, DefinitionSafety, EnvironmentBudget, EnvironmentFault, EnvironmentOutcome,
    EnvironmentRefusal, EnvironmentStop, QuotientKind,
};
use crate::infer::{
    InferenceBudget, InferenceContext, InferenceContextRefusal, InferenceDeferred, InferenceFault,
    InferenceMode, InferenceOutcome, InferenceRefusal, InferenceStop, infer_with,
};
use crate::universe::{NormalNode, normalize};
use crate::whnf::{WhnfBudget, WhnfFault, WhnfOutcome, WhnfRefusal, WhnfStop, whnf_with};
use std::collections::BTreeSet;

use crate::wire::{
    BinderStyle, ExprId, ExprNode, LevelId, LevelNode, NamePart, WireExpr, WireLevel, WireName,
};

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
    /// `ConstantKind` and hardcodes `body: None`, so a caller can build a
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
    /// KR-977 — the peers-only predeclared environment would not build.
    ///
    /// A FAULT and not a rejection: by the time this runs, KR-977a's shape rules
    /// have already established that the block is well formed and its members
    /// distinct, so a failure here is this module's defect rather than bad input.
    PredeclarationUnbuildable { name: WireName },
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
/// An enum rather than an untyped success bit so every new admission ground
/// makes exhaustive callers fail to compile until they classify its authority.
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
    /// KR-950..954 — the fixed quotient primitive rows and their required
    /// equality prelude were reconstructed and compared independently.
    QuotientPrimitiveChecked,
    /// KR-600..803, bounded ground — one safe, single, non-nested,
    /// parameter-free `Type` inductive and its bounded constructor telescopes,
    /// recursor, and computation rules were reconstructed from checker-owned
    /// rows. The current ground permits only direct self-recursive fields;
    /// other inductive shapes remain deferred, never accepted under this
    /// ground.
    InductiveNonrecursiveChecked,
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
    cancelled: &mut dyn FnMut() -> bool,
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
    cancelled: &mut dyn FnMut() -> bool,
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

/// KR-973 and the declaration-kind dispatch boundary.
///
/// The `match` is exhaustive over `ConstantKind` on purpose, so adding or moving
/// a declaration kind is a compile error here rather than a silent behaviour
/// change somewhere else.
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
        // reach is a branch no mutation can kill. `ConstantDeclaration` has no
        // public field; `header` hardcodes `body: None`, while every
        // body-bearing constructor hardcodes a non-Axiom kind. So no caller can
        // hand this rule an axiom with a body. The type already holds the law,
        // and writing it again here would read as diligence while testing
        // nothing.
        // `an_axiom_cannot_be_constructed_with_a_body` binds that measurement,
        // so any constructor that can pair Axiom with a body fails rather than
        // quietly making this false.
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
            let Some(body) = declaration.body_value() else {
                return Verdict::Rejected(AdmissionRejection::DeclarationCarriesNoBody {
                    name: name.clone(),
                    kind,
                });
            };
            match body_matches_declared_type(
                environment,
                name,
                declaration,
                body,
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

// ---------------------------------------------------------------- KR-977

/// KR-977 — why a mutual BLOCK was refused, as distinct from why one member was.
///
/// Block-level defects are properties of the set, so none of them names a
/// verdict: there is no member whose own admission failed. A member whose
/// admission failed is a different outcome entirely, and [`BlockVerdict`] keeps
/// the two apart.
#[derive(Debug, PartialEq, Eq)]
pub enum BlockRejection {
    /// KR-977a — a mutual block with no members. The empty block is not a
    /// degenerate success: nothing has been checked, so nothing is admitted.
    EmptyBlock,
    /// KR-977a — a member appears twice in the supplied block.
    RepeatedMember {
        member: WireName,
        first: usize,
        second: usize,
    },
    /// KR-977a — a member carries no mutual list, so it is not part of a block
    /// at all and was supplied to a block entry point by mistake.
    MemberDeclaresNoBlock { member: WireName },
    /// KR-977a — membership is not symmetric: this member's mutual list differs
    /// from the block actually supplied. Membership is a property of the SET, so
    /// a per-declaration opinion that disagrees with its peers is a defect rather
    /// than a preference.
    AsymmetricMembership { member: WireName },
    /// KR-977b — the block's members do not share one safety class.
    NonUniformSafety {
        member: WireName,
        expected: Quarantine,
        found: Quarantine,
    },
    /// KR-977b — **mutual definitions are unsafe-only.** A block whose members
    /// are all ordinary safe definitions is refused: mutual recursion is admitted
    /// on the strength of the quarantine, never on the strength of a check this
    /// checker has not performed.
    SafeBlock { member: WireName },
}

/// The observation that a whole mutual block passed KR-977.
///
/// Same non-capability discipline as [`Admission`]: no public constructor, no
/// public field, no `Clone`, and no conversion out.
#[derive(Debug, PartialEq, Eq)]
pub struct BlockAdmission {
    members: Vec<WireName>,
    ground: AdmissionGround,
}

impl BlockAdmission {
    /// Every member this observation covers, in the order supplied.
    pub fn members(&self) -> &[WireName] {
        &self.members
    }

    /// Which quarantine the block landed in. Never an ordinary ground — KR-977b
    /// refuses a safe block, so a mutual admission is a quarantined one by rule.
    pub const fn ground(&self) -> AdmissionGround {
        self.ground
    }

    pub const fn schema(&self) -> &'static str {
        ADMISSION_SCHEMA
    }
}

/// What this checker observed about one mutual block.
///
/// The four `Member*` arms exist instead of one "a member failed" arm because
/// FL-INV-07 distinguishes a member that was REJECTED from one that DEFERRED,
/// ran out of resources, or faulted — and collapsing them at the block level
/// would throw that distinction away at exactly the layer a caller consults.
#[derive(Debug, PartialEq, Eq)]
pub enum BlockVerdict {
    Admitted(BlockAdmission),
    /// A property of the SET failed. No member's own admission is implicated.
    Rejected(BlockRejection),
    MemberRejected {
        member: WireName,
        rejection: Box<AdmissionRejection>,
    },
    MemberDeferred {
        member: WireName,
        deferred: Box<AdmissionDeferred>,
    },
    MemberInconclusive {
        member: WireName,
        stop: Box<AdmissionStop>,
    },
    MemberFault {
        member: WireName,
        fault: Box<AdmissionFault>,
    },
}

impl BlockVerdict {
    pub const fn is_admitted(&self) -> bool {
        matches!(self, BlockVerdict::Admitted(_))
    }

    /// The three arms that are not decisions, at the block layer.
    ///
    /// `MemberRejected` is a decision; the other three member arms are not, and
    /// a caller must not fold them together — the same reason
    /// [`Verdict::is_inconclusive_family`] exists one layer down.
    pub const fn is_inconclusive_family(&self) -> bool {
        matches!(
            self,
            BlockVerdict::MemberDeferred { .. }
                | BlockVerdict::MemberInconclusive { .. }
                | BlockVerdict::MemberFault { .. }
        )
    }
}

/// Run KR-977 over a mutual block.
///
/// # Atomicity, and an honest note about what it costs here
///
/// The bead asked that a refused block admit NO member. That holds, and it holds
/// **by construction rather than by a rollback**: `admit_block` takes
/// `&ConstantEnvironment` and returns an observation, exactly as `admit` does —
/// there is no environment mutation anywhere in this module to undo. So the
/// property is real and the mechanism protecting it is the signature.
/// `kr977_a_refused_block_admits_no_member` asserts it anyway, and the value of
/// that cell is prospective: it fails on the day admission becomes stateful,
/// which is the only day the property could be lost.
pub fn admit_block(
    environment: &ConstantEnvironment,
    block: &[ConstantEntry],
    budget: AdmissionBudget,
) -> BlockVerdict {
    admit_block_with(environment, block, budget, || false)
}

/// [`admit_block`], with a cancellation poll shared by every member.
pub fn admit_block_with(
    environment: &ConstantEnvironment,
    block: &[ConstantEntry],
    budget: AdmissionBudget,
    mut cancelled: impl FnMut() -> bool,
) -> BlockVerdict {
    // KR-977a — the block's own shape, checked BEFORE any member is admitted.
    // A block that is not a block cannot have its members judged as one, and
    // spending a full body check per member first would report the expensive
    // cause rather than the real one.
    if let Err(rejection) = block_shape(block) {
        return BlockVerdict::Rejected(rejection);
    }

    // KR-977b — one safety class, and not the safe one.
    if let Err(rejection) = block_safety(block) {
        return BlockVerdict::Rejected(rejection);
    }

    // KR-970 for the WHOLE block, against the BASE environment, before anything
    // is predeclared.
    //
    // This ordering is a repair, and the defect it fixes was found by a gut
    // mutant rather than by reading. Predeclaring member i's peers puts those
    // peers' names in an environment that already contains the base; if ANY
    // member collides with the base, that duplicate appears while checking a
    // DIFFERENT member, and the collision surfaced as
    // `PredeclarationUnbuildable` blaming the wrong member -- an internal fault
    // for what is plainly untrusted input, which is the FL-INV-07 line this
    // module exists to hold. Checking every member up front means a collision is
    // reported as KR-970, on the member that actually collides, and
    // predeclaration never sees a duplicate at all.
    for entry in block {
        if environment.find(entry.name()).is_some() {
            return BlockVerdict::MemberRejected {
                member: entry.name().clone(),
                rejection: Box::new(AdmissionRejection::NameAlreadyDeclared {
                    name: entry.name().clone(),
                }),
            };
        }
    }

    // Every member is admitted under the ordinary rules. The block's verdict is
    // the conjunction: one member short of admitted and the block is not
    // admitted, with that member's own outcome carried at its own FL-INV-07
    // class rather than flattened.
    let mut members = Vec::new();
    for (index, entry) in block.iter().enumerate() {
        // KR-977's predeclaration half. Each member is checked in an environment
        // holding its PEERS' headers -- name and declared type, never a body, so
        // a peer can be referenced but not unfolded, and a body is checked
        // against declared types rather than against other bodies.
        //
        // PEERS-ONLY rather than the whole block, and this is the load-bearing
        // detail. Predeclaring every member INCLUDING self would put each member
        // in its own environment and KR-970 -- one name, one constant -- would
        // refuse every one of them for colliding with itself. Excluding self
        // leaves KR-970 firing correctly against the base environment, with no
        // flag, no skip-list, and no weakening of the rule.
        let scoped = match predeclare_peers(environment, block, index) {
            Ok(scoped) => scoped,
            Err(()) => {
                return BlockVerdict::MemberFault {
                    member: entry.name().clone(),
                    fault: Box::new(AdmissionFault::PredeclarationUnbuildable {
                        name: entry.name().clone(),
                    }),
                };
            }
        };
        match admit_with(&scoped, entry, budget, &mut cancelled) {
            Verdict::Admitted(admission) => members.push(admission.name().clone()),
            Verdict::Rejected(rejection) => {
                return BlockVerdict::MemberRejected {
                    member: entry.name().clone(),
                    rejection: Box::new(rejection),
                };
            }
            Verdict::Deferred(deferred) => {
                return BlockVerdict::MemberDeferred {
                    member: entry.name().clone(),
                    deferred: Box::new(deferred),
                };
            }
            Verdict::Inconclusive(stop) => {
                return BlockVerdict::MemberInconclusive {
                    member: entry.name().clone(),
                    stop: Box::new(stop),
                };
            }
            Verdict::InternalFault(fault) => {
                return BlockVerdict::MemberFault {
                    member: entry.name().clone(),
                    fault: Box::new(fault),
                };
            }
        }
    }

    // KR-977b already refused a safe block, so this is a quarantine ground by
    // rule rather than by coincidence. Taken from the first member, whose class
    // uniformity `block_safety` has already established.
    let ground = ground_for(
        block
            .first()
            .map(|entry| quarantine_of(entry.declaration()))
            .unwrap_or(Quarantine::None),
        AdmissionGround::BodyCheckedAgainstDeclaredType,
    );
    BlockVerdict::Admitted(BlockAdmission { members, ground })
}

// ---------------------------------------------------------------- KR-950..954

/// A completed independent observation over the four primitive quotient rows.
///
/// Like [`Admission`] and [`BlockAdmission`], this is evidence and not a
/// publication capability: its fields are private and it cannot be cloned or
/// converted into an environment entry.
#[derive(Debug, PartialEq, Eq)]
pub struct QuotientAdmission {
    members: Vec<WireName>,
}

impl QuotientAdmission {
    pub fn members(&self) -> &[WireName] {
        &self.members
    }

    pub const fn ground(&self) -> AdmissionGround {
        AdmissionGround::QuotientPrimitiveChecked
    }

    pub const fn schema(&self) -> &'static str {
        ADMISSION_SCHEMA
    }
}

/// A completed rejection of quotient initialization.
#[derive(Debug, PartialEq, Eq)]
pub enum QuotientRejection {
    EqualityTypeMissing,
    EqualityTypeShape,
    EqualityConstructorMissing,
    EqualityConstructorShape,
    DeclarationCount { observed: usize },
    DeclarationMissing { kind: QuotientKind },
    NameAlreadyDeclared { name: WireName },
    UnexpectedLevelParameters { name: WireName },
    UnexpectedType { name: WireName },
}

/// The independent quotient judgment's typed outcomes.
#[derive(Debug, PartialEq, Eq)]
pub enum QuotientVerdict {
    Admitted(QuotientAdmission),
    Rejected(QuotientRejection),
    Inconclusive(QuickDefEqStop),
    InternalFault(QuotientFault),
}

#[derive(Debug, PartialEq, Eq)]
pub enum QuotientFault {
    Structural(QuickDefEqFault),
    ExpectedArenaOverflow,
}

impl QuotientVerdict {
    pub const fn is_admitted(&self) -> bool {
        matches!(self, Self::Admitted(_))
    }

    pub const fn is_inconclusive_family(&self) -> bool {
        matches!(self, Self::Inconclusive(_) | Self::InternalFault(_))
    }
}

fn checker_atom(value: &str) -> WireName {
    WireName::from_parts(vec![NamePart::Text(value.to_owned())])
}

fn checker_child(parent: &WireName, value: &str) -> WireName {
    let mut parts = parent.parts().to_vec();
    parts.push(NamePart::Text(value.to_owned()));
    WireName::from_parts(parts)
}

struct StructuralTermBuilder {
    nodes: Vec<ExprNode>,
    levels: Vec<LevelNode>,
    overflowed: bool,
}

impl StructuralTermBuilder {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            levels: Vec::new(),
            overflowed: false,
        }
    }

    fn level(&mut self, node: LevelNode) -> LevelId {
        let id = match LevelId::from_index(self.levels.len()) {
            Some(id) => id,
            None => {
                self.overflowed = true;
                LevelId::ZERO
            }
        };
        self.levels.push(node);
        id
    }

    fn expression(&mut self, node: ExprNode) -> ExprId {
        let id = match ExprId::from_index(self.nodes.len()) {
            Some(id) => id,
            None => {
                self.overflowed = true;
                ExprId::ZERO
            }
        };
        self.nodes.push(node);
        id
    }

    fn shifted_level_id(offset: usize, id: LevelId, source_len: usize) -> Option<LevelId> {
        (id.index() < source_len)
            .then(|| offset.checked_add(id.index()))
            .flatten()
            .and_then(LevelId::from_index)
    }

    fn shifted_expr_id(offset: usize, id: ExprId, source_len: usize) -> Option<ExprId> {
        (id.index() < source_len)
            .then(|| offset.checked_add(id.index()))
            .flatten()
            .and_then(ExprId::from_index)
    }

    /// Import the source prefix containing `root`, retaining de Bruijn indexes.
    /// Wire arenas are backward-only, so a root can reference no expression
    /// beyond that prefix. The caller has already bounded the conservative
    /// imported size before this allocation starts.
    fn import(&mut self, source: &WireExpr, root: ExprId) -> Option<ExprId> {
        let expression_count = root.index().checked_add(1)?;
        if expression_count > source.nodes().len() {
            return None;
        }
        let level_offset = self.levels.len();
        let level_count = source.levels().len();
        for (index, node) in source.levels().iter().enumerate() {
            let shifted = match node {
                LevelNode::Zero => LevelNode::Zero,
                LevelNode::Succ(child) if child.index() < index => {
                    LevelNode::Succ(Self::shifted_level_id(level_offset, *child, level_count)?)
                }
                LevelNode::Max(left, right) if left.index() < index && right.index() < index => {
                    LevelNode::Max(
                        Self::shifted_level_id(level_offset, *left, level_count)?,
                        Self::shifted_level_id(level_offset, *right, level_count)?,
                    )
                }
                LevelNode::IMax(left, right) if left.index() < index && right.index() < index => {
                    LevelNode::IMax(
                        Self::shifted_level_id(level_offset, *left, level_count)?,
                        Self::shifted_level_id(level_offset, *right, level_count)?,
                    )
                }
                LevelNode::Parameter(name) => LevelNode::Parameter(name.clone()),
                LevelNode::Meta(name) => LevelNode::Meta(name.clone()),
                _ => return None,
            };
            self.level(shifted);
        }

        let expression_offset = self.nodes.len();
        let shift_expr = |id| Self::shifted_expr_id(expression_offset, id, expression_count);
        let shift_level = |id| Self::shifted_level_id(level_offset, id, level_count);
        for (index, node) in source.nodes().iter().take(expression_count).enumerate() {
            let child = |id: ExprId| (id.index() < index).then_some(id).and_then(shift_expr);
            let shifted = match node {
                ExprNode::Bound { index } => ExprNode::Bound { index: *index },
                ExprNode::Free { name } => ExprNode::Free { name: name.clone() },
                ExprNode::Meta { name } => ExprNode::Meta { name: name.clone() },
                ExprNode::Sort { level } => ExprNode::Sort {
                    level: shift_level(*level)?,
                },
                ExprNode::Constant { name, levels } => ExprNode::Constant {
                    name: name.clone(),
                    levels: levels
                        .iter()
                        .map(|level| shift_level(*level))
                        .collect::<Option<Vec<_>>>()?,
                },
                ExprNode::Apply { function, argument } => ExprNode::Apply {
                    function: child(*function)?,
                    argument: child(*argument)?,
                },
                ExprNode::Lambda {
                    binder_name,
                    binder_type,
                    body,
                    style,
                } => ExprNode::Lambda {
                    binder_name: binder_name.clone(),
                    binder_type: child(*binder_type)?,
                    body: child(*body)?,
                    style: *style,
                },
                ExprNode::Forall {
                    binder_name,
                    binder_type,
                    body,
                    style,
                } => ExprNode::Forall {
                    binder_name: binder_name.clone(),
                    binder_type: child(*binder_type)?,
                    body: child(*body)?,
                    style: *style,
                },
                ExprNode::Let {
                    declaration_name,
                    type_,
                    value,
                    body,
                    non_dependent,
                } => ExprNode::Let {
                    declaration_name: declaration_name.clone(),
                    type_: child(*type_)?,
                    value: child(*value)?,
                    body: child(*body)?,
                    non_dependent: *non_dependent,
                },
                ExprNode::NatLiteral { limbs_le } => ExprNode::NatLiteral {
                    limbs_le: limbs_le.clone(),
                },
                ExprNode::StringLiteral(text) => ExprNode::StringLiteral(text.clone()),
                ExprNode::Metadata {
                    entries,
                    expression,
                } => ExprNode::Metadata {
                    entries: entries.clone(),
                    expression: child(*expression)?,
                },
                ExprNode::Projection {
                    structure_name,
                    index,
                    expression,
                } => ExprNode::Projection {
                    structure_name: structure_name.clone(),
                    index: *index,
                    expression: child(*expression)?,
                },
            };
            self.expression(shifted);
        }
        Self::shifted_expr_id(expression_offset, root, expression_count)
    }

    fn bvar(&mut self, index: u32) -> ExprId {
        self.expression(ExprNode::Bound { index })
    }

    fn sort_zero(&mut self) -> ExprId {
        let level = self.level(LevelNode::Zero);
        self.expression(ExprNode::Sort { level })
    }

    fn sort_one(&mut self) -> ExprId {
        let zero = self.level(LevelNode::Zero);
        let level = self.level(LevelNode::Succ(zero));
        self.expression(ExprNode::Sort { level })
    }

    fn sort_parameter(&mut self, parameter: &WireName) -> ExprId {
        let level = self.level(LevelNode::Parameter(parameter.clone()));
        self.expression(ExprNode::Sort { level })
    }

    fn sort_successor_parameter(&mut self, parameter: &WireName) -> ExprId {
        let parameter = self.level(LevelNode::Parameter(parameter.clone()));
        let level = self.level(LevelNode::Succ(parameter));
        self.expression(ExprNode::Sort { level })
    }

    fn sort_successor_max_parameters(&mut self, left: &WireName, right: &WireName) -> ExprId {
        let left = self.level(LevelNode::Parameter(left.clone()));
        let right = self.level(LevelNode::Parameter(right.clone()));
        let maximum = self.level(LevelNode::Max(left, right));
        let level = self.level(LevelNode::Succ(maximum));
        self.expression(ExprNode::Sort { level })
    }

    fn constant(&mut self, name: &WireName, parameters: &[WireName]) -> ExprId {
        let levels = parameters
            .iter()
            .map(|parameter| self.level(LevelNode::Parameter(parameter.clone())))
            .collect();
        self.expression(ExprNode::Constant {
            name: name.clone(),
            levels,
        })
    }

    fn apply(&mut self, function: ExprId, argument: ExprId) -> ExprId {
        self.expression(ExprNode::Apply { function, argument })
    }

    fn forall(
        &mut self,
        name: &str,
        style: BinderStyle,
        binder_type: ExprId,
        body: ExprId,
    ) -> ExprId {
        self.expression(ExprNode::Forall {
            binder_name: checker_atom(name),
            binder_type,
            body,
            style,
        })
    }

    fn forall_name(
        &mut self,
        name: &WireName,
        style: BinderStyle,
        binder_type: ExprId,
        body: ExprId,
    ) -> ExprId {
        self.expression(ExprNode::Forall {
            binder_name: name.clone(),
            binder_type,
            body,
            style,
        })
    }

    fn lambda(
        &mut self,
        name: &str,
        style: BinderStyle,
        binder_type: ExprId,
        body: ExprId,
    ) -> ExprId {
        self.expression(ExprNode::Lambda {
            binder_name: checker_atom(name),
            binder_type,
            body,
            style,
        })
    }

    fn lambda_name(
        &mut self,
        name: &WireName,
        style: BinderStyle,
        binder_type: ExprId,
        body: ExprId,
    ) -> ExprId {
        self.expression(ExprNode::Lambda {
            binder_name: name.clone(),
            binder_type,
            body,
            style,
        })
    }

    fn arrow(&mut self, domain: ExprId, codomain: ExprId) -> ExprId {
        self.forall("a", BinderStyle::Default, domain, codomain)
    }

    fn finish(self, root: ExprId) -> Option<WireExpr> {
        (!self.overflowed).then(|| WireExpr::from_parts(self.nodes, self.levels, root))
    }
}

fn structural_level_equal(
    left: &WireExpr,
    left_root: LevelId,
    right: &WireExpr,
    right_root: LevelId,
    control: &mut StructuralComparisonControl,
    seen: &mut BTreeSet<(LevelId, LevelId)>,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Result<bool, QuickDefEqStop>, QuickDefEqFault> {
    let mut pending = vec![(left_root, right_root)];
    while let Some((left_id, right_id)) = pending.pop() {
        if !seen.insert((left_id, right_id)) {
            continue;
        }
        if let Err(stop) = control.comparison(cancelled) {
            return Ok(Err(stop));
        }
        let left_node = left.level(left_id).ok_or(QuickDefEqFault::Universe {
            left: left_id.index(),
            right: right_id.index(),
            error: crate::universe::UniverseError::InvalidArena,
        })?;
        let right_node = right.level(right_id).ok_or(QuickDefEqFault::Universe {
            left: left_id.index(),
            right: right_id.index(),
            error: crate::universe::UniverseError::InvalidArena,
        })?;
        let mut push = |left_child: LevelId, right_child: LevelId| {
            if left_child.index() >= left_id.index() || right_child.index() >= right_id.index() {
                return Err(QuickDefEqFault::Universe {
                    left: left_id.index(),
                    right: right_id.index(),
                    error: crate::universe::UniverseError::InvalidArena,
                });
            }
            pending.push((left_child, right_child));
            Ok(())
        };
        match (left_node, right_node) {
            (LevelNode::Zero, LevelNode::Zero) => {}
            (LevelNode::Parameter(left), LevelNode::Parameter(right))
            | (LevelNode::Meta(left), LevelNode::Meta(right))
                if left == right => {}
            (LevelNode::Succ(left), LevelNode::Succ(right)) => {
                push(*left, *right)?;
            }
            (LevelNode::Max(ll, lr), LevelNode::Max(rl, rr))
            | (LevelNode::IMax(ll, lr), LevelNode::IMax(rl, rr)) => {
                push(*lr, *rr)?;
                push(*ll, *rl)?;
            }
            _ => return Ok(Ok(false)),
        }
    }
    Ok(Ok(true))
}

struct StructuralComparisonControl {
    budget: QuickDefEqBudget,
    comparisons: u64,
    level_nodes: u64,
    polls: u64,
}

impl StructuralComparisonControl {
    const fn new(budget: QuickDefEqBudget) -> Self {
        Self {
            budget,
            comparisons: 0,
            level_nodes: 0,
            polls: 0,
        }
    }

    fn poll(&mut self, cancelled: &mut dyn FnMut() -> bool) -> Result<(), QuickDefEqStop> {
        self.polls = self.polls.saturating_add(1);
        if cancelled() {
            return Err(QuickDefEqStop::Cancelled {
                polls: self.polls,
                completed_comparisons: self.comparisons,
            });
        }
        Ok(())
    }

    fn comparison(&mut self, cancelled: &mut dyn FnMut() -> bool) -> Result<(), QuickDefEqStop> {
        self.poll(cancelled)?;
        let observed = self.comparisons.saturating_add(1);
        if observed > self.budget.max_comparisons {
            return Err(QuickDefEqStop::Resource {
                limit: QuickDefEqLimit::Comparisons,
                allowed: self.budget.max_comparisons,
                observed,
                completed_comparisons: self.comparisons,
            });
        }
        self.comparisons = observed;
        Ok(())
    }
}

fn structural_expression_equal(
    left: &WireExpr,
    right: &WireExpr,
    control: &mut StructuralComparisonControl,
    compare_binder_styles: bool,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Result<bool, QuickDefEqStop>, QuickDefEqFault> {
    if let Err(stop) = control.poll(cancelled) {
        return Ok(Err(stop));
    }
    let added_level_nodes = u64::try_from(left.levels().len())
        .unwrap_or(u64::MAX)
        .saturating_add(u64::try_from(right.levels().len()).unwrap_or(u64::MAX));
    let observed_level_nodes = control.level_nodes.saturating_add(added_level_nodes);
    if observed_level_nodes > control.budget.max_level_arena_nodes {
        return Ok(Err(QuickDefEqStop::Resource {
            limit: QuickDefEqLimit::LevelArenaNodes,
            allowed: control.budget.max_level_arena_nodes,
            observed: observed_level_nodes,
            completed_comparisons: control.comparisons,
        }));
    }
    control.level_nodes = observed_level_nodes;

    let mut pending = vec![(left.root(), right.root())];
    let mut seen = BTreeSet::new();
    let mut seen_levels = BTreeSet::new();
    while let Some((left_id, right_id)) = pending.pop() {
        if !seen.insert((left_id, right_id)) {
            continue;
        }
        if let Err(stop) = control.comparison(cancelled) {
            return Ok(Err(stop));
        }
        let left_node = left
            .node(left_id)
            .ok_or(QuickDefEqFault::MissingExpression {
                side: QuickDefEqSide::Left,
                index: left_id.index(),
            })?;
        let right_node = right
            .node(right_id)
            .ok_or(QuickDefEqFault::MissingExpression {
                side: QuickDefEqSide::Right,
                index: right_id.index(),
            })?;
        let mut push = |left_child: ExprId, right_child: ExprId| {
            if left_child.index() >= left_id.index() {
                return Err(QuickDefEqFault::NonBackwardExpressionReference {
                    side: QuickDefEqSide::Left,
                    parent: left_id.index(),
                    child: left_child.index(),
                });
            }
            if right_child.index() >= right_id.index() {
                return Err(QuickDefEqFault::NonBackwardExpressionReference {
                    side: QuickDefEqSide::Right,
                    parent: right_id.index(),
                    child: right_child.index(),
                });
            }
            pending.push((left_child, right_child));
            Ok(())
        };

        match (left_node, right_node) {
            (ExprNode::Bound { index: left }, ExprNode::Bound { index: right })
                if left == right => {}
            (ExprNode::Free { name: left }, ExprNode::Free { name: right }) if left == right => {}
            (ExprNode::Meta { name: left }, ExprNode::Meta { name: right }) if left == right => {}
            (ExprNode::Sort { level: left_level }, ExprNode::Sort { level: right_level }) => {
                match structural_level_equal(
                    left,
                    *left_level,
                    right,
                    *right_level,
                    control,
                    &mut seen_levels,
                    cancelled,
                )? {
                    Ok(true) => {}
                    Ok(false) => return Ok(Ok(false)),
                    Err(stop) => return Ok(Err(stop)),
                }
            }
            (
                ExprNode::Constant {
                    name: left_name,
                    levels: left_levels,
                },
                ExprNode::Constant {
                    name: right_name,
                    levels: right_levels,
                },
            ) if left_name == right_name && left_levels.len() == right_levels.len() => {
                for (left_level, right_level) in left_levels.iter().zip(right_levels) {
                    match structural_level_equal(
                        left,
                        *left_level,
                        right,
                        *right_level,
                        control,
                        &mut seen_levels,
                        cancelled,
                    )? {
                        Ok(true) => {}
                        Ok(false) => return Ok(Ok(false)),
                        Err(stop) => return Ok(Err(stop)),
                    }
                }
            }
            (
                ExprNode::Apply {
                    function: left_function,
                    argument: left_argument,
                },
                ExprNode::Apply {
                    function: right_function,
                    argument: right_argument,
                },
            ) => {
                push(*left_argument, *right_argument)?;
                push(*left_function, *right_function)?;
            }
            (
                ExprNode::Lambda {
                    binder_type: left_type,
                    body: left_body,
                    style: left_style,
                    ..
                },
                ExprNode::Lambda {
                    binder_type: right_type,
                    body: right_body,
                    style: right_style,
                    ..
                },
            ) if !compare_binder_styles || left_style == right_style => {
                push(*left_body, *right_body)?;
                push(*left_type, *right_type)?;
            }
            (
                ExprNode::Forall {
                    binder_type: left_type,
                    body: left_body,
                    style: left_style,
                    ..
                },
                ExprNode::Forall {
                    binder_type: right_type,
                    body: right_body,
                    style: right_style,
                    ..
                },
            ) if !compare_binder_styles || left_style == right_style => {
                push(*left_body, *right_body)?;
                push(*left_type, *right_type)?;
            }
            (
                ExprNode::Let {
                    type_: left_type,
                    value: left_value,
                    body: left_body,
                    ..
                },
                ExprNode::Let {
                    type_: right_type,
                    value: right_value,
                    body: right_body,
                    ..
                },
            ) => {
                push(*left_body, *right_body)?;
                push(*left_value, *right_value)?;
                push(*left_type, *right_type)?;
            }
            (
                ExprNode::NatLiteral {
                    limbs_le: left_value,
                },
                ExprNode::NatLiteral {
                    limbs_le: right_value,
                },
            ) if left_value == right_value => {}
            (ExprNode::StringLiteral(left), ExprNode::StringLiteral(right)) if left == right => {}
            (
                ExprNode::Metadata {
                    expression: left_expression,
                    ..
                },
                ExprNode::Metadata {
                    expression: right_expression,
                    ..
                },
            ) => push(*left_expression, *right_expression)?,
            (
                ExprNode::Projection {
                    structure_name: left_structure,
                    index: left_index,
                    expression: left_expression,
                },
                ExprNode::Projection {
                    structure_name: right_structure,
                    index: right_index,
                    expression: right_expression,
                },
            ) if left_structure == right_structure && left_index == right_index => {
                push(*left_expression, *right_expression)?;
            }
            _ => return Ok(Ok(false)),
        }
    }
    Ok(Ok(true))
}

// ------------------------------------------------------- KR-600..803 (bounded inductive ground)

/// Maximum number of constructors reconstructed by the bounded independent
/// inductive judgment. Expected recursor rules are quadratic in this count;
/// larger but otherwise valid blocks remain typed deferrals.
pub const MAX_NONRECURSIVE_CONSTRUCTORS: usize = 32;

/// Maximum aggregate constructor fields in one independently reconstructed
/// block. This is deliberately a block limit: recursor reconstruction touches
/// every field type in every minor premise and computation rule.
pub const MAX_NONRECURSIVE_FIELDS: usize = 64;

/// Maximum conservative node-and-level upper bound for one reconstructed
/// recursor expression. The builder imports the prefix containing each field
/// type, so this bound is checked before allocating any expected arena.
pub const MAX_INDUCTIVE_EXPECTED_ARENA_UNITS: usize = 262_144;

/// The exact boundary of the independent checker's first inductive ground.
/// These are non-answers: K1 may decide the shape, but this checker does not.
#[derive(Debug, PartialEq, Eq)]
pub enum InductiveSupportLimit {
    DeclarationRows {
        observed: usize,
        limit: usize,
    },
    MultipleTypes {
        observed: usize,
    },
    MutualMetadata,
    UniverseParameters {
        observed: usize,
    },
    Parameters {
        observed: u32,
    },
    Indices {
        observed: u32,
    },
    Nested {
        observed: u32,
    },
    Recursive,
    Reflexive,
    Unsafe,
    ResultUniverse,
    ConstructorCount {
        observed: usize,
        limit: usize,
    },
    FieldCount {
        observed: usize,
        limit: usize,
    },
    ExpectedArenaUnits {
        observed: usize,
        limit: usize,
    },
    MemberPreamble {
        name: WireName,
        requirement: Box<AdmissionDeferred>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub enum InductiveRejection {
    MissingInductive,
    MissingMetadata {
        name: WireName,
    },
    DeclarationCount {
        observed: usize,
        expected: usize,
    },
    ConstructorMissing {
        name: WireName,
    },
    RecursorMissing {
        name: WireName,
    },
    RepeatedConstructor {
        name: WireName,
    },
    NameAlreadyDeclared {
        name: WireName,
    },
    ConstructorShape {
        name: WireName,
    },
    RecursorShape {
        name: WireName,
    },
    MemberPreamble {
        name: WireName,
        rejection: Box<AdmissionRejection>,
    },
    Environment {
        name: WireName,
        refusal: Box<EnvironmentRefusal>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub enum InductiveFault {
    Structural(QuickDefEqFault),
    MemberPreamble {
        name: WireName,
        fault: Box<AdmissionFault>,
    },
    Environment {
        name: WireName,
        fault: Box<EnvironmentFault>,
    },
    UnexpectedMemberAdmission {
        name: WireName,
    },
    ExpectedArenaOverflow,
}

#[derive(Debug, PartialEq, Eq)]
pub enum InductiveStop {
    Structural(QuickDefEqStop),
    MemberPreamble {
        name: WireName,
        stop: Box<AdmissionStop>,
    },
    Environment {
        name: WireName,
        stop: Box<EnvironmentStop>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub struct InductiveAdmission {
    members: Vec<WireName>,
}

impl InductiveAdmission {
    pub fn members(&self) -> &[WireName] {
        &self.members
    }

    pub const fn ground(&self) -> AdmissionGround {
        AdmissionGround::InductiveNonrecursiveChecked
    }

    pub const fn schema(&self) -> &'static str {
        ADMISSION_SCHEMA
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum InductiveVerdict {
    Admitted(InductiveAdmission),
    Rejected(InductiveRejection),
    Deferred(InductiveSupportLimit),
    Inconclusive(InductiveStop),
    InternalFault(InductiveFault),
}

impl InductiveVerdict {
    pub const fn is_admitted(&self) -> bool {
        matches!(self, Self::Admitted(_))
    }

    pub const fn is_inconclusive_family(&self) -> bool {
        matches!(
            self,
            Self::Deferred(_) | Self::Inconclusive(_) | Self::InternalFault(_)
        )
    }
}

fn nonrecursive_inductive_type() -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let root = builder.sort_one();
    builder.finish(root)
}

struct ConstructorField<'a> {
    source: &'a WireExpr,
    name: &'a WireName,
    style: BinderStyle,
    type_root: ExprId,
}

struct CheckedConstructor<'a> {
    name: &'a WireName,
    fields: Vec<ConstructorField<'a>>,
    direct_recursive_fields: Vec<bool>,
}

fn constructor_shape<'a>(
    type_: &'a WireExpr,
    inductive: &WireName,
    expected_fields: usize,
) -> Option<Vec<ConstructorField<'a>>> {
    let mut current = type_.root();
    let mut fields = Vec::new();
    fields.try_reserve_exact(expected_fields).ok()?;
    for _ in 0..expected_fields {
        let ExprNode::Forall {
            binder_name,
            binder_type,
            body,
            style,
        } = type_.node(current)?
        else {
            return None;
        };
        if binder_type.index() >= current.index() || body.index() >= current.index() {
            return None;
        }
        fields.push(ConstructorField {
            source: type_,
            name: binder_name,
            style: *style,
            type_root: *binder_type,
        });
        current = *body;
    }
    matches!(
        type_.node(current),
        Some(ExprNode::Constant { name, levels }) if name == inductive && levels.is_empty()
    )
    .then_some(fields)
}

fn expected_minor_type(
    builder: &mut StructuralTermBuilder,
    constructor: &CheckedConstructor<'_>,
    prior_minors: usize,
) -> Option<ExprId> {
    let field_count = constructor.fields.len();
    let recursive_fields: Vec<usize> = constructor
        .direct_recursive_fields
        .iter()
        .enumerate()
        .filter_map(|(index, direct)| direct.then_some(index))
        .collect();
    let recursive_count = recursive_fields.len();
    let motive_index = u32::try_from(
        field_count
            .checked_add(recursive_count)?
            .checked_add(prior_minors)?,
    )
    .ok()?;
    let motive = builder.bvar(motive_index);
    let mut constructor_application = builder.constant(constructor.name, &[]);
    for index in 0..field_count {
        let field = builder.bvar(
            u32::try_from(
                recursive_count.checked_add(field_count.checked_sub(index.checked_add(1)?)?)?,
            )
            .ok()?,
        );
        constructor_application = builder.apply(constructor_application, field);
    }
    let mut result = builder.apply(motive, constructor_application);
    for (induction_hypothesis_index, field_index) in recursive_fields.iter().enumerate().rev() {
        let motive = builder.bvar(
            u32::try_from(
                field_count
                    .checked_add(induction_hypothesis_index)?
                    .checked_add(prior_minors)?,
            )
            .ok()?,
        );
        let field = builder.bvar(
            u32::try_from(
                induction_hypothesis_index
                    .checked_add(field_count.checked_sub(field_index.checked_add(1)?)?)?,
            )
            .ok()?,
        );
        let induction_hypothesis = builder.apply(motive, field);
        result = builder.forall("ih", BinderStyle::Default, induction_hypothesis, result);
    }
    for field in constructor.fields.iter().rev() {
        let field_type = builder.import(field.source, field.type_root)?;
        result = builder.forall_name(field.name, field.style, field_type, result);
    }
    Some(result)
}

fn nonrecursive_recursor_type(
    inductive: &WireName,
    constructors: &[CheckedConstructor<'_>],
    level_parameter: &WireName,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let inductive_type = builder.constant(inductive, &[]);
    let motive_sort = builder.sort_parameter(level_parameter);
    let motive_type = builder.forall("t", BinderStyle::Default, inductive_type, motive_sort);

    let motive = builder.bvar(u32::try_from(constructors.len()).ok()?.checked_add(1)?);
    let major = builder.bvar(0);
    let mut result = builder.apply(motive, major);
    let major_type = builder.constant(inductive, &[]);
    result = builder.forall("t", BinderStyle::Default, major_type, result);

    for (index, constructor) in constructors.iter().enumerate().rev() {
        let minor_type = expected_minor_type(&mut builder, constructor, index)?;
        result = builder.forall("minor", BinderStyle::Default, minor_type, result);
    }
    let root = builder.forall("motive", BinderStyle::Implicit, motive_type, result);
    builder.finish(root)
}

fn nonrecursive_rule_rhs(
    inductive: &WireName,
    constructors: &[CheckedConstructor<'_>],
    level_parameter: &WireName,
    selected: usize,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let selected_constructor = constructors.get(selected)?;
    let field_count = selected_constructor.fields.len();
    let selected_minor =
        field_count.checked_add(constructors.len().checked_sub(selected.checked_add(1)?)?)?;
    let mut result = builder.bvar(u32::try_from(selected_minor).ok()?);
    for index in 0..field_count {
        let field =
            builder.bvar(u32::try_from(field_count.checked_sub(index.checked_add(1)?)?).ok()?);
        result = builder.apply(result, field);
    }
    for (field_index, direct_recursive) in selected_constructor
        .direct_recursive_fields
        .iter()
        .enumerate()
    {
        if !direct_recursive {
            continue;
        }
        let recursor_name = checker_child(inductive, "rec");
        let mut recursive_call =
            builder.constant(&recursor_name, std::slice::from_ref(level_parameter));
        let motive =
            builder.bvar(u32::try_from(field_count.checked_add(constructors.len())?).ok()?);
        recursive_call = builder.apply(recursive_call, motive);
        for minor_index in 0..constructors.len() {
            let minor = builder.bvar(
                u32::try_from(
                    field_count.checked_add(
                        constructors
                            .len()
                            .checked_sub(minor_index.checked_add(1)?)?,
                    )?,
                )
                .ok()?,
            );
            recursive_call = builder.apply(recursive_call, minor);
        }
        let field = builder
            .bvar(u32::try_from(field_count.checked_sub(field_index.checked_add(1)?)?).ok()?);
        recursive_call = builder.apply(recursive_call, field);
        result = builder.apply(result, recursive_call);
    }
    for field in selected_constructor.fields.iter().rev() {
        let field_type = builder.import(field.source, field.type_root)?;
        result = builder.lambda_name(field.name, field.style, field_type, result);
    }
    for (index, constructor) in constructors.iter().enumerate().rev() {
        let minor_type = expected_minor_type(&mut builder, constructor, index)?;
        result = builder.lambda("minor", BinderStyle::Default, minor_type, result);
    }
    let inductive_type = builder.constant(inductive, &[]);
    let motive_sort = builder.sort_parameter(level_parameter);
    let motive_type = builder.forall("t", BinderStyle::Default, inductive_type, motive_sort);
    let root = builder.lambda("motive", BinderStyle::Default, motive_type, result);
    builder.finish(root)
}

fn bool_inductive_type() -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let root = builder.sort_one();
    builder.finish(root)
}

fn bool_constructor_type() -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let root = builder.constant(&checker_atom("Bool"), &[]);
    builder.finish(root)
}

fn bool_recursor_type(level_parameter: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let bool_type = builder.constant(&checker_atom("Bool"), &[]);
    let motive_sort = builder.sort_parameter(level_parameter);
    let motive_type = builder.forall("t", BinderStyle::Default, bool_type, motive_sort);
    let false_value = builder.constant(&checker_child(&checker_atom("Bool"), "false"), &[]);
    let motive = builder.bvar(0);
    let false_minor = builder.apply(motive, false_value);
    let true_value = builder.constant(&checker_child(&checker_atom("Bool"), "true"), &[]);
    let motive = builder.bvar(1);
    let true_minor = builder.apply(motive, true_value);
    let major_type = builder.constant(&checker_atom("Bool"), &[]);
    let motive = builder.bvar(3);
    let major = builder.bvar(0);
    let mut result = builder.apply(motive, major);
    result = builder.forall("t", BinderStyle::Default, major_type, result);
    result = builder.forall("true", BinderStyle::Default, true_minor, result);
    result = builder.forall("false", BinderStyle::Default, false_minor, result);
    let root = builder.forall("motive", BinderStyle::Implicit, motive_type, result);
    builder.finish(root)
}

fn bool_rule_rhs(level_parameter: &WireName, selected_true: bool) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let bool_type = builder.constant(&checker_atom("Bool"), &[]);
    let motive_sort = builder.sort_parameter(level_parameter);
    let motive_type = builder.forall("t", BinderStyle::Default, bool_type, motive_sort);
    let false_value = builder.constant(&checker_child(&checker_atom("Bool"), "false"), &[]);
    let motive = builder.bvar(0);
    let false_minor = builder.apply(motive, false_value);
    let true_value = builder.constant(&checker_child(&checker_atom("Bool"), "true"), &[]);
    let motive = builder.bvar(1);
    let true_minor = builder.apply(motive, true_value);
    let result = builder.bvar(if selected_true { 0 } else { 1 });
    let result = builder.lambda("true", BinderStyle::Default, true_minor, result);
    let result = builder.lambda("false", BinderStyle::Default, false_minor, result);
    let root = builder.lambda("motive", BinderStyle::Default, motive_type, result);
    builder.finish(root)
}

fn unit_constructor_type() -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let root = builder.constant(&checker_atom("Unit"), &[]);
    builder.finish(root)
}

fn unit_recursor_type(motive_universe: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let unit = builder.constant(&checker_atom("Unit"), &[]);
    let motive_sort = builder.sort_parameter(motive_universe);
    let motive_type = builder.forall("t", BinderStyle::Default, unit, motive_sort);
    let unit = builder.constant(&checker_child(&checker_atom("Unit"), "unit"), &[]);
    let motive = builder.bvar(0);
    let minor = builder.apply(motive, unit);
    let major_type = builder.constant(&checker_atom("Unit"), &[]);
    let motive = builder.bvar(2);
    let major = builder.bvar(0);
    let mut result = builder.apply(motive, major);
    result = builder.forall("t", BinderStyle::Default, major_type, result);
    result = builder.forall("unit", BinderStyle::Default, minor, result);
    let root = builder.forall("motive", BinderStyle::Implicit, motive_type, result);
    builder.finish(root)
}

fn unit_rule_rhs(motive_universe: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let unit = builder.constant(&checker_atom("Unit"), &[]);
    let motive_sort = builder.sort_parameter(motive_universe);
    let motive_type = builder.forall("t", BinderStyle::Default, unit, motive_sort);
    let unit = builder.constant(&checker_child(&checker_atom("Unit"), "unit"), &[]);
    let motive = builder.bvar(0);
    let minor = builder.apply(motive, unit);
    let result = builder.bvar(0);
    let result = builder.lambda("unit", BinderStyle::Default, minor, result);
    let root = builder.lambda("motive", BinderStyle::Default, motive_type, result);
    builder.finish(root)
}

fn sum_application(
    builder: &mut StructuralTermBuilder,
    sum: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
    left: ExprId,
    right: ExprId,
) -> ExprId {
    let sum = builder.constant(sum, &[left_universe.clone(), right_universe.clone()]);
    let sum = builder.apply(sum, left);
    builder.apply(sum, right)
}

fn sum_inductive_type(left_universe: &WireName, right_universe: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let left_type = builder.sort_successor_parameter(left_universe);
    let right_type = builder.sort_successor_parameter(right_universe);
    let result = builder.sort_successor_max_parameters(left_universe, right_universe);
    let result = builder.forall("β", BinderStyle::Default, right_type, result);
    let root = builder.forall("α", BinderStyle::Default, left_type, result);
    builder.finish(root)
}

fn sum_constructor_type(
    sum: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
    left_constructor: bool,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let left_type = builder.sort_successor_parameter(left_universe);
    let right_type = builder.sort_successor_parameter(right_universe);
    let left = builder.bvar(2);
    let right = builder.bvar(1);
    let result = sum_application(
        &mut builder,
        sum,
        left_universe,
        right_universe,
        left,
        right,
    );
    let field = builder.bvar(if left_constructor { 1 } else { 0 });
    let result = builder.forall("val", BinderStyle::Default, field, result);
    let result = builder.forall("β", BinderStyle::Default, right_type, result);
    let root = builder.forall("α", BinderStyle::Default, left_type, result);
    builder.finish(root)
}

fn sum_motive_type(
    builder: &mut StructuralTermBuilder,
    sum: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
    motive_universe: &WireName,
) -> ExprId {
    let left = builder.bvar(1);
    let right = builder.bvar(0);
    let sum = sum_application(builder, sum, left_universe, right_universe, left, right);
    let motive_sort = builder.sort_parameter(motive_universe);
    builder.forall("t", BinderStyle::Default, sum, motive_sort)
}

fn sum_minor_type(
    builder: &mut StructuralTermBuilder,
    sum: &WireName,
    constructor: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
    left_constructor: bool,
    prior_minors: u32,
) -> ExprId {
    let alpha = builder.bvar(3 + prior_minors);
    let beta = builder.bvar(2 + prior_minors);
    let constructor = builder.constant(
        constructor,
        &[left_universe.clone(), right_universe.clone()],
    );
    let constructor = builder.apply(constructor, alpha);
    let constructor = builder.apply(constructor, beta);
    let field = builder.bvar(0);
    let constructor = builder.apply(constructor, field);
    let motive = builder.bvar(1 + prior_minors);
    let result = builder.apply(motive, constructor);
    let field_type = builder.bvar(if left_constructor {
        2 + prior_minors
    } else {
        1 + prior_minors
    });
    let _ = sum;
    builder.forall("val", BinderStyle::Default, field_type, result)
}

fn sum_recursor_type(
    sum: &WireName,
    inl: &WireName,
    inr: &WireName,
    motive_universe: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let left_type = builder.sort_successor_parameter(left_universe);
    let right_type = builder.sort_successor_parameter(right_universe);
    let motive_type = sum_motive_type(
        &mut builder,
        sum,
        left_universe,
        right_universe,
        motive_universe,
    );
    let inl_minor = sum_minor_type(
        &mut builder,
        sum,
        inl,
        left_universe,
        right_universe,
        true,
        0,
    );
    let inr_minor = sum_minor_type(
        &mut builder,
        sum,
        inr,
        left_universe,
        right_universe,
        false,
        1,
    );
    let left = builder.bvar(4);
    let right = builder.bvar(3);
    let major_type = sum_application(
        &mut builder,
        sum,
        left_universe,
        right_universe,
        left,
        right,
    );
    let motive = builder.bvar(3);
    let major = builder.bvar(0);
    let mut result = builder.apply(motive, major);
    result = builder.forall("t", BinderStyle::Default, major_type, result);
    result = builder.forall("inr", BinderStyle::Default, inr_minor, result);
    result = builder.forall("inl", BinderStyle::Default, inl_minor, result);
    result = builder.forall("motive", BinderStyle::Implicit, motive_type, result);
    result = builder.forall("β", BinderStyle::Implicit, right_type, result);
    let root = builder.forall("α", BinderStyle::Implicit, left_type, result);
    builder.finish(root)
}

fn sum_rule_rhs(
    sum: &WireName,
    inl: &WireName,
    inr: &WireName,
    motive_universe: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
    selected_left: bool,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let left_type = builder.sort_successor_parameter(left_universe);
    let right_type = builder.sort_successor_parameter(right_universe);
    let motive_type = sum_motive_type(
        &mut builder,
        sum,
        left_universe,
        right_universe,
        motive_universe,
    );
    let inl_minor = sum_minor_type(
        &mut builder,
        sum,
        inl,
        left_universe,
        right_universe,
        true,
        0,
    );
    let inr_minor = sum_minor_type(
        &mut builder,
        sum,
        inr,
        left_universe,
        right_universe,
        false,
        1,
    );
    let minor = builder.bvar(if selected_left { 2 } else { 1 });
    let field = builder.bvar(0);
    let mut result = builder.apply(minor, field);
    let field_type = builder.bvar(if selected_left { 4 } else { 3 });
    result = builder.lambda("val", BinderStyle::Default, field_type, result);
    result = builder.lambda("inr", BinderStyle::Default, inr_minor, result);
    result = builder.lambda("inl", BinderStyle::Default, inl_minor, result);
    result = builder.lambda("motive", BinderStyle::Default, motive_type, result);
    result = builder.lambda("β", BinderStyle::Default, right_type, result);
    let root = builder.lambda("α", BinderStyle::Default, left_type, result);
    builder.finish(root)
}

fn prod_application(
    builder: &mut StructuralTermBuilder,
    prod: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
    left: ExprId,
    right: ExprId,
) -> ExprId {
    let prod = builder.constant(prod, &[left_universe.clone(), right_universe.clone()]);
    let prod = builder.apply(prod, left);
    builder.apply(prod, right)
}

fn prod_inductive_type(left_universe: &WireName, right_universe: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let left_type = builder.sort_successor_parameter(left_universe);
    let right_type = builder.sort_successor_parameter(right_universe);
    let result = builder.sort_successor_max_parameters(left_universe, right_universe);
    let result = builder.forall("β", BinderStyle::Default, right_type, result);
    let root = builder.forall("α", BinderStyle::Default, left_type, result);
    builder.finish(root)
}

fn prod_constructor_type(
    prod: &WireName,
    constructor: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let left_type = builder.sort_successor_parameter(left_universe);
    let right_type = builder.sort_successor_parameter(right_universe);
    let left = builder.bvar(3);
    let right = builder.bvar(2);
    let result = prod_application(
        &mut builder,
        prod,
        left_universe,
        right_universe,
        left,
        right,
    );
    let second_type = builder.bvar(1);
    let result = builder.forall("snd", BinderStyle::Default, second_type, result);
    let first_type = builder.bvar(1);
    let result = builder.forall("fst", BinderStyle::Default, first_type, result);
    let result = builder.forall("β", BinderStyle::Default, right_type, result);
    let root = builder.forall_name(constructor, BinderStyle::Default, left_type, result);
    builder.finish(root)
}

fn prod_motive_type(
    builder: &mut StructuralTermBuilder,
    prod: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
    motive_universe: &WireName,
) -> ExprId {
    let left = builder.bvar(1);
    let right = builder.bvar(0);
    let prod = prod_application(builder, prod, left_universe, right_universe, left, right);
    let motive_sort = builder.sort_parameter(motive_universe);
    builder.forall("t", BinderStyle::Default, prod, motive_sort)
}

fn prod_minor_type(
    builder: &mut StructuralTermBuilder,
    prod: &WireName,
    constructor: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
) -> ExprId {
    let left = builder.bvar(4);
    let right = builder.bvar(3);
    let constructor = builder.constant(
        constructor,
        &[left_universe.clone(), right_universe.clone()],
    );
    let constructor = builder.apply(constructor, left);
    let constructor = builder.apply(constructor, right);
    let first = builder.bvar(1);
    let second = builder.bvar(0);
    let constructor = builder.apply(constructor, first);
    let constructor = builder.apply(constructor, second);
    let motive = builder.bvar(2);
    let result = builder.apply(motive, constructor);
    let second_type = builder.bvar(2);
    let result = builder.forall("snd", BinderStyle::Default, second_type, result);
    let first_type = builder.bvar(2);
    let result = builder.forall("fst", BinderStyle::Default, first_type, result);
    let _ = prod;
    result
}

fn prod_recursor_type(
    prod: &WireName,
    constructor: &WireName,
    motive_universe: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let left_type = builder.sort_successor_parameter(left_universe);
    let right_type = builder.sort_successor_parameter(right_universe);
    let motive_type = prod_motive_type(
        &mut builder,
        prod,
        left_universe,
        right_universe,
        motive_universe,
    );
    let minor = prod_minor_type(
        &mut builder,
        prod,
        constructor,
        left_universe,
        right_universe,
    );
    let left = builder.bvar(3);
    let right = builder.bvar(2);
    let major_type = prod_application(
        &mut builder,
        prod,
        left_universe,
        right_universe,
        left,
        right,
    );
    let motive = builder.bvar(2);
    let major = builder.bvar(0);
    let result = builder.apply(motive, major);
    let result = builder.forall("t", BinderStyle::Default, major_type, result);
    let result = builder.forall("mk", BinderStyle::Default, minor, result);
    let result = builder.forall("motive", BinderStyle::Implicit, motive_type, result);
    let result = builder.forall("β", BinderStyle::Implicit, right_type, result);
    let root = builder.forall("α", BinderStyle::Implicit, left_type, result);
    builder.finish(root)
}

fn prod_rule_rhs(
    prod: &WireName,
    constructor: &WireName,
    motive_universe: &WireName,
    left_universe: &WireName,
    right_universe: &WireName,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let left_type = builder.sort_successor_parameter(left_universe);
    let right_type = builder.sort_successor_parameter(right_universe);
    let motive_type = prod_motive_type(
        &mut builder,
        prod,
        left_universe,
        right_universe,
        motive_universe,
    );
    let minor = prod_minor_type(
        &mut builder,
        prod,
        constructor,
        left_universe,
        right_universe,
    );
    let minor_value = builder.bvar(2);
    let first = builder.bvar(1);
    let result = builder.apply(minor_value, first);
    let second = builder.bvar(0);
    let result = builder.apply(result, second);
    let second_type = builder.bvar(3);
    let result = builder.lambda("snd", BinderStyle::Default, second_type, result);
    let first_type = builder.bvar(3);
    let result = builder.lambda("fst", BinderStyle::Default, first_type, result);
    let result = builder.lambda("mk", BinderStyle::Default, minor, result);
    let result = builder.lambda("motive", BinderStyle::Default, motive_type, result);
    let result = builder.lambda("β", BinderStyle::Default, right_type, result);
    let root = builder.lambda("α", BinderStyle::Default, left_type, result);
    builder.finish(root)
}

fn punit_constructor_type(universe: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let root = builder.constant(&checker_atom("PUnit"), std::slice::from_ref(universe));
    builder.finish(root)
}

fn punit_recursor_type(motive_universe: &WireName, family_universe: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let punit = builder.constant(
        &checker_atom("PUnit"),
        std::slice::from_ref(family_universe),
    );
    let motive_sort = builder.sort_parameter(motive_universe);
    let motive_type = builder.forall("t", BinderStyle::Default, punit, motive_sort);
    let unit = builder.constant(
        &checker_child(&checker_atom("PUnit"), "unit"),
        std::slice::from_ref(family_universe),
    );
    let motive = builder.bvar(0);
    let minor = builder.apply(motive, unit);
    let major_type = builder.constant(
        &checker_atom("PUnit"),
        std::slice::from_ref(family_universe),
    );
    let motive = builder.bvar(2);
    let major = builder.bvar(0);
    let mut result = builder.apply(motive, major);
    result = builder.forall("t", BinderStyle::Default, major_type, result);
    result = builder.forall("unit", BinderStyle::Default, minor, result);
    let root = builder.forall("motive", BinderStyle::Implicit, motive_type, result);
    builder.finish(root)
}

fn punit_rule_rhs(motive_universe: &WireName, family_universe: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let punit = builder.constant(
        &checker_atom("PUnit"),
        std::slice::from_ref(family_universe),
    );
    let motive_sort = builder.sort_parameter(motive_universe);
    let motive_type = builder.forall("t", BinderStyle::Default, punit, motive_sort);
    let unit = builder.constant(
        &checker_child(&checker_atom("PUnit"), "unit"),
        std::slice::from_ref(family_universe),
    );
    let motive = builder.bvar(0);
    let minor = builder.apply(motive, unit);
    let result = builder.bvar(0);
    let result = builder.lambda("unit", BinderStyle::Default, minor, result);
    let root = builder.lambda("motive", BinderStyle::Default, motive_type, result);
    builder.finish(root)
}

fn option_application(
    builder: &mut StructuralTermBuilder,
    option: &WireName,
    universe: &WireName,
    parameter: ExprId,
) -> ExprId {
    let option = builder.constant(option, std::slice::from_ref(universe));
    builder.apply(option, parameter)
}

fn option_inductive_type(universe: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let parameter_type = builder.sort_successor_parameter(universe);
    let result = builder.sort_successor_parameter(universe);
    let root = builder.forall("α", BinderStyle::Default, parameter_type, result);
    builder.finish(root)
}

fn option_constructor_type(
    option: &WireName,
    constructor: &WireName,
    universe: &WireName,
    has_field: bool,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let parameter_type = builder.sort_successor_parameter(universe);
    let parameter = builder.bvar(0);
    let mut result = option_application(&mut builder, option, universe, parameter);
    if has_field {
        let field_type = builder.bvar(0);
        let parameter = builder.bvar(1);
        result = option_application(&mut builder, option, universe, parameter);
        result = builder.forall("value", BinderStyle::Default, field_type, result);
    }
    let root = builder.forall_name(constructor, BinderStyle::Default, parameter_type, result);
    builder.finish(root)
}

fn option_minor_type(
    builder: &mut StructuralTermBuilder,
    option: &WireName,
    constructor: &WireName,
    universe: &WireName,
    has_field: bool,
) -> ExprId {
    let constructor = builder.constant(constructor, std::slice::from_ref(universe));
    let parameter = builder.bvar(if has_field { 3 } else { 1 });
    let constructor = builder.apply(constructor, parameter);
    let constructor = if has_field {
        let value = builder.bvar(0);
        builder.apply(constructor, value)
    } else {
        constructor
    };
    let motive = builder.bvar(if has_field { 2 } else { 0 });
    let mut result = builder.apply(motive, constructor);
    if has_field {
        let parameter = builder.bvar(2);
        result = builder.forall("value", BinderStyle::Default, parameter, result);
    }
    let _ = option;
    result
}

fn option_recursor_type(
    option: &WireName,
    none: &WireName,
    some: &WireName,
    motive_universe: &WireName,
    option_universe: &WireName,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let parameter_type = builder.sort_successor_parameter(option_universe);
    let parameter = builder.bvar(0);
    let inductive = option_application(&mut builder, option, option_universe, parameter);
    let motive_sort = builder.sort_parameter(motive_universe);
    let motive_type = builder.forall("t", BinderStyle::Default, inductive, motive_sort);

    let none_minor = option_minor_type(&mut builder, option, none, option_universe, false);
    let some_minor = option_minor_type(&mut builder, option, some, option_universe, true);
    let parameter = builder.bvar(3);
    let major_type = option_application(&mut builder, option, option_universe, parameter);
    let major = builder.bvar(0);
    let motive = builder.bvar(3);
    let mut result = builder.apply(motive, major);
    result = builder.forall("t", BinderStyle::Default, major_type, result);
    result = builder.forall("some", BinderStyle::Default, some_minor, result);
    result = builder.forall("none", BinderStyle::Default, none_minor, result);
    result = builder.forall("motive", BinderStyle::Implicit, motive_type, result);
    let root = builder.forall("α", BinderStyle::Implicit, parameter_type, result);
    builder.finish(root)
}

fn option_rule_rhs(
    option: &WireName,
    none: &WireName,
    some: &WireName,
    motive_universe: &WireName,
    option_universe: &WireName,
    selected_some: bool,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let parameter_type = builder.sort_successor_parameter(option_universe);
    let parameter = builder.bvar(0);
    let inductive = option_application(&mut builder, option, option_universe, parameter);
    let motive_sort = builder.sort_parameter(motive_universe);
    let motive_type = builder.forall("t", BinderStyle::Default, inductive, motive_sort);
    let none_minor = option_minor_type(&mut builder, option, none, option_universe, false);
    let some_minor = option_minor_type(&mut builder, option, some, option_universe, true);
    let mut result = builder.bvar(1);
    if selected_some {
        let value = builder.bvar(0);
        result = builder.apply(result, value);
        let parameter = builder.bvar(2);
        result = builder.lambda("value", BinderStyle::Default, parameter, result);
    }
    result = builder.lambda("some", BinderStyle::Default, some_minor, result);
    result = builder.lambda("none", BinderStyle::Default, none_minor, result);
    result = builder.lambda("motive", BinderStyle::Default, motive_type, result);
    let root = builder.lambda("α", BinderStyle::Default, parameter_type, result);
    builder.finish(root)
}

fn empty_recursor_type(empty: &WireName, motive_universe: &WireName) -> Option<WireExpr> {
    // Both real empty families met so far (`Init.Empty`, and `Init.False`
    // sharing this helper) bind the motive binder Default.
    empty_recursor_type_at_levels(empty, motive_universe, &[], BinderStyle::Default)
}

fn empty_recursor_type_at_levels(
    empty: &WireName,
    motive_universe: &WireName,
    inductive_universes: &[WireName],
    motive_style: BinderStyle,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let empty_type = builder.constant(empty, inductive_universes);
    let motive_sort = builder.sort_parameter(motive_universe);
    let motive_type = builder.forall("t", BinderStyle::Default, empty_type, motive_sort);
    let motive = builder.bvar(1);
    let major = builder.bvar(0);
    let mut result = builder.apply(motive, major);
    let major_type = builder.constant(empty, inductive_universes);
    result = builder.forall("t", BinderStyle::Default, major_type, result);
    // The pin binds this eliminator's motive Default on `Init.Empty` itself;
    // `PEmpty` currently asserts the Implicit spelling and has not yet been
    // confirmed against real bytes, so the style stays caller-chosen.
    let root = builder.forall("motive", motive_style, motive_type, result);
    builder.finish(root)
}

fn or_application(
    builder: &mut StructuralTermBuilder,
    or_name: &WireName,
    left: ExprId,
    right: ExprId,
) -> ExprId {
    let or_name = builder.constant(or_name, &[]);
    let applied_left = builder.apply(or_name, left);
    builder.apply(applied_left, right)
}

fn or_inductive_type() -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let proposition = builder.sort_zero();
    let result = builder.sort_zero();
    let result = builder.forall("b", BinderStyle::Default, proposition, result);
    let root = builder.forall("a", BinderStyle::Default, proposition, result);
    builder.finish(root)
}

fn or_constructor_type(or_name: &WireName, constructor: &WireName, left: bool) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let proposition = builder.sort_zero();
    let field = builder.bvar(if left { 1 } else { 0 });
    let left_parameter = builder.bvar(2);
    let right_parameter = builder.bvar(1);
    let result = or_application(&mut builder, or_name, left_parameter, right_parameter);
    let result = builder.forall("h", BinderStyle::Default, field, result);
    let result = builder.forall("b", BinderStyle::Default, proposition, result);
    let root = builder.forall_name(constructor, BinderStyle::Default, proposition, result);
    builder.finish(root)
}

fn or_motive_type(builder: &mut StructuralTermBuilder, or_name: &WireName) -> ExprId {
    let left = builder.bvar(1);
    let right = builder.bvar(0);
    let subject = or_application(builder, or_name, left, right);
    let proposition = builder.sort_zero();
    builder.forall("t", BinderStyle::Default, subject, proposition)
}

fn or_minor_type(
    builder: &mut StructuralTermBuilder,
    or_name: &WireName,
    constructor: &WireName,
    left: bool,
) -> ExprId {
    let field = builder.bvar(2);
    let (left_parameter, right_parameter, motive) = if left {
        (builder.bvar(3), builder.bvar(2), builder.bvar(1))
    } else {
        (builder.bvar(4), builder.bvar(3), builder.bvar(2))
    };
    let constructor = builder.constant(constructor, &[]);
    let constructor = builder.apply(constructor, left_parameter);
    let constructor = builder.apply(constructor, right_parameter);
    let field_value = builder.bvar(0);
    let constructor = builder.apply(constructor, field_value);
    let result = builder.apply(motive, constructor);
    let _ = or_name;
    builder.forall("h", BinderStyle::Default, field, result)
}

fn or_recursor_type(or_name: &WireName, inl: &WireName, inr: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let proposition = builder.sort_zero();
    let motive_type = or_motive_type(&mut builder, or_name);
    let inl_minor = or_minor_type(&mut builder, or_name, inl, true);
    let inr_minor = or_minor_type(&mut builder, or_name, inr, false);
    let left = builder.bvar(4);
    let right = builder.bvar(3);
    let major_type = or_application(&mut builder, or_name, left, right);
    let motive = builder.bvar(3);
    let major = builder.bvar(0);
    let mut result = builder.apply(motive, major);
    result = builder.forall("t", BinderStyle::Default, major_type, result);
    result = builder.forall("inr", BinderStyle::Default, inr_minor, result);
    result = builder.forall("inl", BinderStyle::Default, inl_minor, result);
    result = builder.forall("motive", BinderStyle::Implicit, motive_type, result);
    result = builder.forall("b", BinderStyle::Implicit, proposition, result);
    let root = builder.forall("a", BinderStyle::Implicit, proposition, result);
    builder.finish(root)
}

fn or_rule_rhs(
    or_name: &WireName,
    inl: &WireName,
    inr: &WireName,
    selected_left: bool,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let proposition = builder.sort_zero();
    let motive_type = or_motive_type(&mut builder, or_name);
    let inl_minor = or_minor_type(&mut builder, or_name, inl, true);
    let inr_minor = or_minor_type(&mut builder, or_name, inr, false);
    let mut result = builder.bvar(if selected_left { 2 } else { 1 });
    let field = builder.bvar(0);
    result = builder.apply(result, field);
    let field_type = builder.bvar(if selected_left { 4 } else { 3 });
    result = builder.lambda("h", BinderStyle::Default, field_type, result);
    result = builder.lambda("inr", BinderStyle::Default, inr_minor, result);
    result = builder.lambda("inl", BinderStyle::Default, inl_minor, result);
    result = builder.lambda("motive", BinderStyle::Default, motive_type, result);
    result = builder.lambda("b", BinderStyle::Default, proposition, result);
    let root = builder.lambda("a", BinderStyle::Default, proposition, result);
    builder.finish(root)
}

fn and_application(
    builder: &mut StructuralTermBuilder,
    and_name: &WireName,
    left: ExprId,
    right: ExprId,
) -> ExprId {
    let and_name = builder.constant(and_name, &[]);
    let applied_left = builder.apply(and_name, left);
    builder.apply(applied_left, right)
}

fn and_inductive_type() -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let proposition = builder.sort_zero();
    let result = builder.sort_zero();
    let result = builder.forall("b", BinderStyle::Default, proposition, result);
    let root = builder.forall("a", BinderStyle::Default, proposition, result);
    builder.finish(root)
}

fn and_constructor_type(and_name: &WireName, constructor: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let proposition = builder.sort_zero();
    let left_field = builder.bvar(1);
    let right_field = builder.bvar(1);
    let left_parameter = builder.bvar(3);
    let right_parameter = builder.bvar(2);
    let result = and_application(&mut builder, and_name, left_parameter, right_parameter);
    let result = builder.forall("right", BinderStyle::Default, right_field, result);
    let result = builder.forall("left", BinderStyle::Default, left_field, result);
    let result = builder.forall("b", BinderStyle::Implicit, proposition, result);
    let root = builder.forall_name(constructor, BinderStyle::Implicit, proposition, result);
    builder.finish(root)
}

fn and_motive_type(
    builder: &mut StructuralTermBuilder,
    and_name: &WireName,
    motive_universe: &WireName,
) -> ExprId {
    let left = builder.bvar(1);
    let right = builder.bvar(0);
    let subject = and_application(builder, and_name, left, right);
    let motive_sort = builder.sort_parameter(motive_universe);
    builder.forall("t", BinderStyle::Default, subject, motive_sort)
}

fn and_minor_type(
    builder: &mut StructuralTermBuilder,
    and_name: &WireName,
    constructor: &WireName,
) -> ExprId {
    let left_field = builder.bvar(2);
    let right_field = builder.bvar(2);
    let left_parameter = builder.bvar(4);
    let right_parameter = builder.bvar(3);
    let constructor = builder.constant(constructor, &[]);
    let constructor = builder.apply(constructor, left_parameter);
    let constructor = builder.apply(constructor, right_parameter);
    let left_value = builder.bvar(1);
    let constructor = builder.apply(constructor, left_value);
    let right_value = builder.bvar(0);
    let constructor = builder.apply(constructor, right_value);
    let motive = builder.bvar(2);
    let result = builder.apply(motive, constructor);
    let result = builder.forall("right", BinderStyle::Default, right_field, result);
    let _ = and_name;
    builder.forall("left", BinderStyle::Default, left_field, result)
}

fn and_recursor_type(
    and_name: &WireName,
    intro: &WireName,
    motive_universe: &WireName,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let proposition = builder.sort_zero();
    let motive_type = and_motive_type(&mut builder, and_name, motive_universe);
    let minor = and_minor_type(&mut builder, and_name, intro);
    let left = builder.bvar(3);
    let right = builder.bvar(2);
    let major_type = and_application(&mut builder, and_name, left, right);
    let motive = builder.bvar(2);
    let major = builder.bvar(0);
    let mut result = builder.apply(motive, major);
    result = builder.forall("t", BinderStyle::Default, major_type, result);
    result = builder.forall("intro", BinderStyle::Default, minor, result);
    result = builder.forall("motive", BinderStyle::Implicit, motive_type, result);
    result = builder.forall("b", BinderStyle::Implicit, proposition, result);
    let root = builder.forall("a", BinderStyle::Implicit, proposition, result);
    builder.finish(root)
}

fn and_rule_rhs(
    and_name: &WireName,
    intro: &WireName,
    motive_universe: &WireName,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let proposition = builder.sort_zero();
    let motive_type = and_motive_type(&mut builder, and_name, motive_universe);
    let minor = and_minor_type(&mut builder, and_name, intro);
    let mut result = builder.bvar(2);
    let left = builder.bvar(1);
    result = builder.apply(result, left);
    let right = builder.bvar(0);
    result = builder.apply(result, right);
    let right_type = builder.bvar(3);
    result = builder.lambda("right", BinderStyle::Default, right_type, result);
    let left_type = builder.bvar(3);
    result = builder.lambda("left", BinderStyle::Default, left_type, result);
    result = builder.lambda("intro", BinderStyle::Default, minor, result);
    result = builder.lambda("motive", BinderStyle::Default, motive_type, result);
    result = builder.lambda("b", BinderStyle::Default, proposition, result);
    let root = builder.lambda("a", BinderStyle::Default, proposition, result);
    builder.finish(root)
}

fn list_application(
    builder: &mut StructuralTermBuilder,
    list: &WireName,
    universe: &WireName,
    parameter: ExprId,
) -> ExprId {
    let list = builder.constant(list, std::slice::from_ref(universe));
    builder.apply(list, parameter)
}

fn list_inductive_type(universe: &WireName) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let parameter_type = builder.sort_successor_parameter(universe);
    let result = builder.sort_successor_parameter(universe);
    let root = builder.forall("α", BinderStyle::Default, parameter_type, result);
    builder.finish(root)
}

fn list_constructor_type(
    list: &WireName,
    constructor: &WireName,
    universe: &WireName,
    cons: bool,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let parameter_type = builder.sort_successor_parameter(universe);
    let parameter = builder.bvar(0);
    let mut result = list_application(&mut builder, list, universe, parameter);
    if cons {
        let parameter = builder.bvar(2);
        result = list_application(&mut builder, list, universe, parameter);
        let parameter = builder.bvar(1);
        let tail_type = list_application(&mut builder, list, universe, parameter);
        result = builder.forall("tail", BinderStyle::Default, tail_type, result);
        let head_type = builder.bvar(0);
        result = builder.forall("head", BinderStyle::Default, head_type, result);
    }
    let root = builder.forall_name(constructor, BinderStyle::Default, parameter_type, result);
    builder.finish(root)
}

fn list_motive_type(
    builder: &mut StructuralTermBuilder,
    list: &WireName,
    motive_universe: &WireName,
    list_universe: &WireName,
) -> ExprId {
    let parameter = builder.bvar(0);
    let subject = list_application(builder, list, list_universe, parameter);
    let sort = builder.sort_parameter(motive_universe);
    builder.forall("t", BinderStyle::Default, subject, sort)
}

fn list_minor_type(
    builder: &mut StructuralTermBuilder,
    list: &WireName,
    constructor: &WireName,
    motive_universe: &WireName,
    list_universe: &WireName,
    cons: bool,
) -> ExprId {
    if !cons {
        let constructor = builder.constant(constructor, std::slice::from_ref(list_universe));
        let parameter = builder.bvar(1);
        let constructor = builder.apply(constructor, parameter);
        let motive = builder.bvar(0);
        return builder.apply(motive, constructor);
    }
    let constructor = builder.constant(constructor, std::slice::from_ref(list_universe));
    let parameter = builder.bvar(5);
    let constructor = builder.apply(constructor, parameter);
    let head = builder.bvar(2);
    let constructor = builder.apply(constructor, head);
    let tail = builder.bvar(1);
    let constructor = builder.apply(constructor, tail);
    let motive = builder.bvar(4);
    let mut result = builder.apply(motive, constructor);
    let motive = builder.bvar(3);
    let tail = builder.bvar(0);
    let ih_type = builder.apply(motive, tail);
    result = builder.forall("tail_ih", BinderStyle::Default, ih_type, result);
    let parameter = builder.bvar(3);
    let tail_type = list_application(builder, list, list_universe, parameter);
    result = builder.forall("tail", BinderStyle::Default, tail_type, result);
    let head_type = builder.bvar(2);
    result = builder.forall("head", BinderStyle::Default, head_type, result);
    let _ = motive_universe;
    result
}

fn list_recursor_type(
    list: &WireName,
    nil: &WireName,
    cons: &WireName,
    motive_universe: &WireName,
    list_universe: &WireName,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let parameter_type = builder.sort_successor_parameter(list_universe);
    let motive_type = list_motive_type(&mut builder, list, motive_universe, list_universe);
    let nil_minor = list_minor_type(
        &mut builder,
        list,
        nil,
        motive_universe,
        list_universe,
        false,
    );
    let cons_minor = list_minor_type(
        &mut builder,
        list,
        cons,
        motive_universe,
        list_universe,
        true,
    );
    let parameter = builder.bvar(3);
    let major_type = list_application(&mut builder, list, list_universe, parameter);
    let motive = builder.bvar(3);
    let major = builder.bvar(0);
    let mut result = builder.apply(motive, major);
    result = builder.forall("t", BinderStyle::Default, major_type, result);
    result = builder.forall("cons", BinderStyle::Default, cons_minor, result);
    result = builder.forall("nil", BinderStyle::Default, nil_minor, result);
    result = builder.forall("motive", BinderStyle::Implicit, motive_type, result);
    let root = builder.forall("α", BinderStyle::Implicit, parameter_type, result);
    builder.finish(root)
}

fn list_rule_rhs(
    list: &WireName,
    nil: &WireName,
    cons: &WireName,
    motive_universe: &WireName,
    list_universe: &WireName,
    selected_cons: bool,
) -> Option<WireExpr> {
    let mut builder = StructuralTermBuilder::new();
    let parameter_type = builder.sort_successor_parameter(list_universe);
    let motive_type = list_motive_type(&mut builder, list, motive_universe, list_universe);
    let nil_minor = list_minor_type(
        &mut builder,
        list,
        nil,
        motive_universe,
        list_universe,
        false,
    );
    let cons_minor = list_minor_type(
        &mut builder,
        list,
        cons,
        motive_universe,
        list_universe,
        true,
    );
    let mut result = builder.bvar(if selected_cons { 2 } else { 1 });
    if selected_cons {
        let head = builder.bvar(1);
        result = builder.apply(result, head);
        let tail = builder.bvar(0);
        result = builder.apply(result, tail);
        let recursor = checker_child(list, "rec");
        let mut recursive =
            builder.constant(&recursor, &[motive_universe.clone(), list_universe.clone()]);
        let arguments = [
            builder.bvar(5),
            builder.bvar(4),
            builder.bvar(3),
            builder.bvar(2),
            builder.bvar(0),
        ];
        for argument in arguments {
            recursive = builder.apply(recursive, argument);
        }
        result = builder.apply(result, recursive);
        let parameter = builder.bvar(4);
        let tail_type = list_application(&mut builder, list, list_universe, parameter);
        result = builder.lambda("tail", BinderStyle::Default, tail_type, result);
        let head_type = builder.bvar(3);
        result = builder.lambda("head", BinderStyle::Default, head_type, result);
    }
    result = builder.lambda("cons", BinderStyle::Default, cons_minor, result);
    result = builder.lambda("nil", BinderStyle::Default, nil_minor, result);
    result = builder.lambda("motive", BinderStyle::Default, motive_type, result);
    let root = builder.lambda("α", BinderStyle::Default, parameter_type, result);
    builder.finish(root)
}

fn compare_inductive_expression(
    actual: &WireExpr,
    expected: &WireExpr,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<bool, InductiveVerdict> {
    match structural_expression_equal(actual, expected, comparison, true, cancelled) {
        Ok(Ok(equal)) => Ok(equal),
        Ok(Err(stop)) => Err(InductiveVerdict::Inconclusive(InductiveStop::Structural(
            stop,
        ))),
        Err(fault) => Err(InductiveVerdict::InternalFault(InductiveFault::Structural(
            fault,
        ))),
    }
}

fn map_member_preamble(name: &WireName, verdict: Verdict) -> InductiveVerdict {
    match verdict {
        Verdict::Rejected(rejection) => {
            InductiveVerdict::Rejected(InductiveRejection::MemberPreamble {
                name: name.clone(),
                rejection: Box::new(rejection),
            })
        }
        Verdict::Deferred(requirement) => {
            InductiveVerdict::Deferred(InductiveSupportLimit::MemberPreamble {
                name: name.clone(),
                requirement: Box::new(requirement),
            })
        }
        Verdict::Inconclusive(stop) => {
            InductiveVerdict::Inconclusive(InductiveStop::MemberPreamble {
                name: name.clone(),
                stop: Box::new(stop),
            })
        }
        Verdict::InternalFault(fault) => {
            InductiveVerdict::InternalFault(InductiveFault::MemberPreamble {
                name: name.clone(),
                fault: Box::new(fault),
            })
        }
        Verdict::Admitted(_) => {
            InductiveVerdict::InternalFault(InductiveFault::UnexpectedMemberAdmission {
                name: name.clone(),
            })
        }
    }
}

fn stage_inductive_member(
    environment: &ConstantEnvironment,
    entry: &ConstantEntry,
    budget: EnvironmentBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<ConstantEnvironment, InductiveVerdict> {
    let name = entry.name();
    match environment.extend_with(entry.clone(), budget, &mut *cancelled) {
        EnvironmentOutcome::Complete { environment, .. } => Ok(environment),
        EnvironmentOutcome::Refused { refusal, .. } => Err(InductiveVerdict::Rejected(
            InductiveRejection::Environment {
                name: name.clone(),
                refusal: Box::new(refusal),
            },
        )),
        EnvironmentOutcome::Inconclusive(stop) => {
            Err(InductiveVerdict::Inconclusive(InductiveStop::Environment {
                name: name.clone(),
                stop: Box::new(stop),
            }))
        }
        EnvironmentOutcome::InternalFault { fault, .. } => Err(InductiveVerdict::InternalFault(
            InductiveFault::Environment {
                name: name.clone(),
                fault: Box::new(fault),
            },
        )),
    }
}

fn field_mentions_inductive(
    field: &ConstructorField<'_>,
    inductive: &WireName,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<bool, InductiveVerdict> {
    let mut pending = vec![field.type_root];
    let mut seen = BTreeSet::new();
    while let Some(current) = pending.pop() {
        if !seen.insert(current) {
            continue;
        }
        comparison
            .comparison(cancelled)
            .map_err(|stop| InductiveVerdict::Inconclusive(InductiveStop::Structural(stop)))?;
        let node = field.source.node(current).ok_or_else(|| {
            InductiveVerdict::InternalFault(InductiveFault::Structural(
                QuickDefEqFault::MissingExpression {
                    side: QuickDefEqSide::Left,
                    index: current.index(),
                },
            ))
        })?;
        if matches!(node, ExprNode::Constant { name, .. } if name == inductive) {
            return Ok(true);
        }
        let mut push = |child: ExprId| -> Result<(), InductiveVerdict> {
            if child.index() >= current.index() {
                return Err(InductiveVerdict::InternalFault(InductiveFault::Structural(
                    QuickDefEqFault::NonBackwardExpressionReference {
                        side: QuickDefEqSide::Left,
                        parent: current.index(),
                        child: child.index(),
                    },
                )));
            }
            pending.push(child);
            Ok(())
        };
        match node {
            ExprNode::Apply { function, argument } => {
                push(*argument)?;
                push(*function)?;
            }
            ExprNode::Lambda {
                binder_type, body, ..
            }
            | ExprNode::Forall {
                binder_type, body, ..
            } => {
                push(*body)?;
                push(*binder_type)?;
            }
            ExprNode::Let {
                type_, value, body, ..
            } => {
                push(*body)?;
                push(*value)?;
                push(*type_)?;
            }
            ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                push(*expression)?
            }
            ExprNode::Bound { .. }
            | ExprNode::Free { .. }
            | ExprNode::Meta { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Constant { .. }
            | ExprNode::NatLiteral { .. }
            | ExprNode::StringLiteral(_) => {}
        }
    }
    Ok(false)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum FieldRecursion {
    Absent,
    DirectSelf,
    Unsupported,
}

fn classify_field_recursion(
    field: &ConstructorField<'_>,
    inductive: &WireName,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<FieldRecursion, InductiveVerdict> {
    if matches!(
        field.source.node(field.type_root),
        Some(ExprNode::Constant { name, levels }) if name == inductive && levels.is_empty()
    ) {
        return Ok(FieldRecursion::DirectSelf);
    }
    match field_mentions_inductive(field, inductive, comparison, cancelled)? {
        true => Ok(FieldRecursion::Unsupported),
        false => Ok(FieldRecursion::Absent),
    }
}

/// Reconstruct the fixed universe-polymorphic `Init.Option` family without
/// consulting the primary checker. This deliberately names the one supported
/// parameterized family: arbitrary parameterized inductives still take the
/// ordinary typed deferral path below.
fn admit_init_option(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    let Some(option_universe) = declaration.level_parameters().first() else {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: 0,
        });
    };
    if declaration.level_parameters().len() != 1 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.num_parameters() != 1 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    let none = checker_child(name, "none");
    let some = checker_child(name, "some");
    if metadata.constructors() != [none.clone(), some.clone()]
        || declarations.len() != 4
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let Some(expected_type) = option_inductive_type(option_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged_environment =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    let mut members = vec![name.clone()];
    for (index, (constructor_name, has_field)) in [(none.clone(), false), (some.clone(), true)]
        .into_iter()
        .enumerate()
    {
        let Some(constructor) = declarations
            .iter()
            .find(|entry| entry.name() == &constructor_name)
        else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
                name: constructor_name,
            });
        };
        let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        };
        let Some(expected_type) =
            option_constructor_type(name, &constructor_name, option_universe, has_field)
        else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        if constructor.declaration().safety() != ConstantSafety::Safe
            || constructor.declaration().level_parameters() != std::slice::from_ref(option_universe)
            || constructor_metadata.inductive() != name
            || constructor_metadata.index() != index as u32
            || constructor_metadata.num_parameters() != 1
            || constructor_metadata.num_fields() != u32::from(has_field)
            || environment.find(&constructor_name).is_some()
        {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        }
        match compare_inductive_expression(
            constructor.declaration().type_(),
            &expected_type,
            comparison,
            cancelled,
        ) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                    name: constructor_name,
                });
            }
            Err(verdict) => return verdict,
        }
        if let Err(verdict) = declared_type_is_a_type(
            &staged_environment,
            &constructor_name,
            constructor.declaration(),
            &budget,
            cancelled,
        ) {
            return map_member_preamble(&constructor_name, verdict);
        }
        staged_environment = match stage_inductive_member(
            &staged_environment,
            constructor,
            environment_budget,
            cancelled,
        ) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
        members.push(constructor_name);
    }
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let recursor_levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = recursor_levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || recursor_levels.len() != 2
        || recursor_levels.get(1) != Some(option_universe)
        || motive_universe == option_universe
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 1
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 2
        || recursor_metadata.rules().len() != 2
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) =
        option_recursor_type(name, &none, &some, motive_universe, option_universe)
    else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    for (index, (constructor, selected_some)) in
        [(none, false), (some, true)].into_iter().enumerate()
    {
        let Some(rule) = recursor_metadata.rules().get(index) else {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        };
        let Some(expected_rhs) = option_rule_rhs(
            name,
            &checker_child(name, "none"),
            &checker_child(name, "some"),
            motive_universe,
            option_universe,
            selected_some,
        ) else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        if rule.constructor() != &constructor || rule.num_fields() != u32::from(selected_some) {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        match compare_inductive_expression(rule.rhs(), &expected_rhs, comparison, cancelled) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                    name: recursor_name,
                });
            }
            Err(verdict) => return verdict,
        }
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged_environment,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) =
        stage_inductive_member(&staged_environment, recursor, environment_budget, cancelled)
    {
        return verdict;
    }
    members.push(recursor_name);
    InductiveVerdict::Admitted(InductiveAdmission { members })
}

/// Reconstruct the named recursive `Init.List` family. This remains a closed
/// judgment: its universe-polymorphic parameter, recursive constructor,
/// recursor telescope, and both iota rules are regenerated before any member
/// is staged.
fn admit_init_list(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    let Some(list_universe) = declaration.level_parameters().first() else {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: 0,
        });
    };
    if declaration.level_parameters().len() != 1 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.num_parameters() != 1 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if !metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    let nil = checker_child(name, "nil");
    let cons = checker_child(name, "cons");
    if metadata.constructors() != [nil.clone(), cons.clone()]
        || declarations.len() != 4
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let Some(expected_type) = list_inductive_type(list_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged_environment =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    let mut members = vec![name.clone()];
    for (index, (constructor_name, cons_constructor)) in
        [(nil.clone(), false), (cons.clone(), true)]
            .into_iter()
            .enumerate()
    {
        let Some(constructor) = declarations
            .iter()
            .find(|entry| entry.name() == &constructor_name)
        else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
                name: constructor_name,
            });
        };
        let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        };
        let Some(expected_type) =
            list_constructor_type(name, &constructor_name, list_universe, cons_constructor)
        else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        if constructor.declaration().safety() != ConstantSafety::Safe
            || constructor.declaration().level_parameters() != std::slice::from_ref(list_universe)
            || constructor_metadata.inductive() != name
            || constructor_metadata.index() != index as u32
            || constructor_metadata.num_parameters() != 1
            || constructor_metadata.num_fields() != if cons_constructor { 2 } else { 0 }
            || environment.find(&constructor_name).is_some()
        {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        }
        match compare_inductive_expression(
            constructor.declaration().type_(),
            &expected_type,
            comparison,
            cancelled,
        ) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                    name: constructor_name,
                });
            }
            Err(verdict) => return verdict,
        }
        if let Err(verdict) = declared_type_is_a_type(
            &staged_environment,
            &constructor_name,
            constructor.declaration(),
            &budget,
            cancelled,
        ) {
            return map_member_preamble(&constructor_name, verdict);
        }
        staged_environment = match stage_inductive_member(
            &staged_environment,
            constructor,
            environment_budget,
            cancelled,
        ) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
        members.push(constructor_name);
    }
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let recursor_levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = recursor_levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || recursor_levels.len() != 2
        || recursor_levels.get(1) != Some(list_universe)
        || motive_universe == list_universe
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 1
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 2
        || recursor_metadata.rules().len() != 2
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = list_recursor_type(name, &nil, &cons, motive_universe, list_universe)
    else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    for (index, (constructor, selected_cons)) in
        [(nil, false), (cons, true)].into_iter().enumerate()
    {
        let Some(rule) = recursor_metadata.rules().get(index) else {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        };
        let Some(expected_rhs) = list_rule_rhs(
            name,
            &checker_child(name, "nil"),
            &checker_child(name, "cons"),
            motive_universe,
            list_universe,
            selected_cons,
        ) else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        if rule.constructor() != &constructor
            || rule.num_fields() != if selected_cons { 2 } else { 0 }
        {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        match compare_inductive_expression(rule.rhs(), &expected_rhs, comparison, cancelled) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                    name: recursor_name,
                });
            }
            Err(verdict) => return verdict,
        }
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged_environment,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) =
        stage_inductive_member(&staged_environment, recursor, environment_budget, cancelled)
    {
        return verdict;
    }
    members.push(recursor_name);
    InductiveVerdict::Admitted(InductiveAdmission { members })
}

/// Reconstruct the empty `Init.Empty` family and its eliminator. The absence
/// of constructor rows is checked as a fact of this named family, never
/// treated as a vacuous admission for arbitrary inductives.
fn admit_init_empty(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    if !declaration.level_parameters().is_empty() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    if !metadata.constructors().is_empty()
        || declarations.len() != 2
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let Some(expected_type) = nonrecursive_inductive_type() else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let staged_environment =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let recursor_levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = recursor_levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || recursor_levels.len() != 1
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 0
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 0
        || !recursor_metadata.rules().is_empty()
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = empty_recursor_type(name, motive_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged_environment,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) =
        stage_inductive_member(&staged_environment, recursor, environment_budget, cancelled)
    {
        return verdict;
    }
    InductiveVerdict::Admitted(InductiveAdmission {
        members: vec![name.clone(), recursor_name],
    })
}

/// Reconstruct `Init.PEmpty.{u}`: an empty family at an arbitrary universe and
/// an eliminator whose motive universe is deliberately distinct from the
/// family's universe parameter.
fn admit_init_pempty(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    let Some(family_universe) = declaration.level_parameters().first() else {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: 0,
        });
    };
    if declaration.level_parameters().len() != 1 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    if !metadata.constructors().is_empty()
        || declarations.len() != 2
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let mut type_builder = StructuralTermBuilder::new();
    let expected_type = type_builder.sort_parameter(family_universe);
    let Some(expected_type) = type_builder.finish(expected_type) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let staged_environment =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let recursor_levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = recursor_levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || recursor_levels.len() != 2
        || recursor_levels.get(1) != Some(family_universe)
        || motive_universe == family_universe
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 0
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 0
        || !recursor_metadata.rules().is_empty()
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = empty_recursor_type_at_levels(
        name,
        motive_universe,
        std::slice::from_ref(family_universe),
        BinderStyle::Implicit,
    ) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged_environment,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) =
        stage_inductive_member(&staged_environment, recursor, environment_budget, cancelled)
    {
        return verdict;
    }
    InductiveVerdict::Admitted(InductiveAdmission {
        members: vec![name.clone(), recursor_name],
    })
}

/// Reconstruct the named Prop-only `Init.Or` family. This is deliberately not
/// a general two-parameter admission: the two proposition parameters,
/// constructor field sources, zero-universe recursor, and both iota rules are
/// all regenerated and compared here.
fn admit_init_or(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    if !declaration.level_parameters().is_empty() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 2 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    let inl = checker_child(name, "inl");
    let inr = checker_child(name, "inr");
    if metadata.constructors() != [inl.clone(), inr.clone()]
        || declarations.len() != 4
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let Some(expected_type) = or_inductive_type() else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged_environment =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    let mut members = vec![name.clone()];
    for (index, (constructor_name, left)) in [(inl.clone(), true), (inr.clone(), false)]
        .into_iter()
        .enumerate()
    {
        let Some(constructor) = declarations
            .iter()
            .find(|entry| entry.name() == &constructor_name)
        else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
                name: constructor_name,
            });
        };
        let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        };
        let Some(expected_type) = or_constructor_type(name, &constructor_name, left) else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        if constructor.declaration().safety() != ConstantSafety::Safe
            || !constructor.declaration().level_parameters().is_empty()
            || constructor_metadata.inductive() != name
            || constructor_metadata.index() != index as u32
            || constructor_metadata.num_parameters() != 2
            || constructor_metadata.num_fields() != 1
            || environment.find(&constructor_name).is_some()
        {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        }
        match compare_inductive_expression(
            constructor.declaration().type_(),
            &expected_type,
            comparison,
            cancelled,
        ) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                    name: constructor_name,
                });
            }
            Err(verdict) => return verdict,
        }
        if let Err(verdict) = declared_type_is_a_type(
            &staged_environment,
            &constructor_name,
            constructor.declaration(),
            &budget,
            cancelled,
        ) {
            return map_member_preamble(&constructor_name, verdict);
        }
        staged_environment = match stage_inductive_member(
            &staged_environment,
            constructor,
            environment_budget,
            cancelled,
        ) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
        members.push(constructor_name);
    }
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || !recursor.declaration().level_parameters().is_empty()
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 2
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 2
        || recursor_metadata.rules().len() != 2
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = or_recursor_type(name, &inl, &inr) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    for (index, (constructor, selected_left)) in [(inl, true), (inr, false)].into_iter().enumerate()
    {
        let Some(rule) = recursor_metadata.rules().get(index) else {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        };
        let Some(expected_rhs) = or_rule_rhs(
            name,
            &checker_child(name, "inl"),
            &checker_child(name, "inr"),
            selected_left,
        ) else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        if rule.constructor() != &constructor || rule.num_fields() != 1 {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        match compare_inductive_expression(rule.rhs(), &expected_rhs, comparison, cancelled) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                    name: recursor_name,
                });
            }
            Err(verdict) => return verdict,
        }
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged_environment,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) =
        stage_inductive_member(&staged_environment, recursor, environment_budget, cancelled)
    {
        return verdict;
    }
    members.push(recursor_name);
    InductiveVerdict::Admitted(InductiveAdmission { members })
}

/// Reconstruct the fixed Prop-only `Init.And` block without widening the
/// general inductive admission path.
fn admit_init_and(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    if !declaration.level_parameters().is_empty() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 2 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    let intro = checker_child(name, "intro");
    if metadata.constructors() != std::slice::from_ref(&intro)
        || declarations.len() != 3
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let Some(expected_type) = and_inductive_type() else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    let Some(constructor) = declarations.iter().find(|entry| entry.name() == &intro) else {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing { name: intro });
    };
    let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: checker_child(name, "intro"),
        });
    };
    let Some(expected_type) = and_constructor_type(name, &intro) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    if constructor.declaration().safety() != ConstantSafety::Safe
        || !constructor.declaration().level_parameters().is_empty()
        || constructor_metadata.inductive() != name
        || constructor_metadata.index() != 0
        || constructor_metadata.num_parameters() != 2
        || constructor_metadata.num_fields() != 2
        || environment.find(&intro).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { name: intro });
    }
    match compare_inductive_expression(
        constructor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: checker_child(name, "intro"),
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &intro,
        constructor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&intro, verdict);
    }
    staged = match stage_inductive_member(&staged, constructor, environment_budget, cancelled) {
        Ok(environment) => environment,
        Err(verdict) => return verdict,
    };
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || levels.len() != 1
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 2
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 1
        || recursor_metadata.rules().len() != 1
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = and_recursor_type(name, &intro, motive_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    let Some(rule) = recursor_metadata.rules().first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let Some(expected_rhs) = and_rule_rhs(name, &intro, motive_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    if rule.constructor() != &intro || rule.num_fields() != 2 {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    match compare_inductive_expression(rule.rhs(), &expected_rhs, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) = stage_inductive_member(&staged, recursor, environment_budget, cancelled) {
        return verdict;
    }
    InductiveVerdict::Admitted(InductiveAdmission {
        members: vec![name.clone(), intro, recursor_name],
    })
}

/// Reconstruct the fixed `Init.Bool` enumeration without widening the general
/// enumeration admission path.
fn admit_init_bool(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    if !declaration.level_parameters().is_empty() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    let false_name = checker_child(name, "false");
    let true_name = checker_child(name, "true");
    if metadata.constructors() != [false_name.clone(), true_name.clone()]
        || declarations.len() != 4
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let Some(expected_type) = bool_inductive_type() else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    let mut members = vec![name.clone()];
    for (index, constructor_name) in [false_name.clone(), true_name.clone()]
        .into_iter()
        .enumerate()
    {
        let Some(constructor) = declarations
            .iter()
            .find(|entry| entry.name() == &constructor_name)
        else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
                name: constructor_name,
            });
        };
        let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        };
        let Some(expected_type) = bool_constructor_type() else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        if constructor.declaration().safety() != ConstantSafety::Safe
            || !constructor.declaration().level_parameters().is_empty()
            || constructor_metadata.inductive() != name
            || constructor_metadata.index() != index as u32
            || constructor_metadata.num_parameters() != 0
            || constructor_metadata.num_fields() != 0
            || environment.find(&constructor_name).is_some()
        {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        }
        match compare_inductive_expression(
            constructor.declaration().type_(),
            &expected_type,
            comparison,
            cancelled,
        ) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                    name: constructor_name,
                });
            }
            Err(verdict) => return verdict,
        }
        if let Err(verdict) = declared_type_is_a_type(
            &staged,
            &constructor_name,
            constructor.declaration(),
            &budget,
            cancelled,
        ) {
            return map_member_preamble(&constructor_name, verdict);
        }
        staged = match stage_inductive_member(&staged, constructor, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
        members.push(constructor_name);
    }
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let levels = recursor.declaration().level_parameters();
    let Some(level_parameter) = levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || levels.len() != 1
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 0
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 2
        || recursor_metadata.rules().len() != 2
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = bool_recursor_type(level_parameter) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    for (index, (constructor, selected_true)) in [(false_name, false), (true_name, true)]
        .into_iter()
        .enumerate()
    {
        let Some(rule) = recursor_metadata.rules().get(index) else {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        };
        let Some(expected_rhs) = bool_rule_rhs(level_parameter, selected_true) else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        if rule.constructor() != &constructor || rule.num_fields() != 0 {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        match compare_inductive_expression(rule.rhs(), &expected_rhs, comparison, cancelled) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                    name: recursor_name,
                });
            }
            Err(verdict) => return verdict,
        }
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) = stage_inductive_member(&staged, recursor, environment_budget, cancelled) {
        return verdict;
    }
    members.push(recursor_name);
    InductiveVerdict::Admitted(InductiveAdmission { members })
}

/// Reconstruct the one-constructor `Init.Unit` block and its eliminator.
fn admit_init_unit(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    if !declaration.level_parameters().is_empty() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    let unit = checker_child(name, "unit");
    if metadata.constructors() != std::slice::from_ref(&unit)
        || declarations.len() != 3
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let Some(expected_type) = bool_inductive_type() else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    let Some(constructor) = declarations.iter().find(|entry| entry.name() == &unit) else {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing { name: unit });
    };
    let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: checker_child(name, "unit"),
        });
    };
    let Some(expected_type) = unit_constructor_type() else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    if constructor.declaration().safety() != ConstantSafety::Safe
        || !constructor.declaration().level_parameters().is_empty()
        || constructor_metadata.inductive() != name
        || constructor_metadata.index() != 0
        || constructor_metadata.num_parameters() != 0
        || constructor_metadata.num_fields() != 0
        || environment.find(&unit).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { name: unit });
    }
    match compare_inductive_expression(
        constructor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: checker_child(name, "unit"),
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &unit,
        constructor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&unit, verdict);
    }
    staged = match stage_inductive_member(&staged, constructor, environment_budget, cancelled) {
        Ok(environment) => environment,
        Err(verdict) => return verdict,
    };
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || levels.len() != 1
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 0
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 1
        || recursor_metadata.rules().len() != 1
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = unit_recursor_type(motive_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    let Some(rule) = recursor_metadata.rules().first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let Some(expected_rhs) = unit_rule_rhs(motive_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    if rule.constructor() != &unit || rule.num_fields() != 0 {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    match compare_inductive_expression(rule.rhs(), &expected_rhs, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) = stage_inductive_member(&staged, recursor, environment_budget, cancelled) {
        return verdict;
    }
    InductiveVerdict::Admitted(InductiveAdmission {
        members: vec![name.clone(), unit, recursor_name],
    })
}

/// Reconstruct a named two-parameter Type coproduct and its eliminator.
// Same shape as `admit_init_prod` and the site at :871: an admission
// reconstruction carries the whole member preamble explicitly because the
// trusted checker does not hide state in a context struct.
#[allow(clippy::too_many_arguments)]
fn admit_init_sum(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
    left_label: &str,
    right_label: &str,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    let levels = declaration.level_parameters();
    let Some(left_universe) = levels.first() else {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: 0,
        });
    };
    let Some(right_universe) = levels.get(1) else {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: levels.len(),
        });
    };
    if levels.len() != 2 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: levels.len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 2 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    let inl = checker_child(name, left_label);
    let inr = checker_child(name, right_label);
    if metadata.constructors() != [inl.clone(), inr.clone()]
        || declarations.len() != 4
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let Some(expected_type) = sum_inductive_type(left_universe, right_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    for (index, (constructor_name, left_constructor)) in [(inl.clone(), true), (inr.clone(), false)]
        .into_iter()
        .enumerate()
    {
        let Some(constructor) = declarations
            .iter()
            .find(|entry| entry.name() == &constructor_name)
        else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
                name: constructor_name,
            });
        };
        let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        };
        let Some(expected_type) =
            sum_constructor_type(name, left_universe, right_universe, left_constructor)
        else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        if constructor.declaration().safety() != ConstantSafety::Safe
            || constructor.declaration().level_parameters() != levels
            || constructor_metadata.inductive() != name
            || constructor_metadata.index() != index as u32
            || constructor_metadata.num_parameters() != 2
            || constructor_metadata.num_fields() != 1
            || environment.find(&constructor_name).is_some()
        {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        }
        match compare_inductive_expression(
            constructor.declaration().type_(),
            &expected_type,
            comparison,
            cancelled,
        ) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                    name: constructor_name,
                });
            }
            Err(verdict) => return verdict,
        }
        if let Err(verdict) = declared_type_is_a_type(
            &staged,
            &constructor_name,
            constructor.declaration(),
            &budget,
            cancelled,
        ) {
            return map_member_preamble(&constructor_name, verdict);
        }
        staged = match stage_inductive_member(&staged, constructor, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    }
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let recursor_levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = recursor_levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || recursor_levels.len() != 3
        || recursor_levels.get(1) != Some(left_universe)
        || recursor_levels.get(2) != Some(right_universe)
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 2
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 2
        || recursor_metadata.rules().len() != 2
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = sum_recursor_type(
        name,
        &inl,
        &inr,
        motive_universe,
        left_universe,
        right_universe,
    ) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    for (index, (constructor, selected_left)) in
        [(&inl, true), (&inr, false)].into_iter().enumerate()
    {
        let Some(rule) = recursor_metadata.rules().get(index) else {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        };
        let Some(expected_rhs) = sum_rule_rhs(
            name,
            &inl,
            &inr,
            motive_universe,
            left_universe,
            right_universe,
            selected_left,
        ) else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        if rule.constructor() != constructor || rule.num_fields() != 1 {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        match compare_inductive_expression(rule.rhs(), &expected_rhs, comparison, cancelled) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                    name: recursor_name,
                });
            }
            Err(verdict) => return verdict,
        }
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) = stage_inductive_member(&staged, recursor, environment_budget, cancelled) {
        return verdict;
    }
    InductiveVerdict::Admitted(InductiveAdmission {
        members: vec![
            name.clone(),
            checker_child(name, left_label),
            checker_child(name, right_label),
            recursor_name,
        ],
    })
}

/// Reconstruct the two-parameter singleton-constructor `Init.Prod` block.
fn admit_init_prod(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    let levels = declaration.level_parameters();
    let Some(left_universe) = levels.first() else {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: 0,
        });
    };
    let Some(right_universe) = levels.get(1) else {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: levels.len(),
        });
    };
    if levels.len() != 2 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: levels.len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 2 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    let constructor_name = checker_child(name, "mk");
    if metadata.constructors() != std::slice::from_ref(&constructor_name)
        || declarations.len() != 3
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let Some(expected_type) = prod_inductive_type(left_universe, right_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    let Some(constructor) = declarations
        .iter()
        .find(|entry| entry.name() == &constructor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
            name: constructor_name,
        });
    };
    let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: constructor_name,
        });
    };
    let Some(expected_type) =
        prod_constructor_type(name, &constructor_name, left_universe, right_universe)
    else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    if constructor.declaration().safety() != ConstantSafety::Safe
        || constructor.declaration().level_parameters() != levels
        || constructor_metadata.inductive() != name
        || constructor_metadata.index() != 0
        || constructor_metadata.num_parameters() != 2
        || constructor_metadata.num_fields() != 2
        || environment.find(&constructor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: constructor_name,
        });
    }
    match compare_inductive_expression(
        constructor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &constructor_name,
        constructor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&constructor_name, verdict);
    }
    staged = match stage_inductive_member(&staged, constructor, environment_budget, cancelled) {
        Ok(environment) => environment,
        Err(verdict) => return verdict,
    };
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let recursor_levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = recursor_levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || recursor_levels.len() != 3
        || recursor_levels.get(1) != Some(left_universe)
        || recursor_levels.get(2) != Some(right_universe)
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 2
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 1
        || recursor_metadata.rules().len() != 1
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = prod_recursor_type(
        name,
        &constructor_name,
        motive_universe,
        left_universe,
        right_universe,
    ) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    let Some(rule) = recursor_metadata.rules().first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let Some(expected_rhs) = prod_rule_rhs(
        name,
        &constructor_name,
        motive_universe,
        left_universe,
        right_universe,
    ) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    if rule.constructor() != &constructor_name || rule.num_fields() != 2 {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    match compare_inductive_expression(rule.rhs(), &expected_rhs, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) = stage_inductive_member(&staged, recursor, environment_budget, cancelled) {
        return verdict;
    }
    InductiveVerdict::Admitted(InductiveAdmission {
        members: vec![name.clone(), constructor_name, recursor_name],
    })
}

/// Reconstruct one **class-shaped** block: exactly one constructor, zero
/// indices, non-recursive, non-nested, non-reflexive, one family universe,
/// and an arbitrary parameter telescope (`Init.Add`, `Init.Sub`,
/// `Init.Inhabited`, …). Unlike the named-family reconstructions above, this
/// judgment is keyed on SHAPE rather than on a name, because Prelude carries
/// dozens of these blocks and they share one elimination structure.
///
/// What is pinned versus what is imported, and why that is sound here:
///
/// * The inductive TYPE is inspected, not regenerated: exactly
///   [`fln_env::constants::InductiveVal::num_params`] leading binders and a
///   `Sort` residue. The residue level is deliberately unconstrained — real
///   families use both `succ u` (`Add`) and `max 1 u` (`Inhabited`) — and
///   KR-972 has already forced the declared type through WHNF to a sort.
/// * The CONSTRUCTOR is regenerated and compared in full. Parameter types are
///   imported verbatim from the constructor's own telescope (identical
///   binding context, so wire depths transfer unchanged); field types come
///   from the same telescope at their field positions. The judgment pins the
///   skeleton — binder count, the result application `D @ p_1 … @ p_k` with
///   each argument the de Bruijn reference of its own parameter at its final
///   embedding depth — while arbitrary field content arrives through the
///   imported terms.
/// * The RECURSOR is regenerated and compared in full against the canonical
///   eliminator for this family: implicit-or-captured parameter binders, one
///   motive over `D ps` into `Sort v`, one minor premise over the fields
///   ending in `motive (mk ps xs)`, one major premise, body `motive major`.
///   Every subtree is imported from the recursor's own decoded arena, so no
///   depth shifting exists anywhere in this module.
/// * The single iota rule must be exactly `minor applied to the fields`.
///
/// Binder styles are CAPTURED from the decoded block and reused, never
/// assumed: upstream re-binds class parameters implicitly in constructors and
/// recursors while keeping the inductive type's own style, but this judgment
/// does not have to legislate that — capturing keeps it closed over whatever
/// the pin actually emits while still forcing internal consistency between
/// the compared sides.
///
/// Deviations are typed DEFERRALS (`ResultUniverse`, this catalog's
/// established "shape did not match" signal), never rejections: this arm
/// admits by shape class, so an off-spec block must stay a non-answer for
/// human classification rather than become a veto the shape evidence does not
/// support.
#[allow(clippy::too_many_lines)]
fn admit_class_block(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    let family_universes = declaration.level_parameters();
    if family_universes.is_empty() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: 0,
        });
    }
    if family_universes.len() > 8 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: family_universes.len(),
        });
    }
    let parameter_count = metadata.num_parameters();
    let Ok(parameter_count) = usize::try_from(parameter_count) else {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    };
    if parameter_count == 0 || parameter_count > MAX_NONRECURSIVE_FIELDS {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    let defer = |stage: &'static str| {
        if std::env::var_os("FLN_CHECKER_TRACE").is_some() {
            eprintln!("fln-checker: class-block defer at {stage} for {name:?}");
        }
        InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse)
    };
    // -- shared metadata gates --------------------------------------------
    if metadata.mutual() != std::slice::from_ref(name)
        || metadata.num_indices() != 0
        || metadata.num_nested() != 0
        || metadata.is_recursive()
        || metadata.is_reflexive()
        || metadata.constructors().len() != 1
        || declarations.len() != 3
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }

    // -- the inductive type: k binders, then a sort ------------------------
    let Some((_type_binders, type_tail)) = peel_binders_at(
        declaration.type_(),
        declaration.type_().root(),
        parameter_count,
    ) else {
        return defer("inductive-type-peel");
    };
    if !is_sort_at(declaration.type_(), type_tail) {
        return defer("inductive-type-sort-tail");
    }

    // -- the constructor ---------------------------------------------------
    let constructor_name = metadata.constructors()[0].clone();
    let Some(constructor) = declarations
        .iter()
        .find(|entry| entry.name() == &constructor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
            name: constructor_name.clone(),
        });
    };
    let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: constructor_name.clone(),
        });
    };
    let field_count = constructor_metadata.num_fields();
    let Ok(field_count) = usize::try_from(field_count) else {
        return InductiveVerdict::Deferred(InductiveSupportLimit::FieldCount {
            observed: usize::MAX,
            limit: MAX_NONRECURSIVE_FIELDS,
        });
    };
    if field_count > MAX_NONRECURSIVE_FIELDS {
        return InductiveVerdict::Deferred(InductiveSupportLimit::FieldCount {
            observed: field_count,
            limit: MAX_NONRECURSIVE_FIELDS,
        });
    }
    let constructor_type = constructor.declaration().type_();
    let Some((constructor_param_binders, after_params)) =
        peel_binders_at(constructor_type, constructor_type.root(), parameter_count)
    else {
        // The constructor's own metadata demands `parameter_count` leading
        // binders; a term that does not have them contradicts itself, which
        // is corruption rather than an unknown family.
        if std::env::var_os("FLN_CHECKER_TRACE").is_some() {
            eprintln!("fln-checker: class-block reject at constructor-parameter-peel for {name:?}");
        }
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    };
    let Some((constructor_field_binders, _)) =
        peel_binders_at(constructor_type, after_params, field_count)
    else {
        if std::env::var_os("FLN_CHECKER_TRACE").is_some() {
            eprintln!("fln-checker: class-block reject at constructor-field-peel for {name:?}");
        }
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    };

    let mut builder = StructuralTermBuilder::new();
    let mut imported_units = 0usize;
    let mut imported_param_types = Vec::with_capacity(parameter_count);
    for (binder_type, _) in &constructor_param_binders {
        let Some(imported) = builder.import(constructor_type, *binder_type) else {
            return defer("constructor-parameter-import");
        };
        imported_units += imported.index().saturating_add(1);
        imported_param_types.push(imported);
    }
    let mut imported_field_types = Vec::with_capacity(field_count);
    for (binder_type, _) in &constructor_field_binders {
        let Some(imported) = builder.import(constructor_type, *binder_type) else {
            return defer("constructor-field-import");
        };
        imported_units += imported.index().saturating_add(1);
        imported_field_types.push(imported);
    }
    if imported_units.saturating_mul(8) > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
        return InductiveVerdict::Deferred(InductiveSupportLimit::ExpectedArenaUnits {
            observed: imported_units.saturating_mul(8),
            limit: MAX_INDUCTIVE_EXPECTED_ARENA_UNITS,
        });
    }

    // Result application `D p_1 … p_k`: under the k parameter binders and f
    // field binders, parameter i (1-based from the outside) sits at de Bruijn
    // depth `k + f - i`.
    let total_binders = parameter_count + field_count;
    let mut result = builder.constant(name, family_universes);
    for index in 0..parameter_count {
        let depth = total_binders - index;
        let argument = builder.bvar(depth as u32 - 1);
        result = builder.apply(result, argument);
    }
    for field_type in imported_field_types.iter().rev() {
        result = builder.forall("x", BinderStyle::Default, *field_type, result);
    }
    for (index, (_, style)) in constructor_param_binders.iter().enumerate() {
        result = builder.forall("p", *style, imported_param_types[index], result);
    }
    let Some(expected_constructor) = builder.finish(result) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        constructor_type,
        &expected_constructor,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) | Err(_) => return defer("constructor-compare"),
    }
    if constructor.declaration().safety() != ConstantSafety::Safe
        || constructor.declaration().level_parameters() != family_universes
        || constructor_metadata.inductive() != name
        || constructor_metadata.index() != 0
        || constructor_metadata.num_parameters() != parameter_count as u32
        || constructor_metadata.num_fields() != field_count as u32
        || environment.find(&constructor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: constructor_name.clone(),
        });
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &constructor_name,
        constructor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&constructor_name, verdict);
    }
    staged = match stage_inductive_member(&staged, constructor, environment_budget, cancelled) {
        Ok(environment) => environment,
        Err(verdict) => return verdict,
    };

    // -- the recursor ------------------------------------------------------
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let recursor_levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = recursor_levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let recursor_reject = |stage: &'static str| {
        if std::env::var_os("FLN_CHECKER_TRACE").is_some() {
            eprintln!("fln-checker: class-block reject at {stage} for {recursor_name:?}");
        }
        InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name.clone(),
        })
    };
    if recursor.declaration().safety() != ConstantSafety::Safe {
        return recursor_reject("safety");
    }
    if recursor_levels.len() != family_universes.len() + 1 {
        return recursor_reject("level-count");
    }
    if recursor_levels.get(1..) != Some(family_universes) {
        return recursor_reject("family-level");
    }
    if family_universes.contains(motive_universe) {
        return recursor_reject("motive-level-collides");
    }
    if recursor_metadata.mutual() != std::slice::from_ref(name) {
        return recursor_reject("mutual");
    }
    if recursor_metadata.num_parameters() != parameter_count as u32 {
        return recursor_reject("num-parameters");
    }
    if recursor_metadata.num_indices() != 0 {
        return recursor_reject("num-indices");
    }
    if recursor_metadata.num_motives() != 1 {
        return recursor_reject("num-motives");
    }
    if recursor_metadata.num_minors() != 1 {
        return recursor_reject("num-minors");
    }
    if recursor_metadata.rules().len() != 1 {
        return recursor_reject("rule-count");
    }
    if recursor_metadata.k() {
        return recursor_reject("k-flag");
    }
    if environment.find(&recursor_name).is_some() {
        return recursor_reject("already-declared");
    }
    let recursor_type = recursor.declaration().type_();
    let Some((recursor_param_binders, recursor_after_params)) =
        peel_binders_at(recursor_type, recursor_type.root(), parameter_count)
    else {
        return defer("recursor-parameter-peel");
    };
    let Some((recursor_tail_binders, _)) = peel_binders_at(recursor_type, recursor_after_params, 3)
    else {
        return defer("recursor-tail-peel");
    };
    let (motive_binder, minor_binder, major_binder) = (
        recursor_tail_binders[0],
        recursor_tail_binders[1],
        recursor_tail_binders[2],
    );

    let mut builder = StructuralTermBuilder::new();
    let mut imported_units = 0usize;
    let mut recursor_param_imports = Vec::with_capacity(parameter_count);
    for (binder_type, _) in &recursor_param_binders {
        let Some(imported) = builder.import(recursor_type, *binder_type) else {
            return defer("recursor-parameter-import");
        };
        imported_units += imported.index().saturating_add(1);
        recursor_param_imports.push(imported);
    }
    // Motive domain: `∀ t : D p_1 … p_k, Sort v`. Under the motive's own `t`
    // binder, parameter i sits at depth `k - i + 1`; the domain of `t` sees
    // only the parameters, so parameter i sits at depth `k - i + 1` there too
    // when counted from inside `t`'s body — both are the same telescope.
    let d_application_at = |builder: &mut StructuralTermBuilder, base: usize| -> Option<ExprId> {
        let head = builder.constant(name, family_universes);
        let mut applied = head;
        for index in 0..parameter_count {
            let depth = base - index;
            if depth == 0 {
                return None;
            }
            let argument = builder.bvar(depth as u32 - 1);
            applied = builder.apply(applied, argument);
        }
        Some(applied)
    };
    let Some(d_under_params) = d_application_at(&mut builder, parameter_count) else {
        return defer("motive-domain-depth");
    };
    let motive_sort = builder.sort_parameter(motive_universe);
    let motive_domain = builder.forall("t", BinderStyle::Default, d_under_params, motive_sort);
    imported_units += 4;

    // Minor premise: peel the decoded minor telescope for its field types
    // (they live in this exact binding context, so imports transfer), then
    // rebuild its body as `motive (mk p_1 … p_k x_1 … x_f)`.
    let Some((minor_field_binders, _)) =
        peel_binders_at(recursor_type, minor_binder.0, field_count)
    else {
        return defer("minor-field-peel");
    };
    let mut minor_field_imports = Vec::with_capacity(field_count);
    for (binder_type, _) in &minor_field_binders {
        let Some(imported) = builder.import(recursor_type, *binder_type) else {
            return defer("minor-field-import");
        };
        imported_units += imported.index().saturating_add(1);
        minor_field_imports.push(imported);
    }
    let constructor_head = builder.constant(&constructor_name, family_universes);
    // Inside the minor TYPE — the domain of the minor binder, which its own
    // body does not see: fields are innermost (`x_f .. x_1` at depths
    // `0 .. f-1`), the motive sits at `f`, and parameter i sits at
    // `f + k + 1 - i`. The constructor application is parameters first.
    let mut minor_call = constructor_head;
    for index in 0..parameter_count {
        let depth = parameter_count + field_count + 1 - index;
        let argument = builder.bvar(depth as u32 - 1);
        minor_call = builder.apply(minor_call, argument);
    }
    for index in 0..field_count {
        let field_depth = (field_count - 1 - index) as u32;
        let argument = builder.bvar(field_depth);
        minor_call = builder.apply(minor_call, argument);
    }
    let motive_reference = builder.bvar(field_count as u32);
    let mut minor_body = builder.apply(motive_reference, minor_call);
    for field_type in minor_field_imports.iter().rev() {
        minor_body = builder.forall("x", BinderStyle::Default, *field_type, minor_body);
    }
    imported_units += 4;

    // Major premise: `D p_1 … p_k` under the parameters, the motive, and the
    // minor premise — all three binders precede it, so the base is `k + 2`.
    let Some(major_type) = d_application_at(&mut builder, parameter_count + 2) else {
        return defer("major-domain-depth");
    };
    let motive_at_two = builder.bvar(2);
    let major_at_zero = builder.bvar(0);
    let body = builder.apply(motive_at_two, major_at_zero);
    let mut expected = builder.forall("major", major_binder.1, major_type, body);
    expected = builder.forall("minor", minor_binder.1, minor_body, expected);
    expected = builder.forall("motive", motive_binder.1, motive_domain, expected);
    for (index, (_, style)) in recursor_param_binders.iter().enumerate() {
        expected = builder.forall("p", *style, recursor_param_imports[index], expected);
    }
    if imported_units.saturating_mul(8) > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
        return InductiveVerdict::Deferred(InductiveSupportLimit::ExpectedArenaUnits {
            observed: imported_units.saturating_mul(8),
            limit: MAX_INDUCTIVE_EXPECTED_ARENA_UNITS,
        });
    }
    let Some(expected_recursor) = builder.finish(expected) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(recursor_type, &expected_recursor, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) | Err(_) => return defer("recursor-compare"),
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }

    // -- the single iota rule: `minor applied to the fields` ---------------
    let rule = recursor_metadata.rules().first();
    let Some(rule) = rule else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if rule.constructor() != &constructor_name {
        if std::env::var_os("FLN_CHECKER_TRACE").is_some() {
            eprintln!("fln-checker: class-block reject at rule-constructor for {recursor_name:?}");
        }
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    if rule.num_fields() != field_count as u32 {
        if std::env::var_os("FLN_CHECKER_TRACE").is_some() {
            eprintln!("fln-checker: class-block reject at rule-field-count for {recursor_name:?}");
        }
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    if !rule_rhs_is_minor_applied_to_fields(rule.rhs(), parameter_count, field_count) {
        if std::env::var_os("FLN_CHECKER_TRACE").is_some() {
            eprintln!("fln-checker: class-block reject at rule-rhs-shape for {recursor_name:?}");
            eprintln!("rhs arena: {:?}", rule.rhs().nodes());
        }
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    if let Err(verdict) = stage_inductive_member(&staged, recursor, environment_budget, cancelled) {
        return verdict;
    }
    InductiveVerdict::Admitted(InductiveAdmission {
        members: vec![name.clone(), constructor_name, recursor_name],
    })
}

/// Peel exactly `expected` leading `Forall` binders starting at `cursor`,
/// returning each `(binder_type, style)` in order together with the cursor
/// just past the last binder, or `None` when the term runs out first.
fn peel_binders_at(
    expression: &WireExpr,
    cursor: ExprId,
    expected: usize,
) -> Option<(Vec<(ExprId, BinderStyle)>, ExprId)> {
    let mut binders = Vec::new();
    let mut cursor = cursor;
    for _ in 0..expected {
        match expression.node(cursor)? {
            ExprNode::Forall {
                binder_type,
                body,
                style,
                ..
            } => {
                binders.push((*binder_type, *style));
                cursor = *body;
            }
            _ => return None,
        }
    }
    Some((binders, cursor))
}

fn is_sort_at(expression: &WireExpr, cursor: ExprId) -> bool {
    matches!(expression.node(cursor), Some(ExprNode::Sort { .. }))
}

/// The iota-rule right-hand side of this family is `minor x_1 … x_f`: after
/// the `k` parameter lambdas, the motive lambda, the minor lambda, and the
/// `f` field lambdas, the body applies the minor reference (depth `f`) to
/// the field references (depths `f-1 … 0`, fields in declaration order) and
/// nothing else.
fn rule_rhs_is_minor_applied_to_fields(
    rhs: &WireExpr,
    parameter_count: usize,
    field_count: usize,
) -> bool {
    let mut cursor = rhs.root();
    // Rule right-hand sides are TERMS: their binders are lambdas (the pin
    // also emits Forall here for some families, so both are accepted).
    for _ in 0..parameter_count + field_count + 2 {
        match rhs.node(cursor) {
            Some(ExprNode::Lambda { body, .. }) | Some(ExprNode::Forall { body, .. }) => {
                cursor = *body;
            }
            _ => return false,
        }
    }
    // Walk the application spine: head must be `Bound(f)`, arguments must be
    // `Bound(f-1) … Bound(0)` in order.
    let mut arguments = Vec::new();
    loop {
        match rhs.node(cursor) {
            Some(ExprNode::Apply { function, argument }) => {
                arguments.push(*argument);
                cursor = *function;
            }
            Some(ExprNode::Bound { index }) => {
                if *index != field_count as u32 {
                    return false;
                }
                break;
            }
            _ => return false,
        }
    }
    arguments.reverse();
    arguments.iter().enumerate().all(|(position, argument)| {
        matches!(
            rhs.node(*argument),
            Some(ExprNode::Bound { index })
                if *index == (field_count - 1 - position) as u32
        )
    })
}

/// Reconstruct the universe-polymorphic one-constructor `Init.PUnit` block.
fn admit_init_punit(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    let Some(family_universe) = declaration.level_parameters().first() else {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: 0,
        });
    };
    if declaration.level_parameters().len() != 1 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    let unit = checker_child(name, "unit");
    if metadata.constructors() != std::slice::from_ref(&unit)
        || declarations.len() != 3
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let mut builder = StructuralTermBuilder::new();
    let expected_type = builder.sort_parameter(family_universe);
    let Some(expected_type) = builder.finish(expected_type) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged =
        match stage_inductive_member(environment, inductive, environment_budget, cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
    let Some(constructor) = declarations.iter().find(|entry| entry.name() == &unit) else {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing { name: unit });
    };
    let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: checker_child(name, "unit"),
        });
    };
    let Some(expected_type) = punit_constructor_type(family_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    if constructor.declaration().safety() != ConstantSafety::Safe
        || constructor.declaration().level_parameters() != std::slice::from_ref(family_universe)
        || constructor_metadata.inductive() != name
        || constructor_metadata.index() != 0
        || constructor_metadata.num_parameters() != 0
        || constructor_metadata.num_fields() != 0
        || environment.find(&unit).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { name: unit });
    }
    match compare_inductive_expression(
        constructor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: checker_child(name, "unit"),
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &unit,
        constructor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&unit, verdict);
    }
    staged = match stage_inductive_member(&staged, constructor, environment_budget, cancelled) {
        Ok(environment) => environment,
        Err(verdict) => return verdict,
    };
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || levels.len() != 2
        || levels.get(1) != Some(family_universe)
        || motive_universe == family_universe
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 0
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 1
        || recursor_metadata.rules().len() != 1
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = punit_recursor_type(motive_universe, family_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    let Some(rule) = recursor_metadata.rules().first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let Some(expected_rhs) = punit_rule_rhs(motive_universe, family_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    if rule.constructor() != &unit || rule.num_fields() != 0 {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    match compare_inductive_expression(rule.rhs(), &expected_rhs, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) = stage_inductive_member(&staged, recursor, environment_budget, cancelled) {
        return verdict;
    }
    InductiveVerdict::Admitted(InductiveAdmission {
        members: vec![name.clone(), unit, recursor_name],
    })
}

/// Reconstruct the named empty proposition `Init.False` and its eliminator.
fn admit_init_false(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    if !declaration.level_parameters().is_empty() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_recursive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    if !metadata.constructors().is_empty()
        || declarations.len() != 2
        || environment.find(name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
            name: name.clone(),
        });
    }
    let mut builder = StructuralTermBuilder::new();
    let expected_type = builder.sort_zero();
    let Some(expected_type) = builder.finish(expected_type) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(declaration.type_(), &expected_type, comparison, cancelled) {
        Ok(true) => {}
        Ok(false) => return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse),
        Err(verdict) => return verdict,
    }
    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let staged = match stage_inductive_member(environment, inductive, environment_budget, cancelled)
    {
        Ok(environment) => environment,
        Err(verdict) => return verdict,
    };
    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let levels = recursor.declaration().level_parameters();
    let Some(motive_universe) = levels.first() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    if recursor.declaration().safety() != ConstantSafety::Safe
        || levels.len() != 1
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 0
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || recursor_metadata.num_minors() != 0
        || !recursor_metadata.rules().is_empty()
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let Some(expected_type) = empty_recursor_type(name, motive_universe) else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_type,
        comparison,
        cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged,
        &recursor_name,
        recursor.declaration(),
        &budget,
        cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) = stage_inductive_member(&staged, recursor, environment_budget, cancelled) {
        return verdict;
    }
    InductiveVerdict::Admitted(InductiveAdmission {
        members: vec![name.clone(), recursor_name],
    })
}

/// Independently reconstruct one bounded, field-bearing, single `Type`
/// inductive block, including direct self-recursive fields.
pub fn admit_inductive(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
) -> InductiveVerdict {
    admit_inductive_with(
        environment,
        declarations,
        budget,
        environment_budget,
        || false,
    )
}

/// [`admit_inductive`] with cooperative cancellation shared by all row and
/// expression checks.
pub fn admit_inductive_with(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    mut cancelled: impl FnMut() -> bool,
) -> InductiveVerdict {
    let maximum_rows = MAX_NONRECURSIVE_CONSTRUCTORS.saturating_add(2);
    if declarations.len() > maximum_rows {
        return InductiveVerdict::Deferred(InductiveSupportLimit::DeclarationRows {
            observed: declarations.len(),
            limit: maximum_rows,
        });
    }
    let mut comparison = StructuralComparisonControl::new(budget.conversion.quick);
    let mut inductives = declarations
        .iter()
        .filter(|entry| entry.declaration().kind() == ConstantKind::Inductive);
    let Some(inductive) = inductives.next() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingInductive);
    };
    let extra_types = inductives.count();
    if extra_types != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MultipleTypes {
            observed: extra_types.saturating_add(1),
        });
    }
    let name = inductive.name();
    let declaration = inductive.declaration();
    let Some(metadata) = declaration.inductive_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::MissingMetadata {
            name: name.clone(),
        });
    };
    if declaration.safety() != ConstantSafety::Safe {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Unsafe);
    }
    if name == &checker_atom("Empty")
        && declaration.level_parameters().is_empty()
        && metadata.num_parameters() == 0
    {
        return admit_init_empty(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if name == &checker_atom("False")
        && declaration.level_parameters().is_empty()
        && metadata.num_parameters() == 0
    {
        return admit_init_false(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if name == &checker_atom("PEmpty")
        && declaration.level_parameters().len() == 1
        && metadata.num_parameters() == 0
    {
        return admit_init_pempty(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if name == &checker_atom("Unit")
        && declaration.level_parameters().is_empty()
        && metadata.num_parameters() == 0
    {
        return admit_init_unit(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if name == &checker_atom("PUnit")
        && declaration.level_parameters().len() == 1
        && metadata.num_parameters() == 0
    {
        return admit_init_punit(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if name == &checker_atom("Or")
        && declaration.level_parameters().is_empty()
        && metadata.num_parameters() == 2
    {
        return admit_init_or(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if name == &checker_atom("And")
        && declaration.level_parameters().is_empty()
        && metadata.num_parameters() == 2
    {
        return admit_init_and(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if name == &checker_atom("Bool")
        && declaration.level_parameters().is_empty()
        && metadata.num_parameters() == 0
    {
        return admit_init_bool(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if name == &checker_atom("Option")
        && declaration.level_parameters().len() == 1
        && metadata.num_parameters() == 1
    {
        return admit_init_option(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if name == &checker_atom("List")
        && declaration.level_parameters().len() == 1
        && metadata.num_parameters() == 1
    {
        return admit_init_list(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if name == &checker_atom("Sum")
        && declaration.level_parameters().len() == 2
        && metadata.num_parameters() == 2
    {
        return admit_init_sum(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
            "inl",
            "inr",
        );
    }
    if name == &checker_atom("Except")
        && declaration.level_parameters().len() == 2
        && metadata.num_parameters() == 2
    {
        return admit_init_sum(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
            "error",
            "ok",
        );
    }
    if name == &checker_atom("Prod")
        && declaration.level_parameters().len() == 2
        && metadata.num_parameters() == 2
    {
        return admit_init_prod(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    // Class-shaped blocks: one constructor, zero indices, non-recursive, at
    // least one family universe. Gated here so only plausible members enter
    // the shape judgment; everything else keeps the ordinary deferral path
    // below.
    if !declaration.level_parameters().is_empty()
        && metadata.mutual() == std::slice::from_ref(name)
        && metadata.num_indices() == 0
        && metadata.num_nested() == 0
        && !metadata.is_recursive()
        && !metadata.is_reflexive()
        && metadata.constructors().len() == 1
        && declarations.len() == 3
        && declaration.safety() == ConstantSafety::Safe
    {
        return admit_class_block(
            environment,
            declarations,
            inductive,
            budget,
            environment_budget,
            &mut comparison,
            &mut cancelled,
        );
    }
    if !declaration.level_parameters().is_empty() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::UniverseParameters {
            observed: declaration.level_parameters().len(),
        });
    }
    if metadata.mutual() != std::slice::from_ref(name) {
        return InductiveVerdict::Deferred(InductiveSupportLimit::MutualMetadata);
    }
    if metadata.num_parameters() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Parameters {
            observed: metadata.num_parameters(),
        });
    }
    if metadata.num_indices() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Indices {
            observed: metadata.num_indices(),
        });
    }
    if metadata.num_nested() != 0 {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        });
    }
    if metadata.is_reflexive() {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Reflexive);
    }
    if metadata.constructors().is_empty()
        || metadata.constructors().len() > MAX_NONRECURSIVE_CONSTRUCTORS
    {
        return InductiveVerdict::Deferred(InductiveSupportLimit::ConstructorCount {
            observed: metadata.constructors().len(),
            limit: MAX_NONRECURSIVE_CONSTRUCTORS,
        });
    }
    let Some(expected_type) = nonrecursive_inductive_type() else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        declaration.type_(),
        &expected_type,
        &mut comparison,
        &mut cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse);
        }
        Err(verdict) => return verdict,
    }

    let expected_count = metadata.constructors().len().saturating_add(2);
    if declarations.len() != expected_count {
        return InductiveVerdict::Rejected(InductiveRejection::DeclarationCount {
            observed: declarations.len(),
            expected: expected_count,
        });
    }
    if environment.find(name).is_some() {
        return InductiveVerdict::Rejected(InductiveRejection::NameAlreadyDeclared {
            name: name.clone(),
        });
    }

    if let Err(verdict) =
        declared_type_is_a_type(environment, name, declaration, &budget, &mut cancelled)
    {
        return map_member_preamble(name, verdict);
    }
    let mut staged_environment =
        match stage_inductive_member(environment, inductive, environment_budget, &mut cancelled) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };

    let mut seen = BTreeSet::new();
    let mut members = Vec::new();
    let mut checked_constructors = Vec::new();
    let mut total_fields = 0usize;
    let mut imported_arena_units = 0usize;
    members.push(name.clone());
    for (index, constructor_name) in metadata.constructors().iter().enumerate() {
        if let Err(stop) = comparison.comparison(&mut cancelled) {
            return InductiveVerdict::Inconclusive(InductiveStop::Structural(stop));
        }
        if !seen.insert(constructor_name) {
            return InductiveVerdict::Rejected(InductiveRejection::RepeatedConstructor {
                name: constructor_name.clone(),
            });
        }
        let Some(constructor) = declarations
            .iter()
            .find(|entry| entry.name() == constructor_name)
        else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
                name: constructor_name.clone(),
            });
        };
        let Some(constructor_metadata) = constructor.declaration().constructor_metadata() else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name.clone(),
            });
        };
        let expected_index = match u32::try_from(index) {
            Ok(index) => index,
            Err(_) => {
                return InductiveVerdict::Deferred(InductiveSupportLimit::ConstructorCount {
                    observed: metadata.constructors().len(),
                    limit: MAX_NONRECURSIVE_CONSTRUCTORS,
                });
            }
        };
        if constructor.declaration().safety() != ConstantSafety::Safe
            || !constructor.declaration().level_parameters().is_empty()
            || constructor_metadata.inductive() != name
            || constructor_metadata.index() != expected_index
            || constructor_metadata.num_parameters() != 0
            || environment.find(constructor_name).is_some()
        {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name.clone(),
            });
        }
        let field_count = match usize::try_from(constructor_metadata.num_fields()) {
            Ok(count) => count,
            Err(_) => {
                return InductiveVerdict::Deferred(InductiveSupportLimit::FieldCount {
                    observed: usize::MAX,
                    limit: MAX_NONRECURSIVE_FIELDS,
                });
            }
        };
        total_fields = total_fields.saturating_add(field_count);
        if total_fields > MAX_NONRECURSIVE_FIELDS {
            return InductiveVerdict::Deferred(InductiveSupportLimit::FieldCount {
                observed: total_fields,
                limit: MAX_NONRECURSIVE_FIELDS,
            });
        }
        let Some(fields) = constructor_shape(constructor.declaration().type_(), name, field_count)
        else {
            return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                name: constructor_name.clone(),
            });
        };
        let mut direct_recursive_fields = Vec::new();
        for field in &fields {
            match classify_field_recursion(field, name, &mut comparison, &mut cancelled) {
                Ok(FieldRecursion::Absent) => direct_recursive_fields.push(false),
                Ok(FieldRecursion::DirectSelf) if metadata.is_recursive() => {
                    direct_recursive_fields.push(true);
                }
                Ok(FieldRecursion::DirectSelf) => {
                    return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                        name: constructor_name.clone(),
                    });
                }
                Ok(FieldRecursion::Unsupported) if metadata.is_recursive() => {
                    return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
                }
                Ok(FieldRecursion::Unsupported) => {
                    return InductiveVerdict::Rejected(InductiveRejection::ConstructorShape {
                        name: constructor_name.clone(),
                    });
                }
                Err(verdict) => return verdict,
            }
            imported_arena_units = imported_arena_units
                .saturating_add(field.type_root.index().saturating_add(1))
                .saturating_add(field.source.levels().len());
        }
        if let Err(verdict) = declared_type_is_a_type(
            &staged_environment,
            constructor_name,
            constructor.declaration(),
            &budget,
            &mut cancelled,
        ) {
            return map_member_preamble(constructor_name, verdict);
        }
        staged_environment = match stage_inductive_member(
            &staged_environment,
            constructor,
            environment_budget,
            &mut cancelled,
        ) {
            Ok(environment) => environment,
            Err(verdict) => return verdict,
        };
        checked_constructors.push(CheckedConstructor {
            name: constructor_name,
            fields,
            direct_recursive_fields,
        });
        members.push(constructor_name.clone());
    }

    let expected_arena_units = imported_arena_units.saturating_mul(2).saturating_add(
        metadata
            .constructors()
            .len()
            .saturating_add(total_fields)
            .saturating_add(4)
            .saturating_mul(8),
    );
    if expected_arena_units > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
        return InductiveVerdict::Deferred(InductiveSupportLimit::ExpectedArenaUnits {
            observed: expected_arena_units,
            limit: MAX_INDUCTIVE_EXPECTED_ARENA_UNITS,
        });
    }
    if metadata.is_recursive()
        && !checked_constructors
            .iter()
            .flat_map(|constructor| constructor.direct_recursive_fields.iter())
            .any(|direct| *direct)
    {
        return InductiveVerdict::Deferred(InductiveSupportLimit::Recursive);
    }

    let recursor_name = checker_child(name, "rec");
    let Some(recursor) = declarations
        .iter()
        .find(|entry| entry.name() == &recursor_name)
    else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
            name: recursor_name,
        });
    };
    let Some(recursor_metadata) = recursor.declaration().recursor_metadata() else {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    };
    let recursor_levels = recursor.declaration().level_parameters();
    if recursor.declaration().safety() != ConstantSafety::Safe
        || recursor_levels.len() != 1
        || recursor_metadata.mutual() != std::slice::from_ref(name)
        || recursor_metadata.num_parameters() != 0
        || recursor_metadata.num_indices() != 0
        || recursor_metadata.num_motives() != 1
        || u32::try_from(metadata.constructors().len()).ok() != Some(recursor_metadata.num_minors())
        || recursor_metadata.rules().len() != metadata.constructors().len()
        || recursor_metadata.k()
        || environment.find(&recursor_name).is_some()
    {
        return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
            name: recursor_name,
        });
    }
    let level_parameter = &recursor_levels[0];
    let Some(expected_recursor_type) =
        nonrecursive_recursor_type(name, &checked_constructors, level_parameter)
    else {
        return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
    };
    match compare_inductive_expression(
        recursor.declaration().type_(),
        &expected_recursor_type,
        &mut comparison,
        &mut cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        Err(verdict) => return verdict,
    }
    for (index, (constructor, rule)) in metadata
        .constructors()
        .iter()
        .zip(recursor_metadata.rules())
        .enumerate()
    {
        let expected_fields = checked_constructors[index].fields.len();
        if rule.constructor() != constructor
            || usize::try_from(rule.num_fields()).ok() != Some(expected_fields)
        {
            return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                name: recursor_name,
            });
        }
        let Some(expected_rhs) =
            nonrecursive_rule_rhs(name, &checked_constructors, level_parameter, index)
        else {
            return InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow);
        };
        match compare_inductive_expression(
            rule.rhs(),
            &expected_rhs,
            &mut comparison,
            &mut cancelled,
        ) {
            Ok(true) => {}
            Ok(false) => {
                return InductiveVerdict::Rejected(InductiveRejection::RecursorShape {
                    name: recursor_name,
                });
            }
            Err(verdict) => return verdict,
        }
    }
    if let Err(verdict) = declared_type_is_a_type(
        &staged_environment,
        &recursor_name,
        recursor.declaration(),
        &budget,
        &mut cancelled,
    ) {
        return map_member_preamble(&recursor_name, verdict);
    }
    if let Err(verdict) = stage_inductive_member(
        &staged_environment,
        recursor,
        environment_budget,
        &mut cancelled,
    ) {
        return verdict;
    }
    members.push(recursor_name);
    InductiveVerdict::Admitted(InductiveAdmission { members })
}

struct ExpectedQuotient {
    kind: QuotientKind,
    name: WireName,
    level_parameters: Vec<WireName>,
    type_: WireExpr,
}

fn quotient_types() -> Option<Vec<ExpectedQuotient>> {
    let quot = checker_atom("Quot");
    let eq = checker_atom("Eq");
    let u = checker_atom("u");
    let v = checker_atom("v");

    let quot_type = {
        let mut b = StructuralTermBuilder::new();
        let alpha_sort = b.sort_parameter(&u);
        let alpha0 = b.bvar(0);
        let alpha1 = b.bvar(1);
        let prop = b.sort_zero();
        let inner = b.arrow(alpha1, prop);
        let relation = b.arrow(alpha0, inner);
        let result = b.sort_parameter(&u);
        let body = b.arrow(relation, result);
        let root = b.forall("α", BinderStyle::Implicit, alpha_sort, body);
        b.finish(root)?
    };

    let quot_mk_type = {
        let mut b = StructuralTermBuilder::new();
        let alpha_sort = b.sort_parameter(&u);
        let alpha0 = b.bvar(0);
        let alpha1 = b.bvar(1);
        let prop = b.sort_zero();
        let relation_tail = b.arrow(alpha1, prop);
        let relation = b.arrow(alpha0, relation_tail);
        let alpha_for_a = b.bvar(1);
        let quot_const = b.constant(&quot, std::slice::from_ref(&u));
        let alpha_for_quot = b.bvar(2);
        let quot_alpha = b.apply(quot_const, alpha_for_quot);
        let relation_for_quot = b.bvar(1);
        let quot_app = b.apply(quot_alpha, relation_for_quot);
        let a = b.forall("a", BinderStyle::Default, alpha_for_a, quot_app);
        let r = b.forall("r", BinderStyle::Default, relation, a);
        let root = b.forall("α", BinderStyle::Implicit, alpha_sort, r);
        b.finish(root)?
    };

    let quot_lift_type = {
        let mut b = StructuralTermBuilder::new();
        let alpha_sort = b.sort_parameter(&u);
        let alpha0 = b.bvar(0);
        let alpha1 = b.bvar(1);
        let prop = b.sort_zero();
        let relation_tail = b.arrow(alpha1, prop);
        let relation = b.arrow(alpha0, relation_tail);
        let beta_sort = b.sort_parameter(&v);
        let f_alpha = b.bvar(2);
        let f_beta = b.bvar(1);
        let f_type = b.arrow(f_alpha, f_beta);

        let sanity_alpha_a = b.bvar(3);
        let sanity_alpha_b = b.bvar(4);
        let relation_fn = b.bvar(4);
        let a_arg = b.bvar(1);
        let relation_a = b.apply(relation_fn, a_arg);
        let b_arg = b.bvar(0);
        let relation_ab = b.apply(relation_a, b_arg);
        let eq_const = b.constant(&eq, std::slice::from_ref(&v));
        let beta = b.bvar(4);
        let eq_beta = b.apply(eq_const, beta);
        let f_for_a = b.bvar(3);
        let a_for_f = b.bvar(2);
        let f_a = b.apply(f_for_a, a_for_f);
        let eq_fa = b.apply(eq_beta, f_a);
        let f_for_b = b.bvar(3);
        let b_for_f = b.bvar(1);
        let f_b = b.apply(f_for_b, b_for_f);
        let eq_fafb = b.apply(eq_fa, f_b);
        let sanity_body = b.arrow(relation_ab, eq_fafb);
        let sanity_b = b.forall("b", BinderStyle::Default, sanity_alpha_b, sanity_body);
        let sanity = b.forall("a", BinderStyle::Default, sanity_alpha_a, sanity_b);

        let quot_const = b.constant(&quot, std::slice::from_ref(&u));
        let quot_alpha = b.bvar(4);
        let quot_applied_alpha = b.apply(quot_const, quot_alpha);
        let quot_relation = b.bvar(3);
        let quot_app = b.apply(quot_applied_alpha, quot_relation);
        let result_beta = b.bvar(3);
        let quotient_to_beta = b.arrow(quot_app, result_beta);
        let after_sanity = b.arrow(sanity, quotient_to_beta);
        let f = b.forall("f", BinderStyle::Default, f_type, after_sanity);
        let beta = b.forall("β", BinderStyle::Implicit, beta_sort, f);
        let r = b.forall("r", BinderStyle::Implicit, relation, beta);
        let root = b.forall("α", BinderStyle::Implicit, alpha_sort, r);
        b.finish(root)?
    };

    let quot_ind_type = {
        let mut b = StructuralTermBuilder::new();
        let alpha_sort = b.sort_parameter(&u);
        let alpha0 = b.bvar(0);
        let alpha1 = b.bvar(1);
        let prop = b.sort_zero();
        let relation_tail = b.arrow(alpha1, prop);
        let relation = b.arrow(alpha0, relation_tail);

        let quot_const = b.constant(&quot, std::slice::from_ref(&u));
        let beta_alpha = b.bvar(1);
        let beta_quot_alpha = b.apply(quot_const, beta_alpha);
        let beta_relation = b.bvar(0);
        let beta_quot = b.apply(beta_quot_alpha, beta_relation);
        let beta_prop = b.sort_zero();
        let beta_type = b.arrow(beta_quot, beta_prop);

        let mk_alpha = b.bvar(2);
        let beta_fn = b.bvar(1);
        let quot_mk_name = checker_child(&quot, "mk");
        let quot_mk = b.constant(&quot_mk_name, std::slice::from_ref(&u));
        let mk_const_alpha = b.bvar(3);
        let mk_with_alpha = b.apply(quot_mk, mk_const_alpha);
        let mk_relation = b.bvar(2);
        let mk_with_relation = b.apply(mk_with_alpha, mk_relation);
        let mk_value = b.bvar(0);
        let mk_application = b.apply(mk_with_relation, mk_value);
        let beta_mk = b.apply(beta_fn, mk_application);
        let mk_premise = b.forall("a", BinderStyle::Default, mk_alpha, beta_mk);

        let q_quot = b.constant(&quot, std::slice::from_ref(&u));
        let q_alpha = b.bvar(3);
        let q_quot_alpha = b.apply(q_quot, q_alpha);
        let q_relation = b.bvar(2);
        let q_type = b.apply(q_quot_alpha, q_relation);
        let q_beta = b.bvar(2);
        let q_value = b.bvar(0);
        let q_result = b.apply(q_beta, q_value);
        let q = b.forall("q", BinderStyle::Default, q_type, q_result);
        let mk = b.forall("mk", BinderStyle::Default, mk_premise, q);
        let beta = b.forall("β", BinderStyle::Implicit, beta_type, mk);
        let r = b.forall("r", BinderStyle::Implicit, relation, beta);
        let root = b.forall("α", BinderStyle::Implicit, alpha_sort, r);
        b.finish(root)?
    };

    Some(vec![
        ExpectedQuotient {
            kind: QuotientKind::Type,
            name: quot.clone(),
            level_parameters: vec![u.clone()],
            type_: quot_type,
        },
        ExpectedQuotient {
            kind: QuotientKind::Constructor,
            name: checker_child(&quot, "mk"),
            level_parameters: vec![u.clone()],
            type_: quot_mk_type,
        },
        ExpectedQuotient {
            kind: QuotientKind::Lift,
            name: checker_child(&quot, "lift"),
            level_parameters: vec![u.clone(), v],
            type_: quot_lift_type,
        },
        ExpectedQuotient {
            kind: QuotientKind::Induction,
            name: checker_child(&quot, "ind"),
            level_parameters: vec![u],
            type_: quot_ind_type,
        },
    ])
}

fn expected_equality_type(parameter: &WireName) -> Option<WireExpr> {
    let mut b = StructuralTermBuilder::new();
    let alpha_sort = b.sort_parameter(parameter);
    let alpha0 = b.bvar(0);
    let alpha1 = b.bvar(1);
    let prop = b.sort_zero();
    let inner = b.arrow(alpha1, prop);
    let outer = b.arrow(alpha0, inner);
    let root = b.forall("α", BinderStyle::Implicit, alpha_sort, outer);
    b.finish(root)
}

fn expected_equality_constructor_type(parameter: &WireName) -> Option<WireExpr> {
    let mut b = StructuralTermBuilder::new();
    let eq = checker_atom("Eq");
    let alpha_sort = b.sort_parameter(parameter);
    let alpha_for_a = b.bvar(0);
    let eq_const = b.constant(&eq, std::slice::from_ref(parameter));
    let eq_alpha = b.bvar(1);
    let eq_at_alpha = b.apply(eq_const, eq_alpha);
    let a_left = b.bvar(0);
    let eq_left = b.apply(eq_at_alpha, a_left);
    let a_right = b.bvar(0);
    let eq_refl = b.apply(eq_left, a_right);
    let a = b.forall("a", BinderStyle::Default, alpha_for_a, eq_refl);
    let root = b.forall("α", BinderStyle::Implicit, alpha_sort, a);
    b.finish(root)
}

fn compare_or_verdict(
    actual: &WireExpr,
    expected: &WireExpr,
    control: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<bool, QuotientVerdict> {
    // The pinned quotient initializer uses `expr_eq_fn<false>`: binder names
    // and binder annotations are presentation metadata at this authority
    // boundary. Keeping this policy separate from inductive recursor
    // regeneration prevents the two structural contracts from being conflated.
    match structural_expression_equal(actual, expected, control, false, cancelled) {
        Ok(Ok(equal)) => Ok(equal),
        Ok(Err(stop)) => Err(QuotientVerdict::Inconclusive(stop)),
        Err(fault) => Err(QuotientVerdict::InternalFault(QuotientFault::Structural(
            fault,
        ))),
    }
}

/// Independently check the pinned four-row quotient primitive initialization.
pub fn admit_quotient(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    budget: AdmissionBudget,
) -> QuotientVerdict {
    admit_quotient_with(environment, declarations, budget, || false)
}

/// [`admit_quotient`] with cooperative cancellation at every structural pair.
pub fn admit_quotient_with(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    budget: AdmissionBudget,
    mut cancelled: impl FnMut() -> bool,
) -> QuotientVerdict {
    let mut comparison = StructuralComparisonControl::new(budget.conversion.quick);
    let eq = checker_atom("Eq");
    let Some(eq_declaration) = environment.find(&eq) else {
        return QuotientVerdict::Rejected(QuotientRejection::EqualityTypeMissing);
    };
    let Some(eq_metadata) = eq_declaration.inductive_metadata() else {
        return QuotientVerdict::Rejected(QuotientRejection::EqualityTypeShape);
    };
    if eq_declaration.level_parameters().len() != 1 || eq_metadata.constructors().len() != 1 {
        return QuotientVerdict::Rejected(QuotientRejection::EqualityTypeShape);
    }
    let eq_refl = &eq_metadata.constructors()[0];
    let parameter = &eq_declaration.level_parameters()[0];
    let Some(expected_eq) = expected_equality_type(parameter) else {
        return QuotientVerdict::InternalFault(QuotientFault::ExpectedArenaOverflow);
    };
    match compare_or_verdict(
        eq_declaration.type_(),
        &expected_eq,
        &mut comparison,
        &mut cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return QuotientVerdict::Rejected(QuotientRejection::EqualityTypeShape);
        }
        Err(verdict) => return verdict,
    }

    let Some(refl_declaration) = environment.find(eq_refl) else {
        return QuotientVerdict::Rejected(QuotientRejection::EqualityConstructorMissing);
    };
    if refl_declaration.kind() != ConstantKind::Constructor
        || refl_declaration.level_parameters().len() != 1
    {
        return QuotientVerdict::Rejected(QuotientRejection::EqualityConstructorShape);
    }
    let Some(expected_refl) =
        expected_equality_constructor_type(&refl_declaration.level_parameters()[0])
    else {
        return QuotientVerdict::InternalFault(QuotientFault::ExpectedArenaOverflow);
    };
    match compare_or_verdict(
        refl_declaration.type_(),
        &expected_refl,
        &mut comparison,
        &mut cancelled,
    ) {
        Ok(true) => {}
        Ok(false) => {
            return QuotientVerdict::Rejected(QuotientRejection::EqualityConstructorShape);
        }
        Err(verdict) => return verdict,
    }

    let Some(expected) = quotient_types() else {
        return QuotientVerdict::InternalFault(QuotientFault::ExpectedArenaOverflow);
    };
    if declarations.len() != expected.len() {
        return QuotientVerdict::Rejected(QuotientRejection::DeclarationCount {
            observed: declarations.len(),
        });
    }
    let mut members = Vec::new();
    for expected in expected {
        let Some(entry) = declarations
            .iter()
            .find(|entry| entry.declaration().quotient_kind() == Some(expected.kind))
        else {
            return QuotientVerdict::Rejected(QuotientRejection::DeclarationMissing {
                kind: expected.kind,
            });
        };
        if entry.name() != &expected.name {
            return QuotientVerdict::Rejected(QuotientRejection::DeclarationMissing {
                kind: expected.kind,
            });
        }
        if environment.find(&expected.name).is_some() {
            return QuotientVerdict::Rejected(QuotientRejection::NameAlreadyDeclared {
                name: expected.name,
            });
        }
        if entry.declaration().level_parameters() != expected.level_parameters {
            return QuotientVerdict::Rejected(QuotientRejection::UnexpectedLevelParameters {
                name: expected.name,
            });
        }
        match compare_or_verdict(
            entry.declaration().type_(),
            &expected.type_,
            &mut comparison,
            &mut cancelled,
        ) {
            Ok(true) => members.push(expected.name),
            Ok(false) => {
                return QuotientVerdict::Rejected(QuotientRejection::UnexpectedType {
                    name: expected.name,
                });
            }
            Err(verdict) => return verdict,
        }
    }
    QuotientVerdict::Admitted(QuotientAdmission { members })
}

/// KR-977 — the environment a member is checked in: everything already there,
/// plus every OTHER member's header.
///
/// A predeclared peer is built with `ConstantDeclaration::header`, which hardcodes
/// an absent body, so a peer is visible by name and declared type and cannot be
/// delta-unfolded while checking against it. That is not a precaution this
/// function takes; it is what `header` is.
///
/// Built through `ConstantEnvironment::build` rather than a second construction
/// path, so a predeclared environment cannot drift from an ordinary one.
fn predeclare_peers(
    environment: &ConstantEnvironment,
    block: &[ConstantEntry],
    skip: usize,
) -> Result<ConstantEnvironment, ()> {
    let mut entries: Vec<ConstantEntry> = environment
        .constants()
        .map(|(name, declaration)| ConstantEntry::new(name.clone(), declaration.clone()))
        .collect();
    for (index, entry) in block.iter().enumerate() {
        if index == skip {
            continue;
        }
        let declaration = entry.declaration();
        entries.push(ConstantEntry::new(
            entry.name().clone(),
            ConstantDeclaration::header(
                declaration.level_parameters().to_vec(),
                declaration.type_().clone(),
                declaration.kind(),
                declaration.safety(),
            ),
        ));
    }
    match ConstantEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => Ok(environment),
        _ => Err(()),
    }
}

/// KR-977a — the block is a well-formed set.
fn block_shape(block: &[ConstantEntry]) -> Result<(), BlockRejection> {
    if block.is_empty() {
        return Err(BlockRejection::EmptyBlock);
    }

    for (second, entry) in block.iter().enumerate() {
        for (first, earlier) in block.iter().enumerate().take(second) {
            if earlier.name() == entry.name() {
                return Err(BlockRejection::RepeatedMember {
                    member: entry.name().clone(),
                    first,
                    second,
                });
            }
        }
    }

    // Membership is symmetric: every member's own mutual list must name exactly
    // the block supplied. Compared as SETS rather than sequences, because the
    // order a declaration lists its peers in is not a semantic fact and refusing
    // a permutation would be a wall against a correct block.
    let supplied: BTreeSet<&WireName> = block.iter().map(ConstantEntry::name).collect();
    for entry in block {
        let Some(body) = entry.declaration().definition_body() else {
            return Err(BlockRejection::MemberDeclaresNoBlock {
                member: entry.name().clone(),
            });
        };
        if body.mutual().is_empty() {
            return Err(BlockRejection::MemberDeclaresNoBlock {
                member: entry.name().clone(),
            });
        }
        let declared: BTreeSet<&WireName> = body.mutual().iter().collect();
        if declared != supplied {
            return Err(BlockRejection::AsymmetricMembership {
                member: entry.name().clone(),
            });
        }
    }
    Ok(())
}

/// KR-977b — one safety class across the block, and not the safe one.
fn block_safety(block: &[ConstantEntry]) -> Result<(), BlockRejection> {
    // Emptiness is `block_shape`'s to refuse and it runs FIRST, so this returns
    // cleanly rather than checking again. A second check here would be
    // SUBSUMED -- and it was: a planted mutant deleting `block_shape`'s check
    // survived, because this one caught the same case and the campaign scored a
    // rule as tested that nothing tested. One property, one owner.
    let Some(first) = block.first() else {
        return Ok(());
    };
    let expected = quarantine_of(first.declaration());
    for entry in block {
        let found = quarantine_of(entry.declaration());
        if found != expected {
            return Err(BlockRejection::NonUniformSafety {
                member: entry.name().clone(),
                expected,
                found,
            });
        }
    }
    if expected == Quarantine::None {
        return Err(BlockRejection::SafeBlock {
            member: first.name().clone(),
        });
    }
    Ok(())
}
