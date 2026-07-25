//! **fln-kernel** — Crucible — the trusted kernel (plan §8, D6; bead
//! franken_lean-zht, K1 bootstrap slice). One authority, nothing else:
//!
//! ```text
//! check : Environment × Declaration × Budget → Outcome<Verdict>
//! ```
//!
//! Covenant posture (§8.1): `forbid(unsafe_code)`; dependencies exactly the
//! allow-direct set (fln-core, fln-env, fln-bignum here; fln-hash joins with the
//! receipt slice); zero I/O, zero threads, zero global mutable state,
//! zero plugin hooks; the ≤ 12 KLOC covenant is CI-enforced by structure-guard.
//!
//! K1 slice scope (beads franken_lean-zht + 5p2 + irm + ap6): typing
//! KR-100..112, whnf KR-200..205 with recursor computation — quotient
//! reduction KR-955, inductive iota KR-316, K conversion KR-317 — literal
//! acceleration KR-313/KR-314, defeq subset KR-300..315 + KR-903, admission
//! KR-970..974 for axioms/definitions (all safety levels)/theorems, inductive
//! BLOCK admission KR-600..608 with elimination universes KR-700..702 and
//! full recursor REGENERATION KR-800..803 (decoded rows are untrusted and
//! compared against the kernel's own generation), and quotient initialization
//! KR-950..954. Every
//! exhaustion is a typed [`fln_core::outcome::Outcome::Inconclusive`] carrying
//! bounded resource facts (FL-INV-07); an unimplemented reduction can only cause
//! a rejection, never an acceptance.

#![forbid(unsafe_code)]

pub mod verdict;

mod admit;
mod tc;

use fln_core::diag::ResourceReason;
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_env::constants::{
    AxiomVal, ConstantInfo, DefinitionSafety, DefinitionVal, QuotVal, TheoremVal,
};
use fln_env::environment::Environment;

pub use crate::admit::InductiveBlock;
use crate::tc::{Stop, TypeChecker};
use crate::verdict::{Budget, RejectClass, Verdict};

/// The declaration envelope. Axioms, definitions (all safety levels), and
/// theorems check individually; an inductive block (types + constructors +
/// recursors, decoded and untrusted) and the quotient initialization check as
/// units under the KR-6xx/7xx/8xx/95x rules (bead franken_lean-ap6). Opaques
/// and mutual definition blocks remain follow-up slices (KR-97x).
#[derive(Debug, Clone, PartialEq)]
pub enum Declaration {
    Axiom(AxiomVal),
    Defn(DefinitionVal),
    Thm(TheoremVal),
    Inductive(InductiveBlock),
    Quotient(Vec<QuotVal>),
}

impl Declaration {
    fn name(&self) -> Option<&Name> {
        match self {
            Declaration::Axiom(v) => Some(&v.base.name),
            Declaration::Defn(v) => Some(&v.base.name),
            Declaration::Thm(v) => Some(&v.base.name),
            Declaration::Inductive(_) | Declaration::Quotient(_) => None,
        }
    }

    fn level_params(&self) -> &[Name] {
        match self {
            Declaration::Axiom(v) => &v.base.level_params,
            Declaration::Defn(v) => &v.base.level_params,
            Declaration::Thm(v) => &v.base.level_params,
            Declaration::Inductive(_) | Declaration::Quotient(_) => &[],
        }
    }
}

/// The kernel's one authority (§8.2b): checks the declaration against the
/// environment under the given budget. Nothing else in the program can admit a
/// constant (FL-INV-02); callers extend the environment only on `Accepted`.
pub fn check(env: &Environment, decl: &Declaration, budget: Budget) -> Outcome<Verdict> {
    // Block declarations own their freshness/level laws and their scratch
    // environments; they meter consumption themselves.
    match decl {
        Declaration::Inductive(block) => {
            let (outcome, consumption) = admit::check_inductive_block(env, block, budget);
            return check_result_to_outcome(outcome, consumption, budget);
        }
        Declaration::Quotient(decls) => {
            let (outcome, consumption) = admit::check_quotient_init(env, decls, budget);
            return check_result_to_outcome(outcome, consumption, budget);
        }
        _ => {}
    }
    // Pin add_definition (unsafe branch) / add_mutual (partial|unsafe):
    // a NON-SAFE definition checks its header against `env`, is added to a
    // scratch environment (non-safe definitions may be recursive — the
    // `._unsafe_rec` implementation helpers reference themselves), and checks
    // its body there, under a checker running at the definition's own safety.
    if let Declaration::Defn(v) = decl
        && v.safety != DefinitionSafety::Safe
    {
        return check_nonsafe_definition(env, v, budget);
    }
    let mut checker = TypeChecker::new(env, decl.level_params(), budget);
    let outcome = check_inner(env, decl, &mut checker);
    let consumption = checker.consumption();
    check_result_to_outcome(outcome, consumption, budget)
}

/// Pin environment.cpp:160/225 (`add_definition` unsafe branch, `add_mutual`):
/// header first (name/level laws + the type is a sort, under a checker at the
/// definition's own safety), then the body against a scratch env CONTAINING
/// the definition, defeq to the declared type. Non-safe definitions can be
/// recursive — that is exactly why the body checks after the add.
fn check_nonsafe_definition(
    env: &Environment,
    v: &DefinitionVal,
    budget: Budget,
) -> Outcome<Verdict> {
    let mut total = verdict::Consumption::default();
    let mut header = TypeChecker::new_with_safety(env, &v.base.level_params, budget, v.safety);
    let header_outcome = check_header(
        env,
        &v.base.name,
        &v.base.level_params,
        &v.base.type_,
        &mut header,
    );
    let c = header.consumption();
    drop(header);
    total.steps_used += c.steps_used;
    total.max_depth = total.max_depth.max(c.max_depth);
    if let Err(stop) = header_outcome {
        return stop_to_outcome(stop, total, budget);
    }
    let scratch = match env.add_decl(ConstantInfo::Defn(v.clone())) {
        Ok(scratch) => scratch,
        Err(_) => {
            return Outcome::complete(Verdict::Rejected {
                class: RejectClass::AlreadyDeclared,
                message: format!("`{}` is already declared", v.base.name.to_display_string()),
                consumption: total,
            });
        }
    };
    let remaining = Budget {
        steps: budget.steps.saturating_sub(total.steps_used),
        depth: budget.depth,
    };
    let mut body =
        TypeChecker::new_with_safety(&scratch, &v.base.level_params, remaining, v.safety);
    let outcome = (|| -> Result<(), Stop> {
        let value_type = body.infer(&v.value, 0)?;
        if !body.def_eq_public(&value_type, &v.base.type_, 0)? {
            return Err(Stop::Reject(
                RejectClass::DefinitionTypeMismatch,
                format!(
                    "non-safe declaration body type does not match its declared type: body has `{}`, declared `{}`",
                    tc::brief_public(&value_type),
                    tc::brief_public(&v.base.type_)
                ),
            ));
        }
        Ok(())
    })();
    let c = body.consumption();
    total.steps_used += c.steps_used;
    total.max_depth = total.max_depth.max(c.max_depth);
    check_result_to_outcome(outcome, total, budget)
}

fn check_result_to_outcome(
    result: Result<(), Stop>,
    consumption: verdict::Consumption,
    budget: Budget,
) -> Outcome<Verdict> {
    match result {
        Ok(()) => Outcome::complete(Verdict::Accepted { consumption }),
        Err(stop) => stop_to_outcome(stop, consumption, budget),
    }
}

fn stop_to_outcome(
    stop: Stop,
    consumption: verdict::Consumption,
    budget: Budget,
) -> Outcome<Verdict> {
    match stop {
        Stop::Reject(class, message) => Outcome::complete(Verdict::Rejected {
            class,
            message,
            consumption,
        }),
        Stop::Exhausted(reason) => exhaustion_outcome(reason, consumption, budget),
    }
}

fn exhaustion_outcome(
    reason: verdict::ExhaustionReason,
    consumption: verdict::Consumption,
    budget: Budget,
) -> Outcome<Verdict> {
    let usage = match reason {
        verdict::ExhaustionReason::Steps => ResourceUsage {
            reason: ResourceReason::Heartbeats {
                consumed: consumption.steps_used,
                limit: budget.steps,
            },
            allowed: budget.steps,
            observed: consumption.steps_used,
        },
        verdict::ExhaustionReason::Depth => ResourceUsage {
            reason: ResourceReason::RecursionDepth {
                limit: u64::from(budget.depth),
            },
            allowed: u64::from(budget.depth),
            observed: u64::from(consumption.max_depth),
        },
    };
    if usage.is_genuine_exhaustion() {
        Outcome::Inconclusive(Inconclusive::resource(usage))
    } else {
        Outcome::InternalFault(InternalFault::new(
            "FL-INV-07",
            format!(
                "kernel reported {reason:?} exhaustion without exceeding its allowance: \
                 allowed={}, observed={}",
                usage.allowed, usage.observed
            ),
        ))
    }
}

/// The shared header laws (KR-970/971/972) for a single-constant declaration.
fn check_header(
    env: &Environment,
    name: &Name,
    level_params: &[Name],
    type_: &fln_core::expr::Expr,
    checker: &mut TypeChecker<'_>,
) -> Result<(), Stop> {
    if env.contains(name) {
        return Err(Stop::Reject(
            RejectClass::AlreadyDeclared,
            format!("`{}` is already declared", name.to_display_string()),
        ));
    }
    for (i, p) in level_params.iter().enumerate() {
        if level_params[..i].contains(p) {
            return Err(Stop::Reject(
                RejectClass::DuplicateLevelParams,
                format!(
                    "duplicate universe level parameter `{}`",
                    p.to_display_string()
                ),
            ));
        }
    }
    let type_sort = checker.infer(type_, 0)?;
    let type_sort = checker.whnf_public(&type_sort, 0)?;
    if !matches!(type_sort.node(), fln_core::expr::ExprNode::Sort { .. }) {
        return Err(Stop::Reject(
            RejectClass::SortExpected,
            "declaration type is not a sort".to_string(),
        ));
    }
    Ok(())
}

fn check_inner(
    env: &Environment,
    decl: &Declaration,
    checker: &mut TypeChecker<'_>,
) -> Result<(), Stop> {
    // KR-970: one name, one constant.
    if let Some(name) = decl.name()
        && env.contains(name)
    {
        return Err(Stop::Reject(
            RejectClass::AlreadyDeclared,
            format!("`{}` is already declared", name.to_display_string()),
        ));
    }
    // KR-971: distinct level parameters.
    let params = decl.level_params();
    for (i, p) in params.iter().enumerate() {
        if params[..i].contains(p) {
            return Err(Stop::Reject(
                RejectClass::DuplicateLevelParams,
                format!(
                    "duplicate universe level parameter `{}`",
                    p.to_display_string()
                ),
            ));
        }
    }
    // KR-972: the type checks to a sort.
    let (type_, body): (&fln_core::expr::Expr, Option<&fln_core::expr::Expr>) = match decl {
        Declaration::Axiom(v) => (&v.base.type_, None),
        Declaration::Defn(v) => (&v.base.type_, Some(&v.value)),
        Declaration::Thm(v) => (&v.base.type_, Some(&v.value)),
        // Dispatched to admit.rs before this path; nothing to do here.
        Declaration::Inductive(_) | Declaration::Quotient(_) => return Ok(()),
    };
    let type_sort = checker.infer(type_, 0)?;
    let type_sort = checker.whnf_public(&type_sort, 0)?;
    if !matches!(type_sort.node(), fln_core::expr::ExprNode::Sort { .. }) {
        return Err(Stop::Reject(
            RejectClass::SortExpected,
            "declaration type is not a sort".to_string(),
        ));
    }
    // KR-974 (theorems): the type must be a proposition.
    if matches!(decl, Declaration::Thm(_)) {
        let is_prop = matches!(
            type_sort.node(),
            fln_core::expr::ExprNode::Sort { level } if level.is_equiv(&fln_core::level::Level::zero())
        );
        if !is_prop {
            return Err(Stop::Reject(
                RejectClass::TheoremNotProp,
                "theorem type must be a proposition".to_string(),
            ));
        }
    }
    // KR-974 (bodies): the inferred body type must be defeq to the declared type.
    if let Some(body) = body {
        let body_type = checker.infer(body, 0)?;
        if !checker.def_eq_public(&body_type, type_, 0)? {
            return Err(Stop::Reject(
                RejectClass::DefinitionTypeMismatch,
                format!(
                    "declaration body type does not match its declared type: body has `{}`, declared `{}`",
                    tc::brief_public(&body_type),
                    tc::brief_public(type_)
                ),
            ));
        }
    }
    Ok(())
}

/// A standalone defeq query under the same budget discipline (the K2/Tribunal
/// cross-check surface). Verdict semantics match [`check`].
pub fn check_def_eq(
    env: &Environment,
    lparams: &[Name],
    t: &fln_core::expr::Expr,
    s: &fln_core::expr::Expr,
    budget: Budget,
) -> Outcome<Verdict> {
    let mut checker = TypeChecker::new(env, lparams, budget);
    let outcome = checker.def_eq_public(t, s, 0);
    let consumption = checker.consumption();
    match outcome {
        Ok(true) => Outcome::complete(Verdict::Accepted { consumption }),
        Ok(false) => Outcome::complete(Verdict::Rejected {
            class: RejectClass::NotDefEq,
            message: "terms are not definitionally equal".to_string(),
            consumption,
        }),
        Err(Stop::Reject(class, message)) => Outcome::complete(Verdict::Rejected {
            class,
            message,
            consumption,
        }),
        Err(Stop::Exhausted(reason)) => exhaustion_outcome(reason, consumption, budget),
    }
}
