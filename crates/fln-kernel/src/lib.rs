//! **fln-kernel** — Crucible — the trusted kernel (plan §8, D6; bead
//! franken_lean-zht, K1 bootstrap slice). One authority, nothing else:
//!
//! ```text
//! check : Environment × Declaration × Budget → Verdict
//! ```
//!
//! Covenant posture (§8.1): `forbid(unsafe_code)`; dependencies exactly the
//! allow-direct set (fln-core, fln-env, fln-bignum here; fln-hash joins with the
//! receipt slice); zero I/O, zero threads, zero global mutable state,
//! zero plugin hooks; the ≤ 12 KLOC covenant is CI-enforced by structure-guard.
//!
//! K1 slice scope (beads franken_lean-zht + franken_lean-5p2 + franken_lean-irm):
//! typing KR-100..112, whnf KR-200..205 with recursor computation — quotient
//! reduction KR-955, inductive iota KR-316, K conversion KR-317 — literal
//! acceleration KR-313/KR-314 (fln-bignum-backed Nat arithmetic, String
//! expansion), defeq subset KR-300..315 + KR-903, admission KR-970..974 for
//! axioms/definitions/theorems. Every
//! exhaustion is a typed [`verdict::Verdict::Inconclusive`] carrying its
//! consumption profile (FL-INV-07); an unimplemented reduction can only cause a
//! rejection, never an acceptance.

#![forbid(unsafe_code)]

pub mod verdict;

mod tc;

use fln_core::name::Name;
use fln_env::constants::{AxiomVal, DefinitionVal, TheoremVal};
use fln_env::environment::Environment;

use crate::tc::{Stop, TypeChecker};
use crate::verdict::{Budget, RejectClass, Verdict};

/// The declaration envelope this slice admits. Inductives, opaques, quotients, and
/// mutual blocks are follow-up slices (their admission rules are specified at
/// KR-6xx/KR-95x/KR-977).
#[derive(Debug, Clone, PartialEq)]
pub enum Declaration {
    Axiom(AxiomVal),
    Defn(DefinitionVal),
    Thm(TheoremVal),
}

impl Declaration {
    fn name(&self) -> &Name {
        match self {
            Declaration::Axiom(v) => &v.base.name,
            Declaration::Defn(v) => &v.base.name,
            Declaration::Thm(v) => &v.base.name,
        }
    }

    fn level_params(&self) -> &[Name] {
        match self {
            Declaration::Axiom(v) => &v.base.level_params,
            Declaration::Defn(v) => &v.base.level_params,
            Declaration::Thm(v) => &v.base.level_params,
        }
    }
}

/// The kernel's one authority (§8.2b): checks the declaration against the
/// environment under the given budget. Nothing else in the program can admit a
/// constant (FL-INV-02); callers extend the environment only on `Accepted`.
pub fn check(env: &Environment, decl: &Declaration, budget: Budget) -> Verdict {
    let mut checker = TypeChecker::new(env, decl.level_params(), budget);
    let outcome = check_inner(env, decl, &mut checker);
    let consumption = checker.consumption();
    match outcome {
        Ok(()) => Verdict::Accepted { consumption },
        Err(Stop::Reject(class, message)) => Verdict::Rejected {
            class,
            message,
            consumption,
        },
        Err(Stop::Exhausted(reason)) => Verdict::Inconclusive {
            reason,
            consumption,
        },
    }
}

fn check_inner(
    env: &Environment,
    decl: &Declaration,
    checker: &mut TypeChecker<'_>,
) -> Result<(), Stop> {
    // KR-970: one name, one constant.
    if env.contains(decl.name()) {
        return Err(Stop::Reject(
            RejectClass::AlreadyDeclared,
            format!("`{}` is already declared", decl.name().to_display_string()),
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
) -> Verdict {
    let mut checker = TypeChecker::new(env, lparams, budget);
    let outcome = checker.def_eq_public(t, s, 0);
    let consumption = checker.consumption();
    match outcome {
        Ok(true) => Verdict::Accepted { consumption },
        Ok(false) => Verdict::Rejected {
            class: RejectClass::NotDefEq,
            message: "terms are not definitionally equal".to_string(),
            consumption,
        },
        Err(Stop::Reject(class, message)) => Verdict::Rejected {
            class,
            message,
            consumption,
        },
        Err(Stop::Exhausted(reason)) => Verdict::Inconclusive {
            reason,
            consumption,
        },
    }
}
