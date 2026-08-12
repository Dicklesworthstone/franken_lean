//! Declaration-block admission: inductive families (KR-600..608), elimination
//! universes (KR-700..702), recursor generation (KR-800..803), and quotient
//! initialization (KR-950..954) — bead franken_lean-ap6, transcribed from the
//! pin's `kernel/inductive.cpp` (`add_inductive_fn`) and `kernel/quot.cpp`.
//!
//! The decoded block rows (`InductiveVal`, `ConstructorVal`, `RecursorVal`,
//! `QuotVal`) are UNTRUSTED input: the kernel re-derives every observable —
//! flags, counts, elimination level, K-target, and the full recursor types and
//! iota rules — from the declaration alone and compares against the decoded
//! rows. Any mismatch is a typed [`RejectClass::BlockMismatch`], never a
//! silent trust. One deliberate, documented exception: a block containing
//! NESTED inductives (`num_nested > 0`; exactly `Lean.Syntax` in Init.Prelude)
//! is admitted under a PARTIAL ruleset — well-typedness of every type,
//! constructor, and recursor, parameter/arity cross-checks, but neither
//! strict positivity nor recursor regeneration, because both are defined on
//! the pin's `_nested.*` auxiliary translation (inductive.cpp:800-1100),
//! which operates on the pre-elaboration declaration the olean does not
//! carry. That translation is a named follow-up slice; until it lands the
//! partial family is surfaced by the replay census, not hidden.
//!
//! Traversal discipline matches tc.rs: every helper that recurses carries an
//! explicit depth converted to typed exhaustion, and all typing/reduction work
//! runs through budget-metered [`TypeChecker`] instances.

use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId};
use fln_core::level::Level;
use fln_core::name::{LeafView, Name};
use fln_core::outcome::Outcome;
use fln_env::constants::{
    ConstantInfo, ConstructorVal, InductiveVal, QuotKind, QuotVal, RecursorRule, RecursorVal,
};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, DeclarationPlan, Environment};
use fln_env::pmap::CollisionBudget;

use crate::tc::{Stop, TypeChecker};
use crate::verdict::{Budget, Consumption, ExhaustionReason, RejectClass};

type KResult<T> = Result<T, Stop>;

fn reject<T>(class: RejectClass, message: impl Into<String>) -> KResult<T> {
    Err(Stop::Reject(class, message.into()))
}

/// The decoded, untrusted rows of one inductive block, assembled by the caller
/// (module order preserved within each list).
#[derive(Debug, Clone, PartialEq)]
pub struct InductiveBlock {
    pub types: Vec<InductiveVal>,
    pub ctors: Vec<ConstructorVal>,
    pub recursors: Vec<RecursorVal>,
}

/// A telescope entry: the admission engine's own locals, adopted into every
/// [`TypeChecker`] it spawns. `name`/`info` feed faithful reconstruction when
/// the telescope is re-bound (`mk_pi_locals`/`mk_lam_locals`).
#[derive(Debug, Clone)]
struct Local {
    id: FVarId,
    name: Name,
    info: BinderInfo,
    type_: Expr,
}

impl Local {
    fn fvar(&self) -> Expr {
        Expr::fvar(self.id.clone())
    }
}

/// Depth guard for the engine's own structural walks (abstraction, loose-bvar
/// scans, implicit inference). Declaration types are shallow; this converts a
/// hostile deep term into typed exhaustion, never a stack fault.
const WALK_DEPTH: u32 = 2_048;

fn depth_guard(depth: u32) -> KResult<()> {
    if depth > WALK_DEPTH {
        return Err(Stop::Exhausted(ExhaustionReason::Depth));
    }
    Ok(())
}

/// Replace `fvar id` by `bvar k` (k bumped under binders) — the inverse of
/// instantiation, used to re-bind engine telescopes.
fn abstract_fvar(e: &Expr, id: &FVarId, k: u32, depth: u32) -> KResult<Expr> {
    depth_guard(depth)?;
    if !e.has_fvar() {
        return Ok(e.clone());
    }
    Ok(match e.node() {
        ExprNode::FVar { id: found } => {
            if found == id {
                Expr::bvar(k).map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?
            } else {
                e.clone()
            }
        }
        ExprNode::App { f, a } => Expr::app(
            abstract_fvar(f, id, k, depth + 1)?,
            abstract_fvar(a, id, k, depth + 1)?,
        ),
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::lam(
            binder_name.clone(),
            abstract_fvar(binder_type, id, k, depth + 1)?,
            abstract_fvar(body, id, k + 1, depth + 1)?,
            *binder_info,
        ),
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::forall_e(
            binder_name.clone(),
            abstract_fvar(binder_type, id, k, depth + 1)?,
            abstract_fvar(body, id, k + 1, depth + 1)?,
            *binder_info,
        ),
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            non_dep,
        } => Expr::let_e(
            decl_name.clone(),
            abstract_fvar(type_, id, k, depth + 1)?,
            abstract_fvar(value, id, k, depth + 1)?,
            abstract_fvar(body, id, k + 1, depth + 1)?,
            *non_dep,
        ),
        ExprNode::MData { data, expr } => {
            Expr::mdata(data.clone(), abstract_fvar(expr, id, k, depth + 1)?)
        }
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => Expr::proj(
            struct_name.clone(),
            *idx,
            abstract_fvar(expr, id, k, depth + 1)?,
        ),
        _ => e.clone(),
    })
}

/// `Π locals, body` — right fold with abstraction (pin `local_ctx::mk_pi`).
fn mk_pi_locals(locals: &[Local], body: Expr) -> KResult<Expr> {
    let mut acc = body;
    for local in locals.iter().rev() {
        let abstracted = abstract_fvar(&acc, &local.id, 0, 0)?;
        acc = Expr::forall_e(
            local.name.clone(),
            local.type_.clone(),
            abstracted,
            local.info,
        );
    }
    Ok(acc)
}

/// `λ locals, body` — right fold with abstraction (pin `local_ctx::mk_lambda`).
fn mk_lam_locals(locals: &[Local], body: Expr) -> KResult<Expr> {
    let mut acc = body;
    for local in locals.iter().rev() {
        let abstracted = abstract_fvar(&acc, &local.id, 0, 0)?;
        acc = Expr::lam(
            local.name.clone(),
            local.type_.clone(),
            abstracted,
            local.info,
        );
    }
    Ok(acc)
}

/// Lift every loose bvar of `e` by `amount` (the substitutes of
/// [`subst_loose_bvars`] cross binders on the way in). Range-pruned.
fn lift_loose_bvars(e: &Expr, cutoff: u32, amount: u32, depth: u32) -> KResult<Expr> {
    depth_guard(depth)?;
    if amount == 0 || e.loose_bvar_range() <= cutoff {
        return Ok(e.clone());
    }
    Ok(match e.node() {
        ExprNode::BVar { idx } => {
            if *idx >= cutoff {
                Expr::bvar(idx + amount).map_err(|_| {
                    Stop::Reject(
                        RejectClass::BlockMismatch,
                        "nested translation lifted a bound variable out of range".into(),
                    )
                })?
            } else {
                e.clone()
            }
        }
        ExprNode::App { f, a } => Expr::app(
            lift_loose_bvars(f, cutoff, amount, depth + 1)?,
            lift_loose_bvars(a, cutoff, amount, depth + 1)?,
        ),
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::lam(
            binder_name.clone(),
            lift_loose_bvars(binder_type, cutoff, amount, depth + 1)?,
            lift_loose_bvars(body, cutoff + 1, amount, depth + 1)?,
            *binder_info,
        ),
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::forall_e(
            binder_name.clone(),
            lift_loose_bvars(binder_type, cutoff, amount, depth + 1)?,
            lift_loose_bvars(body, cutoff + 1, amount, depth + 1)?,
            *binder_info,
        ),
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            non_dep,
        } => Expr::let_e(
            decl_name.clone(),
            lift_loose_bvars(type_, cutoff, amount, depth + 1)?,
            lift_loose_bvars(value, cutoff, amount, depth + 1)?,
            lift_loose_bvars(body, cutoff + 1, amount, depth + 1)?,
            *non_dep,
        ),
        ExprNode::MData { data, expr } => Expr::mdata(
            data.clone(),
            lift_loose_bvars(expr, cutoff, amount, depth + 1)?,
        ),
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => Expr::proj(
            struct_name.clone(),
            *idx,
            lift_loose_bvars(expr, cutoff, amount, depth + 1)?,
        ),
        _ => e.clone(),
    })
}

/// Simultaneous substitution of the outermost `substs.len()` loose bvars:
/// `bvar (k + j)` becomes `substs[substs.len()-1-j]` lifted by `k` — the
/// restore step instantiates the translation's param-canonical templates at
/// occurrence sites whose arguments are themselves open terms, which the
/// closed-substitute [`TypeChecker::instantiate`] deliberately cannot do.
fn subst_loose_bvars(e: &Expr, k: u32, substs: &[Expr], depth: u32) -> KResult<Expr> {
    depth_guard(depth)?;
    let n = substs.len() as u32;
    if n == 0 || e.loose_bvar_range() <= k {
        return Ok(e.clone());
    }
    Ok(match e.node() {
        ExprNode::BVar { idx } => {
            if *idx >= k && *idx < k + n {
                let j = (idx - k) as usize;
                lift_loose_bvars(&substs[substs.len() - 1 - j], 0, k, depth + 1)?
            } else if *idx >= k + n {
                Expr::bvar(idx - n).unwrap_or_else(|_| e.clone())
            } else {
                e.clone()
            }
        }
        ExprNode::App { f, a } => Expr::app(
            subst_loose_bvars(f, k, substs, depth + 1)?,
            subst_loose_bvars(a, k, substs, depth + 1)?,
        ),
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::lam(
            binder_name.clone(),
            subst_loose_bvars(binder_type, k, substs, depth + 1)?,
            subst_loose_bvars(body, k + 1, substs, depth + 1)?,
            *binder_info,
        ),
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::forall_e(
            binder_name.clone(),
            subst_loose_bvars(binder_type, k, substs, depth + 1)?,
            subst_loose_bvars(body, k + 1, substs, depth + 1)?,
            *binder_info,
        ),
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            non_dep,
        } => Expr::let_e(
            decl_name.clone(),
            subst_loose_bvars(type_, k, substs, depth + 1)?,
            subst_loose_bvars(value, k, substs, depth + 1)?,
            subst_loose_bvars(body, k + 1, substs, depth + 1)?,
            *non_dep,
        ),
        ExprNode::MData { data, expr } => {
            Expr::mdata(data.clone(), subst_loose_bvars(expr, k, substs, depth + 1)?)
        }
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => Expr::proj(
            struct_name.clone(),
            *idx,
            subst_loose_bvars(expr, k, substs, depth + 1)?,
        ),
        _ => e.clone(),
    })
}

/// Does `bvar idx` occur loose in `e`? Range-pruned.
fn has_loose_bvar(e: &Expr, idx: u32, depth: u32) -> KResult<bool> {
    depth_guard(depth)?;
    if e.loose_bvar_range() <= idx {
        return Ok(false);
    }
    Ok(match e.node() {
        ExprNode::BVar { idx: found } => *found == idx,
        ExprNode::App { f, a } => {
            has_loose_bvar(f, idx, depth + 1)? || has_loose_bvar(a, idx, depth + 1)?
        }
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => {
            has_loose_bvar(binder_type, idx, depth + 1)?
                || has_loose_bvar(body, idx + 1, depth + 1)?
        }
        ExprNode::LetE {
            type_, value, body, ..
        } => {
            has_loose_bvar(type_, idx, depth + 1)?
                || has_loose_bvar(value, idx, depth + 1)?
                || has_loose_bvar(body, idx + 1, depth + 1)?
        }
        ExprNode::MData { expr, .. } => has_loose_bvar(expr, idx, depth + 1)?,
        ExprNode::Proj { expr, .. } => has_loose_bvar(expr, idx, depth + 1)?,
        _ => false,
    })
}

/// `has_loose_bvars_in_domain` (pin expr.cpp:370): does `bvar vidx` occur in a
/// (transitively relevant) Π domain of `b`?
fn has_loose_bvars_in_domain(b: &Expr, vidx: u32, strict: bool, depth: u32) -> KResult<bool> {
    depth_guard(depth)?;
    if let ExprNode::ForallE {
        binder_type,
        body,
        binder_info,
        ..
    } = b.node()
    {
        if has_loose_bvar(binder_type, vidx, depth + 1)?
            && (*binder_info == BinderInfo::Default
                || has_loose_bvars_in_domain(body, 0, strict, depth + 1)?)
        {
            return Ok(true);
        }
        has_loose_bvars_in_domain(body, vidx + 1, strict, depth + 1)
    } else if !strict {
        has_loose_bvar(b, vidx, depth)
    } else {
        Ok(false)
    }
}

/// `infer_implicit` (pin expr.cpp:480, strict): mark leading Π binders
/// implicit when a later domain (transitively) needs them.
fn infer_implicit_strict(t: &Expr, depth: u32) -> KResult<Expr> {
    depth_guard(depth)?;
    let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = t.node()
    else {
        return Ok(t.clone());
    };
    let new_body = infer_implicit_strict(body, depth + 1)?;
    let info = if *binder_info != BinderInfo::Default {
        *binder_info
    } else if has_loose_bvars_in_domain(&new_body, 0, true, depth + 1)? {
        BinderInfo::Implicit
    } else {
        BinderInfo::Default
    };
    Ok(Expr::forall_e(
        binder_name.clone(),
        binder_type.clone(),
        new_body,
        info,
    ))
}

/// `mk_rec_name` (inductive.cpp:22).
fn mk_rec_name(ind: &Name) -> Name {
    Name::str(ind.clone(), "rec")
}

/// `consumeTypeAnnotations` (vendor Lean/Expr.lean:1741, applied by the pin's
/// `mk_local_decl` to every telescope local): strip head applications of the
/// type-annotation gadgets — `outParam`/`semiOutParam` at arity 1 keep their
/// argument, `optParam`/`autoParam` at arity 2 keep their FIRST argument.
/// Nested annotations are not removed, exactly as at the pin.
fn consume_type_annotations(e: &Expr) -> Expr {
    fn gadget(e: &Expr) -> Option<Expr> {
        let mut args: Vec<&Expr> = Vec::new();
        let mut head = e;
        while let ExprNode::App { f, a } = head.node() {
            args.push(a);
            head = f;
        }
        args.reverse();
        let ExprNode::Const { name, .. } = head.node() else {
            return None;
        };
        if !name.parent().is_anonymous() {
            return None;
        }
        match name.leaf_view() {
            LeafView::Str(s) if (s == "outParam" || s == "semiOutParam") && args.len() == 1 => {
                Some(args[0].clone())
            }
            LeafView::Str(s) if (s == "optParam" || s == "autoParam") && args.len() == 2 => {
                Some(args[0].clone())
            }
            _ => None,
        }
    }
    let mut current = e.clone();
    while let Some(inner) = gadget(&current) {
        current = inner;
    }
    current
}

/// `Name.hasMacroScopes` (vendor Init/Meta/Defs.lean hygiene encoding): the
/// leaf-side walk skips numeric scope components; the first string component
/// must be the `_hyg` marker.
fn has_macro_scopes(n: &Name) -> bool {
    let mut cur = n.clone();
    loop {
        match cur.leaf_view() {
            LeafView::Num(_) => cur = cur.parent(),
            LeafView::Str(s) => return s == "_hyg",
            LeafView::Anonymous => return false,
        }
    }
}

/// `Name.appendAfter` (vendor Init/Meta/Defs.lean:317): macro-scope aware —
/// the suffix lands on the BASE name (the part before the `_@` scope marker),
/// and the scope components are re-attached verbatim. On the base: a string
/// leaf is extended in place; anything else gains a new string component.
fn append_after(n: &Name, suffix: &str) -> Name {
    #[derive(Clone)]
    enum Comp {
        Str(String),
        Num(u64),
    }
    fn split(n: &Name) -> Vec<Comp> {
        let mut out = Vec::new();
        let mut cur = n.clone();
        loop {
            match cur.leaf_view() {
                LeafView::Str(s) => out.push(Comp::Str(s.to_string())),
                LeafView::Num(v) => out.push(Comp::Num(v)),
                LeafView::Anonymous => break,
            }
            cur = cur.parent();
        }
        out.reverse();
        out
    }
    fn rebuild(comps: &[Comp], onto: Name) -> Name {
        let mut cur = onto;
        for c in comps {
            cur = match c {
                Comp::Str(s) => Name::str(cur, s.clone()),
                Comp::Num(v) => Name::num(cur, *v),
            };
        }
        cur
    }
    fn append_base(n: &Name, suffix: &str) -> Name {
        match n.leaf_view() {
            LeafView::Str(s) => Name::str(n.parent(), format!("{s}{suffix}")),
            _ => Name::str(n.clone(), suffix.to_string()),
        }
    }
    if !has_macro_scopes(n) {
        return append_base(n, suffix);
    }
    let comps = split(n);
    let Some(marker) = comps
        .iter()
        .position(|c| matches!(c, Comp::Str(s) if s == "_@"))
    else {
        return append_base(n, suffix);
    };
    let base = rebuild(&comps[..marker], Name::anonymous());
    let appended = append_base(&base, suffix);
    rebuild(&comps[marker..], appended)
}

/// `name::replace_prefix(prefix, anonymous)` for the minor-premise names
/// (inductive.cpp:670): strip `prefix` off the front when it matches.
fn strip_prefix(n: &Name, prefix: &Name) -> Name {
    fn components(n: &Name) -> Vec<Name> {
        let mut out = Vec::new();
        let mut cur = n.clone();
        while !cur.is_anonymous() {
            out.push(cur.clone());
            cur = cur.parent();
        }
        out.reverse();
        out
    }
    let n_parts = components(n);
    let p_parts = components(prefix);
    if p_parts.len() > n_parts.len() || n_parts[p_parts.len() - 1] != *prefix {
        return n.clone();
    }
    let mut rebuilt = Name::anonymous();
    for part in &n_parts[p_parts.len()..] {
        rebuilt = match part.leaf_view() {
            LeafView::Str(s) => Name::str(rebuilt, s.to_string()),
            LeafView::Num(v) => Name::num(rebuilt, v),
            LeafView::Anonymous => rebuilt,
        };
    }
    rebuilt
}

/// The block-admission engine (pin `add_inductive_fn`). Owns the evolving
/// scratch environment, the telescope, and the budget meter.
struct Engine<'a> {
    env: Environment,
    /// The environment as it stood BEFORE this block's declarations entered
    /// the scratch env — the nested-inductive translation checks its
    /// synthesized auxiliary block against this baseline (pin
    /// `add_inductive`, inductive.cpp:1116-1120).
    base_env: Environment,
    block: &'a InductiveBlock,
    lparams: Vec<Name>,
    levels: Vec<Level>,
    nparams: usize,
    is_unsafe: bool,
    budget: Budget,
    used: Consumption,
    locals: Vec<Local>,
    fresh: u64,
    // Filled by the phases:
    params: Vec<Local>,
    nindices: Vec<usize>,
    ind_consts: Vec<Expr>,
    result_level: Level,
    result_is_not_zero: bool,
    elim_level: Level,
    k_target: bool,
}

/// Per-datatype recursor scaffolding (pin `rec_info`).
struct RecInfo {
    motive: Local,
    minors: Vec<Local>,
    indices: Vec<Local>,
    major: Local,
}

impl<'a> Engine<'a> {
    fn new(env: &Environment, block: &'a InductiveBlock, budget: Budget) -> KResult<Engine<'a>> {
        let first = block.types.first().ok_or_else(|| {
            Stop::Reject(RejectClass::BlockMismatch, "empty inductive block".into())
        })?;
        let lparams = first.base.level_params.clone();
        let levels: Vec<Level> = lparams.iter().cloned().map(Level::param).collect();
        Ok(Engine {
            env: env.clone(),
            base_env: env.clone(),
            block,
            lparams,
            levels,
            nparams: first.num_params as usize,
            is_unsafe: first.is_unsafe,
            budget,
            used: Consumption::default(),
            locals: Vec::new(),
            fresh: 0,
            params: Vec::new(),
            nindices: Vec::new(),
            ind_consts: Vec::new(),
            result_level: Level::zero(),
            result_is_not_zero: false,
            elim_level: Level::zero(),
            k_target: false,
        })
    }

    fn remaining(&self) -> Budget {
        // `narrowed` rather than a fresh literal: the remaining allowance is
        // the SAME derivation with less of it left, and rebuilding a budget
        // beside the calibration is how a ceiling loses its provenance.
        self.budget.narrowed(
            self.budget.steps.saturating_sub(self.used.steps_used),
            self.budget.depth,
        )
    }

    fn charge(&mut self, c: Consumption) -> KResult<()> {
        self.used.steps_used = self.used.steps_used.saturating_add(c.steps_used);
        self.used.max_depth = self.used.max_depth.max(c.max_depth);
        if self.used.steps_used > self.budget.steps {
            return Err(Stop::Exhausted(ExhaustionReason::Steps));
        }
        Ok(())
    }

    /// Spawn a metered checker over the CURRENT scratch env with the full
    /// telescope adopted, run `f`, absorb consumption.
    fn with_tc<T>(&mut self, f: impl FnOnce(&mut TypeChecker<'_>) -> KResult<T>) -> KResult<T> {
        let remaining = self.remaining();
        let safety = if self.is_unsafe {
            fln_env::constants::DefinitionSafety::Unsafe
        } else {
            fln_env::constants::DefinitionSafety::Safe
        };
        let mut tc = TypeChecker::new_with_safety(&self.env, &self.lparams, remaining, safety);
        for local in &self.locals {
            tc.adopt_local(local.id.clone(), local.type_.clone());
        }
        let result = f(&mut tc);
        let consumption = tc.consumption();
        drop(tc);
        self.charge(consumption)?;
        result
    }

    fn mk_local(&mut self, name: Name, type_: Expr, info: BinderInfo) -> Local {
        self.fresh += 1;
        let local = Local {
            id: FVarId(Name::num(Name::str(Name::anonymous(), "_adm"), self.fresh)),
            name,
            info,
            // Pin mk_local_decl (inductive.cpp:178): every telescope local's
            // type sheds its annotation gadgets — this is why generated
            // recursor binders read `Type w`, not `outParam (Type w)`.
            type_: consume_type_annotations(&type_),
        };
        self.locals.push(local.clone());
        local
    }

    /// `mk_local_decl_for`: a local from the head binder of a Π.
    fn mk_local_for(&mut self, pi: &Expr) -> KResult<Local> {
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            binder_info,
            ..
        } = pi.node()
        else {
            return reject(RejectClass::BlockMismatch, "expected a Π type");
        };
        Ok(self.mk_local(binder_name.clone(), binder_type.clone(), *binder_info))
    }

    /// Instantiate a Π body with a local's fvar.
    fn open_pi(&mut self, pi: &Expr, local: &Local) -> KResult<Expr> {
        let ExprNode::ForallE { body, .. } = pi.node() else {
            return reject(RejectClass::BlockMismatch, "expected a Π type");
        };
        let body = body.clone();
        let fvar = local.fvar();
        self.with_tc(|tc| tc.instantiate(&body, 0, &fvar, 0))
    }

    // ---- KR-600..602: the types ------------------------------------------------------

    fn check_inductive_types(&mut self) -> KResult<()> {
        let types = self.block.types.to_vec();
        let mut first = true;
        for ind in &types {
            let name = &ind.base.name;
            // KR-600: freshness of the type name and its recursor name; the
            // decoded row's block facts must be self-consistent.
            if self.env.contains(name) {
                return reject(
                    RejectClass::AlreadyDeclared,
                    format!("`{}` is already declared", name.to_display_string()),
                );
            }
            if self.env.contains(&mk_rec_name(name)) {
                return reject(
                    RejectClass::AlreadyDeclared,
                    format!(
                        "recursor name `{}` is already declared",
                        mk_rec_name(name).to_display_string()
                    ),
                );
            }
            if ind.base.level_params != self.lparams {
                return reject(
                    RejectClass::BlockMismatch,
                    "block members must share level parameters",
                );
            }
            if ind.num_params as usize != self.nparams {
                return reject(
                    RejectClass::BlockMismatch,
                    "block members must share the parameter count",
                );
            }
            if ind.is_unsafe != self.is_unsafe {
                return reject(
                    RejectClass::BlockMismatch,
                    "block members must share the safety flag",
                );
            }
            let type_ = ind.base.type_.clone();
            if type_.has_fvar() || type_.has_expr_mvar() || type_.loose_bvar_range() > 0 {
                return reject(
                    RejectClass::MVarInKernel,
                    "inductive type must be closed (no mvars/fvars)",
                );
            }
            // Well-typedness of the type itself.
            self.with_tc(|tc| tc.infer(&type_, 0))?;

            // Telescope walk: shared params (KR-601), per-type indices.
            let mut indices = 0usize;
            let mut t = self.with_tc(|tc| tc.whnf_public(&type_, 0))?;
            let mut i = 0usize;
            while let ExprNode::ForallE { binder_type, .. } = t.node() {
                let binder_type = binder_type.clone();
                if i < self.nparams {
                    if first {
                        let param = self.mk_local_for(&t)?;
                        t = self.open_pi(&t, &param)?;
                        self.params.push(param);
                    } else {
                        let expected = self.params[i].type_.clone();
                        let matches =
                            self.with_tc(|tc| tc.def_eq_public(&binder_type, &expected, 0))?;
                        if !matches {
                            return reject(
                                RejectClass::BlockMismatch,
                                "parameters of all inductive datatypes must match",
                            );
                        }
                        let param = self.params[i].clone();
                        t = self.open_pi(&t, &param)?;
                    }
                } else {
                    let index = self.mk_local_for(&t)?;
                    t = self.open_pi(&t, &index)?;
                    indices += 1;
                }
                i += 1;
                t = self.with_tc(|tc| tc.whnf_public(&t, 0))?;
            }
            if i < self.nparams {
                return reject(
                    RejectClass::BlockMismatch,
                    "number of parameters mismatch in inductive datatype declaration",
                );
            }
            // KR-602: the residual must be a sort; one universe per block.
            let ExprNode::Sort { level } = t.node() else {
                return reject(
                    RejectClass::SortExpected,
                    "inductive type must end in a sort",
                );
            };
            if first {
                self.result_level = level.clone();
                self.result_is_not_zero = level.is_not_zero();
            } else if !level.is_equiv(&self.result_level) {
                return reject(
                    RejectClass::BlockMismatch,
                    "mutually inductive types must live in the same universe",
                );
            }
            // Decoded-row cross-check: num_indices.
            if ind.num_indices as usize != indices {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "`{}`: decoded num_indices={} but the type has {}",
                        name.to_display_string(),
                        ind.num_indices,
                        indices
                    ),
                );
            }
            self.nindices.push(indices);
            self.ind_consts
                .push(Expr::const_(name.clone(), self.levels.clone()));
            first = false;
        }
        Ok(())
    }

    // ---- KR-607: flags -----------------------------------------------------------------

    fn block_names(&self) -> Vec<Name> {
        self.block
            .types
            .iter()
            .map(|t| t.base.name.clone())
            .collect()
    }

    fn mentions_block(&self, e: &Expr) -> bool {
        let names = self.block_names();
        fn walk(e: &Expr, names: &[Name]) -> bool {
            match e.node() {
                ExprNode::Const { name, .. } => names.contains(name),
                ExprNode::App { f, a } => walk(f, names) || walk(a, names),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => walk(binder_type, names) || walk(body, names),
                ExprNode::LetE {
                    type_, value, body, ..
                } => walk(type_, names) || walk(value, names) || walk(body, names),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => walk(expr, names),
                _ => false,
            }
        }
        walk(e, &names)
    }

    /// KR-607: recursive iff some constructor field domain mentions the block.
    fn compute_is_rec(&mut self) -> KResult<bool> {
        for ctor in &self.block.ctors {
            let mut t = ctor.base.type_.clone();
            while let ExprNode::ForallE {
                binder_type, body, ..
            } = t.node()
            {
                if self.mentions_block(binder_type) {
                    return Ok(true);
                }
                let next = body.clone();
                t = next;
            }
        }
        Ok(false)
    }

    /// KR-607: reflexive iff some field is a function type whose body mentions
    /// a block member. (Pin walks with locals; occurrence checking is
    /// substitution-invariant, so the raw bvar walk is equivalent.)
    fn compute_is_reflexive(&mut self) -> KResult<bool> {
        for ctor in &self.block.ctors {
            let mut t = ctor.base.type_.clone();
            while let ExprNode::ForallE {
                binder_type, body, ..
            } = t.node()
            {
                if matches!(binder_type.node(), ExprNode::ForallE { .. })
                    && self.mentions_block(binder_type)
                {
                    return Ok(true);
                }
                let next = body.clone();
                t = next;
            }
        }
        Ok(false)
    }

    // ---- KR-603..606: constructors ----------------------------------------------------

    /// KR-605 (`is_valid_ind_app`): `I_i params indices`, param positions
    /// syntactically the declared params, and no index argument mentions the
    /// block.
    fn is_valid_ind_app_at(&self, t: &Expr, i: usize) -> bool {
        let mut args: Vec<&Expr> = Vec::new();
        let mut head = t;
        while let ExprNode::App { f, a } = head.node() {
            args.push(a);
            head = f;
        }
        args.reverse();
        if *head != self.ind_consts[i] || args.len() != self.nparams + self.nindices[i] {
            return false;
        }
        for (j, param) in self.params.iter().enumerate() {
            if *args[j] != param.fvar() {
                return false;
            }
        }
        for arg in &args[self.nparams..] {
            if self.mentions_block(arg) {
                return false;
            }
        }
        true
    }

    fn valid_ind_app_index(&self, t: &Expr) -> Option<usize> {
        (0..self.block.types.len()).find(|&i| self.is_valid_ind_app_at(t, i))
    }

    /// Is `t` (a field type) a recursive argument: `Π xs, I_i params indices`?
    fn is_rec_argument(&mut self, t: &Expr) -> KResult<Option<usize>> {
        let mut t = self.with_tc(|tc| tc.whnf_public(t, 0))?;
        while matches!(t.node(), ExprNode::ForallE { .. }) {
            let local = self.mk_local_for(&t)?;
            let body = self.open_pi(&t, &local)?;
            t = self.with_tc(|tc| tc.whnf_public(&body, 0))?;
        }
        Ok(self.valid_ind_app_index(&t))
    }

    /// KR-606 strict positivity.
    fn check_positivity(
        &mut self,
        t: &Expr,
        ctor: &Name,
        arg_idx: usize,
        depth: u32,
    ) -> KResult<()> {
        depth_guard(depth)?;
        let t = self.with_tc(|tc| tc.whnf_public(t, 0))?;
        if !self.mentions_block(&t) {
            return Ok(()); // non-recursive argument
        }
        if matches!(t.node(), ExprNode::ForallE { .. }) {
            let ExprNode::ForallE { binder_type, .. } = t.node() else {
                unreachable!("matched above");
            };
            if self.mentions_block(binder_type) {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "arg #{} of `{}` has a non positive occurrence of the datatypes being declared",
                        arg_idx + 1,
                        ctor.to_display_string()
                    ),
                );
            }
            let local = self.mk_local_for(&t)?;
            let body = self.open_pi(&t, &local)?;
            return self.check_positivity(&body, ctor, arg_idx, depth + 1);
        }
        if self.valid_ind_app_index(&t).is_some() {
            return Ok(()); // recursive argument
        }
        reject(
            RejectClass::BlockMismatch,
            format!(
                "arg #{} of `{}` contains a non valid occurrence of the datatypes being declared",
                arg_idx + 1,
                ctor.to_display_string()
            ),
        )
    }

    /// KR-603/604/605/606 + decoded-row cross-checks, for every constructor.
    /// `check_valid_app`/`check_positive` are switched off on the nested
    /// partial path.
    fn check_constructors(&mut self, full: bool) -> KResult<()> {
        for (idx, ind) in self.block.types.iter().enumerate() {
            let declared: Vec<&ConstructorVal> = self
                .block
                .ctors
                .iter()
                .filter(|c| c.induct == ind.base.name)
                .collect();
            // The decoded parent lists ctors in cidx order; verify the match.
            if ind.ctors.len() != declared.len() {
                return reject(
                    RejectClass::BlockMismatch,
                    "decoded ctor list does not match the block's constructors",
                );
            }
            for (cidx, ctor) in declared.iter().enumerate() {
                let name = &ctor.base.name;
                if ind.ctors.get(cidx) != Some(name) {
                    return reject(
                        RejectClass::BlockMismatch,
                        format!(
                            "decoded ctor order mismatch at `{}`",
                            name.to_display_string()
                        ),
                    );
                }
                if self.env.contains(name) {
                    return reject(
                        RejectClass::AlreadyDeclared,
                        format!("`{}` is already declared", name.to_display_string()),
                    );
                }
                if ctor.base.level_params != self.lparams
                    || ctor.cidx as usize != cidx
                    || ctor.num_params as usize != self.nparams
                    || ctor.is_unsafe != self.is_unsafe
                {
                    return reject(
                        RejectClass::BlockMismatch,
                        format!(
                            "decoded constructor observables mismatch at `{}`",
                            name.to_display_string()
                        ),
                    );
                }
                let t0 = ctor.base.type_.clone();
                if t0.has_fvar() || t0.has_expr_mvar() || t0.loose_bvar_range() > 0 {
                    return reject(
                        RejectClass::MVarInKernel,
                        "constructor type must be closed (no mvars/fvars)",
                    );
                }
                self.with_tc(|tc| tc.infer(&t0, 0))?;
                let mut t = t0;
                let mut i = 0usize;
                let mut fields = 0usize;
                while matches!(t.node(), ExprNode::ForallE { .. }) {
                    let ExprNode::ForallE { binder_type, .. } = t.node() else {
                        unreachable!("matched above");
                    };
                    let binder_type = binder_type.clone();
                    if i < self.nparams {
                        let expected = self.params[i].type_.clone();
                        let matches =
                            self.with_tc(|tc| tc.def_eq_public(&binder_type, &expected, 0))?;
                        if !matches {
                            return reject(
                                RejectClass::BlockMismatch,
                                format!(
                                    "arg #{} of `{}` does not match inductive datatypes parameters",
                                    i + 1,
                                    name.to_display_string()
                                ),
                            );
                        }
                        let param = self.params[i].clone();
                        t = self.open_pi(&t, &param)?;
                    } else {
                        // KR-604: the field's universe fits the datatype (or Prop).
                        let field_sort = self.with_tc(|tc| {
                            let s = tc.infer(&binder_type, 0)?;
                            tc.whnf_public(&s, 0)
                        })?;
                        let ExprNode::Sort { level } = field_sort.node() else {
                            return reject(
                                RejectClass::SortExpected,
                                format!(
                                    "arg #{} of `{}` is not a type",
                                    i + 1,
                                    name.to_display_string()
                                ),
                            );
                        };
                        if !(self.result_level.is_geq(level) || self.result_level.is_zero()) {
                            return reject(
                                RejectClass::BlockMismatch,
                                format!(
                                    "universe level of type_of(arg #{}) of `{}` is too big for the corresponding inductive datatype",
                                    i + 1,
                                    name.to_display_string()
                                ),
                            );
                        }
                        if full && !self.is_unsafe {
                            self.check_positivity(&binder_type, name, i, 0)?;
                        }
                        let local = self.mk_local_for(&t)?;
                        t = self.open_pi(&t, &local)?;
                        fields += 1;
                    }
                    i += 1;
                }
                if full && self.valid_ind_app_index(&t) != Some(idx) {
                    return reject(
                        RejectClass::BlockMismatch,
                        format!("invalid return type for `{}`", name.to_display_string()),
                    );
                }
                if ctor.num_fields as usize != fields {
                    return reject(
                        RejectClass::BlockMismatch,
                        format!(
                            "decoded num_fields mismatch at `{}`",
                            name.to_display_string()
                        ),
                    );
                }
            }
        }
        Ok(())
    }

    // ---- KR-700..702: elimination universe --------------------------------------------

    /// KR-700/701 (`elim_only_at_universe_zero`).
    fn elim_only_at_universe_zero(&mut self) -> KResult<bool> {
        if self.result_is_not_zero {
            return Ok(false);
        }
        if self.block.types.len() > 1 {
            return Ok(true);
        }
        let ctors: Vec<ConstructorVal> = self
            .block
            .ctors
            .iter()
            .filter(|c| c.induct == self.block.types[0].base.name)
            .cloned()
            .collect();
        if ctors.len() > 1 {
            return Ok(true);
        }
        let Some(ctor) = ctors.first() else {
            return Ok(false); // empty inductive predicate eliminates large
        };
        // KR-701: single constructor — every non-param field is a Prop or
        // occurs among the result's arguments.
        let mut t = ctor.base.type_.clone();
        let mut i = 0usize;
        let mut to_check: Vec<Local> = Vec::new();
        while matches!(t.node(), ExprNode::ForallE { .. }) {
            let local = if i < self.nparams {
                self.params[i].clone()
            } else {
                let l = self.mk_local_for(&t)?;
                let field_sort = self.with_tc(|tc| {
                    let s = tc.infer(&l.type_.clone(), 0)?;
                    tc.whnf_public(&s, 0)
                })?;
                // NORMALISE THE LEVEL BEFORE ASKING WHETHER IT IS ZERO.
                // `Level::is_zero` is purely structural, and `whnf` reduces the
                // EXPRESSION without normalising the level inside a `Sort`. A
                // field of sort `Sort (imax u 0)` is semantically a Prop but is
                // not `Node::Zero`, so it was treated as data, pushed to
                // `to_check`, found absent from the result's arguments, and the
                // whole inductive was restricted to Prop-only elimination.
                //
                // That cost 228 corpus rows across 76 subsingleton types (bead
                // `franken_lean-d17i`): the regenerated recursor carried no
                // motive universe and its level-parameter list came out one
                // shorter than the pin's, rejecting every declaration in the
                // block. Restrictive, so never unsound — but wrong.
                let is_prop = matches!(
                    field_sort.node(),
                    ExprNode::Sort { level } if level.normalize_fixpoint().is_zero()
                );
                if !is_prop {
                    to_check.push(l.clone());
                }
                l
            };
            t = self.open_pi(&t, &local)?;
            i += 1;
        }
        let mut result_args: Vec<Expr> = Vec::new();
        let mut head = t.clone();
        while let ExprNode::App { f, a } = head.node() {
            result_args.push(a.clone());
            let next = f.clone();
            head = next;
        }
        for local in &to_check {
            if !result_args.iter().any(|arg| *arg == local.fvar()) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// KR-702: the elimination level — `0`, or a fresh `u`-family parameter.
    fn init_elim_level(&mut self) -> KResult<()> {
        if self.elim_only_at_universe_zero()? {
            self.elim_level = Level::zero();
        } else {
            let mut u = Name::str(Name::anonymous(), "u");
            let mut i = 1u64;
            while self.lparams.contains(&u) {
                u = append_after(&Name::str(Name::anonymous(), "u"), &format!("_{i}"));
                i += 1;
            }
            self.elim_level = Level::param(u);
        }
        Ok(())
    }

    /// K-target (pin `init_K_target`): single type, Prop, one ctor, no fields.
    fn init_k_target(&mut self) {
        self.k_target = self.block.types.len() == 1
            && self.result_level.is_zero()
            && self.block.types[0].ctors.len() == 1
            && self
                .block
                .ctors
                .iter()
                .filter(|c| c.induct == self.block.types[0].base.name)
                .all(|c| c.num_fields == 0);
    }

    // ---- KR-800..803: recursor generation ---------------------------------------------

    fn rec_levels(&self) -> Vec<Level> {
        if matches!(self.elim_level.view(), fln_core::level::LevelView::Param(_)) {
            let mut out = vec![self.elim_level.clone()];
            out.extend(self.levels.iter().cloned());
            out
        } else {
            self.levels.clone()
        }
    }

    fn rec_lparams(&self) -> Vec<Name> {
        if let fln_core::level::LevelView::Param(u) = self.elim_level.view() {
            let mut out = vec![u.clone()];
            out.extend(self.lparams.iter().cloned());
            out
        } else {
            self.lparams.clone()
        }
    }

    /// Split a ctor type telescope into (field locals, rec-arg locals, result).
    fn open_ctor_fields(
        &mut self,
        ctor: &ConstructorVal,
    ) -> KResult<(Vec<Local>, Vec<Local>, Expr)> {
        let mut b_u = Vec::new();
        let mut u = Vec::new();
        let mut t = ctor.base.type_.clone();
        let mut i = 0usize;
        while matches!(t.node(), ExprNode::ForallE { .. }) {
            if i < self.nparams {
                let param = self.params[i].clone();
                t = self.open_pi(&t, &param)?;
            } else {
                let ExprNode::ForallE { binder_type, .. } = t.node() else {
                    unreachable!("matched above");
                };
                let binder_type = binder_type.clone();
                let local = self.mk_local_for(&t)?;
                b_u.push(local.clone());
                if self.is_rec_argument(&binder_type)?.is_some() {
                    u.push(local.clone());
                }
                t = self.open_pi(&t, &local)?;
            }
            i += 1;
        }
        Ok((b_u, u, t))
    }

    /// `I As is` → (datatype index, indices).
    fn get_ind_indices(&self, t: &Expr) -> KResult<(usize, Vec<Expr>)> {
        let Some(idx) = self.valid_ind_app_index(t) else {
            return reject(
                RejectClass::BlockMismatch,
                "constructor result is not a valid inductive application",
            );
        };
        let mut args: Vec<Expr> = Vec::new();
        let mut head = t.clone();
        while let ExprNode::App { f, a } = head.node() {
            args.push(a.clone());
            let next = f.clone();
            head = next;
        }
        args.reverse();
        Ok((idx, args[self.nparams..].to_vec()))
    }

    /// KR-800/801: motives, indices, majors, and minor premises.
    fn mk_rec_infos(&mut self) -> KResult<Vec<RecInfo>> {
        let mut infos: Vec<RecInfo> = Vec::new();
        // Motives, indices, majors.
        for (d_idx, ind) in self.block.types.iter().enumerate() {
            let mut t = self.with_tc(|tc| tc.whnf_public(&ind.base.type_.clone(), 0))?;
            let mut i = 0usize;
            let mut indices: Vec<Local> = Vec::new();
            while matches!(t.node(), ExprNode::ForallE { .. }) {
                if i < self.nparams {
                    let param = self.params[i].clone();
                    t = self.open_pi(&t, &param)?;
                } else {
                    let index = self.mk_local_for(&t)?;
                    t = self.open_pi(&t, &index)?;
                    indices.push(index);
                }
                i += 1;
                t = self.with_tc(|tc| tc.whnf_public(&t, 0))?;
            }
            let mut major_type = self.ind_consts[d_idx].clone();
            for param in &self.params {
                major_type = Expr::app(major_type, param.fvar());
            }
            for index in &indices {
                major_type = Expr::app(major_type, index.fvar());
            }
            let major = self.mk_local(
                Name::str(Name::anonymous(), "t"),
                major_type,
                BinderInfo::Default,
            );
            let mut motive_ty = Expr::sort(self.elim_level.clone());
            motive_ty = mk_pi_locals(std::slice::from_ref(&major), motive_ty)?;
            motive_ty = mk_pi_locals(&indices, motive_ty)?;
            let motive_name = if self.block.types.len() > 1 {
                append_after(
                    &Name::str(Name::anonymous(), "motive"),
                    &format!("_{}", d_idx + 1),
                )
            } else {
                Name::str(Name::anonymous(), "motive")
            };
            let motive = self.mk_local(motive_name, motive_ty, BinderInfo::Default);
            infos.push(RecInfo {
                motive,
                minors: Vec::new(),
                indices,
                major,
            });
        }
        // Minor premises (KR-801).
        for (d_idx, ind) in self.block.types.iter().enumerate() {
            let declared: Vec<ConstructorVal> = self
                .block
                .ctors
                .iter()
                .filter(|c| c.induct == ind.base.name)
                .cloned()
                .collect();
            for ctor in &declared {
                let (b_u, u, result) = self.open_ctor_fields(ctor)?;
                let (it_idx, it_indices) = self.get_ind_indices(&result)?;
                let mut c_app = infos[it_idx].motive.fvar();
                for index in &it_indices {
                    c_app = Expr::app(c_app, index.clone());
                }
                let mut intro_app = Expr::const_(ctor.base.name.clone(), self.levels.clone());
                for param in &self.params {
                    intro_app = Expr::app(intro_app, param.fvar());
                }
                for field in &b_u {
                    intro_app = Expr::app(intro_app, field.fvar());
                }
                c_app = Expr::app(c_app, intro_app);
                // Induction hypotheses.
                let mut v: Vec<Local> = Vec::new();
                for u_i in &u {
                    let mut u_i_ty = self.with_tc(|tc| tc.whnf_public(&u_i.type_.clone(), 0))?;
                    let mut xs: Vec<Local> = Vec::new();
                    while matches!(u_i_ty.node(), ExprNode::ForallE { .. }) {
                        let x = self.mk_local_for(&u_i_ty)?;
                        let body = self.open_pi(&u_i_ty, &x)?;
                        xs.push(x);
                        u_i_ty = self.with_tc(|tc| tc.whnf_public(&body, 0))?;
                    }
                    let (rec_idx, rec_indices) = self.get_ind_indices(&u_i_ty)?;
                    let mut ih_c = infos[rec_idx].motive.fvar();
                    for index in &rec_indices {
                        ih_c = Expr::app(ih_c, index.clone());
                    }
                    let mut u_app = u_i.fvar();
                    for x in &xs {
                        u_app = Expr::app(u_app, x.fvar());
                    }
                    ih_c = Expr::app(ih_c, u_app);
                    let ih_ty = mk_pi_locals(&xs, ih_c)?;
                    let ih =
                        self.mk_local(append_after(&u_i.name, "_ih"), ih_ty, BinderInfo::Default);
                    v.push(ih);
                }
                let minor_ty = mk_pi_locals(&b_u, mk_pi_locals(&v, c_app)?)?;
                let minor_name = strip_prefix(&ctor.base.name, &ind.base.name);
                let minor = self.mk_local(minor_name, minor_ty, BinderInfo::Default);
                infos[d_idx].minors.push(minor);
            }
        }
        Ok(infos)
    }

    /// KR-803: the iota right-hand sides for datatype `d_idx`.
    fn mk_rec_rules(
        &mut self,
        infos: &[RecInfo],
        cs: &[Local],
        minors: &[Local],
        d_idx: usize,
        minor_idx: &mut usize,
    ) -> KResult<Vec<RecursorRule>> {
        let ind = &self.block.types[d_idx].clone();
        let rec_levels = self.rec_levels();
        let declared: Vec<ConstructorVal> = self
            .block
            .ctors
            .iter()
            .filter(|c| c.induct == ind.base.name)
            .cloned()
            .collect();
        let mut rules = Vec::new();
        for ctor in &declared {
            let (b_u, u, _result) = self.open_ctor_fields(ctor)?;
            let mut v: Vec<Expr> = Vec::new();
            for u_i in &u {
                let mut u_i_ty = self.with_tc(|tc| tc.whnf_public(&u_i.type_.clone(), 0))?;
                let mut xs: Vec<Local> = Vec::new();
                while matches!(u_i_ty.node(), ExprNode::ForallE { .. }) {
                    let x = self.mk_local_for(&u_i_ty)?;
                    let body = self.open_pi(&u_i_ty, &x)?;
                    xs.push(x);
                    u_i_ty = self.with_tc(|tc| tc.whnf_public(&body, 0))?;
                }
                let (rec_idx, rec_indices) = self.get_ind_indices(&u_i_ty)?;
                let rec_name = mk_rec_name(&self.block.types[rec_idx].base.name);
                let mut rec_app = Expr::const_(rec_name, rec_levels.clone());
                for param in &self.params {
                    rec_app = Expr::app(rec_app, param.fvar());
                }
                for c in cs {
                    rec_app = Expr::app(rec_app, c.fvar());
                }
                for minor in minors {
                    rec_app = Expr::app(rec_app, minor.fvar());
                }
                for index in &rec_indices {
                    rec_app = Expr::app(rec_app, index.clone());
                }
                let mut u_app = u_i.fvar();
                for x in &xs {
                    u_app = Expr::app(u_app, x.fvar());
                }
                rec_app = Expr::app(rec_app, u_app);
                v.push(mk_lam_locals(&xs, rec_app)?);
            }
            let mut e_app = minors[*minor_idx].fvar();
            for field in &b_u {
                e_app = Expr::app(e_app, field.fvar());
            }
            for ih in &v {
                e_app = Expr::app(e_app, ih.clone());
            }
            let comp_rhs = mk_lam_locals(
                &self.params.clone(),
                mk_lam_locals(cs, mk_lam_locals(minors, mk_lam_locals(&b_u, e_app)?)?)?,
            )?;
            rules.push(RecursorRule {
                ctor: ctor.base.name.clone(),
                nfields: b_u.len() as u32,
                rhs: comp_rhs,
            });
            *minor_idx += 1;
        }
        let _ = infos;
        Ok(rules)
    }

    /// KR-802: regenerate every recursor of the block from its declaration
    /// alone — the block's decoded recursor rows are never consulted. One
    /// `RecursorVal` per datatype, in block order.
    fn generate_recursors(&mut self) -> KResult<Vec<RecursorVal>> {
        let infos = self.mk_rec_infos()?;
        let cs: Vec<Local> = infos.iter().map(|i| i.motive.clone()).collect();
        let minors: Vec<Local> = infos.iter().flat_map(|i| i.minors.clone()).collect();
        let nminors = minors.len() as u32;
        let nmotives = cs.len() as u32;
        let all = self.block_names();
        let mut minor_idx = 0usize;
        let mut generated = Vec::with_capacity(infos.len());
        for (d_idx, info) in infos.iter().enumerate() {
            let mut c_app = info.motive.fvar();
            for index in &info.indices {
                c_app = Expr::app(c_app, index.fvar());
            }
            c_app = Expr::app(c_app, info.major.fvar());
            let mut rec_ty = mk_pi_locals(std::slice::from_ref(&info.major), c_app)?;
            rec_ty = mk_pi_locals(&info.indices, rec_ty)?;
            rec_ty = mk_pi_locals(&minors, rec_ty)?;
            rec_ty = mk_pi_locals(&cs, rec_ty)?;
            rec_ty = mk_pi_locals(&self.params.clone(), rec_ty)?;
            rec_ty = infer_implicit_strict(&rec_ty, 0)?;
            let rules = self.mk_rec_rules(&infos, &cs, &minors, d_idx, &mut minor_idx)?;
            let rec_name = mk_rec_name(&self.block.types[d_idx].base.name);
            generated.push(RecursorVal {
                base: fln_env::constants::ConstantVal {
                    name: rec_name.clone(),
                    level_params: self.rec_lparams(),
                    type_: rec_ty,
                },
                all: all.clone(),
                num_params: self.nparams as u32,
                num_indices: self.nindices[d_idx] as u32,
                num_motives: nmotives,
                num_minors: nminors,
                rules,
                k: self.k_target,
                is_unsafe: self.is_unsafe,
            });
        }
        Ok(generated)
    }

    /// KR-802 + the ap6 cross-check: regenerate every recursor and compare it
    /// field-by-field against the DECODED rows.
    fn check_recursors(&mut self) -> KResult<()> {
        if self.block.recursors.len() != self.block.types.len() {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "block declares {} recursors, expected {}",
                    self.block.recursors.len(),
                    self.block.types.len()
                ),
            );
        }
        let generated = self.generate_recursors()?;
        compare_recursor_sets(&generated, &self.block.recursors)
    }

    // ---- driver ------------------------------------------------------------------------

    fn run(&mut self) -> KResult<()> {
        // KR-971 on the block's level parameters.
        for (i, p) in self.lparams.iter().enumerate() {
            if self.lparams[..i].contains(p) {
                return reject(
                    RejectClass::DuplicateLevelParams,
                    format!(
                        "duplicate universe level parameter `{}`",
                        p.to_display_string()
                    ),
                );
            }
        }
        let nested = self.block.types.iter().any(|t| t.num_nested > 0);
        self.check_inductive_types()?;
        // KR-607 flags + block observables, cross-checked against every row.
        let is_rec = self.compute_is_rec()?;
        let is_reflexive = self.compute_is_reflexive()?;
        let all = self.block_names();
        for ind in &self.block.types {
            if ind.all != all {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "decoded `all` list mismatch at `{}`",
                        ind.base.name.to_display_string()
                    ),
                );
            }
            if !nested && (ind.is_rec != is_rec || ind.is_reflexive != is_reflexive) {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "decoded recursivity flags mismatch at `{}` (is_rec {} vs {}, is_reflexive {} vs {})",
                        ind.base.name.to_display_string(),
                        ind.is_rec,
                        is_rec,
                        ind.is_reflexive,
                        is_reflexive
                    ),
                );
            }
        }
        // Declare the types (pin declare_inductive_types), then check ctors
        // against the extended scratch env.
        for ind in &self.block.types {
            self.env = scratch_admit(&self.env, ConstantInfo::Induct(ind.clone()), &ind.base.name)?;
        }
        self.check_constructors(!nested)?;
        for ctor in &self.block.ctors {
            self.env = scratch_admit(&self.env, ConstantInfo::Ctor(ctor.clone()), &ctor.base.name)?;
        }
        if nested {
            return self.check_nested_full();
        }
        self.init_elim_level()?;
        self.init_k_target();
        self.check_recursors()
    }

    /// The synthesized-block driver: identical to [`Engine::run`] except that
    /// the decoded-row cross-checks (`all` lists, recursivity flags, recursor
    /// comparison) are meaningless — every row was minted by the translation
    /// itself — so the run returns the regenerated recursors and the computed
    /// flags for the CALLER to compare against the decoded originals.
    fn run_synthesized(&mut self) -> KResult<(Vec<RecursorVal>, bool, bool)> {
        self.check_inductive_types()?;
        let is_rec = self.compute_is_rec()?;
        let is_reflexive = self.compute_is_reflexive()?;
        for ind in &self.block.types {
            self.env = scratch_admit(&self.env, ConstantInfo::Induct(ind.clone()), &ind.base.name)?;
        }
        self.check_constructors(true)?;
        for ctor in &self.block.ctors {
            self.env = scratch_admit(&self.env, ConstantInfo::Ctor(ctor.clone()), &ctor.base.name)?;
        }
        self.init_elim_level()?;
        self.init_k_target();
        let recursors = self.generate_recursors()?;
        Ok((recursors, is_rec, is_reflexive))
    }

    // ---- the nested-inductive auxiliary translation (KR-608) ---------------------------
    //
    // Pin `elim_nested_inductive_fn` (inductive.cpp:882-1077), `restore`
    // (795-873), `mk_aux_rec_name_map` (1088-1114), and the `add_inductive`
    // driver (1116-1182), reconstructed over the DECODED (post-restore) rows:
    // nested occurrences in constructor fields are replaced by auxiliary
    // types copied whole-block from the environment with their parameters
    // instantiated at the occurrence; the synthesized mutual block passes the
    // FULL ordinary ruleset — strict positivity included — against the
    // pre-block environment; its regenerated recursors are renamed
    // (`main.rec`, `main.rec_1`, …) and translated back; and the result must
    // match the decoded rows byte-exactly. Auxiliary names never survive the
    // restore, so their exact spelling is kernel-internal (the pin's
    // `_nested.*` uniquifier collides against ITS environment, which the
    // artifact does not carry).

    /// The full nested ruleset: translate, check the auxiliary block under
    /// every ordinary rule, regenerate, restore, and compare.
    fn check_nested_full(&mut self) -> KResult<()> {
        // 1. Forward translation (pin worklist order: main constructors
        //    first, then each minted auxiliary's constructors in creation
        //    order — recursor numbering depends on it).
        let mut st = NestedState::default();
        let mut main_types = self.block.types.to_vec();
        let mut main_ctors = self.block.ctors.to_vec();
        for ctor in &mut main_ctors {
            let translated = self.nested_replace_ctor(&ctor.base.type_.clone(), &mut st)?;
            ctor.base.type_ = translated;
        }
        let mut next = 0usize;
        while next < st.aux_ctors.len() {
            let untranslated = st.aux_ctors[next].base.type_.clone();
            let translated = self.nested_replace_ctor(&untranslated, &mut st)?;
            st.aux_ctors[next].base.type_ = translated;
            next += 1;
        }
        if st.auxes.is_empty() {
            return reject(
                RejectClass::BlockMismatch,
                "decoded num_nested is nonzero but no nested occurrence exists",
            );
        }
        // The translated `all` list: main types then auxiliaries.
        let all: Vec<Name> = main_types
            .iter()
            .map(|t| t.base.name.clone())
            .chain(st.aux_types.iter().map(|t| t.base.name.clone()))
            .collect();
        for t in main_types.iter_mut().chain(st.aux_types.iter_mut()) {
            t.all = all.clone();
            t.num_nested = 0;
        }
        let aux_count = st.auxes.len() as u32;
        let main_count = main_types.len();
        let mut types = main_types;
        types.append(&mut st.aux_types);
        let mut ctors = main_ctors;
        ctors.append(&mut st.aux_ctors);
        let translated_block = InductiveBlock {
            types,
            ctors,
            recursors: Vec::new(),
        };

        // 2. The FULL ordinary ruleset over the synthesized block, against
        //    the pre-block environment (pin add_inductive → add_inductive_fn).
        let mut aux_engine = Engine::new(&self.base_env, &translated_block, self.remaining())?;
        let outcome = aux_engine.run_synthesized();
        let spent = aux_engine.used;
        drop(aux_engine);
        self.charge(spent)?;
        let (generated, comp_is_rec, comp_is_reflexive) = outcome?;

        // 3. Decoded observables against the translation (pin restore keeps
        //    the CHECKER-computed flags, so the decoded rows must carry them;
        //    the decoded num_nested counts the minted auxiliaries).
        for ind in &self.block.types {
            if ind.num_nested != aux_count {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "decoded num_nested {} at `{}` vs {} translated auxiliaries",
                        ind.num_nested,
                        ind.base.name.to_display_string(),
                        aux_count
                    ),
                );
            }
            if ind.is_rec != comp_is_rec || ind.is_reflexive != comp_is_reflexive {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "decoded recursivity flags mismatch at `{}` (is_rec {} vs {}, is_reflexive {} vs {})",
                        ind.base.name.to_display_string(),
                        ind.is_rec,
                        comp_is_rec,
                        ind.is_reflexive,
                        comp_is_reflexive
                    ),
                );
            }
        }

        // 4. Restore: rename the auxiliary recursors (`main.rec_i`), map the
        //    auxiliary constants back to their original instantiated forms,
        //    and compare byte-exactly against the decoded rows — matched BY
        //    NAME (the artifact's row order is module order, not block order).
        let mut rec_rename: Vec<(Name, Name)> = Vec::new();
        let base_rec = mk_rec_name(&self.block.types[0].base.name);
        for (i, g) in generated.iter().enumerate().skip(main_count) {
            rec_rename.push((
                g.base.name.clone(),
                append_after(&base_rec, &format!("_{}", i - main_count + 1)),
            ));
        }
        let main_names: Vec<Name> = self
            .block
            .types
            .iter()
            .map(|t| t.base.name.clone())
            .collect();
        if self.block.recursors.len() != generated.len() {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "block declares {} recursors, expected {} (main + auxiliary)",
                    self.block.recursors.len(),
                    generated.len()
                ),
            );
        }
        for (i, g) in generated.iter().enumerate() {
            let restored_name = if i < main_count {
                g.base.name.clone()
            } else {
                rec_rename[i - main_count].1.clone()
            };
            let restored_ty = self.restore_expr(&g.base.type_, &st, &rec_rename, 0)?;
            let mut restored_rules = Vec::with_capacity(g.rules.len());
            for rule in &g.rules {
                restored_rules.push(RecursorRule {
                    ctor: st.restore_ctor_name(&rule.ctor),
                    nfields: rule.nfields,
                    rhs: self.restore_expr(&rule.rhs, &st, &rec_rename, 0)?,
                });
            }
            let restored = RecursorVal {
                base: fln_env::constants::ConstantVal {
                    name: restored_name.clone(),
                    level_params: g.base.level_params.clone(),
                    type_: restored_ty,
                },
                all: main_names.clone(),
                num_params: g.num_params,
                num_indices: g.num_indices,
                num_motives: g.num_motives,
                num_minors: g.num_minors,
                rules: restored_rules,
                k: g.k,
                is_unsafe: g.is_unsafe,
            };
            let Some(decoded) = self
                .block
                .recursors
                .iter()
                .find(|r| r.base.name == restored_name)
            else {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "decoded block lacks recursor `{}`",
                        restored_name.to_display_string()
                    ),
                );
            };
            compare_recursors(&restored, decoded)?;
        }
        Ok(())
    }

    /// Translate one closed constructor type: the leading `nparams` binders
    /// (the block's parameters) are carried verbatim — the pin re-abstracts
    /// them and never translates inside them — and the field region is
    /// rewritten by [`Engine::nested_replace`].
    fn nested_replace_ctor(&mut self, closed: &Expr, st: &mut NestedState) -> KResult<Expr> {
        let mut binders: Vec<(Name, Expr, BinderInfo)> = Vec::new();
        let mut t = closed.clone();
        for _ in 0..self.nparams {
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = t.node()
            else {
                return reject(
                    RejectClass::BlockMismatch,
                    "constructor type is shorter than the block's parameter telescope",
                );
            };
            binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
            t = body.clone();
        }
        let mut rebuilt = self.nested_replace(&t, 0, 0, st)?;
        for (name, ty, info) in binders.into_iter().rev() {
            rebuilt = Expr::forall_e(name, ty, rebuilt, info);
        }
        Ok(rebuilt)
    }

    /// The pin's `replace_all_nested`/`replace_if_nested` over a closed field
    /// region: `inner` counts binders below the parameter telescope, so a
    /// parameter `j` reads `bvar (inner + nparams - 1 - j)`.
    fn nested_replace(
        &mut self,
        e: &Expr,
        inner: u32,
        depth: u32,
        st: &mut NestedState,
    ) -> KResult<Expr> {
        depth_guard(depth)?;
        // Decompose an application spine.
        let mut args: Vec<Expr> = Vec::new();
        let mut head = e.clone();
        while let ExprNode::App { f, a } = head.node() {
            args.push(a.clone());
            let next = f.clone();
            head = next;
        }
        args.reverse();
        if let ExprNode::Const { name, levels } = head.node()
            && !args.is_empty()
            && !st.is_aux_name(name)
            && !self.block.types.iter().any(|t| &t.base.name == name)
        {
            let head_row = self.base_env.find(name).cloned();
            if let Some(ConstantInfo::Induct(iv)) = head_row {
                let np = iv.num_params as usize;
                let mut mentions = false;
                for a in args.iter().take(np) {
                    if self.mentions_block_type(a, st)? {
                        mentions = true;
                        break;
                    }
                }
                if mentions {
                    if args.len() < np {
                        return reject(
                            RejectClass::BlockMismatch,
                            format!(
                                "nested occurrence of `{}` is under-applied",
                                name.to_display_string()
                            ),
                        );
                    }
                    // Canonicalize the parametric prefix (pin replace_params;
                    // loose non-parameter variables are the pin's hard error).
                    let mut canonical: Vec<Expr> = Vec::with_capacity(np);
                    for arg in args.iter().take(np) {
                        canonical.push(self.lower_to_param_canonical(arg, inner, 0)?);
                    }
                    let key = fold_app(
                        Expr::const_(name.clone(), levels.clone()),
                        canonical.iter().cloned(),
                    );
                    let aux_name = match st.lookup_aux(&key) {
                        Some(found) => found,
                        None => self.nested_mint(&iv, levels.clone(), &canonical, &key, st)?,
                    };
                    // `auxI params trailing…` at this site.
                    let mut replacement = Expr::const_(aux_name, self.levels.clone());
                    for j in 0..self.nparams {
                        replacement = Expr::app(
                            replacement,
                            Expr::bvar(inner + (self.nparams - 1 - j) as u32).map_err(|_| {
                                Stop::Reject(
                                    RejectClass::BlockMismatch,
                                    "nested translation parameter reference out of range".into(),
                                )
                            })?,
                        );
                    }
                    for trailing in &args[np..] {
                        replacement = Expr::app(
                            replacement,
                            self.nested_replace(trailing, inner, depth + 1, st)?,
                        );
                    }
                    return Ok(replacement);
                }
            }
        }
        // Not a nested application: rebuild structurally.
        if !args.is_empty() {
            let mut rebuilt = self.nested_replace(&head, inner, depth + 1, st)?;
            for a in &args {
                rebuilt = Expr::app(rebuilt, self.nested_replace(a, inner, depth + 1, st)?);
            }
            return Ok(rebuilt);
        }
        Ok(match e.node() {
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::lam(
                binder_name.clone(),
                self.nested_replace(binder_type, inner, depth + 1, st)?,
                self.nested_replace(body, inner + 1, depth + 1, st)?,
                *binder_info,
            ),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::forall_e(
                binder_name.clone(),
                self.nested_replace(binder_type, inner, depth + 1, st)?,
                self.nested_replace(body, inner + 1, depth + 1, st)?,
                *binder_info,
            ),
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => Expr::let_e(
                decl_name.clone(),
                self.nested_replace(type_, inner, depth + 1, st)?,
                self.nested_replace(value, inner, depth + 1, st)?,
                self.nested_replace(body, inner + 1, depth + 1, st)?,
                *non_dep,
            ),
            ExprNode::MData { data, expr } => Expr::mdata(
                data.clone(),
                self.nested_replace(expr, inner, depth + 1, st)?,
            ),
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => Expr::proj(
                struct_name.clone(),
                *idx,
                self.nested_replace(expr, inner, depth + 1, st)?,
            ),
            _ => e.clone(),
        })
    }

    /// Does the expression mention a type of the (translated) block?
    fn mentions_block_type(&mut self, e: &Expr, st: &NestedState) -> KResult<bool> {
        let mut stack = vec![e.clone()];
        let mut visited = 0u64;
        while let Some(x) = stack.pop() {
            visited += 1;
            if visited > 100_000 {
                return Err(Stop::Exhausted(ExhaustionReason::Steps));
            }
            match x.node() {
                ExprNode::Const { name, .. } => {
                    if st.is_aux_name(name) || self.block.types.iter().any(|t| &t.base.name == name)
                    {
                        return Ok(true);
                    }
                }
                ExprNode::App { f, a } => {
                    stack.push(f.clone());
                    stack.push(a.clone());
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    stack.push(binder_type.clone());
                    stack.push(body.clone());
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    stack.push(type_.clone());
                    stack.push(value.clone());
                    stack.push(body.clone());
                }
                ExprNode::MData { expr, .. } => stack.push(expr.clone()),
                ExprNode::Proj { expr, .. } => stack.push(expr.clone()),
                _ => {}
            }
        }
        Ok(false)
    }

    /// Shift a parametric argument into param-canonical space (parameters at
    /// `bvar (nparams-1-j)`): every loose bvar must reach INTO the parameter
    /// telescope — the pin rejects nested parameters that capture local
    /// variables (inductive.cpp:949).
    fn lower_to_param_canonical(&self, e: &Expr, inner: u32, depth: u32) -> KResult<Expr> {
        lower_param_expr(e, self.nparams, inner, 0, depth)
    }

    /// Mint auxiliaries for the WHOLE mutual block of a nested head (pin
    /// 993-1027): every type `J` in `head.all` is copied with its own
    /// parameters instantiated at the occurrence and re-abstracted over this
    /// block's parameters. Returns the auxiliary standing for `head` itself.
    fn nested_mint(
        &mut self,
        head: &InductiveVal,
        site_levels: Vec<Level>,
        canonical_args: &[Expr],
        _key: &Expr,
        st: &mut NestedState,
    ) -> KResult<Name> {
        let block_all = head.all.clone();
        let base_idx = st.auxes.len();
        // Register names + dedup keys for the whole copied block FIRST, so
        // self- and sibling references resolve during the copy.
        for (off, jn) in block_all.iter().enumerate() {
            let aux_name = Name::num(
                Name::str(
                    Name::str(Name::anonymous(), "_nested"),
                    jn.to_display_string(),
                ),
                (base_idx + off + 1) as u64,
            );
            let key_j = fold_app(
                Expr::const_(jn.clone(), site_levels.clone()),
                canonical_args.iter().cloned(),
            );
            st.aux_apps.push((key_j, aux_name));
        }
        // The site arguments in fvar space (canonical bvars → param fvars),
        // legal substitutes for the budgeted closed-substitution walk.
        let param_fvars: Vec<Expr> = self.params.iter().map(Local::fvar).collect();
        let mut result: Option<Name> = None;
        for (off, jn) in block_all.iter().enumerate() {
            let aux_name = st.aux_apps[base_idx + off].1.clone();
            if jn == &head.base.name {
                result = Some(aux_name.clone());
            }
            let Some(ConstantInfo::Induct(jv)) = self.base_env.find(jn).cloned() else {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "nested head block member `{}` is not an inductive in the environment",
                        jn.to_display_string()
                    ),
                );
            };
            let np_j = jv.num_params as usize;
            if canonical_args.len() != np_j {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "nested occurrence instantiates {} of `{}`'s {} parameters",
                        canonical_args.len(),
                        jn.to_display_string(),
                        np_j
                    ),
                );
            }
            let args_fvar: Vec<Expr> = canonical_args
                .iter()
                .map(|a| subst_loose_bvars(a, 0, &param_fvars, 0))
                .collect::<KResult<_>>()?;
            // The copied type: J's levels at the site, J's parameters at the
            // instantiated arguments, re-abstracted over this block's params.
            let j_lparams = jv.base.level_params.clone();
            let mut jt = self.with_tc(|tc| {
                tc.instantiate_lparams(&jv.base.type_, &j_lparams, &site_levels, 0)
            })?;
            for arg in &args_fvar {
                let ExprNode::ForallE { body, .. } = jt.node() else {
                    return reject(
                        RejectClass::BlockMismatch,
                        format!(
                            "nested head `{}` type is shorter than its parameter count",
                            jn.to_display_string()
                        ),
                    );
                };
                let body = body.clone();
                jt = self.with_tc(|tc| tc.instantiate(&body, 0, arg, 0))?;
            }
            let aux_ty = mk_pi_locals(&self.params.clone(), jt)?;
            let mut aux_ctor_names: Vec<Name> = Vec::new();
            let mut ctor_names: Vec<(Name, Name)> = Vec::new();
            for cn in &jv.ctors {
                let Some(ConstantInfo::Ctor(cv)) = self.base_env.find(cn).cloned() else {
                    return reject(
                        RejectClass::BlockMismatch,
                        format!(
                            "nested head constructor `{}` is absent from the environment",
                            cn.to_display_string()
                        ),
                    );
                };
                let mut ct = self.with_tc(|tc| {
                    tc.instantiate_lparams(&cv.base.type_, &j_lparams, &site_levels, 0)
                })?;
                for arg in &args_fvar {
                    let ExprNode::ForallE { body, .. } = ct.node() else {
                        return reject(
                            RejectClass::BlockMismatch,
                            format!(
                                "nested head constructor `{}` is shorter than its parameter count",
                                cn.to_display_string()
                            ),
                        );
                    };
                    let body = body.clone();
                    ct = self.with_tc(|tc| tc.instantiate(&body, 0, arg, 0))?;
                }
                let closed = mk_pi_locals(&self.params.clone(), ct)?;
                let aux_ctor_name =
                    Name::str(aux_name.clone(), strip_prefix(cn, jn).to_display_string());
                aux_ctor_names.push(aux_ctor_name.clone());
                ctor_names.push((aux_ctor_name.clone(), cn.clone()));
                st.aux_ctors.push(ConstructorVal {
                    base: fln_env::constants::ConstantVal {
                        name: aux_ctor_name,
                        level_params: self.lparams.clone(),
                        type_: closed,
                    },
                    induct: aux_name.clone(),
                    cidx: cv.cidx,
                    num_params: self.nparams as u32,
                    num_fields: cv.num_fields,
                    is_unsafe: cv.is_unsafe,
                });
            }
            st.aux_types.push(InductiveVal {
                base: fln_env::constants::ConstantVal {
                    name: aux_name.clone(),
                    level_params: self.lparams.clone(),
                    type_: aux_ty,
                },
                num_params: self.nparams as u32,
                num_indices: jv.num_indices,
                all: Vec::new(),
                ctors: aux_ctor_names,
                num_nested: 0,
                is_rec: false,
                is_unsafe: self.is_unsafe,
                is_reflexive: false,
            });
            st.auxes.push(NestedAux {
                aux_name,
                orig_app: st.aux_apps[base_idx + off].0.clone(),
                site_levels: site_levels.clone(),
                inst_args: canonical_args.to_vec(),
                ctor_names,
            });
        }
        result.ok_or_else(|| {
            Stop::Reject(
                RejectClass::BlockMismatch,
                "nested head is absent from its own mutual block".into(),
            )
        })
    }

    /// The pin's `restore_nested` (inductive.cpp:828-872) on closed terms:
    /// renamed auxiliary recursors, auxiliary type applications mapped back
    /// to the original instantiated occurrence, auxiliary constructor
    /// applications mapped back to the original constructor.
    fn restore_expr(
        &self,
        e: &Expr,
        st: &NestedState,
        rec_rename: &[(Name, Name)],
        depth: u32,
    ) -> KResult<Expr> {
        depth_guard(depth)?;
        let mut args: Vec<Expr> = Vec::new();
        let mut head = e.clone();
        while let ExprNode::App { f, a } = head.node() {
            args.push(a.clone());
            let next = f.clone();
            head = next;
        }
        args.reverse();
        if let ExprNode::Const { name, levels } = head.node() {
            let mut restored_args = Vec::with_capacity(args.len());
            for a in &args {
                restored_args.push(self.restore_expr(a, st, rec_rename, depth + 1)?);
            }
            if let Some((_, renamed)) = rec_rename.iter().find(|(g, _)| g == name) {
                return Ok(fold_app(
                    Expr::const_(renamed.clone(), levels.clone()),
                    restored_args.into_iter(),
                ));
            }
            if let Some(aux) = st.auxes.iter().find(|a| &a.aux_name == name) {
                // `auxJ params… trailing…` → the original occurrence with the
                // canonical template instantiated at THIS site's parameters.
                if restored_args.len() < self.nparams {
                    return reject(
                        RejectClass::BlockMismatch,
                        "auxiliary type application is under-applied in a generated recursor",
                    );
                }
                let site_params = &restored_args[..self.nparams];
                let body = subst_loose_bvars(&aux.orig_app, 0, site_params, depth + 1)?;
                return Ok(fold_app(
                    body,
                    restored_args[self.nparams..].iter().cloned(),
                ));
            }
            if let Some((aux, orig_ctor)) = st.find_aux_ctor(name) {
                if restored_args.len() < self.nparams {
                    return reject(
                        RejectClass::BlockMismatch,
                        "auxiliary constructor application is under-applied in a generated recursor",
                    );
                }
                let template = fold_app(
                    Expr::const_(orig_ctor.clone(), aux.site_levels.clone()),
                    aux.inst_args.iter().cloned(),
                );
                let site_params = &restored_args[..self.nparams];
                let body = subst_loose_bvars(&template, 0, site_params, depth + 1)?;
                return Ok(fold_app(
                    body,
                    restored_args[self.nparams..].iter().cloned(),
                ));
            }
            return Ok(fold_app(head.clone(), restored_args.into_iter()));
        }
        if !args.is_empty() {
            let restored_head = self.restore_expr(&head, st, rec_rename, depth + 1)?;
            let mut out = restored_head;
            for a in &args {
                out = Expr::app(out, self.restore_expr(a, st, rec_rename, depth + 1)?);
            }
            return Ok(out);
        }
        Ok(match e.node() {
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::lam(
                binder_name.clone(),
                self.restore_expr(binder_type, st, rec_rename, depth + 1)?,
                self.restore_expr(body, st, rec_rename, depth + 1)?,
                *binder_info,
            ),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::forall_e(
                binder_name.clone(),
                self.restore_expr(binder_type, st, rec_rename, depth + 1)?,
                self.restore_expr(body, st, rec_rename, depth + 1)?,
                *binder_info,
            ),
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => Expr::let_e(
                decl_name.clone(),
                self.restore_expr(type_, st, rec_rename, depth + 1)?,
                self.restore_expr(value, st, rec_rename, depth + 1)?,
                self.restore_expr(body, st, rec_rename, depth + 1)?,
                *non_dep,
            ),
            ExprNode::MData { data, expr } => Expr::mdata(
                data.clone(),
                self.restore_expr(expr, st, rec_rename, depth + 1)?,
            ),
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => Expr::proj(
                struct_name.clone(),
                *idx,
                self.restore_expr(expr, st, rec_rename, depth + 1)?,
            ),
            _ => e.clone(),
        })
    }
}

/// Left fold of applications.
fn fold_app(head: Expr, args: impl Iterator<Item = Expr>) -> Expr {
    let mut out = head;
    for a in args {
        out = Expr::app(out, a);
    }
    out
}

/// One auxiliary type minted by the nested translation, with everything the
/// restore step inverts.
struct NestedAux {
    aux_name: Name,
    /// The original occurrence in param-canonical form (`Const(head, site
    /// levels)` applied to the instantiated parameter args, this block's
    /// parameters as the outermost bvars).
    orig_app: Expr,
    site_levels: Vec<Level>,
    inst_args: Vec<Expr>,
    /// auxiliary ctor name → original ctor name, in `cidx` order.
    ctor_names: Vec<(Name, Name)>,
}

/// Lower one nested-head parameter while keeping binders introduced inside the
/// parameter distinct from loose locals surrounding the occurrence.
pub(crate) fn lower_param_expr(
    e: &Expr,
    nparams: usize,
    site_inner: u32,
    bound_inside_arg: u32,
    depth: u32,
) -> KResult<Expr> {
    depth_guard(depth)?;
    if e.loose_bvar_range() == 0 {
        return Ok(e.clone());
    }
    Ok(match e.node() {
        ExprNode::BVar { idx } if *idx < bound_inside_arg => e.clone(),
        ExprNode::BVar { idx } => {
            let loose = idx - bound_inside_arg;
            if loose < site_inner {
                return reject(
                    RejectClass::BlockMismatch,
                    "nested inductive datatype parameters cannot contain local variables",
                );
            }
            let lowered = loose - site_inner;
            if lowered as usize >= nparams {
                return reject(
                    RejectClass::BlockMismatch,
                    "nested occurrence parameter reference escapes the telescope",
                );
            }
            Expr::bvar(bound_inside_arg + lowered).unwrap_or_else(|_| e.clone())
        }
        ExprNode::App { f, a } => Expr::app(
            lower_param_expr(f, nparams, site_inner, bound_inside_arg, depth + 1)?,
            lower_param_expr(a, nparams, site_inner, bound_inside_arg, depth + 1)?,
        ),
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::lam(
            binder_name.clone(),
            lower_param_expr(
                binder_type,
                nparams,
                site_inner,
                bound_inside_arg,
                depth + 1,
            )?,
            lower_param_expr(body, nparams, site_inner, bound_inside_arg + 1, depth + 1)?,
            *binder_info,
        ),
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::forall_e(
            binder_name.clone(),
            lower_param_expr(
                binder_type,
                nparams,
                site_inner,
                bound_inside_arg,
                depth + 1,
            )?,
            lower_param_expr(body, nparams, site_inner, bound_inside_arg + 1, depth + 1)?,
            *binder_info,
        ),
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            non_dep,
        } => Expr::let_e(
            decl_name.clone(),
            lower_param_expr(type_, nparams, site_inner, bound_inside_arg, depth + 1)?,
            lower_param_expr(value, nparams, site_inner, bound_inside_arg, depth + 1)?,
            lower_param_expr(body, nparams, site_inner, bound_inside_arg + 1, depth + 1)?,
            *non_dep,
        ),
        ExprNode::MData { data, expr } => Expr::mdata(
            data.clone(),
            lower_param_expr(expr, nparams, site_inner, bound_inside_arg, depth + 1)?,
        ),
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => Expr::proj(
            struct_name.clone(),
            *idx,
            lower_param_expr(expr, nparams, site_inner, bound_inside_arg, depth + 1)?,
        ),
        _ => e.clone(),
    })
}

/// The forward translation's accumulating state.
#[derive(Default)]
struct NestedState {
    /// Dedup registry (pin `m_nested_aux`): normalized original application →
    /// auxiliary type name.
    aux_apps: Vec<(Expr, Name)>,
    auxes: Vec<NestedAux>,
    aux_types: Vec<InductiveVal>,
    aux_ctors: Vec<ConstructorVal>,
}

impl NestedState {
    fn is_aux_name(&self, n: &Name) -> bool {
        self.aux_types.iter().any(|t| &t.base.name == n)
    }

    fn lookup_aux(&self, key: &Expr) -> Option<Name> {
        self.aux_apps
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, n)| n.clone())
    }

    fn find_aux_ctor(&self, n: &Name) -> Option<(&NestedAux, &Name)> {
        for aux in &self.auxes {
            for (aux_ctor, orig_ctor) in &aux.ctor_names {
                if aux_ctor == n {
                    return Some((aux, orig_ctor));
                }
            }
        }
        None
    }

    fn restore_ctor_name(&self, n: &Name) -> Name {
        self.find_aux_ctor(n)
            .map(|(_, orig)| orig.clone())
            .unwrap_or_else(|| n.clone())
    }
}

/// Field-by-field comparison of a regenerated recursor against the decoded
/// row. Types and rule right-hand sides compare STRUCTURALLY (the decoded rows
/// were produced by this same algorithm at the pin, so faithful regeneration
/// is byte-identical); the divergence locator pinpoints any drift.
fn compare_recursors(generated: &RecursorVal, decoded: &RecursorVal) -> KResult<()> {
    let name = decoded.base.name.to_display_string();
    if generated.base.name != decoded.base.name {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "recursor name mismatch: generated `{}`, decoded `{name}`",
                generated.base.name.to_display_string()
            ),
        );
    }
    if generated.base.level_params != decoded.base.level_params {
        // Print BOTH lists. The message used to say only that they diverged,
        // which made 228 corpus rows (bead `franken_lean-d17i`) impossible to
        // classify from the log alone: a name difference, an order difference
        // and a missing motive universe all read identically. A divergence
        // report that does not say what diverged is a measurement defect.
        let show = |ps: &[fln_core::name::Name]| -> String {
            ps.iter()
                .map(fln_core::name::Name::to_display_string)
                .collect::<Vec<_>>()
                .join(",")
        };
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "`{name}`: recursor level parameters diverge from regeneration \
                 (generated [{}], decoded [{}])",
                show(&generated.base.level_params),
                show(&decoded.base.level_params)
            ),
        );
    }
    if generated.all != decoded.all
        || generated.num_params != decoded.num_params
        || generated.num_indices != decoded.num_indices
        || generated.num_motives != decoded.num_motives
        || generated.num_minors != decoded.num_minors
        || generated.k != decoded.k
        || generated.is_unsafe != decoded.is_unsafe
    {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "`{name}`: recursor observables diverge from regeneration \
                 (params {}/{}, indices {}/{}, motives {}/{}, minors {}/{}, k {}/{})",
                generated.num_params,
                decoded.num_params,
                generated.num_indices,
                decoded.num_indices,
                generated.num_motives,
                decoded.num_motives,
                generated.num_minors,
                decoded.num_minors,
                generated.k,
                decoded.k
            ),
        );
    }
    if generated.base.type_ != decoded.base.type_ {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "`{name}`: recursor type diverges from regeneration{}",
                divergence_note(&generated.base.type_, &decoded.base.type_)
            ),
        );
    }
    if generated.rules.len() != decoded.rules.len() {
        return reject(
            RejectClass::BlockMismatch,
            format!("`{name}`: rule count diverges from regeneration"),
        );
    }
    for (g, d) in generated.rules.iter().zip(&decoded.rules) {
        if g.ctor != d.ctor || g.nfields != d.nfields {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "`{name}`: rule for `{}` diverges (nfields {}/{})",
                    d.ctor.to_display_string(),
                    g.nfields,
                    d.nfields
                ),
            );
        }
        if g.rhs != d.rhs {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "`{name}`: iota rhs for `{}` diverges from regeneration{}",
                    d.ctor.to_display_string(),
                    divergence_note(&g.rhs, &d.rhs)
                ),
            );
        }
    }
    Ok(())
}

/// Match regenerated recursors by their semantic identity, not by artifact row
/// position. A block's decoded rows retain module order, which need not equal
/// the inductive types' block order.
pub(crate) fn compare_recursor_sets(
    generated: &[RecursorVal],
    decoded: &[RecursorVal],
) -> KResult<()> {
    for generated in generated {
        let Some(decoded) = decoded
            .iter()
            .find(|decoded| decoded.base.name == generated.base.name)
        else {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "decoded block lacks recursor `{}`",
                    generated.base.name.to_display_string()
                ),
            );
        };
        compare_recursors(generated, decoded)?;
    }
    Ok(())
}

fn divergence_note(generated: &Expr, decoded: &Expr) -> String {
    match crate::tc::first_divergence_public(generated, decoded) {
        Some(d) => format!(" (first divergence: {d})"),
        None => String::new(),
    }
}

/// The pin's expression equality (`expr_eq_fn<false>`, kernel/expr_eq_fn.cpp):
/// structural, with binder NAMES and binder INFOS ignored. This is the
/// comparison quot.cpp's `!=` checks actually perform — the decoded `Eq` type
/// carries hygienic binder names that alpha-vary from the pin's constructed
/// expected form.
fn pin_expr_eq(a: &Expr, b: &Expr) -> bool {
    if a == b {
        return true;
    }
    match (a.node(), b.node()) {
        (ExprNode::BVar { idx: i1 }, ExprNode::BVar { idx: i2 }) => i1 == i2,
        (ExprNode::FVar { id: id1 }, ExprNode::FVar { id: id2 }) => id1 == id2,
        (ExprNode::Sort { level: l1 }, ExprNode::Sort { level: l2 }) => l1 == l2,
        (
            ExprNode::Const {
                name: n1,
                levels: l1,
            },
            ExprNode::Const {
                name: n2,
                levels: l2,
            },
        ) => n1 == n2 && l1 == l2,
        (ExprNode::App { f: f1, a: a1 }, ExprNode::App { f: f2, a: a2 }) => {
            pin_expr_eq(f1, f2) && pin_expr_eq(a1, a2)
        }
        (
            ExprNode::Lam {
                binder_type: t1,
                body: b1,
                ..
            },
            ExprNode::Lam {
                binder_type: t2,
                body: b2,
                ..
            },
        )
        | (
            ExprNode::ForallE {
                binder_type: t1,
                body: b1,
                ..
            },
            ExprNode::ForallE {
                binder_type: t2,
                body: b2,
                ..
            },
        ) => pin_expr_eq(t1, t2) && pin_expr_eq(b1, b2),
        (
            ExprNode::LetE {
                type_: t1,
                value: v1,
                body: b1,
                ..
            },
            ExprNode::LetE {
                type_: t2,
                value: v2,
                body: b2,
                ..
            },
        ) => pin_expr_eq(t1, t2) && pin_expr_eq(v1, v2) && pin_expr_eq(b1, b2),
        (ExprNode::Lit { literal: l1 }, ExprNode::Lit { literal: l2 }) => l1 == l2,
        (ExprNode::MData { expr: e1, .. }, ExprNode::MData { expr: e2, .. }) => pin_expr_eq(e1, e2),
        (
            ExprNode::Proj {
                struct_name: n1,
                idx: i1,
                expr: e1,
            },
            ExprNode::Proj {
                struct_name: n2,
                idx: i2,
                expr: e2,
            },
        ) => n1 == n2 && i1 == i2 && pin_expr_eq(e1, e2),
        _ => false,
    }
}

/// Entry: check one inductive block (types + ctors + recursors, decoded and
/// untrusted) against `env` under `budget`.
pub(crate) fn check_inductive_block(
    env: &Environment,
    block: &InductiveBlock,
    budget: Budget,
) -> (KResult<()>, Consumption) {
    match Engine::new(env, block, budget) {
        Ok(mut engine) => {
            let out = engine.run();
            (out, engine.used)
        }
        Err(stop) => (Err(stop), Consumption::default()),
    }
}

// ---- Quotients (KR-950..954) ---------------------------------------------------------

fn arrow(a: Expr, b: Expr) -> Expr {
    // pin `mk_arrow` (expr.cpp:181): binder named `a`, default info.
    Expr::forall_e(Name::str(Name::anonymous(), "a"), a, b, BinderInfo::Default)
}

fn pi(name: &str, info: BinderInfo, type_: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::str(Name::anonymous(), name), type_, body, info)
}

/// KR-950: the environment's `Eq` must be the expected one-parameter,
/// one-constructor equality (types compared structurally, as at the pin).
fn check_eq_type(env: &Environment) -> KResult<()> {
    let eq_name = Name::str(Name::anonymous(), "Eq");
    let Some(ConstantInfo::Induct(eq)) = env.find(&eq_name) else {
        return reject(
            RejectClass::BlockMismatch,
            "failed to initialize quot module, environment does not have 'Eq' type",
        );
    };
    if eq.base.level_params.len() != 1 || eq.ctors.len() != 1 {
        return reject(
            RejectClass::BlockMismatch,
            "failed to initialize quot module, unexpected 'Eq' shape",
        );
    }
    let u = Level::param(eq.base.level_params[0].clone());
    // ∀ {α : Sort u}, α → α → Prop  (bvars: α at the binder)
    let alpha = Expr::bvar(0).expect("packs");
    let alpha1 = Expr::bvar(1).expect("packs");
    let expected = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        arrow(alpha.clone(), {
            // inner arrow shifts α to bvar 1
            arrow(alpha1.clone(), Expr::sort(Level::zero()))
        }),
    );
    if !pin_expr_eq(&eq.base.type_, &expected) {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "failed to initialize quot module, 'Eq' has an unexpected type{}",
                divergence_note(&expected, &eq.base.type_)
            ),
        );
    }
    let refl_name = eq.ctors[0].clone();
    let Some(ConstantInfo::Ctor(refl)) = env.find(&refl_name) else {
        return reject(
            RejectClass::BlockMismatch,
            "failed to initialize quot module, 'Eq' constructor is missing",
        );
    };
    if refl.base.level_params.len() != 1 {
        return reject(
            RejectClass::BlockMismatch,
            "failed to initialize quot module, unexpected 'Eq' constructor shape",
        );
    }
    let u = Level::param(refl.base.level_params[0].clone());
    // ∀ {α : Sort u} (a : α), Eq.{u} α a a
    let expected_refl = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "a",
            BinderInfo::Default,
            Expr::bvar(0).expect("packs"),
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(eq_name, vec![u]),
                        Expr::bvar(1).expect("packs"),
                    ),
                    Expr::bvar(0).expect("packs"),
                ),
                Expr::bvar(0).expect("packs"),
            ),
        ),
    );
    if !pin_expr_eq(&refl.base.type_, &expected_refl) {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "failed to initialize quot module, unexpected type for 'Eq' type constructor{}",
                divergence_note(&expected_refl, &refl.base.type_)
            ),
        );
    }
    Ok(())
}

/// KR-951..954: the four quotient declarations, types built exactly as the
/// pin builds them (quot.cpp:59-97) and compared structurally against the
/// decoded rows.
pub(crate) fn check_quotient_init(
    env: &Environment,
    decls: &[QuotVal],
    _budget: Budget,
) -> (KResult<()>, Consumption) {
    let out = check_quotient_inner(env, decls);
    (out, Consumption::default())
}

fn check_quotient_inner(env: &Environment, decls: &[QuotVal]) -> KResult<()> {
    check_eq_type(env)?;
    let quot = Name::str(Name::anonymous(), "Quot");
    let u_name = Name::str(Name::anonymous(), "u");
    let v_name = Name::str(Name::anonymous(), "v");
    let u = Level::param(u_name.clone());
    let v = Level::param(v_name.clone());
    let prop = || Expr::sort(Level::zero());
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    // Quot.{u} : ∀ {α : Sort u}, (α → α → Prop) → Sort u
    let quot_ty = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        arrow(arrow(bv(0), arrow(bv(1), prop())), Expr::sort(u.clone())),
    );
    // Quot.mk.{u} : ∀ {α : Sort u} (r : α → α → Prop) (a : α), @Quot.{u} α r
    let quot_app = |alpha: Expr, r: Expr| {
        Expr::app(
            Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), alpha),
            r,
        )
    };
    let quot_mk_ty = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "r",
            BinderInfo::Default,
            arrow(bv(0), arrow(bv(1), prop())),
            pi("a", BinderInfo::Default, bv(1), quot_app(bv(2), bv(1))),
        ),
    );
    // Quot.lift.{u,v} :
    //   ∀ {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β),
    //     (∀ (a b : α), r a b → f a = f b) → @Quot.{u} α r → β
    let eq_name = Name::str(Name::anonymous(), "Eq");
    // Binders (outer→inner): α(0 shifts as we descend), r, β, f, then the
    // sanity premise Π a Π b, (arrow) — bvar arithmetic done per position.
    let sanity = pi(
        "a",
        BinderInfo::Default,
        bv(3), // α from under f: binders α r β f → a sees α at 3
        pi(
            "b",
            BinderInfo::Default,
            bv(4),
            arrow(
                Expr::app(Expr::app(bv(4), bv(1)), bv(0)), // r a b (r at 4 under a,b,+arrow-domain? see note)
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(eq_name, vec![v.clone()]), bv(4)), // β
                        Expr::app(bv(3), bv(2)),                                  // f a
                    ),
                    Expr::app(bv(3), bv(1)), // f b
                ),
            ),
        ),
    );
    let quot_lift_ty = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "r",
            BinderInfo::Implicit,
            arrow(bv(0), arrow(bv(1), prop())),
            pi(
                "β",
                BinderInfo::Implicit,
                Expr::sort(v.clone()),
                pi(
                    "f",
                    BinderInfo::Default,
                    arrow(bv(2), bv(1)),
                    arrow(
                        sanity,
                        arrow(
                            {
                                // @Quot.{u} α r with α at 4, r at 3 (under f + sanity-arrow)
                                Expr::app(
                                    Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), bv(4)),
                                    bv(3),
                                )
                            },
                            bv(3), // β
                        ),
                    ),
                ),
            ),
        ),
    );
    // Quot.ind.{u} :
    //   ∀ {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop},
    //     (∀ (a : α), β (@Quot.mk.{u} α r a)) → ∀ (q : @Quot.{u} α r), β q
    let quot_mk = Name::str(quot.clone(), "mk");
    let quot_ind_ty = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "r",
            BinderInfo::Implicit,
            arrow(bv(0), arrow(bv(1), prop())),
            pi(
                "β",
                BinderInfo::Implicit,
                arrow(
                    Expr::app(
                        Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), bv(1)),
                        bv(0),
                    ),
                    prop(),
                ),
                pi(
                    "mk",
                    BinderInfo::Default,
                    pi(
                        "a",
                        BinderInfo::Default,
                        bv(2), // α
                        Expr::app(
                            bv(1), // β
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::const_(quot_mk.clone(), vec![u.clone()]),
                                        bv(3), // α
                                    ),
                                    bv(2), // r
                                ),
                                bv(0), // a
                            ),
                        ),
                    ),
                    pi(
                        "q",
                        BinderInfo::Default,
                        Expr::app(
                            Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), bv(3)),
                            bv(2),
                        ),
                        Expr::app(bv(2), bv(0)), // β q
                    ),
                ),
            ),
        ),
    );
    let expected: Vec<(Name, Vec<Name>, Expr, QuotKind)> = vec![
        (quot.clone(), vec![u_name.clone()], quot_ty, QuotKind::Type),
        (
            Name::str(quot.clone(), "mk"),
            vec![u_name.clone()],
            quot_mk_ty,
            QuotKind::Ctor,
        ),
        (
            Name::str(quot.clone(), "lift"),
            vec![u_name.clone(), v_name],
            quot_lift_ty,
            QuotKind::Lift,
        ),
        (
            Name::str(quot.clone(), "ind"),
            vec![u_name],
            quot_ind_ty,
            QuotKind::Ind,
        ),
    ];
    if decls.len() != expected.len() {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "quotient initialization needs 4 declarations, got {}",
                decls.len()
            ),
        );
    }
    for (name, lparams, type_, kind) in &expected {
        let Some(decoded) = decls.iter().find(|d| &d.base.name == name) else {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "quotient declaration `{}` missing",
                    name.to_display_string()
                ),
            );
        };
        if env.contains(name) {
            return reject(
                RejectClass::AlreadyDeclared,
                format!("`{}` is already declared", name.to_display_string()),
            );
        }
        if decoded.kind != *kind || decoded.base.level_params != *lparams {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "quotient declaration `{}` has unexpected kind or level parameters",
                    name.to_display_string()
                ),
            );
        }
        if !pin_expr_eq(&decoded.base.type_, type_) {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "quotient declaration `{}` type diverges from the pin's construction{}",
                    name.to_display_string(),
                    divergence_note(type_, &decoded.base.type_)
                ),
            );
        }
    }
    Ok(())
}

/// Insert one already-checked constant into a SCRATCH environment through the
/// bounded admission path (`fln-kernel-bounded-decl-admission-ukzx`).
///
/// The five production callers all build temporary environments out of
/// declarations the kernel is itself checking, so three decisions are recorded
/// here once rather than repeated five times:
///
/// **The budget is explicitly UNBOUNDED, not absent.** These sites insert
/// material the kernel has ALREADY traversed under its own [`Budget`] during
/// header inference and constructor checking. `DeclarationBudget` bounds the
/// same row families that traversal just walked, so re-bounding here would
/// double-charge the same declaration and could refuse one the kernel had
/// already found structurally sound. The untrusted-input boundary is upstream,
/// at `check`; this is downstream of it.
///
/// **A duplicate name stays a rejection.** It is a completed determination
/// about the declaration — the name is taken — and it was a rejection before
/// this migration too.
///
/// **A non-answer never becomes one.** `Inconclusive` and `InternalFault` from
/// the environment are propagated as the kernel's own non-answers. Collapsing
/// either into `AlreadyDeclared` would be the FL-INV-07 failure this migration
/// exists to avoid: recording "we ran out of room" or "we broke" as "this
/// declaration is invalid" caches a wrong verdict about someone else's code.
pub(crate) fn scratch_admit(
    env: &Environment,
    info: ConstantInfo,
    name: &Name,
) -> Result<Environment, Stop> {
    let plan = match env.plan_add_decl(
        info,
        DeclarationBudget::UNBOUNDED,
        CollisionBudget::UNBOUNDED,
        None,
    ) {
        Outcome::Complete(DeclarationPlan::Prepared(plan)) => plan,
        Outcome::Complete(DeclarationPlan::DuplicateName { name }) => {
            return Err(Stop::Reject(
                RejectClass::AlreadyDeclared,
                format!("`{}` is already declared", name.to_display_string()),
            ));
        }
        Outcome::Inconclusive(reason) => {
            return Err(Stop::Fault(format!(
                "scratch admission of `{}` was inconclusive: {reason:?}",
                name.to_display_string()
            )));
        }
        Outcome::InternalFault(fault) => {
            return Err(Stop::Fault(format!(
                "scratch admission of `{}` faulted: {fault:?}",
                name.to_display_string()
            )));
        }
    };
    match plan.commit(env, None) {
        Outcome::Complete(DeclarationCommitted::Published(published)) => Ok(published.environment),
        Outcome::Complete(DeclarationCommitted::DuplicateName { name }) => Err(Stop::Reject(
            RejectClass::AlreadyDeclared,
            format!("`{}` is already declared", name.to_display_string()),
        )),
        Outcome::Inconclusive(reason) => Err(Stop::Fault(format!(
            "scratch publication of `{}` was inconclusive: {reason:?}",
            name.to_display_string()
        ))),
        Outcome::InternalFault(fault) => Err(Stop::Fault(format!(
            "scratch publication of `{}` faulted: {fault:?}",
            name.to_display_string()
        ))),
    }
}
