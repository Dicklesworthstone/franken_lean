//! K1 bootstrap: the certified checker's typing, reduction, and defeq core
//! (bead franken_lean-zht; every rule tagged to KERNEL_CONTRACT.md).
//!
//! Slice scope (recorded on beads franken_lean-zht + franken_lean-5p2):
//! KR-100..112 typing, whnf with beta/zeta/mdata/proj/delta (KR-200..204) and
//! recursor dispatch (KR-205) — quotient computation (KR-955), inductive iota
//! (KR-316) with K conversion (KR-317), Nat-literal-to-constructor, and
//! structure-eta coercion — defeq with quick/bindings/levels/proof-irrelevance/
//! lazy-delta/function-eta/app-congruence (KR-300..312 subset), Nat literal
//! acceleration (KR-313: `reduce_nat` in the whnf loop plus the offset and
//! Bool.true-reflection machinery in defeq, wired to fln-bignum), String literal
//! expansion (KR-314: recursor major, projection scrutinee, and the defeq
//! `String.ofList` rung), unit-like eta (KR-315), structure eta in defeq
//! (KR-903), and declaration admission for axioms, definitions, and theorems
//! (KR-970..974). `reduce_native` (`Lean.reduceBool`/`Lean.reduceNat` — the
//! native_decide trust surface), opaque/mutual admission, and receipts are
//! follow-up slices; none of their absence widens acceptance — an unimplemented
//! reduction can only make defeq FAIL (a rejection), never succeed.
//!
//! Traversal discipline (§8.2c): every recursive descent charges the step budget
//! and carries an explicit depth that is checked BEFORE descending, so
//! attacker-controlled term depth converts to a typed `Inconclusive`, never a stack
//! fault. Flag pruning (loose-bvar ranges, has-level-param) keeps substitution
//! linear in the touched region only.

use fln_bignum::interop::{bignat_from_literal, literal_from_bignat};
use fln_bignum::nat::BigNat;
use fln_core::expr::{Expr, ExprNode, FVarId, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::{LeafView, Name};
use fln_env::constants::{
    ConstantInfo, DefinitionSafety, QuotKind, RecursorVal, ReducibilityHints,
};
use fln_env::environment::Environment;

use crate::verdict::{Budget, Consumption, ExhaustionReason, RejectClass};

/// Internal control flow: a real rejection or a budget stop. Never observable
/// outside `check`/`check_defeq`, which convert to [`Verdict`].
#[derive(Debug)]
pub(crate) enum Stop {
    Reject(RejectClass, String),
    Exhausted(ExhaustionReason),
}

type KResult<T> = Result<T, Stop>;

fn reject<T>(class: RejectClass, message: impl Into<String>) -> KResult<T> {
    Err(Stop::Reject(class, message.into()))
}

/// One local binder introduced during descent.
struct LocalDecl {
    id: FVarId,
    type_: Expr,
    /// Present for let-bound locals (zeta target, KR-203).
    value: Option<Expr>,
}

pub(crate) struct TypeChecker<'a> {
    env: &'a Environment,
    lparams: &'a [Name],
    locals: Vec<LocalDecl>,
    fresh: u64,
    budget: Budget,
    used: Consumption,
}

impl<'a> TypeChecker<'a> {
    pub(crate) fn new(env: &'a Environment, lparams: &'a [Name], budget: Budget) -> Self {
        TypeChecker {
            env,
            lparams,
            locals: Vec::new(),
            fresh: 0,
            budget,
            used: Consumption::default(),
        }
    }

    pub(crate) fn consumption(&self) -> Consumption {
        self.used
    }

    /// Crate-facing whnf (the admission path's sort checks).
    pub(crate) fn whnf_public(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.whnf(e, depth)
    }

    /// Crate-facing defeq (admission bodies and the standalone query surface).
    pub(crate) fn def_eq_public(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        self.is_def_eq(t, s, depth)
    }

    /// The counted hook (KR-400..403): every step charges; depth checks precede
    /// every descent.
    fn step(&mut self, depth: u32) -> KResult<()> {
        self.used.steps_used += 1;
        self.used.max_depth = self.used.max_depth.max(depth);
        if self.used.steps_used > self.budget.steps {
            return Err(Stop::Exhausted(ExhaustionReason::Steps));
        }
        if depth > self.budget.depth {
            return Err(Stop::Exhausted(ExhaustionReason::Depth));
        }
        Ok(())
    }

    fn fresh_fvar(&mut self, type_: Expr, value: Option<Expr>) -> FVarId {
        self.fresh += 1;
        let id = FVarId(Name::num(
            Name::str(Name::anonymous(), "_kernel"),
            self.fresh,
        ));
        self.locals.push(LocalDecl {
            id: id.clone(),
            type_,
            value,
        });
        id
    }

    fn drop_local(&mut self) {
        self.locals.pop();
    }

    fn find_local(&self, id: &FVarId) -> Option<&LocalDecl> {
        self.locals.iter().rev().find(|d| &d.id == id)
    }

    // ---- de Bruijn machinery -----------------------------------------------------------

    /// Replace loose `bvar k` by `subst` (which must be closed w.r.t. bvars, as all
    /// kernel substitution values here are: fvars or closed terms), decrementing
    /// looser indices. Flag-pruned: subtrees without loose bvars ≥ k are shared.
    fn instantiate(&mut self, e: &Expr, k: u32, subst: &Expr, depth: u32) -> KResult<Expr> {
        self.step(depth)?;
        if e.loose_bvar_range() <= k {
            return Ok(e.clone());
        }
        Ok(match e.node() {
            ExprNode::BVar { idx } => {
                if *idx == k {
                    subst.clone()
                } else if *idx > k {
                    Expr::bvar(idx - 1).unwrap_or_else(|_| e.clone())
                } else {
                    e.clone()
                }
            }
            ExprNode::App { f, a } => {
                let f2 = self.instantiate(f, k, subst, depth + 1)?;
                let a2 = self.instantiate(a, k, subst, depth + 1)?;
                Expr::app(f2, a2)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.instantiate(binder_type, k, subst, depth + 1)?;
                let b2 = self.instantiate(body, k + 1, subst, depth + 1)?;
                Expr::lam(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.instantiate(binder_type, k, subst, depth + 1)?;
                let b2 = self.instantiate(body, k + 1, subst, depth + 1)?;
                Expr::forall_e(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.instantiate(type_, k, subst, depth + 1)?;
                let v2 = self.instantiate(value, k, subst, depth + 1)?;
                let b2 = self.instantiate(body, k + 1, subst, depth + 1)?;
                Expr::let_e(decl_name.clone(), t2, v2, b2, *non_dep)
            }
            ExprNode::MData { data, expr } => {
                let inner = self.instantiate(expr, k, subst, depth + 1)?;
                Expr::mdata(data.clone(), inner)
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let inner = self.instantiate(expr, k, subst, depth + 1)?;
                Expr::proj(struct_name.clone(), *idx, inner)
            }
            // Range-0 kinds are unreachable here thanks to the pruning guard.
            ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => e.clone(),
        })
    }

    /// Instantiate a binder body with an fvar (the standard descent move).
    fn open_binder(&mut self, body: &Expr, id: &FVarId, depth: u32) -> KResult<Expr> {
        let fv = Expr::fvar(id.clone());
        self.instantiate(body, 0, &fv, depth)
    }

    /// Substitute declared level parameters by concrete levels throughout a type
    /// (KR-105). Flag-pruned on has-level-param.
    fn instantiate_lparams(
        &mut self,
        e: &Expr,
        params: &[Name],
        levels: &[Level],
        depth: u32,
    ) -> KResult<Expr> {
        self.step(depth)?;
        if !e.has_level_param() {
            return Ok(e.clone());
        }
        let subst_level = |l: &Level| -> Level { substitute_level(l, params, levels) };
        Ok(match e.node() {
            ExprNode::Sort { level } => Expr::sort(subst_level(level)),
            ExprNode::Const { name, levels: ls } => {
                Expr::const_(name.clone(), ls.iter().map(subst_level).collect())
            }
            ExprNode::App { f, a } => {
                let f2 = self.instantiate_lparams(f, params, levels, depth + 1)?;
                let a2 = self.instantiate_lparams(a, params, levels, depth + 1)?;
                Expr::app(f2, a2)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.instantiate_lparams(binder_type, params, levels, depth + 1)?;
                let b2 = self.instantiate_lparams(body, params, levels, depth + 1)?;
                Expr::lam(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.instantiate_lparams(binder_type, params, levels, depth + 1)?;
                let b2 = self.instantiate_lparams(body, params, levels, depth + 1)?;
                Expr::forall_e(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.instantiate_lparams(type_, params, levels, depth + 1)?;
                let v2 = self.instantiate_lparams(value, params, levels, depth + 1)?;
                let b2 = self.instantiate_lparams(body, params, levels, depth + 1)?;
                Expr::let_e(decl_name.clone(), t2, v2, b2, *non_dep)
            }
            ExprNode::MData { data, expr } => {
                let inner = self.instantiate_lparams(expr, params, levels, depth + 1)?;
                Expr::mdata(data.clone(), inner)
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let inner = self.instantiate_lparams(expr, params, levels, depth + 1)?;
                Expr::proj(struct_name.clone(), *idx, inner)
            }
            _ => e.clone(),
        })
    }

    // ---- whnf (KR-200..204) ------------------------------------------------------------

    /// KR-200: whnf-core then delta, looped to a fixpoint — with KR-313 literal
    /// arithmetic (`reduce_nat`) tried on every whnf-core'd form before delta,
    /// exactly the pin's loop order (type_checker.cpp:663). `reduce_native`
    /// (`Lean.reduceBool`/`Lean.reduceNat`) is the native_decide surface, a
    /// follow-up slice: its absence leaves those applications stuck —
    /// under-acceptance, never over-acceptance.
    fn whnf(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        let mut current = self.whnf_core(e, depth)?;
        loop {
            if let Some(value) = self.reduce_nat(&current, depth)? {
                return Ok(value);
            }
            match self.unfold_definition(&current, depth)? {
                Some(next) => current = self.whnf_core(&next, depth)?,
                None => return Ok(current),
            }
        }
    }

    /// KR-201..204: mdata, beta (batched), zeta (let + let-fvar), proj.
    fn whnf_core(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.step(depth)?;
        Ok(match e.node() {
            ExprNode::MData { expr, .. } => self.whnf_core(expr, depth + 1)?,
            ExprNode::FVar { id } => match self.find_local(id).and_then(|d| d.value.clone()) {
                // KR-203: a let-bound fvar unfolds to its value.
                Some(value) => self.whnf_core(&value, depth + 1)?,
                None => e.clone(),
            },
            ExprNode::LetE { value, body, .. } => {
                // KR-203 zeta.
                let value = value.clone();
                let body = body.clone();
                let reduced = self.instantiate(&body, 0, &value, depth + 1)?;
                self.whnf_core(&reduced, depth + 1)?
            }
            ExprNode::App { .. } => {
                // Collect the spine, whnf the head, then KR-202 batched beta.
                let (head0, args) = app_spine(e);
                let head = self.whnf_core(&head0, depth + 1)?;
                if matches!(head.node(), ExprNode::Lam { .. }) {
                    let mut current = head;
                    let mut consumed = 0usize;
                    while consumed < args.len() {
                        let ExprNode::Lam { body, .. } = current.node() else {
                            break;
                        };
                        let body = body.clone();
                        let arg = args
                            .get(consumed)
                            .cloned()
                            .unwrap_or_else(|| current.clone());
                        current = self.instantiate(&body, 0, &arg, depth + 1)?;
                        consumed += 1;
                    }
                    for arg in &args[consumed..] {
                        current = Expr::app(current, arg.clone());
                    }
                    self.whnf_core(&current, depth + 1)?
                } else if head == head0 {
                    // KR-205: the head is stable — try quotient computation, then
                    // inductive iota, on the original application.
                    match self.reduce_recursor(e, depth + 1)? {
                        Some(reduced) => self.whnf_core(&reduced, depth + 1)?,
                        None => e.clone(),
                    }
                } else {
                    // The head changed (let-fvar zeta, mdata strip): rebuild and
                    // continue, as the pin re-enters whnf_core on the update.
                    let mut rebuilt = head;
                    for arg in args {
                        rebuilt = Expr::app(rebuilt, arg);
                    }
                    self.whnf_core(&rebuilt, depth + 1)?
                }
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                // KR-204: projection of a constructor application.
                let struct_name = struct_name.clone();
                let idx = *idx;
                let scrutinee = self.whnf(&expr.clone(), depth + 1)?;
                // KR-314 (pin reduce_proj_core, type_checker.cpp:358): a
                // String-literal scrutinee expands to its constructor spine
                // (whnf'd so `String.ofList` unfolds to the real constructor)
                // before field extraction.
                let scrutinee = if let ExprNode::Lit {
                    literal: Literal::Str(value),
                } = scrutinee.node()
                {
                    let expanded = string_lit_to_constructor(value);
                    self.whnf(&expanded, depth + 1)?
                } else {
                    scrutinee
                };
                match self.reduce_proj(&struct_name, idx, &scrutinee) {
                    Some(field) => self.whnf_core(&field, depth + 1)?,
                    None => Expr::proj(struct_name, idx, scrutinee),
                }
            }
            _ => e.clone(),
        })
    }

    /// KR-204's constructor recognition: `proj I idx (mk params fields)`.
    fn reduce_proj(&self, _struct_name: &Name, idx: u64, scrutinee: &Expr) -> Option<Expr> {
        let mut args: Vec<&Expr> = Vec::new();
        let mut head = scrutinee;
        while let ExprNode::App { f, a } = head.node() {
            args.push(a);
            head = f;
        }
        args.reverse();
        let ExprNode::Const { name, .. } = head.node() else {
            return None;
        };
        let ConstantInfo::Ctor(ctor) = self.env.find(name)? else {
            return None;
        };
        let field_index = usize::try_from(ctor.num_params as u64 + idx).ok()?;
        args.get(field_index).map(|e| (*e).clone())
    }

    /// Delta (whnf layer, KR-200): unfold a safe definition at the application head.
    /// Slice note: theorems and opaques are NOT unfolded here (proof irrelevance
    /// covers theorem bodies; opaque unfolding is a follow-up refinement) — an
    /// under-unfolding can only under-accept, never over-accept.
    fn unfold_definition(&mut self, e: &Expr, depth: u32) -> KResult<Option<Expr>> {
        let mut args: Vec<Expr> = Vec::new();
        let mut head = e.clone();
        while let ExprNode::App { f, a } = head.node() {
            args.push(a.clone());
            let next = f.clone();
            head = next;
        }
        args.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Defn(defn)) = self.env.find(name) else {
            return Ok(None);
        };
        if defn.safety != DefinitionSafety::Safe {
            return Ok(None);
        }
        let value = defn.value.clone();
        let params = defn.base.level_params.clone();
        let levels = levels.clone();
        let mut unfolded = self.instantiate_lparams(&value, &params, &levels, depth + 1)?;
        for arg in args {
            unfolded = Expr::app(unfolded, arg);
        }
        Ok(Some(unfolded))
    }

    fn definition_height(&self, e: &Expr) -> Option<u32> {
        let mut head = e;
        while let ExprNode::App { f, .. } = head.node() {
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return None;
        };
        match self.env.find(name)? {
            ConstantInfo::Defn(d) if d.safety == DefinitionSafety::Safe => {
                Some(match d.hints {
                    ReducibilityHints::Regular(h) => h,
                    // Abbrev unfolds eagerly (treated as tall); Opaque as height 0.
                    ReducibilityHints::Abbrev => u32::MAX,
                    ReducibilityHints::Opaque => 0,
                })
            }
            _ => None,
        }
    }

    // ---- recursor reduction (KR-205/316/317/955) ---------------------------------------

    /// KR-205 (`reduce_recursor`): when an application head is stable, try
    /// quotient computation first, then inductive iota. `None` means no rule
    /// fires — the term is simply stuck, never an error.
    fn reduce_recursor(&mut self, e: &Expr, depth: u32) -> KResult<Option<Expr>> {
        self.step(depth)?;
        if let Some(reduced) = self.quot_reduce_rec(e, depth)? {
            return Ok(Some(reduced));
        }
        self.inductive_reduce_rec(e, depth)
    }

    /// KR-955 (`quot_reduce_rec`): `Quot.lift f h (Quot.mk r a) ⟶ f a` (mk at
    /// argument 5, f at 3); `Quot.ind p (Quot.mk r a) ⟶ p a` (mk at 4, p at 3);
    /// trailing arguments preserved. Dispatch is by the head constant's
    /// environment kind (`QuotKind::Lift`/`Ind`, scrutinee head `QuotKind::Ctor`
    /// with exactly three arguments), so the lane is active exactly when
    /// quotients are initialized in this environment.
    fn quot_reduce_rec(&mut self, e: &Expr, depth: u32) -> KResult<Option<Expr>> {
        let (head, args) = app_spine(e);
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        let kind = match self.env.find(name) {
            Some(ConstantInfo::Quot(quot)) => quot.kind,
            _ => return Ok(None),
        };
        let (mk_pos, arg_pos) = match kind {
            QuotKind::Lift => (5usize, 3usize),
            QuotKind::Ind => (4, 3),
            QuotKind::Type | QuotKind::Ctor => return Ok(None),
        };
        if args.len() <= mk_pos {
            return Ok(None);
        }
        let mk = self.whnf(&args[mk_pos], depth + 1)?;
        let (mk_head, mk_args) = app_spine(&mk);
        let ExprNode::Const { name: mk_name, .. } = mk_head.node() else {
            return Ok(None);
        };
        let mk_is_quot_ctor = matches!(
            self.env.find(mk_name),
            Some(ConstantInfo::Quot(quot)) if quot.kind == QuotKind::Ctor
        );
        if !mk_is_quot_ctor || mk_args.len() != 3 {
            return Ok(None);
        }
        // `Quot.mk r a`'s last argument is the underlying element.
        let mut reduced = Expr::app(args[arg_pos].clone(), mk_args[2].clone());
        for extra in &args[mk_pos + 1..] {
            reduced = Expr::app(reduced, extra.clone());
        }
        Ok(Some(reduced))
    }

    /// KR-316 (`inductive_reduce_rec`): a recursor application fires when its
    /// major premise — at `nparams + nmotives + nminors + nindices` — reduces to
    /// a constructor of the right inductive, after K conversion (KR-317) and
    /// Nat-literal-to-constructor / structure-eta coercion. The matching rule's
    /// right-hand side is instantiated with the recursor's levels and applied to
    /// params+motives+minors from the recursor spine, the constructor's fields,
    /// and the trailing arguments. Literal majors convert first: Nat via
    /// `nat_lit_to_constructor`, String via KR-314 expansion (inductive.h:93-95).
    fn inductive_reduce_rec(&mut self, e: &Expr, depth: u32) -> KResult<Option<Expr>> {
        let (head, rec_args) = app_spine(e);
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Rec(rec)) = self.env.find(name) else {
            return Ok(None);
        };
        let rec = rec.clone();
        let levels = levels.clone();
        let major_idx =
            (rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices) as usize;
        if rec_args.len() <= major_idx {
            return Ok(None);
        }
        let mut major = rec_args[major_idx].clone();
        if rec.k {
            major = self.major_to_cnstr_when_k(&rec, &major, depth)?;
        }
        major = self.whnf(&major, depth + 1)?;
        match major.node() {
            ExprNode::Lit {
                literal: Literal::Nat(value),
            } => {
                major = nat_lit_to_constructor(value);
            }
            ExprNode::Lit {
                literal: Literal::Str(value),
            } => {
                // KR-314 (inductive.h:95): a String-literal major expands to its
                // constructor spine, whnf'd so `String.ofList` delta-unfolds to
                // the actual constructor application.
                major = self.whnf(&string_lit_to_constructor(value), depth + 1)?;
            }
            _ => major = self.major_to_cnstr_when_structure(&rec, &major, depth)?,
        }
        let (major_head, major_args) = app_spine(&major);
        let ExprNode::Const {
            name: ctor_name, ..
        } = major_head.node()
        else {
            return Ok(None);
        };
        let Some(rule) = rec.rules.iter().find(|rule| &rule.ctor == ctor_name) else {
            return Ok(None);
        };
        let nfields = rule.nfields as usize;
        if nfields > major_args.len() {
            return Ok(None);
        }
        if levels.len() != rec.base.level_params.len() {
            return Ok(None);
        }
        let mut rhs =
            self.instantiate_lparams(&rule.rhs, &rec.base.level_params, &levels, depth + 1)?;
        // Params, motives, and minors come from the recursor application (the
        // indices are consumed by the motive, never applied to the rule).
        let from_rec = (rec.num_params + rec.num_motives + rec.num_minors) as usize;
        for arg in rec_args.iter().take(from_rec) {
            rhs = Expr::app(rhs, arg.clone());
        }
        // The constructor's parameter count can differ from the recursor's under
        // nested inductives: the fields are always the LAST `nfields` arguments.
        for field in &major_args[major_args.len() - nfields..] {
            rhs = Expr::app(rhs, field.clone());
        }
        for extra in &rec_args[major_idx + 1..] {
            rhs = Expr::app(rhs, extra.clone());
        }
        Ok(Some(rhs))
    }

    /// `recursor_val::get_major_induct` (declaration.cpp:145): walk `major_idx`
    /// binders of the recursor's type; the next binder's domain head names the
    /// inductive of the major premise.
    fn recursor_major_induct(&mut self, rec: &RecursorVal, depth: u32) -> KResult<Option<Name>> {
        let major_idx = rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices;
        let mut telescope = rec.base.type_.clone();
        for _ in 0..major_idx {
            self.step(depth)?;
            let ExprNode::ForallE { body, .. } = telescope.node() else {
                return Ok(None);
            };
            telescope = body.clone();
        }
        let ExprNode::ForallE { binder_type, .. } = telescope.node() else {
            return Ok(None);
        };
        let (head, _) = app_spine(binder_type);
        match head.node() {
            ExprNode::Const { name, .. } => Ok(Some(name.clone())),
            _ => Ok(None),
        }
    }

    /// KR-317 (`to_cnstr_when_K`): a K-flagged recursor replaces any major
    /// premise whose (whnf'd, inferred) type has the recursor's inductive at its
    /// head with the nullary constructor of that type — gated on the constructed
    /// term's type being defeq to the major's. Any gate failure returns the
    /// original major unchanged (reduction without matching the syntactic proof).
    fn major_to_cnstr_when_k(
        &mut self,
        rec: &RecursorVal,
        major: &Expr,
        depth: u32,
    ) -> KResult<Expr> {
        let Some(major_induct) = self.recursor_major_induct(rec, depth)? else {
            return Ok(major.clone());
        };
        let app_type = match self.infer(major, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(major.clone()),
            Err(stop) => return Err(stop),
        };
        let app_type = self.whnf(&app_type, depth + 1)?;
        let (type_head, type_args) = app_spine(&app_type);
        let ExprNode::Const {
            name: type_name,
            levels: type_levels,
        } = type_head.node()
        else {
            return Ok(major.clone());
        };
        if type_name != &major_induct {
            return Ok(major.clone());
        }
        // `mk_nullary_cnstr`: the FIRST constructor, applied to the type's params.
        let ctor_name = match self.env.find(type_name) {
            Some(ConstantInfo::Induct(ind)) => match ind.ctors.first() {
                Some(ctor_name) => ctor_name.clone(),
                None => return Ok(major.clone()),
            },
            _ => return Ok(major.clone()),
        };
        let mut new_ctor = Expr::const_(ctor_name, type_levels.clone());
        for arg in type_args.iter().take(rec.num_params as usize) {
            new_ctor = Expr::app(new_ctor, arg.clone());
        }
        let new_type = match self.infer(&new_ctor, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(major.clone()),
            Err(stop) => return Err(stop),
        };
        if !self.is_def_eq(&app_type, &new_type, depth + 1)? {
            return Ok(major.clone());
        }
        Ok(new_ctor)
    }

    /// KR-316's structure-eta coercion (`to_cnstr_when_structure`): a major of a
    /// one-constructor, index-free, non-recursive, non-Prop structure type that
    /// is not already a constructor application becomes
    /// `mk params (proj 0 major) … (proj n-1 major)`. Any gate failure returns
    /// the original major unchanged.
    fn major_to_cnstr_when_structure(
        &mut self,
        rec: &RecursorVal,
        major: &Expr,
        depth: u32,
    ) -> KResult<Expr> {
        let Some(induct_name) = self.recursor_major_induct(rec, depth)? else {
            return Ok(major.clone());
        };
        if !self.is_non_rec_structure(&induct_name) {
            return Ok(major.clone());
        }
        let (major_head, _) = app_spine(major);
        if let ExprNode::Const { name, .. } = major_head.node()
            && matches!(self.env.find(name), Some(ConstantInfo::Ctor(_)))
        {
            return Ok(major.clone());
        }
        let e_type = match self.infer(major, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(major.clone()),
            Err(stop) => return Err(stop),
        };
        let e_type = self.whnf(&e_type, depth + 1)?;
        let (type_head, type_args) = app_spine(&e_type);
        let ExprNode::Const {
            name: type_name,
            levels: type_levels,
        } = type_head.node()
        else {
            return Ok(major.clone());
        };
        if type_name != &induct_name {
            return Ok(major.clone());
        }
        // Prop-valued structures are excluded (proof irrelevance covers them).
        let type_sort = match self.infer(&e_type, depth) {
            Ok(sort) => sort,
            Err(Stop::Reject(..)) => return Ok(major.clone()),
            Err(stop) => return Err(stop),
        };
        let type_sort = self.whnf(&type_sort, depth + 1)?;
        if matches!(type_sort.node(), ExprNode::Sort { level } if level.is_equiv(&Level::zero())) {
            return Ok(major.clone());
        }
        // `expand_eta_struct`: ctor params from the type, then one proj per field.
        let (ctor_name, ctor_num_params, num_fields) = {
            let ctor_name = match self.env.find(&induct_name) {
                Some(ConstantInfo::Induct(ind)) => match ind.ctors.first() {
                    Some(ctor_name) => ctor_name.clone(),
                    None => return Ok(major.clone()),
                },
                _ => return Ok(major.clone()),
            };
            match self.env.find(&ctor_name) {
                Some(ConstantInfo::Ctor(ctor)) => (
                    ctor_name,
                    ctor.num_params as usize,
                    u64::from(ctor.num_fields),
                ),
                _ => return Ok(major.clone()),
            }
        };
        let mut expanded = Expr::const_(ctor_name, type_levels.clone());
        for arg in type_args.iter().take(ctor_num_params) {
            expanded = Expr::app(expanded, arg.clone());
        }
        for i in 0..num_fields {
            expanded = Expr::app(expanded, Expr::proj(induct_name.clone(), i, major.clone()));
        }
        Ok(expanded)
    }

    // ---- defeq (KR-300..312 subset) ----------------------------------------------------

    /// KR-301/302/303 — the decisive head rules, extracted so they can re-run
    /// on the REDUCED pair after every reduction stage (the pin re-runs its
    /// quick check after whnf_core and inside every lazy-delta iteration; a
    /// pair that only becomes Sort ≟ Sort or binder ≟ binder after reduction
    /// must not fall through to rules that cannot decide it). `None` = this
    /// pair's heads are not covered here — continue down the ladder.
    fn quick_def_eq_rules(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<Option<bool>> {
        // KR-301 quick structural equality (data-word fast path inside Expr::eq).
        if t == s {
            return Ok(Some(true));
        }
        // KR-301's literal half (pin quick_is_def_eq, Lit case): a literal pair
        // decides by value — and DECISIVELY, since two distinct literals are
        // both normal forms no later rule can equate.
        if let (ExprNode::Lit { literal: l1 }, ExprNode::Lit { literal: l2 }) = (t.node(), s.node())
        {
            return Ok(Some(l1 == l2));
        }
        // KR-303 sorts by level equivalence.
        if let (ExprNode::Sort { level: lt }, ExprNode::Sort { level: ls }) = (t.node(), s.node()) {
            return Ok(Some(lt.is_equiv(ls)));
        }
        // KR-302 binder congruence.
        match (t.node(), s.node()) {
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
            ) => {
                let (t1, b1, t2, b2) = (t1.clone(), b1.clone(), t2.clone(), b2.clone());
                if !self.is_def_eq(&t1, &t2, depth + 1)? {
                    return Ok(Some(false));
                }
                let id = self.fresh_fvar(t1, None);
                let ob1 = self.open_binder(&b1, &id, depth + 1)?;
                let ob2 = self.open_binder(&b2, &id, depth + 1)?;
                let result = self.is_def_eq(&ob1, &ob2, depth + 1);
                self.drop_local();
                Ok(Some(result?))
            }
            _ => Ok(None),
        }
    }

    fn is_def_eq(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        self.step(depth)?; // KR-300 resource hook
        if let Some(decided) = self.quick_def_eq_rules(t, s, depth)? {
            return Ok(decided);
        }
        // KR-313's reflection fast path (pin type_checker.cpp:1062): `t` closed
        // and `s` literally `Bool.true` — fully reduce `t` and compare. This is
        // how `decide`-style proofs (`Eq.refl true : decide p = true`) close.
        // One-sided at the pin; the symmetric case still closes through delta.
        if !t.has_fvar()
            && matches!(s.node(), ExprNode::Const { name, .. } if is_name2(name, "Bool", "true"))
        {
            let reduced = self.whnf(t, depth + 1)?;
            if matches!(reduced.node(), ExprNode::Const { name, .. } if is_name2(name, "Bool", "true"))
            {
                return Ok(true);
            }
        }
        // KR-305: normalize both sides without delta, then RE-RUN the head
        // rules on the reduced pair (beta/zeta/iota can expose Sort or binder
        // heads whose levels are equivalent but not structurally equal).
        let tn = self.whnf_core(t, depth + 1)?;
        let sn = self.whnf_core(s, depth + 1)?;
        if (tn != *t || sn != *s)
            && let Some(decided) = self.quick_def_eq_rules(&tn, &sn, depth)?
        {
            return Ok(decided);
        }
        // KR-306 definitional proof irrelevance in Prop.
        if self.proof_irrel_eq(&tn, &sn, depth + 1)? {
            return Ok(true);
        }
        // KR-307/309 lazy delta by definitional height — with the KR-313 offset
        // and literal-arithmetic machinery woven into every iteration, as at
        // the pin — then the head rules once more: delta is exactly how an
        // abbrev (`outParam`, `ReaderT`, `Not`) exposes its Sort or Π structure.
        let (tn, sn) = match self.lazy_delta(tn, sn, depth + 1)? {
            LazyDelta::Decided(decided) => return Ok(decided),
            LazyDelta::Stuck(t, s) => (t, s),
        };
        if let Some(decided) = self.quick_def_eq_rules(&tn, &sn, depth)? {
            return Ok(decided);
        }
        // KR-310: same-name constants with equivalent levels.
        if let (
            ExprNode::Const {
                name: n1,
                levels: l1,
            },
            ExprNode::Const {
                name: n2,
                levels: l2,
            },
        ) = (tn.node(), sn.node())
            && n1 == n2
            && l1.len() == l2.len()
            && l1.iter().zip(l2).all(|(a, b)| a.is_equiv(b))
        {
            return Ok(true);
        }
        // KR-311 application congruence.
        if let (ExprNode::App { f: f1, a: a1 }, ExprNode::App { f: f2, a: a2 }) =
            (tn.node(), sn.node())
        {
            let (f1, a1, f2, a2) = (f1.clone(), a1.clone(), f2.clone(), a2.clone());
            if self.is_def_eq(&f1, &f2, depth + 1)? && self.is_def_eq(&a1, &a2, depth + 1)? {
                return Ok(true);
            }
        }
        // KR-312 function eta, both directions.
        if self.try_eta(&tn, &sn, depth + 1)? || self.try_eta(&sn, &tn, depth + 1)? {
            return Ok(true);
        }
        // KR-903 structure eta, both directions (pin: try_eta_struct).
        if self.try_eta_struct(&tn, &sn, depth + 1)? || self.try_eta_struct(&sn, &tn, depth + 1)? {
            return Ok(true);
        }
        // KR-314 defeq half (pin try_string_lit_expansion, type_checker.cpp:1030):
        // a String literal against a `String.ofList _` spine — decisive when the
        // shape matches, either side.
        if let Some(decided) = self.try_string_lit_expansion(&tn, &sn, depth + 1)? {
            return Ok(decided);
        }
        // KR-315 unit-like structures (pin: is_def_eq_unit_like, one-sided).
        if self.is_def_eq_unit_like(&tn, &sn, depth + 1)? {
            return Ok(true);
        }
        Ok(false)
    }

    /// Is `name` a one-constructor, index-free, non-recursive structure?
    /// (pin: `is_non_rec_structure`, inductive.cpp:27.)
    fn is_non_rec_structure(&self, name: &Name) -> bool {
        matches!(
            self.env.find(name),
            Some(ConstantInfo::Induct(ind))
                if ind.ctors.len() == 1 && ind.num_indices == 0 && !ind.is_rec
        )
    }

    /// KR-903 (`try_eta_struct_core`): `t ≟ mk as fs` for a one-constructor,
    /// index-free, non-recursive structure holds when the types agree and
    /// every field `fᵢ` of `s` is defeq to `t.i`. The type-agreement gate is
    /// load-bearing: without it a zero-field constructor would equate values
    /// of DIFFERENT unit-like types.
    fn try_eta_struct(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        self.step(depth)?;
        let (s_head, s_args) = app_spine(s);
        let ExprNode::Const {
            name: ctor_name, ..
        } = s_head.node()
        else {
            return Ok(false);
        };
        let (induct, num_params, num_fields) = match self.env.find(ctor_name) {
            Some(ConstantInfo::Ctor(ctor)) => (
                ctor.induct.clone(),
                ctor.num_params as usize,
                ctor.num_fields as usize,
            ),
            _ => return Ok(false),
        };
        if s_args.len() != num_params + num_fields || !self.is_non_rec_structure(&induct) {
            return Ok(false);
        }
        let t_type = match self.infer(t, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        let s_type = match self.infer(s, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        if !self.is_def_eq(&t_type, &s_type, depth + 1)? {
            return Ok(false);
        }
        for (i, field) in s_args.iter().enumerate().skip(num_params) {
            let projected = Expr::proj(induct.clone(), (i - num_params) as u64, t.clone());
            if !self.is_def_eq(&projected, field, depth + 1)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// KR-315 (`is_def_eq_unit_like`): two terms of the same one-constructor,
    /// ZERO-field structure type are defeq when their types are. One-sided,
    /// as at the pin — full whnf of `t`'s type unfolds any abbrev first.
    fn is_def_eq_unit_like(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        let t_type = match self.infer(t, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        let t_type = self.whnf(&t_type, depth + 1)?;
        let (type_head, _) = app_spine(&t_type);
        let ExprNode::Const { name, .. } = type_head.node() else {
            return Ok(false);
        };
        if !self.is_non_rec_structure(name) {
            return Ok(false);
        }
        let zero_fields = match self.env.find(name) {
            Some(ConstantInfo::Induct(ind)) => match ind.ctors.first() {
                Some(ctor_name) => matches!(
                    self.env.find(ctor_name),
                    Some(ConstantInfo::Ctor(ctor)) if ctor.num_fields == 0
                ),
                None => false,
            },
            _ => false,
        };
        if !zero_fields {
            return Ok(false);
        }
        let s_type = match self.infer(s, depth) {
            Ok(type_) => type_,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        self.is_def_eq(&t_type, &s_type, depth + 1)
    }

    /// KR-306: if `t`'s type is a Prop, t ≟ s reduces to type-defeq.
    fn proof_irrel_eq(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        let t_type = match self.infer(t, depth) {
            Ok(ty) => ty,
            // A term that fails to type here cannot claim irrelevance; let the
            // main ladder produce the real verdict.
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        if !self.is_prop(&t_type, depth)? {
            return Ok(false);
        }
        let s_type = match self.infer(s, depth) {
            Ok(ty) => ty,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        self.is_def_eq(&t_type, &s_type, depth)
    }

    /// Is `type_` a proposition — i.e., does it live in `Sort 0`? (The pin's
    /// `is_prop(e)` = `whnf(infer_type(e)) == Prop`.)
    fn is_prop(&mut self, type_: &Expr, depth: u32) -> KResult<bool> {
        let sort = self.infer_core(type_, depth)?;
        let sort = self.whnf(&sort, depth)?;
        Ok(matches!(sort.node(), ExprNode::Sort { level } if level.is_equiv(&Level::zero())))
    }

    /// KR-309: unfold the taller definition first; equal heights unfold both —
    /// with the pin's per-iteration literal machinery (`lazy_delta_reduction`,
    /// type_checker.cpp:973): the KR-313 offset check and, on closed pairs,
    /// literal arithmetic on either side run BEFORE every unfold step, so a
    /// side that delta-exposes a literal (the decoded `OfNat.ofNat … ≟
    /// Nat.zero` residual family) decides here instead of falling through.
    fn lazy_delta(&mut self, mut t: Expr, mut s: Expr, depth: u32) -> KResult<LazyDelta> {
        loop {
            self.step(depth)?;
            if let Some(decided) = self.is_def_eq_offset(&t, &s, depth)? {
                return Ok(LazyDelta::Decided(decided));
            }
            if !t.has_fvar() && !s.has_fvar() {
                if let Some(value) = self.reduce_nat(&t, depth)? {
                    return Ok(LazyDelta::Decided(self.is_def_eq(&value, &s, depth + 1)?));
                }
                if let Some(value) = self.reduce_nat(&s, depth)? {
                    return Ok(LazyDelta::Decided(self.is_def_eq(&t, &value, depth + 1)?));
                }
            }
            // (`reduce_native` would run here at the pin — native_decide
            // surface, follow-up slice; omission only under-reduces.)
            let ht = self.definition_height(&t);
            let hs = self.definition_height(&s);
            match (ht, hs) {
                (None, None) => return Ok(LazyDelta::Stuck(t, s)),
                (Some(_), None) => match self.unfold_definition(&t, depth)? {
                    Some(next) => t = self.whnf_core(&next, depth)?,
                    None => return Ok(LazyDelta::Stuck(t, s)),
                },
                (None, Some(_)) => match self.unfold_definition(&s, depth)? {
                    Some(next) => s = self.whnf_core(&next, depth)?,
                    None => return Ok(LazyDelta::Stuck(t, s)),
                },
                (Some(a), Some(b)) => {
                    if a >= b {
                        match self.unfold_definition(&t, depth)? {
                            Some(next) => t = self.whnf_core(&next, depth)?,
                            None => return Ok(LazyDelta::Stuck(t, s)),
                        }
                    }
                    if b >= a {
                        match self.unfold_definition(&s, depth)? {
                            Some(next) => s = self.whnf_core(&next, depth)?,
                            None => return Ok(LazyDelta::Stuck(t, s)),
                        }
                    }
                    if t == s {
                        return Ok(LazyDelta::Stuck(t, s));
                    }
                }
            }
        }
    }

    /// `is_def_eq_offset` (pin type_checker.cpp:961): both sides Nat-zero
    /// (`Nat.zero` or literal `0`) — defeq; both `succ`-peelable (a positive
    /// literal peels to its predecessor literal, `Nat.succ x` peels to `x`) —
    /// defeq of the predecessors, decisively. `None`: not an offset pair.
    fn is_def_eq_offset(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<Option<bool>> {
        if is_nat_zero_expr(t) && is_nat_zero_expr(s) {
            return Ok(Some(true));
        }
        match (nat_succ_peel(t), nat_succ_peel(s)) {
            (Some(pt), Some(ps)) => Ok(Some(self.is_def_eq(&pt, &ps, depth + 1)?)),
            _ => Ok(None),
        }
    }

    /// KR-314 defeq half (`try_string_lit_expansion`, pin type_checker.cpp:1030):
    /// tries both orientations of literal-vs-`String.ofList` spine.
    fn try_string_lit_expansion(
        &mut self,
        t: &Expr,
        s: &Expr,
        depth: u32,
    ) -> KResult<Option<bool>> {
        if let Some(decided) = self.try_string_lit_expansion_core(t, s, depth)? {
            return Ok(Some(decided));
        }
        self.try_string_lit_expansion_core(s, t, depth)
    }

    /// One orientation: `t` a String literal, `s` exactly `String.ofList _`
    /// (a one-argument application of the levels-free constant, as the pin's
    /// whole-expression comparison against `g_string_mk` requires). Expands the
    /// literal (whnf'd, so `ofList` unfolds to the real constructor) and
    /// recurses; the answer is decisive.
    fn try_string_lit_expansion_core(
        &mut self,
        t: &Expr,
        s: &Expr,
        depth: u32,
    ) -> KResult<Option<bool>> {
        let ExprNode::Lit {
            literal: Literal::Str(value),
        } = t.node()
        else {
            return Ok(None);
        };
        let ExprNode::App { f, .. } = s.node() else {
            return Ok(None);
        };
        let ExprNode::Const { name, levels } = f.node() else {
            return Ok(None);
        };
        if !levels.is_empty() || !is_name2(name, "String", "ofList") {
            return Ok(None);
        }
        let expanded = self.whnf(&string_lit_to_constructor(value), depth + 1)?;
        Ok(Some(self.is_def_eq(&expanded, s, depth + 1)?))
    }

    /// KR-312 (function half): `t` a lambda, `s` not — eta-expand `s` through its
    /// Π-type and retry.
    fn try_eta(&mut self, t: &Expr, s: &Expr, depth: u32) -> KResult<bool> {
        if !matches!(t.node(), ExprNode::Lam { .. }) || matches!(s.node(), ExprNode::Lam { .. }) {
            return Ok(false);
        }
        let s_type = match self.infer(s, depth) {
            Ok(ty) => ty,
            Err(Stop::Reject(..)) => return Ok(false),
            Err(stop) => return Err(stop),
        };
        let s_type = self.whnf(&s_type, depth)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            binder_info,
            ..
        } = s_type.node()
        else {
            return Ok(false);
        };
        let expanded = Expr::lam(
            binder_name.clone(),
            binder_type.clone(),
            Expr::app(s.clone(), Expr::bvar(0).unwrap_or_else(|_| s.clone())),
            *binder_info,
        );
        self.is_def_eq(t, &expanded, depth)
    }

    // ---- typing (KR-100..112) ----------------------------------------------------------

    pub(crate) fn infer(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.step(depth)?;
        // KR-100: closed terms only.
        if e.has_loose_bvars() {
            return reject(
                RejectClass::LooseBVar,
                "kernel terms must be closed; replace loose bound variables with free variables",
            );
        }
        // KR-103: no metavariables.
        if e.has_expr_mvar() || e.has_level_mvar() {
            return reject(
                RejectClass::MVarInKernel,
                "kernel does not accept metavariables",
            );
        }
        self.infer_core(e, depth)
    }

    fn infer_core(&mut self, e: &Expr, depth: u32) -> KResult<Expr> {
        self.step(depth)?;
        match e.node() {
            // KR-101: unreachable given the closed-term precondition; still a typed
            // rejection, never a panic.
            ExprNode::BVar { .. } => reject(
                RejectClass::LooseBVar,
                "bound variable escaped the binder telescope",
            ),
            ExprNode::MVar { .. } => {
                reject(RejectClass::MVarInKernel, "metavariable in kernel term")
            }
            // KR-102.
            ExprNode::FVar { id } => match self.find_local(id) {
                Some(decl) => Ok(decl.type_.clone()),
                None => reject(RejectClass::UnknownFVar, "unknown free variable"),
            },
            // KR-104.
            ExprNode::Sort { level } => {
                self.check_level(level)?;
                Ok(Expr::sort(
                    level
                        .clone()
                        .succ()
                        .map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?,
                ))
            }
            // KR-105.
            ExprNode::Const { name, levels } => {
                let Some(info) = self.env.find(name) else {
                    return reject(
                        RejectClass::UnknownConstant,
                        format!("unknown constant `{}`", name.to_display_string()),
                    );
                };
                let params = &info.constant_val().level_params;
                if params.len() != levels.len() {
                    return reject(
                        RejectClass::UniverseArityMismatch,
                        format!(
                            "`{}` expects {} universe level(s), given {}",
                            name.to_display_string(),
                            params.len(),
                            levels.len()
                        ),
                    );
                }
                for level in levels {
                    self.check_level(level)?;
                }
                let params = params.clone();
                let type_ = info.constant_val().type_.clone();
                let levels = levels.clone();
                self.instantiate_lparams(&type_, &params, &levels, depth + 1)
            }
            // KR-106 (checking mode).
            ExprNode::App { f, a } => {
                let (f, a) = (f.clone(), a.clone());
                let f_type = self.infer_core(&f, depth + 1)?;
                let f_type = self.whnf(&f_type, depth + 1)?;
                let ExprNode::ForallE {
                    binder_type, body, ..
                } = f_type.node()
                else {
                    return reject(RejectClass::FunctionExpected, "function expected");
                };
                let (binder_type, body) = (binder_type.clone(), body.clone());
                let a_type = self.infer_core(&a, depth + 1)?;
                if !self.is_def_eq(&a_type, &binder_type, depth + 1)? {
                    return reject(
                        RejectClass::TypeMismatch,
                        format!(
                            "application type mismatch: argument `{}` has type `{}` but the function expects `{}`",
                            brief_expr(&a, 4),
                            brief_expr(&a_type, 5),
                            brief_expr(&binder_type, 5)
                        ),
                    );
                }
                self.instantiate(&body, 0, &a, depth + 1)
            }
            // KR-107.
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (binder_name, binder_type, body, binder_info) = (
                    binder_name.clone(),
                    binder_type.clone(),
                    body.clone(),
                    *binder_info,
                );
                self.ensure_sort_of(&binder_type, depth + 1)?;
                let id = self.fresh_fvar(binder_type.clone(), None);
                let opened = self.open_binder(&body, &id, depth + 1)?;
                let body_type = self.infer_core(&opened, depth + 1);
                let body_type = match body_type {
                    Ok(ty) => ty,
                    Err(stop) => {
                        self.drop_local();
                        return Err(stop);
                    }
                };
                let abstracted = self.abstract_fvar(&body_type, &id, depth + 1);
                self.drop_local();
                Ok(Expr::forall_e(
                    binder_name,
                    binder_type,
                    abstracted?,
                    binder_info,
                ))
            }
            // KR-108: the imax rule.
            ExprNode::ForallE {
                binder_type, body, ..
            } => {
                let (binder_type, body) = (binder_type.clone(), body.clone());
                let dom_level = self.ensure_sort_of(&binder_type, depth + 1)?;
                let id = self.fresh_fvar(binder_type, None);
                let opened = self.open_binder(&body, &id, depth + 1)?;
                let cod = self.infer_core(&opened, depth + 1);
                let cod = match cod {
                    Ok(c) => c,
                    Err(stop) => {
                        self.drop_local();
                        return Err(stop);
                    }
                };
                let cod_sorted = self.whnf(&cod, depth + 1);
                self.drop_local();
                let cod_sorted = cod_sorted?;
                let ExprNode::Sort { level: cod_level } = cod_sorted.node() else {
                    return reject(RejectClass::SortExpected, "Π codomain is not a sort");
                };
                let level = Level::imax(dom_level, cod_level.clone())
                    .map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?;
                Ok(Expr::sort(level))
            }
            // KR-109.
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                let (type_, value, body) = (type_.clone(), value.clone(), body.clone());
                self.ensure_sort_of(&type_, depth + 1)?;
                let value_type = self.infer_core(&value, depth + 1)?;
                if !self.is_def_eq(&value_type, &type_, depth + 1)? {
                    return reject(RejectClass::TypeMismatch, "let value type mismatch");
                }
                let id = self.fresh_fvar(type_, Some(value));
                let opened = self.open_binder(&body, &id, depth + 1)?;
                let body_type = self.infer_core(&opened, depth + 1);
                let body_type = match body_type {
                    Ok(ty) => ty,
                    Err(stop) => {
                        self.drop_local();
                        return Err(stop);
                    }
                };
                // The bootstrap returns the body type with the let-local zeta-expanded
                // out (sound: the local's value is definitionally fixed).
                let result = self.abstract_replace_value(&body_type, &id, depth + 1);
                self.drop_local();
                result
            }
            // KR-110.
            ExprNode::Lit { literal } => Ok(Expr::const_(
                Name::str(
                    Name::anonymous(),
                    match literal {
                        fln_core::expr::Literal::Nat(_) => "Nat",
                        fln_core::expr::Literal::Str(_) => "String",
                    },
                ),
                Vec::new(),
            )),
            // KR-111.
            ExprNode::MData { expr, .. } => {
                let expr = expr.clone();
                self.infer_core(&expr, depth + 1)
            }
            // KR-112 (+ KR-901 Prop guard).
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let (struct_name, idx, scrutinee) = (struct_name.clone(), *idx, expr.clone());
                self.infer_proj(&struct_name, idx, &scrutinee, depth + 1)
            }
        }
    }

    fn check_level(&self, level: &Level) -> KResult<()> {
        // KR-140-class: every named parameter must be declared.
        let mut undeclared = None;
        collect_undeclared_param(level, self.lparams, &mut undeclared);
        match undeclared {
            Some(name) => reject(
                RejectClass::UndefinedLevelParam,
                format!(
                    "undefined universe level parameter `{}`",
                    name.to_display_string()
                ),
            ),
            None => Ok(()),
        }
    }

    /// whnf the type of `e`'s sort-hood: returns the sort level or rejects.
    fn ensure_sort_of(&mut self, e: &Expr, depth: u32) -> KResult<Level> {
        let type_ = self.infer_core(e, depth)?;
        let sorted = self.whnf(&type_, depth)?;
        match sorted.node() {
            ExprNode::Sort { level } => Ok(level.clone()),
            _ => reject(RejectClass::SortExpected, "type expected (not a sort)"),
        }
    }

    /// Close over one fvar: replace it by `bvar 0`, lifting existing loose bvars.
    /// Bootstrap restriction: the types produced by this slice's inference never
    /// contain loose bvars at abstraction time (bodies were opened first), so the
    /// rebuild is a straight replacement.
    fn abstract_fvar(&mut self, e: &Expr, id: &FVarId, depth: u32) -> KResult<Expr> {
        self.step(depth)?;
        if !e.has_fvar() {
            return Ok(e.clone());
        }
        Ok(match e.node() {
            ExprNode::FVar { id: found } if found == id => {
                Expr::bvar(0).unwrap_or_else(|_| e.clone())
            }
            ExprNode::App { f, a } => {
                let f2 = self.abstract_fvar(f, id, depth + 1)?;
                let a2 = self.abstract_fvar(a, id, depth + 1)?;
                Expr::app(f2, a2)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.abstract_fvar(binder_type, id, depth + 1)?;
                let b2 = self.abstract_shifted(body, id, 1, depth + 1)?;
                Expr::lam(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.abstract_fvar(binder_type, id, depth + 1)?;
                let b2 = self.abstract_shifted(body, id, 1, depth + 1)?;
                Expr::forall_e(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.abstract_fvar(type_, id, depth + 1)?;
                let v2 = self.abstract_fvar(value, id, depth + 1)?;
                let b2 = self.abstract_shifted(body, id, 1, depth + 1)?;
                Expr::let_e(decl_name.clone(), t2, v2, b2, *non_dep)
            }
            ExprNode::MData { data, expr } => {
                let inner = self.abstract_fvar(expr, id, depth + 1)?;
                Expr::mdata(data.clone(), inner)
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let inner = self.abstract_fvar(expr, id, depth + 1)?;
                Expr::proj(struct_name.clone(), *idx, inner)
            }
            _ => e.clone(),
        })
    }

    fn abstract_shifted(&mut self, e: &Expr, id: &FVarId, at: u32, depth: u32) -> KResult<Expr> {
        self.step(depth)?;
        if !e.has_fvar() {
            return Ok(e.clone());
        }
        Ok(match e.node() {
            ExprNode::FVar { id: found } if found == id => {
                Expr::bvar(at).map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?
            }
            ExprNode::App { f, a } => {
                let f2 = self.abstract_shifted(f, id, at, depth + 1)?;
                let a2 = self.abstract_shifted(a, id, at, depth + 1)?;
                Expr::app(f2, a2)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.abstract_shifted(binder_type, id, at, depth + 1)?;
                let b2 = self.abstract_shifted(body, id, at + 1, depth + 1)?;
                Expr::lam(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.abstract_shifted(binder_type, id, at, depth + 1)?;
                let b2 = self.abstract_shifted(body, id, at + 1, depth + 1)?;
                Expr::forall_e(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.abstract_shifted(type_, id, at, depth + 1)?;
                let v2 = self.abstract_shifted(value, id, at, depth + 1)?;
                let b2 = self.abstract_shifted(body, id, at + 1, depth + 1)?;
                Expr::let_e(decl_name.clone(), t2, v2, b2, *non_dep)
            }
            ExprNode::MData { data, expr } => {
                let inner = self.abstract_shifted(expr, id, at, depth + 1)?;
                Expr::mdata(data.clone(), inner)
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let inner = self.abstract_shifted(expr, id, at, depth + 1)?;
                Expr::proj(struct_name.clone(), *idx, inner)
            }
            _ => e.clone(),
        })
    }

    /// For let-bodies: substitute the let-local's VALUE for the fvar (zeta on the
    /// type level), so the returned type is closed without a synthetic binder.
    fn abstract_replace_value(&mut self, e: &Expr, id: &FVarId, depth: u32) -> KResult<Expr> {
        let value = self
            .find_local(id)
            .and_then(|d| d.value.clone())
            .unwrap_or_else(|| Expr::fvar(id.clone()));
        self.replace_fvar(e, id, &value, depth)
    }

    fn replace_fvar(&mut self, e: &Expr, id: &FVarId, with: &Expr, depth: u32) -> KResult<Expr> {
        self.step(depth)?;
        if !e.has_fvar() {
            return Ok(e.clone());
        }
        Ok(match e.node() {
            ExprNode::FVar { id: found } if found == id => with.clone(),
            ExprNode::App { f, a } => {
                let f2 = self.replace_fvar(f, id, with, depth + 1)?;
                let a2 = self.replace_fvar(a, id, with, depth + 1)?;
                Expr::app(f2, a2)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.replace_fvar(binder_type, id, with, depth + 1)?;
                let b2 = self.replace_fvar(body, id, with, depth + 1)?;
                Expr::lam(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.replace_fvar(binder_type, id, with, depth + 1)?;
                let b2 = self.replace_fvar(body, id, with, depth + 1)?;
                Expr::forall_e(binder_name.clone(), t2, b2, *binder_info)
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.replace_fvar(type_, id, with, depth + 1)?;
                let v2 = self.replace_fvar(value, id, with, depth + 1)?;
                let b2 = self.replace_fvar(body, id, with, depth + 1)?;
                Expr::let_e(decl_name.clone(), t2, v2, b2, *non_dep)
            }
            ExprNode::MData { data, expr } => {
                let inner = self.replace_fvar(expr, id, with, depth + 1)?;
                Expr::mdata(data.clone(), inner)
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let inner = self.replace_fvar(expr, id, with, depth + 1)?;
                Expr::proj(struct_name.clone(), *idx, inner)
            }
            _ => e.clone(),
        })
    }

    /// KR-112 + KR-901.
    fn infer_proj(
        &mut self,
        struct_name: &Name,
        idx: u64,
        scrutinee: &Expr,
        depth: u32,
    ) -> KResult<Expr> {
        let s_type = self.infer_core(scrutinee, depth)?;
        let s_type = self.whnf(&s_type, depth)?;
        let mut args: Vec<Expr> = Vec::new();
        let mut head = s_type.clone();
        while let ExprNode::App { f, a } = head.node() {
            args.push(a.clone());
            let next = f.clone();
            head = next;
        }
        args.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return reject(
                RejectClass::InvalidProjection,
                "projection of a non-structure",
            );
        };
        if name != struct_name {
            return reject(
                RejectClass::InvalidProjection,
                "projection structure mismatch",
            );
        }
        let Some(ConstantInfo::Induct(ind)) = self.env.find(name) else {
            return reject(
                RejectClass::InvalidProjection,
                "projection of a non-inductive",
            );
        };
        if ind.ctors.len() != 1 || args.len() != (ind.num_params + ind.num_indices) as usize {
            return reject(
                RejectClass::InvalidProjection,
                "projections require a one-constructor structure with exact arity",
            );
        }
        let ctor_name = ind.ctors.first().cloned().unwrap_or_else(Name::anonymous);
        let Some(ConstantInfo::Ctor(ctor)) = self.env.find(&ctor_name) else {
            return reject(
                RejectClass::InvalidProjection,
                "structure constructor missing",
            );
        };
        let is_prop_type = {
            let s_sort = self.infer_core(&s_type, depth)?;
            let s_sort = self.whnf(&s_sort, depth)?;
            matches!(s_sort.node(), ExprNode::Sort { level } if level.is_equiv(&Level::zero()))
        };
        // Walk the constructor telescope: instantiate params, then peel idx fields.
        let ctor_params = ctor.base.level_params.clone();
        let levels = levels.clone();
        let mut telescope =
            self.instantiate_lparams(&ctor.base.type_.clone(), &ctor_params, &levels, depth)?;
        for arg in args.iter().take(ctor.num_params as usize) {
            let ExprNode::ForallE { body, .. } = telescope.node() else {
                return reject(RejectClass::InvalidProjection, "constructor arity mismatch");
            };
            let body = body.clone();
            telescope = self.instantiate(&body, 0, arg, depth)?;
        }
        for i in 0..idx {
            let ExprNode::ForallE {
                binder_type, body, ..
            } = telescope.node()
            else {
                return reject(
                    RejectClass::InvalidProjection,
                    "projection index out of range",
                );
            };
            if is_prop_type && !self.is_prop(&binder_type.clone(), depth)? {
                return reject(
                    RejectClass::InvalidProjection,
                    "projection would leak data out of Prop",
                );
            }
            let body = body.clone();
            let earlier = Expr::proj(struct_name.clone(), i, scrutinee.clone());
            telescope = self.instantiate(&body, 0, &earlier, depth)?;
        }
        let ExprNode::ForallE { binder_type, .. } = telescope.node() else {
            return reject(
                RejectClass::InvalidProjection,
                "projection index out of range",
            );
        };
        let result = binder_type.clone();
        if is_prop_type && !self.is_prop(&result, depth)? {
            return reject(
                RejectClass::InvalidProjection,
                "projection would leak data out of Prop",
            );
        }
        Ok(result)
    }
}

/// Bounded level rendering for rejection messages.
fn brief_level(level: &Level, fuel: usize) -> String {
    use fln_core::level::LevelView;
    if fuel == 0 {
        return "..".to_string();
    }
    match level.view() {
        LevelView::Zero => "0".to_string(),
        LevelView::Param(name) => name.to_display_string(),
        LevelView::MVar(_) => "mvar".to_string(),
        LevelView::Succ(inner) => format!("{}+1", brief_level(inner, fuel - 1)),
        LevelView::Max(a, b) => format!(
            "max({},{})",
            brief_level(a, fuel - 1),
            brief_level(b, fuel - 1)
        ),
        LevelView::IMax(a, b) => format!(
            "imax({},{})",
            brief_level(a, fuel - 1),
            brief_level(b, fuel - 1)
        ),
    }
}

/// Crate-facing bounded rendering (lib.rs admission messages).
pub(crate) fn brief_public(e: &Expr) -> String {
    brief_expr(e, 5)
}

/// Bounded, allocation-light term rendering for rejection MESSAGES only —
/// never part of a judgment. Fuel caps both depth and total size so adversarial
/// terms cannot blow up diagnostics (FL-INV-07 discipline extends to logs).
fn brief_expr(e: &Expr, fuel: usize) -> String {
    if fuel == 0 {
        return "..".to_string();
    }
    match e.node() {
        ExprNode::BVar { idx } => format!("#{idx}"),
        ExprNode::FVar { id } => format!("fvar:{}", id.0.to_display_string()),
        ExprNode::MVar { .. } => "mvar".to_string(),
        ExprNode::Sort { level } => format!("Sort<{}>", brief_level(level, fuel)),
        ExprNode::Const { name, levels } => {
            if levels.is_empty() {
                name.to_display_string()
            } else {
                let rendered: Vec<String> = levels.iter().map(|l| brief_level(l, fuel)).collect();
                format!("{}.{{{}}}", name.to_display_string(), rendered.join(","))
            }
        }
        ExprNode::App { .. } => {
            let (head, args) = app_spine(e);
            let mut out = format!("({}", brief_expr(&head, fuel - 1));
            for arg in &args {
                out.push(' ');
                out.push_str(&brief_expr(arg, fuel - 1));
            }
            out.push(')');
            out
        }
        ExprNode::Lam { body, .. } => format!("(fun _ => {})", brief_expr(body, fuel - 1)),
        ExprNode::ForallE {
            binder_type, body, ..
        } => format!(
            "({} -> {})",
            brief_expr(binder_type, fuel - 1),
            brief_expr(body, fuel - 1)
        ),
        ExprNode::LetE { body, .. } => format!("(let _; {})", brief_expr(body, fuel - 1)),
        ExprNode::MData { expr, .. } => brief_expr(expr, fuel),
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => format!(
            "({}.{} {})",
            struct_name.to_display_string(),
            idx,
            brief_expr(expr, fuel - 1)
        ),
        ExprNode::Lit { .. } => "lit".to_string(),
    }
}

/// Split an application spine into `(head, args-left-to-right)`.
fn app_spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args: Vec<Expr> = Vec::new();
    let mut head = e.clone();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        let next = f.clone();
        head = next;
    }
    args.reverse();
    (head, args)
}

/// `nat_lit_to_constructor` (inductive.cpp:1191): `0 ⟶ Nat.zero`,
/// `n ⟶ Nat.succ (n-1 : literal)` for `n > 0`. The decrement is a plain limb
/// borrow walk — value identity only, no bignum-arithmetic dependency.
fn nat_lit_to_constructor(value: &NatLit) -> Expr {
    let nat = Name::str(Name::anonymous(), "Nat");
    if value.to_u64() == Some(0) {
        return Expr::const_(Name::str(nat, "zero"), Vec::new());
    }
    let mut limbs = value.limbs_le().to_vec();
    for limb in limbs.iter_mut() {
        if *limb > 0 {
            *limb -= 1;
            break;
        }
        *limb = u64::MAX;
    }
    let pred = NatLit::from_limbs_le(limbs);
    Expr::app(
        Expr::const_(Name::str(nat, "succ"), Vec::new()),
        Expr::lit(Literal::Nat(pred)),
    )
}

/// Level-parameter substitution (pure, structural).
fn substitute_level(level: &Level, params: &[Name], levels: &[Level]) -> Level {
    use fln_core::level::LevelView;
    match level.view() {
        LevelView::Zero => Level::zero(),
        LevelView::Param(name) => params
            .iter()
            .position(|p| p == name)
            .and_then(|i| levels.get(i))
            .cloned()
            .unwrap_or_else(|| level.clone()),
        LevelView::Succ(inner) => substitute_level(inner, params, levels)
            .succ()
            .unwrap_or_else(|_| level.clone()),
        LevelView::Max(a, b) => Level::max(
            substitute_level(a, params, levels),
            substitute_level(b, params, levels),
        )
        .unwrap_or_else(|_| level.clone()),
        LevelView::IMax(a, b) => Level::imax(
            substitute_level(a, params, levels),
            substitute_level(b, params, levels),
        )
        .unwrap_or_else(|_| level.clone()),
        LevelView::MVar(_) => level.clone(),
    }
}

fn collect_undeclared_param(level: &Level, declared: &[Name], found: &mut Option<Name>) {
    use fln_core::level::LevelView;
    if found.is_some() || !level.has_param() {
        return;
    }
    match level.view() {
        LevelView::Param(name) => {
            if !declared.contains(name) {
                *found = Some(name.clone());
            }
        }
        LevelView::Succ(inner) => collect_undeclared_param(inner, declared, found),
        LevelView::Max(a, b) | LevelView::IMax(a, b) => {
            collect_undeclared_param(a, declared, found);
            collect_undeclared_param(b, declared, found);
        }
        _ => {}
    }
}
