//! `#reduce`'s normal form: the pin's `Meta.reduce` (vendored `src/Lean/Meta/Reduce.lean`) as
//! `elabReduce` runs it (`src/Lean/Elab/BuiltinCommand.lean:459`), at transparency `all` with
//! smart unfolding off.
//!
//! Each subterm that is neither a type nor a proof is put in weak-head normal form by the
//! unifier's reducer at [`UnificationTransparency::SafeDefinitions`], whose `reduceNat?` rung
//! folds literal arithmetic before delta, as the pin's `whnfImp` does. Then its head and its
//! explicit arguments are reduced in turn, under binders through telescopes. Where this reduction
//! stops but the pin's would go on, nothing is printed: the pin unfolds theorems at `all`, and so
//! can reduce a recursor or quotient whose major premise is a proof this reducer leaves alone.
//! Such a result is refused rather than shown as a normal form.
use super::*;
use std::collections::HashMap;

/// The pin's `maxRecDepth` default: `Meta.reduce` runs under `Core.withIncRecDepth`.
const MAX_REDUCE_DEPTH: usize = 512;

/// The `#reduce` options this engine reads (`Lean.Meta.Command.ReduceConfig`, vendored
/// `src/Init/MetaTypes.lean:469`); every other option keeps the pin's default.
#[derive(Clone, Copy, Debug, Default)]
pub(in crate::source) struct ReduceConfig {
    pub types: bool,
    pub proofs: bool,
    pub implicits: bool,
}

impl Context {
    /// The normal form `#reduce` prints for `term`.
    pub(in crate::source) fn meta_reduce(
        &mut self,
        term: &Expr,
        config: ReduceConfig,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut cache = HashMap::new();
        self.meta_reduce_visit(term, config, &mut cache, 0)
    }

    fn meta_reduce_visit(
        &mut self,
        term: &Expr,
        config: ReduceConfig,
        cache: &mut HashMap<usize, (Expr, Expr)>,
        depth: usize,
    ) -> Result<Expr, NatDefinitionElabError> {
        if depth > MAX_REDUCE_DEPTH {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        self.tick()?;
        let term = self.instantiate(term)?;
        let key = term.allocation_identity();
        if let Some((_, reduced)) = cache.get(&key) {
            return Ok(reduced.clone());
        }
        let reduced = self.meta_reduce_node(&term, config, cache, depth)?;
        // The key's allocation is held with its answer, so no other term can reuse its address.
        cache.insert(key, (term, reduced.clone()));
        Ok(reduced)
    }

    fn meta_reduce_node(
        &mut self,
        term: &Expr,
        config: ReduceConfig,
        cache: &mut HashMap<usize, (Expr, Expr)>,
        depth: usize,
    ) -> Result<Expr, NatDefinitionElabError> {
        if !config.types && self.reduce_is_type(term)? {
            return Ok(term.clone());
        }
        if !config.proofs && self.reduce_is_proof(term)? {
            return Ok(term.clone());
        }
        let term = self.meta_whnf(term)?;
        self.refuse_reduction_stuck_short(&term)?;
        match term.node() {
            ExprNode::App { .. } => {
                let (head, arguments) = operators::spine(&term);
                let head = self.meta_reduce_visit(&head, config, cache, depth + 1)?;
                let explicit = self.reduce_explicit_arguments(&head, &arguments)?;
                let mut reduced = Vec::with_capacity(arguments.len());
                for (index, argument) in arguments.iter().enumerate() {
                    self.tick()?;
                    reduced.push(
                        if config.implicits || explicit.get(index).copied().unwrap_or(true) {
                            self.meta_reduce_visit(argument, config, cache, depth + 1)?
                        } else {
                            argument.clone()
                        },
                    );
                }
                // `Nat.succ n` on a literal is the next literal.
                if matches!(head.node(), ExprNode::Const { name, .. }
                    if *name == Name::from_components(["Nat", "succ"]))
                    && let [argument] = reduced.as_slice()
                    && let ExprNode::Lit {
                        literal: Literal::Nat(value),
                    } = argument.node()
                {
                    let next = fln_bignum::nat::BigNatView::from_limbs_le(value.limbs_le())
                        .add(fln_bignum::nat::BigNatView::from_limbs_le(&[1]));
                    return Ok(Expr::lit(Literal::Nat(
                        fln_bignum::interop::literal_from_bignat(&next),
                    )));
                }
                Ok(reduced.into_iter().fold(head, Expr::app))
            }
            ExprNode::Lam { .. } | ExprNode::ForallE { .. } => {
                self.meta_reduce_binders(&term, config, cache, depth)
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                let inner = self.meta_reduce_visit(expr, config, cache, depth + 1)?;
                Ok(Expr::proj(struct_name.clone(), *idx, inner))
            }
            _ => Ok(term),
        }
    }

    /// `lambdaTelescope`/`forallTelescope`, the body reduced, then the binders closed again with
    /// their types as they were.
    fn meta_reduce_binders(
        &mut self,
        term: &Expr,
        config: ReduceConfig,
        cache: &mut HashMap<usize, (Expr, Expr)>,
        depth: usize,
    ) -> Result<Expr, NatDefinitionElabError> {
        let lambda = matches!(term.node(), ExprNode::Lam { .. });
        let saved = self.txn.lctx.clone();
        let mut binders = Vec::new();
        let mut body = term.clone();
        loop {
            self.tick()?;
            let (name, domain, inner, style) = match body.node() {
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } if lambda => (binder_name, binder_type, body, binder_info),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } if !lambda => (binder_name, binder_type, body, binder_info),
                _ => break,
            };
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_param(id.clone(), name.clone(), domain.clone(), *style);
            let opened = self.substitute(inner, &Expr::fvar(id.clone()))?;
            binders.push((id, name.clone(), domain.clone(), *style));
            body = opened;
        }
        let result = self.meta_reduce_visit(&body, config, cache, depth + 1);
        self.txn.lctx = saved;
        let mut body = result?;
        for (id, name, domain, style) in binders.into_iter().rev() {
            self.tick()?;
            body = body
                .abstract_fvar(&id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            body = if lambda {
                Expr::lam(name, domain, body, style)
            } else {
                Expr::forall_e(name, domain, body, style)
            };
        }
        Ok(body)
    }

    /// The pin's `whnf` at transparency `all`, with its literal arithmetic.
    fn meta_whnf(&mut self, term: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::SafeDefinitions;
        budget.max_steps = 10_000_000;
        let locals = self.txn.lctx.clone();
        self.txn
            .whnf_with(term, &locals, budget)
            .map_err(|error| failure(SourceInferenceError::Unification(Box::new(error))))
    }

    /// `Meta.isType`: its type's weak-head normal form is a sort.
    fn reduce_is_type(&mut self, term: &Expr) -> Result<bool, NatDefinitionElabError> {
        let type_ = self.reduce_type_of(term)?;
        Ok(matches!(self.whnf(&type_)?.node(), ExprNode::Sort { .. }))
    }

    /// `Meta.isProof`: its type's type is `Prop`.
    fn reduce_is_proof(&mut self, term: &Expr) -> Result<bool, NatDefinitionElabError> {
        let type_ = self.reduce_type_of(term)?;
        let sort = self.reduce_type_of(&type_)?;
        Ok(
            matches!(self.whnf(&sort)?.node(), ExprNode::Sort { level } if level.normalize_fixpoint().is_zero()),
        )
    }

    /// The pin's `inferType` never fails on a checked term; where this reconstruction cannot
    /// answer, reducing on would be a guess, so the query is refused.
    fn reduce_type_of(&mut self, term: &Expr) -> Result<Expr, NatDefinitionElabError> {
        self.known_type(term)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))
    }

    /// Which of `arguments` the head takes explicitly (`getFunInfoNArgs`). One past the
    /// function's arity is reduced too, as the pin reduces arguments it has no information on.
    fn reduce_explicit_arguments(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Vec<bool>, NatDefinitionElabError> {
        let mut type_ = self.reduce_type_of(head)?;
        let mut explicit = Vec::with_capacity(arguments.len());
        for argument in arguments {
            self.tick()?;
            let whnf = self.whnf(&type_)?;
            let ExprNode::ForallE {
                body, binder_info, ..
            } = whnf.node()
            else {
                break;
            };
            explicit.push(*binder_info == BinderInfo::Default);
            type_ = self.substitute(body, argument)?;
        }
        Ok(explicit)
    }

    /// Refuse a weak-head normal form at which the pin's reduction at `all` would go on: a
    /// theorem it unfolds, a hole, or an eliminator whose major premise is not stuck on a local.
    fn refuse_reduction_stuck_short(&mut self, term: &Expr) -> Result<(), NatDefinitionElabError> {
        let (head, arguments) = operators::spine(term);
        let stuck = || NatDefinitionElabError::UnexpectedSyntax {
            expected: "a #reduce term whose normal form passes no theorem the pin unfolds at `all`",
        };
        match head.node() {
            ExprNode::MVar { .. } => Err(stuck()),
            ExprNode::Const { name, .. } => match self.txn.env.find(name).cloned() {
                Some(ConstantInfo::Thm(_)) => Err(stuck()),
                Some(ConstantInfo::Defn(definition))
                    if definition.safety == DefinitionSafety::Safe =>
                {
                    Err(stuck())
                }
                Some(ConstantInfo::Rec(recursor)) => {
                    let major = recursor_major(&recursor)?;
                    match arguments.get(major) {
                        Some(major) => self.require_stuck_on_local(major, &stuck),
                        None => Ok(()),
                    }
                }
                Some(ConstantInfo::Quot(_)) => {
                    match self.source_quotient_major(&head, arguments.len())? {
                        Some(major) => {
                            let major = &arguments[major];
                            self.require_stuck_on_local(major, &stuck)
                        }
                        None => Ok(()),
                    }
                }
                _ => Ok(()),
            },
            _ => Ok(()),
        }
    }

    /// A major premise the pin, too, cannot reduce: its weak-head normal form is headed by a
    /// local variable, or by an axiom or opaque constant.
    fn require_stuck_on_local(
        &mut self,
        major: &Expr,
        stuck: &dyn Fn() -> NatDefinitionElabError,
    ) -> Result<(), NatDefinitionElabError> {
        let major = self.meta_whnf(major)?;
        let (head, _) = operators::spine(&major);
        match head.node() {
            ExprNode::FVar { .. } => Ok(()),
            ExprNode::Const { name, .. }
                if matches!(
                    self.txn.env.find(name),
                    Some(ConstantInfo::Axiom(_) | ConstantInfo::Opaque(_))
                ) =>
            {
                Ok(())
            }
            _ => Err(stuck()),
        }
    }
}
