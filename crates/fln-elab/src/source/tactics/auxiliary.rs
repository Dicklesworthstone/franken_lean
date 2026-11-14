//! `as_aux_lemma` isolates the current goal, closes its proof over ordinary
//! local dependencies, and replaces it by an application of a checked theorem.
//! The returned declaration effect still needs the engine's independent seat.
use super::*;
use fln_env::constants::{ConstantVal, TheoremVal};

const MAX_AUXILIARY_LEMMAS: usize = 256;

#[derive(Clone, Default)]
pub(in crate::source) struct AuxLemmaCache(Vec<CachedLemma>);

#[derive(Clone)]
struct CachedLemma {
    type_: Expr,
    levels: Vec<Name>,
    name: Name,
    private: bool,
}

impl Context {
    /// A child proof owns one fresh goal. Its sibling work and outer control
    /// barriers remain on the ordinary term task stack until this child closes.
    pub(in crate::source) fn start_auxiliary_proof<'a>(
        &mut self,
        goal: &ProofGoal,
        body: &'a Syntax,
    ) -> Result<ProofState<'a>, NatDefinitionElabError> {
        if !self.allow_auxiliary_declarations {
            return Err(error(TacticError::AuxLemmaUnsupported(
                "an entry point that does not return auxiliary declarations",
            )));
        }
        self.txn.lctx = goal.lctx.clone();
        let target = self.instantiate(&goal.target)?;
        let sort = self
            .known_type(&target)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        if !matches!(self.whnf(&sort)?.node(), ExprNode::Sort { level } if level.is_always_zero()) {
            return Err(error(TacticError::ExpectedProposition));
        }
        let instructions = self.proof_instructions(body)?;
        let (root, mut child) = self.proof_goal(target.clone())?;
        child.no_implicit_lambda = goal.no_implicit_lambda;
        if let Some(tag) = self.goal_tags.get(&goal.id).cloned() {
            self.goal_tags.insert(child.id.clone(), tag);
        }
        Ok(ProofState {
            extent: self.observation_extent(body)?.map(Box::new),
            saved: goal.lctx.clone(),
            target,
            root,
            instructions,
            cursor: 0,
            work: vec![Work::Goal(child)],
            controls: Vec::new(),
            owned_frame: None,
        })
    }

    pub(in crate::source) fn finish_auxiliary_proof(
        &mut self,
        goal: ProofGoal,
        term: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let mut term = self.finish_open_universes(term)?;
        // Ordinary proof holes have already failed. Declaration finalization
        // may defer a local recursive function, but an auxiliary predecessor
        // cannot refer to that still-unassigned expression obligation.
        if term.value.has_expr_mvar() || term.type_.has_expr_mvar() {
            return Err(error(TacticError::AuxLemmaUnsupported(
                "deferred expression obligations in an auxiliary closure",
            )));
        }
        if term.value.has_level_mvar() || term.type_.has_level_mvar() {
            return Err(error(TacticError::AuxLemmaUnsupported(
                "unresolved universe variables in an auxiliary closure",
            )));
        }

        // A cache hit can replace this proof by an earlier theorem of the
        // same type. Check the completed child before its body can disappear,
        // using the same metered assignment check as a speculative exact.
        let check = self.hole(term.type_.clone())?;
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::SafeDefinitions;
        let report = self
            .txn
            .unify(&check, &term.value, budget)
            .map_err(|reason| failure(SourceInferenceError::Unification(Box::new(reason))))?;
        assert!(report.awakened.is_empty(), "private source queue");

        // Closure visits the target and proof before processing free-variable
        // declarations, in reverse local order. Preserve that universe order
        // while using the ordinary local telescope for expression arguments.
        let mut parameters = Vec::new();
        for root in [&term.type_, &term.value] {
            for parameter in decision::level_params_in_order(root, || self.tick())? {
                if !parameters.contains(&parameter) {
                    parameters.push(parameter);
                }
            }
        }
        let mut reads = self.elimination_reads(&term.type_)?;
        reads.extend(self.elimination_reads(&term.value)?);
        let mut captures = Vec::new();
        for local in goal.lctx.decls().iter().rev() {
            self.tick()?;
            if !reads.remove(&local.id) {
                continue;
            }
            // Lean's default closure decides which let values require zeta
            // expansion by tracking type-checker reductions. Lambda-abstracting
            // one blindly can change definitional equality. Keep this boundary
            // explicit until that tracking is supported by the native checker.
            if local.value.is_some() {
                return Err(error(TacticError::AuxLemmaUnsupported(
                    "captured let variables requiring zetaDelta closure tracking",
                )));
            }
            let mut local = local.clone();
            local.type_ = self.instantiate(&local.type_)?;
            if local.type_.has_expr_mvar() || local.type_.has_level_mvar() {
                return Err(error(TacticError::AuxLemmaUnsupported(
                    "unresolved dependencies in an auxiliary closure",
                )));
            }
            reads.extend(self.elimination_reads(&local.type_)?);
            for parameter in decision::level_params_in_order(&local.type_, || self.tick())? {
                if !parameters.contains(&parameter) {
                    parameters.push(parameter);
                }
            }
            captures.push(local);
        }
        if !reads.is_empty() {
            return Err(error(TacticError::AuxLemmaUnsupported(
                "a local dependency outside the captured telescope",
            )));
        }
        let arguments: Vec<_> = captures
            .iter()
            .rev()
            .map(|local| Expr::fvar(local.id.clone()))
            .collect();
        for local in captures {
            self.tick()?;
            term.value = Expr::lam(
                local.user_name.clone(),
                local.type_.clone(),
                term.value
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
            term.type_ = Expr::forall_e(
                local.user_name,
                local.type_,
                term.type_
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        if term.value.has_fvar()
            || term.type_.has_fvar()
            || term.value.has_loose_bvars()
            || term.type_.has_loose_bvars()
        {
            return Err(failure(SourceInferenceError::Scope));
        }
        let levels: Vec<_> = parameters
            .iter()
            .enumerate()
            .map(|(index, _)| Name::str(Name::anonymous(), format!("u_{}", index + 1)))
            .collect();
        let renamed: Vec<_> = levels.iter().cloned().map(Level::param).collect();
        term.type_ = self.instantiate_params(&term.type_, &parameters, &renamed)?;
        term.value = self.instantiate_params(&term.value, &parameters, &renamed)?;
        let private =
            self.source_scope.private_module.is_some() && !self.source_scope.public_declarations;
        let mut cached = None;
        for index in 0..self.aux_lemma_cache.0.len() {
            self.tick()?;
            let entry = &self.aux_lemma_cache.0[index];
            if (!entry.private || private) && entry.type_ == term.type_ && entry.levels == levels {
                cached = Some(entry.name.clone());
                break;
            }
        }
        let name = if let Some(name) = cached {
            name
        } else {
            if self.aux_lemma_cache.0.len() >= MAX_AUXILIARY_LEMMAS {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            let name = self.aux_decl_name(&Name::from_components(["_proof"]))?;
            self.expose_auxiliary_declaration(Declaration::Thm(TheoremVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: levels.clone(),
                    type_: term.type_.clone(),
                },
                value: term.value,
                all: vec![name.clone()],
            }))?;
            self.aux_lemma_cache.0.push(CachedLemma {
                type_: term.type_,
                levels,
                name: name.clone(),
                private,
            });
            name
        };
        let value = arguments.into_iter().fold(
            Expr::const_(name, parameters.into_iter().map(Level::param).collect()),
            Expr::app,
        );
        self.close_proof_goal(goal, value)
    }
}
