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
        if !self.allow_auxiliary_declarations || self.aux_names.is_none() {
            return Err(error(TacticError::AuxLemmaUnsupported(
                "an entry point or declaration header that does not return auxiliary declarations",
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
        let private = self.auxiliary_declarations_are_private();
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

    /// Enter `private_decl% e` (`elabPrivateDecl`, `Lean/Elab/BuiltinTerm.lean:465-482`):
    /// reserve a public auxiliary name while exporting, then switch to the private world
    /// (`withoutExporting`) to elaborate `e`.
    pub(in crate::source) fn enter_private_decl(
        &mut self,
    ) -> Result<PrivateDeclState, NatDefinitionElabError> {
        if !self.allow_auxiliary_declarations || self.aux_names.is_none() {
            return Err(error(TacticError::AuxLemmaUnsupported(
                "private_decl% in a context that does not return auxiliary declarations",
            )));
        }
        let Some((mut priv_env, priv_scope)) = self.private_decl_world.clone() else {
            return Err(error(TacticError::AuxLemmaUnsupported(
                "private_decl% without a private module world",
            )));
        };
        // Reserve the public auxiliary name BEFORE entering the private world, matching
        // Lean 4's `let name ← mkAuxDeclName \`_private; withoutExporting do ...`.
        let aux_name = self.aux_decl_name(&Name::from_components(["_private"]))?;
        // Replay any earlier auxiliaries created in this declaration so the private world
        // stays coherent with the public world's prefix.
        let existing: Vec<_> = self.auxiliary_declarations.clone();
        for decl in existing {
            if declaration_name(&decl).is_some_and(|name| !priv_env.contains(name)) {
                priv_env = self.admit_auxiliary_into_env(&priv_env, decl)?;
            }
        }
        if let Some((stored_env, _)) = self.private_decl_world.as_mut() {
            *stored_env = priv_env.clone();
        }
        let priv_with_reducibility = priv_scope
            .local_reducibility
            .environment(&priv_env)
            .map_err(|error| {
                failure(SourceInferenceError::Unification(Box::new(
                    UnificationError::Reducibility(error),
                )))
            })?;
        let state = PrivateDeclState {
            aux_name,
            aux_start: self.auxiliary_declarations.len(),
            saved_env: std::mem::replace(&mut self.txn.env, priv_with_reducibility),
            saved_instance_scopes: std::mem::replace(
                &mut self.source_scope.instance_scopes,
                priv_scope.instance_scopes,
            ),
            saved_local_reducibility: std::mem::replace(
                &mut self.source_scope.local_reducibility,
                priv_scope.local_reducibility,
            ),
            saved_computability: std::mem::replace(
                &mut self.source_scope.computability,
                priv_scope.computability,
            ),
            saved_native: std::mem::replace(&mut self.native, priv_scope.native),
            saved_lctx: self.txn.lctx.clone(),
        };
        self.private_auxiliary_declarations = true;
        self.clear_world_caches();
        Ok(state)
    }

    /// Exit `private_decl% e`: close the privately elaborated term over captured locals,
    /// admit the full declaration in the private world, restore the public world, and admit
    /// only its public `Axiom` interface there (refusing any leaked private type).
    pub(in crate::source) fn finish_private_decl(
        &mut self,
        state: PrivateDeclState,
        term: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        use fln_env::constants::{AxiomVal, DefinitionSafety, DefinitionVal, ReducibilityHints};

        self.flush(false)?;
        self.resolve_instances(false)?;
        self.txn.lctx = state.saved_lctx.clone();
        let mut term = self.finish_open_universes(term)?;
        if term.value.has_expr_mvar() || term.type_.has_expr_mvar() {
            return Err(error(TacticError::AuxLemmaUnsupported(
                "unresolved expression metavariables in private_decl%",
            )));
        }
        if term.value.has_level_mvar() || term.type_.has_level_mvar() {
            return Err(error(TacticError::AuxLemmaUnsupported(
                "unresolved universe metavariables in private_decl%",
            )));
        }
        let orig_type = term.type_.clone();
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
        for local in state.saved_lctx.decls().iter().rev() {
            self.tick()?;
            if !reads.remove(&local.id) {
                continue;
            }
            let mut local = local.clone();
            local.type_ = self.instantiate(&local.type_)?;
            if local.type_.has_expr_mvar() || local.type_.has_level_mvar() {
                return Err(error(TacticError::AuxLemmaUnsupported(
                    "unresolved local dependencies in private_decl%",
                )));
            }
            reads.extend(self.elimination_reads(&local.type_)?);
            for parameter in decision::level_params_in_order(&local.type_, || self.tick())? {
                if !parameters.contains(&parameter) {
                    parameters.push(parameter);
                }
            }
            if let Some(val) = local.value.as_mut() {
                *val = self.instantiate(val)?;
                if val.has_expr_mvar() || val.has_level_mvar() {
                    return Err(error(TacticError::AuxLemmaUnsupported(
                        "unresolved let dependencies in private_decl%",
                    )));
                }
                reads.extend(self.elimination_reads(val)?);
                for parameter in decision::level_params_in_order(val, || self.tick())? {
                    if !parameters.contains(&parameter) {
                        parameters.push(parameter);
                    }
                }
            }
            captures.push(local);
        }
        if !reads.is_empty() {
            return Err(error(TacticError::AuxLemmaUnsupported(
                "a local dependency outside the captured telescope in private_decl%",
            )));
        }
        let arguments: Vec<_> = captures
            .iter()
            .rev()
            .filter(|local| local.value.is_none())
            .map(|local| Expr::fvar(local.id.clone()))
            .collect();
        for local in captures {
            self.tick()?;
            if let Some(val) = local.value {
                term.value = Expr::let_e(
                    local.user_name.clone(),
                    local.type_.clone(),
                    val.clone(),
                    term.value
                        .abstract_fvar(&local.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    false,
                );
                let abs_ty = term
                    .type_
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                if abs_ty.has_loose_bvar(0) {
                    term.type_ = Expr::let_e(local.user_name, local.type_, val, abs_ty, false);
                }
            } else {
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
        let sort = self
            .known_type(&term.type_)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let is_prop = matches!(self.whnf(&sort)?.node(), ExprNode::Sort { level } if level.normalize().is_zero());
        let base = ConstantVal {
            name: state.aux_name.clone(),
            level_params: levels,
            type_: term.type_.clone(),
        };
        let mut computable_data_bridge = false;
        let full_decl = if is_prop {
            Declaration::Thm(TheoremVal {
                base: base.clone(),
                value: term.value,
                all: vec![state.aux_name.clone()],
            })
        } else {
            // Check computability in the private world before switching back to the
            // public world's `Axiom` interface (`Lean/Elab/BuiltinTerm.lean:477-478`).
            if !self.declaration_is_noncomputable && !self.noncomputable_definition {
                let saved_lctx = std::mem::take(&mut self.txn.lctx);
                let codegen = self.check_definition_codegen(&Typed {
                    value: term.value.clone(),
                    type_: term.type_.clone(),
                });
                self.txn.lctx = saved_lctx;
                let noncomp = codegen?;
                if noncomp {
                    self.noncomputable_definition = true;
                } else {
                    computable_data_bridge = true;
                }
            }
            Declaration::Defn(DefinitionVal {
                base: base.clone(),
                value: term.value,
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![state.aux_name.clone()],
            })
        };
        // Any auxiliaries generated inside `private_decl%` (before the bridge itself)
        // stay strictly private to the private world.
        let nested_aux: Vec<_> = self.auxiliary_declarations[state.aux_start..].to_vec();
        for decl in &nested_aux {
            if let Some(name) = declaration_name(decl) {
                self.auxiliary_visibility.private_only.insert(name.clone());
            }
        }
        // Admit the full declaration once into the private world (kernel-checked!).
        if let Some((mut raw_priv_env, _)) = self.private_decl_world.clone() {
            for decl in nested_aux {
                if declaration_name(&decl).is_some_and(|name| !raw_priv_env.contains(name)) {
                    raw_priv_env = self.admit_auxiliary_into_env(&raw_priv_env, decl)?;
                }
            }
            raw_priv_env = self.admit_auxiliary_into_env(&raw_priv_env, full_decl.clone())?;
            if let Some((stored_env, _)) = self.private_decl_world.as_mut() {
                *stored_env = raw_priv_env;
            }
        } else {
            let priv_checked_env = self.txn.env.clone();
            let _ = self.admit_auxiliary_into_env(&priv_checked_env, full_decl.clone())?;
        }
        // Restore the public world, then admit ONLY the public `Axiom` interface
        // (mechanically rejecting any private constant leaking into the type).
        self.txn.env = state.saved_env;
        self.source_scope.instance_scopes = state.saved_instance_scopes;
        self.source_scope.local_reducibility = state.saved_local_reducibility;
        self.source_scope.computability = state.saved_computability;
        self.native = state.saved_native;
        self.private_auxiliary_declarations = false;
        self.clear_world_caches();
        let interface = Declaration::Axiom(AxiomVal {
            base,
            is_unsafe: false,
        });
        let public_env = self.txn.env.clone();
        self.txn.env = self.admit_auxiliary_into_env(&public_env, interface)?;
        self.auxiliary_declarations.push(full_decl);
        self.auxiliary_visibility
            .private_bridge
            .insert(state.aux_name.clone());
        if computable_data_bridge {
            self.auxiliary_visibility
                .computable_private_bridge
                .insert(state.aux_name.clone());
        }
        let value = arguments.into_iter().fold(
            Expr::const_(
                state.aux_name,
                parameters.into_iter().map(Level::param).collect(),
            ),
            Expr::app,
        );
        Ok(Typed {
            value,
            type_: orig_type,
        })
    }
}

fn declaration_name(declaration: &Declaration) -> Option<&Name> {
    match declaration {
        Declaration::Axiom(val) => Some(&val.base.name),
        Declaration::Defn(val) => Some(&val.base.name),
        Declaration::Thm(val) => Some(&val.base.name),
        Declaration::Opaque(val) => Some(&val.base.name),
        _ => None,
    }
}

pub(in crate::source) struct PrivateDeclState {
    aux_name: Name,
    aux_start: usize,
    saved_env: Environment,
    saved_instance_scopes: crate::instances::scoped::ActiveScopes,
    saved_local_reducibility: crate::reducibility::LocalReducibility,
    saved_computability: Option<scope::computability::ComputabilityProvider>,
    saved_native: Option<crate::native::NativeProvider>,
    saved_lctx: LocalContext,
}
