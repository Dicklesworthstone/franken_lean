//! Explicit delta/zeta unfolding at proof-state locations.
//!
//! The selected reducer is shared with `simp only [name]`, but `unfold` changes
//! the goal/local types by definitional equality instead of manufacturing an
//! equality theorem. The final proof is still checked against the original
//! declaration telescope by both ordinary admission checkers. `delta` unfolds the
//! same way, by the definitions' values rather than their equations.
use super::*;

/// A step of [`Context::delta_expand`]'s heap walk.
enum DeltaStep {
    Visit(Expr),
    /// Record the result on top of the stack as this expression's.
    Done(Expr),
    /// Rebuild this expression from its children's results, the last on top.
    Rebuild(Expr),
}

impl Context {
    pub(super) fn unfold_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, names, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "unfold", "unfold tactic")?;
        let names = expect_null_args(names, "unfold declarations")?;
        if names.is_empty()
            || names
                .iter()
                .any(|name| !matches!(name, Syntax::Ident { val, .. } if !val.is_anonymous()))
        {
            return Err(error(TacticError::MalformedScript));
        }

        self.txn.lctx = goal.lctx.clone();
        let locations = self.rewrite_locations(location)?;
        let (hypotheses, target) = match locations {
            None => (Vec::new(), true),
            Some(locations) => (locations.hypotheses, locations.target),
        };

        let mut changed = false;
        if !hypotheses.is_empty() {
            let original = self.txn.lctx.clone();
            let mut updates = std::collections::HashMap::new();
            for name in hypotheses {
                self.tick()?;
                let local = original
                    .find_by_user_name(&name)
                    .cloned()
                    .ok_or_else(|| error(TacticError::RewriteLocation))?;
                let (type_, did_change) = self.unfold_tactic_expression(names, &local.type_)?;
                if did_change {
                    updates.insert(local.id.clone(), type_);
                    changed = true;
                }
            }
            if !updates.is_empty() {
                let mut context = LocalContext::new();
                for local in original.decls() {
                    self.tick()?;
                    let mut local = local.clone();
                    if let Some(type_) = updates.get(&local.id) {
                        local.type_ = type_.clone();
                    }
                    eliminate::add_local(&mut context, &local);
                }
                self.txn.lctx = context.clone();
                goal.lctx = context;
            }
        }

        if target {
            let (next, did_change) = self.unfold_tactic_expression(names, &goal.target)?;
            if did_change {
                goal.target = next;
                changed = true;
            }
        }

        if !changed {
            let name = match &names[0] {
                Syntax::Ident { val, .. } => val.clone(),
                _ => unreachable!("validated unfold name"),
            };
            return Err(error(TacticError::UnfoldFailed(name)));
        }
        proof.work.push(Work::Goal(goal));
        Ok(())
    }
}

impl Context {
    /// `delta f+ (at loc)?` (`evalDelta`, vendored src/Lean/Elab/Tactic/Delta.lean): each name
    /// a global constant (`realizeGlobalConstNoOverloadWithInfo`), and each selected type
    /// replaced by its `deltaExpand`, a definitionally equal one (`replaceTargetDefEq`,
    /// `replaceLocalDeclDefEq`). A selected type that does not change fails, and so does
    /// `at *` when nothing changes (`withLocation`, vendored src/Lean/Elab/Tactic/Location.lean).
    pub(super) fn delta_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, names, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "delta", "delta tactic")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "delta"])?;
        self.txn.lctx = goal.lctx.clone();
        let mut declarations = Vec::new();
        for name in expect_null_args(names, "delta declarations")? {
            self.tick()?;
            let Syntax::Ident { val, .. } = name else {
                return Err(error(TacticError::MalformedScript));
            };
            let resolved = self
                .resolve_source_name(val)?
                .filter(|resolved| self.txn.env.contains(resolved))
                .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(val.clone())))?;
            declarations.push(resolved);
        }
        if declarations.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        let failed = |at: Option<Name>| {
            error(TacticError::DeltaFailed {
                declarations: declarations.clone(),
                at,
            })
        };
        let Some(locations) = self.rewrite_locations(location)? else {
            let target = self.instantiate(&goal.target)?;
            let expanded = self.delta_expand(&declarations, &target)?;
            if expanded == target {
                return Err(failed(None));
            }
            goal.target = expanded;
            proof.work.push(Work::Goal(goal));
            return Ok(());
        };
        if locations.all {
            // The target first, then every local from the last (`withLocation`'s wildcard).
            let mut worked = false;
            let target = self.instantiate(&goal.target)?;
            let expanded = self.delta_expand(&declarations, &target)?;
            if expanded != target {
                goal.target = expanded;
                worked = true;
            }
            let ids: Vec<FVarId> = goal
                .lctx
                .decls()
                .iter()
                .rev()
                .filter(|local| !self.is_matrix_hypothesis(local))
                .map(|local| local.id.clone())
                .collect();
            for id in ids {
                worked |= self.delta_local(&mut goal, &declarations, &id)?;
            }
            if !worked {
                return Err(failed(None));
            }
            proof.work.push(Work::Goal(goal));
            return Ok(());
        }
        for name in &locations.hypotheses {
            self.tick()?;
            let local = goal
                .lctx
                .find_by_user_name(name)
                .cloned()
                .ok_or_else(|| error(TacticError::RewriteLocation))?;
            if !self.delta_local(&mut goal, &declarations, &local.id)? {
                return Err(failed(Some(local.user_name)));
            }
        }
        if locations.target {
            self.txn.lctx = goal.lctx.clone();
            let target = self.instantiate(&goal.target)?;
            let expanded = self.delta_expand(&declarations, &target)?;
            if expanded == target {
                return Err(failed(None));
            }
            goal.target = expanded;
        }
        proof.work.push(Work::Goal(goal));
        Ok(())
    }

    /// Replace local `id`'s type by its `deltaExpand` in `goal`'s context, if that changes it.
    fn delta_local(
        &mut self,
        goal: &mut ProofGoal,
        declarations: &[Name],
        id: &FVarId,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(local) = goal
            .lctx
            .decls()
            .iter()
            .find(|local| &local.id == id)
            .cloned()
        else {
            return Ok(false);
        };
        let type_ = self.instantiate(&local.type_)?;
        let expanded = self.delta_expand(declarations, &type_)?;
        if expanded == type_ {
            return Ok(false);
        }
        let mut context = LocalContext::new();
        for other in goal.lctx.decls() {
            self.tick()?;
            let mut other = other.clone();
            if &other.id == id {
                other.type_ = expanded.clone();
            }
            eliminate::add_local(&mut context, &other);
        }
        self.txn.lctx = context.clone();
        goal.lctx = context;
        Ok(true)
    }

    /// `deltaExpand e declarations.contains` (vendored src/Lean/Meta/Tactic/Delta.lean): the
    /// pin's `Core.transform`, outermost first. An application (or a bare constant) whose head
    /// is a named definition at its full universe arity is replaced by the definition's value,
    /// beta-reduced with its arguments (`Expr.betaRev`, zeta-reducing a `let` that blocks a
    /// remaining argument), and the result is visited again; anything else has its children
    /// visited, an application's head and arguments separately. Theorems and opaque constants
    /// never unfold (`hasValue` with `allowOpaque := false`).
    pub(in crate::source) fn delta_expand(
        &mut self,
        declarations: &[Name],
        expr: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut cache: std::collections::HashMap<Expr, Expr> = std::collections::HashMap::new();
        let mut results: Vec<Expr> = Vec::new();
        let mut steps = vec![DeltaStep::Visit(expr.clone())];
        while let Some(step) = steps.pop() {
            self.tick()?;
            match step {
                DeltaStep::Visit(current) => {
                    if let Some(done) = cache.get(&current) {
                        results.push(done.clone());
                        continue;
                    }
                    if let Some(unfolded) = self.delta_step(declarations, &current)? {
                        steps.push(DeltaStep::Done(current));
                        steps.push(DeltaStep::Visit(unfolded));
                        continue;
                    }
                    let children: Vec<Expr> = match current.node() {
                        ExprNode::ForallE {
                            binder_type, body, ..
                        }
                        | ExprNode::Lam {
                            binder_type, body, ..
                        } => vec![binder_type.clone(), body.clone()],
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => vec![type_.clone(), value.clone(), body.clone()],
                        ExprNode::App { .. } => {
                            let mut spine = Vec::new();
                            let mut head = &current;
                            while let ExprNode::App { f, a } = head.node() {
                                spine.push(a.clone());
                                head = f;
                            }
                            spine.push(head.clone());
                            spine.reverse();
                            spine
                        }
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                            vec![expr.clone()]
                        }
                        _ => {
                            cache.insert(current.clone(), current.clone());
                            results.push(current);
                            continue;
                        }
                    };
                    steps.push(DeltaStep::Rebuild(current));
                    steps.extend(children.into_iter().rev().map(DeltaStep::Visit));
                }
                DeltaStep::Done(original) => {
                    let done = results
                        .last()
                        .cloned()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    cache.insert(original, done);
                }
                DeltaStep::Rebuild(original) => {
                    let mut take = |count: usize| {
                        if results.len() < count {
                            return Err(failure(SourceInferenceError::Scope));
                        }
                        Ok(results.split_off(results.len() - count))
                    };
                    let rebuilt = match original.node() {
                        ExprNode::ForallE {
                            binder_name,
                            binder_info,
                            ..
                        } => {
                            let [domain, body] = <[Expr; 2]>::try_from(take(2)?)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                            Expr::forall_e(binder_name.clone(), domain, body, *binder_info)
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_info,
                            ..
                        } => {
                            let [domain, body] = <[Expr; 2]>::try_from(take(2)?)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                            Expr::lam(binder_name.clone(), domain, body, *binder_info)
                        }
                        ExprNode::LetE {
                            decl_name, non_dep, ..
                        } => {
                            let [type_, value, body] = <[Expr; 3]>::try_from(take(3)?)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                            Expr::let_e(decl_name.clone(), type_, value, body, *non_dep)
                        }
                        ExprNode::App { .. } => {
                            let mut count = 1;
                            let mut head = &original;
                            while let ExprNode::App { f, .. } = head.node() {
                                count += 1;
                                head = f;
                            }
                            let mut spine = take(count)?.into_iter();
                            let head = spine
                                .next()
                                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                            spine.fold(head, Expr::app)
                        }
                        ExprNode::MData { data, .. } => {
                            let [inner] = <[Expr; 1]>::try_from(take(1)?)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                            Expr::mdata(data.clone(), inner)
                        }
                        ExprNode::Proj {
                            struct_name, idx, ..
                        } => {
                            let [inner] = <[Expr; 1]>::try_from(take(1)?)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                            Expr::proj(struct_name.clone(), *idx, inner)
                        }
                        _ => return Err(failure(SourceInferenceError::Scope)),
                    };
                    cache.insert(original, rebuilt.clone());
                    results.push(rebuilt);
                }
            }
        }
        match results.as_slice() {
            [result] => Ok(result.clone()),
            _ => Err(failure(SourceInferenceError::Scope)),
        }
    }

    /// `delta? e declarations.contains` (vendored src/Lean/Meta/Tactic/Delta.lean): `e`'s head,
    /// a named definition at its full universe arity, replaced by its value and beta-reduced
    /// with `e`'s arguments (`betaRev (useZeta := true)`).
    fn delta_step(
        &mut self,
        declarations: &[Name],
        expr: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut arguments = Vec::new();
        let mut head = expr;
        while let ExprNode::App { f, a } = head.node() {
            arguments.push(a.clone());
            head = f;
        }
        arguments.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        if !declarations.contains(name) {
            return Ok(None);
        }
        let Some(fln_env::constants::ConstantInfo::Defn(definition)) = self.txn.env.find(name)
        else {
            return Ok(None);
        };
        if definition.base.level_params.len() != levels.len() {
            return Ok(None);
        }
        let (value, parameters) = (
            definition.value.clone(),
            definition.base.level_params.clone(),
        );
        let mut body = self.instantiate_params(&value, &parameters, levels)?;
        if arguments.is_empty() {
            return Ok(Some(body));
        }
        // `Expr.betaRev`: consume a lambda per argument, zeta-reduce a `let` that stands before a
        // remaining one, look through metadata, and instantiate what was consumed.
        let mut consumed = 0;
        while consumed < arguments.len() {
            self.tick()?;
            match body.node() {
                ExprNode::Lam { body: inner, .. } => {
                    body = inner.clone();
                    consumed += 1;
                }
                ExprNode::LetE {
                    value, body: inner, ..
                } => {
                    let (value, inner) = (value.clone(), inner.clone());
                    body = inner
                        .subst_loose(0, std::slice::from_ref(&value))
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                }
                ExprNode::MData { expr, .. } => body = expr.clone(),
                _ => break,
            }
        }
        let body = body
            .subst_loose(0, &arguments[..consumed])
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        Ok(Some(
            arguments[consumed..].iter().cloned().fold(body, Expr::app),
        ))
    }
}
