//! Course-of-values fallback for a single inductive family with local indices.
//!
//! Use the admitted family's below/brecOn definitions, not an unchecked self
//! declaration. A private below parameter is generalized by ordinary dependent
//! matching. As in the pin's Structural/BRecOn.toBelow, a fresh opaque motive
//! distinguishes dictionary entries even when every actual result type is Nat.
use super::*;
use fln_env::constants::{ConstantInfo, DefinitionSafety};

impl Context {
    fn course_spine(&mut self, value: &Expr) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = value.clone();
        let mut args = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    args.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                _ => break,
            }
        }
        args.reverse();
        Ok((head, args))
    }

    /// Assign every universe hole still open in `terms` or in the local context a fresh rigid
    /// parameter, returning those parameters. An auto-bound `α : Sort ?u` keeps its hole until
    /// the declaration generalizes it, and a kernel query refuses any hole. A conversion found
    /// with rigid parameters holds under every later assignment, so the caller may decide with
    /// it — and must restore the universe store afterwards: these assignments are not answers.
    /// The names have a numeric component, which source cannot spell.
    pub(super) fn rigid_open_universes(
        &mut self,
        terms: &[&Expr],
    ) -> Result<Vec<Name>, NatDefinitionElabError> {
        let mut pending = Vec::new();
        for term in terms {
            pending.push(self.instantiate(term)?);
        }
        for local in self.txn.lctx.decls().to_vec() {
            self.tick()?;
            pending.push(self.instantiate(&local.type_)?);
            if let Some(value) = &local.value {
                pending.push(self.instantiate(value)?);
            }
        }
        let mut seen = HashSet::new();
        let mut levels = Vec::new();
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !expr.has_level_mvar() || !seen.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::Sort { level } => levels.push(level.clone()),
                ExprNode::Const { levels: args, .. } => levels.extend(args.iter().cloned()),
                ExprNode::App { f, a } => pending.extend([f.clone(), a.clone()]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => pending.extend([binder_type.clone(), body.clone()]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => pending.extend([type_.clone(), value.clone(), body.clone()]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    pending.push(expr.clone())
                }
                _ => {}
            }
        }
        let mut holes = Vec::new();
        while let Some(level) = levels.pop() {
            self.tick()?;
            match level.view() {
                fln_core::level::LevelView::MVar(id) => {
                    if !holes.contains(id) && !self.txn.universes.is_assigned(id) {
                        holes.push(id.clone());
                    }
                }
                fln_core::level::LevelView::Succ(inner) => levels.push(inner.clone()),
                fln_core::level::LevelView::Max(a, b) | fln_core::level::LevelView::IMax(a, b) => {
                    levels.extend([a.clone(), b.clone()])
                }
                _ => {}
            }
        }
        let mut parameters = Vec::with_capacity(holes.len());
        for (index, hole) in holes.into_iter().enumerate() {
            self.tick()?;
            let parameter = Name::num(Name::from_components(["_fln_open_universe"]), index as u64);
            self.txn
                .universes
                .assign(hole, Level::param(parameter.clone()));
            parameters.push(parameter);
        }
        Ok(parameters)
    }

    fn course_apply(
        &mut self,
        function: Typed,
        value: Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        let type_ = self
            .known_type(&value)?
            .ok_or_else(|| error(RecursionError::NotDecreasing))?;
        self.match_apply(function, Typed { value, type_ })
    }

    pub(super) fn course_of_values_body(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let expected = expected.ok_or_else(|| error(RecursionError::ResultTypeRequired))?;
        let recursion = self
            .recursion
            .clone()
            .expect("prepared structural candidate");
        let major = recursion.parameters[recursion.decreasing].clone();
        let family_type = self.whnf(&major.type_)?;
        let (head, parameters) = self.course_spine(&family_type)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(error(RecursionError::NotDecreasing));
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Err(error(RecursionError::NotDecreasing));
        };
        if family.all.len() != 1
            || parameters.len() != family.num_params as usize + family.num_indices as usize
        {
            return Err(error(RecursionError::NotDecreasing));
        }
        // Only independent source index binders can be generalized here.
        // Fixed/repeated indices keep the ordinary refinement boundary.
        let (parameters, index_values) = parameters.split_at(family.num_params as usize);
        let indices = match self.elimination_index_locals(index_values) {
            Err(NatDefinitionElabError::Inference(SourceInferenceError::Match(
                matching::MatchError::UnrefinedIndices,
            ))) => {
                // This fallback has not changed the fixed-index boundary.
                // Keep other structural candidates and automatic well-founded
                // fallback eligible; resource and typing errors still escape.
                return Err(error(RecursionError::NotDecreasing));
            }
            result => result?,
        };
        let brec = Name::str(name.clone(), "brecOn");
        if !self.is_auxiliary_recursor(&brec)? {
            return Err(error(RecursionError::NotDecreasing));
        }
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(&brec).cloned() else {
            return Err(error(RecursionError::NotDecreasing));
        };
        if definition.safety != DefinitionSafety::Safe {
            return Err(error(RecursionError::NotDecreasing));
        }
        // Preserve the original source obligation before adding any induction
        // dictionary. It must not make invalid original typing disappear.
        let obligation = self.original_recursive_body_obligation(syntax, Some(expected.clone()))?;
        self.recursive_indices(name, parameters, &indices)?;
        let recursion = self
            .recursion
            .clone()
            .expect("classified structural candidate");
        let target = self.recursive_target(&expected)?;
        let type_ = self
            .known_type(&target)?
            .ok_or_else(|| error(RecursionError::NotDecreasing))?;
        let universe = self.sort_level(&Typed {
            value: target.clone(),
            type_,
        })?;
        let mut motive = Expr::lam(
            major.user_name.clone(),
            family_type.clone(),
            target
                .abstract_fvar(&major.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
        // Family order is not necessarily the source telescope order. Keep
        // each index's real dependent domain, followed by the major premise.
        for index in indices.iter().rev() {
            self.tick()?;
            motive = Expr::lam(
                index.user_name.clone(),
                self.instantiate(&index.type_)?,
                motive
                    .abstract_fvar(&index.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
        }
        let mut universes = if definition.base.level_params.len() == levels.len() {
            Vec::new()
        } else {
            vec![universe]
        };
        universes.extend(levels.iter().cloned());
        if universes.len() != definition.base.level_params.len() {
            return Err(error(RecursionError::NotDecreasing));
        }
        let mut recursor = Typed {
            value: Expr::const_(brec, universes.clone()),
            type_: self.instantiate_params(
                &definition.base.type_,
                &definition.base.level_params,
                &universes,
            )?,
        };
        for parameter in parameters {
            recursor = self.course_apply(recursor, parameter.clone())?;
        }
        recursor = self.course_apply(recursor, motive)?;
        for index in &indices {
            recursor = self.course_apply(recursor, Expr::fvar(index.id.clone()))?;
        }
        recursor = self.course_apply(recursor, Expr::fvar(major.id.clone()))?;
        let remaining = self.whnf(&recursor.type_)?;
        let ExprNode::ForallE {
            binder_type: functional_type,
            ..
        } = remaining.node()
        else {
            return Err(error(RecursionError::NotDecreasing));
        };
        let mut function = functional_type.clone();
        for index in &indices {
            self.tick()?;
            function = self.whnf(&function)?;
            let ExprNode::ForallE { body, .. } = function.node() else {
                return Err(error(RecursionError::NotDecreasing));
            };
            function = self.substitute(body, &Expr::fvar(index.id.clone()))?;
        }
        let function = self.whnf(&function)?;
        let ExprNode::ForallE { body, .. } = function.node() else {
            return Err(error(RecursionError::NotDecreasing));
        };
        let body = self.substitute(body, &Expr::fvar(major.id.clone()))?;
        let body = self.whnf(&body)?;
        let ExprNode::ForallE {
            binder_type: below_type,
            ..
        } = body.node()
        else {
            return Err(error(RecursionError::NotDecreasing));
        };
        let saved = self.txn.lctx.clone();
        let below_name = self.fresh_name()?;
        let below_id = FVarId(below_name.clone());
        self.txn.lctx.add_param(
            below_id.clone(),
            below_name.clone(),
            below_type.clone(),
            BinderInfo::Default,
        );
        let state = self.recursion.as_mut().expect("course candidate");
        state.pending = false;
        state.course_name = Some(below_name.clone());
        state.matrix_hidden.insert(below_name);
        let term = self.term(syntax, Some(expected.clone()))?;
        self.resolve_instances_with_defaults()?;
        self.flush(true)?;
        let mut value = self.instantiate(&term.value)?;
        if self.elimination_reads(&value)?.contains(&recursion.marker) {
            return Err(error(RecursionError::PartialApplication));
        }
        // The dictionary's motive already abstracts changing parameters. Keep
        // that order in the functional, including dependency-bearing domains.
        for position in recursion.varying.iter().rev() {
            let local = &recursion.parameters[*position];
            self.tick()?;
            value = Expr::lam(
                local.user_name.clone(),
                self.instantiate(&local.type_)?,
                value
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        value = Expr::lam(
            Name::anonymous(),
            below_type.clone(),
            value
                .abstract_fvar(&below_id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
        value = Expr::lam(
            major.user_name.clone(),
            family_type,
            value
                .abstract_fvar(&major.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
        for index in indices.iter().rev() {
            self.tick()?;
            value = Expr::lam(
                index.user_name.clone(),
                self.instantiate(&index.type_)?,
                value
                    .abstract_fvar(&index.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
        }
        self.txn.lctx = saved;
        self.recursion = Some(recursion.clone());
        let mut result = self.match_apply(
            recursor,
            Typed {
                value,
                type_: functional_type.clone(),
            },
        )?;
        for position in &recursion.varying {
            result = self.course_apply(
                result,
                Expr::fvar(recursion.parameters[*position].id.clone()),
            )?;
        }
        result.value = Expr::let_e(
            structural_obligation_name(recursion.parameters.len()),
            obligation.type_,
            obligation.value,
            result.value,
            false,
        );
        let result = self.finish_term(result, Some(&expected))?;
        // A failed candidate restores the whole context, so only the selected lowering's
        // definition is recorded here.
        if !self.course_definitions.contains(&recursion.name) {
            self.course_definitions.push(recursion.name.clone());
        }
        Ok(result)
    }

    pub(super) fn lower_course_call(
        &mut self,
        arguments: &[Expr],
    ) -> Result<Expr, NatDefinitionElabError> {
        // This hook runs before the final whole-body flush. The recursive
        // argument's checked type may still be constraining an implicit uniform
        // parameter; solve existing equations before mistaking that hole for a
        // changed family parameter. No assignment is guessed from a history hit.
        if arguments
            .iter()
            .any(|arg| arg.has_expr_mvar() || arg.has_level_mvar())
        {
            self.flush(false)?;
        }
        let recursion = self.recursion.clone().expect("course call owner");
        let arguments = arguments
            .iter()
            .map(|argument| self.instantiate(argument))
            .collect::<Result<Vec<_>, _>>()?;
        for (position, parameter) in recursion
            .parameters
            .iter()
            .enumerate()
            .take(recursion.decreasing)
        {
            self.tick()?;
            if !recursion.varying.contains(&position)
                && !recursion.indices.contains(&position)
                && !self.fixed_recursive_argument(&arguments[position], parameter)?
            {
                return Err(error(RecursionError::GeneralizeParameter {
                    owner: recursion.parameters[recursion.decreasing].id.clone(),
                    position,
                }));
            }
        }
        let argument = self.instantiate(&arguments[recursion.decreasing])?;
        if self
            .elimination_reads(&argument)?
            .contains(&recursion.marker)
        {
            return Err(error(RecursionError::NotDecreasing));
        }
        let name = recursion
            .course_name
            .as_ref()
            .expect("course dictionary name");
        let below = self
            .txn
            .lctx
            .find_by_user_name(name)
            .cloned()
            .ok_or_else(|| error(RecursionError::NotDecreasing))?;
        let parameters = recursion.family.as_ref().expect("course family").1;
        // A history entry is identified by every index AND its smaller major.
        // Equal result types never license selecting another child's entry.
        let mut requested = Vec::new();
        for position in &recursion.indices {
            self.tick()?;
            requested.push(
                arguments
                    .get(*position)
                    .cloned()
                    .ok_or_else(|| error(RecursionError::NotDecreasing))?,
            );
        }
        requested.push(argument);
        let (head, mut args) = self.course_spine(&below.type_)?;
        let expected_head = Name::str(recursion.family.as_ref().unwrap().0.clone(), "below");
        if !matches!(head.node(), ExprNode::Const { name, .. } if name == &expected_head)
            || args.len() != parameters + recursion.indices.len() + 2
        {
            return Err(error(RecursionError::NotDecreasing));
        }
        let motive_type = self
            .known_type(&args[parameters])?
            .ok_or_else(|| error(RecursionError::NotDecreasing))?;
        let saved = self.txn.lctx.clone();
        let canary = FVarId(self.fresh_name()?);
        self.txn.lctx.add_param(
            canary.clone(),
            Name::anonymous(),
            motive_type,
            BinderInfo::Default,
        );
        args[parameters] = Expr::fvar(canary.clone());
        let dictionary = args.into_iter().fold(head, Expr::app);
        // Entries are compared generically over any universe the declaration has yet to
        // generalize; the rigid stand-ins never outlive this search.
        let universes = self.txn.universes.clone();
        let mut terms = vec![&dictionary];
        terms.extend(&requested);
        let selected = self.rigid_open_universes(&terms).and_then(|_| {
            self.search_course_dictionary(
                dictionary.clone(),
                Expr::fvar(below.id),
                &canary,
                &requested,
            )
        });
        self.txn.universes = universes;
        self.txn.lctx = saved;
        let mut result = selected?.ok_or_else(|| error(RecursionError::NotDecreasing))?;
        for position in &recursion.varying {
            if let Some(argument) = arguments.get(*position) {
                self.tick()?;
                result = Expr::app(result, argument.clone());
            }
        }
        for argument in arguments.iter().skip(recursion.parameters.len()) {
            self.tick()?;
            result = Expr::app(result, argument.clone());
        }
        Ok(result)
    }

    fn search_course_dictionary(
        &mut self,
        dictionary: Expr,
        value: Expr,
        canary: &FVarId,
        requested: &[Expr],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut pending = vec![(dictionary, value)];
        while let Some((type_, value)) = pending.pop() {
            self.tick()?;
            let type_ = self.whnf(&type_)?;
            let (head, args) = self.course_spine(&type_)?;
            if matches!(head.node(), ExprNode::FVar { id } if id == canary)
                && args.len() == requested.len()
            {
                let mut equal = true;
                for (actual, expected) in args.iter().zip(requested) {
                    self.tick()?;
                    if !self.coercion_kernel_eq(actual.clone(), expected.clone())? {
                        equal = false;
                        break;
                    }
                }
                if equal {
                    return Ok(Some(value));
                }
            } else if matches!(head.node(), ExprNode::Const { name, .. }
                if name == &Name::from_components(["PProd"]) || name == &Name::from_components(["And"]))
                && args.len() == 2
            {
                let ExprNode::Const { name, .. } = head.node() else {
                    unreachable!()
                };
                pending.push((args[1].clone(), Expr::proj(name.clone(), 1, value.clone())));
                pending.push((args[0].clone(), Expr::proj(name.clone(), 0, value)));
            }
        }
        Ok(None)
    }
}
