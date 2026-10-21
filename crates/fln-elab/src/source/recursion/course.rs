//! Course-of-values fallback for a single, unindexed inductive family.
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
            || family.num_indices != 0
            || parameters.len() != family.num_params as usize
        {
            return Err(error(RecursionError::NotDecreasing));
        }
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
        self.recursive_indices(name, &parameters, &[])?;
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
        let motive = Expr::lam(
            major.user_name.clone(),
            family_type.clone(),
            target
                .abstract_fvar(&major.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
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
            recursor = self.course_apply(recursor, parameter)?;
        }
        recursor = self.course_apply(recursor, motive)?;
        recursor = self.course_apply(recursor, Expr::fvar(major.id.clone()))?;
        let remaining = self.whnf(&recursor.type_)?;
        let ExprNode::ForallE {
            binder_type: functional_type,
            ..
        } = remaining.node()
        else {
            return Err(error(RecursionError::NotDecreasing));
        };
        let function = self.whnf(functional_type)?;
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
        self.finish_term(result, Some(&expected))
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
        let (head, mut args) = self.course_spine(&below.type_)?;
        let expected_head = Name::str(recursion.family.as_ref().unwrap().0.clone(), "below");
        if !matches!(head.node(), ExprNode::Const { name, .. } if name == &expected_head)
            || args.len() != parameters + 2
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
        let selected =
            self.search_course_dictionary(dictionary, Expr::fvar(below.id), &canary, &argument);
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
        argument: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut pending = vec![(dictionary, value)];
        while let Some((type_, value)) = pending.pop() {
            self.tick()?;
            let type_ = self.whnf(&type_)?;
            let (head, args) = self.course_spine(&type_)?;
            if matches!(head.node(), ExprNode::FVar { id } if id == canary) && args.len() == 1 {
                if self.coercion_kernel_eq(args[0].clone(), argument.clone())? {
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
