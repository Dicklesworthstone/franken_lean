//! Canonical conditional applications with source-ordered branch elaboration.
//! Branch evidence and well-founded call caches retain separate lexical scopes;
//! every application still passes ordinary elaboration and kernel checking.
use super::*;

/// The pin's conditional macros (`Init/Notation.lean`, `termIfThenElse` and
/// `termDepIfThenElse`) elaborate the condition before giving it the expected
/// type `Prop`, then apply the admitted `ite` or `dite`. Keep that order without
/// introducing a match: its recursor representation hides the conditional from
/// ordinary lemmas and the pretty printer and can refine a Boolean's branches.
pub(in crate::source) struct ConditionalBuild<'a> {
    parts: ConditionalParts<'a>,
    saved: LocalContext,
    target: Expr,
    function: Typed,
    cursor: usize,
    branch_scope_depth: Option<usize>,
}

impl Context {
    pub(super) fn start_conditional<'a>(
        &mut self,
        parts: ConditionalParts<'a>,
        mut condition: Typed,
        expected: Option<Expr>,
    ) -> Result<ConditionalBuild<'a>, NatDefinitionElabError> {
        let proposition = Expr::sort(Level::zero());
        let boolean = Expr::const_(Name::from_components(["Bool"]), vec![]);
        // The bounded seed has no coercion classes. Its Boolean conditional
        // uses the same equality as the pin's `boolToProp`; imported worlds
        // take the ordinary coercion path, so their registered instances apply.
        if self.whnf(&condition.type_)? == boolean && !self.has_coercion_class("CoeT")? {
            condition = Typed {
                value: [
                    boolean,
                    condition.value,
                    Expr::const_(Name::from_components(["Bool", "true"]), vec![]),
                ]
                .into_iter()
                .fold(
                    Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]),
                    Expr::app,
                ),
                type_: proposition.clone(),
            };
        } else {
            condition = self.finish_term(condition, Some(&proposition))?;
        }
        let target = match expected {
            Some(expected) => self.instantiate(&expected)?,
            None => {
                let sort = self.type_expected()?;
                self.hole(sort)?
            }
        };
        let target_type = self
            .known_type(&target)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let function = self.constant(&Name::from_components([if parts.binds_evidence {
            "dite"
        } else {
            "ite"
        }]))?;
        let function = self.match_apply(
            function,
            Typed {
                value: target.clone(),
                type_: target_type,
            },
        )?;
        let function = self.match_apply(function, condition)?;
        // The condition is retained as written. Normalizing it before posing
        // `Decidable c` would change instance selection (fln-52qv).
        let function = self.insert_implicits(function, ImplicitInsertion::ExplicitArgument)?;
        self.resolve_instances(false)?;
        Ok(ConditionalBuild {
            parts,
            saved: self.txn.lctx.clone(),
            target,
            function,
            cursor: 0,
            branch_scope_depth: self.well_founded_branch_depth(),
        })
    }

    pub(in crate::source) fn next_conditional_branch<'a>(
        &mut self,
        state: &mut ConditionalBuild<'a>,
    ) -> Result<MatchStep<'a>, NatDefinitionElabError> {
        self.txn.lctx = state.saved.clone();
        let syntax = match state.cursor {
            0 => state.parts.yes,
            1 => state.parts.no,
            _ => {
                return Ok(MatchStep::Complete(
                    self.finish_term(state.function.clone(), Some(&state.target))?,
                ));
            }
        };
        let telescope = self.whnf(&state.function.type_)?;
        let ExprNode::ForallE { binder_type, .. } = telescope.node() else {
            return Err(error(MatchError::ExpectedCondition));
        };
        let domain = binder_type.clone();
        let mut expected = domain.clone();
        let mut locals = Vec::new();
        if state.parts.binds_evidence {
            let telescope = self.whnf(&domain)?;
            let ExprNode::ForallE {
                binder_type,
                binder_info,
                body,
                ..
            } = telescope.node()
            else {
                return Err(error(MatchError::ExpectedCondition));
            };
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                state.parts.binding.cloned().unwrap_or_else(Name::anonymous),
                binder_type.clone(),
                *binder_info,
            );
            locals.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("conditional evidence")
                    .clone(),
            );
            expected = self.substitute(body, &Expr::fvar(id))?;
        }
        // Even a nondependent branch needs a lexical cache boundary: a
        // recursive call prepared in one arm must not escape into its sibling.
        if let Some(depth) = state.branch_scope_depth {
            self.enter_well_founded_branch(depth)?;
        }
        Ok(MatchStep::Branch {
            syntax,
            expected,
            binders: BranchBinders {
                unrefined: HashSet::new(),
                hypotheses: Vec::new(),
                locals,
                type_: domain,
            },
        })
    }

    pub(in crate::source) fn accept_conditional_branch(
        &mut self,
        state: &mut ConditionalBuild<'_>,
        binders: BranchBinders,
        mut branch: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.resolve_instances(false)?;
        self.flush(false)?;
        branch.value = self.instantiate(&branch.value)?;
        branch.type_ = self.instantiate(&branch.type_)?;
        self.capture_bound_metavars(&binders.locals, &state.saved, &mut branch)?;
        if self.capture_bound_coercions(&binders.locals, &state.saved, &branch)? {
            branch.value = self.instantiate(&branch.value)?;
        }
        for local in &binders.locals {
            let value = branch
                .value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            branch.value = Expr::lam(
                local.user_name.clone(),
                self.instantiate(&local.type_)?,
                value,
                local.binder_info,
            );
        }
        branch.type_ = binders.type_;
        self.txn.lctx = state.saved.clone();
        if let Some(depth) = state.branch_scope_depth {
            self.leave_well_founded_branch(depth)?;
        }
        state.function = self.match_apply(state.function.clone(), branch)?;
        state.cursor += 1;
        Ok(())
    }
}
