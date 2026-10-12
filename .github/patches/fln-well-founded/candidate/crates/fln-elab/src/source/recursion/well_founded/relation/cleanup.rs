//! The relation-facing part of the pin's `clean_wf`. Only well-founded
//! dictionary receivers and the named wrappers selected by that tactic are
//! unfolded. Arithmetic expressions and arbitrary relation bodies retain
//! their ordinary opacity, and the raw obligation remains the admission goal.
use super::*;

impl Context {
    fn decreasing_inverse_image(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (head, arguments) = operators::spine(expression);
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        if name != &Name::from_components(["InvImage"]) || arguments.len() < 4 {
            return Ok(None);
        }
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        if definition.safety != DefinitionSafety::Safe {
            return Ok(None);
        }
        // Open the actual selected definition, including partial applications.
        // Its relation binders are scoped normally by the worklist below.
        let value = self.unfold_selected_definition(expression, &definition)?;
        Ok((value != *expression).then_some(value))
    }

    fn decreasing_size_of_nat(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (head, arguments) = operators::spine(expression);
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        if name != &Name::from_components(["SizeOf", "sizeOf"])
            || arguments.len() < 2
            || arguments[0] != nat_const()
        {
            return Ok(None);
        }
        let canonical_name = Name::from_components(["instSizeOfNat"]);
        if !matches!(self.txn.env.find(&canonical_name),
            Some(ConstantInfo::Defn(definition))
                if definition.safety == DefinitionSafety::Safe
                    && definition.base.level_params.is_empty())
        {
            return Ok(None);
        }
        let canonical = Expr::const_(canonical_name, Vec::new());
        if arguments[1] != canonical {
            // Compare the complete selected dictionary. A custom Nat SizeOf
            // relation must not be replaced merely because its carrier is Nat.
            let original = self.clone();
            let equal = (|| {
                self.flush(false)?;
                let mut budget = UnificationBudget::new(self.kernel);
                budget.transparency = UnificationTransparency::Instances;
                match self.txn.unify(&arguments[1], &canonical, budget) {
                    Ok(report) => {
                        assert!(report.awakened.is_empty(), "private source queue");
                        Ok(true)
                    }
                    Err(UnificationError::Deferred(reason))
                        if !matches!(
                            reason,
                            crate::constraint::unify::UnificationDeferred::InvalidLocalContext
                                | crate::constraint::unify::UnificationDeferred::UnknownMetavariable(_)
                        ) =>
                    {
                        Ok(false)
                    }
                    Err(UnificationError::AssignmentCheck { outcome, .. })
                        if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })) =>
                    {
                        Ok(false)
                    }
                    Err(problem) => Err(failure(SourceInferenceError::Unification(Box::new(
                        problem,
                    )))),
                }
            })();
            let spent = self.txn.budget.heartbeats_consumed;
            *self = original;
            self.txn.budget.heartbeats_consumed = spent;
            if !equal? {
                return Ok(None);
            }
        }
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        if definition.safety != DefinitionSafety::Safe {
            return Ok(None);
        }
        // Reduce only the selected projection and its canonical dictionary.
        // Apply its real checked field afterward at None transparency, so a
        // source subtraction is never delta-normalized as a rewrite match.
        let projection = Expr::app(Expr::app(head, nat_const()), canonical);
        let function = self.unfold_selected_definition(&projection, &definition)?;
        let mut value =
            self.reduce_source_head(&function, UnificationTransparency::Instances, false)?;
        for argument in arguments.into_iter().skip(2) {
            self.tick()?;
            value = Expr::app(value, argument);
        }
        value = self.reduce_source_head(&value, UnificationTransparency::None, false)?;
        Ok((value != *expression).then_some(value))
    }

    fn decreasing_dictionary_head(
        &mut self,
        dictionary: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut value = dictionary.clone();
        loop {
            self.tick()?;
            let (head, arguments) = operators::spine(&value);
            let selected = matches!(head.node(), ExprNode::Const { name, .. }
                if [
                    Name::from_components(["invImage"]),
                    Name::from_components(["Prod", "lex"]),
                    Name::from_components(["Nat", "lt_wfRel"]),
                    Name::from_components(["sizeOfWFRel"]),
                    Name::from_components(["measure"]),
                ].contains(name));
            let mut next = value.clone();
            if selected
                && let ExprNode::Const { name, levels } = head.node()
                && let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned()
                && definition.safety == DefinitionSafety::Safe
                && definition.base.level_params.len() == levels.len()
            {
                // These are explicit unfold entries in Init.WFTactics, so a
                // later reducibility attribute does not erase their meaning.
                next = self.instantiate_params(
                    &definition.value,
                    &definition.base.level_params,
                    levels,
                )?;
                for argument in arguments {
                    self.tick()?;
                    next = Expr::app(next, argument);
                }
                next = self.reduce_source_head(&next, UnificationTransparency::None, true)?;
            } else {
                // Class projections expose reducible/instance receivers. This
                // never unfolds an arbitrary semireducible relation body.
                next = self.reduce_source_head(&next, UnificationTransparency::Instances, true)?;
            }
            if next == value {
                return Ok(value);
            }
            value = next;
        }
    }

    fn decreasing_relation_projection(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (head, arguments) = operators::spine(expression);
        let (dictionary, trailing) = match head.node() {
            ExprNode::Proj {
                struct_name,
                idx: 0,
                expr,
            } if struct_name == &Name::from_components(["WellFoundedRelation"]) => {
                (expr.clone(), arguments.as_slice())
            }
            ExprNode::Const { name, .. }
                if name == &Name::from_components(["WellFoundedRelation", "rel"])
                    && arguments.len() >= 2 =>
            {
                (arguments[1].clone(), &arguments[2..])
            }
            _ => return Ok(None),
        };
        let dictionary = self.decreasing_dictionary_head(&dictionary)?;
        let (constructor, fields) = operators::spine(&dictionary);
        if !matches!(constructor.node(), ExprNode::Const { name, .. }
            if name == &Name::from_components(["WellFoundedRelation", "mk"]))
            || fields.len() != 3
        {
            return Ok(None);
        }
        let mut relation = fields[1].clone();
        for argument in trailing {
            self.tick()?;
            relation = Expr::app(relation, argument.clone());
        }
        Ok(Some(relation))
    }

    pub(in crate::source) fn clean_decreasing_relation(
        &mut self,
        relation: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        enum Work {
            Visit(Expr),
            Application {
                head: Expr,
                prefix: Vec<Expr>,
                children: usize,
                suffix: Vec<Expr>,
            },
            Lambda {
                local: LocalDecl,
                saved: LocalContext,
            },
        }
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut work = vec![Work::Visit(relation.clone())];
            let mut values = Vec::new();
            while let Some(task) = work.pop() {
                self.tick()?;
                match task {
                    Work::Visit(mut value) => {
                        loop {
                            value = self.reduce_source_head(
                                &value,
                                UnificationTransparency::None,
                                true,
                            )?;
                            if let Some(next) = self.decreasing_inverse_image(&value)? {
                                value = next;
                                continue;
                            }
                            let Some(next) = self.decreasing_relation_projection(&value)? else {
                                break;
                            };
                            value = next;
                        }
                        if let ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } = value.node()
                        {
                            // Dependent PSigma relations contain a family of
                            // dictionaries. Open its binder normally; never
                            // run a reducer on an unscoped loose bound variable.
                            let saved = self.txn.lctx.clone();
                            let id = FVarId(self.fresh_name()?);
                            self.txn.lctx.add_param(
                                id.clone(),
                                binder_name.clone(),
                                binder_type.clone(),
                                *binder_info,
                            );
                            let local = self.txn.lctx.find(&id).unwrap().clone();
                            let body = self.substitute(body, &Expr::fvar(id))?;
                            work.push(Work::Lambda { local, saved });
                            work.push(Work::Visit(body));
                            continue;
                        }
                        let (head, mut arguments) = operators::spine(&value);
                        // InvImage's freshly opened relation binders may be
                        // passed through canonical Nat SizeOf projections.
                        // User measure operands have not been attached yet.
                        let mut simplified = false;
                        let start = arguments.len().saturating_sub(2);
                        for operand in &mut arguments[start..] {
                            self.tick()?;
                            if let Some(next) = self.decreasing_size_of_nat(operand)? {
                                *operand = next;
                                simplified = true;
                            }
                        }
                        if simplified {
                            value = head.clone();
                            for argument in &arguments {
                                self.tick()?;
                                value = Expr::app(value, argument.clone());
                            }
                        }
                        let children = if matches!(head.node(), ExprNode::Const { name, .. }
                            if name == &Name::from_components(["Prod", "Lex"])
                                || name == &Name::from_components(["PSigma", "Lex"]))
                            && arguments.len() >= 4
                        {
                            2
                        } else if matches!(head.node(), ExprNode::Const { name, .. }
                            if name == &Name::from_components(["InvImage"]))
                            && arguments.len() >= 4
                        {
                            1
                        } else {
                            values.push(value);
                            continue;
                        };
                        work.push(Work::Application {
                            head,
                            prefix: arguments[..2].to_vec(),
                            children,
                            suffix: arguments[2 + children..].to_vec(),
                        });
                        for child in arguments[2..2 + children].iter().rev() {
                            work.push(Work::Visit(child.clone()));
                        }
                    }
                    Work::Application {
                        head,
                        prefix,
                        children,
                        suffix,
                    } => {
                        let offset = values
                            .len()
                            .checked_sub(children)
                            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                        let children = values.split_off(offset);
                        let mut result = head;
                        for argument in prefix.into_iter().chain(children).chain(suffix) {
                            self.tick()?;
                            result = Expr::app(result, argument);
                        }
                        values.push(result);
                    }
                    Work::Lambda { local, saved } => {
                        let body = values
                            .pop()
                            .ok_or_else(|| failure(SourceInferenceError::Scope))?
                            .abstract_fvar(&local.id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                        let value = if let ExprNode::App { f, a } = body.node()
                            && matches!(a.node(), ExprNode::BVar { idx: 0 })
                            && !f.has_loose_bvars()
                        {
                            // Keep partial LT.lt applications recognizable to
                            // arithmetic instead of introducing an avoidable
                            // lambda over the same checked relation.
                            f.clone()
                        } else {
                            Expr::lam(local.user_name, local.type_, body, local.binder_info)
                        };
                        self.txn.lctx = saved;
                        values.push(value);
                    }
                }
            }
            if values.len() != 1 {
                return Err(failure(SourceInferenceError::Scope));
            }
            Ok(values.pop().unwrap())
        })();
        self.txn.lctx = saved;
        result
    }
}
