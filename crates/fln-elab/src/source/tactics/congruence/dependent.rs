//! General dependent congruence for a fixed function and its full telescope.
//!
//! The theorem quantifies the right-hand arguments at their dependent types.
//! Its proof eliminates one same-typed argument equality at a time, with ALL
//! later arguments inside the motive. No cast is guessed and no arbitrary
//! expression occurrence is replaced. Proof arguments need no equality premise:
//! after earlier indices are eliminated they coincide by proof irrelevance.
use super::*;

struct Parameter {
    domain: Expr,
    level: Level,
    proof: bool,
}

impl Context {
    fn congruence_heq(
        &mut self,
        parameter: &Parameter,
        left: Expr,
        right_domain: Expr,
        right: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        Ok([parameter.domain.clone(), left, right_domain, right]
            .into_iter()
            .fold(
                Expr::const_(
                    Name::from_components(["HEq"]),
                    vec![parameter.level.clone()],
                ),
                Expr::app,
            ))
    }

    fn congruence_binder(&mut self, domain: Expr) -> Result<LocalDecl, NatDefinitionElabError> {
        self.tick()?;
        let id = FVarId(self.fresh_name()?);
        let name = id.0.clone();
        self.txn
            .lctx
            .add_param(id.clone(), name, domain, BinderInfo::Default);
        self.txn
            .lctx
            .find(&id)
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::Scope))
    }

    fn congruence_abstract(
        &mut self,
        binder: &LocalDecl,
        body: Expr,
        lambda: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        let body = body
            .abstract_fvar(&binder.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        Ok(if lambda {
            Expr::lam(
                binder.user_name.clone(),
                binder.type_.clone(),
                body,
                BinderInfo::Default,
            )
        } else {
            Expr::forall_e(
                binder.user_name.clone(),
                binder.type_.clone(),
                body,
                BinderInfo::Default,
            )
        })
    }

    /// Build the suffix statement with the supplied right prefix. Every domain
    /// is obtained by specializing the function's telescope, not by replacing
    /// values in an expression (two argument positions may hold the same value).
    fn congruence_suffix(
        &mut self,
        mut right: Typed,
        left: &Typed,
        result_level: &Level,
        arguments: &[Expr],
        parameters: &[Parameter],
    ) -> Result<Expr, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut binders = Vec::new();
            for (left, parameter) in arguments.iter().zip(parameters) {
                self.tick()?;
                let current = self.whnf(&right.type_)?;
                let ExprNode::ForallE {
                    binder_type: domain,
                    body,
                    ..
                } = current.node()
                else {
                    return Err(failure(SourceInferenceError::ExpectedFunction));
                };
                let binder = self.congruence_binder(domain.clone())?;
                let variable = Expr::fvar(binder.id.clone());
                right.value = Expr::app(right.value, variable.clone());
                right.type_ = self.substitute(body, &variable)?;
                binders.push(binder);
                if !parameter.proof {
                    let equation =
                        self.congruence_heq(parameter, left.clone(), domain.clone(), variable)?;
                    binders.push(self.congruence_binder(equation)?);
                }
            }
            let mut target = [
                left.type_.clone(),
                left.value.clone(),
                right.type_,
                right.value,
            ]
            .into_iter()
            .fold(
                Expr::const_(Name::from_components(["HEq"]), vec![result_level.clone()]),
                Expr::app,
            );
            for binder in binders.iter().rev() {
                target = self.congruence_abstract(binder, target, false)?;
            }
            Ok(target)
        })();
        self.txn.lctx = saved;
        result
    }

    pub(super) fn congruence_dependent_application(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<Option<(Expr, Vec<ProofGoal>)>, NatDefinitionElabError> {
        let (head, left_args) = self.congruence_spine(left)?;
        let (other, right_args) = self.congruence_spine(right)?;
        if left_args.is_empty() || left_args.len() != right_args.len() {
            return Ok(None);
        }
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::Default;
        if !self.proof_types_match_with_budget(&head, &other, budget)? {
            return Ok(None);
        }
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let head_type = self
                .known_type(&head)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let mut prefixes = vec![(head.clone(), head_type.clone())];
            let mut parameters = Vec::new();
            for argument in &left_args {
                self.tick()?;
                let (prefix, type_) = prefixes.last().expect("head prefix");
                let type_ = self.whnf(type_)?;
                let ExprNode::ForallE {
                    binder_type: domain,
                    body,
                    ..
                } = type_.node()
                else {
                    return Ok(None);
                };
                let level = self.congruence_sort(domain)?;
                parameters.push(Parameter {
                    domain: domain.clone(),
                    proof: level.is_zero(),
                    level,
                });
                prefixes.push((
                    Expr::app(prefix.clone(), argument.clone()),
                    self.substitute(body, argument)?,
                ));
            }
            let (left_result, result_domain) = prefixes.last().expect("applied prefix").clone();
            let result_level = self.congruence_sort(&result_domain)?;
            let left_term = Typed {
                value: left_result.clone(),
                type_: result_domain.clone(),
            };
            let mut value = [result_domain.clone(), left_result.clone()]
                .into_iter()
                .fold(
                    Expr::const_(
                        Name::from_components(["HEq", "refl"]),
                        vec![result_level.clone()],
                    ),
                    Expr::app,
                );
            // Reverse construction is a heap iteration. Each motive closes over
            // its entire suffix; the minor is exactly the already-built proof
            // at the left endpoint. Thus dependent domains change together.
            for index in (0..left_args.len()).rev() {
                self.tick()?;
                self.txn.lctx = saved.clone();
                let parameter = &parameters[index];
                let binder = self.congruence_binder(parameter.domain.clone())?;
                let variable = Expr::fvar(binder.id.clone());
                if !parameter.proof {
                    let heq_type = self.congruence_heq(
                        parameter,
                        left_args[index].clone(),
                        parameter.domain.clone(),
                        variable.clone(),
                    )?;
                    let hypothesis = self.congruence_binder(heq_type)?;
                    let equation = Equation {
                        level: parameter.level.clone(),
                        domain: parameter.domain.clone(),
                        left: left_args[index].clone(),
                        right: variable.clone(),
                    };
                    let evidence = [
                        parameter.domain.clone(),
                        left_args[index].clone(),
                        variable,
                        Expr::fvar(hypothesis.id.clone()),
                    ]
                    .into_iter()
                    .fold(
                        Expr::const_(
                            Name::from_components(["eq_of_heq"]),
                            vec![parameter.level.clone()],
                        ),
                        Expr::app,
                    );
                    // Construct the motive using a fresh endpoint, with this
                    // endpoint present in the local context during type queries.
                    let endpoint = self.congruence_binder(parameter.domain.clone())?;
                    let point = Expr::fvar(endpoint.id.clone());
                    let (_, prefix_type) = &prefixes[index];
                    let prefix_type = self.whnf(prefix_type)?;
                    let ExprNode::ForallE { body, .. } = prefix_type.node() else {
                        return Ok(None);
                    };
                    let suffix_type = self.substitute(body, &point)?;
                    let suffix = self.congruence_suffix(
                        Typed {
                            value: Expr::app(prefixes[index].0.clone(), point.clone()),
                            type_: suffix_type,
                        },
                        &left_term,
                        &result_level,
                        &left_args[index + 1..],
                        &parameters[index + 1..],
                    )?;
                    let proof_domain = equality::equation(
                        parameter.level.clone(),
                        parameter.domain.clone(),
                        left_args[index].clone(),
                        point,
                    );
                    let inner =
                        Expr::lam(Name::anonymous(), proof_domain, suffix, BinderInfo::Default);
                    let motive = self.congruence_abstract(&endpoint, inner, true)?;
                    value = [
                        equation.domain,
                        equation.left,
                        motive,
                        value,
                        equation.right,
                        evidence,
                    ]
                    .into_iter()
                    .fold(
                        Expr::const_(
                            Name::from_components(["Eq", "rec"]),
                            vec![Level::zero(), equation.level],
                        ),
                        Expr::app,
                    );
                    value = self.congruence_abstract(&hypothesis, value, true)?;
                }
                value = self.congruence_abstract(&binder, value, true)?;
            }
            self.txn.lctx = saved.clone();
            let mut children = Vec::new();
            let mut right_type = head_type;
            for ((a, b), parameter) in left_args.iter().zip(&right_args).zip(&parameters) {
                self.tick()?;
                let current = self.whnf(&right_type)?;
                let ExprNode::ForallE {
                    binder_type: right_domain,
                    body,
                    ..
                } = current.node()
                else {
                    return Ok(None);
                };
                value = Expr::app(value, b.clone());
                right_type = self.substitute(body, b)?;
                if parameter.proof {
                    continue;
                }
                let same_domain =
                    self.proof_types_match_with_budget(&parameter.domain, right_domain, budget)?;
                let evidence = if same_domain && self.proof_types_match_with_budget(a, b, budget)? {
                    [parameter.domain.clone(), a.clone()].into_iter().fold(
                        Expr::const_(
                            Name::from_components(["HEq", "refl"]),
                            vec![parameter.level.clone()],
                        ),
                        Expr::app,
                    )
                } else if same_domain {
                    let equation = Equation {
                        level: parameter.level.clone(),
                        domain: parameter.domain.clone(),
                        left: a.clone(),
                        right: b.clone(),
                    };
                    let (hole, child) = self.proof_goal(equation.target())?;
                    children.push(child);
                    let minor = [parameter.domain.clone(), a.clone()].into_iter().fold(
                        Expr::const_(
                            Name::from_components(["HEq", "refl"]),
                            vec![parameter.level.clone()],
                        ),
                        Expr::app,
                    );
                    self.congruence_transport(
                        &equation,
                        hole,
                        |point| {
                            [
                                parameter.domain.clone(),
                                a.clone(),
                                parameter.domain.clone(),
                                point,
                            ]
                            .into_iter()
                            .fold(
                                Expr::const_(
                                    Name::from_components(["HEq"]),
                                    vec![parameter.level.clone()],
                                ),
                                Expr::app,
                            )
                        },
                        minor,
                    )?
                } else {
                    let target =
                        self.congruence_heq(parameter, a.clone(), right_domain.clone(), b.clone())?;
                    let (hole, child) = self.proof_goal(target)?;
                    children.push(child);
                    hole
                };
                value = Expr::app(value, evidence);
            }
            Ok(Some((value, children)))
        })();
        self.txn.lctx = saved;
        result
    }
}
