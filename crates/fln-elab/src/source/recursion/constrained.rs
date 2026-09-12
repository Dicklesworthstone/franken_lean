//! Conditional recursion hypotheses for source functions at constrained indices.
//!
//! The ordinary equation-elimination compiler constructs the recursor. This
//! module replaces only syntactic calls on direct children, applying the actual
//! child hypothesis to source arguments and checked reflexive equations.
//! Hidden hypotheses are absent while user branch syntax is elaborated.
use super::*;
use crate::source::tactics::ProofGoal;

#[derive(Clone)]
enum Argument {
    Source(usize),
    Equation,
}

#[derive(Clone)]
pub(in crate::source) struct ConstrainedBranch {
    arguments: Vec<Argument>,
    children: Vec<(Expr, LocalDecl)>,
    hidden: Vec<LocalDecl>,
}

impl Context {
    /// Only dependencies of uniform family parameters stay fixed. Other source
    /// arguments are returned parameters of the conditional recursive motive.
    pub(in crate::source) fn constrained_recursive_parameters(
        &mut self,
        parameters: &[Expr],
    ) -> Result<HashSet<FVarId>, NatDefinitionElabError> {
        let source = self
            .recursion
            .as_ref()
            .expect("source recursion specification")
            .parameters
            .clone();
        let mut fixed = HashSet::new();
        for parameter in parameters {
            fixed.extend(self.elimination_reads(parameter)?);
        }
        for local in self.txn.lctx.clone().decls().iter().rev() {
            self.tick()?;
            if fixed.contains(&local.id) {
                fixed.extend(self.elimination_reads(&local.type_)?);
                if let Some(value) = &local.value {
                    fixed.extend(self.elimination_reads(value)?);
                }
            }
        }
        Ok(source
            .iter()
            .filter(|p| !fixed.contains(&p.id))
            .map(|p| p.id.clone())
            .collect())
    }

    /// A private checked alias survives index substitutions and source-name
    /// shadowing. It introduces a definition, never an additional assumption.
    pub(in crate::source) fn recursive_child_alias(
        &mut self,
        branch: &mut ProofGoal,
        child: &LocalDecl,
    ) -> Result<Name, NatDefinitionElabError> {
        let name = self.fresh_name()?;
        let local = LocalDecl {
            id: FVarId(name.clone()),
            user_name: name.clone(),
            type_: child.type_.clone(),
            value: Some(Expr::fvar(child.id.clone())),
            binder_info: BinderInfo::Default,
            index: self.txn.lctx.len(),
        };
        crate::source::tactics::eliminate::add_local(&mut self.txn.lctx, &local);
        branch.introduced.push(local);
        Ok(name)
    }

    pub(super) fn recursive_alias_value(
        &mut self,
        expr: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut value = expr.clone();
        let mut seen = HashSet::new();
        while let ExprNode::FVar { id } = value.node() {
            self.tick()?;
            if !seen.insert(id.clone()) {
                return Err(error(RecursionError::NotDecreasing));
            }
            let Some(local) = self.txn.lctx.find(id) else {
                break;
            };
            let Some(next) = &local.value else {
                break;
            };
            if !matches!(next.node(), ExprNode::FVar { .. }) {
                break;
            }
            value = next.clone();
        }
        Ok(value)
    }

    pub(in crate::source) fn register_constrained_recursive_branch(
        &mut self,
        branch: &mut ProofGoal,
        hypotheses: &[(Name, Name)],
        reverted: &[LocalDecl],
        equations: &[Name],
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = branch.lctx.clone();
        let parameters = self
            .recursion
            .as_ref()
            .expect("source recursion specification")
            .parameters
            .clone();
        let mut arguments = Vec::new();
        for local in reverted.iter().filter(|local| local.value.is_none()) {
            self.tick()?;
            if let Some(position) = parameters.iter().position(|p| p.id == local.id) {
                arguments.push(Argument::Source(position));
            } else if equations.contains(&local.user_name) {
                arguments.push(Argument::Equation);
            } else {
                return Err(error(RecursionError::ChangedParameter));
            }
        }
        let mut children = Vec::new();
        let mut hidden = Vec::new();
        for (hypothesis, child) in hypotheses {
            let ih = branch
                .lctx
                .find_by_user_name(hypothesis)
                .cloned()
                .ok_or_else(|| error(RecursionError::NotDecreasing))?;
            let child = branch
                .lctx
                .find_by_user_name(child)
                .cloned()
                .ok_or_else(|| error(RecursionError::NotDecreasing))?;
            let child = self.recursive_alias_value(&Expr::fvar(child.id))?;
            hidden.push(ih.clone());
            children.push((child, ih));
        }
        let ids: HashSet<_> = hidden.iter().map(|local| local.id.clone()).collect();
        let mut visible = LocalContext::new();
        for local in branch.lctx.decls() {
            if !ids.contains(&local.id) {
                crate::source::tactics::eliminate::add_local(&mut visible, local);
            }
        }
        branch.lctx = visible;
        self.txn.lctx = branch.lctx.clone();
        self.recursion
            .as_mut()
            .expect("source recursion specification")
            .equation_goals
            .insert(
                branch.id.clone(),
                ConstrainedBranch {
                    arguments,
                    children,
                    hidden,
                },
            );
        Ok(())
    }

    /// Sufficient checked reflexivity for generated premises. All source
    /// arguments remain in the actual hypothesis application and cross K1.
    fn recursive_equation_refl(&mut self, domain: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let domain = self.whnf(domain)?;
        let mut head = &domain;
        let mut args = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            args.push(a.clone());
            head = f;
        }
        args.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(error(RecursionError::ChangedIndex));
        };
        let [universe] = levels.as_slice() else {
            return Err(error(RecursionError::ChangedIndex));
        };
        let (alpha, left, beta, right) = if name == &Name::from_components(["HEq"]) {
            let [alpha, left, beta, right] = args.as_slice() else {
                return Err(error(RecursionError::ChangedIndex));
            };
            (alpha, left, beta, right)
        } else if name == &Name::from_components(["Eq"]) {
            let [alpha, left, right] = args.as_slice() else {
                return Err(error(RecursionError::ChangedIndex));
            };
            (alpha, left, alpha, right)
        } else {
            return Err(error(RecursionError::ChangedIndex));
        };
        for (a, b) in [(alpha, beta), (left, right)] {
            let a = self.whnf(a)?;
            let b = self.whnf(b)?;
            if a != b
                && (a.has_loose_bvars()
                    || b.has_loose_bvars()
                    || !self.proof_types_match(&a, &b)?)
            {
                return Err(error(RecursionError::ChangedIndex));
            }
        }
        Ok([alpha.clone(), left.clone()].into_iter().fold(
            Expr::const_(Name::str(name.clone(), "refl"), vec![universe.clone()]),
            Expr::app,
        ))
    }

    /// Partial calls are legal only after the decreasing input is supplied.
    /// Eta-complete the remaining telescope with fresh locals, then close it
    /// capture-avoidantly. Loose variables can refer to an enclosing source
    /// lambda: lift them before adding each new binder.
    fn constrained_call(
        &mut self,
        arguments: &[Expr],
        plan: &ConstrainedBranch,
    ) -> Result<Expr, NatDefinitionElabError> {
        let recursion = self
            .recursion
            .as_ref()
            .expect("source recursion specification");
        if arguments.len() <= recursion.decreasing {
            return Err(error(RecursionError::PartialApplication));
        }
        let count = recursion.parameters.len();
        if arguments.len() >= count {
            return self.constrained_saturated_call(arguments, plan);
        }
        let mut type_ = recursion.reference.type_.clone();
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut args = arguments.to_vec();
            let mut locals = Vec::new();
            for position in 0..count {
                self.tick()?;
                let current = self.whnf(&type_)?;
                let ExprNode::ForallE {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } = current.node()
                else {
                    return Err(error(RecursionError::PartialApplication));
                };
                if position >= args.len() {
                    let id = FVarId(self.fresh_name()?);
                    let local = self
                        .txn
                        .lctx
                        .add_param(
                            id.clone(),
                            Name::anonymous(),
                            binder_type.clone(),
                            *binder_info,
                        )
                        .clone();
                    locals.push(local);
                    args.push(Expr::fvar(id));
                }
                type_ = self.substitute(body, &args[position])?;
            }
            let mut value = self.constrained_saturated_call(&args, plan)?;
            for local in locals.into_iter().rev() {
                self.tick()?;
                value = value
                    .lift_loose(0, 1)
                    .and_then(|value| value.abstract_fvar(&local.id, 0))
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                value = Expr::lam(local.user_name, local.type_, value, local.binder_info);
            }
            Ok(value)
        })();
        self.txn.lctx = saved;
        result
    }

    fn constrained_saturated_call(
        &mut self,
        arguments: &[Expr],
        plan: &ConstrainedBranch,
    ) -> Result<Expr, NatDefinitionElabError> {
        let recursion = self
            .recursion
            .as_ref()
            .expect("source recursion specification");
        let parameters = recursion.parameters.clone();
        let decreasing = recursion.decreasing;
        if arguments.len() < parameters.len() {
            return Err(error(RecursionError::PartialApplication));
        }
        let varying: HashSet<_> = plan
            .arguments
            .iter()
            .filter_map(|arg| match arg {
                Argument::Source(position) => Some(*position),
                Argument::Equation => None,
            })
            .collect();
        for (position, (argument, parameter)) in arguments.iter().zip(&parameters).enumerate() {
            if !varying.contains(&position)
                && !self.fixed_recursive_argument(argument, parameter)?
            {
                return Err(error(RecursionError::ChangedParameter));
            }
        }
        let child = self.recursive_alias_value(&arguments[decreasing])?;
        let hypothesis = plan
            .children
            .iter()
            .find(|(field, _)| *field == child)
            .map(|(_, ih)| ih)
            .ok_or_else(|| error(RecursionError::NotDecreasing))?;
        let mut value = Expr::fvar(hypothesis.id.clone());
        let mut type_ = hypothesis.type_.clone();
        for argument in &plan.arguments {
            self.tick()?;
            let current = self.whnf(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = current.node()
            else {
                return Err(error(RecursionError::ChangedIndex));
            };
            let argument = match argument {
                Argument::Source(position) => arguments[*position].clone(),
                Argument::Equation => self.recursive_equation_refl(binder_type)?,
            };
            type_ = self.substitute(body, &argument)?;
            value = Expr::app(value, argument);
        }
        Ok(arguments
            .iter()
            .skip(parameters.len())
            .cloned()
            .fold(value, Expr::app))
    }

    pub(in crate::source) fn lower_constrained_recursive_calls(
        &mut self,
        expr: &Expr,
        plan: &ConstrainedBranch,
    ) -> Result<Expr, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        for local in &plan.hidden {
            crate::source::tactics::eliminate::add_local(&mut self.txn.lctx, local);
        }
        let result = self.lower_constrained_inner(expr, plan);
        self.txn.lctx = saved;
        result
    }

    fn lower_constrained_inner(
        &mut self,
        expr: &Expr,
        plan: &ConstrainedBranch,
    ) -> Result<Expr, NatDefinitionElabError> {
        enum Task<'a> {
            Visit(&'a Expr),
            Node(&'a Expr),
            Call(&'a Expr, Vec<&'a Expr>),
        }
        let marker = self
            .recursion
            .as_ref()
            .expect("source recursion specification")
            .marker
            .clone();
        let mut tasks = vec![Task::Visit(expr)];
        let mut done: HashMap<usize, Expr> = HashMap::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(input) => {
                    if done.contains_key(&input.allocation_identity()) {
                        continue;
                    }
                    if !input.has_fvar() {
                        done.insert(input.allocation_identity(), input.clone());
                        continue;
                    }
                    let mut head = input;
                    let mut args = Vec::new();
                    while let ExprNode::App { f, a } = head.node() {
                        self.tick()?;
                        args.push(a);
                        head = f;
                    }
                    if matches!(head.node(), ExprNode::FVar { id } if *id == marker) {
                        args.reverse();
                        tasks.push(Task::Call(input, args.clone()));
                        tasks.extend(args.into_iter().rev().map(Task::Visit));
                    } else {
                        tasks.push(Task::Node(input));
                        tasks.extend(children(input).into_iter().flatten().map(Task::Visit));
                    }
                }
                Task::Call(input, args) => {
                    let args: Vec<_> = args
                        .iter()
                        .map(|arg| done[&arg.allocation_identity()].clone())
                        .collect();
                    let result = self.constrained_call(&args, plan)?;
                    done.insert(input.allocation_identity(), result);
                }
                Task::Node(input) => {
                    let get = |value: &Expr| done[&value.allocation_identity()].clone();
                    let result = match input.node() {
                        ExprNode::App { f, a } => Expr::app(get(f), get(a)),
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::lam(
                            binder_name.clone(),
                            get(binder_type),
                            get(body),
                            *binder_info,
                        ),
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::forall_e(
                            binder_name.clone(),
                            get(binder_type),
                            get(body),
                            *binder_info,
                        ),
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } => Expr::let_e(
                            decl_name.clone(),
                            get(type_),
                            get(value),
                            get(body),
                            *non_dep,
                        ),
                        ExprNode::MData { data, expr } => Expr::mdata(data.clone(), get(expr)),
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => Expr::proj(struct_name.clone(), *idx, get(expr)),
                        _ => input.clone(),
                    };
                    done.insert(input.allocation_identity(), result);
                }
            }
        }
        Ok(done
            .remove(&expr.allocation_identity())
            .expect("postorder root"))
    }
}
