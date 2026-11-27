//! Preserve the actual structural hypotheses across source scopes and splits.
//!
//! A later discriminant can force the first child's type and hypothesis into
//! its generalized telescope. Private names survive that reconstruction; the
//! current local context, not a stale variable identity, determines scope.
//! Recursive calls are lowered while those locals are still open. Ordinary
//! proof and instance search never receive these compiler-only hypotheses.
use super::*;

impl Context {
    pub(in crate::source) fn is_private_self(&self, id: &FVarId) -> bool {
        self.private_self_ids.contains(id)
            || self
                .recursion
                .iter()
                .chain(&self.enclosing_recursions)
                .any(|recursion| &recursion.marker == id)
    }

    pub(in crate::source) fn is_matrix_hypothesis(&self, local: &LocalDecl) -> bool {
        self.is_private_self(&local.id)
            || self
                .well_founded
                .as_ref()
                .is_some_and(|state| state.hides(local))
            || self
                .mutual_structural_member
                .as_ref()
                .is_some_and(|member| member.hides(local))
            || self
                .recursion
                .iter()
                .chain(&self.enclosing_recursions)
                .any(|recursion| recursion.matrix_hidden.contains(&local.user_name))
    }

    pub(in crate::source) fn register_matrix_hypotheses(
        &mut self,
        locals: &mut Vec<LocalDecl>,
        hypotheses: &[(FVarId, FVarId)],
    ) -> Result<(), NatDefinitionElabError> {
        for (child, hypothesis) in hypotheses {
            self.tick()?;
            let name = self.fresh_name()?;
            let declaration = locals
                .iter_mut()
                .find(|local| &local.id == hypothesis)
                .ok_or_else(|| error(RecursionError::NotDecreasing))?;
            declaration.user_name = name.clone();
            declaration.index = self.txn.lctx.len();
            crate::source::tactics::eliminate::add_local(&mut self.txn.lctx, declaration);
            let child = self
                .txn
                .lctx
                .find(child)
                .cloned()
                .ok_or_else(|| error(RecursionError::NotDecreasing))?;
            let alias_name = self.fresh_name()?;
            let alias = LocalDecl {
                id: FVarId(alias_name.clone()),
                user_name: alias_name.clone(),
                type_: child.type_,
                value: Some(Expr::fvar(child.id)),
                binder_info: BinderInfo::Default,
                index: self.txn.lctx.len(),
            };
            crate::source::tactics::eliminate::add_local(&mut self.txn.lctx, &alias);
            locals.push(alias);
            let recursion = self.recursion.as_mut().expect("recursive matrix branch");
            recursion.matrix_hidden.insert(name.clone());
            recursion.matrix_hypotheses.push((alias_name, name));
        }
        Ok(())
    }

    /// Only complete source applications whose structural argument is already
    /// present are lowered here. Escaping bare markers remain subject to the
    /// final whole-branch traversal, including unused values and annotations.
    pub(in crate::source) fn lower_matrix_call(
        &mut self,
        value: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        if let Some(lowered) = self.lower_mutual_structural_call(value)? {
            return Ok(lowered);
        }
        if !value.has_fvar() || (self.recursion.is_none() && self.enclosing_recursions.is_empty()) {
            return Ok(value.clone());
        }
        let mut head = value;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        let ExprNode::FVar { id } = head.node() else {
            return Ok(value.clone());
        };
        let Some(recursion) = self
            .recursion
            .iter()
            .chain(self.enclosing_recursions.iter().rev())
            .find(|recursion| &recursion.marker == id)
            .filter(|recursion| {
                !recursion.pending
                    && (!recursion.matrix_hypotheses.is_empty() || recursion.course_name.is_some())
                    && arguments.len() > recursion.decreasing
            })
            .cloned()
        else {
            return Ok(value.clone());
        };
        arguments.reverse();
        let mut instantiated = Vec::with_capacity(arguments.len());
        for argument in arguments {
            self.tick()?;
            instantiated.push(self.instantiate(&argument)?);
        }
        // Implicit arguments up through the decreasing parameter (e.g.
        // `Nat.mul_pos (Nat.pow_pos h) h`) may still be unsolved holes until
        // the enclosing application unifies with the branch goal. Leave the
        // marker intact for the branch's post-flush lowering pass rather than
        // rejecting an unsolved hole as `NotDecreasing`.
        if instantiated[..=recursion.decreasing]
            .iter()
            .any(Expr::has_expr_mvar)
        {
            return Ok(value.clone());
        }
        let marker = recursion.marker.clone();
        if recursion.course_name.is_some() {
            let active = self.recursion.replace(recursion);
            let result = self.defer_selected_recursive_lowering(value, |context| {
                context.lower_course_call(&instantiated)
            });
            self.recursion = active;
            return result;
        }
        let pairs = recursion.matrix_hypotheses.clone();
        let mut hypotheses = Vec::new();
        for (child, hypothesis) in pairs {
            self.tick()?;
            let Some(child) = self.txn.lctx.find_by_user_name(&child).cloned() else {
                continue;
            };
            let Some(hypothesis) = self.txn.lctx.find_by_user_name(&hypothesis).cloned() else {
                continue;
            };
            let child = self.recursive_alias_value(&Expr::fvar(child.id))?;
            if let ExprNode::FVar { id } = child.node() {
                hypotheses.push((id.clone(), hypothesis.id));
            }
        }
        if hypotheses.is_empty() {
            return Ok(value.clone());
        }
        let mut application = Expr::fvar(marker);
        for argument in instantiated {
            self.tick()?;
            application = Expr::app(application, self.recursive_alias_value(&argument)?);
        }
        // The enclosing recursion remains the owner of a call made in a local
        // helper. In particular, requests to generalize its earlier arguments
        // must reach its checkpoint, not the helper's structural candidate.
        let active = self.recursion.replace(recursion);
        let result = self.lower_recursive_calls(&application, &hypotheses);
        self.recursion = active;
        result
    }

    /// Lower recursive calls that [`Self::lower_matrix_call`] deferred while
    /// implicit arguments through the decreasing parameter still contained
    /// metavariables, before an inner match closes its generalized hypotheses.
    pub(in crate::source) fn lower_deferred_matrix_calls(
        &mut self,
        value: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        if !value.has_fvar()
            || !self
                .recursion
                .iter()
                .chain(self.enclosing_recursions.iter())
                .any(|recursion| {
                    !recursion.pending
                        && (!recursion.matrix_hypotheses.is_empty()
                            || recursion.course_name.is_some())
                })
        {
            return Ok(value.clone());
        }
        enum Task<'a> {
            Visit(&'a Expr),
            Node(&'a Expr),
            Call(&'a Expr, FVarId, Vec<&'a Expr>),
        }
        let mut done: HashMap<usize, Expr> = HashMap::new();
        let mut tasks = vec![Task::Visit(value)];
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(expr) => {
                    let key = expr.allocation_identity();
                    if done.contains_key(&key) {
                        continue;
                    }
                    if !expr.has_fvar() {
                        done.insert(key, expr.clone());
                        continue;
                    }
                    let mut head = expr;
                    let mut arguments = Vec::new();
                    while let ExprNode::App { f, a } = head.node() {
                        self.tick()?;
                        arguments.push(a);
                        head = f;
                    }
                    if let ExprNode::FVar { id } = head.node()
                        && self
                            .recursion
                            .iter()
                            .chain(self.enclosing_recursions.iter().rev())
                            .any(|recursion| {
                                &recursion.marker == id
                                    && !recursion.pending
                                    && (!recursion.matrix_hypotheses.is_empty()
                                        || recursion.course_name.is_some())
                                    && arguments.len() > recursion.decreasing
                            })
                    {
                        arguments.reverse();
                        tasks.push(Task::Call(expr, id.clone(), arguments.clone()));
                        tasks.extend(arguments.into_iter().rev().map(Task::Visit));
                    } else {
                        tasks.push(Task::Node(expr));
                        tasks.extend(children(expr).into_iter().flatten().map(Task::Visit));
                    }
                }
                Task::Call(expr, marker, arguments) => {
                    let mut rebuilt = Expr::fvar(marker);
                    for argument in arguments {
                        self.tick()?;
                        rebuilt = Expr::app(rebuilt, done[&argument.allocation_identity()].clone());
                    }
                    let lowered = self.lower_matrix_call(&rebuilt)?;
                    done.insert(expr.allocation_identity(), lowered);
                }
                Task::Node(expr) => {
                    let child = |e: &Expr| done[&e.allocation_identity()].clone();
                    let result = match expr.node() {
                        ExprNode::App { f, a } => Expr::app(child(f), child(a)),
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::lam(
                            binder_name.clone(),
                            child(binder_type),
                            child(body),
                            *binder_info,
                        ),
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::forall_e(
                            binder_name.clone(),
                            child(binder_type),
                            child(body),
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
                            child(type_),
                            child(value),
                            child(body),
                            *non_dep,
                        ),
                        ExprNode::MData { data, expr } => Expr::mdata(data.clone(), child(expr)),
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => Expr::proj(struct_name.clone(), *idx, child(expr)),
                        _ => expr.clone(),
                    };
                    done.insert(expr.allocation_identity(), result);
                }
            }
        }
        Ok(done
            .remove(&value.allocation_identity())
            .expect("deferred matrix lowering finishes its root"))
    }
}
