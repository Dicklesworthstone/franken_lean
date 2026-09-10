//! Primitive structural recursion, compiled into the match recursor's hypotheses.
//!
//! A recursive name is a private local marker, never an environment declaration.
//! Only calls on an immediate recursive constructor field may replace that marker.
//! The entire body must be the selected match: an induction hypothesis for an
//! inner subexpression cannot stand for the whole function. Fixed arguments must
//! be the original locals, not arbitrary terms that conversion could erase.
use super::*;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecursionError {
    ResultTypeRequired,
    RootMatchRequired,
    ExplicitParameterRequired,
    NotDecreasing,
    ChangedParameter,
    PartialApplication,
}
impl std::fmt::Display for RecursionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::ResultTypeRequired => "recursive definition requires an explicit result type",
            Self::RootMatchRequired => {
                "structural recursion requires a body matching a function parameter"
            }
            Self::ExplicitParameterRequired => {
                "structural recursion requires an explicit decreasing parameter"
            }
            Self::NotDecreasing => {
                "recursive call is not on an immediate recursive constructor field"
            }
            Self::ChangedParameter => "recursive call changes a fixed parameter",
            Self::PartialApplication => {
                "recursive function escapes without its structural argument"
            }
        })
    }
}
fn error(reason: RecursionError) -> NatDefinitionElabError {
    failure(SourceInferenceError::Recursion(reason))
}

#[derive(Clone)]
pub(super) struct Recursion {
    pub(super) name: Name,
    pub(super) reference: Typed,
    pub(super) marker: FVarId,
    pub(super) parameters: Vec<LocalDecl>,
    pub(super) decreasing: usize,
    pub(super) pending: bool,
}
impl Context {
    /// Retry only an actual unresolved self-reference. Lexical shadowing and
    /// nonrecursive definitions follow their ordinary path, including errors.
    pub(super) fn definition_body(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let snapshot = self.clone();
        match self.term(syntax, expected.clone()) {
            Err(NatDefinitionElabError::Inference(SourceInferenceError::UnknownConstant(
                found,
            ))) if &found == name && !self.txn.env.contains(name) => {
                let consumed = self.txn.budget.heartbeats_consumed;
                *self = snapshot;
                self.txn.budget.heartbeats_consumed = consumed;
                self.prepare_recursion(name, parameters, syntax, expected.as_ref())?;
                self.term(syntax, expected)
            }
            result => result,
        }
    }

    fn prepare_recursion(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        mut syntax: &Syntax,
        expected: Option<&Expr>,
    ) -> Result<(), NatDefinitionElabError> {
        let expected = expected.ok_or_else(|| error(RecursionError::ResultTypeRequired))?;
        while let Some(inner) = parenthesized_inner(syntax)? {
            self.tick()?;
            syntax = inner;
        }
        if !matches!(syntax, Syntax::Node { kind, .. } if kind == &parser_kind(&["Term", "match"]))
        {
            return Err(error(RecursionError::RootMatchRequired));
        }
        let parts = self.match_parts(syntax)?;
        let mut discriminant = parts.discriminant;
        while let Some(inner) = parenthesized_inner(discriminant)? {
            self.tick()?;
            discriminant = inner;
        }
        let Syntax::Ident { val, .. } = discriminant else {
            return Err(error(RecursionError::RootMatchRequired));
        };
        let decreasing = parameters
            .iter()
            .rposition(|local| &local.user_name == val)
            .ok_or_else(|| error(RecursionError::RootMatchRequired))?;
        if parameters[decreasing].binder_info != BinderInfo::Default {
            return Err(error(RecursionError::ExplicitParameterRequired));
        }
        let mut full_type = self.instantiate(expected)?;
        for local in parameters.iter().rev() {
            self.tick()?;
            full_type = full_type
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            full_type = Expr::forall_e(
                local.user_name.clone(),
                self.instantiate(&local.type_)?,
                full_type,
                local.binder_info,
            );
        }
        let marker = FVarId(self.fresh_name()?);
        self.txn.lctx.add_param(
            marker.clone(),
            Name::anonymous(),
            full_type.clone(),
            BinderInfo::Default,
        );
        self.recursion = Some(Recursion {
            name: name.clone(),
            reference: Typed {
                value: Expr::fvar(marker.clone()),
                type_: full_type,
            },
            marker,
            parameters: parameters.to_vec(),
            decreasing,
            pending: true,
        });
        Ok(())
    }

    pub(super) fn recursive_match(&mut self, major: &Expr) -> bool {
        let Some(recursion) = &mut self.recursion else {
            return false;
        };
        if recursion.pending
            && *major == Expr::fvar(recursion.parameters[recursion.decreasing].id.clone())
        {
            recursion.pending = false;
            true
        } else {
            false
        }
    }

    /// Abstract trailing arguments into the motive, so the induction hypothesis
    /// is a function of their *new* values, rather than a result at captured
    /// values from the original call. Domains may depend on the major and on
    /// preceding trailing arguments.
    pub(super) fn recursive_target(
        &mut self,
        target: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("recursive target specification");
        let mut target = self.instantiate(target)?;
        for local in recursion.parameters[recursion.decreasing + 1..]
            .iter()
            .rev()
        {
            self.tick()?;
            target = target
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            target = Expr::forall_e(
                local.user_name.clone(),
                self.instantiate(&local.type_)?,
                target,
                local.binder_info,
            );
        }
        Ok(target)
    }

    pub(super) fn recursive_arguments(&self) -> Vec<Expr> {
        let recursion = self
            .recursion
            .as_ref()
            .expect("recursive result specification");
        recursion.parameters[recursion.decreasing + 1..]
            .iter()
            .map(|local| Expr::fvar(local.id.clone()))
            .collect()
    }

    pub(super) fn recursive_parameters(
        &mut self,
        locals: &mut Vec<LocalDecl>,
        mut target: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("recursive branch specification");
        for parameter in &recursion.parameters[recursion.decreasing + 1..] {
            self.tick()?;
            target = self.whnf(&target)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = target.node()
            else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            // A pattern binder shadows an equally named header parameter. The
            // generalized parameter still exists but is not name-resolvable.
            let name = if locals
                .iter()
                .any(|local| local.user_name == parameter.user_name)
            {
                Name::anonymous()
            } else {
                parameter.user_name.clone()
            };
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_param(id.clone(), name, binder_type.clone(), *binder_info);
            locals.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("generalized argument")
                    .clone(),
            );
            target = self.substitute(body, &Expr::fvar(id))?;
        }
        Ok(target)
    }

    /// The original major must not remain captured in a recursive minor: its
    /// value at smaller arguments is the constructor currently being inspected.
    pub(super) fn recursive_branch_context(&mut self) {
        let recursion = self
            .recursion
            .as_ref()
            .expect("recursive match has a specification");
        self.txn
            .lctx
            .truncate(recursion.parameters[recursion.decreasing].index);
        self.txn.lctx.add_param(
            recursion.marker.clone(),
            Name::anonymous(),
            recursion.reference.type_.clone(),
            BinderInfo::Default,
        );
    }

    pub(super) fn recursive_major_alias(
        &mut self,
        locals: &mut Vec<LocalDecl>,
        constructor: &Expr,
        family_type: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let recursion = self
            .recursion
            .as_ref()
            .expect("recursive match specification");
        let name = recursion.parameters[recursion.decreasing].user_name.clone();
        if !locals.iter().any(|local| local.user_name == name) {
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_let(id.clone(), name, family_type.clone(), constructor.clone());
            locals.push(self.txn.lctx.find(&id).expect("major alias").clone());
        }
        Ok(())
    }

    /// Transform every node, including unused values and annotations. Only the
    /// original fixed local arguments and a direct child are discarded; every
    /// other argument remains in the checked term. No beta reduction is used to
    /// hide an invalid self-call. Memoization preserves DAG sharing and depth.
    pub(super) fn lower_recursive_calls(
        &mut self,
        value: &Expr,
        hypotheses: &[(FVarId, FVarId)],
    ) -> Result<Expr, NatDefinitionElabError> {
        enum Task<'a> {
            Visit(&'a Expr),
            Node(&'a Expr),
            Call(&'a Expr, Expr, Vec<&'a Expr>),
        }
        let recursion = self
            .recursion
            .clone()
            .expect("recursive branch specification");
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
                    if matches!(head.node(), ExprNode::FVar { id } if id == &recursion.marker) {
                        arguments.reverse();
                        if arguments.len() <= recursion.decreasing {
                            return Err(error(RecursionError::PartialApplication));
                        }
                        for (argument, parameter) in arguments
                            .iter()
                            .zip(&recursion.parameters)
                            .take(recursion.decreasing)
                        {
                            if **argument != Expr::fvar(parameter.id.clone()) {
                                return Err(error(RecursionError::ChangedParameter));
                            }
                        }
                        let ExprNode::FVar { id: child } = arguments[recursion.decreasing].node()
                        else {
                            return Err(error(RecursionError::NotDecreasing));
                        };
                        let hypothesis = hypotheses
                            .iter()
                            .find(|(field, _)| field == child)
                            .map(|(_, ih)| Expr::fvar(ih.clone()))
                            .ok_or_else(|| error(RecursionError::NotDecreasing))?;
                        let extra = arguments[recursion.decreasing + 1..].to_vec();
                        tasks.push(Task::Call(expr, hypothesis, extra.clone()));
                        tasks.extend(extra.into_iter().rev().map(Task::Visit));
                    } else {
                        tasks.push(Task::Node(expr));
                        tasks.extend(children(expr).into_iter().flatten().map(Task::Visit));
                    }
                }
                Task::Call(expr, mut result, extra) => {
                    for argument in extra {
                        self.tick()?;
                        result = Expr::app(result, done[&argument.allocation_identity()].clone());
                    }
                    done.insert(expr.allocation_identity(), result);
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
            .expect("recursive lowering finishes its root"))
    }
}
fn children(expr: &Expr) -> [Option<&Expr>; 3] {
    match expr.node() {
        ExprNode::App { f, a } => [Some(f), Some(a), None],
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => [Some(binder_type), Some(body), None],
        ExprNode::LetE {
            type_, value, body, ..
        } => [Some(type_), Some(value), Some(body)],
        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => [Some(expr), None, None],
        _ => [None, None, None],
    }
}
