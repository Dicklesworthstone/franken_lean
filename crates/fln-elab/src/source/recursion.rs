//! Primitive structural recursion, compiled into the match recursor's hypotheses.
//!
//! A recursive name is a private local marker, never an environment declaration.
//! Only calls on an immediate recursive constructor field may replace that marker.
//! The entire body must be the selected match: an induction hypothesis for an
//! inner subexpression cannot stand for the whole function. Fixed arguments must
//! be the original locals or their domain-checked eta expansions, not arbitrary
//! terms that conversion could erase.
use super::*;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecursionError {
    ResultTypeRequired,
    RootMatchRequired,
    ExplicitParameterRequired,
    NotDecreasing,
    ChangedParameter,
    ChangedIndex,
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
            Self::ChangedIndex => "recursive call indices do not match its structural child's type",
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
    /// Family-ordered index binders, each pointing into the source telescope.
    indices: Vec<usize>,
    /// Source-ordered arguments universally quantified in each hypothesis.
    varying: Vec<usize>,
    family: Option<(Name, usize)>,
}
impl Context {
    /// Implicit higher-order inference can produce `fun x => P x` for the fixed
    /// parameter `P`. Recognize only that exact eta shape, checking every domain
    /// against P's dependent function telescope. Unlike general conversion this
    /// cannot erase a let, application argument, annotation, or recursive call.
    fn fixed_recursive_argument(
        &mut self,
        argument: &Expr,
        parameter: &LocalDecl,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut body = argument;
        let type_ = self.instantiate(&parameter.type_)?;
        let mut domain = &type_;
        let mut arity = 0u32;
        while let ExprNode::Lam {
            binder_type,
            body: inner,
            ..
        } = body.node()
        {
            self.tick()?;
            let ExprNode::ForallE {
                binder_type: expected,
                body: result,
                ..
            } = domain.node()
            else {
                return Ok(false);
            };
            if binder_type != expected {
                return Ok(false);
            }
            arity = arity
                .checked_add(1)
                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
            body = inner;
            domain = result;
        }
        for index in 0..arity {
            self.tick()?;
            let ExprNode::App { f, a } = body.node() else {
                return Ok(false);
            };
            if !matches!(a.node(), ExprNode::BVar { idx } if *idx == index) {
                return Ok(false);
            }
            body = f;
        }
        Ok(matches!(body.node(), ExprNode::FVar { id } if id == &parameter.id))
    }

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
            indices: Vec::new(),
            varying: (decreasing + 1..parameters.len()).collect(),
            family: None,
        });
        Ok(())
    }

    /// Separate fixed family parameters from indices that change at each child.
    /// Earlier arguments depending on an index must vary too; capturing them
    /// would give a recursive hypothesis a value at the *outer* index. Index
    /// domains may depend on preceding indices, but never on a generalized
    /// ordinary argument or a later index.
    pub(super) fn recursive_indices(
        &mut self,
        family: &Name,
        parameters: &[Expr],
        indices: &[LocalDecl],
    ) -> Result<(), NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("recursive match specification");
        let mut positions = Vec::new();
        let mut removed: HashSet<_> = indices.iter().map(|local| local.id.clone()).collect();
        for local in indices {
            self.tick()?;
            let position = recursion
                .parameters
                .iter()
                .position(|param| param.id == local.id)
                .filter(|position| *position < recursion.decreasing)
                .ok_or_else(|| {
                    failure(SourceInferenceError::Match(
                        matching::MatchError::UnrefinedIndices,
                    ))
                })?;
            positions.push(position);
        }
        removed.insert(recursion.parameters[recursion.decreasing].id.clone());
        let mut varying = Vec::new();
        for (position, local) in recursion.parameters.iter().enumerate() {
            self.tick()?;
            if position != recursion.decreasing
                && !positions.contains(&position)
                && (position > recursion.decreasing
                    || !self.elimination_reads(&local.type_)?.is_disjoint(&removed))
            {
                varying.push(position);
                removed.insert(local.id.clone());
            }
        }
        for parameter in parameters {
            if !self.elimination_reads(parameter)?.is_disjoint(&removed) {
                return Err(error(RecursionError::ChangedParameter));
            }
        }
        let mut preceding = HashSet::new();
        for index in indices {
            if self
                .elimination_reads(&index.type_)?
                .iter()
                .any(|id| removed.contains(id) && !preceding.contains(id))
            {
                return Err(failure(SourceInferenceError::Match(
                    matching::MatchError::UnrefinedIndices,
                )));
            }
            preceding.insert(index.id.clone());
        }
        let recursion = self
            .recursion
            .as_mut()
            .expect("recursive match specification");
        recursion.indices = positions;
        recursion.varying = varying;
        recursion.family = Some((family.clone(), parameters.len()));
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
        for position in recursion.varying.iter().rev() {
            let local = &recursion.parameters[*position];
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
        recursion
            .varying
            .iter()
            .map(|position| Expr::fvar(recursion.parameters[*position].id.clone()))
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
        for position in &recursion.varying {
            let parameter = &recursion.parameters[*position];
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
    pub(super) fn recursive_branch_context(&mut self) -> Result<(), NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("recursive match has a specification");
        let removed: HashSet<_> = recursion
            .indices
            .iter()
            .chain(&recursion.varying)
            .map(|position| recursion.parameters[*position].id.clone())
            .chain([
                recursion.parameters[recursion.decreasing].id.clone(),
                recursion.marker.clone(),
            ])
            .collect();
        let previous = self.txn.lctx.clone();
        self.txn.lctx = LocalContext::new();
        for local in previous.decls() {
            self.tick()?;
            if !removed.contains(&local.id) {
                if let Some(value) = &local.value {
                    self.txn.lctx.add_let(
                        local.id.clone(),
                        local.user_name.clone(),
                        local.type_.clone(),
                        value.clone(),
                    );
                } else {
                    self.txn.lctx.add_param(
                        local.id.clone(),
                        local.user_name.clone(),
                        local.type_.clone(),
                        local.binder_info,
                    );
                }
            }
        }
        self.txn.lctx.add_param(
            recursion.marker.clone(),
            Name::anonymous(),
            recursion.reference.type_.clone(),
            BinderInfo::Default,
        );
        Ok(())
    }

    /// Rebind source index names to this branch's constructor result, just as
    /// the original major is rebound to the constructor. Pattern names shadow
    /// these aliases, but core identities never do. Domains are specialized in
    /// family order for genuinely dependent index telescopes.
    pub(super) fn recursive_index_aliases(
        &mut self,
        locals: &mut Vec<LocalDecl>,
        constructor_type: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("recursive match specification");
        let (family, parameters) = recursion
            .family
            .as_ref()
            .expect("recursive family classified");
        let values = self.elimination_result_indices(
            constructor_type,
            family,
            *parameters,
            recursion.indices.len(),
        )?;
        let mut replacements = Vec::new();
        for (position, value) in recursion.indices.iter().zip(values) {
            let old = &recursion.parameters[*position];
            let mut type_ = self.instantiate(&old.type_)?;
            for (id, replacement) in &replacements {
                self.tick()?;
                type_ = type_
                    .abstract_fvar(id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                type_ = self.substitute(&type_, replacement)?;
            }
            if !locals.iter().any(|local| local.user_name == old.user_name) {
                let id = FVarId(self.fresh_name()?);
                self.txn
                    .lctx
                    .add_let(id.clone(), old.user_name.clone(), type_, value.clone());
                locals.push(self.txn.lctx.find(&id).expect("branch index alias").clone());
            }
            replacements.push((old.id.clone(), value));
        }
        Ok(())
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
                        for (position, (argument, parameter)) in arguments
                            .iter()
                            .zip(&recursion.parameters)
                            .take(recursion.decreasing)
                            .enumerate()
                        {
                            if !recursion.indices.contains(&position)
                                && !recursion.varying.contains(&position)
                                && !self.fixed_recursive_argument(argument, parameter)?
                            {
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
                        if !recursion.indices.is_empty() {
                            let child_type = self
                                .txn
                                .lctx
                                .find(child)
                                .map(|local| local.type_.clone())
                                .ok_or_else(|| error(RecursionError::NotDecreasing))?;
                            let (family, parameters) = recursion
                                .family
                                .as_ref()
                                .expect("recursive family classified");
                            let indices = self.elimination_result_indices(
                                &child_type,
                                family,
                                *parameters,
                                recursion.indices.len(),
                            )?;
                            for (position, index) in recursion.indices.iter().zip(indices) {
                                // These arguments disappear into the recursor's
                                // own indices. Require the actual child index,
                                // not conversion which could erase a bad term.
                                if *arguments[*position] != index {
                                    return Err(error(RecursionError::ChangedIndex));
                                }
                            }
                        }
                        let mut extra: Vec<_> = recursion
                            .varying
                            .iter()
                            .filter_map(|position| arguments.get(*position).copied())
                            .collect();
                        extra.extend(arguments.iter().skip(recursion.parameters.len()).copied());
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_parameter_eta_checks_dependent_domains_and_variable_order() {
        let mut context = Context::new(&Environment::new(), Budget::DEFAULT);
        let f = FVarId(Name::from_components(["polymorphic_identity"]));
        let type_ = Expr::forall_e(
            Name::anonymous(),
            Expr::sort(Level::one()),
            Expr::forall_e(
                Name::anonymous(),
                Expr::bvar(0).unwrap(),
                Expr::bvar(1).unwrap(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let parameter = LocalDecl {
            id: f.clone(),
            user_name: f.0.clone(),
            type_,
            value: None,
            binder_info: BinderInfo::Default,
            index: 0,
        };
        let expanded = |domain: Expr, first: u32, second: u32| {
            Expr::lam(
                Name::anonymous(),
                Expr::sort(Level::one()),
                Expr::lam(
                    Name::anonymous(),
                    domain,
                    Expr::app(
                        Expr::app(Expr::fvar(f.clone()), Expr::bvar(first).unwrap()),
                        Expr::bvar(second).unwrap(),
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            )
        };
        assert!(
            context
                .fixed_recursive_argument(&expanded(Expr::bvar(0).unwrap(), 1, 0), &parameter)
                .unwrap()
        );
        assert!(
            !context
                .fixed_recursive_argument(&expanded(Expr::sort(Level::zero()), 1, 0), &parameter)
                .unwrap()
        );
        assert!(
            !context
                .fixed_recursive_argument(&expanded(Expr::bvar(0).unwrap(), 0, 1), &parameter)
                .unwrap()
        );
        assert!(
            !context
                .fixed_recursive_argument(&expanded(Expr::bvar(0).unwrap(), 1, 1), &parameter)
                .unwrap()
        );
    }

    #[test]
    fn fixed_parameter_eta_refusal_does_not_reduce_discardable_annotations() {
        let mut context = Context::new(&Environment::new(), Budget::DEFAULT);
        let f = FVarId(Name::from_components(["fixed"]));
        let parameter = LocalDecl {
            id: f.clone(),
            user_name: f.0.clone(),
            type_: Expr::forall_e(
                Name::anonymous(),
                Expr::sort(Level::one()),
                Expr::sort(Level::one()),
                BinderInfo::Default,
            ),
            value: None,
            binder_info: BinderInfo::Default,
            index: 0,
        };
        let body = Expr::let_e(
            Name::anonymous(),
            Expr::sort(Level::zero()),
            Expr::sort(Level::one()),
            Expr::app(Expr::fvar(f), Expr::bvar(1).unwrap()),
            false,
        );
        let value = Expr::lam(
            Name::anonymous(),
            Expr::sort(Level::one()),
            body,
            BinderInfo::Default,
        );
        assert!(
            !context
                .fixed_recursive_argument(&value, &parameter)
                .unwrap()
        );
        context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed;
        assert!(matches!(
            context.fixed_recursive_argument(&value, &parameter),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }
}
