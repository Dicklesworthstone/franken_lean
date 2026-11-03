//! Source conditionals are applications of the admitted `ite`/`dite`, as in
//! `Init/Prelude.lean`. Elaborate then before else without refining the condition
//! or introducing a recursor: ordinary conditional lemmas must see the same head.
use super::*;

const MAX_DEFERRED_CONDITIONAL_CACHE: usize = 65_536;

fn deferred_conditional_tag() -> Name {
    Name::from_components(["_fln", "source", "deferredIte"])
}

pub(in crate::source) struct ConditionalBuild<'a> {
    saved: LocalContext,
    function: Typed,
    ordinary: Option<Typed>,
    target: Expr,
    branches: std::collections::VecDeque<&'a Syntax>,
    dependent: bool,
    hidden_evidence: bool,
    binding: Option<Name>,
    local: Option<LocalDecl>,
    domain: Option<Expr>,
    branch_scope_depth: Option<usize>,
}

impl ConditionalBuild<'_> {
    pub(in crate::source) fn closes_scope(&self) -> bool {
        self.dependent
    }
}

pub(in crate::source) enum ConditionalStep<'a> {
    Branch { syntax: &'a Syntax, expected: Expr },
    Complete(Typed),
}

impl Context {
    pub(super) fn start_conditional<'a>(
        &mut self,
        parts: ConditionalParts<'a>,
        mut condition: Typed,
        expected: Option<Expr>,
    ) -> Result<ConditionalBuild<'a>, NatDefinitionElabError> {
        let type_ = self.whnf(&condition.type_)?;
        let boolean = Expr::const_(Name::from_components(["Bool"]), vec![]);
        let prop = Expr::sort(Level::zero());
        // The bounded seed has no coercion classes. Its Boolean conditional
        // uses the pin's `boolToProp` equality; imported worlds use the ordinary
        // coercion path so their registered instances apply.
        if type_ == boolean && !self.has_coercion_class("CoeT")? {
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
                type_: prop,
            };
        } else {
            condition = self.finish_term(condition, Some(&prop))?;
        }
        // The result metavariable belongs to the outer context. A branch's
        // evidence may occur in its value, never escape into this result type.
        let target = match expected {
            Some(target) => self.instantiate(&target)?,
            None => {
                let sort = self.type_expected()?;
                self.hole(sort)?
            }
        };
        let target_sort = self
            .known_type(&target)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        // The pin's WF preprocessing rewrites `ite` to `dite` with
        // `Init.WF.ite_eq_dite`. Our recursive calls are lowered while the
        // branches elaborate, so retain that evidence now, hidden from source
        // tactics and available only to their later decreasing obligations.
        let hidden_evidence = !parts.binds_evidence && self.well_founded_branch_depth().is_some();
        let dependent = parts.binds_evidence || hidden_evidence;
        let name = if dependent { "dite" } else { "ite" };
        let function = self.constant(&Name::from_components([name]))?;
        let result_type = Typed {
            value: target.clone(),
            type_: target_sort,
        };
        let function = self.match_apply(function, result_type.clone())?;
        // Do not normalize the condition before synthesis: `n < 5` must keep
        // the class problem that its source spelling produced (fln-52qv).
        condition.value = self.instantiate(&condition.value)?;
        let function = self.match_apply(function, condition.clone())?;
        let telescope = self.whnf(&function.type_)?;
        let ExprNode::ForallE {
            binder_type,
            binder_info: BinderInfo::InstImplicit,
            ..
        } = telescope.node()
        else {
            return Err(error(MatchError::UnsupportedFamily));
        };
        let dictionary = Typed {
            value: self.instance_hole(binder_type.clone())?,
            type_: binder_type.clone(),
        };
        let function = self.match_apply(function, dictionary.clone())?;
        // Source proofs still see `ite` before the pin's WF preprocessing.
        // Build its checked prefix alongside the dependent form, retaining it
        // only when neither branch needs the private termination evidence.
        let ordinary = if hidden_evidence {
            let function = self.constant(&Name::from_components(["ite"]))?;
            let function = self.match_apply(function, result_type)?;
            let function = self.match_apply(function, condition)?;
            Some(self.match_apply(function, dictionary)?)
        } else {
            None
        };
        self.resolve_instances(false)?;
        Ok(ConditionalBuild {
            saved: self.txn.lctx.clone(),
            function,
            ordinary,
            target,
            branches: [parts.yes, parts.no].into(),
            dependent,
            hidden_evidence,
            binding: parts.binding.cloned(),
            local: None,
            domain: None,
            branch_scope_depth: self.well_founded_branch_depth(),
        })
    }

    pub(in crate::source) fn next_conditional_branch<'a>(
        &mut self,
        state: &mut ConditionalBuild<'a>,
    ) -> Result<ConditionalStep<'a>, NatDefinitionElabError> {
        self.txn.lctx = state.saved.clone();
        let Some(syntax) = state.branches.pop_front() else {
            let mut function = state.ordinary.as_ref().unwrap_or(&state.function).clone();
            if state.hidden_evidence && state.ordinary.is_none() {
                // A numeral's carrier may be fixed by a later argument. Keep
                // its original inference scope and reconsider the conditional
                // only after its captured holes have actually been assigned.
                let mut data = KVMap::new();
                data.insert(
                    deferred_conditional_tag(),
                    fln_core::options::DataValue::OfBool(true),
                );
                function.value = Expr::mdata(data, function.value);
                self.deferred_conditional_forms = true;
            }
            return Ok(ConditionalStep::Complete(
                self.finish_term(function, Some(&state.target))?,
            ));
        };
        let telescope = self.whnf(&state.function.type_)?;
        let ExprNode::ForallE { binder_type, .. } = telescope.node() else {
            return Err(error(MatchError::UnsupportedFamily));
        };
        state.domain = Some(binder_type.clone());
        let expected = if state.dependent {
            let domain = self.whnf(binder_type)?;
            let ExprNode::ForallE {
                binder_type,
                binder_info,
                body,
                ..
            } = domain.node()
            else {
                return Err(error(MatchError::UnsupportedFamily));
            };
            let id = FVarId(self.fresh_name()?);
            let name =
                match &state.binding {
                    Some(name) => name.clone(),
                    None => self.fresh_inaccessible(&Name::from_components([
                        if state.hidden_evidence { "h" } else { "x" },
                    ]))?,
                };
            self.txn
                .lctx
                .add_param(id.clone(), name.clone(), binder_type.clone(), *binder_info);
            if state.hidden_evidence {
                self.register_well_founded_conditional_hypothesis(name)?;
            }
            state.local = self.txn.lctx.find(&id).cloned();
            self.substitute(body, &Expr::fvar(id))?
        } else {
            binder_type.clone()
        };
        // Sibling recursive calls must not reuse a decreasing obligation from
        // another branch. Nondependent `ite` has no proof local to distinguish
        // the scopes, so preserve the existing lexical cache boundary explicitly.
        if let Some(depth) = state.branch_scope_depth {
            self.enter_well_founded_branch(depth)?;
        }
        Ok(ConditionalStep::Branch { syntax, expected })
    }

    pub(in crate::source) fn accept_conditional_branch(
        &mut self,
        state: &mut ConditionalBuild<'_>,
        mut branch: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.resolve_instances(false)?;
        self.flush(false)?;
        branch.value = self.instantiate(&branch.value)?;
        branch.type_ = self.instantiate(&branch.type_)?;
        if let Some(local) = state.local.take() {
            let locals = std::slice::from_ref(&local);
            self.capture_bound_metavars(locals, &state.saved, &mut branch)?;
            if self.capture_bound_coercions(locals, &state.saved, &branch)? {
                branch.value = self.instantiate(&branch.value)?;
                branch.type_ = self.instantiate(&branch.type_)?;
            }
            // An unresolved metavariable may still capture the private local.
            // Recursive calls explicitly apply their decreasing-proof holes to
            // captured locals, so their need for this evidence is visible here.
            // Test after both capture paths have exposed their dependencies.
            if let Some(function) = state.ordinary.take()
                && !branch.value.has_expr_mvar()
                && !self.elimination_reads(&branch.value)?.contains(&local.id)
            {
                state.ordinary = Some(self.match_apply(function, branch.clone())?);
            }
            branch.value = Expr::lam(
                local.user_name,
                self.instantiate(&local.type_)?,
                branch
                    .value
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        if let Some(depth) = state.branch_scope_depth {
            self.leave_well_founded_branch(depth)?;
        }
        self.txn.lctx = state.saved.clone();
        branch.type_ = state
            .domain
            .take()
            .ok_or_else(|| error(MatchError::UnsupportedFamily))?;
        state.function = self.match_apply(state.function.clone(), branch)?;
        Ok(())
    }

    /// Reconsider only our private WF conditionals after ordinary instantiation
    /// has settled captured metavariables and beta-reduced their applications.
    /// No hole loses its scope, and named/source `dite` terms carry no marker.
    /// The iterative postorder preserves unchanged nodes and shared subterms.
    pub(in crate::source) fn canonicalize_deferred_conditionals(
        &mut self,
        root: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        // Assignment changes have already produced a new input expression.
        // This rewrite reads no environment or metavariable state, so an exact
        // immutable expression key safely reuses work across speculative forks.
        let cache = self.deferred_conditional_cache.clone();
        let mut cache = cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(result) = cache.get(root) {
            return Ok(result.clone());
        }
        let tag = deferred_conditional_tag();
        let mut done = HashMap::<usize, Expr>::new();
        let mut pending = vec![(root, false)];
        while let Some((term, exit)) = pending.pop() {
            let key = term.allocation_identity();
            if done.contains_key(&key) {
                continue;
            }
            if let Some(result) = cache.get(term) {
                done.insert(key, result.clone());
                continue;
            }
            self.tick()?;
            if !exit {
                pending.push((term, true));
                pending.extend(
                    conditional_children(term)
                        .into_iter()
                        .flatten()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let child = |expr: &Expr| {
                done.get(&expr.allocation_identity())
                    .expect("conditional postorder child")
                    .clone()
            };
            let unchanged = conditional_children(term)
                .into_iter()
                .flatten()
                .all(|expr| child(expr).allocation_identity() == expr.allocation_identity());
            let rebuilt = if unchanged {
                term.clone()
            } else {
                match term.node() {
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
                    _ => term.clone(),
                }
            };
            let result = match rebuilt.node() {
                ExprNode::MData { data, expr }
                    if data.find(&tag) == Some(&fln_core::options::DataValue::OfBool(true))
                        && !expr.has_expr_mvar() =>
                {
                    let value = ordinary_conditional(expr)?.unwrap_or_else(|| expr.clone());
                    let mut data = data.clone();
                    data.erase(&tag);
                    if data.is_empty() {
                        value
                    } else {
                        Expr::mdata(data, value)
                    }
                }
                _ => rebuilt,
            };
            // Eviction cannot invalidate this traversal: its separate local
            // memo retains every completed child until the root is finished.
            if cache.len() >= MAX_DEFERRED_CONDITIONAL_CACHE {
                cache.clear();
            }
            cache.insert(term.clone(), result.clone());
            done.insert(key, result);
        }
        Ok(done
            .remove(&root.allocation_identity())
            .expect("conditional postorder root"))
    }
}

/// A constant-branch `dite` is definitionally equal to the admitted `ite` at
/// the same universe, result type, condition and dictionary. Removing each
/// unused proof binder must also lower references to its surrounding binders.
fn ordinary_conditional(value: &Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
    let (head, args) = operators::spine(value);
    let ExprNode::Const { name, levels } = head.node() else {
        return Ok(None);
    };
    if name != &Name::from_components(["dite"]) {
        return Ok(None);
    }
    let [type_, condition, dictionary, yes, no] = args.as_slice() else {
        return Ok(None);
    };
    let (ExprNode::Lam { body: yes, .. }, ExprNode::Lam { body: no, .. }) = (yes.node(), no.node())
    else {
        return Ok(None);
    };
    if yes.has_loose_bvar(0) || no.has_loose_bvar(0) {
        return Ok(None);
    }
    let lower = |body: &Expr| {
        body.subst_loose(0, &[Expr::sort(Level::zero())])
            .map_err(|_| failure(SourceInferenceError::Scope))
    };
    Ok(Some(
        [
            type_.clone(),
            condition.clone(),
            dictionary.clone(),
            lower(yes)?,
            lower(no)?,
        ]
        .into_iter()
        .fold(
            Expr::const_(Name::from_components(["ite"]), levels.clone()),
            Expr::app,
        ),
    ))
}

fn conditional_children(expr: &Expr) -> [Option<&Expr>; 3] {
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
