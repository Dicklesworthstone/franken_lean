//! Heap-driven, scope-indexed reduction. Proofs and instance arguments are not
//! visited; binder bodies are opened with fresh private locals before inference
//! or rewriting. Cache keys include that scope, and retain their input Expr so
//! allocator reuse cannot alias an earlier key.
use super::*;
mod eta;

#[derive(Clone)]
enum Child {
    Visit(Expr, usize),
    Keep(Expr),
}

enum Task {
    Visit(Expr, usize),
    Rebuild(Expr, usize, Vec<Child>),
    OpenBinder(Expr, usize, Expr),
    CloseBinder {
        original: Expr,
        scope: usize,
        domain: Expr,
        id: FVarId,
        body: Expr,
        body_scope: usize,
    },
    Link(Expr, usize, Expr),
}

type Cache = HashMap<(usize, usize), (Expr, Expr)>;

fn cached(cache: &Cache, term: &Expr, scope: usize) -> Expr {
    cache[&(scope, term.allocation_identity())].1.clone()
}
fn remember(cache: &mut Cache, original: Expr, scope: usize, value: Expr) {
    cache.insert((scope, original.allocation_identity()), (original, value));
}

impl Context {
    pub(super) fn dsimp_expression(
        &mut self,
        expression: &Expr,
        set: &DsimpSet<'_>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut trial = self.rewrite_trial();
        let saved = trial.txn.lctx.clone();
        let result = trial.dsimp_walk(expression, set);
        trial.txn.lctx = saved;
        self.charge_rewrite_trial(&trial);
        if matches!(
            &result,
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ObservationComplete
            ))
        ) {
            self.inspection = trial.inspection.clone();
        }
        let result = result?;
        *self = trial;
        Ok(result)
    }

    fn dsimp_walk(
        &mut self,
        expression: &Expr,
        set: &DsimpSet<'_>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut scopes = vec![self.txn.lctx.clone()];
        let mut work = vec![Task::Visit(expression.clone(), 0)];
        let mut done = Cache::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Task::Visit(term, scope) => {
                    if done.contains_key(&(scope, term.allocation_identity())) {
                        continue;
                    }
                    self.txn.lctx = scopes[scope].clone();
                    let instantiated = self.instantiate(&term)?;
                    if !self.rewrite_same(&term, &instantiated)? {
                        work.push(Task::Link(term, scope, instantiated.clone()));
                        work.push(Task::Visit(instantiated, scope));
                        continue;
                    }
                    if let Some(type_) = self.known_type(&term)?
                        && self.dsimp_is_proposition(&type_)?
                    {
                        remember(&mut done, term.clone(), scope, term);
                        continue;
                    }
                    if self.dsimp_literal(&term, set)? {
                        let next = self.dsimp_rewrite(&term, set)?;
                        self.dsimp_resume(&mut work, &mut done, term, scope, next)?;
                        continue;
                    }
                    match term.node() {
                        ExprNode::LetE { value, body, .. } => {
                            // zeta/usedLetOnly: don't normalize an unused value
                            // (or its type) and charge work that cannot contribute.
                            let next = self.substitute(body, value)?;
                            self.dsimp_resume(&mut work, &mut done, term, scope, next)?;
                        }
                        ExprNode::Lam { binder_type, .. }
                        | ExprNode::ForallE { binder_type, .. } => {
                            let domain = binder_type.clone();
                            work.push(Task::OpenBinder(term, scope, domain.clone()));
                            work.push(Task::Visit(domain, scope));
                        }
                        ExprNode::App { .. } => {
                            let (head, arguments) = self.dsimp_spine(&term)?;
                            let mut children = vec![Child::Visit(head.clone(), scope)];
                            let mut type_ = self.known_type(&head)?;
                            for argument in arguments {
                                self.tick()?;
                                let signature = match type_ {
                                    Some(ref type_) => Some(self.whnf(type_)?),
                                    None => None,
                                };
                                let instance = matches!(
                                    signature.as_ref().map(Expr::node),
                                    Some(ExprNode::ForallE {
                                        binder_info: BinderInfo::InstImplicit,
                                        ..
                                    })
                                );
                                type_ = match signature.as_ref().map(Expr::node) {
                                    Some(ExprNode::ForallE { body, .. }) => {
                                        Some(self.substitute(body, &argument)?)
                                    }
                                    _ => None,
                                };
                                children.push(if instance {
                                    Child::Keep(argument)
                                } else {
                                    Child::Visit(argument, scope)
                                });
                            }
                            self.dsimp_schedule_children(&mut work, term, scope, children);
                        }
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                            let child = expr.clone();
                            self.dsimp_schedule_children(
                                &mut work,
                                term,
                                scope,
                                vec![Child::Visit(child, scope)],
                            );
                        }
                        _ => {
                            let next = self.dsimp_post(&term, set)?;
                            self.dsimp_resume(&mut work, &mut done, term, scope, next)?;
                        }
                    }
                }
                Task::OpenBinder(original, scope, domain) => {
                    self.txn.lctx = scopes[scope].clone();
                    let domain = cached(&done, &domain, scope);
                    let body = match original.node() {
                        ExprNode::Lam { body, .. } | ExprNode::ForallE { body, .. } => body,
                        _ => unreachable!("only binders schedule opening"),
                    };
                    // A private name prevents the selected source rule's syntax
                    // from being captured by the binder currently being visited.
                    let mut local = self.equality_local(domain.clone())?;
                    local.binder_info = match original.node() {
                        ExprNode::Lam { binder_info, .. }
                        | ExprNode::ForallE { binder_info, .. } => *binder_info,
                        _ => unreachable!("only binders schedule opening"),
                    };
                    eliminate::add_local(&mut self.txn.lctx, &local);
                    let body = self.substitute(body, &Expr::fvar(local.id.clone()))?;
                    let body_scope = scopes.len();
                    scopes.push(self.txn.lctx.clone());
                    work.push(Task::CloseBinder {
                        original,
                        scope,
                        domain,
                        id: local.id,
                        body: body.clone(),
                        body_scope,
                    });
                    work.push(Task::Visit(body, body_scope));
                }
                Task::CloseBinder {
                    original,
                    scope,
                    domain,
                    id,
                    body,
                    body_scope,
                } => {
                    self.txn.lctx = scopes[scope].clone();
                    let body = cached(&done, &body, body_scope)
                        .abstract_fvar(&id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                    let rebuilt = match original.node() {
                        ExprNode::Lam {
                            binder_name,
                            binder_info,
                            ..
                        } => Expr::lam(binder_name.clone(), domain, body, *binder_info),
                        ExprNode::ForallE {
                            binder_name,
                            binder_info,
                            ..
                        } => Expr::forall_e(binder_name.clone(), domain, body, *binder_info),
                        _ => unreachable!("only binders schedule closing"),
                    };
                    let next = self.dsimp_post(&rebuilt, set)?;
                    self.dsimp_resume_rebuilt(
                        &mut work, &mut done, original, scope, rebuilt, next,
                    )?;
                }
                Task::Rebuild(original, scope, children) => {
                    self.txn.lctx = scopes[scope].clone();
                    let mut values = children.into_iter().map(|child| match child {
                        Child::Visit(term, scope) => cached(&done, &term, scope),
                        Child::Keep(term) => term,
                    });
                    let first = values.next().expect("a compound expression has a child");
                    let rebuilt = match original.node() {
                        ExprNode::App { .. } => values.fold(first, Expr::app),
                        ExprNode::MData { data, .. } => Expr::mdata(data.clone(), first),
                        ExprNode::Proj {
                            struct_name, idx, ..
                        } => Expr::proj(struct_name.clone(), *idx, first),
                        _ => unreachable!("only compound expressions schedule rebuilding"),
                    };
                    let next = self.dsimp_post(&rebuilt, set)?;
                    self.dsimp_resume_rebuilt(
                        &mut work, &mut done, original, scope, rebuilt, next,
                    )?;
                }
                Task::Link(original, scope, next) => {
                    let value = cached(&done, &next, scope);
                    remember(&mut done, original, scope, value);
                }
            }
        }
        Ok(cached(&done, expression, 0))
    }

    fn dsimp_schedule_children(
        &self,
        work: &mut Vec<Task>,
        original: Expr,
        scope: usize,
        children: Vec<Child>,
    ) {
        let visits: Vec<_> = children
            .iter()
            .filter_map(|child| match child {
                Child::Visit(term, scope) => Some((term.clone(), *scope)),
                Child::Keep(_) => None,
            })
            .collect();
        work.push(Task::Rebuild(original, scope, children));
        work.extend(
            visits
                .into_iter()
                .rev()
                .map(|(term, scope)| Task::Visit(term, scope)),
        );
    }

    fn dsimp_resume(
        &mut self,
        work: &mut Vec<Task>,
        done: &mut Cache,
        original: Expr,
        scope: usize,
        next: Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if self.rewrite_same(&original, &next)? {
            remember(done, original.clone(), scope, original);
        } else {
            work.push(Task::Link(original, scope, next.clone()));
            work.push(Task::Visit(next, scope));
        }
        Ok(())
    }

    fn dsimp_resume_rebuilt(
        &mut self,
        work: &mut Vec<Task>,
        done: &mut Cache,
        original: Expr,
        scope: usize,
        rebuilt: Expr,
        next: Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if self.rewrite_same(&rebuilt, &next)? {
            // All children are already normal. Don't revisit a rebuilt binder
            // merely because opening and closing it allocated a new Expr.
            let value = if self.rewrite_same(&original, &next)? {
                original.clone()
            } else {
                next
            };
            remember(done, original, scope, value);
            Ok(())
        } else {
            self.dsimp_resume(work, done, original, scope, next)
        }
    }

    fn dsimp_literal(
        &mut self,
        term: &Expr,
        set: &DsimpSet<'_>,
    ) -> Result<bool, NatDefinitionElabError> {
        let (head, args) = self.dsimp_spine(term)?;
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(false);
        };
        if set.unfolds(name) {
            return Ok(false);
        }
        let raw = |e: &Expr| {
            matches!(
                e.node(),
                ExprNode::Lit {
                    literal: Literal::Nat(_)
                }
            )
        };
        Ok(
            (name == &Name::from_components(["OfNat", "ofNat"])
                && args.len() >= 3
                && raw(&args[1]))
                || (name == &Name::from_components(["OfScientific", "ofScientific"])
                    && args.len() == 5
                    && raw(&args[2])
                    && raw(&args[4]))
                || (name == &Name::from_components(["Char", "ofNat"])
                    && args.len() == 1
                    && raw(&args[0])),
        )
    }

    fn dsimp_unfoldable(
        &mut self,
        definition: &fln_env::constants::DefinitionVal,
    ) -> Result<bool, NatDefinitionElabError> {
        self.tick()?;
        let table = crate::reducibility::table(&self.txn.env).map_err(|e| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(e),
            )))
        })?;
        Ok(definition.safety == DefinitionSafety::Safe
            && table.status(&definition.base.name)
                != crate::reducibility::Reducibility::Irreducible)
    }

    fn dsimp_post(
        &mut self,
        term: &Expr,
        set: &DsimpSet<'_>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let rewritten = self.dsimp_rewrite(term, set)?;
        if !self.rewrite_same(term, &rewritten)? {
            return Ok(rewritten);
        }
        let (head, arguments) = self.dsimp_spine(term)?;
        // Check saturated heads, never the function part of a partial call.
        if let Some(selection) = set.selection_for(&head) {
            self.tick()?;
            match selection {
                Selection::Local(_, value) => {
                    return Ok(arguments.into_iter().fold(value.clone(), Expr::app));
                }
                Selection::Global(definition) => {
                    if self.dsimp_unfoldable(definition)? {
                        let mut body = &definition.value;
                        let mut arity = 0usize;
                        while let ExprNode::Lam { body: next, .. } = body.node() {
                            self.tick()?;
                            arity = arity
                                .checked_add(1)
                                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                            body = next;
                        }
                        if arguments.len() >= arity {
                            let next = self.unfold_selected_definition(term, definition)?;
                            if !self.rewrite_same(term, &next)? {
                                return Ok(next);
                            }
                        }
                    }
                }
            }
        }
        if let ExprNode::Const { name, .. } = head.node()
            && let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned()
        {
            let environment = self.txn.env.clone();
            if let Some(projection) =
                crate::records::projection::generated_projection(&environment, &definition, || {
                    self.tick()
                })?
                && let Some(receiver) = arguments.get(projection.parameters)
                // The pin's `Simp.reduceProjFn?` reduces a class's projection only when it
                // was selected for unfolding (handled above): `dsimp only` left `x + y`
                // alone at the pin and rewrote it to `x.add y` here, then claimed progress.
                && !self.instance_registry()?.is_class(&projection.structure)
            {
                let receiver = self.whnf_with_transparency(
                    receiver,
                    UnificationTransparency::Instances,
                    false,
                )?;
                let (receiver_head, mut receiver_args) = self.dsimp_spine(&receiver)?;
                receiver_args.reverse();
                if let Some(field) = crate::records::constructor_field(
                    &environment,
                    &projection.structure,
                    projection.index,
                    &receiver_head,
                    &receiver_args,
                ) {
                    return Ok(arguments
                        .iter()
                        .skip(projection.parameters + 1)
                        .cloned()
                        .fold(field, Expr::app));
                }
            }
        }
        // Record eta is a conversion rule, not a standalone dsimp reduction.
        // Keep constructor-of-projections syntax unless a selected theorem
        // rewrites it; eta remains available to reflexive-goal comparison.
        // The pin folds orphan raw numerals back into their source-level OfNat
        // spelling, unless that projection was explicitly selected for unfolding.
        // Keep raw fixture environments without numeric classes separate. In a
        // class environment independently check the constructed term: neither a
        // familiar instance name nor a changed dictionary establishes conversion.
        if matches!(
            term.node(),
            ExprNode::Lit {
                literal: Literal::Nat(_)
            }
        ) && !set.unfolds(&Name::from_components(["OfNat", "ofNat"]))
            && self
                .txn
                .env
                .contains(&Name::from_components(["OfNat", "ofNat"]))
            && self
                .txn
                .env
                .contains(&Name::from_components(["instOfNatNat"]))
        {
            let packed = app(
                Expr::const_(
                    Name::from_components(["OfNat", "ofNat"]),
                    vec![Level::zero()],
                ),
                [
                    nat_const(),
                    term.clone(),
                    Expr::app(
                        Expr::const_(Name::from_components(["instOfNatNat"]), Vec::new()),
                        term.clone(),
                    ),
                ],
            );
            if self.known_type(&packed)?.is_some() {
                let mut budget = UnificationBudget::new(self.kernel);
                budget.transparency = UnificationTransparency::Instances;
                budget.zeta_delta = false;
                if self.proof_types_match_with_budget(term, &packed, budget)? {
                    return Ok(packed);
                }
            }
        }
        // Never use the ordinary/default transparency here: an unrelated
        // abbreviation or local let is not permission for global delta.
        self.whnf_with_transparency(term, UnificationTransparency::None, false)
    }
}
