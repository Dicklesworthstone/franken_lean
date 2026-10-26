//! `pattern (occs)? p` and `conv in (occs)? p` (vendored `Lean/Elab/Tactic/Conv/Pattern.lean`).
//!
//! The pin runs `Simp.main` over `lhs` with the neutral configuration and a `pre` method that
//! stops at each subterm matching `p` (at reducible transparency, after `toHeadIndex` agrees,
//! trying the application's prefixes), making it a conv goal. This walk visits what that
//! traversal visits: an application's function and its arguments without forward dependencies
//! (`simpAppUsingCongr`), a `fun`'s body under its binders (`simpLambda`), an arrow's two sides
//! and a proposition `∀`'s body (`simpForall`), a `have`'s value and body (`simpHaveTelescope`),
//! under metadata; and it builds the equation from `congrArg`, `congr`, `congrFun'`,
//! `congrFun`, `funext`, `implies_congr`, `forall_congr` and the `let` congruence lemmas. Where
//! the pin would take a path this walk does not (an `@[congr]` theorem, an automatically
//! generated congruence theorem with casts, a proposition `∀`'s domain, a projection) and the
//! pattern's head occurs there, it refuses, typed; elsewhere neither can match.
use super::congr::{ArgKind, FunInfo};
use super::*;

/// `toHeadIndex`: an application's head symbol.
#[derive(Clone, PartialEq, Eq)]
enum Head {
    Const(Name),
    FVar(FVarId),
    MVar(MVarId),
    Sort,
    Lit,
    Lam,
    Forall,
    Proj(Name, u64),
    Other,
}

fn head_of(expr: &Expr) -> Head {
    let (head, _) = spine(&cleanup(expr));
    match head.node() {
        ExprNode::Const { name, .. } => Head::Const(name.clone()),
        ExprNode::FVar { id } => Head::FVar(id.clone()),
        ExprNode::MVar { id } => Head::MVar(id.clone()),
        ExprNode::Sort { .. } => Head::Sort,
        ExprNode::Lit { .. } => Head::Lit,
        ExprNode::Lam { .. } => Head::Lam,
        ExprNode::ForallE { .. } => Head::Forall,
        ExprNode::Proj {
            struct_name, idx, ..
        } => Head::Proj(struct_name.clone(), *idx),
        _ => Head::Other,
    }
}

/// The application heads with an `@[congr]` theorem in `Init`, which `Simp.congr` tries before
/// its default congruence.
const CONGR_HEADS: [&[&str]; 10] = [
    &["Exists"],
    &["ite"],
    &["dite"],
    &["ForIn'", "forIn'"],
    &["Fin", "foldlM"],
    &["Fin", "foldrM"],
    &["Fin", "foldl"],
    &["Fin", "foldr"],
    &["Vector", "mapM"],
    &["Vector", "forM"],
];

/// `PatternMatchState`.
enum Occurrences {
    All(Vec<ProofGoal>),
    Listed {
        found: Vec<(usize, ProofGoal)>,
        index: usize,
        // `(occurrence, position in the user's list)`, by occurrence.
        remaining: std::collections::VecDeque<(usize, usize)>,
    },
}

impl Occurrences {
    fn is_done(&self) -> bool {
        matches!(self, Self::Listed { remaining, .. } if remaining.is_empty())
    }
    fn is_ready(&self) -> bool {
        match self {
            Self::All(_) => true,
            Self::Listed {
                index, remaining, ..
            } => remaining.front().is_some_and(|(wanted, _)| wanted == index),
        }
    }
}

/// The pattern with its metavariables as marker locals (`abstractMVars`).
struct Pattern {
    template: Expr,
    markers: Vec<(FVarId, Expr)>,
    head: Head,
}

/// `Simp.Result`: the expression a subterm became, with its equation unless unchanged.
#[derive(Clone)]
struct Simplified {
    expr: Expr,
    proof: Option<Expr>,
}

enum Task {
    Visit(Expr),
    /// The application `e`, its function and the arguments in order, with whether each was
    /// visited (pushed onto the values) or kept.
    App {
        e: Expr,
        f: Expr,
        args: Vec<(Expr, bool)>,
    },
    Lambda {
        locals: Vec<LocalDecl>,
        body: Expr,
        saved: LocalContext,
    },
    Arrow {
        e: Expr,
    },
    Forall {
        e: Expr,
        local: LocalDecl,
        saved: LocalContext,
    },
    Have {
        e: Expr,
        local: LocalDecl,
        saved: LocalContext,
    },
    /// Open the `have`'s body after its value was visited.
    HaveBody {
        e: Expr,
    },
    MData(KVMap),
}

impl Context {
    /// `pattern (occs)? p` on `goal`: the work that replaces it, in execution order (its goals,
    /// then the closes they defer).
    pub(super) fn conv_pattern<'w>(
        &mut self,
        goal: ProofGoal,
        occs: &Syntax,
        term: &Syntax,
    ) -> Result<Vec<Work<'w>>, NatDefinitionElabError> {
        let (_, _, lhs, rhs) = self.conv_sides(&goal)?;
        self.txn.lctx = goal.lctx.clone();
        let mut state = match expect_null_args(occs, "pattern occurrences")? {
            [] => Occurrences::Listed {
                found: Vec::new(),
                index: 0,
                remaining: std::collections::VecDeque::from([(0, 0)]),
            },
            [occs] => pattern_occurrences(occs)?,
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let pattern = self.conv_pattern_term(term)?;
        let memoize = matches!(state, Occurrences::All(_));
        let mut deferred = Vec::new();
        let lhs = self.instantiate(&lhs)?;
        let result = self.conv_pattern_walk(&pattern, &mut state, memoize, &lhs, &mut deferred)?;
        self.txn.lctx = goal.lctx.clone();
        let goals = match state {
            Occurrences::All(goals) if !goals.is_empty() => goals,
            Occurrences::Listed { index: 0, .. } | Occurrences::All(_) => {
                return Err(error(TacticError::ConvFailure(
                    "'pattern' conv tactic failed, pattern was not found".to_owned(),
                )));
            }
            Occurrences::Listed {
                mut found,
                index,
                remaining,
            } => {
                if let Some((wanted, _)) = remaining.back() {
                    return Err(error(TacticError::ConvFailure(format!(
                        "'pattern' conv tactic failed, pattern was found only {index} times but {} expected",
                        wanted + 1
                    ))));
                }
                found.sort_by_key(|(position, _)| *position);
                found.into_iter().map(|(_, goal)| goal).collect()
            }
        };
        let proof = result
            .proof
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        if !self.conv_resolve_rhs(&rhs, &result.expr)? {
            return Err(error(TacticError::ConvFailure(
                "'pattern' conv tactic failed to resolve the right-hand side".to_owned(),
            )));
        }
        self.conv_goals.remove(&goal.id);
        self.conv_close(goal, proof)?;
        let mut work: Vec<Work<'w>> = goals.into_iter().map(Work::Goal).collect();
        // Innermost closes first, after every goal.
        work.extend(deferred.into_iter().rev());
        Ok(work)
    }

    /// The pattern, elaborated with no expected type in a discarded copy of the state
    /// (`withoutModifyingElabMetaStateWithInfo`, with type class failures ignored), its
    /// unassigned metavariables replaced by marker locals (`abstractMVars`).
    fn conv_pattern_term(&mut self, term: &Syntax) -> Result<Pattern, NatDefinitionElabError> {
        let mut trial = Box::new(self.clone());
        let elaborated = trial.term(term, None);
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        let value = trial.instantiate(&elaborated?.value)?;
        // The unassigned metavariables, in order of first occurrence, with their types.
        let mut order: Vec<MVarId> = Vec::new();
        let mut pending = vec![value.clone()];
        while let Some(expr) = pending.pop() {
            trial.tick()?;
            let expr = trial.instantiate(&expr)?;
            let mut stack = vec![expr];
            while let Some(current) = stack.pop() {
                trial.tick()?;
                if !current.has_expr_mvar() {
                    continue;
                }
                match current.node() {
                    ExprNode::MVar { id } => {
                        if !order.contains(id) {
                            order.push(id.clone());
                            if let Some(decl) = trial.txn.mvars.get_decl(id) {
                                pending.push(decl.type_.clone());
                            }
                        }
                    }
                    ExprNode::App { f, a } => {
                        stack.push(a.clone());
                        stack.push(f.clone());
                    }
                    ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        stack.push(body.clone());
                        stack.push(binder_type.clone());
                    }
                    ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        stack.push(body.clone());
                        stack.push(value.clone());
                        stack.push(type_.clone());
                    }
                    ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                        stack.push(expr.clone())
                    }
                    _ => {}
                }
            }
        }
        // Each marker stands for its metavariable everywhere, its type included.
        let mut replacements: Vec<(MVarId, Expr)> = Vec::new();
        for id in &order {
            trial.tick()?;
            replacements.push((id.clone(), Expr::fvar(FVarId(trial.fresh_name()?))));
        }
        let template = trial.conv_replace_mvars(&value, &replacements)?;
        let mut abstracted = Vec::new();
        for (id, marker) in &replacements {
            trial.tick()?;
            let type_ = trial
                .txn
                .mvars
                .get_decl(id)
                .map(|decl| decl.type_.clone())
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let type_ = trial.instantiate(&type_)?;
            let type_ = trial.conv_replace_mvars(&type_, &replacements)?;
            let ExprNode::FVar { id: marker } = marker.node() else {
                unreachable!("marker local");
            };
            abstracted.push((marker.clone(), type_));
        }
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        let head = head_of(&template);
        Ok(Pattern {
            template,
            markers: abstracted,
            head,
        })
    }

    /// `root` with the metavariables of `replacements` replaced (`root` instantiated).
    fn conv_replace_mvars(
        &mut self,
        root: &Expr,
        replacements: &[(MVarId, Expr)],
    ) -> Result<Expr, NatDefinitionElabError> {
        let root = self.instantiate(root)?;
        let mut done = std::collections::HashMap::<usize, Expr>::new();
        let mut keep = Vec::new();
        let mut work = vec![(root.clone(), false)];
        while let Some((term, exit)) = work.pop() {
            let key = term.allocation_identity();
            if done.contains_key(&key) {
                continue;
            }
            self.tick()?;
            if !term.has_expr_mvar() {
                done.insert(key, term.clone());
                keep.push(term);
                continue;
            }
            let children: Vec<Expr> = match term.node() {
                ExprNode::App { f, a } => vec![f.clone(), a.clone()],
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => vec![binder_type.clone(), body.clone()],
                ExprNode::LetE {
                    type_, value, body, ..
                } => vec![type_.clone(), value.clone(), body.clone()],
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => vec![expr.clone()],
                _ => Vec::new(),
            };
            if !exit
                && children
                    .iter()
                    .any(|c| !done.contains_key(&c.allocation_identity()))
            {
                work.push((term.clone(), true));
                for child in children.into_iter().rev() {
                    work.push((child, false));
                }
                continue;
            }
            let get = |e: &Expr| done[&e.allocation_identity()].clone();
            let result = match term.node() {
                ExprNode::MVar { id } => replacements
                    .iter()
                    .find(|(candidate, _)| candidate == id)
                    .map_or_else(|| term.clone(), |(_, marker)| marker.clone()),
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
                _ => term.clone(),
            };
            done.insert(key, result);
            keep.push(term);
        }
        Ok(done[&root.allocation_identity()].clone())
    }

    /// `matchPattern? pattern e`: `e`, or its longest prefix, definitionally equal to a fresh
    /// instance of the pattern at reducible transparency, with the arguments after it.
    fn conv_pattern_match(
        &mut self,
        pattern: &Pattern,
        e: &Expr,
    ) -> Result<Option<(Expr, Vec<Expr>)>, NatDefinitionElabError> {
        let mut candidate = cleanup(e);
        let mut extra = Vec::new();
        loop {
            self.tick()?;
            if head_of(&candidate) != pattern.head {
                return Ok(None);
            }
            let mut trial = Box::new(self.clone());
            let attempt = (|| -> Result<bool, NatDefinitionElabError> {
                let mut instance = pattern.template.clone();
                let mut holes: Vec<(FVarId, Expr)> = Vec::new();
                for (marker, type_) in &pattern.markers {
                    let mut type_ = type_.clone();
                    for (earlier, hole) in &holes {
                        type_ = type_
                            .abstract_fvar(earlier, 0)
                            .and_then(|t| t.subst_loose(0, std::slice::from_ref(hole)))
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                    }
                    let hole = trial.hole(type_)?;
                    instance = instance
                        .abstract_fvar(marker, 0)
                        .and_then(|t| t.subst_loose(0, std::slice::from_ref(&hole)))
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                    holes.push((marker.clone(), hole));
                }
                let mut budget = UnificationBudget::new(trial.kernel);
                budget.transparency = UnificationTransparency::Abbreviations;
                trial.proof_types_match_with_budget(&instance, &candidate, budget)
            })();
            self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
            match attempt {
                Ok(true) => {
                    extra.reverse();
                    return Ok(Some((candidate, extra)));
                }
                Ok(false) => {}
                Err(problem) if super::super::backtrack::recoverable(&problem) => {}
                Err(problem) => return Err(problem),
            }
            let ExprNode::App { f, a } = candidate.node() else {
                return Ok(None);
            };
            extra.push(a.clone());
            candidate = f.clone();
        }
    }

    /// Whether the pattern's head occurs anywhere in `e`, where the pin's traversal could
    /// match it but this walk does not follow.
    fn conv_pattern_head_occurs(
        &mut self,
        pattern: &Pattern,
        e: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut stack = vec![e.clone()];
        let mut seen = std::collections::HashSet::new();
        while let Some(current) = stack.pop() {
            self.tick()?;
            if !seen.insert(current.allocation_identity()) {
                continue;
            }
            if head_of(&current) == pattern.head {
                return Ok(true);
            }
            match current.node() {
                ExprNode::App { f, a } => {
                    stack.push(a.clone());
                    stack.push(f.clone());
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    stack.push(body.clone());
                    stack.push(binder_type.clone());
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    stack.push(body.clone());
                    stack.push(value.clone());
                    stack.push(type_.clone());
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    stack.push(expr.clone())
                }
                _ => {}
            }
        }
        Ok(false)
    }

    /// A conv goal for the matched subterm `matched`, in the walk's current context; when the
    /// walk is under binders, its right-hand side and proof are lifted out of them
    /// ([`Context::conv_lift`]). Returns the result standing for `matched` applied to `extra`.
    fn conv_pattern_occurrence<'w>(
        &mut self,
        matched: &Expr,
        extra: &[Expr],
        binders: &[LocalDecl],
        deferred: &mut Vec<Work<'w>>,
    ) -> Result<(Simplified, ProofGoal), NatDefinitionElabError> {
        let extended = self.txn.lctx.clone();
        let (r, hole, goal) = self.conv_goal_for(matched, &Name::anonymous())?;
        let alpha = self.conv_type(matched)?;
        let level = self.conv_level(&alpha)?;
        let r_type = self.conv_close_binders(binders, alpha.clone(), false)?;
        let lifted_r = self.conv_lift(deferred, &extended, binders, r.clone(), r_type)?;
        let applied_r = binders.iter().fold(lifted_r, |e, local| {
            Expr::app(e, Expr::fvar(local.id.clone()))
        });
        let applied_r = if binders.is_empty() { r } else { applied_r };
        let equation = equality::equation(level, alpha, matched.clone(), applied_r.clone());
        let p_type = self.conv_close_binders(binders, equation, false)?;
        let lifted_p = self.conv_lift(deferred, &extended, binders, hole.clone(), p_type)?;
        let mut proof = if binders.is_empty() {
            hole
        } else {
            binders.iter().fold(lifted_p, |e, local| {
                Expr::app(e, Expr::fvar(local.id.clone()))
            })
        };
        let mut left = matched.clone();
        let mut right = applied_r;
        for argument in extra {
            self.tick()?;
            proof = self.conv_congr_fun(proof, &left, &right, argument)?;
            left = Expr::app(left, argument.clone());
            right = Expr::app(right, argument.clone());
        }
        Ok((
            Simplified {
                expr: right,
                proof: Some(proof),
            },
            goal,
        ))
    }

    /// The `Simp.main` walk with the pattern's `pre` method, over `root` in the current
    /// context. An explicit worklist: tasks run last-pushed first, results stack up.
    fn conv_pattern_walk<'w>(
        &mut self,
        pattern: &Pattern,
        state: &mut Occurrences,
        memoize: bool,
        root: &Expr,
        deferred: &mut Vec<Work<'w>>,
    ) -> Result<Simplified, NatDefinitionElabError> {
        let mut tasks = vec![Task::Visit(root.clone())];
        let mut values: Vec<Simplified> = Vec::new();
        let mut binders: Vec<LocalDecl> = Vec::new();
        let mut cache: Vec<(Expr, Simplified)> = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(e) => {
                    if state.is_done() {
                        values.push(Simplified {
                            expr: e,
                            proof: None,
                        });
                        continue;
                    }
                    if memoize {
                        let mut hit = None;
                        for (key, value) in &cache {
                            if key.allocation_identity() == e.allocation_identity() {
                                hit = Some(value.clone());
                                break;
                            }
                        }
                        if hit.is_none() {
                            for (key, value) in &cache {
                                if self.rewrite_same(key, &e)? {
                                    hit = Some(value.clone());
                                    break;
                                }
                            }
                        }
                        if let Some(value) = hit {
                            values.push(value);
                            continue;
                        }
                    }
                    if let Some((matched, extra)) = self.conv_pattern_match(pattern, &e)? {
                        if state.is_ready() {
                            let (result, goal) =
                                self.conv_pattern_occurrence(&matched, &extra, &binders, deferred)?;
                            match state {
                                Occurrences::All(goals) => goals.push(goal),
                                Occurrences::Listed {
                                    found,
                                    index,
                                    remaining,
                                } => {
                                    let (_, position) =
                                        remaining.pop_front().expect("ready occurrence");
                                    found.push((position, goal));
                                    *index += 1;
                                }
                            }
                            if memoize {
                                cache.push((e.clone(), result.clone()));
                            }
                            values.push(result);
                            continue;
                        }
                        if let Occurrences::Listed { index, .. } = state {
                            *index += 1;
                        }
                    }
                    self.conv_pattern_children(pattern, e, &mut tasks, &mut values, &mut binders)?;
                }
                Task::MData(data) => {
                    let inner = values.pop().expect("metadata body");
                    values.push(Simplified {
                        expr: Expr::mdata(data, inner.expr),
                        proof: inner.proof,
                    });
                }
                Task::App { e, f, args } => {
                    let result = self.conv_pattern_app(&e, &f, &args, &mut values)?;
                    values.push(result);
                }
                Task::Lambda {
                    locals,
                    body: original,
                    saved,
                } => {
                    let body = values.pop().expect("lambda body");
                    let result = self.conv_pattern_lambdas(&locals, &original, body)?;
                    for _ in &locals {
                        binders.pop();
                    }
                    self.txn.lctx = saved;
                    values.push(result);
                }
                Task::Arrow { e } => {
                    let body = values.pop().expect("arrow conclusion");
                    let domain = values.pop().expect("arrow premise");
                    values.push(self.conv_pattern_arrow(&e, domain, body)?);
                }
                Task::Forall { e, local, saved } => {
                    let body = values.pop().expect("forall body");
                    binders.pop();
                    let result = self.conv_pattern_forall(&e, &local, body)?;
                    self.txn.lctx = saved;
                    values.push(result);
                }
                Task::HaveBody { e } => {
                    let ExprNode::LetE {
                        decl_name,
                        type_,
                        body,
                        ..
                    } = e.node()
                    else {
                        return Err(failure(SourceInferenceError::Scope));
                    };
                    let saved = self.txn.lctx.clone();
                    let local =
                        self.conv_local(decl_name.clone(), type_.clone(), BinderInfo::Default)?;
                    let opened = self.substitute(body, &Expr::fvar(local.id.clone()))?;
                    binders.push(local.clone());
                    tasks.push(Task::Have {
                        e: e.clone(),
                        local,
                        saved,
                    });
                    tasks.push(Task::Visit(opened));
                }
                Task::Have { e, local, saved } => {
                    let body = values.pop().expect("have body");
                    let value = values.pop().expect("have value");
                    binders.pop();
                    let result = self.conv_pattern_have(&e, &local, value, body)?;
                    self.txn.lctx = saved;
                    values.push(result);
                }
            }
        }
        values
            .pop()
            .ok_or_else(|| failure(SourceInferenceError::Scope))
    }

    /// The children of `e` the pin's traversal visits, scheduled.
    fn conv_pattern_children(
        &mut self,
        pattern: &Pattern,
        e: Expr,
        tasks: &mut Vec<Task>,
        values: &mut Vec<Simplified>,
        binders: &mut Vec<LocalDecl>,
    ) -> Result<(), NatDefinitionElabError> {
        let unchanged = |e: Expr| Simplified {
            expr: e,
            proof: None,
        };
        match e.node() {
            ExprNode::MData { data, expr } => {
                tasks.push(Task::MData(data.clone()));
                tasks.push(Task::Visit(expr.clone()));
            }
            ExprNode::App { .. } => {
                let (f, args) = spine(&e);
                // `Simp.congr`: an `@[congr]` theorem, or an automatically generated one with
                // casts (`tryAutoCongrTheorem?`), would be tried first.
                let congr_head = matches!(f.node(), ExprNode::Const { name, .. }
                    if CONGR_HEADS.iter().any(|head| name == &Name::from_components(head.iter().copied())));
                let info = self.conv_fun_info(&f, args.len())?;
                let auto = if congr_head {
                    true
                } else {
                    let full = self.conv_fun_info(&f, usize::MAX)?;
                    let kinds = self.conv_congr_simp_kinds_or_fixed(&f, &full)?;
                    kinds.len() == args.len()
                        && kinds
                            .iter()
                            .any(|kind| matches!(kind, ArgKind::Cast | ArgKind::SubsingletonInst))
                };
                if auto {
                    if self.conv_pattern_head_occurs(pattern, &e)? {
                        return Err(error(TacticError::ConvUnsupported(
                            "`pattern` inside an application simp rewrites by a congruence theorem",
                        )));
                    }
                    values.push(unchanged(e));
                    return Ok(());
                }
                // `simpAppUsingCongr`: the function, then each argument without forward
                // dependencies (or of an arrow), the others kept (`dsimp`, which the neutral
                // configuration leaves as it is).
                let mut plan = Vec::new();
                let mut prefix = f.clone();
                for (i, arg) in args.iter().enumerate() {
                    self.tick()?;
                    let visited = match info.params.get(i) {
                        Some(param) if !param.has_fwd_deps => true,
                        _ => self.conv_is_arrow(&prefix)?,
                    };
                    plan.push((arg.clone(), visited));
                    prefix = Expr::app(prefix, arg.clone());
                }
                tasks.push(Task::App {
                    e: e.clone(),
                    f: f.clone(),
                    args: plan.clone(),
                });
                for (arg, visited) in plan.iter().rev() {
                    if *visited {
                        tasks.push(Task::Visit(arg.clone()));
                    }
                }
                tasks.push(Task::Visit(f));
            }
            ExprNode::Lam { .. } => {
                // `lambdaTelescopeDSimp`: every leading binder.
                let saved = self.txn.lctx.clone();
                let mut body = e.clone();
                let mut locals = Vec::new();
                while let ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body: inner,
                    binder_info,
                } = body.node()
                {
                    self.tick()?;
                    let local =
                        self.conv_local(binder_name.clone(), binder_type.clone(), *binder_info)?;
                    let opened = self.substitute(inner, &Expr::fvar(local.id.clone()))?;
                    binders.push(local.clone());
                    locals.push(local);
                    body = opened;
                }
                tasks.push(Task::Lambda {
                    locals,
                    body: body.clone(),
                    saved,
                });
                tasks.push(Task::Visit(body));
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                if !body.has_loose_bvar(0) {
                    // `simpArrow`: the premise, then the conclusion (not contextual).
                    let conclusion = body
                        .subst_loose(0, &[Expr::sort(Level::zero())])
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                    tasks.push(Task::Arrow { e: e.clone() });
                    tasks.push(Task::Visit(conclusion));
                    tasks.push(Task::Visit(binder_type.clone()));
                } else if self.conv_is_prop(&e)? {
                    if self.conv_is_prop(binder_type)?
                        && self.conv_pattern_head_occurs(pattern, binder_type)?
                    {
                        return Err(error(TacticError::ConvUnsupported(
                            "`pattern` in the domain of a proposition `∀`",
                        )));
                    }
                    let saved = self.txn.lctx.clone();
                    let local =
                        self.conv_local(binder_name.clone(), binder_type.clone(), *binder_info)?;
                    let opened = self.substitute(body, &Expr::fvar(local.id.clone()))?;
                    binders.push(local.clone());
                    tasks.push(Task::Forall {
                        e: e.clone(),
                        local,
                        saved,
                    });
                    tasks.push(Task::Visit(opened));
                } else {
                    // `dsimp` only.
                    values.push(unchanged(e));
                }
            }
            ExprNode::LetE { value, non_dep, .. } => {
                if *non_dep {
                    // `simpHaveTelescope`: the value, then the body.
                    tasks.push(Task::HaveBody { e: e.clone() });
                    tasks.push(Task::Visit(value.clone()));
                } else {
                    // A dependent `let` is only `dsimp`ed.
                    values.push(unchanged(e));
                }
            }
            ExprNode::Proj { .. } => {
                if self.conv_pattern_head_occurs(pattern, &e)? {
                    return Err(error(TacticError::ConvUnsupported(
                        "`pattern` inside a projection",
                    )));
                }
                values.push(unchanged(e));
            }
            _ => values.push(unchanged(e)),
        }
        Ok(())
    }

    /// `getCongrSimpKinds`, read as all `.fixed` where it would refuse (a class constructor).
    fn conv_congr_simp_kinds_or_fixed(
        &mut self,
        f: &Expr,
        info: &FunInfo,
    ) -> Result<Vec<ArgKind>, NatDefinitionElabError> {
        match self.conv_congr_simp_kinds(f, info) {
            Ok(kinds) => Ok(kinds),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                TacticError::ConvUnsupported(_),
            ))) => Ok(vec![ArgKind::Fixed; info.params.len()]),
            Err(problem) => Err(problem),
        }
    }

    /// `(← whnfD (← inferType f)).isArrow`.
    fn conv_is_arrow(&mut self, f: &Expr) -> Result<bool, NatDefinitionElabError> {
        let type_ = self.conv_type(f)?;
        let type_ = self.whnf(&type_)?;
        Ok(matches!(type_.node(), ExprNode::ForallE { body, .. } if !body.has_loose_bvar(0)))
    }

    /// `simpAppUsingCongr`'s combination: `congrArg`, `congrFun'`, `congr` and `congrFun`.
    fn conv_pattern_app(
        &mut self,
        e: &Expr,
        f: &Expr,
        args: &[(Expr, bool)],
        values: &mut Vec<Simplified>,
    ) -> Result<Simplified, NatDefinitionElabError> {
        let visited = args.iter().filter(|(_, visited)| *visited).count();
        let mut results = values.split_off(values.len() - visited - 1);
        let mut current = results.remove(0);
        let mut original = f.clone();
        let mut results = results.into_iter();
        for (arg, was_visited) in args {
            self.tick()?;
            let applied = Expr::app(original.clone(), arg.clone());
            if *was_visited {
                let argument = results.next().expect("visited argument");
                current = self.conv_pattern_congr(&applied, current, argument)?;
            } else {
                current = self.conv_pattern_congr_fun(&applied, current)?;
            }
            original = applied;
        }
        let _ = e;
        Ok(current)
    }

    /// `mkCongrPrefix declName e`: `declName.{u, v} α β`, `α` the argument's type, `β` `e`'s.
    fn conv_congr_prefix(
        &mut self,
        name: &[&str],
        e: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let ExprNode::App { a, .. } = e.node() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let alpha = self.conv_type(a)?;
        let u = self.conv_level(&alpha)?;
        let beta = self.conv_type(e)?;
        let v = self.conv_level(&beta)?;
        Ok(app(self.conv_constant(name, vec![u, v])?, [alpha, beta]))
    }

    /// `mkCongr'`.
    fn conv_pattern_congr(
        &mut self,
        e: &Expr,
        function: Simplified,
        argument: Simplified,
    ) -> Result<Simplified, NatDefinitionElabError> {
        let ExprNode::App { f, a } = e.node() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let expr = Expr::app(function.expr.clone(), argument.expr.clone());
        let proof = match (function.proof, argument.proof) {
            (None, None) => None,
            (Some(hf), None) => {
                let prefix = self.conv_congr_prefix(&["congrFun'"], e)?;
                Some(app(prefix, [f.clone(), function.expr, hf, argument.expr]))
            }
            (None, Some(ha)) => {
                let prefix = self.conv_congr_prefix(&["congrArg"], e)?;
                Some(app(prefix, [a.clone(), argument.expr, function.expr, ha]))
            }
            (Some(hf), Some(ha)) => {
                let prefix = self.conv_congr_prefix(&["congr"], e)?;
                Some(app(
                    prefix,
                    [f.clone(), function.expr, a.clone(), argument.expr, hf, ha],
                ))
            }
        };
        Ok(Simplified { expr, proof })
    }

    /// `mkCongrFun'`: the argument kept.
    fn conv_pattern_congr_fun(
        &mut self,
        e: &Expr,
        function: Simplified,
    ) -> Result<Simplified, NatDefinitionElabError> {
        let ExprNode::App { f, a } = e.node() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let expr = Expr::app(function.expr.clone(), a.clone());
        let Some(hf) = function.proof else {
            return Ok(Simplified { expr, proof: None });
        };
        let proof = self.conv_congr_fun(hf, f, &function.expr, a)?;
        Ok(Simplified {
            expr,
            proof: Some(proof),
        })
    }

    /// `Result.addLambdas xs`: `fun xs => e'`, its equation by `funext` per binder, from the
    /// innermost out (`funext (fun x => h)`). `original` is the body before, under `locals`.
    fn conv_pattern_lambdas(
        &mut self,
        locals: &[LocalDecl],
        original: &Expr,
        body: Simplified,
    ) -> Result<Simplified, NatDefinitionElabError> {
        let expr = self.conv_close_binders(locals, body.expr.clone(), true)?;
        let Some(mut proof) = body.proof else {
            return Ok(Simplified { expr, proof: None });
        };
        for index in (0..locals.len()).rev() {
            self.tick()?;
            let inner = &locals[index..];
            let f = self.conv_close_binders(inner, original.clone(), true)?;
            let g = self.conv_close_binders(inner, body.expr.clone(), true)?;
            let local = &locals[index];
            let type_ = self.conv_type(&f)?;
            let type_ = self.whnf(&type_)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body: codomain,
                ..
            } = type_.node()
            else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let u = self.conv_level(binder_type)?;
            let codomain_at = self.substitute(codomain, &Expr::fvar(local.id.clone()))?;
            let v = self.conv_level(&codomain_at)?;
            let beta = Expr::lam(
                binder_name.clone(),
                binder_type.clone(),
                codomain.clone(),
                BinderInfo::Default,
            );
            let pointwise = self.conv_close_binders(std::slice::from_ref(local), proof, true)?;
            proof = app(
                self.conv_constant(&["funext"], vec![u, v])?,
                [binder_type.clone(), beta, f, g, pointwise],
            );
        }
        Ok(Simplified {
            expr,
            proof: Some(proof),
        })
    }

    /// `simpArrow` without context: `implies_congr` of the two sides' equations.
    fn conv_pattern_arrow(
        &mut self,
        e: &Expr,
        premise: Simplified,
        conclusion: Simplified,
    ) -> Result<Simplified, NatDefinitionElabError> {
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = e.node()
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let lifted = conclusion
            .expr
            .lift_loose(0, 1)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let expr = Expr::forall_e(
            binder_name.clone(),
            premise.expr.clone(),
            lifted,
            *binder_info,
        );
        if premise.proof.is_none() && conclusion.proof.is_none() {
            return Ok(Simplified { expr, proof: None });
        }
        let p1 = binder_type.clone();
        let q1 = body
            .subst_loose(0, &[Expr::sort(Level::zero())])
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let hp = match premise.proof {
            Some(proof) => proof,
            None => self.conv_eq_refl(&p1)?,
        };
        let hq = match conclusion.proof {
            Some(proof) => proof,
            None => self.conv_eq_refl(&q1)?,
        };
        let u = self.conv_level(&p1)?;
        let v = self.conv_level(&q1)?;
        let proof = app(
            self.conv_constant(&["implies_congr"], vec![u, v])?,
            [p1, premise.expr, q1, conclusion.expr, hp, hq],
        );
        Ok(Simplified {
            expr,
            proof: Some(proof),
        })
    }

    /// `simpForall` on a proposition: `forall_congr` of the body's equation.
    fn conv_pattern_forall(
        &mut self,
        e: &Expr,
        local: &LocalDecl,
        body: Simplified,
    ) -> Result<Simplified, NatDefinitionElabError> {
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body: original,
            binder_info,
        } = e.node()
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let expr =
            self.conv_close_binders(std::slice::from_ref(local), body.expr.clone(), false)?;
        let Some(proof) = body.proof else {
            return Ok(Simplified {
                expr: e.clone(),
                proof: None,
            });
        };
        let u = self.conv_level(binder_type)?;
        let p = Expr::lam(
            binder_name.clone(),
            binder_type.clone(),
            original.clone(),
            *binder_info,
        );
        let q = self.conv_close_binders(std::slice::from_ref(local), body.expr, true)?;
        let h = self.conv_close_binders(std::slice::from_ref(local), proof, true)?;
        let proof = app(
            self.conv_constant(&["forall_congr"], vec![u])?,
            [binder_type.clone(), p, q, h],
        );
        Ok(Simplified {
            expr,
            proof: Some(proof),
        })
    }

    /// `simpHaveTelescope` on one `have`: `let_congr`, `let_val_congr` or `let_body_congr`.
    fn conv_pattern_have(
        &mut self,
        e: &Expr,
        local: &LocalDecl,
        value: Simplified,
        body: Simplified,
    ) -> Result<Simplified, NatDefinitionElabError> {
        let ExprNode::LetE {
            decl_name,
            type_,
            value: original_value,
            body: original_body,
            ..
        } = e.node()
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let new_body = body
            .expr
            .abstract_fvar(&local.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let expr = Expr::let_e(
            decl_name.clone(),
            type_.clone(),
            value.expr.clone(),
            new_body.clone(),
            true,
        );
        if value.proof.is_none() && body.proof.is_none() {
            return Ok(Simplified {
                expr: e.clone(),
                proof: None,
            });
        }
        let u = self.conv_level(type_)?;
        let body_type = self.conv_type(&body.expr)?;
        let v = self.conv_level(&body_type)?;
        if value.proof.is_some() && self.elimination_reads(&body_type)?.contains(&local.id) {
            return Err(error(TacticError::ConvUnsupported(
                "`pattern` in the value of a `have` whose body's type depends on it",
            )));
        }
        let b = Expr::lam(
            decl_name.clone(),
            type_.clone(),
            original_body.clone(),
            BinderInfo::Default,
        );
        let b2 = Expr::lam(
            decl_name.clone(),
            type_.clone(),
            new_body,
            BinderInfo::Default,
        );
        let proof = match (value.proof, body.proof) {
            (Some(hv), None) => {
                // `let_val_congr {α β} {a a'} (b : α → β) (h : a = a')`.
                app(
                    self.conv_constant(&["let_val_congr"], vec![u, v])?,
                    [
                        type_.clone(),
                        body_type,
                        original_value.clone(),
                        value.expr,
                        b,
                        hv,
                    ],
                )
            }
            (hv, Some(hb)) => {
                let pointwise = self.conv_close_binders(std::slice::from_ref(local), hb, true)?;
                match hv {
                    // `let_congr {α β} {a a'} {b b'} (h₁ : a = a') (h₂ : ∀ x, b x = b' x)`.
                    Some(hv) => app(
                        self.conv_constant(&["let_congr"], vec![u, v])?,
                        [
                            type_.clone(),
                            body_type,
                            original_value.clone(),
                            value.expr,
                            b,
                            b2,
                            hv,
                            pointwise,
                        ],
                    ),
                    // `let_body_congr {α} {β : α → Sort v} {b b'} (a : α) (h : ∀ x, b x = b' x)`.
                    None => {
                        let family = Expr::lam(
                            decl_name.clone(),
                            type_.clone(),
                            body_type
                                .abstract_fvar(&local.id, 0)
                                .map_err(|_| failure(SourceInferenceError::Scope))?,
                            BinderInfo::Default,
                        );
                        app(
                            self.conv_constant(&["let_body_congr"], vec![u, v])?,
                            [
                                type_.clone(),
                                family,
                                b,
                                b2,
                                original_value.clone(),
                                pointwise,
                            ],
                        )
                    }
                }
            }
            (None, None) => unreachable!("handled above"),
        };
        Ok(Simplified {
            expr,
            proof: Some(proof),
        })
    }
}

/// `(occs := *)` or `(occs := n₁ … nₖ)`, as `PatternMatchState`.
fn pattern_occurrences(syntax: &Syntax) -> Result<Occurrences, NatDefinitionElabError> {
    let [open, keyword, assign, inner, close] = expect_node(syntax, &conv_kind("occs"), 5, "occs")?
    else {
        return Err(error(TacticError::MalformedScript));
    };
    expect_atom(open, "(", "occs parenthesis")?;
    expect_atom(keyword, "occs", "occs keyword")?;
    expect_atom(assign, ":=", "occs assignment")?;
    expect_atom(close, ")", "occs parenthesis")?;
    if inner.kind() == Some(&conv_kind("occsWildcard")) {
        return Ok(Occurrences::All(Vec::new()));
    }
    let [numbers] = expect_node(inner, &conv_kind("occsIndexed"), 1, "occs list")? else {
        return Err(error(TacticError::MalformedScript));
    };
    let mut ids = Vec::new();
    for (position, number) in expect_null_args(numbers, "occs numbers")?
        .iter()
        .enumerate()
    {
        let [Syntax::Atom { val, .. }] = expect_node(
            number,
            &Name::str(Name::anonymous(), "num"),
            1,
            "occs number",
        )?
        else {
            return Err(error(TacticError::MalformedScript));
        };
        let value: usize = val
            .parse()
            .map_err(|_| error(TacticError::MalformedScript))?;
        if value == 0 {
            return Err(error(TacticError::ConvFailure(
                "positive integer expected".to_owned(),
            )));
        }
        ids.push((value - 1, position));
    }
    ids.sort_by_key(|(value, _)| *value);
    if ids.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return Err(error(TacticError::ConvFailure(
            "occurrence list is not distinct".to_owned(),
        )));
    }
    Ok(Occurrences::Listed {
        found: Vec::new(),
        index: 0,
        remaining: ids.into_iter().collect(),
    })
}
