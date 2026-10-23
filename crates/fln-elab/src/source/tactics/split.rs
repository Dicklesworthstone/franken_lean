//! `split` (`evalSplit`, vendored src/Lean/Elab/Tactic/Split.lean:17-43): the first `if` in the
//! goal, or in one hypothesis, is split by cases on its decision (`splitIfTarget?` and
//! `splitIfLocalDecl?`, vendored src/Lean/Meta/Tactic/SplitIf.lean:316-340, through
//! `MVarId.byCasesDec`, src/Lean/Meta/Tactic/Cases.lean:371-377). In each case every
//! conditional that a hypothesis then decides is reduced, as `simpIfTarget`/`simpIfLocalDecl`
//! (SplitIf.lean:284-313) reduce them with `if_pos`, `if_neg`, `dif_pos` and `dif_neg` under
//! the default `backward.split` (line 131).
//!
//! A conditional is the pin's `ite`/`dite`, or what this engine elaborates a source `if` to:
//! `Decidable.rec` with a constant motive, its dictionary let-bound as elaborated or bare once
//! unfolded, and for `if b` on a `Bool` the let-bound `Bool.rec`, which the pin reads as
//! `if b = true`. A `match` (the pin's matcher, or this engine's compiled recursor) is refused:
//! the pin splits it with the matcher's splitter (vendored src/Lean/Meta/Tactic/Split.lean),
//! which is not implemented here.
//!
//! The proof is not the pin's. The case split is `Decidable.rec` on the selected dictionary, as
//! `byCasesDec` cases on it; each reduction eliminates one decided dictionary (or `Bool`) with
//! a motive abstracting it at its conditionals, closing the impossible case by `absurd`, so a
//! reduced conditional is that recursor's iota reduction. The kernel checks all of it with the
//! declaration. A reduction rewrites where `simp`'s congruence reaches and, inside a conditional
//! whose condition it rewrites, the dictionary and evidence binders that follow the condition,
//! where `ite_congr`/`dite_congr` synthesize a new dictionary and cast the branches instead; a
//! conditional whose dictionary does not mention the change is refused (typed).
use super::decision::{apps, constant};
use super::*;
use crate::lctx::LocalContext;
use fln_core::expr::BinderInfo;
use fln_env::constants::ConstantInfo;
use std::collections::{HashMap, HashSet};

/// Reductions in one case: each eliminates one decided dictionary or `Bool`.
const MAX_REDUCTIONS: usize = 256;

#[derive(Clone)]
enum Decision {
    /// A `Decidable c` dictionary.
    Dictionary(Expr),
    /// A `Bool`, whose condition is the pin's `b = true`.
    Boolean(Expr),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Form {
    /// `@ite α c d t e …`.
    Ite,
    /// `@dite α c d t e …`.
    Dite,
    /// `@Decidable.rec c (fun _ => α) e t d …`: an unfolded source `if`.
    Recursor,
    /// `let _ : Decidable c := d; @Decidable.rec c (fun _ => α) e t #0`: a source `if`.
    LetRecursor,
    /// `let _ : Bool := b; Bool.rec (fun _ => α) e t #0`: a source `if b` on a `Bool`.
    LetBoolean,
    /// `Bool.rec (fun _ => α) e t b …`: a source `if b` unfolded, or a `match` on `b`. Only
    /// reduced where it follows a changed condition (a dictionary synthesized for the condition
    /// unfolded reads it so), never selected or decided as an `if`.
    Boolean,
}

#[derive(Clone)]
struct Conditional {
    form: Form,
    /// The pin's condition, outside any binder of the node.
    condition: Expr,
    decision: Decision,
}

enum Candidate {
    Conditional(Conditional),
    Match,
}

/// Where the reduction rewrites a subterm.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Reach {
    /// Where the pin's `simp` rewrites: the congruence it builds, under binders.
    Simp,
    /// Everywhere: a dictionary, or a binder's type, that follows a changed condition.
    Whole,
    /// A branch of a dependent conditional: the type of its evidence follows the condition,
    /// its body is rewritten as by `simp`.
    Branch,
    /// A constant motive: only the type of its binder, which reads the condition.
    Binder,
}

/// A parameter of an applied function, as the pin's `getFunInfo` reads it.
#[derive(Clone, Copy)]
struct Parameter {
    explicit: bool,
    proof: bool,
    /// A later parameter's type, or the result type, reads it: `simp` keeps it fixed.
    dependent: bool,
}

/// What `split` splits.
#[derive(Clone)]
enum Subject {
    Target,
    Hypothesis(LocalDecl),
}

/// One case: its hypothesis, and the goal (or hypothesis type) with the conditionals it
/// decides reduced, with the transports between the two, outermost first.
struct Case {
    local: LocalDecl,
    reduced: Expr,
    transports: Vec<Expr>,
}

struct Plan {
    condition: Expr,
    dictionary: Expr,
    yes: Case,
    no: Case,
}

fn name(components: &[&str]) -> Name {
    Name::from_components(components.iter().copied())
}

/// An application's head and arguments in order.
fn spine(expr: &Expr) -> (Expr, Vec<Expr>) {
    let mut head = expr;
    let mut args = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        head = f;
    }
    args.reverse();
    (head.clone(), args)
}

fn is_constant_motive(motive: &Expr) -> bool {
    matches!(motive.node(), ExprNode::Lam { body, .. } if !body.has_loose_bvar(0))
}

/// `expr` under one binder it does not read, outside it.
fn lower(expr: &Expr) -> Option<Expr> {
    if expr.has_loose_bvar(0) {
        return None;
    }
    expr.subst_loose(0, &[Expr::sort(Level::zero())]).ok()
}

fn is_head(expr: &Expr, head: &[&str]) -> bool {
    matches!(spine(expr).0.node(), ExprNode::Const { name: actual, .. } if actual == &name(head))
}

/// The pin's `b = true` for a `Bool` `b`.
fn boolean_condition(value: Expr) -> Expr {
    apps(
        constant("Eq", vec![Level::one()]),
        [
            constant("Bool", vec![]),
            value,
            constant("Bool.true", vec![]),
        ],
    )
}

fn negation(proposition: Expr) -> Expr {
    Expr::app(constant("Not", vec![]), proposition)
}

/// The conditional `expr` is, if any. `applied` also reads a let-bound conditional at the head
/// of an application, as the pin's `isCandidate?` reads an over-applied `ite`.
fn conditional(expr: &Expr, applied: bool) -> Option<Conditional> {
    let (head, args) = spine(expr);
    match head.node() {
        ExprNode::Const { name: head, .. } if args.len() >= 5 => {
            if head == &name(&["ite"]) || head == &name(&["dite"]) {
                return Some(Conditional {
                    form: if head == &name(&["ite"]) {
                        Form::Ite
                    } else {
                        Form::Dite
                    },
                    condition: args[1].clone(),
                    decision: Decision::Dictionary(args[2].clone()),
                });
            }
            if head == &name(&["Decidable", "rec"]) && is_constant_motive(&args[1]) {
                return Some(Conditional {
                    form: Form::Recursor,
                    condition: args[0].clone(),
                    decision: Decision::Dictionary(args[4].clone()),
                });
            }
            None
        }
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            ..
        } if decl_name.is_anonymous() && (applied || args.is_empty()) => {
            let (inner, inner_args) = spine(body);
            let ExprNode::Const { name: inner, .. } = inner.node() else {
                return None;
            };
            let bound = |arg: &Expr| matches!(arg.node(), ExprNode::BVar { idx: 0 });
            if inner == &name(&["Decidable", "rec"])
                && inner_args.len() == 5
                && is_constant_motive(&inner_args[1])
                && bound(&inner_args[4])
                && is_head(type_, &["Decidable"])
            {
                // The dictionary is elaborated as `let _ : Prop := c; d`, keeping the condition.
                let dictionary = match value.node() {
                    ExprNode::LetE { type_, body, .. } if matches!(type_.node(), ExprNode::Sort { level } if level.is_zero()) => {
                        lower(body)?
                    }
                    _ => value.clone(),
                };
                return Some(Conditional {
                    form: Form::LetRecursor,
                    condition: lower(&inner_args[0])?,
                    decision: Decision::Dictionary(dictionary),
                });
            }
            if inner == &name(&["Bool", "rec"])
                && inner_args.len() == 4
                && is_constant_motive(&inner_args[0])
                && bound(&inner_args[3])
                && matches!(type_.node(), ExprNode::Const { name: actual, .. } if actual == &name(&["Bool"]))
                && !matches!(value.node(), ExprNode::BVar { .. })
            {
                return Some(Conditional {
                    form: Form::LetBoolean,
                    condition: boolean_condition(value.clone()),
                    decision: Decision::Boolean(value.clone()),
                });
            }
            None
        }
        _ => None,
    }
}

/// An unfolded `Bool` conditional ([`Form::Boolean`]).
fn boolean_conditional(expr: &Expr) -> Option<Conditional> {
    let (head, args) = spine(expr);
    match head.node() {
        ExprNode::Const { name: head, .. }
            if head == &name(&["Bool", "rec"])
                && args.len() >= 4
                && is_constant_motive(&args[0]) =>
        {
            Some(Conditional {
                form: Form::Boolean,
                condition: boolean_condition(args[3].clone()),
                decision: Decision::Boolean(args[3].clone()),
            })
        }
        _ => None,
    }
}

/// The parts of a conditional the pin's `findSplit?` visits when it is no candidate, and
/// `simp`'s `ite_congr`/`dite_congr` rewrite: the condition, then both branches, then any
/// further arguments.
fn conditional_parts(expr: &Expr, form: Form) -> Vec<Expr> {
    let (head, args) = spine(expr);
    match form {
        Form::Ite | Form::Dite => [&args[1], &args[3], &args[4]]
            .into_iter()
            .chain(&args[5..])
            .cloned()
            .collect(),
        Form::Recursor => [&args[0], &args[3], &args[2]]
            .into_iter()
            .chain(&args[5..])
            .cloned()
            .collect(),
        Form::Boolean => args.iter().skip(1).cloned().collect(),
        Form::LetRecursor | Form::LetBoolean => {
            let ExprNode::LetE { value, body, .. } = head.node() else {
                return Vec::new();
            };
            let inner = spine(body).1;
            let mut parts = if form == Form::LetRecursor {
                vec![inner[0].clone(), inner[3].clone(), inner[2].clone()]
            } else {
                vec![value.clone(), inner[2].clone(), inner[1].clone()]
            };
            parts.extend(args);
            parts
        }
    }
}

/// The position of a conditional's decision among [`children`].
fn decision_child(form: Form) -> usize {
    match form {
        Form::Ite | Form::Dite => 3,
        Form::Recursor => 5,
        Form::Boolean => 4,
        Form::LetRecursor | Form::LetBoolean => 1,
    }
}

/// Every immediate part of `expr`: an application's head and arguments, a binder's type and
/// body, a `let`'s type, value and body.
fn children(expr: &Expr) -> Vec<Expr> {
    match expr.node() {
        ExprNode::App { .. } => {
            let (head, mut args) = spine(expr);
            args.insert(0, head);
            args
        }
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
    }
}

/// `expr` with its [`children`] replaced.
fn rebuild(expr: &Expr, mut parts: Vec<Expr>) -> Expr {
    match expr.node() {
        ExprNode::App { .. } => {
            let head = parts.remove(0);
            parts.into_iter().fold(head, Expr::app)
        }
        ExprNode::Lam {
            binder_name,
            binder_info,
            ..
        } => {
            let body = parts.pop().expect("lambda body");
            Expr::lam(binder_name.clone(), parts.remove(0), body, *binder_info)
        }
        ExprNode::ForallE {
            binder_name,
            binder_info,
            ..
        } => {
            let body = parts.pop().expect("forall body");
            Expr::forall_e(binder_name.clone(), parts.remove(0), body, *binder_info)
        }
        ExprNode::LetE {
            decl_name, non_dep, ..
        } => {
            let body = parts.pop().expect("let body");
            let value = parts.pop().expect("let value");
            Expr::let_e(decl_name.clone(), parts.remove(0), value, body, *non_dep)
        }
        ExprNode::MData { data, .. } => Expr::mdata(data.clone(), parts.remove(0)),
        ExprNode::Proj {
            struct_name, idx, ..
        } => Expr::proj(struct_name.clone(), *idx, parts.remove(0)),
        _ => expr.clone(),
    }
}

/// Whether `expr` is a `match` the pin's `split` splits (`isMatcherAppCore?`): an auxiliary
/// matcher's application, or what this engine compiles a source `match` to, a recursor or
/// `casesOn` application or a `let` naming a column, whose discriminant reads no variable bound
/// inside the goal. A matcher's discriminants are not located, so it always counts.
fn is_match(env: &fln_env::environment::Environment, expr: &Expr) -> bool {
    if let ExprNode::LetE {
        decl_name, value, ..
    } = expr.node()
        && is_match_column(decl_name)
    {
        return !value.has_loose_bvars();
    }
    let (head, args) = spine(expr);
    let ExprNode::Const { name: head, .. } = head.node() else {
        return false;
    };
    let last = match head.leaf_view() {
        LeafView::Str(last) => last.to_owned(),
        _ => return false,
    };
    if last
        .strip_prefix("match_")
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
    {
        return true;
    }
    let major = match env.find(head) {
        Some(ConstantInfo::Rec(rec)) => {
            u64::from(rec.num_params)
                + u64::from(rec.num_motives)
                + u64::from(rec.num_minors)
                + u64::from(rec.num_indices)
        }
        _ if last == "casesOn" => match env.find(&head.parent()) {
            Some(ConstantInfo::Induct(family)) => {
                u64::from(family.num_params) + 1 + u64::from(family.num_indices)
            }
            _ => return false,
        },
        _ => return false,
    };
    usize::try_from(major)
        .ok()
        .and_then(|major| args.get(major))
        .is_none_or(|major| !major.has_loose_bvars())
}

/// A conditional whose condition changed must have its dictionary, and the evidence its
/// branches bind, follow: `ite_congr` and `dite_congr` synthesize a new dictionary and cast the
/// branches, which this reduction does not. `original` and `parts` are its [`children`] before
/// and after the rewrite.
fn check_follows(
    form: Form,
    original: &[Expr],
    parts: &[Expr],
) -> Result<(), NatDefinitionElabError> {
    let (condition, dictionary, branches): (usize, usize, &[usize]) = match form {
        Form::Ite => (2, 3, &[]),
        Form::Dite => (2, 3, &[4, 5]),
        Form::Recursor => (1, 5, &[3, 4]),
        // The condition is the let's type, the dictionary its value.
        Form::LetRecursor => (0, 1, &[]),
        Form::LetBoolean | Form::Boolean => return Ok(()),
    };
    let moved =
        |index: usize| original[index].allocation_identity() != parts[index].allocation_identity();
    if !moved(condition) {
        return Ok(());
    }
    // The dictionary itself: under the `let` that keeps the condition, when elaborated so.
    let dictionary_moved = match (original[dictionary].node(), parts[dictionary].node()) {
        (ExprNode::LetE { body: before, .. }, ExprNode::LetE { body: after, .. })
            if form == Form::LetRecursor =>
        {
            before.allocation_identity() != after.allocation_identity()
        }
        _ => moved(dictionary),
    };
    let lambda = |index: &usize| matches!(parts[*index].node(), ExprNode::Lam { .. });
    // A compiled `if`'s recursor reads its dictionary through the enclosing `let`, checked there.
    let bound = matches!(parts[dictionary].node(), ExprNode::BVar { .. });
    if !(dictionary_moved || bound) || !branches.iter().all(lambda) {
        return Err(error(TacticError::SplitDependentCondition));
    }
    Ok(())
}

/// The binder this engine's match compiler names a column with: a number.
fn is_match_column(name: &Name) -> bool {
    matches!(name.leaf_view(), LeafView::Num(_)) && name.parent().is_anonymous()
}

impl Context {
    pub(in crate::source) fn split_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, term, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "split", "split keyword")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "split"])?;
        // What the case split and the reductions are built from.
        for required in [
            &["Decidable", "rec"][..],
            &["Bool", "rec"],
            &["absurd"],
            &["ne_true_of_eq_false"],
            &["Eq", "refl"],
        ] {
            if !self.txn.env.contains(&name(required)) {
                return Err(failure(SourceInferenceError::UnknownConstant(name(
                    required,
                ))));
            }
        }
        self.txn.lctx = goal.lctx.clone();
        let located = !expect_null_args(location, "split location")?.is_empty();
        match expect_null_args(term, "split term")? {
            [] => {}
            [term] => {
                // `throwTermUnsupported`: a lone identifier naming a hypothesis gets a hint.
                let local = match term {
                    Syntax::Ident { val, .. }
                        if !located
                            && matches!(val.leaf_view(), LeafView::Str(_))
                            && goal.lctx.find_by_user_name(val).is_some() =>
                    {
                        Some(val.clone())
                    }
                    _ => None,
                };
                return Err(error(TacticError::SplitTermUnsupported { local }));
            }
            _ => return Err(error(TacticError::MalformedScript)),
        }
        let Some(locations) = self.rewrite_locations(location)? else {
            return self.split_target(proof, goal);
        };
        if locations.all {
            return self.split_everywhere(proof, goal);
        }
        if (!locations.hypotheses.is_empty() && locations.target) || locations.hypotheses.len() > 1
        {
            return Err(error(TacticError::SplitMultipleLocations {
                goal: locations.target,
                hypotheses: locations.hypotheses,
            }));
        }
        let Some(hypothesis) = locations.hypotheses.first() else {
            return self.split_target(proof, goal);
        };
        let local = goal
            .lctx
            .find_by_user_name(hypothesis)
            .cloned()
            .ok_or_else(|| error(TacticError::SplitUnknownHypothesis(hypothesis.clone())))?;
        let subject = Subject::Hypothesis(local.clone());
        let Some(plan) = self.split_plan(&goal, &subject)? else {
            let hint = self.split_cases_hint(&local.type_)?;
            return Err(error(TacticError::SplitHypothesis {
                local: local.user_name,
                hint,
            }));
        };
        self.split_apply(proof, goal, &subject, plan)
    }

    fn split_target(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        let Some(plan) = self.split_plan(&goal, &Subject::Target)? else {
            let hint = self.split_cases_hint(&goal.target)?;
            return Err(error(TacticError::SplitGoal { hint }));
        };
        self.split_apply(proof, goal, &Subject::Target, plan)
    }

    /// `split at *`: the first nondependent propositional hypothesis that splits
    /// (`MVarId.getNondepPropHyps`, vendored src/Lean/Meta/Tactic/Util.lean), else the goal.
    fn split_everywhere(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        let mut candidates: Vec<LocalDecl> = Vec::new();
        for local in goal.lctx.decls() {
            self.tick()?;
            if self.is_matrix_hypothesis(local) || local.user_name.is_anonymous() {
                continue;
            }
            let mut reads = self.elimination_reads(&local.type_)?;
            if let Some(value) = &local.value {
                reads.extend(self.elimination_reads(value)?);
            }
            candidates.retain(|candidate| !reads.contains(&candidate.id));
            if local.value.is_none() && self.split_is_proposition(&local.type_)? {
                candidates.push(local.clone());
            }
        }
        let reads = self.elimination_reads(&goal.target)?;
        candidates.retain(|candidate| !reads.contains(&candidate.id));
        for local in &candidates {
            self.tick()?;
            let subject = Subject::Hypothesis(local.clone());
            if let Some(plan) = self.split_plan(&goal, &subject)? {
                return self.split_apply(proof, goal, &subject, plan);
            }
        }
        if let Some(plan) = self.split_plan(&goal, &Subject::Target)? {
            return self.split_apply(proof, goal, &Subject::Target, plan);
        }
        Err(error(TacticError::SplitWildcard(
            candidates
                .into_iter()
                .map(|local| local.user_name)
                .collect(),
        )))
    }

    /// `mkCasesHint`: a conjunction or a pair. (The pin also names a structure.)
    fn split_cases_hint(
        &mut self,
        type_: &Expr,
    ) -> Result<Option<&'static str>, NatDefinitionElabError> {
        let type_ = self.instantiate(type_)?;
        Ok(if is_head(&type_, &["And"]) {
            Some("conjunction")
        } else if is_head(&type_, &["Prod"]) {
            Some("pair")
        } else {
            None
        })
    }

    fn split_is_proposition(&mut self, type_: &Expr) -> Result<bool, NatDefinitionElabError> {
        let Some(sort) = self.known_type(type_)? else {
            return Ok(false);
        };
        let sort = self.whnf(&sort)?;
        Ok(matches!(sort.node(), ExprNode::Sort { level } if level.is_zero()))
    }

    fn split_sort_level(&mut self, type_: &Expr) -> Result<Level, NatDefinitionElabError> {
        let sort = self
            .known_type(type_)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        self.sort_level(&Typed {
            value: type_.clone(),
            type_: sort,
        })
    }

    /// The selected conditional and both cases, or `None` where the pin's `split` finds nothing,
    /// or its cases leave both unchanged.
    fn split_plan(
        &mut self,
        goal: &ProofGoal,
        subject: &Subject,
    ) -> Result<Option<Plan>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let subject_type = match subject {
            Subject::Target => self.instantiate(&goal.target)?,
            Subject::Hypothesis(local) => self.instantiate(&local.type_)?,
        };
        let selected = match self.split_find(&subject_type)? {
            None => return Ok(None),
            Some(Candidate::Match) => return Err(error(TacticError::SplitMatchUnsupported)),
            Some(Candidate::Conditional(selected)) => selected,
        };
        let condition = selected.condition;
        let dictionary = match selected.decision {
            Decision::Dictionary(dictionary) => dictionary,
            // `if b` on a `Bool` is the pin's `if b = true`, decided by the instance it finds.
            Decision::Boolean(_) => self.decision_dictionary(&condition)?,
        };
        if [&condition, &dictionary]
            .iter()
            .any(|e| e.has_loose_bvars() || e.has_expr_mvar() || e.has_level_mvar())
        {
            return Err(error(TacticError::SplitBoundDecision));
        }
        let hypothesis = self.fresh_inaccessible(&name(&["h"]))?;
        let mut cases = Vec::new();
        for proposition in [condition.clone(), negation(condition.clone())] {
            let mut context = goal.lctx.clone();
            context.add_param(
                FVarId(self.fresh_name()?),
                hypothesis.clone(),
                proposition,
                BinderInfo::Default,
            );
            let local = context.decls().last().expect("case hypothesis").clone();
            self.txn.lctx = context;
            let reduced = self.split_reductions(&subject_type, subject);
            self.txn.lctx = goal.lctx.clone();
            let (reduced, transports) = reduced?;
            cases.push(Case {
                local,
                reduced,
                transports,
            });
        }
        let (no, yes) = (
            cases.pop().expect("isFalse case"),
            cases.pop().expect("isTrue case"),
        );
        if yes.transports.is_empty() && no.transports.is_empty() {
            return Ok(None);
        }
        Ok(Some(Plan {
            condition,
            dictionary,
            yes,
            no,
        }))
    }

    /// `findSplit?`: the first candidate, by the pin's `FindSplitImpl.visit` order; for a
    /// conditional, a candidate in its condition first.
    fn split_find(&mut self, root: &Expr) -> Result<Option<Candidate>, NatDefinitionElabError> {
        let mut found = None;
        let mut current = root.clone();
        loop {
            self.tick()?;
            match self.split_find_in(&current)? {
                None => return Ok(found.map(Candidate::Conditional)),
                Some(Candidate::Match) => return Ok(Some(Candidate::Match)),
                Some(Candidate::Conditional(selected)) => {
                    current = selected.condition.clone();
                    found = Some(selected);
                }
            }
        }
    }

    fn split_find_in(&mut self, root: &Expr) -> Result<Option<Candidate>, NatDefinitionElabError> {
        let mut parameters = HashMap::new();
        let mut visited = HashSet::new();
        let mut pending = vec![root.clone()];
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !visited.insert(expr.allocation_identity()) {
                continue;
            }
            let (head, args) = spine(&expr);
            let found = conditional(&expr, true);
            if let Some(found) = &found {
                // `isCandidate?` reads an `ite`'s condition as `getArg! 1 5`: of an over-applied
                // one, the argument four from the end.
                let condition = match found.form {
                    Form::Ite | Form::Dite => &args[args.len() - 4],
                    _ => &found.condition,
                };
                if !condition.has_loose_bvars() {
                    return Ok(Some(Candidate::Conditional(found.clone())));
                }
            } else if is_match(&self.txn.env, &expr) {
                return Ok(Some(Candidate::Match));
            }
            // Candidates are not looked for in proofs.
            if !expr.has_loose_bvars() && self.is_proof(&expr)? {
                continue;
            }
            let mut next = Vec::new();
            if let Some(found) = found {
                next = conditional_parts(&expr, found.form);
            } else {
                match expr.node() {
                    ExprNode::Lam { body, .. } => next.push(body.clone()),
                    ExprNode::Proj { expr, .. } | ExprNode::MData { expr, .. } => {
                        next.push(expr.clone())
                    }
                    ExprNode::ForallE {
                        binder_type, body, ..
                    } => next.extend([binder_type.clone(), body.clone()]),
                    ExprNode::LetE { value, body, .. } => {
                        next.extend([value.clone(), body.clone()])
                    }
                    ExprNode::App { .. } => {
                        let infos = if head.has_loose_bvars() {
                            Vec::new()
                        } else {
                            self.split_parameters(&head, &mut parameters)?
                        };
                        for (index, arg) in args.iter().enumerate() {
                            if infos
                                .get(index)
                                .is_none_or(|info| info.explicit && !info.proof)
                            {
                                next.push(arg.clone());
                            }
                        }
                        next.push(head);
                    }
                    _ => {}
                }
            }
            pending.extend(next.into_iter().rev());
        }
        Ok(None)
    }

    /// The pin's `getFunInfo`: each parameter of `head`'s type, the type reduced to expose
    /// them. Cached per constant.
    fn split_parameters(
        &mut self,
        head: &Expr,
        cache: &mut HashMap<Name, Vec<Parameter>>,
    ) -> Result<Vec<Parameter>, NatDefinitionElabError> {
        let key = match head.node() {
            ExprNode::Const { name, .. } => Some(name.clone()),
            _ => None,
        };
        if let Some(cached) = key.as_ref().and_then(|key| cache.get(key)) {
            return Ok(cached.clone());
        }
        let saved = self.txn.lctx.clone();
        let result = self.split_parameters_in(head);
        self.txn.lctx = saved;
        let result = result?;
        if let Some(key) = key {
            cache.insert(key, result.clone());
        }
        Ok(result)
    }

    fn split_parameters_in(
        &mut self,
        head: &Expr,
    ) -> Result<Vec<Parameter>, NatDefinitionElabError> {
        let Some(mut type_) = self.known_type(head)? else {
            return Ok(Vec::new());
        };
        let mut parameters = Vec::new();
        let mut locals: Vec<(FVarId, Expr)> = Vec::new();
        loop {
            self.tick()?;
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = type_.node()
            else {
                break;
            };
            let (binder_name, binder_type, body, binder_info) = (
                binder_name.clone(),
                binder_type.clone(),
                body.clone(),
                *binder_info,
            );
            let id = FVarId(self.fresh_name()?);
            let proof = self.split_is_proposition(&binder_type)?;
            self.txn
                .lctx
                .add_param(id.clone(), binder_name, binder_type.clone(), binder_info);
            parameters.push(Parameter {
                explicit: binder_info == BinderInfo::Default,
                proof,
                dependent: false,
            });
            locals.push((id.clone(), binder_type));
            type_ = self.substitute(&body, &Expr::fvar(id))?;
        }
        for (index, (id, _)) in locals.iter().enumerate() {
            self.tick()?;
            let mut read = self.elimination_reads(&type_)?.contains(id);
            for (_, later) in &locals[index + 1..] {
                read = read || self.elimination_reads(later)?.contains(id);
            }
            parameters[index].dependent = read;
        }
        Ok(parameters)
    }

    /// The first conditional that `simp` reaches and a hypothesis decides, with the side it is
    /// decided to and the proof (`SplitIf.discharge?`).
    fn split_decided(
        &mut self,
        root: &Expr,
        discharged: &mut Vec<(Expr, Option<(bool, Expr)>)>,
    ) -> Result<Option<(Conditional, bool, Expr)>, NatDefinitionElabError> {
        let mut parameters = HashMap::new();
        let mut visited = HashSet::new();
        let mut pending = vec![root.clone()];
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !visited.insert(expr.allocation_identity()) {
                continue;
            }
            if let Some(found) = conditional(&expr, false) {
                if !found.condition.has_loose_bvars()
                    && !found.condition.has_expr_mvar()
                    && let Some((side, proof)) =
                        self.split_discharge(&found.condition, discharged)?
                {
                    let decision = match &found.decision {
                        Decision::Dictionary(e) | Decision::Boolean(e) => e,
                    };
                    if decision.has_loose_bvars() || decision.has_expr_mvar() {
                        return Err(error(TacticError::SplitBoundDecision));
                    }
                    return Ok(Some((found, side, proof)));
                }
                pending.extend(conditional_parts(&expr, found.form));
                continue;
            }
            match expr.node() {
                ExprNode::Lam { body, .. } => pending.push(body.clone()),
                ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    // An implication's premise (`implies_congr`), never a dependent domain.
                    if !body.has_loose_bvar(0) {
                        pending.push(binder_type.clone());
                    }
                    pending.push(body.clone());
                }
                ExprNode::LetE { value, body, .. } => {
                    pending.extend([value.clone(), body.clone()]);
                }
                ExprNode::Proj { expr, .. } | ExprNode::MData { expr, .. } => {
                    pending.push(expr.clone());
                }
                ExprNode::App { .. } => {
                    let (head, args) = spine(&expr);
                    let infos = if head.has_loose_bvars() {
                        Vec::new()
                    } else {
                        self.split_parameters(&head, &mut parameters)?
                    };
                    // The congruence `simp` builds: explicit arguments nothing depends on.
                    for (index, arg) in args.into_iter().enumerate() {
                        if infos
                            .get(index)
                            .is_none_or(|info| info.explicit && !info.proof && !info.dependent)
                        {
                            pending.push(arg);
                        }
                    }
                    if !matches!(
                        head.node(),
                        ExprNode::Const { .. } | ExprNode::FVar { .. } | ExprNode::MVar { .. }
                    ) {
                        pending.push(head);
                    }
                }
                _ => {}
            }
        }
        Ok(None)
    }

    /// `SplitIf.discharge?` (`useDecide := false`): a hypothesis, newest first, whose type is
    /// the condition (or, for `¬¬a`, `a`) at reducible transparency, else one for its negation.
    fn split_discharge(
        &mut self,
        condition: &Expr,
        discharged: &mut Vec<(Expr, Option<(bool, Expr)>)>,
    ) -> Result<Option<(bool, Expr)>, NatDefinitionElabError> {
        for (known, result) in discharged.iter() {
            if self.rewrite_same(known, condition)? {
                return Ok(result.clone());
            }
        }
        let result = if let Some(proof) = self.split_assumption(condition)? {
            Some((true, proof))
        } else {
            self.split_assumption(&negation(condition.clone()))?
                .map(|proof| (false, proof))
        };
        discharged.push((condition.clone(), result.clone()));
        Ok(result)
    }

    fn split_assumption(
        &mut self,
        proposition: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        // `Expr.notNot?`: `a` for `¬¬a`.
        let not = |e: &Expr| {
            let (head, args) = spine(e);
            match (head.node(), args.as_slice()) {
                (ExprNode::Const { name: head, .. }, [inner]) if head == &name(&["Not"]) => {
                    Some(inner.clone())
                }
                _ => None,
            }
        };
        let doubled = not(proposition)
            .and_then(|inner| not(&inner))
            .filter(|_| self.txn.env.contains(&name(&["not_not_intro"])));
        for local in self.txn.lctx.decls().to_vec().into_iter().rev() {
            self.tick()?;
            if self.is_matrix_hypothesis(&local) || local.user_name.is_anonymous() {
                continue;
            }
            let type_ = self.instantiate(&local.type_)?;
            if self.proof_types_match(proposition, &type_)? {
                return Ok(Some(Expr::fvar(local.id)));
            }
            if let Some(inner) = &doubled
                && self.proof_types_match(inner, &type_)?
            {
                return Ok(Some(apps(
                    constant("not_not_intro", vec![]),
                    [inner.clone(), Expr::fvar(local.id)],
                )));
            }
        }
        Ok(None)
    }

    /// `subject` (the goal, or a hypothesis's type) with every conditional the current context
    /// decides reduced, and the transports: for the goal each maps a reduced goal to the one
    /// before it, for a hypothesis each maps the hypothesis forward.
    fn split_reductions(
        &mut self,
        subject_type: &Expr,
        subject: &Subject,
    ) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let level = self.split_sort_level(subject_type)?;
        let mut current = subject_type.clone();
        let mut transports = Vec::new();
        let mut discharged = Vec::new();
        while let Some((site, side, proof)) = self.split_decided(&current, &mut discharged)? {
            if transports.len() >= MAX_REDUCTIONS {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            let marker_type = match &site.decision {
                Decision::Dictionary(_) => {
                    Expr::app(constant("Decidable", vec![]), site.condition.clone())
                }
                Decision::Boolean(_) => constant("Bool", vec![]),
            };
            let marker = self.equality_local(marker_type)?;
            let (reduced, motive) = self.split_rewrite(
                &current,
                &site,
                side,
                &proof,
                &Expr::fvar(marker.id.clone()),
            )?;
            if reduced.allocation_identity() == current.allocation_identity() {
                return Err(failure(SourceInferenceError::Scope));
            }
            let forward = matches!(subject, Subject::Hypothesis(_));
            transports.push(self.split_transport(
                &site, side, &proof, &marker, &reduced, &motive, &level, forward,
            )?);
            current = reduced;
        }
        Ok((current, transports))
    }

    /// `root` with every conditional of `site`'s decision that `simp` reaches reduced to its
    /// decided branch, and the same with that decision replaced by `marker` instead. Inside a
    /// conditional whose condition changes, its dictionary and the binders that read the
    /// condition change with it, as `ite_congr`/`dite_congr` change them; one whose dictionary
    /// does not mention the change cannot follow it, and is refused.
    fn split_rewrite(
        &mut self,
        root: &Expr,
        site: &Conditional,
        side: bool,
        proof: &Expr,
        marker: &Expr,
    ) -> Result<(Expr, Expr), NatDefinitionElabError> {
        let mut parameters = HashMap::new();
        let mut reaches = HashMap::<(usize, Reach), Vec<Option<Reach>>>::new();
        let mut done = HashMap::<(usize, Reach), (Expr, Expr)>::new();
        let mut work = vec![(root.clone(), Reach::Simp, false)];
        while let Some((expr, reach, exit)) = work.pop() {
            let key = (expr.allocation_identity(), reach);
            if done.contains_key(&key) {
                continue;
            }
            self.tick()?;
            let parts = children(&expr);
            if !exit {
                let plan = self.split_reaches(&expr, reach, &mut parameters)?;
                work.push((expr, reach, true));
                for (part, part_reach) in parts.into_iter().zip(&plan) {
                    if let Some(part_reach) = part_reach {
                        work.push((part, *part_reach, false));
                    }
                }
                reaches.insert(key, plan);
                continue;
            }
            let plan = reaches.remove(&key).expect("planned node");
            let mut reduced = Vec::with_capacity(parts.len());
            let mut abstracted = Vec::with_capacity(parts.len());
            let mut moved = false;
            for (part, part_reach) in parts.iter().zip(&plan) {
                let (r, a) = match part_reach {
                    Some(part_reach) => done
                        .get(&(part.allocation_identity(), *part_reach))
                        .expect("postorder part")
                        .clone(),
                    None => (part.clone(), part.clone()),
                };
                moved |= r.allocation_identity() != part.allocation_identity()
                    || a.allocation_identity() != part.allocation_identity();
                reduced.push(r);
                abstracted.push(a);
            }
            let found = conditional(&expr, false).or_else(|| {
                (reach == Reach::Whole)
                    .then(|| boolean_conditional(&expr))
                    .flatten()
            });
            if let Some(found) = &found {
                check_follows(found.form, &parts, &reduced)?;
                check_follows(found.form, &parts, &abstracted)?;
            }
            let value = match found {
                Some(found) if self.split_same_decision(&found, site)? => {
                    let branch = self.split_branch(&found, &reduced, side, proof)?;
                    abstracted[decision_child(found.form)] = marker.clone();
                    (branch, rebuild(&expr, abstracted))
                }
                _ if moved => (rebuild(&expr, reduced), rebuild(&expr, abstracted)),
                _ => (expr.clone(), expr.clone()),
            };
            done.insert(key, value);
        }
        Ok(done
            .remove(&(root.allocation_identity(), Reach::Simp))
            .expect("rewritten root"))
    }

    /// The [`children`] of `expr` the rewrite visits at `reach`, and at which reach each.
    fn split_reaches(
        &mut self,
        expr: &Expr,
        reach: Reach,
        parameters: &mut HashMap<Name, Vec<Parameter>>,
    ) -> Result<Vec<Option<Reach>>, NatDefinitionElabError> {
        let count = children(expr).len();
        let lambda = matches!(expr.node(), ExprNode::Lam { .. });
        Ok(match reach {
            Reach::Whole => vec![Some(Reach::Whole); count],
            Reach::Binder if lambda => vec![Some(Reach::Whole), None],
            Reach::Binder => vec![None; count],
            Reach::Branch if lambda => vec![Some(Reach::Whole), Some(Reach::Simp)],
            Reach::Simp | Reach::Branch => {
                if let Some(found) = conditional(expr, false) {
                    use Reach::{Binder, Branch, Simp, Whole};
                    let mut plan = match found.form {
                        Form::Ite => {
                            vec![None, None, Some(Simp), Some(Whole), Some(Simp), Some(Simp)]
                        }
                        Form::Dite => {
                            vec![
                                None,
                                None,
                                Some(Simp),
                                Some(Whole),
                                Some(Branch),
                                Some(Branch),
                            ]
                        }
                        Form::Recursor => vec![
                            None,
                            Some(Simp),
                            Some(Binder),
                            Some(Branch),
                            Some(Branch),
                            Some(Whole),
                        ],
                        Form::LetRecursor => vec![Some(Whole), Some(Whole), Some(Simp)],
                        Form::LetBoolean => vec![None, Some(Simp), Some(Simp)],
                        Form::Boolean => vec![None, None, Some(Simp), Some(Simp), None],
                    };
                    plan.resize(count, Some(Simp));
                    plan
                } else {
                    match expr.node() {
                        ExprNode::App { .. } => {
                            let (head, args) = spine(expr);
                            let infos = if head.has_loose_bvars() {
                                Vec::new()
                            } else {
                                self.split_parameters(&head, parameters)?
                            };
                            let mut plan = vec![
                                (!matches!(
                                    head.node(),
                                    ExprNode::Const { .. }
                                        | ExprNode::FVar { .. }
                                        | ExprNode::MVar { .. }
                                ))
                                .then_some(Reach::Simp),
                            ];
                            // The congruence `simp` builds: explicit arguments nothing depends on.
                            plan.extend((0..args.len()).map(|index| {
                                infos
                                    .get(index)
                                    .is_none_or(|info| {
                                        info.explicit && !info.proof && !info.dependent
                                    })
                                    .then_some(Reach::Simp)
                            }));
                            plan
                        }
                        ExprNode::Lam { .. } => vec![None, Some(Reach::Simp)],
                        // An implication's premise (`implies_congr`), never a dependent domain.
                        ExprNode::ForallE { body, .. } => vec![
                            (!body.has_loose_bvar(0)).then_some(Reach::Simp),
                            Some(Reach::Simp),
                        ],
                        ExprNode::LetE { .. } => vec![None, Some(Reach::Simp), Some(Reach::Simp)],
                        _ => vec![Some(Reach::Simp); count],
                    }
                }
            }
        })
    }

    fn split_same_decision(
        &mut self,
        found: &Conditional,
        site: &Conditional,
    ) -> Result<bool, NatDefinitionElabError> {
        match (&found.decision, &site.decision) {
            (Decision::Dictionary(found_dictionary), Decision::Dictionary(dictionary)) => Ok(self
                .rewrite_same(found_dictionary, dictionary)?
                && self.rewrite_same(&found.condition, &site.condition)?),
            (Decision::Boolean(found), Decision::Boolean(value)) => self.rewrite_same(found, value),
            _ => Ok(false),
        }
    }

    /// The decided branch of a conditional whose [`children`] are `parts`, given the proof
    /// of its condition (or of its negation): `if_pos`, `if_neg`, `dif_pos`, `dif_neg`.
    fn split_branch(
        &mut self,
        found: &Conditional,
        parts: &[Expr],
        side: bool,
        proof: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let scope = || failure(SourceInferenceError::Scope);
        let (branch, extra) = match found.form {
            Form::Ite => (parts[if side { 4 } else { 5 }].clone(), &parts[6..]),
            Form::Dite => (
                self.head_beta(Expr::app(
                    parts[if side { 4 } else { 5 }].clone(),
                    proof.clone(),
                ))?,
                &parts[6..],
            ),
            Form::Recursor => (
                self.head_beta(Expr::app(
                    parts[if side { 4 } else { 3 }].clone(),
                    proof.clone(),
                ))?,
                &parts[6..],
            ),
            Form::LetRecursor => {
                let inner = spine(&parts[2]).1;
                let branch = inner.get(if side { 3 } else { 2 }).ok_or_else(scope)?;
                let branch = lower(branch).ok_or_else(scope)?;
                (self.head_beta(Expr::app(branch, proof.clone()))?, &[][..])
            }
            Form::Boolean => (parts[if side { 3 } else { 2 }].clone(), &parts[5..]),
            Form::LetBoolean => {
                let inner = spine(&parts[2]).1;
                let branch = inner.get(if side { 2 } else { 1 }).ok_or_else(scope)?;
                (lower(branch).ok_or_else(scope)?, &[][..])
            }
        };
        Ok(extra.iter().cloned().fold(branch, Expr::app))
    }

    /// The map between `reduced` and `motive` (with `marker` replaced by the decision): from
    /// `reduced` to it for the goal, to `reduced` from it for a hypothesis. It eliminates the
    /// decision with that motive; the decided case is the identity, by iota reduction, and the
    /// other is refuted by the proof.
    #[allow(clippy::too_many_arguments)]
    fn split_transport(
        &mut self,
        site: &Conditional,
        side: bool,
        proof: &Expr,
        marker: &LocalDecl,
        reduced: &Expr,
        motive: &Expr,
        level: &Level,
        forward: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let limit = |_| failure(SourceInferenceError::ResourceLimit);
        let arrow_level = Level::imax(level.clone(), level.clone()).map_err(limit)?;
        let arrow = |motive: Expr| {
            if forward {
                Expr::forall_e(
                    Name::anonymous(),
                    motive,
                    reduced.clone(),
                    BinderInfo::Default,
                )
            } else {
                Expr::forall_e(
                    Name::anonymous(),
                    reduced.clone(),
                    motive,
                    BinderInfo::Default,
                )
            }
        };
        let abstracted = motive
            .abstract_fvar(&marker.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let at = |this: &mut Self, value: Expr| -> Result<Expr, NatDefinitionElabError> {
            Ok(arrow(this.substitute(&abstracted, &value)?))
        };
        let identity = Expr::lam(
            name(&["h"]),
            reduced.clone(),
            Expr::bvar(0).map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
        match &site.decision {
            Decision::Dictionary(dictionary) => {
                let condition = site.condition.clone();
                let motive = self.close_equality_binder(marker, arrow(motive.clone()), true)?;
                let refuted = |this: &mut Self,
                               domain: Expr,
                               constructor: &str|
                 -> Result<Expr, NatDefinitionElabError> {
                    let local = this.equality_local(domain)?;
                    let value = apps(
                        constant(constructor, vec![]),
                        [condition.clone(), Expr::fvar(local.id.clone())],
                    );
                    let target = at(this, value)?;
                    let (yes, no) = if side {
                        (proof.clone(), Expr::fvar(local.id.clone()))
                    } else {
                        (Expr::fvar(local.id.clone()), proof.clone())
                    };
                    let refutation = apps(
                        constant("absurd", vec![arrow_level.clone()]),
                        [condition.clone(), target, yes, no],
                    );
                    this.close_equality_binder(&local, refutation, true)
                };
                let decided = |domain: Expr| {
                    Expr::lam(name(&["h"]), domain, identity.clone(), BinderInfo::Default)
                };
                let (no, yes) = if side {
                    (
                        refuted(self, negation(condition.clone()), "Decidable.isFalse")?,
                        decided(condition.clone()),
                    )
                } else {
                    (
                        decided(negation(condition.clone())),
                        refuted(self, condition.clone(), "Decidable.isTrue")?,
                    )
                };
                Ok(apps(
                    constant("Decidable.rec", vec![arrow_level]),
                    [condition, motive, no, yes, dictionary.clone()],
                ))
            }
            Decision::Boolean(value) => {
                let premise = |marker: Expr| {
                    let equation = boolean_condition(marker);
                    if side { equation } else { negation(equation) }
                };
                let motive_level =
                    Level::imax(Level::zero(), arrow_level.clone()).map_err(limit)?;
                let motive = self.close_equality_binder(
                    marker,
                    Expr::forall_e(
                        Name::anonymous(),
                        premise(Expr::fvar(marker.id.clone())),
                        arrow(motive.clone()),
                        BinderInfo::Default,
                    ),
                    true,
                )?;
                let reflexive = |constructor: &str| {
                    apps(
                        constant("Eq.refl", vec![Level::one()]),
                        [constant("Bool", vec![]), constant(constructor, vec![])],
                    )
                };
                let decided = |constructor: &str| {
                    Expr::lam(
                        name(&["h"]),
                        premise(constant(constructor, vec![])),
                        identity.clone(),
                        BinderInfo::Default,
                    )
                };
                // The other constructor's premise is false: `false = true`, or `¬true = true`.
                let other = if side { "Bool.false" } else { "Bool.true" };
                let local = self.equality_local(premise(constant(other, vec![])))?;
                let target = at(self, constant(other, vec![]))?;
                let refutation = if side {
                    let distinct = apps(
                        constant("ne_true_of_eq_false", vec![]),
                        [constant("Bool.false", vec![]), reflexive("Bool.false")],
                    );
                    apps(
                        constant("absurd", vec![arrow_level.clone()]),
                        [
                            boolean_condition(constant("Bool.false", vec![])),
                            target,
                            Expr::fvar(local.id.clone()),
                            distinct,
                        ],
                    )
                } else {
                    apps(
                        constant("absurd", vec![arrow_level.clone()]),
                        [
                            boolean_condition(constant("Bool.true", vec![])),
                            target,
                            reflexive("Bool.true"),
                            Expr::fvar(local.id.clone()),
                        ],
                    )
                };
                let refuted = self.close_equality_binder(&local, refutation, true)?;
                let (no, yes) = if side {
                    (refuted, decided("Bool.true"))
                } else {
                    (decided("Bool.false"), refuted)
                };
                Ok(apps(
                    constant("Bool.rec", vec![motive_level]),
                    [motive, no, yes, value.clone(), proof.clone()],
                ))
            }
        }
    }

    /// Close `goal` by cases on the selected decision, each case a goal with its hypothesis
    /// and the reduced goal (or, at a hypothesis, the reduced hypothesis after it).
    fn split_apply(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        subject: &Subject,
        plan: Plan,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let target = self.instantiate(&goal.target)?;
        let level = self.split_sort_level(&target)?;
        // A hypothesis that nothing else reads leaves the context; otherwise it stays, shadowed
        // by its reduced copy, as the pin's `replaceLocalDecl` fails to clear it.
        let mut base = goal.lctx.clone();
        if let Subject::Hypothesis(local) = subject {
            let mut read = self.elimination_reads(&target)?.contains(&local.id);
            for case in [&plan.yes, &plan.no] {
                read = read || self.elimination_reads(&case.reduced)?.contains(&local.id);
            }
            for other in goal.lctx.decls() {
                if other.id == local.id {
                    continue;
                }
                read = read || self.elimination_reads(&other.type_)?.contains(&local.id);
                if let Some(value) = &other.value {
                    read = read || self.elimination_reads(value)?.contains(&local.id);
                }
            }
            if !read {
                base = LocalContext::new();
                for other in goal.lctx.decls() {
                    if other.id != local.id {
                        eliminate::add_local(&mut base, other);
                    }
                }
            }
        }
        let parent = self
            .goal_tags
            .get(&goal.id)
            .cloned()
            .unwrap_or_else(Name::anonymous);
        let mut minors = Vec::new();
        let mut children = Vec::new();
        for (case, tag) in [(plan.no, "isFalse"), (plan.yes, "isTrue")] {
            self.tick()?;
            let mut introduced = vec![case.local.clone()];
            let mut context = base.clone();
            eliminate::add_local(&mut context, &case.local);
            let case_target = match subject {
                Subject::Target => case.reduced.clone(),
                Subject::Hypothesis(local) => {
                    context.add_param(
                        FVarId(self.fresh_name()?),
                        local.user_name.clone(),
                        case.reduced.clone(),
                        local.binder_info,
                    );
                    introduced.push(context.decls().last().expect("reduced hypothesis").clone());
                    target.clone()
                }
            };
            let mut function_type = case_target.clone();
            for local in introduced.iter().rev() {
                function_type = self.close_equality_binder(local, function_type, false)?;
            }
            self.txn.lctx = base.clone();
            let (hole, mut child) = self.proof_goal(function_type)?;
            child.target = case_target;
            child.lctx = context;
            child.introduced = introduced;
            let applied = Expr::app(hole, Expr::fvar(case.local.id.clone()));
            let value = match subject {
                Subject::Target => case
                    .transports
                    .iter()
                    .rev()
                    .cloned()
                    .fold(applied, |inner, transport| Expr::app(transport, inner)),
                Subject::Hypothesis(local) => Expr::app(
                    applied,
                    case.transports
                        .iter()
                        .cloned()
                        .fold(Expr::fvar(local.id.clone()), |inner, transport| {
                            Expr::app(transport, inner)
                        }),
                ),
            };
            minors.push(self.close_equality_binder(&case.local, value, true)?);
            // `MVarId.cases` tags each case with its constructor (`isTrue`, `isFalse`).
            self.goal_tags.insert(
                child.id.clone(),
                super::super::trace::append_tag(&parent, &name(&[tag])),
            );
            children.push(child);
        }
        self.txn.lctx = goal.lctx.clone();
        let motive = Expr::lam(
            Name::anonymous(),
            Expr::app(constant("Decidable", vec![]), plan.condition.clone()),
            target,
            BinderInfo::Default,
        );
        let mut minors = minors.into_iter();
        let (no, yes) = (
            minors.next().expect("isFalse minor"),
            minors.next().expect("isTrue minor"),
        );
        let value = apps(
            constant("Decidable.rec", vec![level]),
            [plan.condition, motive, no, yes, plan.dictionary],
        );
        let mut children = children.into_iter();
        let (no, yes) = (
            children.next().expect("isFalse goal"),
            children.next().expect("isTrue goal"),
        );
        proof.work.push(Work::Close(goal, value));
        proof.work.push(Work::Goal(no));
        proof.work.push(Work::Goal(yes));
        Ok(())
    }
}
