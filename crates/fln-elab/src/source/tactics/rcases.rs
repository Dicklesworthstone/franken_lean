//! Native recursive case patterns, lowered to the ordinary checked case compiler.
//! Pattern trees and the resulting goal forest are traversed on heap worklists.
//! Constructors and equality transports remain ordinary checked proof terms.
use super::*;
use fln_env::constants::ConstantInfo;
use std::collections::{HashMap, HashSet};
mod derived;
mod generalize;

#[derive(Clone)]
enum Pattern<'a> {
    One(Option<Name>),
    Substitute,
    Clear,
    Explicit(usize),
    Tuple(Vec<usize>),
    Alts(Vec<usize>),
    Typed(usize, &'a Syntax),
}

enum Parse<'a> {
    Visit(&'a Syntax),
    Explicit,
    Tuple(usize),
    Alts(usize),
    Typed(&'a Syntax),
}

#[derive(Clone)]
struct TrackedLocal {
    value: Expr,
}

#[derive(Clone)]
struct Subject {
    local: TrackedLocal,
    pattern: usize,
    rename: bool,
    /// A top-level target annotation is elaborated before any pattern binds a
    /// name. Nested annotations still elaborate in their constructor context.
    expected: Option<Expr>,
}

enum Step<'a> {
    Match(ProofGoal, Vec<Subject>, Vec<TrackedLocal>),
    Emit(Work<'a>),
}

fn kind(parts: &[&str]) -> Name {
    let mut path = vec!["Tactic"];
    path.extend_from_slice(parts);
    parser_kind(&path)
}

fn malformed() -> NatDefinitionElabError {
    error(TacticError::MalformedScript)
}

fn separated<'a>(
    syntax: &'a Syntax,
    separator: &str,
) -> Result<Vec<&'a Syntax>, NatDefinitionElabError> {
    let items = expect_null_args(syntax, "recursive case patterns")?;
    if !items.is_empty() && items.len() % 2 == 0 {
        return Err(malformed());
    }
    let mut result = Vec::new();
    for (index, item) in items.iter().enumerate() {
        if index % 2 == 0 {
            result.push(item);
        } else if !matches!(item, Syntax::Atom { val, .. } if val == separator) {
            return Err(malformed());
        }
    }
    Ok(result)
}

fn pattern_name(arena: &[Pattern<'_>], mut index: usize) -> Option<Name> {
    loop {
        match &arena[index] {
            Pattern::One(name) => return name.clone(),
            Pattern::Typed(inner, _) => index = *inner,
            Pattern::Alts(items) if items.len() == 1 => index = items[0],
            _ => return None,
        }
    }
}

fn pattern_tuple(arena: &[Pattern<'_>], mut index: usize) -> (bool, Vec<usize>) {
    let mut explicit = false;
    loop {
        match &arena[index] {
            Pattern::Explicit(inner) => {
                explicit = true;
                index = *inner;
            }
            Pattern::Tuple(items) => return (explicit, items.clone()),
            _ => return (explicit, vec![index]),
        }
    }
}

impl Context {
    fn parse_rcases_pattern<'a>(
        &mut self,
        syntax: &'a Syntax,
        arena: &mut Vec<Pattern<'a>>,
    ) -> Result<usize, NatDefinitionElabError> {
        let mut pending = vec![Parse::Visit(syntax)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            self.tick()?;
            let pattern = match task {
                Parse::Visit(syntax) => {
                    let Syntax::Node {
                        kind: node, args, ..
                    } = syntax
                    else {
                        return Err(malformed());
                    };
                    if node == &kind(&["rcasesPatLo"]) {
                        let [inner, annotation] = args.as_slice() else {
                            return Err(malformed());
                        };
                        match expect_null_args(annotation, "rcases annotation")? {
                            [] => {}
                            [colon, type_] => {
                                expect_atom(colon, ":", "rcases annotation")?;
                                pending.push(Parse::Typed(type_));
                            }
                            _ => return Err(malformed()),
                        }
                        pending.push(Parse::Visit(inner));
                        continue;
                    } else if node == &kind(&["rcasesPat", "paren"]) {
                        let [open, inner, close] = args.as_slice() else {
                            return Err(malformed());
                        };
                        expect_atom(open, "(", "rcases parenthesis")?;
                        expect_atom(close, ")", "rcases parenthesis")?;
                        pending.push(Parse::Visit(inner));
                        continue;
                    } else if node == &kind(&["rcasesPatMed"]) {
                        let [listed] = args.as_slice() else {
                            return Err(malformed());
                        };
                        let patterns = separated(listed, "|")?;
                        if patterns.is_empty() {
                            return Err(malformed());
                        }
                        pending.push(Parse::Alts(patterns.len()));
                        pending.extend(patterns.into_iter().rev().map(Parse::Visit));
                        continue;
                    } else if node == &kind(&["rcasesPat", "tuple"]) {
                        let [open, listed, close] = args.as_slice() else {
                            return Err(malformed());
                        };
                        expect_atom(open, "⟨", "rcases tuple")?;
                        expect_atom(close, "⟩", "rcases tuple")?;
                        let patterns = separated(listed, ",")?;
                        pending.push(Parse::Tuple(patterns.len()));
                        pending.extend(patterns.into_iter().rev().map(Parse::Visit));
                        continue;
                    } else if node == &kind(&["rcasesPat", "ignore"]) {
                        let [hole] = args.as_slice() else {
                            return Err(malformed());
                        };
                        expect_atom(hole, "_", "rcases wildcard")?;
                        Pattern::One(None)
                    } else if node == &kind(&["rcasesPat", "clear"]) {
                        let [dash] = args.as_slice() else {
                            return Err(malformed());
                        };
                        expect_atom(dash, "-", "rcases clear")?;
                        Pattern::Clear
                    } else if node == &kind(&["rcasesPat", "explicit"]) {
                        let [at, inner] = args.as_slice() else {
                            return Err(malformed());
                        };
                        expect_atom(at, "@", "explicit rcases pattern")?;
                        pending.push(Parse::Explicit);
                        pending.push(Parse::Visit(inner));
                        continue;
                    } else if node == &kind(&["rcasesPat", "one"]) {
                        let [Syntax::Ident { val, .. }] = args.as_slice() else {
                            return Err(malformed());
                        };
                        if val == &Name::from_components(["rfl"]) {
                            Pattern::Substitute
                        } else {
                            Pattern::One(Some(val.clone()))
                        }
                    } else {
                        return Err(error(TacticError::UnsupportedTactic(node.clone())));
                    }
                }
                Parse::Explicit => Pattern::Explicit(values.pop().ok_or_else(malformed)?),
                Parse::Tuple(count) => {
                    let start = values.len().checked_sub(count).ok_or_else(malformed)?;
                    Pattern::Tuple(values.split_off(start))
                }
                Parse::Alts(count) => {
                    let start = values.len().checked_sub(count).ok_or_else(malformed)?;
                    let items = values.split_off(start);
                    if let [only] = items.as_slice() {
                        values.push(*only);
                        continue;
                    }
                    Pattern::Alts(items)
                }
                Parse::Typed(type_) => Pattern::Typed(values.pop().ok_or_else(malformed)?, type_),
            };
            let index = arena.len();
            arena.push(pattern);
            values.push(index);
        }
        match values.as_slice() {
            [only] => Ok(*only),
            _ => Err(malformed()),
        }
    }

    pub(super) fn rcases_proof_goal<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        mut goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, targets, with] = args else {
            return Err(malformed());
        };
        expect_atom(keyword, "rcases", "rcases keyword")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "rcases"])?;
        let targets = separated(targets, ",")?;
        if targets.is_empty() {
            return Err(malformed());
        }
        let mut arena = vec![Pattern::One(None)];
        let pattern = match expect_null_args(with, "rcases pattern")? {
            [] => {
                let index = arena.len();
                arena.push(Pattern::Tuple(Vec::new()));
                index
            }
            [keyword, pattern] => {
                expect_atom(keyword, "with", "rcases with")?;
                self.parse_rcases_pattern(pattern, &mut arena)?
            }
            _ => return Err(malformed()),
        };
        // The pin distributes the tuple over targets exactly as over fields:
        // missing patterns are wildcards; excess patterns belong to the last
        // target. The synthetic target tuple has no implicit binders.
        let patterns = if targets.len() == 1 {
            vec![pattern]
        } else {
            let (_, supplied) = pattern_tuple(&arena, pattern);
            let mut patterns = Vec::new();
            for index in 0..targets.len() {
                self.tick()?;
                let pattern = if index + 1 == targets.len() && supplied.len() > index + 1 {
                    let next = arena.len();
                    arena.push(Pattern::Tuple(supplied[index..].to_vec()));
                    next
                } else {
                    supplied.get(index).copied().unwrap_or(0)
                };
                patterns.push(pattern);
            }
            patterns
        };
        let mut subjects = Vec::new();
        let mut generalized = Vec::new();
        let mut positions = Vec::new();
        // Elaborate every target in the original context, including targets
        // following an impossible one. Earlier pattern names are not in scope.
        for (target, pattern) in targets.into_iter().zip(patterns) {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            let [equation, expression] =
                expect_node(target, &kind(&["elimTarget"]), 2, "rcases target")?
            else {
                return Err(malformed());
            };
            let equation = match expect_null_args(equation, "rcases equation")? {
                [] => None,
                [binder, colon] => {
                    expect_atom(colon, ":", "rcases equation")?;
                    let [Syntax::Ident { val, .. }] = expect_node(
                        binder,
                        &Name::from_components(["Lean", "binderIdent"]),
                        1,
                        "rcases equation name",
                    )?
                    else {
                        return Err(malformed());
                    };
                    Some(val.clone())
                }
                _ => return Err(malformed()),
            };
            let expected = match &arena[pattern] {
                Pattern::Typed(_, type_) => Some(self.type_term(type_)?),
                _ => None,
            };
            let term = self.term(expression, expected.clone())?;
            self.resolve_instances_with_defaults()?;
            self.flush(false)?;
            let term = Typed {
                value: self.instantiate(&term.value)?,
                type_: self.instantiate(&term.type_)?,
            };
            self.require_resolved(&[term.value.clone(), term.type_.clone()])?;
            let value = term.value.clone();
            if equation.is_some() || !matches!(value.node(), ExprNode::FVar { .. }) {
                let name = match pattern_name(&arena, pattern) {
                    Some(name) => name,
                    None => self.fresh_name()?,
                };
                positions.push(subjects.len());
                generalized.push((name, equation, term));
            }
            subjects.push(Subject {
                local: TrackedLocal { value },
                pattern,
                rename: false,
                expected,
            });
        }
        if !generalized.is_empty() {
            let (child, ids) = self.generalize_rcases_targets(proof, goal, generalized)?;
            goal = child;
            for (position, id) in positions.into_iter().zip(ids) {
                self.tick()?;
                subjects[position].local.value = Expr::fvar(id);
            }
        }
        subjects.reverse();
        self.run_rcases_patterns(proof, goal, arena, subjects, Vec::new(), true)
            .map(|_| ())
    }

    fn update_rcases_local(
        &mut self,
        goal: &mut ProofGoal,
        id: &FVarId,
        name: Option<Name>,
        type_: Option<Expr>,
    ) {
        let mut context = LocalContext::new();
        for original in goal.lctx.decls() {
            let mut local = original.clone();
            if &local.id == id {
                if let Some(name) = &name {
                    local.user_name = name.clone();
                }
                if let Some(type_) = &type_ {
                    local.type_ = type_.clone();
                }
            }
            eliminate::add_local(&mut context, &local);
        }
        for local in &mut goal.introduced {
            if &local.id == id {
                if let Some(name) = &name {
                    local.user_name = name.clone();
                }
                if let Some(type_) = &type_ {
                    local.type_ = type_.clone();
                }
            }
        }
        goal.lctx = context.clone();
        self.txn.lctx = context;
    }

    fn remap_rcases_local(
        &mut self,
        tracked: &mut TrackedLocal,
        substitutions: &[(FVarId, Expr)],
    ) -> Result<(), NatDefinitionElabError> {
        tracked.value = self.specialize_locals(&tracked.value, substitutions)?;
        Ok(())
    }

    fn remap_rcases_subject(
        &mut self,
        subject: &mut Subject,
        substitutions: &[eliminate::CaseSubstitution],
    ) -> Result<(), NatDefinitionElabError> {
        for step in substitutions {
            self.tick()?;
            if let ExprNode::FVar { id } = subject.local.value.node() {
                for (eliminated, _) in step.replacements.iter().take(step.eliminated) {
                    self.tick()?;
                    if id == eliminated {
                        // A replacement local retains its own name. Recreated
                        // dependent fields still receive their pending pattern.
                        subject.rename = false;
                        break;
                    }
                }
            }
            self.remap_rcases_local(&mut subject.local, &step.replacements)?;
        }
        Ok(())
    }

    /// Annotation conversion may determine a literal's carrier and then need
    /// its pending OfNat instance in the same comparison. Keep ordinary tactic
    /// transparency and failure handling, but give synthesis its existing
    /// source owner instead of prematurely defaulting the annotation to Nat.
    fn rcases_annotation_matches(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        self.flush(false)?;
        let budget = self.ambient_budget(UnificationTransparency::Abbreviations);
        match self.unify_pending(&[(actual.clone(), expected.clone())], budget)? {
            Ok(report) => {
                assert!(report.awakened.is_empty(), "private source queue");
                Ok(true)
            }
            Err(UnificationError::Deferred(_)) => Ok(false),
            Err(UnificationError::AssignmentCheck { outcome, .. })
                if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })) =>
            {
                Ok(false)
            }
            Err(error) => Err(failure(SourceInferenceError::Unification(Box::new(error)))),
        }
    }

    /// Match the pin's `tryClearMany'`: defer deletion until all patterns and
    /// introductions finish, include forward dependencies through types and let
    /// values, then keep any local still required by the target or a survivor.
    fn finish_rcases_clears(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        clears: &[TrackedLocal],
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let mut removed = HashSet::new();
        for clear in clears {
            self.tick()?;
            if let ExprNode::FVar { id } = clear.value.node()
                && goal.lctx.find(id).is_some()
            {
                removed.insert(id.clone());
            }
        }
        if removed.is_empty() {
            return Ok(goal);
        }
        let mut candidates = Vec::new();
        for local in goal.lctx.decls() {
            self.tick()?;
            let mut reads = self.elimination_reads(&local.type_)?;
            if let Some(value) = &local.value {
                reads.extend(self.elimination_reads(value)?);
            }
            if removed.contains(&local.id) || !reads.is_disjoint(&removed) {
                removed.insert(local.id.clone());
                candidates.push(local.id.clone());
            }
        }
        self.try_clear_proof_locals(proof, goal, &candidates)
    }

    fn run_rcases_patterns<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        mut arena: Vec<Pattern<'_>>,
        subjects: Vec<Subject>,
        clears: Vec<TrackedLocal>,
        finish: bool,
    ) -> Result<HashMap<MVarId, Vec<TrackedLocal>>, NatDefinitionElabError> {
        let mut pending = vec![Step::Match(goal, subjects, clears)];
        let mut output = Vec::new();
        let mut deferred = HashMap::new();
        while let Some(step) = pending.pop() {
            self.tick()?;
            let (mut goal, mut subjects, mut clears) = match step {
                Step::Emit(work) => {
                    output.push(work);
                    continue;
                }
                Step::Match(goal, subjects, clears) => (goal, subjects, clears),
            };
            self.txn.lctx = goal.lctx.clone();
            let Some(subject) = subjects.pop() else {
                let start = proof.work.len();
                if finish {
                    goal = self.finish_rcases_clears(proof, goal, &clears)?;
                } else {
                    deferred.insert(goal.id.clone(), clears);
                }
                output.push(Work::Goal(goal));
                output.extend(proof.work.split_off(start).into_iter().rev());
                continue;
            };
            let local = match subject.local.value.node() {
                ExprNode::FVar { id } => goal.lctx.find(id).cloned(),
                _ => None,
            };
            match arena[subject.pattern].clone() {
                Pattern::One(name) => {
                    if subject.rename
                        && let Some(name) = name
                        && let Some(local) = local
                    {
                        self.update_rcases_local(&mut goal, &local.id, Some(name), None);
                    }
                    pending.push(Step::Match(goal, subjects, clears));
                }
                Pattern::Clear => {
                    clears.push(subject.local);
                    pending.push(Step::Match(goal, subjects, clears));
                }
                Pattern::Substitute => {
                    let local = local.ok_or_else(|| error(TacticError::SubstitutionLocal))?;
                    let start = proof.work.len();
                    let substitutions = self.substitute_rcases_equality(proof, goal, &local.id)?;
                    let Some(Work::Goal(child)) = proof.work.pop() else {
                        return Err(malformed());
                    };
                    self.txn.lctx = child.lctx.clone();
                    let steps = [eliminate::CaseSubstitution {
                        eliminated: 1,
                        replacements: substitutions,
                    }];
                    for subject in &mut subjects {
                        self.remap_rcases_subject(subject, &steps)?;
                    }
                    for clear in &mut clears {
                        self.remap_rcases_local(clear, &steps[0].replacements)?;
                    }
                    pending.extend(proof.work.split_off(start).into_iter().map(Step::Emit));
                    pending.push(Step::Match(child, subjects, clears));
                }
                Pattern::Typed(inner, syntax) => {
                    let type_ = match &subject.expected {
                        Some(type_) => type_.clone(),
                        None => self.type_term(syntax)?,
                    };
                    let actual = match &local {
                        Some(local) => local.type_.clone(),
                        None => self
                            .known_type(&subject.local.value)?
                            .ok_or_else(|| error(TacticError::EliminationLocal))?,
                    };
                    if !self.rcases_annotation_matches(&actual, &type_)? {
                        return Err(error(TacticError::ApplyMismatch));
                    }
                    if let Some(local) = local {
                        self.update_rcases_local(&mut goal, &local.id, None, Some(type_));
                    }
                    subjects.push(Subject {
                        pattern: inner,
                        expected: None,
                        ..subject
                    });
                    pending.push(Step::Match(goal, subjects, clears));
                }
                Pattern::Tuple(_) | Pattern::Alts(_) | Pattern::Explicit(_) => {
                    let local = local.ok_or_else(|| error(TacticError::EliminationLocal))?;
                    let type_ = self.whnf(&local.type_)?;
                    let mut head = &type_;
                    while let ExprNode::App { f, .. } = head.node() {
                        self.tick()?;
                        head = f;
                    }
                    let ExprNode::Const { name, .. } = head.node() else {
                        return Err(error(TacticError::UnsupportedEliminator));
                    };
                    let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned()
                    else {
                        return Err(error(TacticError::UnsupportedEliminator));
                    };
                    let alternatives = match &arena[subject.pattern] {
                        Pattern::Alts(items) => items.clone(),
                        _ => vec![subject.pattern],
                    };
                    let mut field_names = HashMap::new();
                    let mut field_plans = HashMap::new();
                    for (index, constructor) in family.ctors.iter().enumerate() {
                        self.tick()?;
                        let selected = alternatives.get(index).copied().unwrap_or(0);
                        let (explicit, patterns) =
                            if index + 1 == family.ctors.len() && alternatives.len() > index + 1 {
                                let next = arena.len();
                                arena.push(Pattern::Alts(alternatives[index..].to_vec()));
                                (false, vec![next])
                            } else {
                                pattern_tuple(&arena, selected)
                            };
                        let Some(ConstantInfo::Ctor(ctor)) =
                            self.txn.env.find(constructor).cloned()
                        else {
                            return Err(error(TacticError::UnsupportedEliminator));
                        };
                        let mut telescope = ctor.base.type_.clone();
                        for _ in 0..ctor.num_params {
                            self.tick()?;
                            let ExprNode::ForallE { body, .. } = telescope.node() else {
                                return Err(malformed());
                            };
                            telescope = body.clone();
                        }
                        let mut consumed = 0;
                        let mut names = Vec::new();
                        let mut plans = Vec::new();
                        for field in 0..ctor.num_fields {
                            self.tick()?;
                            let ExprNode::ForallE {
                                body, binder_info, ..
                            } = telescope.node()
                            else {
                                return Err(malformed());
                            };
                            let pattern = if !explicit && *binder_info != BinderInfo::Default {
                                0
                            } else if field + 1 == ctor.num_fields && patterns.len() > consumed + 1
                            {
                                let next = arena.len();
                                arena.push(Pattern::Tuple(patterns[consumed..].to_vec()));
                                if explicit {
                                    let wrapper = arena.len();
                                    arena.push(Pattern::Explicit(next));
                                    wrapper
                                } else {
                                    next
                                }
                            } else {
                                let next = patterns.get(consumed).copied().unwrap_or(0);
                                consumed += 1;
                                next
                            };
                            telescope = body.clone();
                            let name = self.fresh_name()?;
                            names.push(name);
                            plans.push(pattern);
                        }
                        field_names.insert(constructor.clone(), names);
                        field_plans.insert(constructor.clone(), plans);
                    }
                    let start = proof.work.len();
                    let mut branches = self.eliminate_proof_goal_with_substitutions(
                        proof,
                        goal,
                        &eliminate::EliminationSyntax::RCases(field_names),
                        false,
                        Some(&local.id),
                        None,
                    )?;
                    for work in proof.work.split_off(start) {
                        pending.push(match work {
                            Work::Goal(child) => {
                                let branch = branches.remove(&child.id).ok_or_else(malformed)?;
                                let mut next = subjects.clone();
                                for subject in &mut next {
                                    self.remap_rcases_subject(subject, &branch.substitutions)?;
                                }
                                let mut next_clears = clears.clone();
                                for clear in &mut next_clears {
                                    for step in &branch.substitutions {
                                        self.remap_rcases_local(clear, &step.replacements)?;
                                    }
                                }
                                let plans =
                                    field_plans.get(&branch.constructor).ok_or_else(malformed)?;
                                if plans.len() != branch.fields.len() {
                                    return Err(malformed());
                                }
                                for (value, pattern) in branch.fields.into_iter().zip(plans).rev() {
                                    self.tick()?;
                                    let mut subject = Subject {
                                        local: TrackedLocal { value },
                                        pattern: *pattern,
                                        rename: true,
                                        expected: None,
                                    };
                                    self.remap_rcases_subject(&mut subject, &branch.substitutions)?;
                                    next.push(subject);
                                }
                                Step::Match(child, next, next_clears)
                            }
                            work @ Work::Close(..) => Step::Emit(work),
                            _ => return Err(malformed()),
                        });
                    }
                }
            }
        }
        proof.work.extend(output.into_iter().rev());
        Ok(deferred)
    }
}
