//! Native recursive case patterns, lowered to the ordinary checked case compiler.
//! Pattern trees and the resulting goal forest are traversed on heap worklists.
//! No branch is solved by the pattern itself; each live minor remains a goal.
use super::*;
use fln_env::constants::ConstantInfo;
use std::collections::HashMap;
mod derived;

#[derive(Clone)]
enum Pattern<'a> {
    One(Option<Name>),
    Tuple(Vec<usize>),
    Alts(Vec<usize>),
    Typed(usize, &'a Syntax),
}

enum Parse<'a> {
    Visit(&'a Syntax),
    Tuple(usize),
    Alts(usize),
    Typed(&'a Syntax),
}

#[derive(Clone)]
struct Subject {
    name: Name,
    pattern: usize,
    rename: bool,
}

enum Step<'a> {
    Match(ProofGoal, Vec<Subject>),
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
                    } else if node == &kind(&["rcasesPat", "one"]) {
                        let [Syntax::Ident { val, .. }] = args.as_slice() else {
                            return Err(malformed());
                        };
                        if val == &Name::from_components(["rfl"]) {
                            return Err(error(TacticError::UnsupportedTactic(kind(&["rcases"]))));
                        }
                        Pattern::One(Some(val.clone()))
                    } else {
                        // Clearing, equality substitution and explicit patterns are not
                        // no-op names. Until implemented they remain hard refusals, even
                        // inside a tactic alternative, rather than hiding a valid branch.
                        return Err(error(TacticError::UnsupportedTactic(node.clone())));
                    }
                }
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
        let [target] = targets.as_slice() else {
            return Err(error(TacticError::UnsupportedTactic(kind(&["rcases"]))));
        };
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
        self.txn.lctx = goal.lctx.clone();
        let expected = match &arena[pattern] {
            Pattern::Typed(_, type_) => Some(self.type_term(type_)?),
            _ => None,
        };
        let term = self.term(expression, expected)?;
        self.resolve_instances_with_defaults()?;
        self.flush(false)?;
        let term = Typed {
            value: self.instantiate(&term.value)?,
            type_: self.instantiate(&term.type_)?,
        };
        self.require_resolved(&[term.value.clone(), term.type_.clone()])?;
        let local = if equation.is_none()
            && let ExprNode::FVar { id } = term.value.node()
        {
            goal.lctx
                .find(id)
                .cloned()
                .ok_or_else(|| error(TacticError::EliminationLocal))?
        } else {
            let name = match pattern_name(&arena, pattern) {
                Some(name) => name,
                None => self.fresh_name()?,
            };
            let (child, id) = self.generalized_proof_goal(proof, goal, name, equation, term)?;
            goal = child;
            goal.lctx
                .find(&id)
                .cloned()
                .ok_or_else(|| error(TacticError::EliminationLocal))?
        };
        self.run_rcases_patterns(
            proof,
            goal,
            arena,
            vec![Subject {
                name: local.user_name,
                pattern,
                rename: false,
            }],
        )
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

    fn run_rcases_patterns<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        mut arena: Vec<Pattern<'_>>,
        subjects: Vec<Subject>,
    ) -> Result<(), NatDefinitionElabError> {
        let mut pending = vec![Step::Match(goal, subjects)];
        let mut output = Vec::new();
        while let Some(step) = pending.pop() {
            self.tick()?;
            let (mut goal, mut subjects) = match step {
                Step::Emit(work) => {
                    output.push(work);
                    continue;
                }
                Step::Match(goal, subjects) => (goal, subjects),
            };
            self.txn.lctx = goal.lctx.clone();
            let Some(subject) = subjects.pop() else {
                output.push(Work::Goal(goal));
                continue;
            };
            let local = goal
                .lctx
                .find_by_user_name(&subject.name)
                .cloned()
                .ok_or_else(|| error(TacticError::EliminationLocal))?;
            match arena[subject.pattern].clone() {
                Pattern::One(name) => {
                    if subject.rename
                        && let Some(name) = name
                    {
                        self.update_rcases_local(&mut goal, &local.id, Some(name), None);
                    }
                    pending.push(Step::Match(goal, subjects));
                }
                Pattern::Typed(inner, syntax) => {
                    let type_ = self.type_term(syntax)?;
                    if !self.proof_types_match(&local.type_, &type_)? {
                        return Err(error(TacticError::ApplyMismatch));
                    }
                    self.update_rcases_local(&mut goal, &local.id, None, Some(type_));
                    subjects.push(Subject {
                        pattern: inner,
                        ..subject
                    });
                    pending.push(Step::Match(goal, subjects));
                }
                Pattern::Tuple(_) | Pattern::Alts(_) => {
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
                    let mut field_plans = Vec::new();
                    for (index, constructor) in family.ctors.iter().enumerate() {
                        self.tick()?;
                        let selected = alternatives.get(index).copied().unwrap_or(0);
                        let patterns =
                            if index + 1 == family.ctors.len() && alternatives.len() > index + 1 {
                                let next = arena.len();
                                arena.push(Pattern::Alts(alternatives[index..].to_vec()));
                                vec![next]
                            } else {
                                match &arena[selected] {
                                    Pattern::Tuple(items) => items.clone(),
                                    _ => vec![selected],
                                }
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
                        for field in 0..ctor.num_fields {
                            self.tick()?;
                            let ExprNode::ForallE {
                                body, binder_info, ..
                            } = telescope.node()
                            else {
                                return Err(malformed());
                            };
                            let pattern = if *binder_info != BinderInfo::Default {
                                0
                            } else if field + 1 == ctor.num_fields && patterns.len() > consumed + 1
                            {
                                let next = arena.len();
                                arena.push(Pattern::Tuple(patterns[consumed..].to_vec()));
                                next
                            } else {
                                let next = patterns.get(consumed).copied().unwrap_or(0);
                                consumed += 1;
                                next
                            };
                            telescope = body.clone();
                            let name = self.fresh_name()?;
                            names.push(name.clone());
                            field_plans.push(Subject {
                                name,
                                pattern,
                                rename: true,
                            });
                        }
                        field_names.insert(constructor.clone(), names);
                    }
                    let start = proof.work.len();
                    self.eliminate_proof_goal_with_indices(
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
                                let mut next = subjects.clone();
                                for field in field_plans.iter().rev() {
                                    self.tick()?;
                                    if child.lctx.find_by_user_name(&field.name).is_some() {
                                        next.push(field.clone());
                                    }
                                }
                                Step::Match(child, next)
                            }
                            work @ Work::Close(..) => Step::Emit(work),
                            _ => return Err(malformed()),
                        });
                    }
                }
            }
        }
        proof.work.extend(output.into_iter().rev());
        Ok(())
    }
}
