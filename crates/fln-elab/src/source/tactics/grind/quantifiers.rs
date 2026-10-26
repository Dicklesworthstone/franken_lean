//! Bounded E-matching for quantified propositions.
//!
//! Patterns only select arguments. A selected instance is the original proof
//! applied to those arguments, with every domain checked again before the fact
//! enters saturation. Equality classes guide matching, never type conversion.
use super::*;

const MAX_PARAMETERS: usize = 16;
const MAX_PATTERNS: usize = 32;
const MAX_THEOREMS: usize = 64;
const MAX_INSTANCES: usize = 256;
const MAX_MATCHES: usize = 100_000;
const MAX_SUBSTITUTIONS: usize = 512;
const MAX_MATCH_DEPTH: usize = 128;
// The pinned Init.Grind.Config default. Each round sees only the terms already
// internalized by the ground engine; instances become terms in the next round.
const MAX_ROUNDS: usize = 5;

#[derive(Clone, PartialEq, Eq, Hash)]
struct Substitution {
    terms: Vec<Option<Expr>>,
    levels: Vec<Option<Level>>,
}

#[derive(Clone)]
struct Parameter {
    id: FVarId,
}

#[derive(Clone)]
struct Theorem {
    evidence: Typed,
    level_params: Vec<Name>,
    parameters: Vec<Parameter>,
    patterns: Vec<Vec<Expr>>,
}

#[derive(Clone, Default)]
pub(super) struct Quantifiers {
    theorems: Vec<Theorem>,
    instances: HashSet<(usize, Vec<Expr>, Vec<Level>)>,
    matches: usize,
    rounds: usize,
}

fn resource() -> Error {
    failure(SourceInferenceError::ResourceLimit)
}

fn parameter_at(parameters: &[Parameter], expression: &Expr) -> Option<usize> {
    let ExprNode::FVar { id } = expression.node() else {
        return None;
    };
    parameters.iter().position(|parameter| parameter.id == *id)
}

/// Applications are the only pattern constructors in this fragment. Binding
/// forms and projections need the pin's pattern preprocessing and stay opaque.
fn variables(
    context: &mut Context,
    parameters: &[Parameter],
    expression: &Expr,
) -> Result<Option<Vec<bool>>, Error> {
    let mut found = vec![false; parameters.len()];
    let mut pending = vec![expression];
    let mut seen = HashSet::new();
    while let Some(term) = pending.pop() {
        context.tick()?;
        if !seen.insert(term.allocation_identity()) {
            continue;
        }
        if let Some(index) = parameter_at(parameters, term) {
            found[index] = true;
            continue;
        }
        match term.node() {
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::MData { expr, .. } => pending.push(expr),
            ExprNode::Const { .. }
            | ExprNode::FVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
            _ => return Ok(None),
        }
    }
    Ok(Some(found))
}

fn pattern_head(
    context: &mut Context,
    parameters: &[Parameter],
    expression: &Expr,
) -> Result<bool, Error> {
    let mut head = expression;
    while let ExprNode::App { f, .. } | ExprNode::MData { expr: f, .. } = head.node() {
        context.tick()?;
        head = f;
    }
    Ok(match head.node() {
        ExprNode::Const { name: head, .. } => {
            // Init.Grind.Tactics marks logical connectives as priority zero.
            // Interpreted arithmetic/conditionals are not triggers here either.
            ![
                "Eq",
                "HEq",
                "Iff",
                "And",
                "Or",
                "Not",
                "Ne",
                "ite",
                "dite",
                "HAdd.hAdd",
                "HSub.hSub",
                "HMul.hMul",
                "HDiv.hDiv",
                "HMod.hMod",
                "LT.lt",
                "LE.le",
            ]
            .iter()
            .any(|text| *head == name(text))
        }
        ExprNode::FVar { .. } => parameter_at(parameters, head).is_none(),
        _ => false,
    })
}

fn matching_heads(
    context: &mut Context,
    graph: &Equalities,
    pattern: &Expr,
    ground: &Expr,
) -> Result<bool, Error> {
    let head = |context: &mut Context, expression: &Expr| -> Result<(Expr, usize), Error> {
        let mut term = expression;
        let mut arity = 0;
        loop {
            context.tick()?;
            match term.node() {
                ExprNode::App { f, .. } => {
                    arity += 1;
                    term = f;
                }
                ExprNode::MData { expr, .. } => term = expr,
                _ => return Ok((term.clone(), arity)),
            }
        }
    };
    let (left, a) = head(context, pattern)?;
    let (right, b) = head(context, ground)?;
    if a != b {
        return Ok(false);
    }
    match (left.node(), right.node()) {
        (ExprNode::Const { name: a, .. }, ExprNode::Const { name: b, .. }) => Ok(a == b),
        (ExprNode::FVar { .. }, ExprNode::FVar { .. }) => graph.equivalent(context, &left, &right),
        _ => Ok(false),
    }
}

/// Candidate order follows the pin's conclusion/premise traversal. Keep child
/// candidates too: local forall facts additionally use all singleton patterns
/// (Lean.Meta.Grind.ForallProp.addLocalEMatchTheorems).
fn candidates(
    context: &mut Context,
    parameters: &[Parameter],
    expression: &Expr,
) -> Result<Vec<(Expr, Vec<bool>)>, Error> {
    let mut result = Vec::new();
    let mut pending = vec![expression.clone()];
    let mut seen = HashSet::new();
    while let Some(term) = pending.pop() {
        context.tick()?;
        let term = normalize(context, &term)?;
        if !seen.insert(term.clone()) {
            continue;
        }
        match term.node() {
            ExprNode::App { .. } => {
                if pattern_head(context, parameters, &term)?
                    && let Some(found) = variables(context, parameters, &term)?
                    && found.iter().any(|found| *found)
                {
                    if result.len() >= MAX_PATTERNS {
                        return Err(resource());
                    }
                    result.push((term.clone(), found));
                }
                // Visit complete arguments, not artificial partial applications.
                let mut head = &term;
                while let ExprNode::App { f, a } = head.node() {
                    context.tick()?;
                    pending.push(a.clone());
                    head = f;
                }
            }
            ExprNode::ForallE {
                binder_type, body, ..
            } if !body.has_loose_bvars() && is_prop(context, binder_type)? => {
                pending.push(body.clone());
                pending.push(binder_type.clone());
            }
            _ => {}
        }
    }
    Ok(result)
}

fn collect_group(
    context: &mut Context,
    parameters: &[Parameter],
    places: &[Expr],
) -> Result<Option<Vec<Expr>>, Error> {
    let mut covered = vec![false; parameters.len()];
    let mut group = Vec::new();
    for place in places {
        for (term, found) in candidates(context, parameters, place)? {
            context.tick()?;
            if !found
                .iter()
                .zip(&covered)
                .any(|(found, covered)| *found && !covered)
            {
                continue;
            }
            for (covered, found) in covered.iter_mut().zip(found) {
                *covered |= found;
            }
            group.push(term);
            if covered.iter().all(|covered| *covered) {
                return Ok(Some(group));
            }
        }
    }
    Ok(None)
}

impl Theorem {
    fn prepare(
        context: &mut Context,
        evidence: &Typed,
        level_params: &[Name],
        local: bool,
    ) -> Result<Option<Self>, Error> {
        let saved = context.txn.lctx.clone();
        let result = (|| {
            let mut type_ = normalize(context, &evidence.type_)?;
            let mut parameters = Vec::new();
            // Stop at a proof binder. After data instantiation the ordinary
            // implication engine can discharge it, including an ensuing forall.
            // This avoids guessing a dependent proof argument during matching.
            while let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = type_.node()
            {
                if is_prop(context, binder_type)? {
                    break;
                }
                if parameters.len() >= MAX_PARAMETERS {
                    return Err(resource());
                }
                let local = context.equality_local(binder_type.clone())?;
                context.txn.lctx.add_param(
                    local.id.clone(),
                    local.user_name,
                    binder_type.clone(),
                    *binder_info,
                );
                parameters.push(Parameter {
                    id: local.id.clone(),
                });
                let opened = context.substitute(body, &Expr::fvar(local.id))?;
                type_ = normalize(context, &opened)?;
            }
            if parameters.is_empty() {
                return Ok(None);
            }
            let mut conclusion = type_.clone();
            let mut premises = Vec::new();
            while let ExprNode::ForallE {
                binder_type, body, ..
            } = conclusion.node()
            {
                if body.has_loose_bvars() || !is_prop(context, binder_type)? {
                    break;
                }
                premises.push(binder_type.clone());
                conclusion = normalize(context, body)?;
            }
            let mut patterns = Vec::new();
            let mut backwards = vec![conclusion.clone()];
            backwards.extend(premises.iter().cloned());
            if local {
                for place in premises.iter().chain(std::iter::once(&conclusion)) {
                    for (pattern, covered) in candidates(context, &parameters, place)? {
                        if covered.iter().all(|covered| *covered) {
                            let group = vec![pattern];
                            if !patterns.contains(&group) {
                                patterns.push(group);
                            }
                        }
                    }
                }
                let mut forwards = premises.clone();
                forwards.push(conclusion.clone());
                if let Some(group) = collect_group(context, &parameters, &forwards)?
                    && !patterns.contains(&group)
                {
                    patterns.push(group);
                }
                backwards = vec![conclusion];
                backwards.extend(premises.into_iter().rev());
            }
            if let Some(group) = collect_group(context, &parameters, &backwards)?
                && !patterns.contains(&group)
            {
                patterns.push(group);
            }
            if patterns.is_empty() {
                return Ok(None);
            }
            if patterns.len() > MAX_PATTERNS {
                return Err(resource());
            }
            Ok(Some(Self {
                evidence: evidence.clone(),
                level_params: level_params.to_vec(),
                parameters,
                patterns,
            }))
        })();
        // A cutoff while opening the telescope must not leave its pattern
        // variables visible to later goals, instance search or source lookup.
        context.txn.lctx = saved;
        result
    }

    fn instantiate(
        &self,
        context: &mut Context,
        arguments: &[Expr],
        levels: &[Level],
    ) -> Result<Option<Typed>, Error> {
        let mut type_ =
            context.instantiate_params(&self.evidence.type_, &self.level_params, levels)?;
        let mut value =
            context.instantiate_params(&self.evidence.value, &self.level_params, levels)?;
        for argument in arguments {
            context.tick()?;
            type_ = normalize(context, &type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = type_.node()
            else {
                return Ok(None);
            };
            let Some(actual) = context.known_type(argument)? else {
                return Ok(None);
            };
            if !convert(context, &actual, binder_type)? {
                return Ok(None);
            }
            type_ = context.substitute(body, argument)?;
            value = Expr::app(value, argument.clone());
        }
        Ok(Some(Typed {
            value,
            type_: normalize(context, &type_)?,
        }))
    }
}

impl Quantifiers {
    pub fn register(
        &mut self,
        context: &mut Context,
        evidence: &Typed,
        level_params: &[Name],
        local: bool,
    ) -> Result<bool, Error> {
        let Some(theorem) = Theorem::prepare(context, evidence, level_params, local)? else {
            return Ok(false);
        };
        if self.theorems.len() >= MAX_THEOREMS {
            return Err(resource());
        }
        self.theorems.push(theorem);
        Ok(true)
    }

    fn tick(&mut self, context: &mut Context) -> Result<(), Error> {
        context.tick()?;
        self.matches = self.matches.checked_add(1).ok_or_else(resource)?;
        if self.matches > MAX_MATCHES {
            return Err(resource());
        }
        Ok(())
    }

    fn match_level(
        &mut self,
        context: &mut Context,
        parameters: &[Name],
        pattern: &Level,
        ground: &Level,
        substitution: &mut Substitution,
    ) -> Result<bool, Error> {
        use fln_core::level::LevelView;
        let mut pending = vec![(pattern.clone(), ground.clone())];
        while let Some((pattern, ground)) = pending.pop() {
            self.tick(context)?;
            let pattern = pattern.normalize_fixpoint();
            let ground = ground.normalize_fixpoint();
            if let LevelView::Param(name) = pattern.view()
                && let Some(index) = parameters.iter().position(|parameter| parameter == name)
            {
                if let Some(previous) = &substitution.levels[index] {
                    if !previous.is_equiv(&ground) {
                        return Ok(false);
                    }
                } else {
                    substitution.levels[index] = Some(ground);
                }
                continue;
            }
            if pattern == ground {
                continue;
            }
            match (pattern.view(), ground.view()) {
                (LevelView::Succ(a), LevelView::Succ(b)) => pending.push((a.clone(), b.clone())),
                (LevelView::Max(a, b), LevelView::Max(c, d))
                | (LevelView::IMax(a, b), LevelView::IMax(c, d)) => {
                    pending.push((a.clone(), c.clone()));
                    pending.push((b.clone(), d.clone()));
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn match_term(
        &mut self,
        context: &mut Context,
        graph: &Equalities,
        theorem: &Theorem,
        terms: (&Expr, &Expr),
        substitution: Substitution,
        depth: usize,
    ) -> Result<Vec<Substitution>, Error> {
        let (mut pattern, ground) = terms;
        self.tick(context)?;
        if depth >= MAX_MATCH_DEPTH {
            return Err(resource());
        }
        while let ExprNode::MData { expr, .. } = pattern.node() {
            self.tick(context)?;
            pattern = expr;
        }
        let ground = normalize(context, ground)?;
        let ground = &ground;
        if let Some(index) = parameter_at(&theorem.parameters, pattern) {
            if let Some(previous) = &substitution.terms[index] {
                return Ok(if graph.equivalent(context, previous, ground)? {
                    vec![substitution]
                } else {
                    Vec::new()
                });
            }
            let mut substitution = substitution;
            substitution.terms[index] = Some(ground.clone());
            return Ok(vec![substitution]);
        }
        let Some(found) = variables(context, &theorem.parameters, pattern)? else {
            return Ok(Vec::new());
        };
        if !found.iter().any(|found| *found) && theorem.level_params.is_empty() {
            return Ok(if graph.equivalent(context, pattern, ground)? {
                vec![substitution]
            } else {
                Vec::new()
            });
        }
        match (pattern.node(), ground.node()) {
            (
                ExprNode::Const {
                    name: left,
                    levels: a,
                },
                ExprNode::Const {
                    name: right,
                    levels: b,
                },
            ) if left == right && a.len() == b.len() => {
                let mut substitution = substitution;
                for (a, b) in a.iter().zip(b) {
                    if !self.match_level(context, &theorem.level_params, a, b, &mut substitution)? {
                        return Ok(Vec::new());
                    }
                }
                return Ok(vec![substitution]);
            }
            (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => {
                let mut substitution = substitution;
                return Ok(
                    if self.match_level(context, &theorem.level_params, a, b, &mut substitution)? {
                        vec![substitution]
                    } else {
                        Vec::new()
                    },
                );
            }
            (ExprNode::FVar { .. } | ExprNode::Lit { .. }, _) => {
                return Ok(if graph.equivalent(context, pattern, ground)? {
                    vec![substitution]
                } else {
                    Vec::new()
                });
            }
            _ => {}
        }
        let ExprNode::App {
            f: pattern_f,
            a: pattern_a,
        } = pattern.node()
        else {
            return Ok(Vec::new());
        };
        let mut answers = Vec::new();
        let mut seen = HashSet::new();
        for equivalent in graph.class_terms(context, ground)? {
            self.tick(context)?;
            let ExprNode::App { f, a } = equivalent.node() else {
                continue;
            };
            for partial in self.match_term(
                context,
                graph,
                theorem,
                (pattern_f, f),
                substitution.clone(),
                depth + 1,
            )? {
                for answer in
                    self.match_term(context, graph, theorem, (pattern_a, a), partial, depth + 1)?
                {
                    self.tick(context)?;
                    if seen.insert(answer.clone()) {
                        if answers.len() >= MAX_SUBSTITUTIONS {
                            return Err(resource());
                        }
                        answers.push(answer);
                    }
                }
            }
        }
        Ok(answers)
    }

    pub fn instantiate(
        &mut self,
        context: &mut Context,
        graph: &Equalities,
    ) -> Result<Vec<Typed>, Error> {
        let mut instances = Vec::new();
        // Snapshot before matching: no theorem in this round can see terms
        // manufactured by an earlier theorem in the same round.
        let terms: Vec<_> = graph
            .nodes
            .iter()
            .filter(|node| node.application.is_some())
            .map(|node| node.term.clone())
            .collect();
        for (index, theorem) in self.theorems.clone().into_iter().enumerate() {
            for patterns in &theorem.patterns {
                let mut substitutions = vec![Substitution {
                    terms: vec![None; theorem.parameters.len()],
                    levels: vec![None; theorem.level_params.len()],
                }];
                for pattern in patterns {
                    let mut next = Vec::new();
                    let mut seen = HashSet::new();
                    for substitution in substitutions {
                        for term in &terms {
                            self.tick(context)?;
                            if !matching_heads(context, graph, pattern, term)? {
                                continue;
                            }
                            for answer in self.match_term(
                                context,
                                graph,
                                &theorem,
                                (pattern, term),
                                substitution.clone(),
                                0,
                            )? {
                                if seen.insert(answer.clone()) {
                                    if next.len() >= MAX_SUBSTITUTIONS {
                                        return Err(resource());
                                    }
                                    next.push(answer);
                                }
                            }
                        }
                    }
                    substitutions = next;
                    if substitutions.is_empty() {
                        break;
                    }
                }
                for substitution in substitutions {
                    self.tick(context)?;
                    let Some(arguments) =
                        substitution.terms.into_iter().collect::<Option<Vec<_>>>()
                    else {
                        continue;
                    };
                    let Some(levels) = substitution.levels.into_iter().collect::<Option<Vec<_>>>()
                    else {
                        continue;
                    };
                    let key = (index, arguments.clone(), levels.clone());
                    if self.instances.contains(&key) {
                        continue;
                    }
                    let Some(instance) = theorem.instantiate(context, &arguments, &levels)? else {
                        continue;
                    };
                    if self.rounds >= MAX_ROUNDS || self.instances.len() >= MAX_INSTANCES {
                        return Err(resource());
                    }
                    self.instances.insert(key);
                    instances.push(instance);
                }
            }
        }
        if !instances.is_empty() {
            self.rounds += 1;
        }
        Ok(instances)
    }
}
