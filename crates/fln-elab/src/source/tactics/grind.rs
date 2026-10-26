//! Native equality, propositional saturation and bounded E-matching for grind.
//!
//! Every merge, propagation and case split retains an ordinary proof term.
//! There is no arithmetic oracle or new axiom. Quantified facts instantiate
//! their original proofs; arithmetic plugins and custom configurations remain
//! outside this fragment.
//! A failure of this fragment is a nonrecoverable capability refusal: it must
//! never make "try grind; ..." accept a script the pin would already have closed.
use super::*;
use std::collections::{HashMap, HashSet, VecDeque};
mod equalities;
mod quantifiers;
use equalities::Equalities;
use quantifiers::Quantifiers;

type Error = NatDefinitionElabError;
const MAX_FACTS: usize = 256;
const MAX_SPLITS: usize = 9;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn constant(text: &str) -> Expr {
    Expr::const_(name(text), Vec::new())
}
fn apply<const N: usize>(head: Expr, args: [Expr; N]) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn unsupported() -> Error {
    error(TacticError::UnsupportedTactic(parser_kind(&[
        "Tactic", "grind",
    ])))
}
fn normalize(context: &mut Context, expression: &Expr) -> Result<Expr, Error> {
    let mut expression = context.instantiate(expression)?;
    if expression.has_expr_mvar() || expression.has_level_mvar() || expression.has_loose_bvars() {
        return Err(unsupported());
    }
    loop {
        expression = context.whnf_with_transparency(
            &expression,
            UnificationTransparency::Abbreviations,
            true,
        )?;
        let mut head = &expression;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            context.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        let ExprNode::Const {
            name: head_name,
            levels,
        } = head.node()
        else {
            return Ok(expression);
        };
        if arguments.is_empty() || ![name("Not"), name("Ne")].contains(head_name) {
            return Ok(expression);
        }
        // Negation is an interpreted connective even though the pin's `Not`
        // declaration is semireducible. Unfold its actual admitted body only;
        // arbitrary user functions keep the abbreviation-only policy above.
        let Some(fln_env::constants::ConstantInfo::Defn(definition)) =
            context.txn.env.find(head_name).cloned()
        else {
            return Ok(expression);
        };
        if definition.safety != fln_env::constants::DefinitionSafety::Safe {
            return Ok(expression);
        }
        context.tick()?;
        let mut unfolded =
            context.instantiate_params(&definition.value, &definition.base.level_params, levels)?;
        for argument in arguments.into_iter().rev() {
            context.tick()?;
            unfolded = Expr::app(unfolded, argument);
        }
        if unfolded == expression {
            return Ok(expression);
        }
        expression = unfolded;
    }
}
fn convert(context: &mut Context, left: &Expr, right: &Expr) -> Result<bool, Error> {
    let mut budget = UnificationBudget::new(context.kernel);
    budget.transparency = UnificationTransparency::Abbreviations;
    budget.max_assignments = 0;
    budget.zeta_delta = true;
    context.proof_types_match_with_budget(left, right, budget)
}
fn is_prop(context: &mut Context, expression: &Expr) -> Result<bool, Error> {
    let Some(type_) = context.known_type(expression)? else {
        return Ok(false);
    };
    let type_ = normalize(context, &type_)?;
    Ok(matches!(type_.node(), ExprNode::Sort { level } if level.normalize_fixpoint().is_zero()))
}
fn binary(expression: &Expr, operator: &str) -> Option<(Expr, Expr)> {
    let ExprNode::App { f, a: right } = expression.node() else {
        return None;
    };
    let ExprNode::App { f: head, a: left } = f.node() else {
        return None;
    };
    matches!(head.node(), ExprNode::Const { name: n, .. } if *n == name(operator))
        .then(|| (left.clone(), right.clone()))
}
fn arrow(left: Expr, right: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), left, right, BinderInfo::Default)
}
fn lambda(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}
fn bound() -> Expr {
    Expr::bvar(0).expect("grind proof binder")
}
fn false_elim(target: Expr, proof: Expr) -> Expr {
    apply(
        Expr::const_(name("False.elim"), vec![Level::zero()]),
        [target, proof],
    )
}
fn restore(context: &mut Context, before: Context) {
    let spent = context.txn.budget.heartbeats_consumed;
    let aux_names = context.aux_names.take();
    *context = before;
    context.txn.budget.heartbeats_consumed = spent;
    context.aux_names = aux_names;
}

fn constructor_shape(context: &mut Context, value: &Expr) -> Result<Option<(Name, usize)>, Error> {
    let mut head = normalize(context, value)?;
    while let ExprNode::App { f, .. } = head.node() {
        context.tick()?;
        head = f.clone();
    }
    Ok(match head.node() {
        ExprNode::Const { name, .. } => match context.txn.env.find(name) {
            Some(fln_env::constants::ConstantInfo::Ctor(value)) => {
                Some((name.clone(), value.num_fields as usize))
            }
            _ => None,
        },
        ExprNode::Lit {
            literal: Literal::Nat(_),
        } => Some((name("Nat"), 0)),
        _ => None,
    })
}

#[derive(Clone)]
struct Rule {
    premise: Expr,
    conclusion: Expr,
    proof: Expr,
}

#[derive(Clone, Default)]
struct State {
    graph: Equalities,
    facts: Vec<Typed>,
    indices: HashMap<Expr, usize>,
    pending: VecDeque<Typed>,
    queued: HashSet<Expr>,
    rules: Vec<Rule>,
    quantifiers: Quantifiers,
}

impl State {
    fn enqueue(&mut self, context: &mut Context, mut fact: Typed) -> Result<(), Error> {
        fact.type_ = normalize(context, &fact.type_)?;
        if self.indices.contains_key(&fact.type_) || !self.queued.insert(fact.type_.clone()) {
            return Ok(());
        }
        if self.facts.len() + self.pending.len() >= MAX_FACTS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        self.pending.push_back(fact);
        Ok(())
    }

    fn observe(&mut self, context: &mut Context, proposition: &Expr) -> Result<(), Error> {
        let mut pending = vec![proposition.clone()];
        let mut seen = HashSet::new();
        while let Some(proposition) = pending.pop() {
            context.tick()?;
            let proposition = normalize(context, &proposition)?;
            if !seen.insert(proposition.clone()) {
                continue;
            }
            self.graph.intern(context, &proposition)?;
            for operator in ["And", "Or", "Iff"] {
                if let Some((left, right)) = binary(&proposition, operator) {
                    pending.push(left.clone());
                    pending.push(right.clone());
                    if operator == "Iff" {
                        pending.push(arrow(left.clone(), right.clone()));
                        pending.push(arrow(right, left));
                    }
                }
            }
            if let ExprNode::ForallE {
                binder_type, body, ..
            } = proposition.node()
                && !body.has_loose_bvars()
                && is_prop(context, binder_type)?
            {
                pending.push(binder_type.clone());
                pending.push(body.clone());
            }
        }
        Ok(())
    }

    fn truth_equality(&mut self, context: &mut Context, fact: &Typed) -> Result<(), Error> {
        let p = fact.type_.clone();
        let true_ = constant("True");
        let iff = apply(
            constant("Iff.intro"),
            [
                p.clone(),
                true_.clone(),
                lambda(p.clone(), constant("True.intro")),
                lambda(true_.clone(), fact.value.clone()),
            ],
        );
        self.graph.add(
            context,
            &Typed {
                value: apply(constant("propext"), [p.clone(), true_.clone(), iff]),
                type_: equality::equation(Level::one(), Expr::sort(Level::zero()), p, true_),
            },
        )
    }

    fn expand(&mut self, context: &mut Context, fact: Typed) -> Result<(), Error> {
        self.quantifiers.register(context, &fact, &[], true)?;
        self.observe(context, &fact.type_)?;
        self.graph.add(context, &fact)?;
        self.truth_equality(context, &fact)?;
        if let Some((left, right)) = binary(&fact.type_, "And") {
            for (projection, type_) in [("And.left", left.clone()), ("And.right", right.clone())] {
                self.enqueue(
                    context,
                    Typed {
                        value: apply(
                            constant(projection),
                            [left.clone(), right.clone(), fact.value.clone()],
                        ),
                        type_,
                    },
                )?;
            }
        }
        if let Some((left, right)) = binary(&fact.type_, "Iff") {
            self.graph.add(
                context,
                &Typed {
                    value: apply(
                        constant("propext"),
                        [left.clone(), right.clone(), fact.value.clone()],
                    ),
                    type_: equality::equation(
                        Level::one(),
                        Expr::sort(Level::zero()),
                        left.clone(),
                        right.clone(),
                    ),
                },
            )?;
            self.rules.push(Rule {
                premise: left.clone(),
                conclusion: right.clone(),
                proof: apply(
                    constant("Iff.mp"),
                    [left.clone(), right.clone(), fact.value.clone()],
                ),
            });
            self.rules.push(Rule {
                premise: right.clone(),
                conclusion: left.clone(),
                proof: apply(constant("Iff.mpr"), [left, right, fact.value.clone()]),
            });
        }
        if let ExprNode::ForallE {
            binder_type, body, ..
        } = fact.type_.node()
            && !body.has_loose_bvars()
            && is_prop(context, binder_type)?
        {
            self.rules.push(Rule {
                premise: binder_type.clone(),
                conclusion: body.clone(),
                proof: fact.value.clone(),
            });
            if *body == constant("False") {
                let iff = apply(
                    constant("Iff.intro"),
                    [
                        binder_type.clone(),
                        constant("False"),
                        fact.value.clone(),
                        lambda(constant("False"), false_elim(binder_type.clone(), bound())),
                    ],
                );
                self.graph.add(
                    context,
                    &Typed {
                        value: apply(
                            constant("propext"),
                            [binder_type.clone(), constant("False"), iff],
                        ),
                        type_: equality::equation(
                            Level::one(),
                            Expr::sort(Level::zero()),
                            binder_type.clone(),
                            constant("False"),
                        ),
                    },
                )?;
            }
        }
        Ok(())
    }

    fn truth(&mut self, context: &mut Context, target: &Expr) -> Result<Option<Expr>, Error> {
        let target = normalize(context, target)?;
        if let Some(index) = self.indices.get(&target) {
            return Ok(Some(self.facts[*index].value.clone()));
        }
        if let Some(index) = self.indices.get(&constant("False")) {
            return Ok(Some(false_elim(target, self.facts[*index].value.clone())));
        }
        if target == constant("True") {
            return Ok(Some(constant("True.intro")));
        }
        if let Some((_, _, left, right)) = equality_target(&target)
            && let Some(proof) = self.graph.equation(context, &left, &right)?
        {
            return Ok(Some(proof));
        }
        Ok(self
            .graph
            .equation(context, &target, &constant("True"))?
            .map(|proof| {
                apply(
                    Expr::const_(name("Eq.mpr"), vec![Level::zero()]),
                    [target, constant("True"), proof, constant("True.intro")],
                )
            }))
    }

    fn negative(
        &mut self,
        context: &mut Context,
        proposition: &Expr,
    ) -> Result<Option<Expr>, Error> {
        let p = normalize(context, proposition)?;
        Ok(self
            .graph
            .equation(context, &p, &constant("False"))?
            .map(|proof| {
                lambda(
                    p.clone(),
                    apply(
                        Expr::const_(name("Eq.mp"), vec![Level::zero()]),
                        [p, constant("False"), proof, bound()],
                    ),
                )
            }))
    }

    fn construct(&mut self, context: &mut Context, proposition: &Expr) -> Result<(), Error> {
        if let Some((left, right)) = binary(proposition, "And") {
            if let (Some(a), Some(b)) = (self.truth(context, &left)?, self.truth(context, &right)?)
            {
                self.enqueue(
                    context,
                    Typed {
                        type_: proposition.clone(),
                        value: apply(constant("And.intro"), [left, right, a, b]),
                    },
                )?;
            }
        } else if let Some((left, right)) = binary(proposition, "Or") {
            let proof = if let Some(proof) = self.truth(context, &left)? {
                Some(apply(
                    constant("Or.inl"),
                    [left.clone(), right.clone(), proof],
                ))
            } else {
                self.truth(context, &right)?
                    .map(|proof| apply(constant("Or.inr"), [left.clone(), right.clone(), proof]))
            };
            if let Some(value) = proof {
                self.enqueue(
                    context,
                    Typed {
                        type_: proposition.clone(),
                        value,
                    },
                )?;
            }
            if let Some(index) = self.indices.get(proposition).copied() {
                let disjunction = self.facts[index].value.clone();
                if let Some(no_left) = self.negative(context, &left)? {
                    let value = apply(
                        constant("Or.elim"),
                        [
                            left.clone(),
                            right.clone(),
                            right.clone(),
                            disjunction.clone(),
                            lambda(
                                left.clone(),
                                false_elim(right.clone(), Expr::app(no_left, bound())),
                            ),
                            lambda(right.clone(), bound()),
                        ],
                    );
                    self.enqueue(
                        context,
                        Typed {
                            type_: right.clone(),
                            value,
                        },
                    )?;
                }
                if let Some(no_right) = self.negative(context, &right)? {
                    let value = apply(
                        constant("Or.elim"),
                        [
                            left.clone(),
                            right.clone(),
                            left.clone(),
                            disjunction,
                            lambda(left.clone(), bound()),
                            lambda(
                                right.clone(),
                                false_elim(left.clone(), Expr::app(no_right, bound())),
                            ),
                        ],
                    );
                    self.enqueue(context, Typed { type_: left, value })?;
                }
            }
        } else if let Some((left, right)) = binary(proposition, "Iff") {
            if let (Some(a), Some(b)) = (
                self.truth(context, &arrow(left.clone(), right.clone()))?,
                self.truth(context, &arrow(right.clone(), left.clone()))?,
            ) {
                self.enqueue(
                    context,
                    Typed {
                        type_: proposition.clone(),
                        value: apply(constant("Iff.intro"), [left, right, a, b]),
                    },
                )?;
            }
        } else if let ExprNode::ForallE {
            binder_type, body, ..
        } = proposition.node()
            && !body.has_loose_bvars()
            && is_prop(context, binder_type)?
        {
            let value = if binder_type == body {
                Some(lambda(binder_type.clone(), bound()))
            } else if let Some(proof) = self.truth(context, body)? {
                Some(lambda(binder_type.clone(), proof))
            } else {
                self.negative(context, binder_type)?.map(|proof| {
                    lambda(
                        binder_type.clone(),
                        false_elim(body.clone(), Expr::app(proof, bound())),
                    )
                })
            };
            if let Some(value) = value {
                self.enqueue(
                    context,
                    Typed {
                        type_: proposition.clone(),
                        value,
                    },
                )?;
            }
        }
        Ok(())
    }

    fn saturate(&mut self, context: &mut Context, target: &Expr) -> Result<Option<Expr>, Error> {
        loop {
            while let Some(fact) = self.pending.pop_front() {
                context.tick()?;
                self.queued.remove(&fact.type_);
                if self.indices.contains_key(&fact.type_) {
                    continue;
                }
                self.indices.insert(fact.type_.clone(), self.facts.len());
                self.facts.push(fact.clone());
                self.expand(context, fact)?;
            }
            self.graph.saturate(context)?;
            for evidence in std::mem::take(&mut self.graph.consequences) {
                context.tick()?;
                if let Some((_, _, left, right)) = equality_target(&evidence.type_)
                    && let (Some((left_name, fields)), Some((right_name, _))) = (
                        constructor_shape(context, &left)?,
                        constructor_shape(context, &right)?,
                    )
                {
                    // Do not let the generic injection helper unfold a
                    // semireducible function that grind treats as uninterpreted.
                    if let Some(false_) = context.constructor_clash_evidence(&evidence)? {
                        self.enqueue(context, false_)?;
                    } else if left_name == right_name {
                        for index in 0..fields {
                            context.tick()?;
                            if let Some(field) =
                                context.constructor_injection_evidence(&evidence, index)?
                            {
                                self.enqueue(context, field)?;
                            }
                        }
                    }
                }
            }
            if let Some(proof) = self.truth(context, target)? {
                return Ok(Some(proof));
            }
            for rule in self.rules.clone() {
                context.tick()?;
                if let Some(premise) = self.truth(context, &rule.premise)? {
                    self.enqueue(
                        context,
                        Typed {
                            type_: rule.conclusion,
                            value: Expr::app(rule.proof, premise),
                        },
                    )?;
                }
            }
            let propositions: Vec<_> = self
                .graph
                .nodes
                .iter()
                .filter(|node| node.proposition)
                .map(|node| node.term.clone())
                .collect();
            for proposition in propositions {
                context.tick()?;
                if let Some(value) = self.truth(context, &proposition)? {
                    self.enqueue(
                        context,
                        Typed {
                            type_: proposition.clone(),
                            value,
                        },
                    )?;
                }
                self.construct(context, &proposition)?;
            }
            if self.pending.is_empty() {
                let instances = self.quantifiers.instantiate(context, &self.graph)?;
                for instance in instances {
                    self.enqueue(context, instance)?;
                }
            }
            if self.pending.is_empty() {
                return Ok(None);
            }
        }
    }

    fn solve(
        &mut self,
        context: &mut Context,
        target: &Expr,
        depth: usize,
    ) -> Result<Option<Expr>, Error> {
        if let Some(proof) = self.saturate(context, target)? {
            return Ok(Some(proof));
        }
        let mut propositions = vec![target.clone()];
        propositions.extend(
            self.graph
                .nodes
                .iter()
                .filter(|node| node.proposition)
                .map(|node| node.term.clone()),
        );
        let mut selected = None;
        for proposition in propositions {
            context.tick()?;
            if proposition == constant("True")
                || proposition == constant("False")
                || matches!(proposition.node(), ExprNode::ForallE { .. })
                || ["And", "Or", "Iff"]
                    .iter()
                    .any(|operator| binary(&proposition, operator).is_some())
                || self.truth(context, &proposition)?.is_some()
                || self.negative(context, &proposition)?.is_some()
            {
                continue;
            }
            selected = Some(proposition);
            break;
        }
        let Some(proposition) = selected else {
            return Ok(None);
        };
        if depth >= MAX_SPLITS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut branches = Vec::new();
        for hypothesis in [
            proposition.clone(),
            arrow(proposition.clone(), constant("False")),
        ] {
            let before = context.clone();
            let mut branch = self.clone();
            let local = context.equality_local(hypothesis.clone())?;
            context.txn.lctx.add_param(
                local.id.clone(),
                local.user_name.clone(),
                hypothesis.clone(),
                BinderInfo::Default,
            );
            let result = (|| {
                branch.enqueue(
                    context,
                    Typed {
                        value: Expr::fvar(local.id.clone()),
                        type_: hypothesis,
                    },
                )?;
                branch
                    .solve(context, target, depth + 1)?
                    .map(|proof| context.close_equality_binder(&local, proof, true))
                    .transpose()
            })();
            restore(context, before);
            let Some(proof) = result? else {
                return Ok(None);
            };
            branches.push(proof);
        }
        Ok(Some(apply(
            constant("Classical.byCases"),
            [
                proposition,
                target.clone(),
                branches[0].clone(),
                branches[1].clone(),
            ],
        )))
    }
}

impl Context {
    fn grind_parameters<'a>(&mut self, syntax: &'a Syntax) -> Result<Vec<&'a Syntax>, Error> {
        let parts = expect_null_args(syntax, "grind parameters")?;
        if parts.is_empty() {
            return Ok(Vec::new());
        }
        let [open, entries, close] = parts else {
            return Err(unsupported());
        };
        expect_atom(open, "[", "grind parameters")?;
        expect_atom(close, "]", "grind parameters")?;
        let entries = expect_null_args(entries, "grind parameters")?;
        if !entries.is_empty() && entries.len() % 2 == 0 {
            return Err(unsupported());
        }
        let mut terms = Vec::new();
        for (index, entry) in entries.iter().enumerate() {
            self.tick()?;
            if index % 2 == 1 {
                expect_atom(entry, ",", "grind parameter separator")?;
                continue;
            }
            let [entry] = expect_node(
                entry,
                &parser_kind(&["Tactic", "grindParam"]),
                1,
                "grind parameter",
            )
            .map_err(|_| unsupported())?
            else {
                return Err(unsupported());
            };
            let [modifier, term] = expect_node(
                entry,
                &parser_kind(&["Tactic", "grindLemma"]),
                2,
                "grind lemma",
            )
            .map_err(|_| unsupported())?
            else {
                return Err(unsupported());
            };
            if !expect_null_args(modifier, "grind modifier")?.is_empty() {
                return Err(unsupported());
            }
            terms.push(term);
        }
        Ok(terms)
    }

    fn grind_lemma(&mut self, syntax: &Syntax) -> Result<(Typed, Vec<Name>), Error> {
        let mut level_params = Vec::new();
        let evidence = if let Syntax::Ident { val, .. } = syntax {
            // Bare local names are redundant parameters at the pin, which
            // already activates quantified hypotheses automatically.
            if self.txn.lctx.find_by_user_name(val).is_some() {
                return Err(unsupported());
            }
            let resolved = self
                .resolve_source_name(val)?
                .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(val.clone())))?;
            let info = self
                .txn
                .env
                .find(&resolved)
                .cloned()
                .ok_or_else(unsupported)?;
            if !matches!(
                info,
                fln_env::constants::ConstantInfo::Thm(_)
                    | fln_env::constants::ConstantInfo::Axiom(_)
                    | fln_env::constants::ConstantInfo::Ctor(_)
            ) {
                // Definition selections need their equation theorem producer.
                return Err(unsupported());
            }
            let base = info.constant_val();
            for _ in &base.level_params {
                // These names belong to this matching template, never to the
                // caller's universe context. Every one must be instantiated
                // from the selected ground applications before proof use.
                level_params.push(self.fresh_name()?);
            }
            let levels: Vec<_> = level_params.iter().cloned().map(Level::param).collect();
            Typed {
                value: Expr::const_(resolved, levels.clone()),
                type_: self.instantiate_params(&base.type_, &base.level_params, &levels)?,
            }
        } else {
            // As for rewrite/simp, do not re-enter the proof driver through a
            // syntax client while this proof worklist frame is active.
            let mut pending = vec![syntax];
            while let Some(term) = pending.pop() {
                self.tick()?;
                if let Syntax::Node { kind, args, .. } = term {
                    if kind == &parser_kind(&["Term", "byTactic"]) {
                        return Err(unsupported());
                    }
                    pending.extend(args);
                }
            }
            self.term(syntax, None)?
        };
        let evidence = Typed {
            value: normalize(self, &evidence.value)?,
            type_: normalize(self, &evidence.type_)?,
        };
        if !is_prop(self, &evidence.type_)? {
            return Err(unsupported());
        }
        Ok((evidence, level_params))
    }

    pub(super) fn grind_proof_goal(
        &mut self,
        mut goal: ProofGoal,
        syntax: &[Syntax],
    ) -> Result<(), Error> {
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "grind"])?;
        if !self.txn.env.contains(&name("Lean.Parser.Tactic.grind")) {
            return Err(failure(SourceInferenceError::UnknownConstant(name(
                "Lean.Parser.Tactic.grind",
            ))));
        }
        let [keyword, config, only, parameters, interactive] = syntax else {
            return Err(unsupported());
        };
        expect_atom(keyword, "grind", "grind tactic")?;
        if expect_default_config(config, "grind configuration").is_err() {
            return Err(unsupported());
        }
        match expect_null_args(only, "grind only")? {
            [] => {}
            [keyword] => {
                expect_atom(keyword, "only", "grind only")?;
            }
            _ => return Err(unsupported()),
        }
        if !expect_null_args(interactive, "grind interactive block")?.is_empty() {
            return Err(unsupported());
        }
        let parameters = self.grind_parameters(parameters)?;
        let before = self.clone();
        let result = (|| {
            self.txn.lctx = goal.lctx.clone();
            loop {
                let target = normalize(self, &goal.target)?;
                if !matches!(
                    target.node(),
                    ExprNode::ForallE { .. } | ExprNode::LetE { .. }
                ) {
                    break;
                }
                self.tick()?;
                let name = self.fresh_name()?;
                self.introduce_proof_binder(&mut goal, name)?;
            }
            goal.lctx = self.txn.lctx.clone();
            let target = normalize(self, &goal.target)?;
            if !is_prop(self, &target)? {
                return Err(unsupported());
            }
            let mut state = State::default();
            state.observe(self, &target)?;
            for local in goal.lctx.decls().to_vec() {
                self.tick()?;
                if !self.is_matrix_hypothesis(&local) && is_prop(self, &local.type_)? {
                    state.enqueue(
                        self,
                        Typed {
                            type_: local.type_,
                            value: Expr::fvar(local.id),
                        },
                    )?;
                }
            }
            for parameter in parameters {
                let (evidence, level_params) = self.grind_lemma(parameter)?;
                if matches!(evidence.type_.node(), ExprNode::ForallE { .. }) {
                    if !state
                        .quantifiers
                        .register(self, &evidence, &level_params, false)?
                    {
                        return Err(unsupported());
                    }
                } else {
                    if !level_params.is_empty() || matches!(parameter, Syntax::Ident { .. }) {
                        // A bare declaration uses the pin's theorem-pattern
                        // path even when ground. In particular, `[falseAx]`
                        // is invalid, while the explicit proof `[(falseAx)]`
                        // is an extra fact. Ground declaration pattern
                        // inference is not implemented by this fragment.
                        return Err(unsupported());
                    }
                    state.enqueue(self, evidence)?;
                }
            }
            let proof = state.solve(self, &target, 0)?.ok_or_else(unsupported)?;
            self.close_proof_goal(goal, proof)
        })();
        if result.is_err() {
            restore(self, before);
        }
        result
    }
}
