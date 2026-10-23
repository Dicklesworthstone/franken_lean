//! Native omega frontend. Logical cases and arithmetic normalization construct
//! ordinary proof terms; only the enclosing declaration admission checks them.
mod normalize;
mod replay;

use super::*;
use crate::arithmetic::{OmegaLimits, OmegaResource};
use fln_bignum::int::BigInt;
use replay::{apply, constant, integer, resource};
use std::collections::{HashSet, VecDeque};

#[derive(Clone, Copy)]
enum Relation {
    Le,
    Lt,
    Eq,
    Ne,
}
#[derive(Clone)]
struct Comparison {
    relation: Relation,
    natural: bool,
    left: Expr,
    right: Expr,
}
#[derive(Clone)]
struct Facts {
    pending: VecDeque<(Expr, Expr)>,
    processed: HashSet<Expr>,
    subtractions: HashSet<Expr>,
    /// `Fin.val n i` atoms whose bound `i < n` is already a fact.
    fins: HashSet<Expr>,
    linear: Vec<(Expr, Expr)>,
}
impl Facts {
    fn new(pending: VecDeque<(Expr, Expr)>) -> Self {
        Self {
            pending,
            processed: HashSet::new(),
            subtractions: HashSet::new(),
            fins: HashSet::new(),
            linear: Vec::new(),
        }
    }
    fn push(&mut self, proposition: Expr, evidence: Expr) -> Result<(), NatDefinitionElabError> {
        let size = self.pending.len().saturating_add(self.processed.len());
        if size >= OmegaLimits::default().max_rows {
            return Err(resource(
                OmegaResource::Rows,
                OmegaLimits::default().max_rows,
                size + 1,
            ));
        }
        self.pending
            .try_reserve(1)
            .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
        self.pending.push_back((proposition, evidence));
        Ok(())
    }
}
fn is_constant(expr: &Expr, name: &str) -> bool {
    matches!(expr.node(), ExprNode::Const { name: found, .. }
        if found == &Name::from_components(name.split('.')))
}
fn application(expr: &Expr) -> Option<(Name, Vec<Expr>)> {
    let mut head = expr;
    let mut arguments = Vec::new();
    loop {
        match head.node() {
            ExprNode::App { f, a } => {
                if arguments.len() >= 8 {
                    return None;
                }
                arguments.push(a.clone());
                head = f;
            }
            ExprNode::MData { expr, .. } => head = expr,
            ExprNode::Const { name, .. } => {
                arguments.reverse();
                return Some((name.clone(), arguments));
            }
            _ => return None,
        }
    }
}
fn unary(expr: &Expr, name: &str) -> Option<Expr> {
    let (head, arguments) = application(expr)?;
    (head == Name::from_components(name.split('.')) && arguments.len() == 1)
        .then(|| arguments[0].clone())
}
fn binary(expr: &Expr, name: &str) -> Option<(Expr, Expr)> {
    let (head, arguments) = application(expr)?;
    (head == Name::from_components(name.split('.')) && arguments.len() == 2)
        .then(|| (arguments[0].clone(), arguments[1].clone()))
}
fn not(proposition: Expr) -> Expr {
    apply(constant("Not"), [proposition])
}
fn and(left: Expr, right: Expr) -> Expr {
    apply(constant("And"), [left, right])
}
fn or(left: Expr, right: Expr) -> Expr {
    apply(constant("Or"), [left, right])
}
fn negated(proposition: &Expr) -> Option<Expr> {
    unary(proposition, "Not").or_else(|| match proposition.node() {
        ExprNode::ForallE {
            binder_type, body, ..
        } if is_constant(body, "False") => Some(binder_type.clone()),
        _ => None,
    })
}
fn implication(proposition: &Expr) -> Option<(Expr, Expr)> {
    match proposition.node() {
        ExprNode::ForallE {
            binder_type, body, ..
        } if !body.has_loose_bvars() => Some((binder_type.clone(), body.clone())),
        _ => None,
    }
}
fn domain(natural: bool) -> Expr {
    constant(if natural { "Nat" } else { "Int" })
}
fn relation_expression(comparison: &Comparison) -> Expr {
    let name = match (comparison.natural, comparison.relation) {
        (true, Relation::Le) => "Nat.le",
        (false, Relation::Le) => "Int.le",
        (true, Relation::Lt) => "Nat.lt",
        (false, Relation::Lt) => "Int.lt",
        (_, Relation::Eq) => "Eq",
        (_, Relation::Ne) => "Ne",
    };
    if matches!(comparison.relation, Relation::Eq | Relation::Ne) {
        apply(
            Expr::const_(Name::from_components([name]), vec![Level::one()]),
            [
                domain(comparison.natural),
                comparison.left.clone(),
                comparison.right.clone(),
            ],
        )
    } else {
        apply(
            constant(name),
            [comparison.left.clone(), comparison.right.clone()],
        )
    }
}
fn comparison(proposition: &Expr) -> Option<Comparison> {
    let (head, arguments) = application(proposition)?;
    for (natural, prefix, le, lt) in [
        (true, "Nat", "instLENat", "instLTNat"),
        (false, "Int", "Int.instLEInt", "Int.instLTInt"),
    ] {
        if arguments.len() == 2 {
            let relation = if head == Name::from_components([prefix, "le"]) {
                Some(Relation::Le)
            } else if head == Name::from_components([prefix, "lt"]) {
                Some(Relation::Lt)
            } else {
                None
            };
            if let Some(relation) = relation {
                return Some(Comparison {
                    relation,
                    natural,
                    left: arguments[0].clone(),
                    right: arguments[1].clone(),
                });
            }
        }
        if arguments.len() == 3 && is_constant(&arguments[0], prefix) {
            let relation = if head == Name::from_components(["Eq"]) {
                Some(Relation::Eq)
            } else if head == Name::from_components(["Ne"]) {
                Some(Relation::Ne)
            } else {
                None
            };
            if let Some(relation) = relation {
                return Some(Comparison {
                    relation,
                    natural,
                    left: arguments[1].clone(),
                    right: arguments[2].clone(),
                });
            }
        }
        if arguments.len() == 4 && is_constant(&arguments[0], prefix) {
            for (field, relation, dictionary, reverse) in [
                ("LE.le", Relation::Le, le, false),
                ("LT.lt", Relation::Lt, lt, false),
                ("GE.ge", Relation::Le, le, true),
                ("GT.gt", Relation::Lt, lt, true),
            ] {
                if head == Name::from_components(field.split('.'))
                    && is_constant(&arguments[1], dictionary)
                {
                    let (left, right) = if reverse {
                        (&arguments[3], &arguments[2])
                    } else {
                        (&arguments[2], &arguments[3])
                    };
                    return Some(Comparison {
                        relation,
                        natural,
                        left: left.clone(),
                        right: right.clone(),
                    });
                }
            }
        }
    }
    None
}

impl Context {
    fn omega_proposition(&mut self, value: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let mut value = self.instantiate(value)?;
        while let ExprNode::MData { expr, .. } = value.node() {
            self.tick()?;
            value = expr.clone();
        }
        if comparison(&value).is_some()
            || negated(&value).is_some()
            || binary(&value, "And").is_some()
            || binary(&value, "Or").is_some()
            || binary(&value, "Iff").is_some()
            || matches!(value.node(), ExprNode::ForallE { .. })
        {
            return Ok(value);
        }
        self.reduce_source_head(&value, UnificationTransparency::Abbreviations, true)
    }

    fn omega_is_proposition(&mut self, value: &Expr) -> Result<bool, NatDefinitionElabError> {
        let Some(type_) = self.known_type(value)? else {
            return Ok(false);
        };
        // Reconstructed function types retain raw imax levels. As in the pin's
        // Meta.isProp, an implication is a proposition when that level is
        // always zero, even if it is not the literal Zero constructor.
        Ok(matches!(self.whnf(&type_)?.node(), ExprNode::Sort { level } if level.is_always_zero()))
    }

    /// A failed ordinary synthesis attempt must leave no instance hole behind.
    /// Resource and cancellation errors are never caught by this fallback.
    fn omega_decidable(
        &mut self,
        proposition: &Expr,
    ) -> Result<(Expr, bool), NatDefinitionElabError> {
        let saved = self.clone();
        match self.decision_dictionary(proposition) {
            Ok(dictionary) => Ok((dictionary, false)),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::InstanceSynthesisRequired,
            )) => {
                let spent = self.txn.budget.heartbeats_consumed;
                *self = saved;
                self.txn.budget.heartbeats_consumed = spent;
                let name = Name::from_components(["Classical", "propDecidable"]);
                if !self.txn.env.contains(&name) {
                    return Err(error(TacticError::ArithmeticUnsupported));
                }
                Ok((
                    apply(constant("Classical.propDecidable"), [proposition.clone()]),
                    true,
                ))
            }
            Err(problem) => Err(problem),
        }
    }

    pub(super) fn omega_proof_goal(
        &mut self,
        mut goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.resolve_instances(false)?;
        self.flush(false)?;
        // The pin tries assumption once before falseOrByContra introduces binders.
        if let Some(proof) = self.matching_assumption(&goal)? {
            return self.close_proof_goal(goal, proof);
        }
        loop {
            self.tick()?;
            let mut raw = self.instantiate(&goal.target)?;
            while let ExprNode::MData { expr, .. } = raw.node() {
                self.tick()?;
                raw = expr.clone();
            }
            // Expose head lets before predicate recognition: a general head
            // reduction would continue into the arithmetic relation itself.
            let mut peek = raw.clone();
            loop {
                self.tick()?;
                match peek.node() {
                    ExprNode::LetE { body, value, .. } => {
                        peek = self.substitute(body, value)?;
                    }
                    ExprNode::MData { expr, .. } => peek = expr.clone(),
                    _ => break,
                }
            }
            let target = self.omega_proposition(&peek)?;
            let binder = matches!(target.node(), ExprNode::ForallE { .. })
                || unary(&target, "Not").is_some()
                || comparison(&target).is_some_and(|c| matches!(c.relation, Relation::Ne));
            // Like falseOrByContra, inspect the reduced head but introduce from
            // the original goal when a let precedes a binder. Its local value
            // must remain opaque inside divisors. A let ending in a proposition
            // is zeta-substituted instead, with conversion against the original
            // goal still checked when close_proof_goal assigns its metavariable.
            goal.target = if binder && matches!(raw.node(), ExprNode::LetE { .. }) {
                raw
            } else {
                target
            };
            if !binder {
                break;
            }
            let name = self.fresh_name()?;
            self.introduce_proof_binder(&mut goal, name)?;
            goal.lctx = self.txn.lctx.clone();
        }
        goal.target = self.instantiate(&goal.target)?;
        self.require_resolved(std::slice::from_ref(&goal.target))?;
        if !self.omega_is_proposition(&goal.target)? {
            return Err(error(TacticError::ExpectedProposition));
        }
        let locals = self.txn.lctx.decls().to_vec();
        let mut pending = VecDeque::new();
        for local in locals {
            self.tick()?;
            if self.is_matrix_hypothesis(&local) || !self.omega_is_proposition(&local.type_)? {
                continue;
            }
            pending.push_back((local.type_, Expr::fvar(local.id)));
        }
        let mut fuel = 256_usize;
        let value = if is_constant(&goal.target, "False") {
            self.omega_refute(Facts::new(pending), &mut fuel)?
        } else {
            let (dictionary, classical) = self.omega_decidable(&goal.target)?;
            let negative = not(goal.target.clone());
            let saved = self.txn.lctx.clone();
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                id.0.clone(),
                negative.clone(),
                BinderInfo::Default,
            );
            pending.push_back((negative.clone(), Expr::fvar(id.clone())));
            let result = self.omega_refute(Facts::new(pending), &mut fuel);
            self.txn.lctx = saved;
            let body = result?
                .abstract_fvar(&id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            let function = Expr::lam(id.0, negative, body, BinderInfo::Default);
            if classical {
                apply(
                    constant("Classical.byContradiction"),
                    [goal.target.clone(), function],
                )
            } else {
                apply(
                    constant("Decidable.byContradiction"),
                    [goal.target.clone(), dictionary, function],
                )
            }
        };
        self.close_proof_goal(goal, value)
    }

    fn omega_scan_subtractions(
        &mut self,
        proposition: &Expr,
        facts: &mut Facts,
    ) -> Result<(), NatDefinitionElabError> {
        let mut pending = vec![proposition.clone()];
        let mut visited = HashSet::new();
        while let Some(value) = pending.pop() {
            self.tick()?;
            if !visited.insert(value.clone()) {
                continue;
            }
            if !value.has_loose_bvars()
                && let Some((left, right)) = normalize::nat_subtraction(&value)
            {
                let key = normalize::standard_sub("Nat", left.clone(), right.clone());
                if facts.subtractions.insert(key.clone()) {
                    let cast = |x| apply(constant("Int.ofNat"), [x]);
                    let linear =
                        normalize::standard_sub("Int", cast(left.clone()), cast(right.clone()));
                    let eq = |x, y| replay::equation(constant("Int"), x, y);
                    let proposition = or(
                        and(
                            apply(constant("Nat.le"), [right.clone(), left.clone()]),
                            eq(cast(key.clone()), linear),
                        ),
                        and(
                            apply(constant("Nat.lt"), [left.clone(), right.clone()]),
                            eq(cast(key), integer(&BigInt::zero())),
                        ),
                    );
                    facts.push(
                        proposition,
                        apply(
                            constant("Lean.Omega.Int.ofNat_sub_dichotomy"),
                            [left, right],
                        ),
                    )?;
                }
            }
            // The pin's `analyzeAtom` (vendored `Lean/Elab/Tactic/Omega/OmegaM.lean:178-179`): a
            // `Fin.val n i` atom brings its bound `↑i < n`, `Fin.isLt n i`.
            if !value.has_loose_bvars()
                && let ExprNode::App { f, a: index } = value.node()
                && let ExprNode::App { f: head, a: bound } = f.node()
                && is_constant(head, "Fin.val")
                && facts.fins.insert(value.clone())
            {
                facts.push(
                    apply(constant("Nat.lt"), [value.clone(), bound.clone()]),
                    apply(constant("Fin.isLt"), [bound.clone(), index.clone()]),
                )?;
            }
            match value.node() {
                ExprNode::App { f, a } => {
                    pending.push(f.clone());
                    pending.push(a.clone());
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    pending.push(expr.clone())
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    pending.push(type_.clone());
                    pending.push(value.clone());
                    pending.push(body.clone());
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    pending.push(binder_type.clone());
                    pending.push(body.clone());
                }
                ExprNode::FVar { id } => {
                    if let Some(value) =
                        self.txn.lctx.find(id).and_then(|local| local.value.clone())
                    {
                        pending.push(value);
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn omega_linear_fact(
        &mut self,
        mut c: Comparison,
        mut proof: Expr,
        facts: &mut Facts,
    ) -> Result<(), NatDefinitionElabError> {
        if c.natural {
            proof = apply(
                constant(if matches!(c.relation, Relation::Lt) {
                    "Lean.Omega.Int.ofNat_lt_of_lt"
                } else {
                    "Lean.Omega.Int.ofNat_le_of_le"
                }),
                [c.left.clone(), c.right.clone(), proof],
            );
            c.left = apply(constant("Int.ofNat"), [c.left]);
            c.right = apply(constant("Int.ofNat"), [c.right]);
        }
        if matches!(c.relation, Relation::Lt) {
            proof = apply(
                constant("Int.add_one_le_of_lt"),
                [c.left.clone(), c.right.clone(), proof],
            );
            c.left = apply(constant("Int.add"), [c.left, integer(&BigInt::from_u64(1))]);
        }
        let term = normalize::standard_sub("Int", c.right.clone(), c.left.clone());
        let proof = apply(constant("Int.sub_nonneg_of_le"), [c.right, c.left, proof]);
        if facts.linear.len() >= OmegaLimits::default().max_rows {
            return Err(resource(
                OmegaResource::Rows,
                OmegaLimits::default().max_rows,
                facts.linear.len() + 1,
            ));
        }
        facts.linear.push((term, proof));
        Ok(())
    }

    fn omega_comparison_fact(
        &mut self,
        c: Comparison,
        proof: Expr,
        facts: &mut Facts,
    ) -> Result<(), NatDefinitionElabError> {
        match c.relation {
            Relation::Le | Relation::Lt => self.omega_linear_fact(c, proof, facts),
            Relation::Eq => {
                let symmetric = apply(
                    Expr::const_(Name::from_components(["Eq", "symm"]), vec![Level::one()]),
                    [
                        domain(c.natural),
                        c.left.clone(),
                        c.right.clone(),
                        proof.clone(),
                    ],
                );
                let rule = constant(if c.natural {
                    "Nat.le_of_eq"
                } else {
                    "Int.le_of_eq"
                });
                for (left, right, evidence) in [
                    (c.left.clone(), c.right.clone(), proof),
                    (c.right, c.left, symmetric),
                ] {
                    let evidence = apply(rule.clone(), [left.clone(), right.clone(), evidence]);
                    self.omega_linear_fact(
                        Comparison {
                            relation: Relation::Le,
                            natural: c.natural,
                            left,
                            right,
                        },
                        evidence,
                        facts,
                    )?;
                }
                Ok(())
            }
            Relation::Ne => {
                let first = Comparison {
                    relation: Relation::Lt,
                    ..c.clone()
                };
                let second = Comparison {
                    relation: Relation::Lt,
                    left: c.right.clone(),
                    right: c.left.clone(),
                    ..c.clone()
                };
                facts.push(
                    or(relation_expression(&first), relation_expression(&second)),
                    apply(
                        constant(if c.natural {
                            "Nat.lt_or_gt_of_ne"
                        } else {
                            "Int.lt_or_gt_of_ne"
                        }),
                        [c.left, c.right, proof],
                    ),
                )
            }
        }
    }

    fn omega_negative_comparison(
        &mut self,
        mut c: Comparison,
        proof: Expr,
        facts: &mut Facts,
    ) -> Result<(), NatDefinitionElabError> {
        match c.relation {
            Relation::Eq => {
                c.relation = Relation::Ne;
                self.omega_comparison_fact(c, proof, facts)
            }
            Relation::Ne => {
                c.relation = Relation::Eq;
                let equality = relation_expression(&c);
                let (dictionary, _) = self.omega_decidable(&equality)?;
                self.omega_comparison_fact(
                    c,
                    apply(
                        constant("Decidable.of_not_not"),
                        [equality, dictionary, proof],
                    ),
                    facts,
                )
            }
            Relation::Le | Relation::Lt => {
                let name = match (c.natural, c.relation) {
                    (true, Relation::Le) => "Nat.gt_of_not_le",
                    (true, _) => "Nat.le_of_not_lt",
                    (false, Relation::Le) => "Lean.Omega.Int.lt_of_not_le",
                    (false, _) => "Lean.Omega.Int.le_of_not_lt",
                };
                let evidence = apply(constant(name), [c.left.clone(), c.right.clone(), proof]);
                c.relation = if matches!(c.relation, Relation::Le) {
                    Relation::Lt
                } else {
                    Relation::Le
                };
                std::mem::swap(&mut c.left, &mut c.right);
                self.omega_linear_fact(c, evidence, facts)
            }
        }
    }

    fn omega_branch(
        &mut self,
        mut facts: Facts,
        proposition: Expr,
        fuel: &mut usize,
    ) -> Result<Expr, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let id = FVarId(self.fresh_name()?);
        self.txn.lctx.add_param(
            id.clone(),
            id.0.clone(),
            proposition.clone(),
            BinderInfo::Default,
        );
        let result = (|| {
            facts.push(proposition.clone(), Expr::fvar(id.clone()))?;
            self.omega_refute(facts, fuel)
        })();
        self.txn.lctx = saved;
        let body = result?
            .abstract_fvar(&id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        Ok(Expr::lam(id.0, proposition, body, BinderInfo::Default))
    }

    fn omega_refute(
        &mut self,
        mut facts: Facts,
        fuel: &mut usize,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        if *fuel == 0 {
            return Err(resource(OmegaResource::Rows, 256, 257));
        }
        *fuel -= 1;
        while let Some((proposition, proof)) = facts.pending.pop_front() {
            self.tick()?;
            let proposition = self.omega_proposition(&proposition)?;
            if !facts.processed.insert(proposition.clone()) {
                continue;
            }
            self.omega_scan_subtractions(&proposition, &mut facts)?;
            if let Some(c) = comparison(&proposition) {
                self.omega_comparison_fact(c, proof, &mut facts)?;
                continue;
            }
            if let Some((left, right)) = binary(&proposition, "And") {
                facts.push(
                    left.clone(),
                    apply(
                        constant("And.left"),
                        [left.clone(), right.clone(), proof.clone()],
                    ),
                )?;
                facts.push(
                    right.clone(),
                    apply(constant("And.right"), [left, right, proof]),
                )?;
                continue;
            }
            if let Some((left, right)) = binary(&proposition, "Or") {
                // Both branches inherit the processed original and all generated
                // dichotomies, so this disjunction cannot regenerate itself.
                let first = self.omega_branch(facts.clone(), left.clone(), fuel)?;
                let second = self.omega_branch(facts, right.clone(), fuel)?;
                return Ok(apply(
                    constant("Or.elim"),
                    [left, right, constant("False"), proof, first, second],
                ));
            }
            if let Some(inner) = negated(&proposition) {
                let inner = self.omega_proposition(&inner)?;
                if let Some(c) = comparison(&inner) {
                    self.omega_negative_comparison(c, proof, &mut facts)?;
                    continue;
                }
                if let Some(positive) = negated(&inner) {
                    let (dictionary, _) = self.omega_decidable(&positive)?;
                    facts.push(
                        positive.clone(),
                        apply(
                            constant("Decidable.of_not_not"),
                            [positive, dictionary, proof],
                        ),
                    )?;
                    continue;
                }
                if let Some((left, right)) = binary(&inner, "Or") {
                    facts.push(
                        and(not(left.clone()), not(right.clone())),
                        apply(
                            constant("Lean.Omega.and_not_not_of_not_or"),
                            [left, right, proof],
                        ),
                    )?;
                    continue;
                }
                if let Some((left, right)) = binary(&inner, "And") {
                    let (dl, _) = self.omega_decidable(&left)?;
                    let (dr, _) = self.omega_decidable(&right)?;
                    facts.push(
                        or(not(left.clone()), not(right.clone())),
                        apply(
                            constant("Lean.Omega.Decidable.or_not_not_of_not_and"),
                            [left, right, dl, dr, proof],
                        ),
                    )?;
                    continue;
                }
                if let Some((left, right)) = binary(&inner, "Iff") {
                    let (dl, _) = self.omega_decidable(&left)?;
                    let (dr, _) = self.omega_decidable(&right)?;
                    facts.push(
                        or(
                            and(left.clone(), not(right.clone())),
                            and(not(left.clone()), right.clone()),
                        ),
                        apply(
                            constant("Lean.Omega.Decidable.and_not_or_not_and_of_not_iff"),
                            [left, right, dl, dr, proof],
                        ),
                    )?;
                    continue;
                }
                if let Some((left, right)) = implication(&inner)
                    && self.omega_is_proposition(&left)?
                    && self.omega_is_proposition(&right)?
                {
                    let (dictionary, _) = self.omega_decidable(&left)?;
                    facts.push(
                        and(left.clone(), not(right.clone())),
                        apply(
                            constant("Lean.Omega.Decidable.and_not_of_not_imp"),
                            [left, right, dictionary, proof],
                        ),
                    )?;
                }
                continue;
            }
            if let Some((left, right)) = binary(&proposition, "Iff") {
                let (dictionary, _) = self.omega_decidable(&right)?;
                facts.push(
                    or(
                        and(left.clone(), right.clone()),
                        and(not(left.clone()), not(right.clone())),
                    ),
                    apply(
                        constant("Lean.Omega.Decidable.and_or_not_and_not_of_iff"),
                        [left, right, dictionary, proof],
                    ),
                )?;
                continue;
            }
            if let Some((left, right)) = implication(&proposition)
                && self.omega_is_proposition(&left)?
                && self.omega_is_proposition(&right)?
            {
                let (dictionary, _) = self.omega_decidable(&left)?;
                facts.push(
                    or(not(left.clone()), right.clone()),
                    apply(
                        constant("Decidable.not_or_of_imp"),
                        [left, right, dictionary, proof],
                    ),
                )?;
            }
        }
        self.omega_contradiction(facts.linear)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn implication_hypotheses_are_propositions_under_raw_imax_levels() {
        let mut context = Context::new(&Environment::new(), Budget::DEFAULT);
        let mut parameter = |name: &str, level: Level| {
            let name = Name::from_components([name]);
            let id = FVarId(name.clone());
            context
                .txn
                .lctx
                .add_param(id.clone(), name, Expr::sort(level), BinderInfo::Default);
            Expr::fvar(id)
        };
        let proposition = parameter("P", Level::zero());
        let conclusion = parameter("Q", Level::zero());
        let data = parameter("T", Level::one());
        let implication = Expr::forall_e(
            Name::anonymous(),
            proposition.clone(),
            conclusion,
            BinderInfo::Default,
        );
        let inferred = context.known_type(&implication).unwrap().unwrap();
        assert!(matches!(inferred.node(), ExprNode::Sort { level }
            if !level.is_zero() && level.is_always_zero()));
        assert!(context.omega_is_proposition(&implication).unwrap());
        let data_function =
            Expr::forall_e(Name::anonymous(), proposition, data, BinderInfo::Default);
        assert!(!context.omega_is_proposition(&data_function).unwrap());
    }
}
