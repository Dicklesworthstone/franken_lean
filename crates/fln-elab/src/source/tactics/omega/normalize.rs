//! Proof-producing reification of integer affine expressions.
//!
//! Reification records a DAG first. Equality proofs are made only after the
//! complete atom vector is known, so adding a later atom cannot change the
//! meaning of a previously constructed coordinate proof. Definitions and
//! arbitrary instance dictionaries are never unfolded to guess arithmetic.

mod divmod;

use super::super::*;
use super::replay::{
    Proofs, apply, check_integer, coefficients, constant, equation, int_list, int_symmetry,
    int_transitivity, integer, natural, reflexivity, resource,
};
use crate::arithmetic::{LinearConstraint, OmegaLimits, OmegaResource};
use fln_bignum::{int::BigInt, interop::bignat_from_literal, nat::BigNat};
use std::collections::{HashMap, HashSet};

#[derive(Clone)]
pub(super) struct Affine {
    pub(super) constant: BigInt,
    pub(super) coefficients: Vec<BigInt>,
}

impl Affine {
    fn constant(value: BigInt) -> Self {
        Self {
            constant: value,
            coefficients: Vec::new(),
        }
    }

    fn is_constant(&self) -> bool {
        self.coefficients.iter().all(BigInt::is_zero)
    }

    pub(super) fn expression(&self) -> Expr {
        apply(
            constant("Lean.Omega.LinearCombo.mk"),
            [integer(&self.constant), coefficients(&self.coefficients)],
        )
    }

    pub(super) fn evaluation(&self, atoms: &Expr) -> Expr {
        apply(
            constant("Lean.Omega.LinearCombo.eval"),
            [self.expression(), atoms.clone()],
        )
    }

    fn binary(
        &self,
        other: &Self,
        operation: Binary,
        context: &mut Context,
        limits: OmegaLimits,
    ) -> Result<Self, NatDefinitionElabError> {
        let constant = match operation {
            Binary::Add => self.constant.add(&other.constant),
            Binary::Sub => self.constant.sub(&other.constant),
            Binary::Mul => self.constant.mul(&other.constant),
        };
        check_integer(&constant, limits)?;
        let length = self.coefficients.len().max(other.coefficients.len());
        let zero = BigInt::zero();
        let mut coefficients = Vec::new();
        coefficients
            .try_reserve_exact(length)
            .map_err(|_| resource(OmegaResource::Allocation, 0, length))?;
        for index in 0..length {
            context.tick()?;
            let left = self.coefficients.get(index).unwrap_or(&zero);
            let right = other.coefficients.get(index).unwrap_or(&zero);
            let coefficient = match operation {
                Binary::Add => left.add(right),
                Binary::Sub => left.sub(right),
                // The caller established that one vector is all zero.
                // This is the exact coefficient formula of LinearCombo.mul.
                Binary::Mul => left.mul(&other.constant).add(&right.mul(&self.constant)),
            };
            check_integer(&coefficient, limits)?;
            coefficients.push(coefficient);
        }
        Ok(Self {
            constant,
            coefficients,
        })
    }
}

#[derive(Clone, Copy)]
enum Binary {
    Add,
    Sub,
    Mul,
}

enum Recipe {
    Constant,
    Atom(usize),
    Rewrite {
        child: usize,
        evidence: Option<Expr>,
    },
    Neg(usize),
    Binary {
        left: usize,
        right: usize,
        operation: Binary,
        constant_left: bool,
    },
}

pub(super) struct Node {
    pub(super) expression: Expr,
    pub(super) affine: Affine,
    recipe: Recipe,
}

enum Work {
    Visit(Expr),
    Rewrite(Expr, Option<Expr>),
    Neg(Expr),
    Binary(Expr, Binary),
}

pub(super) struct Normalization {
    pub(super) nodes: Vec<Node>,
    pub(super) facts: Vec<(usize, Expr)>,
    atoms: Vec<Expr>,
    node_index: HashMap<Expr, usize>,
    atom_index: HashMap<Expr, usize>,
    nonnegative: HashSet<Expr>,
    divmod: divmod::State,
    pending_facts: Vec<(Expr, Expr)>,
    bytes: usize,
    limits: OmegaLimits,
}

impl Normalization {
    pub(super) fn collect(
        context: &mut Context,
        facts: Vec<(Expr, Expr)>,
        limits: OmegaLimits,
    ) -> Result<Self, NatDefinitionElabError> {
        let mut result = Self {
            nodes: Vec::new(),
            facts: Vec::new(),
            atoms: Vec::new(),
            node_index: HashMap::new(),
            atom_index: HashMap::new(),
            nonnegative: HashSet::new(),
            divmod: divmod::State::default(),
            pending_facts: facts,
            bytes: 0,
            limits,
        };
        let mut next = 0;
        while next < result.pending_facts.len() {
            context.tick()?;
            if result.pending_facts.len() > limits.max_rows {
                return Err(resource(
                    OmegaResource::Rows,
                    limits.max_rows,
                    result.pending_facts.len(),
                ));
            }
            let (expression, evidence) = result.pending_facts[next].clone();
            let expression = context.instantiate(&expression)?;
            let evidence = context.instantiate(&evidence)?;
            context.require_resolved(&[expression.clone(), evidence.clone()])?;
            if expression.has_loose_bvars() || evidence.has_loose_bvars() {
                return Err(failure(SourceInferenceError::Scope));
            }
            let root = result.reify(context, expression)?;
            result.facts.push((root, evidence));
            next += 1;
        }
        Ok(result)
    }

    pub(super) fn inputs(&self) -> Vec<LinearConstraint> {
        self.facts
            .iter()
            .map(|(root, _)| {
                let affine = &self.nodes[*root].affine;
                LinearConstraint {
                    coeffs: affine.coefficients.iter().map(BigInt::neg).collect(),
                    bound: affine.constant.clone(),
                }
            })
            .collect()
    }

    pub(super) fn atoms_expression(&self) -> Expr {
        int_list(self.atoms.iter().cloned())
    }

    pub(super) fn atom_count(&self) -> usize {
        self.atoms.len()
    }

    pub(super) fn atom_expression(&self, index: usize) -> Option<&Expr> {
        self.atoms.get(index)
    }

    fn node(
        &mut self,
        context: &mut Context,
        expression: Expr,
        affine: Affine,
        recipe: Recipe,
    ) -> Result<usize, NatDefinitionElabError> {
        context.tick()?;
        if self.nodes.len() >= self.limits.max_rows {
            return Err(resource(
                OmegaResource::Rows,
                self.limits.max_rows,
                self.nodes.len() + 1,
            ));
        }
        let mut added = 32_usize;
        for value in affine
            .coefficients
            .iter()
            .chain(std::iter::once(&affine.constant))
        {
            check_integer(value, self.limits)?;
            added = added
                .checked_add(9 + 8 * value.magnitude().limbs_le().len())
                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        }
        self.bytes = self
            .bytes
            .checked_add(added)
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        if self.bytes > self.limits.max_certificate_bytes {
            return Err(resource(
                OmegaResource::CertificateBytes,
                self.limits.max_certificate_bytes,
                self.bytes,
            ));
        }
        self.nodes
            .try_reserve(1)
            .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
        self.node_index
            .try_reserve(1)
            .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
        let index = self.nodes.len();
        self.node_index.insert(expression.clone(), index);
        self.nodes.push(Node {
            expression,
            affine,
            recipe,
        });
        Ok(index)
    }

    fn atom(
        &mut self,
        context: &mut Context,
        expression: Expr,
    ) -> Result<usize, NatDefinitionElabError> {
        let coordinate = if let Some(&index) = self.atom_index.get(&expression) {
            index
        } else {
            if self.atoms.len() >= self.limits.max_variables {
                return Err(resource(
                    OmegaResource::Variables,
                    self.limits.max_variables,
                    self.atoms.len() + 1,
                ));
            }
            let index = self.atoms.len();
            self.atoms
                .try_reserve(1)
                .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
            self.atom_index
                .try_reserve(1)
                .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
            self.atoms.push(expression.clone());
            self.atom_index.insert(expression.clone(), index);
            index
        };
        let mut coefficients = vec![BigInt::zero(); coordinate + 1];
        coefficients[coordinate] = BigInt::from_u64(1);
        self.node(
            context,
            expression,
            Affine {
                constant: BigInt::zero(),
                coefficients,
            },
            Recipe::Atom(coordinate),
        )
    }

    fn nat_nonnegative(
        &mut self,
        expression: &Expr,
        argument: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        self.nonnegative
            .try_reserve(1)
            .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
        if self.nonnegative.insert(expression.clone()) {
            if self.pending_facts.len() >= self.limits.max_rows {
                return Err(resource(
                    OmegaResource::Rows,
                    self.limits.max_rows,
                    self.pending_facts.len() + 1,
                ));
            }
            self.pending_facts
                .try_reserve(1)
                .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
            self.pending_facts.push((
                expression.clone(),
                apply(constant("Int.natCast_nonneg"), [argument.clone()]),
            ));
        }
        Ok(())
    }

    fn reify(
        &mut self,
        context: &mut Context,
        expression: Expr,
    ) -> Result<usize, NatDefinitionElabError> {
        let mut work = vec![Work::Visit(expression)];
        let mut values = Vec::new();
        while let Some(item) = work.pop() {
            context.tick()?;
            if work.len() > self.limits.max_rows {
                return Err(resource(
                    OmegaResource::Rows,
                    self.limits.max_rows,
                    work.len(),
                ));
            }
            match item {
                Work::Visit(expression) => {
                    if let Some(&index) = self.node_index.get(&expression) {
                        values.push(index);
                        continue;
                    }
                    // Source ascriptions retain a checked anonymous identity
                    // let, whereas the pin emits their inner expression. Reify
                    // that value but keep the original assertion in the equality
                    // proof, so admission still checks its annotation. Written
                    // lets and beta applications remain arithmetic atoms.
                    let reduced = match expression.node() {
                        ExprNode::MData { expr, .. } => Some(expr.clone()),
                        ExprNode::LetE {
                            decl_name,
                            value,
                            body,
                            ..
                        } if decl_name.is_anonymous()
                            && matches!(body.node(), ExprNode::BVar { idx: 0 }) =>
                        {
                            Some(value.clone())
                        }
                        ExprNode::FVar { id } => context
                            .txn
                            .lctx
                            .find(id)
                            .and_then(|local| local.value.clone()),
                        _ => None,
                    };
                    if let Some(reduced) = reduced {
                        let reduced = context.instantiate(&reduced)?;
                        work.push(Work::Rewrite(expression, None));
                        work.push(Work::Visit(reduced));
                        continue;
                    }

                    if let Some(argument) = cast_argument(&expression) {
                        let canonical = apply(constant("Int.ofNat"), [argument.clone()]);
                        if expression != canonical {
                            work.push(Work::Rewrite(expression, None));
                            work.push(Work::Visit(canonical));
                            continue;
                        }
                        if let Some(value) = nat_literal(&argument, self.limits)? {
                            values.push(self.node(
                                context,
                                expression,
                                Affine::constant(BigInt::from_sign_magnitude(false, value)),
                                Recipe::Constant,
                            )?);
                            continue;
                        }
                        let nat_reduced = match argument.node() {
                            ExprNode::MData { expr, .. } => Some(expr.clone()),
                            ExprNode::LetE {
                                decl_name,
                                value,
                                body,
                                ..
                            } if decl_name.is_anonymous()
                                && matches!(body.node(), ExprNode::BVar { idx: 0 }) =>
                            {
                                Some(value.clone())
                            }
                            ExprNode::FVar { id } => context
                                .txn
                                .lctx
                                .find(id)
                                .and_then(|local| local.value.clone()),
                            _ => None,
                        };
                        if let Some(reduced) = nat_reduced {
                            work.push(Work::Rewrite(expression, None));
                            work.push(Work::Visit(apply(constant("Int.ofNat"), [reduced])));
                            continue;
                        }
                        if let Some((head, args)) = named_application(&argument)
                            && head == Name::from_components(["Nat", "succ"])
                            && args.len() == 1
                        {
                            let next = apply(
                                constant("Int.add"),
                                [
                                    apply(constant("Int.ofNat"), [args[0].clone()]),
                                    integer(&BigInt::from_u64(1)),
                                ],
                            );
                            work.push(Work::Rewrite(
                                expression,
                                Some(apply(constant("Int.natCast_succ"), [args[0].clone()])),
                            ));
                            work.push(Work::Visit(next));
                            continue;
                        }
                        if let Some((next, evidence)) = self.divmod_nat_cast(context, &argument)? {
                            work.push(Work::Rewrite(expression, Some(evidence)));
                            work.push(Work::Visit(next));
                            continue;
                        }
                        if let Some((operation, left, right)) = binary_expression(&argument, "Nat")
                        {
                            let (primitive, lemma) = match operation {
                                Binary::Add => ("Int.add", "Int.natCast_add"),
                                Binary::Mul => ("Int.mul", "Int.natCast_mul"),
                                // Truncated subtraction is an atom. The tactic's
                                // checked dichotomy branches constrain this same atom.
                                Binary::Sub => {
                                    let canonical = apply(
                                        constant("Int.ofNat"),
                                        [standard_sub("Nat", left, right)],
                                    );
                                    if expression != canonical {
                                        work.push(Work::Rewrite(expression, None));
                                        work.push(Work::Visit(canonical));
                                        continue;
                                    }
                                    self.nat_nonnegative(&expression, &argument)?;
                                    values.push(self.atom(context, expression)?);
                                    continue;
                                }
                            };
                            if matches!(operation, Binary::Mul) {
                                self.nat_nonnegative(&expression, &argument)?;
                            }
                            let next = apply(
                                constant(primitive),
                                [
                                    apply(constant("Int.ofNat"), [left.clone()]),
                                    apply(constant("Int.ofNat"), [right.clone()]),
                                ],
                            );
                            work.push(Work::Rewrite(
                                expression,
                                Some(apply(constant(lemma), [left, right])),
                            ));
                            work.push(Work::Visit(next));
                            continue;
                        }
                        self.nat_nonnegative(&expression, &argument)?;
                        values.push(self.atom(context, expression)?);
                        continue;
                    }

                    if let Some((head, args)) = named_application(&expression) {
                        if head == Name::from_components(["OfNat", "ofNat"])
                            && args.len() == 3
                            && named_constant(&args[0], "Int")
                            && standard_numeral_instance(&args[2], &args[1], "instOfNat")
                            && let Some(value) = nat_literal(&args[1], self.limits)?
                        {
                            values.push(self.node(
                                context,
                                expression,
                                Affine::constant(BigInt::from_sign_magnitude(false, value)),
                                Recipe::Constant,
                            )?);
                            continue;
                        }
                        if head == Name::from_components(["Int", "negSucc"]) && args.len() == 1 {
                            if let Some(value) = nat_literal(&args[0], self.limits)? {
                                let negative = BigInt::from_sign_magnitude(
                                    true,
                                    value.add(&BigNat::from_u64(1)),
                                );
                                values.push(self.node(
                                    context,
                                    expression,
                                    Affine::constant(negative),
                                    Recipe::Constant,
                                )?);
                            } else {
                                let next = apply(
                                    constant("Int.neg"),
                                    [apply(
                                        constant("Int.add"),
                                        [
                                            apply(constant("Int.ofNat"), [args[0].clone()]),
                                            integer(&BigInt::from_u64(1)),
                                        ],
                                    )],
                                );
                                work.push(Work::Rewrite(
                                    expression,
                                    Some(apply(constant("Int.negSucc_eq"), [args[0].clone()])),
                                ));
                                work.push(Work::Visit(next));
                            }
                            continue;
                        }
                    }
                    if let Some(expansion) = self.divmod_expansion(context, &expression)? {
                        match expansion {
                            divmod::Expansion::Rewrite(next, evidence) => {
                                work.push(Work::Rewrite(expression, evidence));
                                work.push(Work::Visit(next));
                            }
                            divmod::Expansion::Quotient => {
                                values.push(self.atom(context, expression)?);
                            }
                        }
                        continue;
                    }
                    if let Some(inner) = neg_expression(&expression) {
                        work.push(Work::Neg(expression));
                        work.push(Work::Visit(inner));
                    } else if let Some((operation, left, right)) =
                        binary_expression(&expression, "Int")
                    {
                        work.push(Work::Binary(expression, operation));
                        work.push(Work::Visit(right));
                        work.push(Work::Visit(left));
                    } else {
                        values.push(self.atom(context, expression)?);
                    }
                }
                Work::Rewrite(expression, evidence) => {
                    let child = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let affine = self.nodes[child].affine.clone();
                    values.push(self.node(
                        context,
                        expression,
                        affine,
                        Recipe::Rewrite { child, evidence },
                    )?);
                }
                Work::Neg(expression) => {
                    let child = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let original = &self.nodes[child].affine;
                    let affine = Affine {
                        constant: original.constant.neg(),
                        coefficients: original.coefficients.iter().map(BigInt::neg).collect(),
                    };
                    values.push(self.node(context, expression, affine, Recipe::Neg(child))?);
                }
                Work::Binary(expression, operation) => {
                    let right = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let left = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let constant_left = self.nodes[left].affine.is_constant();
                    if matches!(operation, Binary::Mul)
                        && !constant_left
                        && !self.nodes[right].affine.is_constant()
                    {
                        values.push(self.atom(context, expression)?);
                        continue;
                    }
                    let affine = self.nodes[left].affine.binary(
                        &self.nodes[right].affine,
                        operation,
                        context,
                        self.limits,
                    )?;
                    values.push(self.node(
                        context,
                        expression,
                        affine,
                        Recipe::Binary {
                            left,
                            right,
                            operation,
                            constant_left,
                        },
                    )?);
                }
            }
        }
        if values.len() != 1 {
            return Err(failure(SourceInferenceError::Scope));
        }
        values
            .pop()
            .ok_or_else(|| failure(SourceInferenceError::Scope))
    }

    pub(super) fn proofs(
        &self,
        context: &mut Context,
        proofs: &mut Proofs,
        atoms: &Expr,
    ) -> Result<Vec<usize>, NatDefinitionElabError> {
        let mut handles = Vec::new();
        handles
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| resource(OmegaResource::Allocation, 0, self.nodes.len()))?;
        for node in &self.nodes {
            context.tick()?;
            let mut slots = node.affine.coefficients.len().saturating_add(1);
            match &node.recipe {
                Recipe::Neg(child) => {
                    slots = slots.saturating_add(
                        self.nodes[*child]
                            .affine
                            .coefficients
                            .len()
                            .saturating_add(1),
                    );
                }
                Recipe::Binary { left, right, .. } => {
                    slots = slots
                        .saturating_add(
                            self.nodes[*left]
                                .affine
                                .coefficients
                                .len()
                                .saturating_add(1),
                        )
                        .saturating_add(
                            self.nodes[*right]
                                .affine
                                .coefficients
                                .len()
                                .saturating_add(1),
                        );
                }
                _ => {}
            }
            proofs.precharge_affines(context, slots)?;
            let evaluation = node.affine.evaluation(atoms);
            let value = match &node.recipe {
                Recipe::Constant => reflexivity(constant("Int"), node.expression.clone()),
                Recipe::Atom(index) => {
                    let coordinate = apply(
                        constant("Lean.Omega.LinearCombo.coordinate_eval"),
                        [natural(&BigNat::from_u64(*index as u64)), atoms.clone()],
                    );
                    int_symmetry(evaluation.clone(), node.expression.clone(), coordinate)
                }
                Recipe::Rewrite { child, evidence } => {
                    let child_node = &self.nodes[*child];
                    let bridge = evidence
                        .clone()
                        .unwrap_or_else(|| reflexivity(constant("Int"), node.expression.clone()));
                    int_transitivity(
                        node.expression.clone(),
                        child_node.expression.clone(),
                        evaluation.clone(),
                        bridge,
                        proofs.reference(handles[*child])?,
                    )
                }
                Recipe::Neg(child) => {
                    let child_node = &self.nodes[*child];
                    let child_evaluation = child_node.affine.evaluation(atoms);
                    let middle = apply(constant("Int.neg"), [child_evaluation.clone()]);
                    let first = apply(
                        constant("Lean.Omega.Int.neg_congr"),
                        [
                            child_node.expression.clone(),
                            child_evaluation,
                            proofs.reference(handles[*child])?,
                        ],
                    );
                    let last = apply(
                        constant("Lean.Omega.LinearCombo.neg_eval"),
                        [child_node.affine.expression(), atoms.clone()],
                    );
                    int_transitivity(
                        node.expression.clone(),
                        middle.clone(),
                        evaluation.clone(),
                        first,
                        int_symmetry(evaluation.clone(), middle, last),
                    )
                }
                Recipe::Binary {
                    left,
                    right,
                    operation,
                    constant_left,
                } => {
                    let left_node = &self.nodes[*left];
                    let right_node = &self.nodes[*right];
                    let left_evaluation = left_node.affine.evaluation(atoms);
                    let right_evaluation = right_node.affine.evaluation(atoms);
                    let (primitive, congruence, rule) = match operation {
                        Binary::Add => (
                            "Int.add",
                            "Lean.Omega.Int.add_congr",
                            "Lean.Omega.LinearCombo.add_eval",
                        ),
                        Binary::Sub => (
                            "Int.sub",
                            "Lean.Omega.Int.sub_congr",
                            "Lean.Omega.LinearCombo.sub_eval",
                        ),
                        Binary::Mul if *constant_left => (
                            "Int.mul",
                            "Lean.Omega.Int.mul_congr",
                            "Lean.Omega.LinearCombo.mul_eval_of_const_left",
                        ),
                        Binary::Mul => (
                            "Int.mul",
                            "Lean.Omega.Int.mul_congr",
                            "Lean.Omega.LinearCombo.mul_eval_of_const_right",
                        ),
                    };
                    let middle = apply(
                        constant(primitive),
                        [left_evaluation.clone(), right_evaluation.clone()],
                    );
                    let first = apply(
                        constant(congruence),
                        [
                            left_node.expression.clone(),
                            left_evaluation,
                            right_node.expression.clone(),
                            right_evaluation,
                            proofs.reference(handles[*left])?,
                            proofs.reference(handles[*right])?,
                        ],
                    );
                    let mut arguments = vec![
                        left_node.affine.expression(),
                        right_node.affine.expression(),
                        atoms.clone(),
                    ];
                    if matches!(operation, Binary::Mul) {
                        let vector = if *constant_left {
                            &left_node.affine.coefficients
                        } else {
                            &right_node.affine.coefficients
                        };
                        arguments.push(zero_coefficients_proof(vector));
                    }
                    let last = apply(constant(rule), arguments);
                    int_transitivity(
                        node.expression.clone(),
                        middle.clone(),
                        evaluation.clone(),
                        first,
                        int_symmetry(evaluation.clone(), middle, last),
                    )
                }
            };
            handles.push(proofs.push(
                context,
                equation(constant("Int"), node.expression.clone(), evaluation),
                value,
            )?);
        }
        Ok(handles)
    }
}

fn zero_coefficients_proof(vector: &[BigInt]) -> Expr {
    let vector = coefficients(vector);
    let zero = natural(&BigNat::zero());
    let left = equation(
        constant("Nat"),
        apply(constant("Lean.Omega.Coeffs.gcd"), [vector.clone()]),
        zero.clone(),
    );
    let right = apply(constant("Lean.Omega.Coeffs.isZero"), [vector.clone()]);
    let equivalence = apply(constant("Lean.Omega.IntList.gcd_eq_zero"), [vector]);
    apply(
        constant("Iff.mp"),
        [left, right, equivalence, reflexivity(constant("Nat"), zero)],
    )
}

fn named_constant(expression: &Expr, name: &str) -> bool {
    matches!(expression.node(), ExprNode::Const { name: found, .. } if found == &Name::from_components(name.split('.')))
}

fn named_application(expression: &Expr) -> Option<(Name, Vec<Expr>)> {
    let mut current = expression;
    let mut arguments = Vec::new();
    loop {
        match current.node() {
            ExprNode::App { f, a } => {
                if arguments.len() == 8 {
                    return None;
                }
                arguments.push(a.clone());
                current = f;
            }
            ExprNode::MData { expr, .. } => current = expr,
            ExprNode::Const { name, .. } => {
                arguments.reverse();
                return Some((name.clone(), arguments));
            }
            _ => return None,
        }
    }
}

fn standard_numeral_instance(instance: &Expr, value: &Expr, name: &str) -> bool {
    named_application(instance).is_some_and(|(head, arguments)| {
        head == Name::from_components(name.split('.'))
            && arguments.len() == 1
            && arguments[0] == *value
    })
}

fn nat_literal(
    expression: &Expr,
    limits: OmegaLimits,
) -> Result<Option<BigNat>, NatDefinitionElabError> {
    if let ExprNode::Lit {
        literal: Literal::Nat(value),
    } = expression.node()
    {
        if value.limbs_le().len() > limits.max_coefficient_limbs {
            return Err(resource(
                OmegaResource::CoefficientLimbs,
                limits.max_coefficient_limbs,
                value.limbs_le().len(),
            ));
        }
        return Ok(Some(bignat_from_literal(value)));
    }
    if named_constant(expression, "Nat.zero") {
        return Ok(Some(BigNat::zero()));
    }
    if let Some((head, arguments)) = named_application(expression)
        && head == Name::from_components(["OfNat", "ofNat"])
        && arguments.len() == 3
        && named_constant(&arguments[0], "Nat")
        && standard_numeral_instance(&arguments[2], &arguments[1], "instOfNatNat")
        && let ExprNode::Lit {
            literal: Literal::Nat(value),
        } = arguments[1].node()
    {
        if value.limbs_le().len() > limits.max_coefficient_limbs {
            return Err(resource(
                OmegaResource::CoefficientLimbs,
                limits.max_coefficient_limbs,
                value.limbs_le().len(),
            ));
        }
        return Ok(Some(bignat_from_literal(value)));
    }
    Ok(None)
}

fn cast_argument(expression: &Expr) -> Option<Expr> {
    let (head, arguments) = named_application(expression)?;
    if head == Name::from_components(["Int", "ofNat"]) && arguments.len() == 1 {
        Some(arguments[0].clone())
    } else if (head == Name::from_components(["Nat", "cast"])
        || head == Name::from_components(["NatCast", "natCast"]))
        && arguments.len() == 3
        && named_constant(&arguments[0], "Int")
        && named_constant(&arguments[1], "instNatCastInt")
    {
        Some(arguments[2].clone())
    } else {
        None
    }
}

fn binary_expression(expression: &Expr, domain: &str) -> Option<(Binary, Expr, Expr)> {
    let (head, arguments) = named_application(expression)?;
    let domain_is = |expr: &Expr| named_constant(expr, domain);
    for (operation, field, class, lift, instance) in [
        (
            Binary::Add,
            "add",
            "HAdd.hAdd",
            "instHAdd",
            if domain == "Int" {
                "Int.instAdd"
            } else {
                "instAddNat"
            },
        ),
        (
            Binary::Sub,
            "sub",
            "HSub.hSub",
            "instHSub",
            if domain == "Int" {
                "Int.instSub"
            } else {
                "instSubNat"
            },
        ),
        (
            Binary::Mul,
            "mul",
            "HMul.hMul",
            "instHMul",
            if domain == "Int" {
                "Int.instMul"
            } else {
                "instMulNat"
            },
        ),
    ] {
        if !matches!(operation, Binary::Sub)
            && head == Name::from_components([domain, field])
            && arguments.len() == 2
        {
            return Some((operation, arguments[0].clone(), arguments[1].clone()));
        }
        if head == Name::from_components(class.split('.'))
            && arguments.len() == 6
            && arguments[..3].iter().all(domain_is)
            && let Some((constructor, dictionary)) = named_application(&arguments[3])
            && constructor == Name::from_components([lift])
            && dictionary.len() == 2
            && domain_is(&dictionary[0])
            && named_constant(&dictionary[1], instance)
        {
            return Some((operation, arguments[4].clone(), arguments[5].clone()));
        }
    }
    None
}

fn neg_expression(expression: &Expr) -> Option<Expr> {
    let (head, arguments) = named_application(expression)?;
    if head == Name::from_components(["Int", "neg"]) && arguments.len() == 1 {
        Some(arguments[0].clone())
    } else if head == Name::from_components(["Neg", "neg"])
        && arguments.len() == 3
        && named_constant(&arguments[0], "Int")
        && named_constant(&arguments[1], "Int.instNegInt")
    {
        Some(arguments[2].clone())
    } else {
        None
    }
}

/// Only the ordinary Nat subtraction dictionary participates in dichotomies.
pub(super) fn nat_subtraction(expression: &Expr) -> Option<(Expr, Expr)> {
    match binary_expression(expression, "Nat")? {
        (Binary::Sub, left, right) => Some((left, right)),
        _ => None,
    }
}

/// Generated inequalities use the same standard notation spine that the pin
/// reifies. An explicit source Int.sub or Nat.sub remains an opaque atom.
pub(super) fn standard_sub(domain: &str, left: Expr, right: Expr) -> Expr {
    let alpha = constant(domain);
    let dictionary = apply(
        Expr::const_(Name::from_components(["instHSub"]), vec![Level::zero()]),
        [
            alpha.clone(),
            constant(if domain == "Int" {
                "Int.instSub"
            } else {
                "instSubNat"
            }),
        ],
    );
    apply(
        Expr::const_(
            Name::from_components(["HSub", "hSub"]),
            vec![Level::zero(); 3],
        ),
        [alpha.clone(), alpha.clone(), alpha, dictionary, left, right],
    )
}
