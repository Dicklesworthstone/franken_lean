//! Erase a checked Nat equality decision to its existing Boolean runtime row.
//!
//! The proof-producing definitions remain unchanged in the admitted environment.
//! This recognizes their complete seed contracts, including the families and
//! definitions on which they depend. Other decision procedures stay ordinary
//! source code; a familiar name alone never authorizes this reduction.

use super::*;

fn required_decision_name(candidate: &Name, instance: bool) -> bool {
    [
        "Nat",
        "Bool",
        "Eq",
        "Decidable",
        "False",
        "True",
        "Not",
        "decide",
        "Nat.decEq",
        "Nat.beq",
    ]
    .into_iter()
    .any(|expected| candidate == &name(expected))
        || instance && candidate == &name("instDecidableEqNat")
}

impl Preparation<'_> {
    fn checked_nat_decision_contract(&mut self, instance: bool) -> Result<(), IngressError> {
        // Use the same candidates admitted by the source seed. Checking only
        // the instance wrapper would miss a replaced Nat.decEq dependency;
        // checking only Nat.decEq would miss changed eliminator rules.
        for expected in fln_elab::seed::source_seed_declarations() {
            self.tick()?;
            let canonical = match expected {
                Declaration::Axiom(expected)
                    if required_decision_name(&expected.base.name, instance) =>
                {
                    matches!(self.environment.find(&expected.base.name),
                        Some(ConstantInfo::Axiom(actual)) if actual == &expected)
                }
                Declaration::Defn(expected)
                    if required_decision_name(&expected.base.name, instance) =>
                {
                    matches!(self.environment.find(&expected.base.name),
                        Some(ConstantInfo::Defn(actual)) if actual == &expected)
                }
                Declaration::Inductive(block)
                    if block
                        .types
                        .iter()
                        .any(|family| required_decision_name(&family.base.name, instance)) =>
                {
                    for expected in &block.types {
                        self.tick()?;
                        if !matches!(self.environment.find(&expected.base.name),
                            Some(ConstantInfo::Induct(actual)) if actual == expected)
                        {
                            return Err(unsupported("noncanonical Nat decision family"));
                        }
                    }
                    for expected in &block.ctors {
                        self.tick()?;
                        if !matches!(self.environment.find(&expected.base.name),
                            Some(ConstantInfo::Ctor(actual)) if actual == expected)
                        {
                            return Err(unsupported("noncanonical Nat decision constructor"));
                        }
                    }
                    for expected in &block.recursors {
                        self.tick()?;
                        if !matches!(self.environment.find(&expected.base.name),
                            Some(ConstantInfo::Rec(actual)) if actual == expected)
                        {
                            return Err(unsupported("noncanonical Nat decision recursor"));
                        }
                    }
                    true
                }
                _ => continue,
            };
            if !canonical {
                return Err(unsupported("noncanonical Nat decision definition"));
            }
        }
        Ok(())
    }

    pub(super) fn nat_equality_decision(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: callee,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if callee != &name("decide") || !levels.is_empty() || arguments.len() != 2 {
            return Ok(None);
        }

        // The first argument is an admitted proposition, hence static. Keep
        // every runtime initializer inside the decision in its original order.
        // No initializer is substituted, duplicated, or dropped.
        let mut decision = arguments[1].clone();
        let mut bindings = Vec::new();
        loop {
            self.tick()?;
            match decision.node() {
                ExprNode::MData { expr, .. } => {
                    decision = expr.clone();
                    continue;
                }
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value,
                    body,
                    non_dep,
                } => {
                    reserve(&mut bindings, self.limits.max_context_depth)?;
                    bindings.push((decl_name.clone(), type_.clone(), value.clone(), *non_dep));
                    decision = body.clone();
                    continue;
                }
                _ => {}
            }
            let (callee, operands) = self.spine(&decision)?;
            if matches!(callee.node(), ExprNode::Lam { .. } | ExprNode::LetE { .. }) {
                let Some(reduced) = self.static_apply(&callee, &operands)? else {
                    return Ok(None);
                };
                decision = reduced;
                continue;
            }
            let ExprNode::Const {
                name: callee,
                levels,
            } = callee.node()
            else {
                return Ok(None);
            };
            let instance = callee == &name("instDecidableEqNat");
            if (!instance && callee != &name("Nat.decEq"))
                || !levels.is_empty()
                || operands.len() != 2
            {
                return Ok(None);
            }
            self.checked_nat_decision_contract(instance)?;
            let mut result = operands
                .into_iter()
                .fold(Expr::const_(name("Nat.beq"), vec![]), Expr::app);
            for (name, type_, value, nondep) in bindings.into_iter().rev() {
                self.tick()?;
                result = Expr::let_e(name, type_, value, result, nondep);
            }
            return Ok(Some(result));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::level::Level;

    fn constant(spelling: &str) -> Expr {
        Expr::const_(name(spelling), vec![])
    }

    fn apply(spelling: &str, operands: impl IntoIterator<Item = Expr>) -> Expr {
        operands.into_iter().fold(constant(spelling), Expr::app)
    }

    // Deliberately install unchecked metadata here to exercise the authority
    // guard itself. Public source ingress still requires both checking engines.
    fn environment(replaced: &str) -> Environment {
        let mut environment = Environment::new();
        for declaration in fln_elab::seed::source_seed_declarations() {
            match declaration {
                Declaration::Axiom(mut value) if required_decision_name(&value.base.name, true) => {
                    if value.base.name == name(replaced) {
                        value.is_unsafe = !value.is_unsafe;
                    }
                    environment = environment.add_decl(ConstantInfo::Axiom(value)).unwrap();
                }
                Declaration::Defn(mut value) if required_decision_name(&value.base.name, true) => {
                    if value.base.name == name(replaced) {
                        value.value = constant("Bool.false");
                    }
                    environment = environment.add_decl(ConstantInfo::Defn(value)).unwrap();
                }
                Declaration::Inductive(block)
                    if block
                        .types
                        .iter()
                        .any(|family| required_decision_name(&family.base.name, true)) =>
                {
                    for mut value in block.types {
                        if value.base.name == name(replaced) {
                            value.num_indices += 1;
                        }
                        environment = environment.add_decl(ConstantInfo::Induct(value)).unwrap();
                    }
                    for mut value in block.ctors {
                        if value.base.name == name(replaced) {
                            value.num_fields += 1;
                        }
                        environment = environment.add_decl(ConstantInfo::Ctor(value)).unwrap();
                    }
                    for mut value in block.recursors {
                        if value.base.name == name(replaced) {
                            value.num_minors += 1;
                        }
                        environment = environment.add_decl(ConstantInfo::Rec(value)).unwrap();
                    }
                }
                _ => {}
            }
        }
        environment
    }

    fn decide_args(decision: Expr) -> [Expr; 2] {
        // The proposition is static and has already been checked. Its exact
        // syntax may be altered by earlier proof/type erasure.
        [constant("Bool.false"), decision]
    }

    #[test]
    fn nat_decision_requires_definitions_and_every_canonical_family_dependency() {
        let decision = apply("instDecidableEqNat", [nat::literal(3), nat::literal(4)]);
        for replaced in [
            "decide",
            "Nat.decEq",
            "instDecidableEqNat",
            "Nat.beq",
            "Nat",
            "Nat.succ",
            "Nat.rec",
            "Bool",
            "Bool.true",
            "Bool.rec",
            "Eq",
            "Eq.refl",
            "Eq.rec",
            "Decidable",
            "Decidable.isTrue",
            "Decidable.rec",
            "False",
            "True",
            "Not",
        ] {
            let environment = environment(replaced);
            assert!(
                Preparation::new(&environment, IngressLimits::default())
                    .nat_equality_decision(&constant("decide"), &decide_args(decision.clone()))
                    .is_err(),
                "replaced dependency {replaced} was accepted"
            );
        }
        let environment = environment("");
        for callee in ["Nat.decEq", "instDecidableEqNat"] {
            let actual = Preparation::new(&environment, IngressLimits::default())
                .nat_equality_decision(
                    &constant("decide"),
                    &decide_args(apply(callee, [nat::literal(3), nat::literal(4)])),
                )
                .unwrap();
            assert_eq!(
                actual,
                Some(apply("Nat.beq", [nat::literal(3), nat::literal(4)]))
            );
        }
    }

    #[test]
    fn decision_lambda_wrappers_keep_strict_operands_once_and_in_scope() {
        let environment = environment("");
        let variable = |index| Expr::bvar(index).unwrap();
        let lambda = Expr::lam(
            name("a"),
            constant("Nat"),
            Expr::lam(
                name("b"),
                constant("Nat"),
                apply("Nat.decEq", [variable(1), variable(0)]),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let left = apply("Nat.add", [variable(0), nat::literal(3)]);
        let right = apply("Nat.add", [variable(1), nat::literal(4)]);
        let decision = Expr::app(Expr::app(lambda, left.clone()), right);
        let actual = Preparation::new(&environment, IngressLimits::default())
            .nat_equality_decision(&constant("decide"), &decide_args(decision))
            .unwrap();
        let expected = Expr::let_e(
            name("a"),
            constant("Nat"),
            left,
            Expr::let_e(
                name("b"),
                constant("Nat"),
                apply("Nat.add", [variable(2), nat::literal(4)]),
                apply("Nat.beq", [variable(1), variable(0)]),
                false,
            ),
            false,
        );
        assert_eq!(actual, Some(expected));
    }

    #[test]
    fn unrelated_decisions_remain_ordinary_source_and_budget_stops_are_typed() {
        let environment = environment("");
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        assert_eq!(
            preparation
                .nat_equality_decision(
                    &constant("decide"),
                    &decide_args(constant("instDecidableTrue")),
                )
                .unwrap(),
            None
        );
        assert_eq!(
            preparation
                .nat_equality_decision(
                    &constant("decide"),
                    &decide_args(Expr::app(
                        Expr::app(
                            Expr::const_(name("Nat.decEq"), vec![Level::one()]),
                            nat::literal(0),
                        ),
                        nat::literal(0),
                    )),
                )
                .unwrap(),
            None
        );
        let limits = IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        };
        assert!(matches!(
            Preparation::new(&environment, limits).nat_equality_decision(
                &constant("decide"),
                &decide_args(apply("Nat.decEq", [nat::literal(0), nat::literal(0)])),
            ),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                ..
            })
        ));
    }
}
