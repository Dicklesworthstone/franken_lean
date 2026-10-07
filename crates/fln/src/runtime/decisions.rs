//! Runtime representations for admitted constructive decisions.
//!
//! Decidable has a uniform constructor layout independent of its proposition;
//! the proposition and proof fields are static/erased, but its chosen tag is
//! computed normally. Nat and Bool equality retain their checked fast paths.
//! Both transformations check the admitted contracts; a familiar name alone
//! never authorizes erasure. The logical declarations remain unchanged.

use super::*;

fn required_decision_name(candidate: &Name, carrier: &str, instance: bool) -> bool {
    ["Bool", "Eq", "Decidable", "False", "True", "Not", "decide"]
        .into_iter()
        .any(|expected| candidate == &name(expected))
        || candidate == &name(carrier)
        || candidate == &name(&format!("{carrier}.decEq"))
        || carrier == "Nat" && candidate == &name("Nat.beq")
        || instance && candidate == &name(&format!("instDecidableEq{carrier}"))
}

/// `Not` is a static proof-field alias. The pinned Prelude and source seed
/// have the same `fun p : Prop => p -> False` body, but use different binder
/// names and unfolding hints. Neither changes this erased representation.
/// Keep the type, value, universes, safety and mutual group bound to the
/// canonical declaration; a same-named foreign alias still cannot qualify.
fn canonical_decision_proof_alias(actual: Option<&ConstantInfo>, expected: &DefinitionVal) -> bool {
    matches!(actual, Some(ConstantInfo::Defn(actual))
        if actual.base.name == expected.base.name
            && actual.base.level_params == expected.base.level_params
            && crate::olean_imports::expr_eqv(&actual.base.type_, &expected.base.type_)
            && crate::olean_imports::expr_eqv(&actual.value, &expected.value)
            && actual.safety == expected.safety
            && actual.all == expected.all)
}

impl Preparation<'_> {
    /// Proposition arguments do not affect Decidable's runtime layout: both
    /// constructors retain their tag and one erased proof slot. Choose a closed
    /// representative only AFTER admission, in the compiler's type plane. The
    /// original proposition, proof and decision are never changed in the logical
    /// environment. In particular, do not evaluate the decision to choose a tag.
    pub(super) fn decision_representation(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if !matches!(head.node(), ExprNode::Const { name: n, levels }
            if n == &name("Decidable") && levels.is_empty())
            || arguments.len() != 1
        {
            return Ok(None);
        }
        if !self.specializations.decision_family_checked {
            // Recognition includes the proof-field aliases and the closed
            // representative. A same-named foreign family cannot acquire this
            // erasure, and a failed check never fills the cached guard.
            for expected in fln_elab::seed::source_seed_declarations() {
                self.tick()?;
                match expected {
                    Declaration::Inductive(block)
                        if block.types.iter().any(|family| {
                            ["Decidable", "True", "False"]
                                .iter()
                                .any(|label| family.base.name == name(label))
                        }) =>
                    {
                        for expected in &block.types {
                            self.tick()?;
                            if self.environment.find(&expected.base.name)
                                != Some(&ConstantInfo::Induct(expected.clone()))
                            {
                                return Err(unsupported("noncanonical decision family"));
                            }
                        }
                        for expected in &block.ctors {
                            self.tick()?;
                            if self.environment.find(&expected.base.name)
                                != Some(&ConstantInfo::Ctor(expected.clone()))
                            {
                                return Err(unsupported("noncanonical decision constructor"));
                            }
                        }
                        for expected in &block.recursors {
                            self.tick()?;
                            if self.environment.find(&expected.base.name)
                                != Some(&ConstantInfo::Rec(expected.clone()))
                            {
                                return Err(unsupported("noncanonical decision recursor"));
                            }
                        }
                    }
                    Declaration::Defn(expected)
                        if expected.base.name == name("Not")
                            && !canonical_decision_proof_alias(
                                self.environment.find(&expected.base.name),
                                &expected,
                            ) =>
                    {
                        return Err(unsupported("noncanonical decision proof field"));
                    }
                    _ => {}
                }
            }
            if source_scalar_constructor_binding(self.environment, &name("Bool.false")).is_none() {
                return Err(unsupported("decision proof erasure unavailable"));
            }
            self.specializations.decision_family_checked = true;
        }
        Ok(Some(Expr::app(
            head.clone(),
            Expr::const_(name("True"), vec![]),
        )))
    }

    fn checked_equality_decision_contract(
        &mut self,
        carrier: &str,
        instance: bool,
    ) -> Result<(), IngressError> {
        // Use the same candidates admitted by the source seed. Checking only
        // the instance wrapper would miss a replaced carrier decEq dependency;
        // checking only decEq would miss changed eliminator rules.
        for expected in fln_elab::seed::source_seed_declarations() {
            self.tick()?;
            let canonical = match expected {
                Declaration::Axiom(expected)
                    if required_decision_name(&expected.base.name, carrier, instance) =>
                {
                    matches!(self.environment.find(&expected.base.name),
                        Some(ConstantInfo::Axiom(actual)) if actual == &expected)
                }
                Declaration::Defn(expected)
                    if required_decision_name(&expected.base.name, carrier, instance) =>
                {
                    if expected.base.name == name("Not") {
                        canonical_decision_proof_alias(
                            self.environment.find(&expected.base.name),
                            &expected,
                        )
                    } else {
                        matches!(self.environment.find(&expected.base.name),
                            Some(ConstantInfo::Defn(actual)) if actual == &expected)
                    }
                }
                Declaration::Inductive(block)
                    if block.types.iter().any(|family| {
                        required_decision_name(&family.base.name, carrier, instance)
                    }) =>
                {
                    for expected in &block.types {
                        self.tick()?;
                        if !matches!(self.environment.find(&expected.base.name),
                            Some(ConstantInfo::Induct(actual)) if actual == expected)
                        {
                            return Err(unsupported("noncanonical equality decision family"));
                        }
                    }
                    for expected in &block.ctors {
                        self.tick()?;
                        if !matches!(self.environment.find(&expected.base.name),
                            Some(ConstantInfo::Ctor(actual)) if actual == expected)
                        {
                            return Err(unsupported("noncanonical equality decision constructor"));
                        }
                    }
                    for expected in &block.recursors {
                        self.tick()?;
                        if !matches!(self.environment.find(&expected.base.name),
                            Some(ConstantInfo::Rec(actual)) if actual == expected)
                        {
                            return Err(unsupported("noncanonical equality decision recursor"));
                        }
                    }
                    true
                }
                _ => continue,
            };
            if !canonical {
                return Err(unsupported("noncanonical equality decision definition"));
            }
        }
        Ok(())
    }

    fn bool_equality_value(&mut self, left: Expr, right: Expr) -> Result<Expr, IngressError> {
        let bool_type = Expr::const_(name("Bool"), vec![]);
        let motive = Expr::lam(
            Name::anonymous(),
            bool_type.clone(),
            self.lift(&bool_type, 1)?,
            BinderInfo::Default,
        );
        let right_value = Expr::bvar(0).map_err(|_| unsupported("Boolean equality scope"))?;
        let left_value = Expr::bvar(1).map_err(|_| unsupported("Boolean equality scope"))?;
        let negated_right = [
            motive.clone(),
            Expr::const_(name("Bool.true"), vec![]),
            Expr::const_(name("Bool.false"), vec![]),
            right_value.clone(),
        ]
        .into_iter()
        .fold(
            Expr::const_(name("Bool.rec"), vec![fln_core::level::Level::one()]),
            Expr::app,
        );
        let equality = [motive, negated_right, right_value, left_value]
            .into_iter()
            .fold(
                Expr::const_(name("Bool.rec"), vec![fln_core::level::Level::one()]),
                Expr::app,
            );
        Ok(Expr::let_e(
            Name::anonymous(),
            bool_type.clone(),
            left,
            Expr::let_e(
                Name::anonymous(),
                bool_type,
                self.lift(&right, 1)?,
                equality,
                false,
            ),
            false,
        ))
    }

    pub(super) fn nat_equality_decision(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        self.equality_decision(head, arguments)
    }

    fn equality_decision(
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
            let (carrier, instance) = if callee == &name("Nat.decEq") {
                ("Nat", false)
            } else if callee == &name("instDecidableEqNat") {
                ("Nat", true)
            } else if callee == &name("Bool.decEq") {
                ("Bool", false)
            } else if callee == &name("instDecidableEqBool") {
                ("Bool", true)
            } else {
                return Ok(None);
            };
            if !levels.is_empty() || operands.len() != 2 {
                return Ok(None);
            }
            self.checked_equality_decision_contract(carrier, instance)?;
            let mut result = if carrier == "Nat" {
                operands
                    .into_iter()
                    .fold(Expr::const_(name("Nat.beq"), vec![]), Expr::app)
            } else {
                self.bool_equality_value(operands[0].clone(), operands[1].clone())?
            };
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

    #[test]
    fn decision_layout_does_not_depend_on_or_evaluate_the_proposition() {
        let env = environment("Nat", "");
        let mut prep = Preparation::new(&env, IngressLimits::default());
        let representative = apply("Decidable", [constant("True")]);
        for proposition in [
            constant("True"),
            constant("False"),
            Expr::bvar(0).unwrap(),
            apply("unevaluatedProposition", [nat::literal(17)]),
        ] {
            assert_eq!(
                prep.decision_representation(&constant("Decidable"), &[proposition])
                    .unwrap(),
                Some(representative.clone())
            );
        }
        assert!(prep.specializations.decision_family_checked);
        assert_eq!(
            prep.value_type(&apply("Decidable", [Expr::bvar(0).unwrap()]))
                .unwrap(),
            Some(ValueType::Constructor)
        );
    }

    #[test]
    fn decision_layout_refuses_replaced_authority_and_cannot_cache_a_failed_check() {
        for replaced in [
            "Decidable",
            "Decidable.isTrue",
            "Decidable.isFalse",
            "Decidable.rec",
            "True",
            "True.intro",
            "False",
            "Not",
            "Bool.false",
        ] {
            let env = environment("Nat", replaced);
            let mut prep = Preparation::new(&env, IngressLimits::default());
            for _ in 0..2 {
                assert!(
                    prep.decision_representation(&constant("Decidable"), &[constant("True")])
                        .is_err(),
                    "{replaced}"
                );
                assert!(!prep.specializations.decision_family_checked);
            }
            assert!(prep.constructors.is_empty());
        }
    }

    #[test]
    fn proof_alias_accepts_pinned_binder_and_hint_variations_but_not_other_changes() {
        let seed = environment("Nat", "");
        let ConstantInfo::Defn(expected) = seed.find(&name("Not")).unwrap() else {
            panic!("the canonical proof alias is a definition");
        };
        let prop = Expr::sort(Level::zero());
        let mut imported = expected.clone();
        imported.base.type_ =
            Expr::forall_e(name("a"), prop.clone(), prop.clone(), BinderInfo::Default);
        imported.value = Expr::lam(
            name("a"),
            prop.clone(),
            Expr::forall_e(
                name("a._@._internal._hyg.0"),
                Expr::bvar(0).unwrap(),
                constant("False"),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        imported.hints = fln_env::constants::ReducibilityHints::Regular(1);
        assert_ne!(imported, *expected);

        let with_not = |definition: &DefinitionVal| {
            seed.constants()
                .fold(Environment::new(), |environment, (n, info)| {
                    let info = if n == &name("Not") {
                        ConstantInfo::Defn(definition.clone())
                    } else {
                        info.clone()
                    };
                    environment.add_decl(info).unwrap()
                })
        };
        let admitted = with_not(&imported);
        let mut preparation = Preparation::new(&admitted, IngressLimits::default());
        assert_eq!(
            preparation
                .decision_representation(&constant("Decidable"), &[constant("True")])
                .unwrap(),
            Some(apply("Decidable", [constant("True")]))
        );
        assert_eq!(
            preparation
                .equality_decision(
                    &constant("decide"),
                    &decide_args(apply("Nat.decEq", [nat::literal(3), nat::literal(4)])),
                )
                .unwrap(),
            Some(apply("Nat.beq", [nat::literal(3), nat::literal(4)]))
        );
        assert_eq!(
            admitted.find(&name("Not")),
            Some(&ConstantInfo::Defn(imported.clone()))
        );

        let mut wrong_body = imported.clone();
        wrong_body.value = Expr::lam(
            name("a"),
            prop.clone(),
            constant("True"),
            BinderInfo::Default,
        );
        let mut wrong_type = imported.clone();
        wrong_type.base.type_ = Expr::forall_e(
            name("a"),
            Expr::sort(Level::one()),
            prop,
            BinderInfo::Default,
        );
        let mut wrong_levels = imported.clone();
        wrong_levels.base.level_params.push(name("u"));
        let mut unsafe_alias = imported.clone();
        unsafe_alias.safety = fln_env::constants::DefinitionSafety::Unsafe;
        let mut wrong_group = imported;
        wrong_group.all.push(name("other"));
        for altered in [
            wrong_body,
            wrong_type,
            wrong_levels,
            unsafe_alias,
            wrong_group,
        ] {
            let environment = with_not(&altered);
            let mut preparation = Preparation::new(&environment, IngressLimits::default());
            assert!(
                preparation
                    .decision_representation(&constant("Decidable"), &[constant("True")])
                    .is_err()
            );
            assert!(!preparation.specializations.decision_family_checked);
        }
    }

    #[test]
    fn decision_layout_retains_arity_and_work_limits() {
        let env = environment("Nat", "");
        let mut prep = Preparation::new(&env, IngressLimits::default());
        for (head, args) in [
            (constant("Decidable"), vec![]),
            (
                constant("Decidable"),
                vec![constant("True"), constant("False")],
            ),
            (
                Expr::const_(name("Decidable"), vec![Level::zero()]),
                vec![constant("True")],
            ),
            (constant("userDecision"), vec![constant("True")]),
        ] {
            assert_eq!(prep.decision_representation(&head, &args).unwrap(), None);
        }
        assert!(!prep.specializations.decision_family_checked);
        let mut prep = Preparation::new(
            &env,
            IngressLimits {
                max_nodes: 1,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            prep.decision_representation(&constant("Decidable"), &[constant("True")]),
            Err(IngressError::ResourceLimit { .. })
        ));
        assert!(!prep.specializations.decision_family_checked);
    }

    // Deliberately install unchecked metadata here to exercise the authority
    // guard itself. Public source ingress still requires both checking engines.
    fn environment(carrier: &str, replaced: &str) -> Environment {
        let mut environment = Environment::new();
        for declaration in fln_elab::seed::source_seed_declarations() {
            match declaration {
                Declaration::Axiom(mut value)
                    if required_decision_name(&value.base.name, carrier, true) =>
                {
                    if value.base.name == name(replaced) {
                        value.is_unsafe = !value.is_unsafe;
                    }
                    environment = environment.add_decl(ConstantInfo::Axiom(value)).unwrap();
                }
                Declaration::Defn(mut value)
                    if required_decision_name(&value.base.name, carrier, true) =>
                {
                    if value.base.name == name(replaced) {
                        value.value = constant("Bool.false");
                    }
                    environment = environment.add_decl(ConstantInfo::Defn(value)).unwrap();
                }
                Declaration::Inductive(block)
                    if block
                        .types
                        .iter()
                        .any(|family| required_decision_name(&family.base.name, carrier, true)) =>
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
            let environment = environment("Nat", replaced);
            assert!(
                Preparation::new(&environment, IngressLimits::default())
                    .equality_decision(&constant("decide"), &decide_args(decision.clone()))
                    .is_err(),
                "replaced dependency {replaced} was accepted"
            );
        }
        let environment = environment("Nat", "");
        for callee in ["Nat.decEq", "instDecidableEqNat"] {
            let actual = Preparation::new(&environment, IngressLimits::default())
                .equality_decision(
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
    fn bool_decision_requires_the_canonical_bool_equality_contract() {
        let decision = apply(
            "instDecidableEqBool",
            [constant("Bool.true"), constant("Bool.false")],
        );
        for replaced in [
            "decide",
            "Bool.decEq",
            "instDecidableEqBool",
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
            let environment = environment("Bool", replaced);
            assert!(
                Preparation::new(&environment, IngressLimits::default())
                    .equality_decision(&constant("decide"), &decide_args(decision.clone()))
                    .is_err(),
                "replaced dependency {replaced} was accepted"
            );
        }
        let environment = environment("Bool", "");
        for callee in ["Bool.decEq", "instDecidableEqBool"] {
            let actual = Preparation::new(&environment, IngressLimits::default())
                .equality_decision(
                    &constant("decide"),
                    &decide_args(apply(
                        callee,
                        [constant("Bool.true"), constant("Bool.false")],
                    )),
                )
                .unwrap()
                .expect("canonical Boolean equality lowers");
            let ExprNode::LetE {
                type_, value, body, ..
            } = actual.node()
            else {
                panic!("left Boolean operand must be strict");
            };
            assert_eq!(*type_, constant("Bool"));
            assert_eq!(*value, constant("Bool.true"));
            let ExprNode::LetE {
                type_, value, body, ..
            } = body.node()
            else {
                panic!("right Boolean operand must be strict");
            };
            assert_eq!(*type_, constant("Bool"));
            assert_eq!(*value, constant("Bool.false"));
            assert!(matches!(body.node(), ExprNode::App { .. }));
        }
    }

    #[test]
    fn decision_lambda_wrappers_keep_strict_operands_once_and_in_scope() {
        let environment = environment("Nat", "");
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
            .equality_decision(&constant("decide"), &decide_args(decision))
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
        let environment = environment("Nat", "");
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        assert_eq!(
            preparation
                .equality_decision(
                    &constant("decide"),
                    &decide_args(constant("instDecidableTrue")),
                )
                .unwrap(),
            None
        );
        assert_eq!(
            preparation
                .equality_decision(
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
            Preparation::new(&environment, limits).equality_decision(
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
