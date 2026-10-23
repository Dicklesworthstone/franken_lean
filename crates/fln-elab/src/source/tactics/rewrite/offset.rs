//! Automatic Nat offset closure, without unfolding arbitrary arithmetic operands.
//!
//! Offset.lean at the pin distinguishes `isOffset?` (instance conversion is
//! permitted) from `evalNat` (structural instance tests and no delta). Keep that
//! distinction while recognizing a bounded fragment. Recognition is not a proof:
//! once bases are numeric or agree at reducible transparency, the existing
//! scoped, metered kernel conversion must establish the ORIGINAL equation. Ordinary definitions
//! and hidden multiplication operands cannot become new automatic simp rules.
use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Operation {
    Zero,
    Numeral,
    Succ,
    Add,
    Other,
}

struct OffsetBase {
    base: Expr,
    numeric: bool,
    offset: bool,
}

fn primitive(name: &Name) -> Option<(&'static str, Operation)> {
    for (family, field, raw, kind) in [
        ("Nat", "zero", "zero", Operation::Zero),
        ("Nat", "succ", "succ", Operation::Succ),
        ("Nat", "add", "add", Operation::Add),
        ("Nat", "sub", "sub", Operation::Other),
        ("Nat", "mul", "mul", Operation::Other),
        ("Nat", "div", "div", Operation::Other),
        ("Nat", "mod", "mod", Operation::Other),
        ("OfNat", "ofNat", "ofNat", Operation::Numeral),
        ("Add", "add", "add", Operation::Add),
        ("HAdd", "hAdd", "add", Operation::Add),
        ("Sub", "sub", "sub", Operation::Other),
        ("HSub", "hSub", "sub", Operation::Other),
        ("Mul", "mul", "mul", Operation::Other),
        ("HMul", "hMul", "mul", Operation::Other),
        ("Div", "div", "div", Operation::Other),
        ("HDiv", "hDiv", "div", Operation::Other),
        ("Mod", "mod", "mod", Operation::Other),
        ("HMod", "hMod", "mod", Operation::Other),
    ] {
        if name == &Name::from_components([family, field]) {
            return Some((raw, kind));
        }
    }
    None
}

impl Context {
    /// Additional Eq-only completion, never a change to ordinary unification or
    /// HEq closure. There must be an actual offset on at least one endpoint.
    pub(super) fn automatic_nat_offset_reflexivity(
        &mut self,
        alpha: &Expr,
        left: &Expr,
        right: &Expr,
        zeta_delta: bool,
    ) -> Result<bool, NatDefinitionElabError> {
        let alpha = self.instantiate(alpha)?;
        let left = self.instantiate(left)?;
        let right = self.instantiate(right)?;
        if [&alpha, &left, &right]
            .iter()
            .any(|e| e.has_expr_mvar() || e.has_level_mvar() || e.has_loose_bvars())
        {
            return Ok(false);
        }
        let mut budget = UnificationBudget::new(self.kernel);
        budget.zeta_delta = zeta_delta;
        budget.max_assignments = 0;
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        if !self.proof_types_match_with_budget(&alpha, &nat, budget)? {
            return Ok(false);
        }
        let lhs = self.automatic_offset_base(&left, zeta_delta)?;
        let rhs = self.automatic_offset_base(&right, zeta_delta)?;
        if !lhs.offset && !rhs.offset {
            return Ok(false);
        }
        // An offset against a term that is neither an offset nor a numeral is undecided at the
        // pin (`Lean/Meta/Offset.lean:136-139`), so reducible conversion alone decides it: `n + 0`
        // is not `n` there, `Nat.add` being only implicit-reducible.
        if lhs.offset != rhs.offset && !lhs.numeric && !rhs.numeric {
            return Ok(false);
        }
        if !(lhs.numeric && rhs.numeric)
            && (lhs.numeric != rhs.numeric
                || !self.proof_types_match_with_budget(&lhs.base, &rhs.base, budget)?)
        {
            return Ok(false);
        }
        // This existing conversion closes the actual local telescope, checks
        // universe parameters, respects irreducible definitions and charges K1
        // work. No residual, guessed result, or new declaration is created.
        self.coercion_kernel_eq(left, right)
    }

    fn automatic_offset_base(
        &mut self,
        expression: &Expr,
        zeta_delta: bool,
    ) -> Result<OffsetBase, NatDefinitionElabError> {
        let mut base = expression.clone();
        let mut offset = false;
        loop {
            base = self.automatic_arithmetic_head(&base, zeta_delta)?;
            let Some((operation, operands)) = self.automatic_arithmetic_operation(&base, false)?
            else {
                break;
            };
            if operation == Operation::Succ
                || (operation == Operation::Add
                    && self.automatic_literal_arithmetic(&operands[1])?)
            {
                base = operands[0].clone();
            } else {
                break;
            }
            offset = true;
        }
        let numeric = self.automatic_literal_arithmetic(&base)?;
        Ok(OffsetBase {
            base,
            numeric,
            offset,
        })
    }

    /// Only a comparison's exposed head may delta-reduce. Stop BEFORE unfolding
    /// the class operators: source WHNF would otherwise leave a projection on
    /// an implicit-reducible dictionary, hiding Offset.lean's source shape.
    fn automatic_arithmetic_head(
        &mut self,
        expression: &Expr,
        zeta_delta: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut head = expression.clone();
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::LetE { value, body, .. } => head = self.substitute(body, value)?,
                ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                    head = self.substitute(body, &arguments.pop().expect("nonempty spine"))?;
                }
                ExprNode::FVar { id } if zeta_delta => {
                    let Some(value) = self.txn.lctx.find(id).and_then(|l| l.value.clone()) else {
                        break;
                    };
                    head = value;
                }
                ExprNode::Const { name, levels } if primitive(name).is_none() => {
                    let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned()
                    else {
                        break;
                    };
                    let status = crate::reducibility::table(&self.txn.env)
                        .map_err(|e| {
                            failure(SourceInferenceError::Unification(Box::new(
                                UnificationError::Reducibility(e),
                            )))
                        })?
                        .get(name);
                    if definition.safety != DefinitionSafety::Safe
                        || !status.map_or(definition.hints == ReducibilityHints::Abbrev, |s| {
                            s == crate::reducibility::Reducibility::Reducible
                        })
                    {
                        break;
                    }
                    head = self.instantiate_params(
                        &definition.value,
                        &definition.base.level_params,
                        levels,
                    )?;
                }
                _ => break,
            }
        }
        for argument in arguments.into_iter().rev() {
            self.tick()?;
            head = Expr::app(head, argument);
        }
        Ok(head)
    }

    /// Return source-order operands. Strict mode implements evalNat's
    /// structural dictionary test; only an offset's Add dictionary may convert.
    fn automatic_arithmetic_operation(
        &mut self,
        expression: &Expr,
        strict: bool,
    ) -> Result<Option<(Operation, Vec<Expr>)>, NatDefinitionElabError> {
        let mut head = expression;
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f;
                }
                ExprNode::MData { expr, .. } => head = expr,
                _ => break,
            }
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some((raw, operation)) = primitive(name) else {
            return Ok(None);
        };
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        let Some(info) = self.txn.env.find(name) else {
            return Ok(None);
        };
        if levels.len() != info.constant_val().level_params.len() {
            return Ok(None);
        }
        let constant = |s| Expr::const_(Name::from_components([s]), vec![]);
        if name.parent() == Name::from_components(["Nat"]) {
            let arity = match operation {
                Operation::Zero => 0,
                Operation::Succ => 1,
                _ => 2,
            };
            if !levels.is_empty() || arguments.len() != arity {
                return Ok(None);
            }
            if matches!(operation, Operation::Zero | Operation::Succ) {
                if !matches!(info, ConstantInfo::Ctor(ctor)
                    if !ctor.is_unsafe
                        && ctor.induct == Name::from_components(["Nat"])
                        && ctor.num_params == 0 && ctor.num_fields as usize == arity)
                {
                    return Ok(None);
                }
            } else if !self.exact_nat_intrinsic(name) {
                return Ok(None);
            }
            arguments.reverse();
            return Ok(Some((operation, arguments)));
        }
        let (dictionary, expected, operands) = if operation == Operation::Numeral {
            if arguments.len() != 3 || arguments[2] != nat {
                return Ok(None);
            }
            (
                arguments[0].clone(),
                Expr::app(constant("instOfNatNat"), arguments[1].clone()),
                vec![arguments[1].clone()],
            )
        } else {
            let (instance, bridge) = match raw {
                "add" => (constant("instAddNat"), "instHAdd"),
                "sub" => (constant("instSubNat"), "instHSub"),
                "mul" => (constant("instMulNat"), "instHMul"),
                "div" => (
                    Expr::const_(Name::from_components(["Nat", "instDiv"]), vec![]),
                    "instHDiv",
                ),
                "mod" => (
                    Expr::const_(Name::from_components(["Nat", "instMod"]), vec![]),
                    "instHMod",
                ),
                _ => return Ok(None),
            };
            let heterogeneous = ["HAdd", "HSub", "HMul", "HDiv", "HMod"]
                .iter()
                .any(|family| name.parent() == Name::from_components([*family]));
            let expected = if heterogeneous
                && arguments.len() == 6
                && arguments[3..].iter().all(|a| a == &nat)
            {
                app(
                    Expr::const_(Name::from_components([bridge]), vec![Level::zero()]),
                    [nat, instance],
                )
            } else if !heterogeneous && arguments.len() == 4 && arguments[3] == nat {
                instance
            } else {
                return Ok(None);
            };
            (
                arguments[2].clone(),
                expected,
                vec![arguments[1].clone(), arguments[0].clone()],
            )
        };
        if dictionary.has_expr_mvar() || dictionary.has_level_mvar() {
            return Ok(None);
        }
        let valid = if strict || operation != Operation::Add {
            self.rewrite_same(&dictionary, &expected)?
        } else {
            let mut budget = UnificationBudget::new(self.kernel);
            budget.transparency = UnificationTransparency::Instances;
            budget.zeta_delta = false;
            budget.max_assignments = 0;
            self.proof_types_match_with_budget(&dictionary, &expected, budget)?
        };
        Ok(valid.then_some((operation, operands)))
    }

    /// A heap/DAG walk over closed arithmetic syntax, not a normalizer. In
    /// particular an abbreviation inside a multiplication operand is NOT read.
    fn automatic_literal_arithmetic(
        &mut self,
        expression: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        if expression.has_fvar()
            || expression.has_expr_mvar()
            || expression.has_level_mvar()
            || expression.has_loose_bvars()
        {
            return Ok(false);
        }
        let mut pending = vec![expression.clone()];
        let mut seen = HashMap::new();
        while let Some(term) = pending.pop() {
            self.tick()?;
            if seen.contains_key(&term.allocation_identity()) {
                continue;
            }
            match term.node() {
                ExprNode::Lit {
                    literal: Literal::Nat(_),
                } => {}
                ExprNode::MData { expr, .. } => pending.push(expr.clone()),
                _ => {
                    let Some((_, operands)) = self.automatic_arithmetic_operation(&term, true)?
                    else {
                        return Ok(false);
                    };
                    pending.extend(operands);
                }
            }
            seen.insert(term.allocation_identity(), term);
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::NatLit;
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};

    fn context() -> Context {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let mut env = Environment::new();
        for declaration in crate::seed::source_seed_declarations_iter() {
            let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
                panic!("seed check did not complete");
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("seed check refused");
            };
            env = match checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) {
                Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
                    p.environment
                }
                Outcome::Complete(Published::BlockCommitted(p)) => p.environment,
                other => panic!("seed publication: {other:?}"),
            };
        }
        Context::new(&env, budget)
    }
    fn constant(parts: &[&str]) -> Expr {
        Expr::const_(Name::from_components(parts.iter().copied()), vec![])
    }
    fn number(n: u64) -> Expr {
        Expr::lit(Literal::Nat(NatLit::from_u64(n)))
    }
    fn plus(a: Expr, b: Expr) -> Expr {
        app(constant(&["Nat", "add"]), [a, b])
    }

    #[test]
    fn literal_eligibility_walks_shared_dags_and_obeys_work_stops() {
        let mut context = context();
        let mut expression = number(1);
        for _ in 0..64 {
            expression = plus(expression.clone(), expression);
        }
        let before = context.txn.clone();
        assert!(context.automatic_literal_arithmetic(&expression).unwrap());
        let work = context.txn.budget.heartbeats_consumed - before.budget.heartbeats_consumed;
        assert!(
            work < 2000,
            "shared nodes, not exponentially many paths: {work}"
        );
        assert_eq!(context.txn.env, before.env);
        assert_eq!(context.txn.mvars, before.mvars);
        let mut stopped = context.clone();
        stopped.txn.budget.max_heartbeats = stopped.txn.budget.heartbeats_consumed + 8;
        assert!(stopped.automatic_literal_arithmetic(&expression).is_err());
        assert_eq!(stopped.txn.mvars, before.mvars);
        assert_eq!(stopped.txn.universes, before.universes);
        assert!(context.automatic_literal_arithmetic(&expression).unwrap());
    }

    #[test]
    fn exposed_head_uses_heap_frames_and_keeps_local_let_policy() {
        let mut context = context();
        let id = FVarId(Name::from_components(["bound"]));
        context
            .txn
            .lctx
            .add_let(id.clone(), id.0.clone(), constant(&["Nat"]), number(2));
        let local = Expr::fvar(id);
        assert!(
            context
                .rewrite_same(
                    &context
                        .clone()
                        .automatic_arithmetic_head(&local, false)
                        .unwrap(),
                    &local
                )
                .unwrap()
        );
        assert!(
            context
                .rewrite_same(
                    &context
                        .clone()
                        .automatic_arithmetic_head(&local, true)
                        .unwrap(),
                    &number(2)
                )
                .unwrap()
        );
        let identity = Expr::lam(
            Name::anonymous(),
            constant(&["Nat"]),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        );
        let mut input = number(7);
        for _ in 0..2048 {
            input = Expr::app(identity.clone(), input);
        }
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(move || {
                let result = context.automatic_arithmetic_head(&input, false).unwrap();
                assert_eq!(result, number(7));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn malformed_arithmetic_and_unknown_dictionaries_do_not_license_offsets() {
        let mut context = context();
        let nat = constant(&["Nat"]);
        let dict = Expr::mvar(MVarId(Name::from_components(["dictionary"])));
        let class = Expr::const_(
            Name::from_components(["HAdd", "hAdd"]),
            vec![Level::zero(); 3],
        );
        let unknown = app(
            class.clone(),
            [
                nat.clone(),
                nat.clone(),
                nat.clone(),
                dict,
                number(1),
                number(2),
            ],
        );
        for expression in [
            unknown,
            app(
                class,
                [nat.clone(), constant(&["instAddNat"]), number(1), number(2)],
            ),
            app(
                Expr::const_(Name::from_components(["Nat", "add"]), vec![Level::zero()]),
                [number(1), number(2)],
            ),
            Expr::app(plus(number(1), number(2)), number(3)),
        ] {
            assert!(
                context
                    .automatic_arithmetic_operation(&expression, false)
                    .unwrap()
                    .is_none()
            );
        }
        assert!(context.txn.mvars.is_empty());
    }

    #[test]
    fn offset_conversion_checks_the_original_equation_and_charges_kernel_work() {
        let mut context = context();
        let nat = constant(&["Nat"]);
        let id = FVarId(Name::from_components(["x"]));
        context
            .txn
            .lctx
            .add_param(id.clone(), id.0.clone(), nat.clone(), BinderInfo::Default);
        let x = Expr::fvar(id);
        let lhs = plus(plus(x.clone(), number(2)), number(3));
        let rhs = plus(x.clone(), number(5));
        let before = context.txn.clone();
        assert!(
            context
                .automatic_nat_offset_reflexivity(&nat, &lhs, &rhs, false)
                .unwrap()
        );
        assert!(
            !context
                .automatic_nat_offset_reflexivity(&nat, &lhs, &plus(x, number(6)), false)
                .unwrap()
        );
        assert_eq!(context.txn.env, before.env);
        assert_eq!(context.txn.mvars, before.mvars);
        assert_eq!(context.txn.universes, before.universes);
        assert_eq!(context.txn.lctx, before.lctx);
        assert!(context.txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
        for allowance in [1, 4, 16, 64] {
            let mut stopped = context.clone();
            stopped.txn.budget.max_heartbeats = stopped.txn.budget.heartbeats_consumed + allowance;
            assert!(
                stopped
                    .automatic_nat_offset_reflexivity(&nat, &lhs, &rhs, false)
                    .is_err()
            );
            assert_eq!(stopped.txn.mvars, before.mvars);
            assert_eq!(stopped.txn.env, before.env);
        }
    }
}
