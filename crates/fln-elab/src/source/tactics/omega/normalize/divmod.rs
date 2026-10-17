//! Constant-divisor quotient and remainder normalization.
//!
//! A quotient is a shared integer atom with the checked bounds
//! `d * q <= x < d * q + d`. Remainders rewrite to `x - d * q`, so all
//! subsequent reasoning uses the ordinary affine certificate machinery.
//! Only the pin's syntactically ground Nat expressions supply divisors;
//! raw primitives, arbitrary definitions, and algebraic cancellation do not.

use super::*;

#[derive(Default)]
pub(super) struct State {
    ground: HashMap<Expr, Option<BigNat>>,
    quotients: HashSet<Expr>,
    steps: u64,
}

pub(super) enum Expansion {
    Rewrite(Expr, Option<Expr>),
    Quotient,
}

#[derive(Clone, Copy)]
enum Operation {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

#[derive(Clone, Copy)]
enum Division {
    Quotient,
    Remainder,
}

enum GroundWork {
    Visit(Expr),
    Alias(Expr),
    Binary(Expr, Operation),
}

impl Normalization {
    /// This local finite ledger also applies when source heartbeats are unlimited.
    /// Charge before arithmetic or generated expression allocation.
    fn divmod_charge(
        &mut self,
        context: &mut Context,
        amount: usize,
    ) -> Result<(), NatDefinitionElabError> {
        let amount_u64 = u64::try_from(amount).unwrap_or(u64::MAX);
        let observed = self.divmod.steps.saturating_add(amount_u64);
        if observed > self.limits.max_steps {
            return Err(resource(
                OmegaResource::Steps,
                usize::try_from(self.limits.max_steps).unwrap_or(usize::MAX),
                usize::try_from(observed).unwrap_or(usize::MAX),
            ));
        }
        for _ in 0..amount {
            context.tick()?;
        }
        self.divmod.steps = observed;
        Ok(())
    }

    fn remember_ground(
        &mut self,
        expression: Expr,
        value: Option<BigNat>,
    ) -> Result<(), NatDefinitionElabError> {
        if self.divmod.ground.contains_key(&expression) {
            return Ok(());
        }
        if self.divmod.ground.len() >= self.limits.max_rows {
            return Err(resource(
                OmegaResource::Rows,
                self.limits.max_rows,
                self.divmod.ground.len() + 1,
            ));
        }
        let added = value.as_ref().map_or(32, |number| {
            41_usize.saturating_add(8_usize.saturating_mul(number.limbs_le().len()))
        });
        let observed = self.bytes.saturating_add(added);
        if observed > self.limits.max_certificate_bytes {
            return Err(resource(
                OmegaResource::CertificateBytes,
                self.limits.max_certificate_bytes,
                observed,
            ));
        }
        self.divmod
            .ground
            .try_reserve(1)
            .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
        self.bytes = observed;
        self.divmod.ground.insert(expression, value);
        Ok(())
    }

    fn ground_nat(
        &mut self,
        context: &mut Context,
        expression: &Expr,
    ) -> Result<Option<BigNat>, NatDefinitionElabError> {
        let mut work = vec![GroundWork::Visit(expression.clone())];
        let mut values = Vec::new();
        while let Some(task) = work.pop() {
            self.divmod_charge(context, 1)?;
            let retained = work.len().saturating_add(values.len());
            if retained > self.limits.max_rows {
                return Err(resource(
                    OmegaResource::Rows,
                    self.limits.max_rows,
                    retained,
                ));
            }
            match task {
                GroundWork::Visit(expression) => {
                    if let Some(value) = self.divmod.ground.get(&expression) {
                        values.push(value.clone());
                        continue;
                    }
                    // Lean.Expr.nat? recognizes literals and OfNat syntax,
                    // not the definitionally equal Nat.zero/Nat.succ spellings.
                    if !named_constant(&expression, "Nat.zero")
                        && let Some(value) = nat_literal(&expression, self.limits)?
                    {
                        self.remember_ground(expression, Some(value.clone()))?;
                        values.push(Some(value));
                        continue;
                    }
                    if let Some(value) = transparent_value(&expression) {
                        work.push(GroundWork::Alias(expression));
                        work.push(GroundWork::Visit(value));
                    } else if let Some((operation, left, right)) = ground_operation(&expression) {
                        work.push(GroundWork::Binary(expression, operation));
                        work.push(GroundWork::Visit(right));
                        work.push(GroundWork::Visit(left));
                    } else {
                        self.remember_ground(expression, None)?;
                        values.push(None);
                    }
                }
                GroundWork::Alias(expression) => {
                    let value = values
                        .last()
                        .cloned()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    self.remember_ground(expression, value)?;
                }
                GroundWork::Binary(expression, operation) => {
                    let right = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let left = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let result = match (left, right) {
                        (Some(left), Some(right)) => {
                            Some(self.ground_binary(context, &left, &right, operation)?)
                        }
                        _ => None,
                    };
                    self.remember_ground(expression, result.clone())?;
                    values.push(result);
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

    fn ground_binary(
        &mut self,
        context: &mut Context,
        left: &BigNat,
        right: &BigNat,
        operation: Operation,
    ) -> Result<BigNat, NatDefinitionElabError> {
        if matches!(operation, Operation::Pow) {
            return self.ground_power(context, left, right);
        }
        let left_len = left.limbs_le().len();
        let right_len = right.limbs_le().len();
        let linear = left_len.max(right_len).saturating_add(1);
        let cost = if matches!(operation, Operation::Mul | Operation::Div) {
            left_len
                .saturating_add(1)
                .saturating_mul(right_len.saturating_add(1))
                .saturating_mul(16)
                .saturating_add(linear)
        } else {
            linear
        };
        if matches!(operation, Operation::Mul) && !left.is_zero() && !right.is_zero() {
            // The exact product needs at least bits(left)+bits(right)-1 bits.
            // At the boundary its temporary result may use one extra limb;
            // the exact retained width is checked immediately afterward.
            let minimum = left
                .bit_length()
                .saturating_add(right.bit_length())
                .saturating_sub(1);
            self.check_ground_bits(minimum)?;
        }
        self.divmod_charge(context, cost)?;
        let result = match operation {
            Operation::Add => left.add(right),
            Operation::Sub => left.sub(right),
            Operation::Mul => left.mul(right),
            Operation::Div => left.div(right),
            Operation::Pow => unreachable!(),
        };
        self.check_ground_bits(result.bit_length())?;
        Ok(result)
    }

    fn check_ground_bits(&self, bits: u64) -> Result<(), NatDefinitionElabError> {
        let limbs = bits.saturating_add(63) / 64;
        if limbs > self.limits.max_coefficient_limbs as u64 {
            return Err(resource(
                OmegaResource::CoefficientLimbs,
                self.limits.max_coefficient_limbs,
                usize::try_from(limbs).unwrap_or(usize::MAX),
            ));
        }
        Ok(())
    }

    fn ground_power(
        &mut self,
        context: &mut Context,
        base: &BigNat,
        exponent: &BigNat,
    ) -> Result<BigNat, NatDefinitionElabError> {
        self.divmod_charge(context, 1)?;
        if exponent.is_zero() || base == &BigNat::from_u64(1) {
            return Ok(BigNat::from_u64(1));
        }
        if base.is_zero() {
            return Ok(BigNat::zero());
        }
        // A base >= 2 needs at least exponent+1 result bits. Exponents
        // larger than one machine limb cannot fit any permitted result.
        let power = match exponent.limbs_le() {
            [power] => *power,
            _ => {
                return Err(resource(
                    OmegaResource::CoefficientLimbs,
                    self.limits.max_coefficient_limbs,
                    usize::MAX,
                ));
            }
        };
        let minimum = base
            .bit_length()
            .saturating_sub(1)
            .saturating_mul(power)
            .saturating_add(1);
        self.check_ground_bits(minimum)?;
        let mut remaining = power;
        let mut factor = base.clone();
        let mut result = BigNat::from_u64(1);
        while remaining != 0 {
            if remaining & 1 != 0 {
                result = self.ground_binary(context, &result, &factor, Operation::Mul)?;
            }
            remaining >>= 1;
            if remaining != 0 {
                factor = self.ground_binary(context, &factor, &factor, Operation::Mul)?;
            }
        }
        Ok(result)
    }

    pub(super) fn divmod_nat_cast(
        &mut self,
        context: &mut Context,
        argument: &Expr,
    ) -> Result<Option<(Expr, Expr)>, NatDefinitionElabError> {
        let Some((operation, left, right)) = division_expression(argument, "Nat") else {
            return Ok(None);
        };
        let Some(divisor) = self.ground_nat(context, &right)? else {
            return Ok(None);
        };
        self.divmod_charge(context, 64)?;
        let next = standard_division(
            operation,
            apply(constant("Int.ofNat"), [left.clone()]),
            integer(&BigInt::from_sign_magnitude(false, divisor)),
        );
        let evidence = apply(
            constant(match operation {
                Division::Quotient => "Int.natCast_ediv",
                Division::Remainder => "Int.natCast_emod",
            }),
            [left, right],
        );
        Ok(Some((next, evidence)))
    }

    fn integer_divisor(
        &mut self,
        context: &mut Context,
        expression: &Expr,
    ) -> Result<Option<BigNat>, NatDefinitionElabError> {
        let mut expression = expression.clone();
        loop {
            self.divmod_charge(context, 1)?;
            if let Some(argument) = cast_argument(&expression) {
                return self.ground_nat(context, &argument);
            }
            if let Some((head, arguments)) = named_application(&expression)
                && head == Name::from_components(["OfNat", "ofNat"])
                && arguments.len() == 3
                && named_constant(&arguments[0], "Int")
                && standard_numeral_instance(&arguments[2], &arguments[1], "instOfNat")
            {
                return self.ground_nat(context, &arguments[1]);
            }
            if let Some(value) = transparent_value(&expression) {
                expression = value;
            } else {
                return Ok(None);
            }
        }
    }

    pub(super) fn divmod_expansion(
        &mut self,
        context: &mut Context,
        expression: &Expr,
    ) -> Result<Option<Expansion>, NatDefinitionElabError> {
        let Some((operation, left, right)) = division_expression(expression, "Int") else {
            return Ok(None);
        };
        let Some(divisor) = self.integer_divisor(context, &right)? else {
            return Ok(None);
        };
        self.divmod_charge(context, 32)?;
        let divisor_expr = integer(&BigInt::from_sign_magnitude(false, divisor.clone()));
        let canonical = standard_division(operation, left.clone(), divisor_expr.clone());
        if *expression != canonical {
            return Ok(Some(Expansion::Rewrite(canonical, None)));
        }
        if divisor.is_zero() {
            self.divmod_charge(context, 16)?;
            let (next, rule) = match operation {
                Division::Quotient => (integer(&BigInt::zero()), "Int.ediv_zero"),
                Division::Remainder => (left.clone(), "Int.emod_zero"),
            };
            return Ok(Some(Expansion::Rewrite(
                next,
                Some(apply(constant(rule), [left])),
            )));
        }
        match operation {
            Division::Quotient => {
                self.record_quotient(context, expression, &left, &divisor)?;
                Ok(Some(Expansion::Quotient))
            }
            Division::Remainder => {
                self.divmod_charge(context, 64)?;
                let quotient =
                    standard_division(Division::Quotient, left.clone(), divisor_expr.clone());
                let product = apply(constant("Int.mul"), [divisor_expr.clone(), quotient]);
                let next = standard_sub("Int", left.clone(), product);
                let evidence = apply(constant("Int.emod_def"), [left, divisor_expr]);
                Ok(Some(Expansion::Rewrite(next, Some(evidence))))
            }
        }
    }

    fn record_quotient(
        &mut self,
        context: &mut Context,
        quotient: &Expr,
        dividend: &Expr,
        divisor: &BigNat,
    ) -> Result<(), NatDefinitionElabError> {
        if self.divmod.quotients.contains(quotient) {
            return Ok(());
        }
        let rows = self.pending_facts.len().saturating_add(2);
        if rows > self.limits.max_rows {
            return Err(resource(OmegaResource::Rows, self.limits.max_rows, rows));
        }
        self.divmod
            .quotients
            .try_reserve(1)
            .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
        self.pending_facts
            .try_reserve(2)
            .map_err(|_| resource(OmegaResource::Allocation, 0, 2))?;
        self.divmod_charge(context, 192)?;
        // Mark before recording facts: those facts contain this quotient and
        // reification must not enqueue them again.
        self.divmod.quotients.insert(quotient.clone());
        let zero = integer(&BigInt::zero());
        let one = integer(&BigInt::from_u64(1));
        let d_nat = natural(divisor);
        let d = integer(&BigInt::from_sign_magnitude(false, divisor.clone()));
        let predecessor = natural(&divisor.sub(&BigNat::from_u64(1)));
        let positive = apply(
            constant("Lean.Omega.Int.ofNat_pos_of_pos"),
            [d_nat, apply(constant("Nat.succ_pos"), [predecessor])],
        );
        let nonzero = apply(
            constant("Int.ne_of_gt"),
            [d.clone(), zero, positive.clone()],
        );
        let product = apply(constant("Int.mul"), [d.clone(), quotient.clone()]);
        let lower = apply(
            constant("Int.mul_ediv_self_le"),
            [dividend.clone(), d.clone(), nonzero],
        );
        self.pending_facts.push((
            standard_sub("Int", dividend.clone(), product.clone()),
            apply(
                constant("Int.sub_nonneg_of_le"),
                [dividend.clone(), product.clone(), lower],
            ),
        ));
        let ceiling = apply(constant("Int.add"), [product, d.clone()]);
        let successor = apply(constant("Int.add"), [dividend.clone(), one]);
        let upper = apply(
            constant("Int.lt_mul_ediv_self_add"),
            [dividend.clone(), d, positive],
        );
        let upper = apply(
            constant("Int.add_one_le_of_lt"),
            [dividend.clone(), ceiling.clone(), upper],
        );
        self.pending_facts.push((
            standard_sub("Int", ceiling.clone(), successor.clone()),
            apply(
                constant("Int.sub_nonneg_of_le"),
                [ceiling, successor, upper],
            ),
        ));
        Ok(())
    }
}

// Goal preprocessing can substitute a top-level let before reification.
// A local FVar nested in a divisor is deliberately not unfolded here: the
// pin treats that expression as nonground even if the local has a value.
fn transparent_value(expression: &Expr) -> Option<Expr> {
    match expression.node() {
        ExprNode::MData { expr, .. } => Some(expr.clone()),
        ExprNode::LetE {
            decl_name,
            value,
            body,
            ..
        } if decl_name.is_anonymous() && matches!(body.node(), ExprNode::BVar { idx: 0 }) => {
            Some(value.clone())
        }
        _ => None,
    }
}

fn canonical_binary(
    expression: &Expr,
    domain: &str,
    field: &str,
    lift_name: &str,
    instance: &str,
) -> Option<(Expr, Expr)> {
    let (head, arguments) = named_application(expression)?;
    if head != Name::from_components(field.split('.'))
        || arguments.len() != 6
        || !arguments[..3]
            .iter()
            .all(|argument| named_constant(argument, domain))
    {
        return None;
    }
    let (lift, dictionary) = named_application(&arguments[3])?;
    if lift != Name::from_components([lift_name])
        || dictionary.len() != 2
        || !named_constant(&dictionary[0], domain)
        || !named_constant(&dictionary[1], instance)
    {
        return None;
    }
    Some((arguments[4].clone(), arguments[5].clone()))
}

fn division_expression(expression: &Expr, domain: &str) -> Option<(Division, Expr, Expr)> {
    for (operation, field, lift, nat_instance, int_instance) in [
        (
            Division::Quotient,
            "HDiv.hDiv",
            "instHDiv",
            "Nat.instDiv",
            "Int.instDiv",
        ),
        (
            Division::Remainder,
            "HMod.hMod",
            "instHMod",
            "Nat.instMod",
            "Int.instMod",
        ),
    ] {
        let instance = if domain == "Nat" {
            nat_instance
        } else {
            int_instance
        };
        if let Some((left, right)) = canonical_binary(expression, domain, field, lift, instance) {
            return Some((operation, left, right));
        }
    }
    None
}

fn ground_operation(expression: &Expr) -> Option<(Operation, Expr, Expr)> {
    for (operation, field, lift, instance) in [
        (Operation::Add, "HAdd.hAdd", "instHAdd", "instAddNat"),
        (Operation::Sub, "HSub.hSub", "instHSub", "instSubNat"),
        (Operation::Mul, "HMul.hMul", "instHMul", "instMulNat"),
        (Operation::Div, "HDiv.hDiv", "instHDiv", "Nat.instDiv"),
    ] {
        if let Some((left, right)) = canonical_binary(expression, "Nat", field, lift, instance) {
            return Some((operation, left, right));
        }
    }
    let (head, arguments) = named_application(expression)?;
    if head != Name::from_components(["HPow", "hPow"])
        || arguments.len() != 6
        || !arguments[..3]
            .iter()
            .all(|argument| named_constant(argument, "Nat"))
    {
        return None;
    }
    let (lift, dictionary) = named_application(&arguments[3])?;
    if lift != Name::from_components(["instHPow"])
        || dictionary.len() != 3
        || !dictionary[..2]
            .iter()
            .all(|argument| named_constant(argument, "Nat"))
    {
        return None;
    }
    let (lift, dictionary) = named_application(&dictionary[2])?;
    if lift != Name::from_components(["instPowNat"])
        || dictionary.len() != 2
        || !named_constant(&dictionary[0], "Nat")
        || !named_constant(&dictionary[1], "instNatPowNat")
    {
        return None;
    }
    Some((Operation::Pow, arguments[4].clone(), arguments[5].clone()))
}

fn standard_division(operation: Division, left: Expr, right: Expr) -> Expr {
    let (field, lift, instance) = match operation {
        Division::Quotient => ("HDiv.hDiv", "instHDiv", "Int.instDiv"),
        Division::Remainder => ("HMod.hMod", "instHMod", "Int.instMod"),
    };
    let int = constant("Int");
    let dictionary = apply(
        Expr::const_(Name::from_components([lift]), vec![Level::zero()]),
        [int.clone(), constant(instance)],
    );
    apply(
        Expr::const_(
            Name::from_components(field.split('.')),
            vec![Level::zero(); 3],
        ),
        [int.clone(), int.clone(), int, dictionary, left, right],
    )
}
