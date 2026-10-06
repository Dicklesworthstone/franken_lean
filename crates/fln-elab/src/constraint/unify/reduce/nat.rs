//! Nat computation and compact symbolic offsets for ordinary term conversion.
//!
//! The operation set and closed-operand rule come from the pinned
//! `Lean/Meta/WHNF.lean` (`withNatValue`, `reduceNat?`) and
//! `Lean/Meta/ExprDefEq.lean` (`isDefEqNat`). Operand evaluation uses the
//! parent's heap continuations, never recursive host calls. All allocations
//! and arithmetic work are bounded before entering the owned bignum routines.
//! Symbolic offsets follow `Lean/Meta/Offset.lean`: peel `succ` and additions
//! with known right operands, then cancel the common offset before comparing
//! bases. An opaque base is never unfolded merely to collect an offset.

use super::*;
use fln_bignum::nat::{BigNat, BigNatView};
use fln_core::expr::NatLit;

#[derive(Clone, Copy)]
pub(super) enum NatOperation {
    Succ,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Gcd,
    Beq,
    Ble,
    Land,
    Lor,
    Xor,
    ShiftLeft,
    ShiftRight,
}

struct NatOffset {
    base: Expr,
    value: NatLit,
    found: bool,
    literal: bool,
}

fn has_offset_head(expression: &Expr) -> bool {
    let ExprNode::App { f, .. } = expression.node() else {
        return false;
    };
    let (head, arity) = match f.node() {
        ExprNode::App { f, .. } => (f, 2),
        _ => (f, 1),
    };
    let ExprNode::Const { name, levels } = head.node() else {
        return false;
    };
    levels.is_empty()
        && matches!(
            (NatOperation::from_name(name), arity),
            (Some(NatOperation::Succ), 1) | (Some(NatOperation::Add), 2)
        )
}

impl NatOperation {
    fn from_name(name: &Name) -> Option<Self> {
        use fln_core::name::LeafView;
        if name.parent() != Name::from_components(["Nat"]) {
            return None;
        }
        Some(match name.leaf_view() {
            LeafView::Str("succ") => Self::Succ,
            LeafView::Str("add") => Self::Add,
            LeafView::Str("sub") => Self::Sub,
            LeafView::Str("mul") => Self::Mul,
            LeafView::Str("div") => Self::Div,
            LeafView::Str("mod") => Self::Mod,
            LeafView::Str("pow") => Self::Pow,
            LeafView::Str("gcd") => Self::Gcd,
            LeafView::Str("beq") => Self::Beq,
            LeafView::Str("ble") => Self::Ble,
            LeafView::Str("land") => Self::Land,
            LeafView::Str("lor") => Self::Lor,
            LeafView::Str("xor") => Self::Xor,
            LeafView::Str("shiftLeft") => Self::ShiftLeft,
            LeafView::Str("shiftRight") => Self::ShiftRight,
            _ => return None,
        })
    }

    pub(super) fn arity(self) -> usize {
        if matches!(self, Self::Succ) { 1 } else { 2 }
    }

    fn is_predicate(self) -> bool {
        matches!(self, Self::Beq | Self::Ble)
    }
}

impl Engine<'_> {
    /// The constructor laws must be present, not an axiom merely named `Nat`.
    /// These fixed metadata checks do not require allocation-identity equality
    /// with the source seed, so an imported pin-shaped Nat works as well.
    fn has_nat_literals(&mut self) -> Result<bool, UnificationError> {
        self.meter.tick()?;
        if let Some(valid) = self.nat_literals_valid {
            return Ok(valid);
        }
        let nat_name = Name::from_components(["Nat"]);
        let nat_type = Expr::const_(nat_name.clone(), Vec::new());
        let zero = Name::from_components(["Nat", "zero"]);
        let succ = Name::from_components(["Nat", "succ"]);
        let valid = match self.work.env.find(&nat_name) {
            Some(ConstantInfo::Induct(info)) => {
                !info.is_unsafe
                    && info.is_rec
                    && info.num_params == 0
                    && info.num_indices == 0
                    && info.num_nested == 0
                    && info.base.level_params.is_empty()
                    && info.base.type_ == Expr::sort(Level::one())
                    && info.all == [nat_name.clone()]
                    && info.ctors == [zero.clone(), succ.clone()]
            }
            _ => false,
        } && [(zero, 0), (succ, 1)].into_iter().all(|(name, fields)| {
            let Some(ConstantInfo::Ctor(info)) = self.work.env.find(&name) else {
                return false;
            };
            let type_matches = if fields == 0 {
                info.base.type_ == nat_type
            } else {
                matches!(info.base.type_.node(), ExprNode::ForallE { binder_type, body, .. }
                    if binder_type == &nat_type && body == &nat_type)
            };
            !info.is_unsafe
                && info.induct == nat_name
                && info.cidx == fields
                && info.num_params == 0
                && info.num_fields == fields
                && info.base.level_params.is_empty()
                && type_matches
        });
        self.nat_literals_valid = Some(valid);
        Ok(valid)
    }

    pub(super) fn nat_operation(
        &mut self,
        head: &Expr,
        arguments: &mut [Expr],
    ) -> Result<Option<NatOperation>, UnificationError> {
        let Some(operation) = self.nat_operation_kind(head, arguments.len())? else {
            return Ok(None);
        };
        for argument in arguments {
            if argument.has_expr_mvar() || argument.has_level_mvar() {
                *argument = self.instantiate(argument)?;
            }
            if argument.has_expr_mvar() || argument.has_level_mvar() || argument.has_fvar() {
                return Ok(None);
            }
        }
        Ok(Some(operation))
    }

    fn nat_operation_kind(
        &mut self,
        head: &Expr,
        arity: usize,
    ) -> Result<Option<NatOperation>, UnificationError> {
        // Keep the instance-selection and abbreviation-only approximation
        // unchanged. Ordinary source inference retries at Default explicitly.
        if !matches!(
            self.budget.transparency,
            UnificationTransparency::Default | UnificationTransparency::SafeDefinitions
        ) {
            return Ok(None);
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(operation) = NatOperation::from_name(name) else {
            return Ok(None);
        };
        if !levels.is_empty() || arity != operation.arity() || !self.has_nat_literals()? {
            return Ok(None);
        }
        let Some(info) = self.work.env.find(name) else {
            return Ok(None);
        };
        if !match info {
            ConstantInfo::Axiom(info) => !info.is_unsafe,
            ConstantInfo::Defn(info) => info.safety == DefinitionSafety::Safe,
            ConstantInfo::Ctor(info) => matches!(operation, NatOperation::Succ) && !info.is_unsafe,
            _ => false,
        } {
            return Ok(None);
        }
        let base = info.constant_val();
        let nat_type = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let mut type_ = &base.type_;
        for _ in 0..operation.arity() {
            self.meter.node()?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = type_.node()
            else {
                return Ok(None);
            };
            if binder_type != &nat_type {
                return Ok(None);
            }
            type_ = body;
        }
        let result_type = if operation.is_predicate() {
            Expr::const_(Name::from_components(["Bool"]), Vec::new())
        } else {
            nat_type
        };
        if !base.level_params.is_empty() || type_ != &result_type {
            return Ok(None);
        }
        if operation.is_predicate() {
            for leaf in ["false", "true"] {
                let name = Name::from_components(["Bool", leaf]);
                if !matches!(self.work.env.find(&name), Some(ConstantInfo::Ctor(info))
                    if !info.is_unsafe && info.num_params == 0 && info.num_fields == 0
                        && info.base.level_params.is_empty() && info.base.type_ == result_type
                        && info.induct == Name::from_components(["Bool"]))
                {
                    return Ok(None);
                }
            }
        }
        Ok(Some(operation))
    }

    /// A single iteration peels one offset constructor. Closed right operands
    /// use the existing heap-based evaluator; it never calls this collector.
    fn nat_offset(
        &mut self,
        expression: &Expr,
        locals: &LocalContext,
    ) -> Result<NatOffset, UnificationError> {
        let mut base = if expression.has_expr_mvar() || expression.has_level_mvar() {
            self.instantiate(expression)?
        } else {
            expression.clone()
        };
        let mut value = NatLit::from_u64(0);
        let mut found = false;
        loop {
            self.meter.node()?;
            if let ExprNode::MData { expr, .. } = base.node() {
                base = expr.clone();
                continue;
            }
            let ExprNode::App { f, a } = base.node() else {
                break;
            };
            let (next, increment) = if let ExprNode::App { f: head, a: left } = f.node() {
                if !matches!(self.nat_operation_kind(head, 2)?, Some(NatOperation::Add))
                    || a.has_expr_mvar()
                    || a.has_level_mvar()
                    || a.has_fvar()
                {
                    break;
                }
                let right = self.whnf(a, locals)?;
                let Some(increment) = self.nat_operand(&right)? else {
                    break;
                };
                (left.clone(), increment)
            } else if matches!(self.nat_operation_kind(f, 1)?, Some(NatOperation::Succ)) {
                (a.clone(), NatLit::from_u64(1))
            } else {
                break;
            };
            value = self.combine_nat_offsets(&value, &increment, false)?;
            base = next;
            found = true;
        }
        let literal = self.nat_operand(&base)?;
        let is_literal = literal.is_some();
        if let Some(literal) = literal {
            value = self.combine_nat_offsets(&value, &literal, false)?;
            base = Expr::lit(Literal::Nat(NatLit::from_u64(0)));
        }
        Ok(NatOffset {
            base,
            value,
            found,
            literal: is_literal,
        })
    }

    fn combine_nat_offsets(
        &mut self,
        left: &NatLit,
        right: &NatLit,
        subtract: bool,
    ) -> Result<NatLit, UnificationError> {
        // Charge the arithmetic, owned result and literal copy before any of
        // their proportional allocations. Offsets never expand to unary terms.
        let width = (left.limbs_le().len() as u128)
            .saturating_add(right.limbs_le().len() as u128)
            .saturating_add(1);
        self.charge_nat_work(width.saturating_mul(3))?;
        let left = BigNatView::from_limbs_le(left.limbs_le());
        let right = BigNatView::from_limbs_le(right.limbs_le());
        let result = if subtract {
            left.sub(right)
        } else {
            left.add(right)
        };
        Ok(fln_bignum::interop::literal_from_bignat(&result))
    }

    fn make_nat_offset(&mut self, base: Expr, value: &NatLit) -> Result<Expr, UnificationError> {
        self.meter.node()?;
        if BigNatView::from_limbs_le(value.limbs_le()).is_zero() {
            return Ok(base);
        }
        if let Some(literal) = self.nat_operand(&base)? {
            return Ok(Expr::lit(Literal::Nat(
                self.combine_nat_offsets(&literal, value, false)?,
            )));
        }
        for _ in 0..3 {
            self.meter.node()?;
        }
        Ok(Expr::app(
            Expr::app(
                Expr::const_(Name::from_components(["Nat", "add"]), Vec::new()),
                base,
            ),
            Expr::lit(Literal::Nat(value.clone())),
        ))
    }

    pub(in crate::constraint::unify) fn nat_offset_equation(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<(Expr, Expr)>, UnificationError> {
        if !has_offset_head(left) && !has_offset_head(right) {
            return Ok(None);
        }
        // The reconstructed compact form itself uses Nat.add. Require its
        // complete operation signature and the actual Nat constructor laws.
        let add = Expr::const_(Name::from_components(["Nat", "add"]), Vec::new());
        if !matches!(self.nat_operation_kind(&add, 2)?, Some(NatOperation::Add)) {
            return Ok(None);
        }
        let lhs = self.nat_offset(left, locals)?;
        let rhs = self.nat_offset(right, locals)?;
        if !lhs.found && !rhs.found {
            return Ok(None);
        }
        // The pin cancels against another offset or a literal. A positive
        // one-sided offset against a bare symbolic term gives no new equation.
        // In particular, rewriting n = succ n to n = n+1 would cycle with delta
        // on Nat.add. A zero offset may always remove its redundant wrapper.
        if (lhs.found
            && !rhs.found
            && !rhs.literal
            && !BigNatView::from_limbs_le(lhs.value.limbs_le()).is_zero())
            || (rhs.found
                && !lhs.found
                && !lhs.literal
                && !BigNatView::from_limbs_le(rhs.value.limbs_le()).is_zero())
        {
            return Ok(None);
        }
        self.charge_nat_work(
            (lhs.value.limbs_le().len() as u128)
                .saturating_add(rhs.value.limbs_le().len() as u128)
                .saturating_add(1),
        )?;
        let ordering = lhs.value.cmp(&rhs.value);
        // An offset cannot equal a smaller literal (Offset.lean:143–146,
        // 153–156). Refuse directly: rebuilding x+1=0 would cycle when delta
        // exposes succ x and the next offset pass puts the addition back.
        if (lhs.found && rhs.literal && ordering == std::cmp::Ordering::Greater)
            || (rhs.found && lhs.literal && ordering == std::cmp::Ordering::Less)
        {
            return Err(UnificationError::Deferred(
                UnificationDeferred::UnsupportedEquation,
            ));
        }
        let (new_left, new_right) = if ordering != std::cmp::Ordering::Greater {
            let difference = self.combine_nat_offsets(&rhs.value, &lhs.value, true)?;
            (lhs.base, self.make_nat_offset(rhs.base, &difference)?)
        } else {
            let difference = self.combine_nat_offsets(&lhs.value, &rhs.value, true)?;
            (self.make_nat_offset(lhs.base, &difference)?, rhs.base)
        };
        // One-sided already canonical offsets make no progress. Returning the
        // same equation would turn a rigid mismatch into an exhaustion loop.
        if same_terms(left, &new_left, &mut self.meter)?
            && same_terms(right, &new_right, &mut self.meter)?
        {
            Ok(None)
        } else {
            Ok(Some((new_left, new_right)))
        }
    }

    pub(super) fn nat_operand(&mut self, expr: &Expr) -> Result<Option<NatLit>, UnificationError> {
        match expr.node() {
            ExprNode::Lit {
                literal: Literal::Nat(value),
            } => {
                for _ in value.limbs_le() {
                    self.meter.node()?;
                }
                Ok(Some(value.clone()))
            }
            ExprNode::Const { name, levels }
                if name == &Name::from_components(["Nat", "zero"]) && levels.is_empty() =>
            {
                Ok(Some(NatLit::from_u64(0)))
            }
            _ => Ok(None),
        }
    }

    fn charge_nat_work(&mut self, work: u128) -> Result<(), UnificationError> {
        for _ in 0..work {
            self.meter.node()?;
        }
        Ok(())
    }

    pub(super) fn evaluate_nat(
        &mut self,
        operation: NatOperation,
        values: &[NatLit],
    ) -> Result<Option<Expr>, UnificationError> {
        use NatOperation::*;
        let left = BigNatView::from_limbs_le(values[0].limbs_le());
        let right = values
            .get(1)
            .map(|value| BigNatView::from_limbs_le(value.limbs_le()));
        let left_width = left.limbs_le().len() as u128;
        let right_width = right.map_or(0, |value| value.limbs_le().len() as u128);
        let width = left_width.saturating_add(right_width).saturating_add(1);
        let binary = right.unwrap_or_else(|| BigNatView::from_limbs_le(&[]));
        let exponent = if matches!(operation, Pow) {
            let threshold = self
                .work
                .options
                .get_nat(&Name::from_components(["exponentiation", "threshold"]), 256);
            let Some(exponent) = binary.to_u64().filter(|value| *value <= threshold) else {
                // The pin's SafeExponentiation.lean refuses this computation.
                // Leave the equation available to other conversion rules.
                return Ok(None);
            };
            exponent
        } else {
            0
        };
        let work = match operation {
            Mul | Div | Mod => {
                width.saturating_add(left_width.saturating_mul(right_width).saturating_mul(64))
            }
            Gcd => width
                .saturating_mul(width)
                .saturating_mul(width)
                .saturating_mul(64),
            Pow if !left.is_zero() && left.to_u64() != Some(1) => {
                let result_width = u128::from(left.bit_length())
                    .saturating_mul(u128::from(exponent))
                    .div_ceil(64)
                    .saturating_add(1);
                width.saturating_add(result_width.saturating_mul(result_width).saturating_mul(64))
            }
            ShiftLeft if !left.is_zero() => {
                let Some(bits) = binary.to_u64() else {
                    return Err(UnificationError::NodeLimit {
                        limit: self.meter.max_nodes,
                    });
                };
                width.saturating_add(u128::from(bits).div_ceil(64))
            }
            _ => width,
        };
        self.charge_nat_work(work)?;
        let allocation_limit = || UnificationError::NodeLimit {
            limit: self.meter.max_nodes,
        };
        let result = match operation {
            Succ => left.add(BigNatView::from_limbs_le(&[1])),
            Add => left.add(binary),
            Sub => left.sub(binary),
            Mul => left.mul(binary),
            Div => left.div(binary),
            Mod => left.rem(binary),
            Pow if exponent == 0 || left.to_u64() == Some(1) => BigNat::from_u64(1),
            Pow if left.is_zero() => BigNat::zero(),
            Pow => left
                .checked_pow(u32::try_from(exponent).map_err(|_| allocation_limit())?)
                .ok_or_else(allocation_limit)?,
            Gcd => left.gcd(binary),
            Beq | Ble => {
                let value = if matches!(operation, Beq) {
                    left.beq(binary)
                } else {
                    left.ble(binary)
                };
                return Ok(Some(Expr::const_(
                    Name::from_components(["Bool", if value { "true" } else { "false" }]),
                    Vec::new(),
                )));
            }
            Land => left.land(binary),
            Lor => left.lor(binary),
            Xor => left.lxor(binary),
            ShiftLeft if left.is_zero() => BigNat::zero(),
            ShiftLeft => left
                .checked_shl(binary.to_u64().expect("charged representable shift"))
                .ok_or_else(allocation_limit)?,
            ShiftRight => match binary.to_u64() {
                Some(bits) => left.shr(bits),
                None => BigNat::zero(),
            },
        };
        for _ in result.limbs_le() {
            self.meter.node()?;
        }
        Ok(Some(Expr::lit(Literal::Nat(
            fln_bignum::interop::literal_from_bignat(&result),
        ))))
    }
}
