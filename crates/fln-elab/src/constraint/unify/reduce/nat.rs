//! Closed Nat computation for the ordinary term-conversion path.
//!
//! The operation set and closed-operand rule come from the pinned
//! `Lean/Meta/WHNF.lean` (`withNatValue`, `reduceNat?`) and
//! `Lean/Meta/ExprDefEq.lean` (`isDefEqNat`). Operand evaluation uses the
//! parent's heap continuations, never recursive host calls. All allocations
//! and arithmetic work are bounded before entering the owned bignum routines.

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
        if !levels.is_empty() || arguments.len() != operation.arity() || !self.has_nat_literals()? {
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
