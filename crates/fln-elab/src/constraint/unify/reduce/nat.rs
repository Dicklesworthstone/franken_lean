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

/// The answer of the pin's `isDefEqOffset` (vendored Lean/Meta/Offset.lean:116-161) for one
/// equation, read over the canonical class terms the frontend elaborates.
pub(in crate::constraint::unify) enum ClassOffset {
    /// Neither side is an offset or an evaluable literal: other rules decide.
    Undecided,
    /// Two literals, or an offset against a literal, that differ.
    Refuted,
    /// Two literals of the same value.
    Equal,
    /// The equation with the common offset cancelled.
    Equation(Expr, Expr),
}

/// An `evalNat` operation: its operation, `Nat`'s function, class, method, monomorphic
/// instance, and the heterogeneous instance wrapping it (empty for `NatPow`).
type ClassOperation = (
    NatOperation,
    &'static str,
    &'static str,
    &'static str,
    &'static [&'static str],
    &'static [&'static str],
);

/// The operation an `evalNat` term applies, after its instance test.
enum ClassFrame {
    Visit(Expr),
    Apply(NatOperation),
}

/// `expression`'s head constant name and arguments, outermost annotation removed.
fn class_spine(expression: &Expr) -> Option<(&Name, Vec<&Expr>)> {
    let mut head = expression;
    while let ExprNode::MData { expr, .. } = head.node() {
        head = expr;
    }
    let mut arguments = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        arguments.push(a);
        head = f;
    }
    arguments.reverse();
    match head.node() {
        ExprNode::Const { name, .. } => Some((name, arguments)),
        _ => None,
    }
}

/// One of the pin's structural instance tests (vendored Lean/Meta/NatInstTesters.lean):
/// the constant `path` applied to exactly `arity` arguments, whose argument at each
/// position `inner` names is the argument-free constant named there.
fn is_class_instance(
    expression: &Expr,
    path: &[&str],
    arity: usize,
    inner: &[(usize, &[&str])],
) -> bool {
    let Some((name, arguments)) = class_spine(expression) else {
        return false;
    };
    name == &Name::from_components(path.iter().copied())
        && arguments.len() == arity
        && inner.iter().all(|(index, path)| {
            arguments
                .get(*index)
                .is_some_and(|argument| is_class_instance(argument, path, 0, &[]))
        })
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
    /// Smart unfolding is a shortcut for this complete logical model, not an
    /// interpretation attached to a user-chosen declaration name. Helpers must
    /// agree too: replacing the functional while retaining the root changes it.
    fn has_nat_sub_smart_model(&mut self) -> Result<bool, UnificationError> {
        if let Some(valid) = self.nat_sub_model_valid {
            return Ok(valid);
        }
        self.meter.node()?;
        if self
            .work
            .nat_sub_model_cache
            .snapshot
            .as_ref()
            .is_some_and(|snapshot| snapshot.has_same_declarations(&self.work.env))
        {
            self.nat_sub_model_valid = Some(true);
            return Ok(true);
        }
        static MODEL: std::sync::OnceLock<Option<Vec<ConstantInfo>>> = std::sync::OnceLock::new();
        let initialize = || {
            let mut entries = Vec::new();
            let sub = Name::from_components(["Nat", "sub"]);
            let declarations = crate::seed::imported_nat_intrinsic_model_declarations(&sub)?;
            for declaration in declarations {
                match declaration {
                    fln_kernel::Declaration::Defn(value) => {
                        entries.push(ConstantInfo::Defn(value));
                    }
                    fln_kernel::Declaration::Inductive(block) => {
                        entries.extend(block.types.into_iter().map(ConstantInfo::Induct));
                        entries.extend(block.ctors.into_iter().map(ConstantInfo::Ctor));
                        entries.extend(block.recursors.into_iter().map(ConstantInfo::Rec));
                    }
                    _ => return None,
                }
            }
            (!entries.is_empty()).then_some(entries)
        };
        let model = MODEL.get_or_init(initialize);
        let Some(model) = model else {
            self.nat_sub_model_valid = Some(false);
            return Ok(false);
        };
        for expected in model {
            self.meter.node()?;
            let Some(actual) = self.work.env.find(expected.name()) else {
                self.nat_sub_model_valid = Some(false);
                return Ok(false);
            };
            let a = actual.constant_val();
            let b = expected.constant_val();
            let metadata = a.level_params == b.level_params
                && match (actual, expected) {
                    (ConstantInfo::Defn(a), ConstantInfo::Defn(b)) => {
                        a.hints == b.hints && a.safety == b.safety && a.all == b.all
                    }
                    (ConstantInfo::Induct(a), ConstantInfo::Induct(b)) => {
                        a.num_params == b.num_params
                            && a.num_indices == b.num_indices
                            && a.all == b.all
                            && a.ctors == b.ctors
                            && a.num_nested == b.num_nested
                            && a.is_rec == b.is_rec
                            && a.is_unsafe == b.is_unsafe
                            && a.is_reflexive == b.is_reflexive
                    }
                    (ConstantInfo::Ctor(a), ConstantInfo::Ctor(b)) => {
                        a.induct == b.induct
                            && a.cidx == b.cidx
                            && a.num_params == b.num_params
                            && a.num_fields == b.num_fields
                            && a.is_unsafe == b.is_unsafe
                    }
                    (ConstantInfo::Rec(a), ConstantInfo::Rec(b)) => {
                        a.all == b.all
                            && a.num_params == b.num_params
                            && a.num_indices == b.num_indices
                            && a.num_motives == b.num_motives
                            && a.num_minors == b.num_minors
                            && a.rules.len() == b.rules.len()
                            && a.k == b.k
                            && a.is_unsafe == b.is_unsafe
                    }
                    _ => false,
                };
            let mut matches = metadata && same_terms(&a.type_, &b.type_, &mut self.meter)?;
            if matches {
                match (actual, expected) {
                    (ConstantInfo::Defn(a), ConstantInfo::Defn(b)) => {
                        matches = same_terms(&a.value, &b.value, &mut self.meter)?;
                    }
                    (ConstantInfo::Rec(a), ConstantInfo::Rec(b)) => {
                        for (a, b) in a.rules.iter().zip(&b.rules) {
                            self.meter.node()?;
                            if a.ctor != b.ctor
                                || a.nfields != b.nfields
                                || !same_terms(&a.rhs, &b.rhs, &mut self.meter)?
                            {
                                matches = false;
                                break;
                            }
                        }
                    }
                    _ => {}
                }
            }
            if !matches {
                self.nat_sub_model_valid = Some(false);
                return Ok(false);
            }
        }
        self.nat_sub_model_valid = Some(true);
        self.work.nat_sub_model_cache.snapshot = Some(self.work.env.clone());
        Ok(true)
    }

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
        self.nat_operation_signature(head, arity)
    }

    /// Whether `head` is the admitted Nat operation of this name and arity, at any
    /// transparency.
    fn nat_operation_signature(
        &mut self,
        head: &Expr,
        arity: usize,
    ) -> Result<Option<NatOperation>, UnificationError> {
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
            // Init's operations borrow their operands (`Nat.mul : (@& Nat) → (@& Nat) → Nat`,
            // vendored Init/Prelude.lean): `@&` is a `borrowed` annotation, an mdata around `Nat`
            // in the declaration's type. The pin's `reduceBinNatOp` keys on the name alone.
            let mut domain = binder_type;
            while let ExprNode::MData { expr, .. } = domain.node() {
                self.meter.node()?;
                domain = expr;
            }
            if domain != &nat_type {
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
        // `x + k` with `k > 0` is never `x` itself: no natural number is its own
        // successor, and definitional equality implies equality. The pin refutes it
        // by unfolding `Nat.add` (smart unfolding) to `Nat.succ _` against `x`; delta
        // here reaches `Nat.add`'s compiled recursor body instead, which cost a simp
        // trial matching `?n < ?n` against `acc + 1 < acc` some 18,000 steps.
        if lhs.found != rhs.found {
            let (offset, other) = if lhs.found {
                (&lhs, &rhs)
            } else {
                (&rhs, &lhs)
            };
            if !BigNatView::from_limbs_le(offset.value.limbs_le()).is_zero()
                && !other.literal
                && same_terms(&offset.base, &other.base, &mut self.meter)?
            {
                return Err(UnificationError::Deferred(
                    UnificationDeferred::UnsupportedEquation,
                ));
            }
        }
        // Against a bare symbolic term the pin's `isDefEqOffset` decides nothing
        // (`Lean/Meta/Offset.lean:136-139`): only unfolding `Nat.add`, which is
        // implicit-reducible, removes even a zero offset. Below `instances` that
        // unfolding is unavailable, so `n + 0 =?= n` fails at reducible
        // transparency, as simp's `eq_self` test does at the pin.
        if matches!(
            self.budget.transparency,
            UnificationTransparency::None | UnificationTransparency::Abbreviations
        ) && ((lhs.found && !rhs.found && !rhs.literal)
            || (rhs.found && !lhs.found && !lhs.literal))
        {
            return Ok(None);
        }
        // The pin cancels against another offset or a literal. A positive
        // one-sided offset against a bare symbolic term gives no new equation.
        // In particular, rewriting n = succ n to n = n+1 would cycle with delta
        // on Nat.add. A zero offset may otherwise remove its redundant wrapper.
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

    /// The pin's smart unfolding of `Nat.add` and `Nat.sub`, which recurse on their second
    /// argument (`_sunfold`): with a literal second argument `k`, `n + 0` and `n - 0` are
    /// `n`, `n + (k + 1)` is `(n + k).succ` and `n - (k + 1)` is `(n - k).pred`, the
    /// recursive call left folded. Called only where delta is about to unfold the
    /// operation, at whatever transparency permits that (both are `implicit_reducible` at
    /// the pin). Delta reached the compiled recursor body instead, leaving `Nat.succ` over
    /// recursor residue where the offset rules no longer see `n`: refuting
    /// `acc + 1 =?= acc` in a simp match cost thousands of steps. `None` unless `head` is
    /// `Nat.add` or `Nat.sub` applied to exactly two arguments (`arguments` is the reversed
    /// spine, so the second is `arguments[0]`) whose second reduces to a literal.
    pub(super) fn nat_literal_step(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
        locals: &LocalContext,
    ) -> Result<Option<Expr>, UnificationError> {
        let [second, first] = arguments else {
            return Ok(None);
        };
        let wrapper = match self.nat_operation_signature(head, 2)? {
            Some(NatOperation::Add) => Name::from_components(["Nat", "succ"]),
            Some(NatOperation::Sub) => {
                if !self.has_nat_sub_smart_model()? {
                    return Ok(None);
                }
                let pred = Name::from_components(["Nat", "pred"]);
                if !matches!(self.work.env.find(&pred), Some(ConstantInfo::Defn(info))
                    if info.safety == DefinitionSafety::Safe && info.base.level_params.is_empty())
                {
                    return Ok(None);
                }
                pred
            }
            _ => return Ok(None),
        };
        let second = self.whnf(second, locals)?;
        let Some(value) = self.nat_operand(&second)? else {
            return Ok(None);
        };
        if BigNatView::from_limbs_le(value.limbs_le()).is_zero() {
            return Ok(Some(first.clone()));
        }
        let previous = self.combine_nat_offsets(&value, &NatLit::from_u64(1), true)?;
        for _ in 0..4 {
            self.meter.node()?;
        }
        Ok(Some(Expr::app(
            Expr::const_(wrapper, Vec::new()),
            Expr::app(
                Expr::app(head.clone(), first.clone()),
                Expr::lit(Literal::Nat(previous)),
            ),
        )))
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

    /// The pin's `isDefEqOffset` (vendored Lean/Meta/Offset.lean:116-161), on the sides
    /// as they stand: an offset `s + k` (`isOffset?`) or a literal (`evalNat`) on either
    /// side cancels against the other side's, and two literals are compared. Instances are
    /// tested structurally, a subset of the pin's `matchesInstance`.
    pub(in crate::constraint::unify) fn class_offset_equation(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<ClassOffset, UnificationError> {
        if !self.has_nat_literals()? {
            return Ok(ClassOffset::Undecided);
        }
        let left = self.instantiate(left)?;
        let right = self.instantiate(right)?;
        let step = match self.class_offset(&left)? {
            Some((s, k1)) => match self.class_offset(&right)? {
                Some((t, k2)) => match k1.cmp(&k2) {
                    std::cmp::Ordering::Equal => Some((s, t)),
                    std::cmp::Ordering::Less => {
                        let difference = self.combine_nat_offsets(&k2, &k1, true)?;
                        self.class_offset_term(t, difference)?.map(|t| (s, t))
                    }
                    std::cmp::Ordering::Greater => {
                        let difference = self.combine_nat_offsets(&k1, &k2, true)?;
                        self.class_offset_term(s, difference)?.map(|s| (s, t))
                    }
                },
                None => match self.class_nat_value(&right)? {
                    Some(v2) if v2 >= k1 => {
                        let difference = self.combine_nat_offsets(&v2, &k1, true)?;
                        self.class_numeral(difference)?.map(|t| (s, t))
                    }
                    Some(_) => return Ok(ClassOffset::Refuted),
                    None => None,
                },
            },
            None => match self.class_nat_value(&left)? {
                Some(v1) => match self.class_offset(&right)? {
                    Some((t, k2)) if v1 >= k2 => {
                        let difference = self.combine_nat_offsets(&v1, &k2, true)?;
                        self.class_numeral(difference)?.map(|s| (s, t))
                    }
                    Some(_) => return Ok(ClassOffset::Refuted),
                    None => match self.class_nat_value(&right)? {
                        Some(v2) if v1 == v2 => return Ok(ClassOffset::Equal),
                        Some(_) => return Ok(ClassOffset::Refuted),
                        None => None,
                    },
                },
                None => None,
            },
        };
        Ok(match step {
            Some((s, t)) => ClassOffset::Equation(s, t),
            None => ClassOffset::Undecided,
        })
    }

    /// The pin's `isOffset?` (Offset.lean:87-106): `succ`, `Nat.add`, `Add.add` and
    /// `HAdd.hAdd` at Nat's canonical instances, with an evaluable right operand, peeled
    /// until the base is none of them. `None` unless at least one layer is peeled.
    fn class_offset(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<(Expr, NatLit)>, UnificationError> {
        let mut base = expression.clone();
        let mut total = NatLit::from_u64(0);
        let mut found = false;
        loop {
            self.meter.tick()?;
            let Some((name, arguments)) = class_spine(&base) else {
                break;
            };
            let add = |path: &[&str]| name == &Name::from_components(path.iter().copied());
            let (next, operand) = if add(&["Nat", "succ"]) && arguments.len() == 1 {
                (arguments[0].clone(), None)
            } else if add(&["Nat", "add"]) && arguments.len() == 2 {
                (arguments[0].clone(), Some(arguments[1].clone()))
            } else if add(&["Add", "add"])
                && arguments.len() == 4
                && is_class_instance(arguments[1], &["instAddNat"], 0, &[])
            {
                (arguments[2].clone(), Some(arguments[3].clone()))
            } else if add(&["HAdd", "hAdd"])
                && arguments.len() == 6
                && is_class_instance(arguments[3], &["instHAdd"], 2, &[(1, &["instAddNat"])])
            {
                (arguments[4].clone(), Some(arguments[5].clone()))
            } else {
                break;
            };
            let increment = match operand {
                None => NatLit::from_u64(1),
                Some(operand) => match self.class_nat_value(&operand)? {
                    Some(value) => value,
                    None => break,
                },
            };
            total = self.combine_nat_offsets(&total, &increment, false)?;
            base = next;
            found = true;
        }
        Ok(found.then_some((base, total)))
    }

    /// The pin's `evalNat` (Offset.lean:26-61): literals, `Nat.zero`, numerals at
    /// `instOfNatNat`, and the Nat operations and their class forms at Nat's canonical
    /// instances (structural tests, as `Structural` there). A heap worklist, not recursion.
    fn class_nat_value(&mut self, expression: &Expr) -> Result<Option<NatLit>, UnificationError> {
        use NatOperation::*;
        let mut frames = vec![ClassFrame::Visit(expression.clone())];
        let mut values: Vec<NatLit> = Vec::new();
        while let Some(frame) = frames.pop() {
            self.meter.tick()?;
            let term = match frame {
                ClassFrame::Apply(operation) => {
                    let operands = values.split_off(values.len() - operation.arity());
                    let Some(result) = self.evaluate_nat(operation, &operands)? else {
                        return Ok(None);
                    };
                    let ExprNode::Lit {
                        literal: Literal::Nat(value),
                    } = result.node()
                    else {
                        return Ok(None);
                    };
                    values.push(value.clone());
                    continue;
                }
                ClassFrame::Visit(term) => term,
            };
            let mut stripped = &term;
            while let ExprNode::MData { expr, .. } = stripped.node() {
                stripped = expr;
            }
            if let ExprNode::Lit {
                literal: Literal::Nat(value),
            } = stripped.node()
            {
                values.push(value.clone());
                continue;
            }
            let Some((name, arguments)) = class_spine(stripped) else {
                return Ok(None);
            };
            let is = |path: &[&str]| name == &Name::from_components(path.iter().copied());
            if arguments.is_empty() && is(&["Nat", "zero"]) {
                values.push(NatLit::from_u64(0));
                continue;
            }
            if is(&["OfNat", "ofNat"])
                && arguments.len() == 3
                && is_class_instance(arguments[2], &["instOfNatNat"], 1, &[])
            {
                frames.push(ClassFrame::Visit(arguments[1].clone()));
                continue;
            }
            if is(&["Nat", "succ"]) && arguments.len() == 1 {
                frames.push(ClassFrame::Apply(Succ));
                frames.push(ClassFrame::Visit(arguments[0].clone()));
                continue;
            }
            const BINARY: [ClassOperation; 6] = [
                (Add, "add", "Add", "add", &["instAddNat"], &["instHAdd"]),
                (Sub, "sub", "Sub", "sub", &["instSubNat"], &["instHSub"]),
                (Mul, "mul", "Mul", "mul", &["instMulNat"], &["instHMul"]),
                (Div, "div", "Div", "div", &["Nat", "instDiv"], &["instHDiv"]),
                (Mod, "mod", "Mod", "mod", &["Nat", "instMod"], &["instHMod"]),
                (Pow, "pow", "NatPow", "pow", &["instNatPowNat"], &[]),
            ];
            let mut operation = None;
            for (kind, function, class, method, instance, heterogeneous) in BINARY {
                let class_method = [class, method];
                let heterogeneous_class = format!("H{class}");
                let heterogeneous_method = format!("h{class}");
                let operands = if is(&["Nat", function]) && arguments.len() == 2 {
                    Some((arguments[0], arguments[1]))
                } else if is(&class_method)
                    && arguments.len() == 4
                    && is_class_instance(arguments[1], instance, 0, &[])
                {
                    Some((arguments[2], arguments[3]))
                } else if !heterogeneous.is_empty()
                    && is(&[heterogeneous_class.as_str(), heterogeneous_method.as_str()])
                    && arguments.len() == 6
                    && is_class_instance(arguments[3], heterogeneous, 2, &[(1, instance)])
                {
                    Some((arguments[4], arguments[5]))
                } else if matches!(kind, Pow)
                    && is(&["Pow", "pow"])
                    && arguments.len() == 5
                    && is_class_instance(arguments[2], &["instPowNat"], 2, &[(1, instance)])
                {
                    Some((arguments[3], arguments[4]))
                } else if matches!(kind, Pow)
                    && is(&["HPow", "hPow"])
                    && arguments.len() == 6
                    && class_spine(arguments[3]).is_some_and(|(name, inner)| {
                        name == &Name::from_components(["instHPow"])
                            && inner.len() == 3
                            && is_class_instance(inner[2], &["instPowNat"], 2, &[(1, instance)])
                    })
                {
                    Some((arguments[4], arguments[5]))
                } else {
                    None
                };
                if let Some(operands) = operands {
                    operation = Some((kind, operands));
                    break;
                }
            }
            let Some((kind, (left, right))) = operation else {
                return Ok(None);
            };
            frames.push(ClassFrame::Apply(kind));
            frames.push(ClassFrame::Visit(right.clone()));
            frames.push(ClassFrame::Visit(left.clone()));
        }
        Ok(values.pop())
    }

    /// The pin's `mkNatLit` (vendored Lean/Expr.lean:750): `OfNat.ofNat Nat n (instOfNatNat
    /// n)`, when the environment declares both constants.
    fn class_numeral(&mut self, value: NatLit) -> Result<Option<Expr>, UnificationError> {
        self.meter.tick()?;
        let of_nat = Name::from_components(["OfNat", "ofNat"]);
        let instance = Name::from_components(["instOfNatNat"]);
        if self.work.env.find(&of_nat).is_none() || self.work.env.find(&instance).is_none() {
            return Ok(None);
        }
        let literal = Expr::lit(Literal::Nat(value));
        Ok(Some(
            [
                Expr::const_(Name::from_components(["Nat"]), Vec::new()),
                literal.clone(),
                Expr::app(Expr::const_(instance, Vec::new()), literal),
            ]
            .into_iter()
            .fold(Expr::const_(of_nat, vec![Level::zero()]), Expr::app),
        ))
    }

    /// The pin's `mkOffset` (Offset.lean:108-114): `base` itself for a zero offset, the
    /// numeral when `base` evaluates to zero, and otherwise `base + offset` as the frontend
    /// spells it (`mkNatAdd`, vendored Lean/Expr.lean:2254).
    fn class_offset_term(
        &mut self,
        base: Expr,
        offset: NatLit,
    ) -> Result<Option<Expr>, UnificationError> {
        if offset.limbs_le().is_empty() {
            return Ok(Some(base));
        }
        if self
            .class_nat_value(&base)?
            .is_some_and(|value| value.limbs_le().is_empty())
        {
            return self.class_numeral(offset);
        }
        let Some(numeral) = self.class_numeral(offset)? else {
            return Ok(None);
        };
        let add = Name::from_components(["HAdd", "hAdd"]);
        let heterogeneous = Name::from_components(["instHAdd"]);
        let homogeneous = Name::from_components(["instAddNat"]);
        if [&add, &heterogeneous, &homogeneous]
            .iter()
            .any(|name| self.work.env.find(name).is_none())
        {
            return Ok(None);
        }
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let instance = Expr::app(
            Expr::app(
                Expr::const_(heterogeneous, vec![Level::zero()]),
                nat.clone(),
            ),
            Expr::const_(homogeneous, Vec::new()),
        );
        Ok(Some(
            [nat.clone(), nat.clone(), nat, instance, base, numeral]
                .into_iter()
                .fold(
                    Expr::const_(add, vec![Level::zero(), Level::zero(), Level::zero()]),
                    Expr::app,
                ),
        ))
    }
}
