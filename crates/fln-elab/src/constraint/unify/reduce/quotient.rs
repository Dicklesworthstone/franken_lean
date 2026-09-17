//! Quotient computation in the unifier, not a new admission authority.
//!
//! K1's quotient initialization owns the four primitive types (KR-950..954).
//! This module uses only those registered primitive tags and the corresponding
//! KR-955 computation positions. An ordinary definition called `Quot.lift`
//! cannot acquire primitive behavior. The result is an ordinary expression:
//! every resulting assignment still passes the parent's K1 validation barrier.
use super::*;
use fln_env::constants::QuotKind;

impl Engine<'_> {
    /// A saturated primitive's major position, in forward application order.
    /// Check the entire registered quartet, not merely a familiar-looking head.
    pub(super) fn quotient_major_index(
        &mut self,
        head: &Expr,
        arguments: usize,
    ) -> Result<Option<usize>, UnificationError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let root = Name::from_components(["Quot"]);
        let (major, level_count) = if name == &Name::str(root.clone(), "lift") {
            (5, 2)
        } else if name == &Name::str(root.clone(), "ind") {
            (4, 1)
        } else {
            return Ok(None);
        };
        if arguments <= major || levels.len() != level_count {
            return Ok(None);
        }
        let u = Name::from_components(["u"]);
        let v = Name::from_components(["v"]);
        for (expected, kind, count) in [
            (root.clone(), QuotKind::Type, 1),
            (Name::str(root.clone(), "mk"), QuotKind::Ctor, 1),
            (Name::str(root.clone(), "lift"), QuotKind::Lift, 2),
            (Name::str(root, "ind"), QuotKind::Ind, 1),
        ] {
            self.meter.node()?;
            let Some(ConstantInfo::Quot(primitive)) = self.work.env.find(&expected) else {
                return Ok(None);
            };
            let parameters = &primitive.base.level_params;
            // Quotient initialization at the pin requires these parameter names
            // and this order. The type bodies were checked at admission; do not
            // clone or rewalk them on every reduction.
            if primitive.base.name != expected
                || primitive.kind != kind
                || parameters.len() != count
                || parameters.first() != Some(&u)
                || (count == 2 && parameters.get(1) != Some(&v))
            {
                return Ok(None);
            }
        }
        Ok(Some(major))
    }

    /// `Quot.lift f h (Quot.mk r a)` and `Quot.ind h (Quot.mk r a)`
    /// compute to `f a` and `h a`. Both branches occupy forward argument 3;
    /// the representative occupies forward argument 2 of the constructor.
    /// Every slice here is in the reducer's reverse-application order.
    pub(super) fn quotient_step(
        &mut self,
        eliminator: &Expr,
        arguments: &[Expr],
        major_head: &Expr,
        major_arguments: &[Expr],
    ) -> Result<Option<Expr>, UnificationError> {
        self.meter.tick()?;
        if major_arguments.len() != 3 {
            return Ok(None);
        }
        let eliminator = self.instantiate(eliminator)?;
        let constructor = self.instantiate(major_head)?;
        let ExprNode::Const { levels, .. } = eliminator.node() else {
            return Ok(None);
        };
        let ExprNode::Const {
            name,
            levels: constructor_levels,
        } = constructor.node()
        else {
            return Ok(None);
        };
        if name != &Name::from_components(["Quot", "mk"])
            || constructor_levels.len() != 1
        {
            return Ok(None);
        }
        let Some(level) = levels.first() else {
            return Ok(None);
        };
        // Do not solve universe holes just to unlock computation. A later
        // equation can assign them and the ordinary retry loop will revisit it.
        // Normalization is a sufficient equality test, not an assignment rule.
        let level = simplify_level(level, &mut self.meter)?;
        let constructor_level = simplify_level(&constructor_levels[0], &mut self.meter)?;
        if !same_levels(&level, &constructor_level, &mut self.meter)? {
            return Ok(None);
        }
        let Some(branch_position) = arguments.len().checked_sub(4) else {
            return Ok(None);
        };
        let Some(branch) = arguments.get(branch_position) else {
            return Ok(None);
        };
        self.meter.node()?;
        Ok(Some(Expr::app(branch.clone(), major_arguments[0].clone())))
    }
}
