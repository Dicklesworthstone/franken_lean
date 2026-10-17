//! The pin's `Expr.toCtorIfLit` String case: expose the literal through
//! `String.ofList`, then let the ordinary reducer interpret that definition.
//! No native equality result, proof or replacement implementation is trusted.
use super::*;
use fln_core::expr::NatLit;

impl Engine<'_> {
    /// Expand one literal for one pending recursor/projection consumer. The
    /// continuation records that it has already tried: a definition that
    /// returns a literal again must not repeatedly re-enter this expansion.
    pub(super) fn string_literal_constructor(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<Expr>, UnificationError> {
        let ExprNode::Lit {
            literal: Literal::Str(value),
        } = expression.node()
        else {
            return Ok(None);
        };
        let string_of_list = Name::from_components(["String", "ofList"]);
        let char_of_nat = Name::from_components(["Char", "ofNat"]);
        // In an incomplete import world the literal must stay stuck, rather
        // than acquiring references to definitions which do not exist. Their
        // bodies are not replaced here: normal delta transparency and the
        // checked recursor/field rules remain in charge of every further step.
        for name in [&string_of_list, &char_of_nat] {
            self.meter.node()?;
            if !matches!(self.work.env.find(name), Some(ConstantInfo::Defn(definition))
                if definition.safety == DefinitionSafety::Safe
                    && definition.base.level_params.is_empty())
            {
                return Ok(None);
            }
        }
        for label in ["Char", "String", "List"] {
            self.meter.node()?;
            if !matches!(self.work.env.find(&Name::from_components([label])),
                Some(ConstantInfo::Induct(family)) if !family.is_unsafe)
            {
                return Ok(None);
            }
        }
        for (label, fields) in [("nil", 0), ("cons", 2)] {
            self.meter.node()?;
            if !matches!(self.work.env.find(&Name::from_components(["List", label])),
                Some(ConstantInfo::Ctor(constructor)) if !constructor.is_unsafe
                    && constructor.induct == Name::from_components(["List"])
                    && constructor.num_params == 1 && constructor.num_fields == fields)
            {
                return Ok(None);
            }
        }
        for _ in 0..10 {
            self.meter.node()?;
        }
        let char_type = Expr::const_(Name::from_components(["Char"]), vec![]);
        let cons = Expr::app(
            Expr::const_(Name::from_components(["List", "cons"]), vec![Level::zero()]),
            char_type.clone(),
        );
        let mut list = Expr::app(
            Expr::const_(Name::from_components(["List", "nil"]), vec![Level::zero()]),
            char_type,
        );
        let of_nat = Expr::const_(char_of_nat, vec![]);
        // Reverse iteration builds a forward list without an intermediate
        // character array or a recursive host-stack walk. Charge generated
        // cells before allocation, including each Unicode scalar's Nat literal.
        for character in value.chars().rev() {
            for _ in 0..6 {
                self.meter.node()?;
            }
            let scalar = Expr::lit(Literal::Nat(NatLit::from_u64(u64::from(u32::from(
                character,
            )))));
            list = Expr::app(
                Expr::app(cons.clone(), Expr::app(of_nat.clone(), scalar)),
                list,
            );
        }
        Ok(Some(Expr::app(Expr::const_(string_of_list, vec![]), list)))
    }
}
