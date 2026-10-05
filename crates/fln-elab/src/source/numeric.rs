//! Numeric notation produces ordinary class applications, including the raw
//! mantissa/exponent arguments specified by the pinned `elabScientificLit`.
use super::*;

fn raw_nat(value: &BigNat) -> Expr {
    Expr::lit(Literal::Nat(literal_from_bignat(value)))
}

fn decode_scientific(spelling: &str) -> Result<(Expr, bool, Expr), NatDefinitionElabError> {
    use fln_syntax::literal::{LiteralKind, lex_literal};
    use fln_syntax::source::SourceText;
    let invalid = || NatDefinitionElabError::InvalidScientificLiteral;
    let text = SourceText::from_utf8(spelling.as_bytes()).map_err(|_| invalid())?;
    let token = lex_literal(&text, BytePos(0)).map_err(|_| invalid())?;
    if token.kind != LiteralKind::Scientific || token.extent.end().0 != spelling.len() {
        return Err(invalid());
    }
    let compact: String = spelling.chars().filter(|c| *c != '_').collect();
    let (mantissa, exponent) = match compact.find(['e', 'E']) {
        Some(index) => (&compact[..index], Some(&compact[index + 1..])),
        None => (compact.as_str(), None),
    };
    let decimals = mantissa
        .find('.')
        .map_or(0, |index| mantissa.len() - index - 1);
    let digits: String = mantissa.chars().filter(|c| *c != '.').collect();
    let mantissa = BigNat::from_decimal(&digits).ok_or_else(invalid)?;
    let decimals = BigNat::from_u64(u64::try_from(decimals).map_err(|_| invalid())?);
    let (negative, exponent) = match exponent {
        None => (true, decimals),
        Some(exponent) => {
            let (negative, digits) = match exponent.as_bytes().first() {
                Some(b'-') => (true, &exponent[1..]),
                Some(b'+') => (false, &exponent[1..]),
                _ => (false, exponent),
            };
            let exponent = BigNat::from_decimal(digits).ok_or_else(invalid)?;
            if negative {
                (true, exponent.add(&decimals))
            } else if exponent >= decimals {
                (false, exponent.sub(&decimals))
            } else {
                (true, decimals.sub(&exponent))
            }
        }
    };
    Ok((raw_nat(&mantissa), negative, raw_nat(&exponent)))
}

impl Context {
    pub(super) fn has_numeric_class(&self, class: &str) -> Result<bool, NatDefinitionElabError> {
        Ok(self
            .instance_registry()?
            .is_class(&Name::from_components([class])))
    }

    fn numeric_argument(
        &mut self,
        mut function: Typed,
        argument: Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        let signature = self.whnf(&function.type_)?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = signature.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let actual = self
            .known_type(&argument)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        self.constrain_type(&actual, binder_type)?;
        function.type_ = self.substitute(body, &argument)?;
        function.value = Expr::app(function.value, argument);
        Ok(function)
    }

    fn numeric_dictionary(&mut self, function: Typed) -> Result<Typed, NatDefinitionElabError> {
        let signature = self.whnf(&function.type_)?;
        let ExprNode::ForallE { binder_type, .. } = signature.node() else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let dictionary = self.instance_hole(binder_type.clone())?;
        self.numeric_argument(function, dictionary)
    }

    fn numeric_method(
        &mut self,
        class: &str,
        method: &str,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let function = self.constant(&Name::from_components([class, method]))?;
        let signature = self.whnf(&function.type_)?;
        let ExprNode::ForallE { binder_type, .. } = signature.node() else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let type_ = self.hole(binder_type.clone())?;
        if let Some(expected) = expected {
            self.constrain(&type_, expected)?;
        }
        self.numeric_argument(function, type_)
    }

    pub(super) fn numeric_literal(
        &mut self,
        syntax: &Syntax,
        expected: Option<&Expr>,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let Syntax::Node { kind, args, .. } = syntax else {
            return Ok(None);
        };
        let scientific = kind == &Name::from_components(["scientific"]);
        let natural = kind == &Name::from_components(["num"]);
        if !scientific && !natural {
            return Ok(None);
        }
        // The raw Nat fixture has no class environment. Its deliberately
        // separate entry point retains raw numerals until classes are admitted.
        if natural && !self.has_numeric_class("OfNat")? {
            return Ok(None);
        }
        let [Syntax::Atom { val: spelling, .. }] = args.as_slice() else {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "one numeric literal atom",
            });
        };
        if scientific {
            let (mantissa, negative, exponent) = decode_scientific(spelling)?;
            let function = self.numeric_method("OfScientific", "ofScientific", expected)?;
            let mut function = self.numeric_dictionary(function)?;
            for argument in [
                mantissa,
                Expr::const_(
                    Name::from_components(["Bool", if negative { "true" } else { "false" }]),
                    Vec::new(),
                ),
                exponent,
            ] {
                function = self.numeric_argument(function, argument)?;
            }
            Ok(Some(function))
        } else {
            let number = Expr::lit(decode_natural(spelling)?);
            let function = self.numeric_method("OfNat", "ofNat", expected)?;
            let function = self.numeric_argument(function, number)?;
            Ok(Some(self.numeric_dictionary(function)?))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scientific_components_match_the_pins_raw_natural_contract() {
        for (source, mantissa, negative, exponent) in [
            ("1.23", "123", true, "2"),
            ("121e100", "121", false, "100"),
            ("1.25e+2", "125", false, "0"),
            ("1.25E-2", "125", true, "4"),
            ("1.", "1", true, "0"),
            ("1.0e0", "10", true, "1"),
            ("1_2.3_4e5_6", "1234", false, "54"),
            ("0e18446744073709551616", "0", false, "18446744073709551616"),
        ] {
            assert_eq!(
                decode_scientific(source).unwrap(),
                (
                    raw_nat(&BigNat::from_decimal(mantissa).unwrap()),
                    negative,
                    raw_nat(&BigNat::from_decimal(exponent).unwrap())
                ),
                "{source}",
            );
        }
        for source in [
            "1", "1e", "1e-", "1..2", "1.foo", "1.2tail", "1.2_", ".5", "-1.0",
        ] {
            assert_eq!(
                decode_scientific(source),
                Err(NatDefinitionElabError::InvalidScientificLiteral),
                "{source}"
            );
        }
    }
}
