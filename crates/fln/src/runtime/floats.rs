//! Lower closed scientific literals only after both checking engines admitted
//! the exact seed declaration. The checked kernel expression is never changed.
use super::*;
use fln_core::expr::NatLit;
use fln_vm::scientific::{ScientificFloatWidth, scientific_float_bits};

impl Preparation<'_> {
    /// Referencing a verified primitive function executes none of its body.
    /// This permits ordinary checked dictionary constructors to store native
    /// methods while applications of those methods still execute in the VM.
    pub(super) fn inert_native_function(
        &mut self,
        expression: &Expr,
    ) -> Result<bool, IngressError> {
        let ExprNode::Const {
            name: callee,
            levels,
        } = expression.node()
        else {
            return Ok(false);
        };
        if !levels.is_empty() {
            return Ok(false);
        }
        if executable_intrinsic_binding(self.environment, callee, &mut self.visited, self.limits)?
            .is_some()
        {
            return Ok(true);
        }
        if callee != &name("Float.ofScientific") && callee != &name("Float32.ofScientific") {
            return Ok(false);
        }
        Ok(matches!(
            (self.environment.find(callee), fln_elab::seed::float_intrinsic_seed_declaration(callee)),
            (Some(ConstantInfo::Axiom(actual)), Some(Declaration::Axiom(expected))) if actual == &expected
        ))
    }

    fn scientific_nat_literal(&mut self, input: &Expr) -> Result<Option<NatLit>, IngressError> {
        let mut value = input.clone();
        loop {
            self.tick()?;
            match value.node() {
                ExprNode::Lit {
                    literal: Literal::Nat(number),
                } => return Ok(Some(number.clone())),
                ExprNode::MData { expr, .. } => value = expr.clone(),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    let Some(field) = self.static_projection(struct_name, *idx, expr)? else {
                        return Ok(None);
                    };
                    value = field;
                }
                ExprNode::App { .. } => {
                    let (head, arguments) = self.spine(&value)?;
                    let Some(projected) = self.projection_call(&head, &arguments)? else {
                        return Ok(None);
                    };
                    value = projected;
                }
                _ => return Ok(None),
            }
        }
    }

    pub(super) fn float_literal(
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
        if !levels.is_empty() {
            return Ok(None);
        }
        let spelling = callee.to_display_string();
        if matches!(
            spelling.as_str(),
            "Float.ofNat" | "Float32.ofNat" | "Nat.toFloat" | "Nat.toFloat32"
        ) && arguments.len() == 1
        {
            let Some(number) = self.scientific_nat_literal(&arguments[0])? else {
                return Ok(None);
            };
            // Expose the actual checked body rather than assuming anything
            // about its dictionary or the definitions it references. Those
            // dependencies must still reduce to the canonical opaque primitive.
            if let (Some(ConstantInfo::Defn(actual)), Some(Declaration::Defn(expected))) = (
                self.environment.find(callee),
                fln_elab::seed::float_intrinsic_seed_declaration(callee),
            ) && actual == &expected
                && let ExprNode::Lam { body, .. } = actual.value.node()
            {
                return self
                    .substitution(body, &Expr::lit(Literal::Nat(number)))
                    .map(Some);
            }
            return Ok(None);
        }
        let width = match spelling.as_str() {
            "Float.ofScientific" => ScientificFloatWidth::Float,
            "Float32.ofScientific" => ScientificFloatWidth::Float32,
            _ => return Ok(None),
        };
        if arguments.len() != 3 {
            return Ok(None);
        }
        let Some(expected) = fln_elab::seed::float_intrinsic_seed_declaration(callee) else {
            return Err(unsupported("scientific conversion seed"));
        };
        let canonical = match (self.environment.find(callee), expected) {
            (Some(ConstantInfo::Axiom(actual)), Declaration::Axiom(expected)) => {
                actual == &expected
            }
            (Some(ConstantInfo::Defn(actual)), Declaration::Defn(expected)) => actual == &expected,
            _ => false,
        };
        if !canonical {
            return Err(unsupported("noncanonical scientific conversion"));
        }
        let Some(mantissa) = self.scientific_nat_literal(&arguments[0])? else {
            return Ok(None);
        };
        let (negative_exponent, exponent) = {
            let ExprNode::Const { name: sign, levels } = arguments[1].node() else {
                return Ok(None);
            };
            if !levels.is_empty() {
                return Ok(None);
            }
            let Some(sign) = source_scalar_constructor_binding(self.environment, sign) else {
                return Err(unsupported("noncanonical scientific exponent sign"));
            };
            let Some(exponent) = self.scientific_nat_literal(&arguments[2])? else {
                return Ok(None);
            };
            (sign.value, exponent)
        };
        let (float, integer) = match width {
            ScientificFloatWidth::Float => ("Float.ofBits", "UInt64.ofNat"),
            ScientificFloatWidth::Float32 => ("Float32.ofBits", "UInt32.ofNat"),
        };
        if source_intrinsic_binding(self.environment, &name(float)).is_none()
            || source_intrinsic_binding(self.environment, &name(integer)).is_none()
        {
            return Err(unsupported("noncanonical scientific bit conversion"));
        }
        self.tick()?;
        // Intermediate exact arithmetic is bounded by the same byte ceiling
        // as executable literal payloads. The helper checks before allocation.
        // Ordinary finite/subnormal IEEE literals need fewer than 100 limbs.
        // This explicit bounded slice caps uninterruptible bignum arithmetic
        // independently of the much larger aggregate source literal budget.
        const MAX_SCIENTIFIC_LIMBS: usize = 4096;
        let max_bytes = self
            .limits
            .max_literal_bytes
            .min(MAX_SCIENTIFIC_LIMBS * std::mem::size_of::<u64>());
        let max_limbs = max_bytes / std::mem::size_of::<u64>();
        let bits = scientific_float_bits(
            mantissa.limbs_le(),
            negative_exponent,
            exponent.limbs_le(),
            width,
            max_limbs,
        )
        .map_err(|_| IngressError::ResourceLimit {
            resource: IngressResource::LiteralBytes,
            limit: max_bytes,
            observed: max_bytes.saturating_add(1),
        })?;
        Ok(Some(Expr::app(
            Expr::const_(name(float), vec![]),
            Expr::app(
                Expr::const_(name(integer), vec![]),
                Expr::lit(Literal::Nat(NatLit::from_u64(bits))),
            ),
        )))
    }
}
