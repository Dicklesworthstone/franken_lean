//! An admitted recursor whose minors never use induction hypotheses is a case
//! split, even when its datatype is recursive. Remove only syntactically unused
//! hypothesis binders; never substitute a recursive computation or erase work.
use super::*;

impl Preparation<'_> {
    pub(in crate::runtime) fn case_only_minors(
        &mut self,
        shape: &records::Shape,
        minors: &[Expr],
    ) -> Result<Option<Vec<Expr>>, IngressError> {
        if shape.constructors.len() != minors.len() {
            return Ok(None);
        }
        let mut result = Vec::new();
        for (constructor, minor) in shape.constructors.iter().zip(minors) {
            self.tick()?;
            let mut body = minor.clone();
            let mut fields = Vec::new();
            let mut hypotheses = 0usize;
            for field in &constructor.fields {
                self.tick()?;
                while let ExprNode::MData { expr, .. } = body.node() {
                    self.tick()?;
                    body = expr.clone();
                }
                let ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body: next,
                    binder_info,
                } = body.node()
                else {
                    return Ok(None);
                };
                self.producer_depth(fields.len().saturating_add(1))?;
                reserve(&mut fields, self.limits.max_context_depth)?;
                fields.push((binder_name.clone(), binder_type.clone(), *binder_info));
                body = next.clone();
                if self
                    .recursive_field(field, std::slice::from_ref(&shape.source))?
                    .is_some()
                {
                    hypotheses = hypotheses.saturating_add(1);
                }
            }
            for _ in 0..hypotheses {
                self.tick()?;
                while let ExprNode::MData { expr, .. } = body.node() {
                    self.tick()?;
                    body = expr.clone();
                }
                let ExprNode::Lam { body: next, .. } = body.node() else {
                    return Ok(None);
                };
                if next.has_loose_bvar(0) {
                    return Ok(None);
                }
                // The argument is absent, including in dependent annotations.
                // Substitution merely closes the removed de Bruijn slot.
                body = self.substitution(next, &nat::literal(0))?;
            }
            for (label, domain, info) in fields.into_iter().rev() {
                self.tick()?;
                body = Expr::lam(label, domain, body, info);
            }
            reserve(&mut result, self.limits.max_lambda_bindings)?;
            result.push(body);
        }
        Ok(Some(result))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn ty(s: &str) -> Expr {
        Expr::const_(name(s), vec![])
    }
    fn b(i: u32) -> Expr {
        Expr::bvar(i).unwrap()
    }
    fn lam(label: &str, domain: Expr, body: Expr) -> Expr {
        Expr::lam(name(label), domain, body, BinderInfo::Default)
    }
    fn fixture() -> crate::Engine {
        let limits =
            crate::EngineAdmissionLimits::new(crate::Budget::for_stack_bytes(2 * 1024 * 1024));
        crate::Engine::with_source_seed(limits).unwrap().into_complete().unwrap()
            .check_source_files(&[b"inductive Branch where | leaf : Nat -> Branch | fork : Branch -> Branch -> Branch"], &KVMap::new(), crate::SourceCheckLimits::new(limits))
            .unwrap().into_complete().unwrap().engine
    }
    fn minors(body: Expr) -> Vec<Expr> {
        vec![
            lam("n", ty("Nat"), b(0)),
            lam(
                "left",
                ty("Branch"),
                lam(
                    "right",
                    ty("Branch"),
                    lam("lh", ty("Nat"), lam("rh", ty("Nat"), body)),
                ),
            ),
        ]
    }
    #[test]
    fn unused_hypotheses_close_their_slots_without_capturing_fields_or_outer_locals() {
        let engine = fixture();
        let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
        let shape = preparation.record_shape(&ty("Branch")).unwrap().unwrap();
        let body = Expr::app(Expr::app(b(4), b(3)), b(2));
        let output = preparation
            .case_only_minors(&shape, &minors(body))
            .unwrap()
            .unwrap();
        assert_eq!(
            output[1],
            lam(
                "left",
                ty("Branch"),
                lam(
                    "right",
                    ty("Branch"),
                    Expr::app(Expr::app(b(2), b(1)), b(0))
                )
            )
        );
    }
    #[test]
    fn a_used_hypothesis_even_in_an_annotation_keeps_real_recursion() {
        let engine = fixture();
        let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
        let shape = preparation.record_shape(&ty("Branch")).unwrap().unwrap();
        for body in [
            b(0),
            b(1),
            Expr::lam(name("x"), b(0), nat::literal(0), BinderInfo::Default),
        ] {
            assert!(
                preparation
                    .case_only_minors(&shape, &minors(body))
                    .unwrap()
                    .is_none()
            );
        }
        let mut strict = minors(nat::literal(0));
        strict[1] = Expr::let_e(
            name("paid"),
            ty("Nat"),
            nat::literal(1),
            strict[1].clone(),
            false,
        );
        assert!(
            preparation
                .case_only_minors(&shape, &strict)
                .unwrap()
                .is_none()
        );
        assert!(
            preparation
                .case_only_minors(&shape, &strict[..1])
                .unwrap()
                .is_none()
        );
    }
    #[test]
    fn case_only_inspection_is_bounded_and_does_not_publish_partial_metadata() {
        let engine = fixture();
        let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
        let shape = preparation.record_shape(&ty("Branch")).unwrap().unwrap();
        let input = minors(nat::literal(42));
        let expected = preparation
            .case_only_minors(&shape, &input)
            .unwrap()
            .unwrap();
        let mut stopped = Preparation::new(
            engine.environment(),
            IngressLimits {
                max_nodes: 1,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            stopped.case_only_minors(&shape, &input),
            Err(IngressError::ResourceLimit { .. })
        ));
        assert!(stopped.lambdas.is_empty() && stopped.variant_cases.is_empty());
        assert_eq!(
            Preparation::new(engine.environment(), IngressLimits::default())
                .case_only_minors(&shape, &input)
                .unwrap(),
            Some(expected)
        );
    }
}
