//! Recover the original field type, not its erased runtime representation.
//! Dependent proof predicates use syntactic projections of the original receiver;
//! no receiver is evaluated here. Classification must precede representation.
use super::*;

impl Preparation<'_> {
    pub(in crate::runtime) fn original_projection_type(
        &mut self,
        receiver_type: &Expr,
        structure: &Name,
        index: u64,
        receiver: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        let source = self.normalize_type(receiver_type)?;
        let (head, parameters) = self.spine(&source)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(family)) = self.environment.find(name) else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.is_rec
            || family.num_indices != 0
            || family.ctors.len() != 1
            || family.num_params as usize != parameters.len()
            || family.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        // A second preparation pass may see a private projection key, but it
        // must be bound to this exact previously discovered source family.
        if name != structure
            && self.data_shapes.get(&source).map(|shape| &shape.name) != Some(structure)
        {
            return Err(unsupported("projection receiver family mismatch"));
        }
        let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(&family.ctors[0]) else {
            return Ok(None);
        };
        if ctor.is_unsafe
            || ctor.induct != *name
            || ctor.num_params != family.num_params
            || ctor.base.level_params != family.base.level_params
        {
            return Ok(None);
        }
        if index >= u64::from(ctor.num_fields) {
            return Err(unsupported(
                "projection field outside constructor telescope",
            ));
        }
        let mut type_ =
            self.universe_instance(&ctor.base.type_, &ctor.base.level_params, levels)?;
        for parameter in &parameters {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE { body, .. } = normal.node() else {
                return Ok(None);
            };
            type_ = self.substitution(body, parameter)?;
        }
        for field in 0..=index {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            if field == index {
                return Ok(Some(binder_type.clone()));
            }
            let projection = Expr::proj(name.clone(), field, receiver.clone());
            type_ = self.substitution(body, &projection)?;
        }
        Ok(None)
    }
}
