//! Runtime elimination of checked, nonrecursive singleton propositions.
//! Their major and constructor fields are proofs, so they have no data layout.
//! Apply the admitted recursor rule to inert proof slots; never manufacture a
//! constructor value or change the logical declaration sent to either checker.
use super::*;

impl Preparation<'_> {
    pub(in crate::runtime) fn singleton_proof_recursor(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if !self.proof_erasure_available() {
            return Ok(None);
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(name) else {
            return Ok(None);
        };
        if rec.is_unsafe
            || rec.all.len() != 1
            || rec.num_motives != 1
            || rec.num_minors != 1
            || rec.num_indices != 0
            || rec.rules.len() != 1
            || levels.len() != rec.base.level_params.len()
            || levels
                .iter()
                .any(|level| level.has_mvar() || level.has_param())
        {
            return Ok(None);
        }
        let arity = (rec.num_params as usize)
            .checked_add(3)
            .ok_or_else(|| unsupported("singleton proof recursor arity"))?;
        if args.len() != arity {
            return Ok(None);
        }
        let Some(ConstantInfo::Induct(family)) = self.environment.find(&rec.all[0]) else {
            return Ok(None);
        };
        let [constructor] = family.ctors.as_slice() else {
            return Ok(None);
        };
        let rule = &rec.rules[0];
        let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(constructor) else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.is_rec
            || family.is_reflexive
            || family.num_nested != 0
            || family.all != rec.all
            || family.base.name != rec.all[0]
            || family.num_params != rec.num_params
            || family.num_indices != 0
            || ctor.is_unsafe
            || ctor.induct != family.base.name
            || ctor.cidx != 0
            || ctor.num_params != family.num_params
            || ctor.base.level_params != family.base.level_params
            || rule.ctor != *constructor
            || rule.nfields != ctor.num_fields
        {
            return Ok(None);
        }
        // Recover the major's logical family from the checked telescope. Its
        // runtime operand is already erased, so inspecting that operand cannot
        // establish whether this was a proposition or an ordinary data record.
        let mut type_ = self.universe_instance(&rec.base.type_, &rec.base.level_params, levels)?;
        for argument in &args[..arity - 1] {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE { body, .. } = normal.node() else {
                return Ok(None);
            };
            type_ = self.substitution(body, argument)?;
        }
        let normal = self.type_head(&type_)?;
        let ExprNode::ForallE {
            binder_type: major_type,
            ..
        } = normal.node()
        else {
            return Ok(None);
        };
        if !self.proposition_type(major_type, &[])? {
            return Ok(None);
        }
        let (major, parameters) = self.spine(major_type)?;
        let ExprNode::Const {
            name: major_name,
            levels: family_levels,
        } = major.node()
        else {
            return Ok(None);
        };
        if major_name != &family.base.name
            || family_levels.len() != family.base.level_params.len()
            || parameters.len() != family.num_params as usize
        {
            return Ok(None);
        }
        let mut constructor_type =
            self.universe_instance(&ctor.base.type_, &ctor.base.level_params, family_levels)?;
        for parameter in &parameters {
            self.tick()?;
            let normal = self.type_head(&constructor_type)?;
            let ExprNode::ForallE { body, .. } = normal.node() else {
                return Ok(None);
            };
            constructor_type = self.substitution(body, parameter)?;
        }
        // Only proof fields may disappear. In particular, an existential's
        // data witness and recursive proof fields must retain their existing
        // refusal/recursion paths. Keep dependent proof domains in their
        // original telescope while classifying each field.
        let mut fields = Vec::new();
        for _ in 0..ctor.num_fields {
            self.tick()?;
            let normal = self.type_head(&constructor_type)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            if !self.proposition_type(binder_type, &fields)? {
                return Ok(None);
            }
            self.push_proof_local(&mut fields, binder_type.clone())?;
            constructor_type = body.clone();
        }
        // Execute the actual admitted rule, not a name-based assumption about
        // its branch. The parameter/motive/minor prefix remains unchanged;
        // its proof field arguments use the compiler's existing inert slots.
        let mut reduced = self.universe_instance(&rule.rhs, &rec.base.level_params, levels)?;
        for argument in args[..arity - 1].iter().cloned().chain(std::iter::repeat_n(
            erased_value(),
            ctor.num_fields as usize,
        )) {
            self.tick()?;
            let ExprNode::Lam { body, .. } = reduced.node() else {
                return Ok(None);
            };
            reduced = self.substitution(body, &argument)?;
        }
        Ok(Some(reduced))
    }
}
