//! Empty elimination is a non-returning runtime call, not a fabricated inhabitant.
//! Recognizers run only after both checkers have admitted the original source.
use super::*;
use fln_comp::ingress::EmptyCaseBinding;

impl Preparation<'_> {
    fn check_false_family(&mut self) -> Result<(), IngressError> {
        if self.false_family_checked {
            return Ok(());
        }
        let Declaration::Inductive(block) = fln_elab::seed::false_seed_declaration() else {
            return Err(unsupported("empty proposition seed"));
        };
        for expected in &block.types {
            self.tick()?;
            if !matches!(self.environment.find(&expected.base.name),
                Some(ConstantInfo::Induct(actual)) if actual == expected)
            {
                return Err(unsupported("noncanonical empty proposition"));
            }
        }
        for expected in &block.recursors {
            self.tick()?;
            if !matches!(self.environment.find(&expected.base.name),
                Some(ConstantInfo::Rec(actual)) if actual == expected)
            {
                return Err(unsupported("noncanonical empty recursor"));
            }
        }
        self.false_family_checked = true;
        Ok(())
    }

    fn empty_name(&mut self, major: ValueType, result: ValueType) -> Result<Name, IngressError> {
        for case in &self.empty_cases {
            charge_catalog_node(&mut self.visited, self.limits)?;
            if case.major == major && case.result == result {
                return Ok(case.name.clone());
            }
        }
        let id = u64::try_from(self.empty_cases.len())
            .map_err(|_| unsupported("empty case identity"))?;
        let name = Name::num(name("_fln_runtime_empty_case"), id);
        if self.environment.contains(&name) {
            return Err(unsupported("runtime empty case name collision"));
        }
        reserve(&mut self.empty_cases, self.limits.fir.max_functions)?;
        self.empty_cases.push(EmptyCaseBinding {
            name: name.clone(),
            major,
            result,
        });
        Ok(name)
    }

    pub(super) fn empty_recursor(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: callee,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(callee) else {
            return Ok(None);
        };
        if rec.is_unsafe
            || rec.k
            || rec.all.len() != 1
            || rec.num_motives != 1
            || rec.num_minors != 0
            || !rec.rules.is_empty()
            || levels.len() != rec.base.level_params.len()
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Induct(family)) = self.environment.find(&rec.all[0]) else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.is_rec
            || family.is_reflexive
            || family.num_nested != 0
            || !family.ctors.is_empty()
            || family.all != rec.all
            || family.base.name != rec.all[0]
            || family.num_params != rec.num_params
            || family.num_indices != rec.num_indices
        {
            return Ok(None);
        }
        if callee == &name("False.rec") {
            self.check_false_family()?;
        }
        let arity = (rec.num_params as usize)
            .checked_add(rec.num_indices as usize)
            .and_then(|n| n.checked_add(2))
            .ok_or_else(|| unsupported("empty recursor arity"))?;
        if args.len() < arity {
            return Ok(None);
        }
        let mut type_ = self.universe_instance(&rec.base.type_, &rec.base.level_params, levels)?;
        let mut bindings = Vec::new();
        let mut major_type = None;
        for (index, argument) in args[..arity].iter().enumerate() {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Err(unsupported("empty recursor telescope"));
            };
            if index == arity - 1 {
                let domain = self.type_head(binder_type)?;
                let (head, arguments) = self.spine(&domain)?;
                if !matches!(head.node(), ExprNode::Const { name, levels }
                    if name == &family.base.name && levels.len() == family.base.level_params.len())
                    || arguments.len() != arity - 2
                {
                    return Err(unsupported("empty recursor major family"));
                }
            }
            if !self.type_parameter(binder_type)? {
                let runtime_type = self.erase_runtime_type(binder_type)?;
                let value_type = self
                    .value_type(&runtime_type)?
                    .ok_or_else(|| unsupported("empty recursor argument representation"))?;
                if index == arity - 1 {
                    major_type = Some(value_type);
                }
                reserve(&mut bindings, self.limits.max_context_depth)?;
                bindings.push((runtime_type, argument.clone()));
            }
            type_ = self.substitution(body, argument)?;
        }
        let major_type =
            major_type.ok_or_else(|| unsupported("empty recursor major representation"))?;
        if !matches!(major_type, ValueType::Bool | ValueType::Constructor) {
            return Err(unsupported("empty recursor major representation"));
        }
        // Emptiness comes from the admitted zero-constructor family, not from
        // a static approximation of an ordinary, potentially inhabited type.
        let result_type = self.erase_runtime_type(&type_)?;
        let result = self
            .value_type(&result_type)?
            .ok_or_else(|| unsupported("empty elimination result representation"))?;
        let name = self.empty_name(major_type, result)?;
        let mut value = Expr::app(
            Expr::const_(name, vec![]),
            Expr::bvar(0).map_err(|_| unsupported("empty major scope"))?,
        );
        let depth =
            u32::try_from(bindings.len()).map_err(|_| unsupported("empty argument depth"))?;
        if args.len() > arity {
            // The non-returning call precedes evaluation of suffix arguments,
            // even when its nominal result is a callback.
            let mut applied = Expr::bvar(0).map_err(|_| unsupported("empty result scope"))?;
            let lifted = depth
                .checked_add(1)
                .ok_or_else(|| unsupported("empty result depth"))?;
            for argument in &args[arity..] {
                self.tick()?;
                applied = Expr::app(applied, self.lift(argument, lifted)?);
            }
            value = Expr::let_e(
                Name::anonymous(),
                self.lift(&result_type, depth)?,
                value,
                applied,
                false,
            );
        }
        // Parameters, indices and the major preserve their ordinary source
        // evaluation order. Only static types/motives and checked proofs erase.
        for (index, (type_, init)) in bindings.into_iter().enumerate().rev() {
            self.tick()?;
            let index = u32::try_from(index).map_err(|_| unsupported("empty argument scope"))?;
            value = Expr::let_e(
                Name::anonymous(),
                self.lift(&type_, index)?,
                self.lift(&init, index)?,
                value,
                false,
            );
        }
        Ok(Some(value))
    }
}

#[cfg(test)]
mod tests;
