//! The unary, right-nested `PSigma` construction from `Meta.ArgsPacker`.
//! Every constructor and eliminator application uses the admitted declaration
//! and the ordinary typed application path. A source parameter is never
//! rewritten into a captured projection while its body is being elaborated.
use super::*;

impl Context {
    fn packing_apply(
        &mut self,
        name: &[&str],
        arguments: impl IntoIterator<Item = Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut function = self.constant(&Name::from_components(name.iter().copied()))?;
        for value in arguments {
            self.tick()?;
            let type_ = self
                .known_type(&value)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            function = self.match_apply(function, Typed { value, type_ })?;
        }
        Ok(function)
    }

    /// `Unary.packType`: the last argument is the tail, so a unary function
    /// keeps its original domain and no artificial Unit field is introduced.
    pub(super) fn well_founded_domain(
        &mut self,
        parameters: &[LocalDecl],
    ) -> Result<Expr, NatDefinitionElabError> {
        let Some((last, prefix)) = parameters.split_last() else {
            return Err(error(RecursionError::WellFoundedArgumentRequired));
        };
        let mut domain = self.instantiate(&last.type_)?;
        for parameter in prefix.iter().rev() {
            self.tick()?;
            let type_ = self.instantiate(&parameter.type_)?;
            let family = Expr::lam(
                parameter.user_name.clone(),
                type_.clone(),
                domain
                    .abstract_fvar(&parameter.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
            domain = self.packing_apply(&["PSigma"], [type_, family])?.value;
        }
        self.instantiate(&domain)
    }

    fn sigma_parts(&mut self, domain: &Expr) -> Result<(Expr, Expr), NatDefinitionElabError> {
        let domain = self.whnf(domain)?;
        let (head, arguments) = operators::spine(&domain);
        if !matches!(head.node(), ExprNode::Const { name, .. }
            if name == &Name::from_components(["PSigma"]))
            || arguments.len() != 2
        {
            return Err(failure(SourceInferenceError::ExpectedType));
        }
        Ok((arguments[0].clone(), arguments[1].clone()))
    }

    /// `Unary.pack`: follow this encoding's arity, never the apparent shape of
    /// a user argument whose own type might also happen to be PSigma.
    pub(super) fn pack_well_founded_arguments(
        &mut self,
        domain: &Expr,
        arguments: &[Expr],
    ) -> Result<Typed, NatDefinitionElabError> {
        let Some((last, prefix)) = arguments.split_last() else {
            return Err(error(RecursionError::WellFoundedArgumentRequired));
        };
        let mut tail_type = domain.clone();
        let mut layers = Vec::new();
        for argument in prefix {
            self.tick()?;
            let (type_, family) = self.sigma_parts(&tail_type)?;
            let family_whnf = self.whnf(&family)?;
            let ExprNode::Lam { body, .. } = family_whnf.node() else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            tail_type = self.substitute(body, argument)?;
            layers.push((type_, family, argument.clone()));
        }
        let mut packed = Typed {
            value: last.clone(),
            type_: self
                .known_type(last)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?,
        };
        self.constrain_type(&packed.type_, &tail_type)?;
        for (type_, family, argument) in layers.into_iter().rev() {
            self.tick()?;
            packed =
                self.packing_apply(&["PSigma", "mk"], [type_, family, argument, packed.value])?;
        }
        self.constrain_type(&packed.type_, domain)?;
        Ok(packed)
    }

    /// `Unary.mkTupleElems`, used in motives only. The source body retains the
    /// original argument locals and is subsequently closed by casesOn minors.
    fn packed_substitution(
        &mut self,
        expression: &Expr,
        parameters: &[LocalDecl],
        packed: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut result = expression.clone();
        let mut tail = packed.clone();
        for (index, parameter) in parameters.iter().enumerate() {
            self.tick()?;
            let value = if index + 1 == parameters.len() {
                tail.clone()
            } else {
                Expr::proj(Name::from_components(["PSigma"]), 0, tail.clone())
            };
            result = result
                .abstract_fvar(&parameter.id, 0)
                .and_then(|body| body.subst_loose(0, &[value]))
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            tail = Expr::proj(Name::from_components(["PSigma"]), 1, tail);
        }
        Ok(result)
    }

    pub(super) fn well_founded_motive(
        &mut self,
        parameters: &[LocalDecl],
        domain: &Expr,
        result_type: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let name = if parameters.len() == 1 {
            parameters[0].user_name.clone()
        } else {
            self.fresh_name()?
        };
        let id = FVarId(self.fresh_name()?);
        let body = self.packed_substitution(result_type, parameters, &Expr::fvar(id.clone()))?;
        Ok(Expr::lam(
            name,
            domain.clone(),
            body.abstract_fvar(&id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        ))
    }

    fn packing_lambda(
        &mut self,
        local: &LocalDecl,
        body: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        let domain = self.instantiate(&local.type_)?;
        Ok(Typed {
            value: Expr::lam(
                local.user_name.clone(),
                domain.clone(),
                body.value
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            ),
            type_: Expr::forall_e(
                local.user_name.clone(),
                domain,
                body.type_
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            ),
        })
    }

    /// `Unary.uncurry` and the continuation specialization in
    /// `WF.processPSigmaCasesOn`. Build the nested cases iteratively; each
    /// minor closes the actual source locals, including their dependent types.
    pub(super) fn uncurry_well_founded_value(
        &mut self,
        parameters: &[LocalDecl],
        value: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        if parameters.len() == 1 {
            return self.packing_lambda(&parameters[0], value);
        }
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut tails = Vec::new();
            for index in 0..parameters.len().saturating_sub(1) {
                self.tick()?;
                let type_ = self.well_founded_domain(&parameters[index..])?;
                let name = self.fresh_name()?;
                let id = FVarId(name.clone());
                self.txn
                    .lctx
                    .add_param(id.clone(), name, type_, BinderInfo::Default);
                tails.push(
                    self.txn
                        .lctx
                        .find(&id)
                        .expect("inserted packed argument")
                        .clone(),
                );
            }
            let Some(last) = parameters.last() else {
                return Err(error(RecursionError::WellFoundedArgumentRequired));
            };
            tails.push(last.clone());
            let result_type = value.type_.clone();
            let mut body = value;
            for index in (0..parameters.len() - 1).rev() {
                self.tick()?;
                let tail = &tails[index];
                let motive =
                    self.well_founded_motive(&parameters[index..], &tail.type_, &result_type)?;
                let minor = self.packing_lambda(&tails[index + 1], body)?;
                let minor = self.packing_lambda(&parameters[index], minor)?;
                let (type_, family) = self.sigma_parts(&tail.type_)?;
                body = self.packing_apply(
                    &["PSigma", "casesOn"],
                    [
                        type_,
                        family,
                        motive,
                        Expr::fvar(tail.id.clone()),
                        minor.value,
                    ],
                )?;
            }
            self.packing_lambda(&tails[0], body)
        })();
        self.txn.lctx = saved;
        result
    }
}
