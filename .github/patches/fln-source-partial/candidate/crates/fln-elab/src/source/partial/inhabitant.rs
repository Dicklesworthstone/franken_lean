//! The logical witness search of the pin's PreDefinition/MkInhabitant.lean.
//! Parameters supply local Inhabited instances; function results open further
//! binders. Only exhausted instance search can select the Nonempty fallback.
use super::*;

enum Closure {
    Parameter(LocalDecl),
    Instance(LocalDecl),
}

fn no_instance(error: &NatDefinitionElabError) -> bool {
    matches!(
        error,
        NatDefinitionElabError::Inference(SourceInferenceError::InstanceSynthesisRequired)
    )
}

impl Context {
    pub(super) fn partial_inhabitant(
        &mut self,
        expected: &Expr,
        parameters: &[LocalDecl],
    ) -> Result<Typed, NatDefinitionElabError> {
        let snapshot = self.clone();
        let result = self.partial_inhabitant_strategy(expected, parameters, false);
        let result = match result {
            Err(error)
                if no_instance(&error)
                    && self
                        .txn
                        .env
                        .contains(&Name::from_components(["Classical", "ofNonempty"])) =>
            {
                let spent = self.txn.budget.heartbeats_consumed;
                *self = snapshot.clone();
                self.txn.budget.heartbeats_consumed = spent;
                self.partial_inhabitant_strategy(expected, parameters, true)
            }
            result => result,
        };
        // All generated locals are now bound in the witness. Do not let a
        // witness-only instance affect subsequent source elaboration.
        self.txn.lctx = snapshot.txn.lctx;
        result
    }

    fn partial_inhabitant_strategy(
        &mut self,
        expected: &Expr,
        parameters: &[LocalDecl],
        nonempty: bool,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut closures = Vec::new();
        for parameter in parameters {
            self.partial_argument_instance(parameter, &mut closures)?;
        }
        let mut target = self.instantiate(expected)?;
        let provider = Syntax::Ident {
            info: fln_syntax::source::SourceInfo::None,
            raw_val: fln_syntax::source::ByteSpan::default(),
            // A source parameter called `default` must not replace the pin's
            // generated global application.
            val: if nonempty {
                Name::from_components(["_root_", "Classical", "ofNonempty"])
            } else {
                Name::from_components(["_root_", "default"])
            },
            preresolved: Vec::new(),
        };
        let mut value = loop {
            self.tick()?;
            let snapshot = self.clone();
            let result = self
                .term(&provider, Some(target.clone()))
                .and_then(|value| self.finish_open_universes(value));
            match result {
                Ok(value) => break value.value,
                Err(error) if no_instance(&error) => {
                    let spent = self.txn.budget.heartbeats_consumed;
                    *self = snapshot;
                    self.txn.budget.heartbeats_consumed = spent;
                    let reduced = self.whnf(&target)?;
                    let ExprNode::ForallE {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } = reduced.node()
                    else {
                        return Err(error);
                    };
                    let id = FVarId(self.fresh_name()?);
                    let local = self
                        .txn
                        .lctx
                        .add_param(
                            id.clone(),
                            binder_name.clone(),
                            binder_type.clone(),
                            *binder_info,
                        )
                        .clone();
                    target = self.substitute(body, &Expr::fvar(id))?;
                    closures.push(Closure::Parameter(local.clone()));
                    self.partial_argument_instance(&local, &mut closures)?;
                }
                Err(error) => return Err(error),
            }
        };
        for closure in closures.into_iter().rev() {
            self.tick()?;
            let (local, instance) = match closure {
                Closure::Parameter(local) => (local, false),
                Closure::Instance(local) => (local, true),
            };
            let body = value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            if instance {
                if body.has_loose_bvar(0) {
                    value = Expr::let_e(
                        local.user_name,
                        self.instantiate(&local.type_)?,
                        self.instantiate(local.value.as_ref().expect("generated instance let"))?,
                        body,
                        false,
                    );
                }
            } else {
                value = Expr::lam(
                    local.user_name,
                    self.instantiate(&local.type_)?,
                    body,
                    local.binder_info,
                );
            }
        }
        Ok(Typed {
            value,
            type_: self.instantiate(expected)?,
        })
    }

    fn partial_argument_instance(
        &mut self,
        parameter: &LocalDecl,
        closures: &mut Vec<Closure>,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        let type_ = self.instantiate(&parameter.type_)?;
        let sort = self
            .known_type(&type_)?
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let sort = self.whnf(&sort)?;
        let ExprNode::Sort { level } = sort.node() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let instance_type = Expr::app(
            Expr::const_(Name::from_components(["Inhabited"]), vec![level.clone()]),
            type_.clone(),
        );
        let value = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_components(["Inhabited", "mk"]),
                    vec![level.clone()],
                ),
                type_,
            ),
            Expr::fvar(parameter.id.clone()),
        );
        let id = FVarId(self.fresh_name()?);
        let local = self
            .txn
            .lctx
            .add_let(id, Name::anonymous(), instance_type, value)
            .clone();
        closures.push(Closure::Instance(local));
        Ok(())
    }
}
