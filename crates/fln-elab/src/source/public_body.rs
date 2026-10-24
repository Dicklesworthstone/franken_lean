//! Public declaration headers and hidden implementations share one transaction,
//! but not a name-resolution world. These candidates carry no export authority.
use super::*;

/// Whether a declaration has an ordinary definition/opaque body. Instances
/// retain their header-dependent automatic-exposure policy in their own entry.
pub fn is_definition_body(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Command", "declaration"])
            && args.len() == 2
            && ["definition", "abbrev", "opaque"].iter().any(|form|
                args[1].kind() == Some(&parser_kind(&["Command", form]))))
}

/// Elaborate a public signature before entering its private implementation.
/// Inferred result types must still pass admission in the public predecessor;
/// no filtered environment or caller-provided axiom stands in for that check.
pub fn elaborate_public_definition(
    syntax: &Syntax,
    worlds: &TheoremWorlds<'_>,
    kernel: Budget,
) -> Result<ElaboratedDeclaration, NatDefinitionElabError> {
    let mut context = Context::public_definition(syntax, worlds, kernel)?;
    let declaration = definition_in_context(syntax, &mut context)?;
    let local_functions = context.lift_local_functions(&declaration)?;
    Ok(ElaboratedDeclaration {
        declaration,
        native_axioms: Vec::new(),
        equation_info: context.equation_info.take(),
        local_functions,
        irreducible: context.well_founded_definition,
        noncomputable: context.noncomputable_definition,
    })
}

/// Classify the body context of a complete public definition header without
/// elaborating a placeholder body. Inferred result types are not invented;
/// they remain obligations of ordinary admission, not this read-only query.
pub fn public_definition_header_is_hidden(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<bool, NatDefinitionElabError> {
    let scope = scope.for_declaration(syntax)?;
    if !is_definition_body(syntax) || !scope.exports_declaration() {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "a public definition header in a module file",
        });
    }
    probe_header_visibility(syntax, environment, kernel, &scope)
}

/// Retain authored binder domains and the optional result before elaborating
/// the body. Unlike theorem headers, data-header universes may be constrained
/// by the body. Only their checked assignments are instantiated at closure.
#[derive(Clone)]
pub(super) struct Header {
    parameters: Vec<LocalDecl>,
    sections: Vec<LocalDecl>,
    result: Option<Expr>,
}

impl Context {
    pub(super) fn public_definition(
        syntax: &Syntax,
        worlds: &TheoremWorlds<'_>,
        kernel: Budget,
    ) -> Result<Self, NatDefinitionElabError> {
        let scope = worlds.public_scope.for_declaration(syntax)?;
        if !is_definition_body(syntax) || !scope.exports_declaration() || scope.expose_definitions {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "a public definition with a hidden implementation",
            });
        }
        let mut context = Self::scoped(worlds.public, kernel, &scope);
        context.private_proof_body = Some((
            worlds.private.clone(),
            worlds.private_scope.instance_scopes.clone(),
        ));
        context.private_definition_body = true;
        Ok(context)
    }

    pub(super) fn enter_public_definition_body(
        &mut self,
        parameters: &[LocalDecl],
        result: Option<&Expr>,
    ) -> Result<(), NatDefinitionElabError> {
        if let Some(result) = result {
            let sort = self
                .known_type(result)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let sort = self.whnf(&sort)?;
            if matches!(sort.node(), ExprNode::Sort { level } if level.normalize().is_zero()) {
                // levelMVarToParamHeaders freezes every explicitly Prop-valued
                // header, not just theorems. A proof body cannot specialize it.
                let mut roots: Vec<_> = self
                    .source_scope
                    .variables
                    .locals()
                    .decls()
                    .iter()
                    .chain(parameters)
                    .map(|local| local.type_.clone())
                    .collect();
                roots.push(result.clone());
                self.generalize_declaration_universes(&roots)?;
            }
        }
        self.public_definition_header = Some(Header {
            parameters: parameters.to_vec(),
            sections: self.source_scope.variables.locals().decls().to_vec(),
            result: result.cloned(),
        });
        self.private_definition_body = false;
        self.enter_private_proof()
    }
}

impl Header {
    pub(super) fn close(
        &self,
        context: &mut Context,
        selected: &[LocalDecl],
        inferred_result: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        // Instantiate before abstraction: an inferred type hole may now be a
        // section local. Abstracting the hole itself would let that free local
        // escape when the final candidate is instantiated.
        let mut type_ = context.instantiate(self.result.as_ref().unwrap_or(inferred_result))?;
        for local in self.parameters.iter().rev() {
            context.tick()?;
            type_ = Expr::forall_e(
                local.user_name.clone(),
                context.instantiate(&local.type_)?,
                type_
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        let selected: std::collections::HashSet<_> =
            selected.iter().map(|local| &local.id).collect();
        let mut count = 0;
        for local in self.sections.iter().rev() {
            context.tick()?;
            if selected.contains(&local.id) {
                count += 1;
                type_ = Expr::forall_e(
                    local.user_name.clone(),
                    context.instantiate(&local.type_)?,
                    type_
                        .abstract_fvar(&local.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    local.binder_info,
                );
            }
        }
        if count != selected.len() || type_.has_fvar() || type_.has_loose_bvars() {
            return Err(failure(SourceInferenceError::Scope));
        }
        Ok(type_)
    }
}
