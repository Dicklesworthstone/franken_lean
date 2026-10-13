//! Source partial recursion is not a new logical reduction rule.
//!
//! Follow the pin's PreDefinition/Main.lean and Basic.lean: elaborate the body
//! against a local self header, close an inhabited opaque interface, then hand
//! the actual recursive body to ordinary mutual-Partial admission. The runtime
//! already validates this complete pair before selecting `._unsafe_rec`.
use super::*;
mod inhabitant;

#[derive(Clone)]
pub(super) struct State {
    pub(super) name: Name,
    pub(super) reference: Typed,
    marker: FVarId,
    body: Option<Typed>,
}

pub(super) fn modifier(slot: &Syntax) -> Result<bool, NatDefinitionElabError> {
    match expect_null_args(slot, "recursion modifier")? {
        [] => Ok(false),
        [modifier] => {
            let parts = expect_node(
                modifier,
                &parser_kind(&["Command", "partial"]),
                1,
                "partial modifier",
            )?;
            expect_atom(&parts[0], "partial", "partial keyword")?;
            Ok(true)
        }
        _ => Err(failure(SourceInferenceError::Scope)),
    }
}

/// No termination hint may be silently ignored by this lowering.
pub(super) fn check_termination(syntax: &Syntax) -> Result<(), NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Termination", "suffix"]),
        2,
        "partial definition termination suffix",
    )?;
    for part in parts {
        expect_empty_null(part, "no termination hints on a partial definition")?;
    }
    Ok(())
}

impl Context {
    pub(super) fn partial_definition_body(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let written_result = expected.clone();
        // When a result is inferred, read the written leading lambda telescope
        // to establish a callable self signature. A complete result annotation
        // already gives that signature: elaborate its lambdas normally with
        // self in scope, including recursive references in their annotations.
        // Never move a lambda across an effect or another expression.
        let mut recursive_parameters = parameters.to_vec();
        let (syntax, expected, lambdas) = if expected.is_none() {
            self.open_recursive_lambdas(syntax, expected, &mut recursive_parameters)?
        } else {
            (syntax, expected, Vec::new())
        };
        let expected = match expected {
            Some(expected) => expected,
            None => {
                // Infer the result from the actual selected body, never by
                // first elaborating a different body with an unknown self.
                // This hole predates the marker and cannot capture it.
                let sort = self.type_expected()?;
                self.hole(sort)?
            }
        };
        let mut full_type = self.instantiate(&expected)?;
        for local in recursive_parameters.iter().rev() {
            self.tick()?;
            full_type = Expr::forall_e(
                local.user_name.clone(),
                self.instantiate(&local.type_)?,
                full_type
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        let marker = FVarId(self.fresh_name()?);
        self.txn.lctx.add_param(
            marker.clone(),
            Name::anonymous(),
            full_type.clone(),
            BinderInfo::Default,
        );
        self.partial_definition = Some(State {
            name: name.clone(),
            reference: Typed {
                value: Expr::fvar(marker.clone()),
                type_: full_type.clone(),
            },
            marker: marker.clone(),
            body: None,
        });
        let body = self.term(syntax, Some(expected.clone()))?;
        let body = self.finish_open_universes(body)?;
        let body = self.close_recursive_lambdas(&lambdas, body)?;
        // A discarded tactic alternative is not a surviving recursive edge.
        // As at the pin, nonrecursive partial definitions remain ordinary defs.
        if !body
            .value
            .abstract_fvar(&marker, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?
            .has_loose_bvar(0)
        {
            self.partial_definition = None;
            return Ok(body);
        }
        // Nonrecursive partial declarations may be constants. Only an actual
        // surviving recursive edge imposes the pin's function-type restriction.
        if !matches!(self.whnf(&full_type)?.node(), ExprNode::ForallE { .. }) {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "a function type for recursive partial def",
            });
        }
        // Closing written lambdas restores their outer lexical scope, which
        // predates the private header. Retain that header while the recursive
        // body is finished and then replaced with its executable constant.
        if self.txn.lctx.find(&marker).is_none() {
            self.txn
                .lctx
                .add_param(marker, Name::anonymous(), full_type, BinderInfo::Default);
        }
        // The recursive body is retained even though it is not the logical
        // value. Both checkers must still check it against the closed signature.
        let mut roots: Vec<_> = parameters.iter().map(|local| local.type_.clone()).collect();
        roots.extend([body.value.clone(), body.type_.clone()]);
        let mut arguments = self.section_parameters(&roots, false)?;
        arguments.extend_from_slice(parameters);
        // The interface uses the written signature, not elaborated lambda
        // annotations that are merely convertible to it. Those annotations
        // can mention self and belong only to the actual recursive body.
        let expected = written_result.unwrap_or_else(|| body.type_.clone());
        self.partial_definition
            .as_mut()
            .expect("partial header")
            .body = Some(body);
        self.partial_inhabitant(&expected, &arguments)
    }
}

pub(super) fn extend_roots(context: &Context, roots: &mut Vec<Expr>) {
    if let Some(body) = context
        .partial_definition
        .as_ref()
        .and_then(|state| state.body.as_ref())
    {
        roots.extend([body.value.clone(), body.type_.clone()]);
    }
}

pub(super) fn executable_body(
    context: &mut Context,
    sections: &[LocalDecl],
    roots: &[Expr],
) -> Result<Option<Typed>, NatDefinitionElabError> {
    let Some(state) = context.partial_definition.clone() else {
        return Ok(None);
    };
    let Some(body) = state.body else {
        return Err(failure(SourceInferenceError::Scope));
    };
    let mut body = context.finish(body)?;
    let levels = context
        .declaration_levels(roots)?
        .into_iter()
        .map(Level::param)
        .collect();
    let mut reference = Expr::const_(Name::str(state.name, "_unsafe_rec"), levels);
    // Section parameters are captured, unlike the written recursive arguments.
    for local in sections {
        context.tick()?;
        reference = Expr::app(reference, Expr::fvar(local.id.clone()));
    }
    let abstracted = body
        .value
        .abstract_fvar(&state.marker, 0)
        .map_err(|_| failure(SourceInferenceError::Scope))?;
    body.value = context.substitute(&abstracted, &reference)?;
    Ok(Some(body))
}

pub(super) fn complete(
    context: &mut Context,
    base: ConstantVal,
    inhabitant: Expr,
    body: Expr,
) -> Result<Declaration, NatDefinitionElabError> {
    context.tick()?;
    if body.has_fvar() || body.has_loose_bvars() {
        return Err(failure(SourceInferenceError::Scope));
    }
    context.require_resolved(std::slice::from_ref(&body))?;
    let executable_name = Name::str(base.name.clone(), "_unsafe_rec");
    if context.txn.env.contains(&executable_name) {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "a fresh partial-definition executable companion",
        });
    }
    context
        .executable_companions
        .push(Declaration::Mutual(vec![DefinitionVal {
            base: ConstantVal {
                name: executable_name.clone(),
                ..base.clone()
            },
            value: body,
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Partial,
            all: vec![executable_name],
        }]));
    Ok(Declaration::Opaque(fln_env::constants::OpaqueVal {
        all: vec![base.name.clone()],
        base,
        value: inhabitant,
        is_unsafe: false,
    }))
}
