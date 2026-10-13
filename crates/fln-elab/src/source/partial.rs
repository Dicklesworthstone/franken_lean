//! Source partial definitions have a checked opaque interface and a separate
//! Partial mutual block. See the pin's Elab/PreDefinition/Main.lean
//! `addAndCompilePartial` and Basic.lean `addAndCompilePartialRec`. Neither a
//! logical inhabitant alone nor a recursive body alone is a source publication.
use super::*;
use fln_env::constants::ConstantInfo;
use std::collections::BTreeSet;
mod group;
pub use group::elaborate_group;
#[cfg(test)]
mod codegen_tests;

/// A complete partial-definition command and its deferred compilation effects.
/// The declarations are untrusted candidates until the caller's whole council
/// batch succeeds. Compilation metadata is recorded only on that successor.
pub struct ElaboratedPartial {
    declarations: Vec<Declaration>,
    noncomputable: BTreeSet<Name>,
    scope: SourceScope,
    budget: ElabBudget,
    kernel: Budget,
}

impl ElaboratedPartial {
    /// The entire atomic admission batch, including logical interfaces.
    pub fn declarations(&self) -> &[Declaration] {
        &self.declarations
    }

    /// Record supported, section-suppressed compilation failures on the actual
    /// admitted executable declarations, never on a recursive logical witness.
    ///
    /// Components are already in dependency order. Rechecking their executable
    /// references against the admitted environment propagates earlier failures
    /// without inventing temporary axioms or confusing erased proofs/types with
    /// runtime dependencies. Like `CoreM.compileDecls`, a failed mutual compiler
    /// unit marks every executable member. All work spends the original command
    /// budget; a failure exposes neither the partial successor nor a tag prefix.
    pub fn record_codegen(
        &self,
        admitted: &Environment,
    ) -> Result<Environment, NatDefinitionElabError> {
        if self.noncomputable.is_empty() {
            return Ok(admitted.clone());
        }
        if !self.scope.noncomputable_section {
            return Err(failure(SourceInferenceError::Scope));
        }
        let mut context = Context::scoped(admitted, self.kernel, &self.scope);
        context.txn.budget = self.budget.clone();
        context.validate_codegen_metadata()?;
        for declaration in &self.declarations {
            context.tick()?;
            let definitions = match declaration {
                Declaration::Defn(definition) => std::slice::from_ref(definition),
                Declaration::Mutual(definitions) => definitions.as_slice(),
                // This is the checked logical inhabitant, not executable code.
                Declaration::Opaque(_) => continue,
                _ => return Err(failure(SourceInferenceError::Scope)),
            };
            let mut failed = false;
            for definition in definitions {
                context.tick()?;
                // The API may not stamp an unrelated declaration under the
                // same name if handed a different successor by an embedder.
                if context.txn.env.find(&definition.base.name)
                    != Some(&ConstantInfo::Defn(definition.clone()))
                {
                    return Err(failure(SourceInferenceError::Scope));
                }
                failed |= self.noncomputable.contains(&definition.base.name);
            }
            if !failed {
                for definition in definitions {
                    context.level_params = definition.base.level_params.clone();
                    if context.check_definition_codegen(&Typed {
                        type_: definition.base.type_.clone(),
                        value: definition.value.clone(),
                    })? {
                        failed = true;
                        break;
                    }
                }
            }
            if failed {
                for definition in definitions {
                    context.tick()?;
                    context.txn.env =
                        crate::noncomputable::register(&context.txn.env, &definition.base.name)
                            .map_err(|error| match error {
                                crate::noncomputable::NoncomputableError::Limit => {
                                    failure(SourceInferenceError::ResourceLimit)
                                }
                                other => failure(SourceInferenceError::NoncomputableJournal(other)),
                            })?;
                }
            }
        }
        Ok(context.txn.env)
    }
}

#[derive(Clone, Default)]
pub(super) struct State {
    pub reference: Option<Reference>,
    pub group: Option<group::Group>,
}

#[derive(Clone)]
pub(super) struct Reference {
    pub name: Name,
    pub term: Typed,
    marker: FVarId,
}

/// Inspect only the modifier, leaving malformed declarations to normal parsing.
pub fn is_partial(syntax: &Syntax) -> bool {
    let Some(args) = syntax_args(syntax, &parser_kind(&["Command", "declaration"])) else {
        return false;
    };
    let Some(modifiers) = args
        .first()
        .and_then(|node| syntax_args(node, &parser_kind(&["Command", "declModifiers"])))
    else {
        return false;
    };
    modifiers
        .get(6)
        .is_some_and(|slot| validate_modifier(slot).is_ok())
}

fn syntax_args<'a>(syntax: &'a Syntax, expected: &Name) -> Option<&'a [Syntax]> {
    match syntax {
        Syntax::Node { kind, args, .. } if kind == expected => Some(args),
        _ => None,
    }
}

pub(super) fn validate_modifier(slot: &Syntax) -> Result<(), NatDefinitionElabError> {
    let [modifier] = expect_null_args(slot, "partial modifier")? else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "partial modifier",
        });
    };
    let [keyword] = expect_node(
        modifier,
        &parser_kind(&["Command", "partial"]),
        1,
        "partial modifier",
    )?
    else {
        return Err(failure(SourceInferenceError::Scope));
    };
    expect_atom(keyword, "partial", "partial modifier").map(|_| ())
}

/// Untrusted candidates, in admission order. The caller must admit the entire
/// batch through both checkers before publishing either half. The single-
/// declaration entry points deliberately retain their partial-modifier refusal.
pub fn elaborate(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<ElaboratedPartial, NatDefinitionElabError> {
    validate(syntax)?;
    let scope = scope.for_declaration(syntax)?;
    let mut context = Context::scoped(environment, kernel, &scope);
    context.partial = Some(State::default());
    let candidate = definition_in_context(syntax, &mut context)?;
    let Declaration::Mutual(ref definitions) = candidate else {
        // The pin uses its nonrecursive path when no self-reference survives.
        let mut noncomputable = BTreeSet::new();
        if context.noncomputable_definition {
            let Declaration::Defn(definition) = &candidate else {
                return Err(failure(SourceInferenceError::Scope));
            };
            noncomputable.insert(definition.base.name.clone());
        }
        return Ok(ElaboratedPartial {
            declarations: vec![candidate],
            noncomputable,
            scope,
            budget: context.txn.budget,
            kernel,
        });
    };
    let [implementation] = definitions.as_slice() else {
        return Err(failure(SourceInferenceError::Scope));
    };
    let noncomputable = if context.noncomputable_definition {
        BTreeSet::from([implementation.base.name.clone()])
    } else {
        BTreeSet::new()
    };
    let reference = context
        .partial
        .as_ref()
        .and_then(|state| state.reference.as_ref())
        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
    let name = reference.name.clone();
    let mut inhabitant_context = Context::scoped(environment, kernel, &scope);
    inhabitant_context.level_params = implementation.base.level_params.clone();
    // Both phases consume the same declaration budget, not independent fresh
    // allowances. The companion's original body is checked at batch admission.
    inhabitant_context.txn.budget = context.txn.budget.clone();
    let inhabitant = inhabitant_context.partial_inhabitant(&implementation.base.type_)?;
    let logical = Declaration::Opaque(fln_env::constants::OpaqueVal {
        base: ConstantVal {
            name: name.clone(),
            ..implementation.base.clone()
        },
        value: inhabitant,
        is_unsafe: false,
        all: vec![name],
    });
    Ok(ElaboratedPartial {
        declarations: vec![logical, candidate],
        noncomputable,
        scope,
        budget: inhabitant_context.txn.budget,
        kernel,
    })
}

fn validate(syntax: &Syntax) -> Result<(), NatDefinitionElabError> {
    let declaration = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "partial definition",
    )?;
    expect_node(
        &declaration[1],
        &parser_kind(&["Command", "definition"]),
        5,
        "partial def",
    )?;
    let modifiers = expect_node(
        &declaration[0],
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "declaration modifiers",
    )?;
    validate_modifier(&modifiers[6])?;
    // Attribute effects need a separate checked registration path. Do not
    // silently discard them or publish a noncomputable body as executable.
    for &index in &[1_usize, PROTECTED_SLOT, NONCOMPUTABLE_SLOT, 5] {
        expect_empty_null(&modifiers[index], "unattributed safe partial definition")?;
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
        let mut type_ = expected.clone().ok_or_else(|| {
            failure(SourceInferenceError::Recursion(
                recursion::RecursionError::ResultTypeRequired,
            ))
        })?;
        for parameter in parameters.iter().rev() {
            self.tick()?;
            type_ = type_
                .abstract_fvar(&parameter.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            type_ = Expr::forall_e(
                parameter.user_name.clone(),
                parameter.type_.clone(),
                type_,
                parameter.binder_info,
            );
        }
        if !matches!(self.whnf(&type_)?.node(), ExprNode::ForallE { .. }) {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "a function type for recursive partial def",
            });
        }
        let marker = FVarId(self.fresh_name()?);
        self.txn.lctx.add_param(
            marker.clone(),
            name.clone(),
            type_.clone(),
            BinderInfo::Default,
        );
        self.partial
            .as_mut()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?
            .reference = Some(Reference {
            name: name.clone(),
            marker: marker.clone(),
            term: Typed {
                value: Expr::fvar(marker),
                type_,
            },
        });
        self.term(syntax, expected)
    }

    pub(super) fn close_partial_reference(
        &mut self,
        term: &mut Typed,
        parameters: &[LocalDecl],
        captures: &[LocalDecl],
    ) -> Result<(), NatDefinitionElabError> {
        let Some(reference) = self
            .partial
            .as_ref()
            .and_then(|state| state.reference.clone())
        else {
            return Ok(());
        };
        let mut roots = vec![term.type_.clone(), term.value.clone()];
        for parameter in parameters {
            roots.push(self.instantiate(&parameter.type_)?);
        }
        let levels = self.declaration_levels(&roots)?;
        let mut executable = Expr::const_(
            Name::str(reference.name, "_unsafe_rec"),
            levels.into_iter().map(Level::param).collect(),
        );
        for capture in captures {
            self.tick()?;
            executable = Expr::app(executable, Expr::fvar(capture.id.clone()));
        }
        self.tick()?;
        let abstracted = term
            .value
            .abstract_fvar(&reference.marker, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        term.value = self.substitute(&abstracted, &executable)?;
        Ok(())
    }

    /// The logical witness is synthesized WITHOUT the recursive local. Open the
    /// complete telescope, making every parameter an Inhabited provider as in
    /// the pin's MkInhabitant.lean. Search Inhabited first, then Nonempty; no
    /// axiom, arbitrary zero value, or unsafe body may fill the logical half.
    fn partial_inhabitant(&mut self, type_: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let mut remaining = type_.clone();
        let mut parameters = Vec::new();
        loop {
            let normalized = self.whnf(&remaining)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = normalized.node()
            else {
                break;
            };
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                binder_name.clone(),
                binder_type.clone(),
                *binder_info,
            );
            parameters.push(self.txn.lctx.find(&id).expect("inserted parameter").clone());
            remaining = self.substitute(body, &Expr::fvar(id))?;
        }
        let parameter_context = self.txn.lctx.clone();
        for parameter in &parameters {
            self.tick()?;
            let type_of_type = self
                .known_type(&parameter.type_)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let level = self.sort_level(&Typed {
                value: parameter.type_.clone(),
                type_: type_of_type,
            })?;
            let instance_type = Expr::app(
                Expr::const_(Name::from_components(["Inhabited"]), vec![level.clone()]),
                parameter.type_.clone(),
            );
            let instance_value = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_components(["Inhabited", "mk"]), vec![level]),
                    parameter.type_.clone(),
                ),
                Expr::fvar(parameter.id.clone()),
            );
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_let(id.clone(), id.0.clone(), instance_type, instance_value);
        }
        let mut value = None;
        'strategies: for components in [&["default"][..], &["Classical", "ofNonempty"][..]] {
            if !self
                .txn
                .env
                .contains(&Name::from_components(components.iter().copied()))
            {
                continue;
            }
            let syntax = Syntax::Ident {
                info: fln_syntax::source::SourceInfo::None,
                raw_val: fln_syntax::source::ByteSpan::default(),
                // These are elaborator support constants, not user syntax.
                // Namespace/local declarations named `default` must not change
                // which inhabitant-synthesis operation is attempted.
                val: Name::from_components(
                    std::iter::once("_root_").chain(components.iter().copied()),
                ),
                preresolved: Vec::new(),
            };
            // Instance search uses `instances` transparency. A semireducible
            // return-type alias may hide an otherwise available witness. Try
            // every alias before unfolding it, including intermediate aliases
            // with their own instances; full whnf would skip those providers.
            // Exhaust this Inhabited path before trying Nonempty at the original
            // result type (the pin's MkInhabitantForAux? strategy order).
            let mut target = remaining.clone();
            loop {
                self.tick()?;
                let snapshot = self.clone();
                let attempt = self
                    .term(&syntax, Some(target.clone()))
                    .and_then(|term| self.finish(term));
                match attempt {
                    Ok(term) => {
                        value = Some(term.value);
                        break 'strategies;
                    }
                    Err(error)
                        if instances::nonmatch(&error)
                            || matches!(
                                error,
                                NatDefinitionElabError::Inference(
                                    SourceInferenceError::InstanceSynthesisRequired
                                        | SourceInferenceError::UnresolvedHoles { .. }
                                )
                            ) =>
                    {
                        let spent = self.txn.budget.heartbeats_consumed;
                        *self = snapshot;
                        self.txn.budget.heartbeats_consumed = spent;
                    }
                    Err(error) => return Err(error),
                }
                let reduced =
                    self.whnf_with_transparency(&target, UnificationTransparency::None, true)?;
                let Some(unfolded) = self.unfold_head_definition(&reduced)? else {
                    break;
                };
                target = unfolded;
            }
        }
        let mut value = value.ok_or(NatDefinitionElabError::UnexpectedSyntax {
            expected: "an inhabited result type for partial def",
        })?;
        // Close every synthetic provider as a let; unused providers are harmless
        // but still checked, and cannot leave their private free IDs in the value.
        let providers = self.txn.lctx.decls()[parameter_context.decls().len()..].to_vec();
        for provider in providers.into_iter().rev() {
            self.tick()?;
            value = value
                .abstract_fvar(&provider.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value = Expr::let_e(
                provider.user_name,
                self.instantiate(&provider.type_)?,
                self.instantiate(
                    provider
                        .value
                        .as_ref()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?,
                )?,
                value,
                false,
            );
        }
        for parameter in parameters.into_iter().rev() {
            self.tick()?;
            value = value
                .abstract_fvar(&parameter.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value = Expr::lam(
                parameter.user_name,
                self.instantiate(&parameter.type_)?,
                value,
                parameter.binder_info,
            );
        }
        self.require_resolved(&[value.clone()])?;
        Ok(value)
    }
}
