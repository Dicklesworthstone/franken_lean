//! Source partial definitions have a checked opaque interface and a separate
//! Partial mutual block. See the pin's Elab/PreDefinition/Main.lean
//! `addAndCompilePartial` and Basic.lean `addAndCompilePartialRec`. Neither a
//! logical inhabitant alone nor a recursive body alone is a source publication.
use super::*;
use fln_env::constants::ConstantInfo;
use std::collections::BTreeSet;
mod group;
mod inhabitant;
pub use group::{elaborate_group, elaborate_ordinary_group, is_ordinary_group_member};
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
    /// Both forms elaborate recursion against private typed locals. Only
    /// `partial` subsequently needs a safe inhabited logical interface.
    pub kind: Kind,
    pub reference: Option<Reference>,
    pub group: Option<group::Group>,
}

#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(super) enum Kind {
    #[default]
    Partial,
    Unsafe,
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

/// Classify an unsafe `def` for mutual admission without dropping its syntax.
/// This is not validation: the complete modifier/header/body checks still run.
pub fn is_unsafe_definition(syntax: &Syntax) -> bool {
    let Some(args) = syntax_args(syntax, &parser_kind(&["Command", "declaration"])) else {
        return false;
    };
    if args.get(1).and_then(Syntax::kind) != Some(&parser_kind(&["Command", "definition"])) {
        return false;
    }
    args.first()
        .and_then(|node| syntax_args(node, &parser_kind(&["Command", "declModifiers"])))
        .and_then(|modifiers| modifiers.get(5))
        .is_some_and(|slot| validate_unsafe_modifier(slot).is_ok())
}

pub(super) fn validate_unsafe_modifier(slot: &Syntax) -> Result<(), NatDefinitionElabError> {
    let [modifier] = expect_null_args(slot, "unsafe modifier")? else {
        return Err(failure(SourceInferenceError::Scope));
    };
    let [keyword] = expect_node(
        modifier,
        &parser_kind(&["Command", "unsafe"]),
        1,
        "unsafe modifier",
    )?
    else {
        return Err(failure(SourceInferenceError::Scope));
    };
    expect_atom(keyword, "unsafe", "unsafe modifier").map(|_| ())
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
        // A written result type supplies the whole recursive signature. Only
        // inferred results require opening the actual leading lambda telescope;
        // do not move lambdas through lets, applications, or effects.
        let mut recursive_parameters = parameters.to_vec();
        let (syntax, expected, lambdas) = if expected.is_none() {
            self.open_recursive_lambdas(syntax, expected, &mut recursive_parameters)?
        } else {
            (syntax, expected, Vec::new())
        };
        let expected = match expected {
            Some(expected) => expected,
            None => {
                // Allocate the result hole before the self local. Its scope
                // cannot accidentally capture that private recursive reference.
                let sort = self.type_expected()?;
                self.hole(sort)?
            }
        };
        let mut type_ = self.instantiate(&expected)?;
        for parameter in recursive_parameters.iter().rev() {
            self.tick()?;
            type_ = type_
                .abstract_fvar(&parameter.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            type_ = Expr::forall_e(
                parameter.user_name.clone(),
                self.instantiate(&parameter.type_)?,
                type_,
                parameter.binder_info,
            );
        }
        let marker = FVarId(self.fresh_name()?);
        self.txn.lctx.add_param(
            marker.clone(),
            Name::anonymous(),
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
                value: Expr::fvar(marker.clone()),
                type_: type_.clone(),
            },
        });
        let body = self.term(syntax, Some(expected))?;
        let body = self.finish_open_universes(body)?;
        let body = self.close_recursive_lambdas(&lambdas, body)?;
        // A failed tactic alternative can discard its recursive reference.
        // Judge the surviving checked term, not whether a trial mentioned self.
        if !body
            .value
            .abstract_fvar(&marker, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?
            .has_loose_bvar(0)
        {
            self.partial
                .as_mut()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?
                .reference = None;
            return Ok(body);
        }
        // The pin permits nonrecursive partial constants. Only a surviving
        // recursive edge imposes this restriction on the function signature.
        if self
            .partial
            .as_ref()
            .is_some_and(|state| state.kind == Kind::Partial)
            && !matches!(self.whnf(&type_)?.node(), ExprNode::ForallE { .. })
        {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "a function type for recursive partial def",
            });
        }
        // Closing written lambdas restores their original lexical scope. Keep
        // the private header until ordinary declaration closure substitutes the
        // checked executable companion and captures its section parameters.
        if self.txn.lctx.find(&marker).is_none() {
            self.txn
                .lctx
                .add_param(marker, Name::anonymous(), type_, BinderInfo::Default);
        }
        Ok(body)
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
        let executable_name = if self
            .partial
            .as_ref()
            .is_some_and(|state| state.kind == Kind::Unsafe)
        {
            reference.name
        } else {
            Name::str(reference.name, "_unsafe_rec")
        };
        let mut executable = Expr::const_(
            executable_name,
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
}
