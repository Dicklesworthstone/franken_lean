//! `.c`: the pin's dotted identifier (`Term.dotIdent`; `resolveDottedIdentFn`,
//! `Lean/Elab/App.lean:1984`), bead `franken_lean-z8j.1.10`.
//!
//! The namespace of `.c` is read off the expected type:
//!
//! 1. `c` must be atomic, and the expected type must be known. The pin postpones while it is
//!    not; this elaborator has no postponement here, so it refuses where the pin would wait,
//!    which can refuse a program the pin accepts but never accepts one it rejects;
//! 2. the expected type is put in weak head normal form *without* unfolding definitions
//!    (`whnfCore`), and the bodies of its `∀`s are entered (`withForallBody`), so
//!    `.some : Nat → Option Nat` reads `Option`;
//! 3. a constant head `C` names `C.c`, resolved globally with no current namespace but with
//!    the open namespaces (`resolveGlobalName env opts Name.anonymous openDecls`), then as a
//!    local;
//! 4. when that fails, the head definition is unfolded one step (`unfoldDefinition?`) and the
//!    lookup is retried, so `def MyT := T` gives `.leaf : MyT` the namespace `T`. When nothing
//!    more unfolds the pin logs every failure in order and throws the last; the first is
//!    reported here.
//!
//! A sort head is the pin's "Not supported on type universe" and any other head its "not of
//! the form `C ...`". Several resolutions are an overload the pin elaborates by trying each;
//! that is refused, never approximated.
use super::*;
use fln_env::constants::ConstantInfo;

/// Why `.c` was refused. All but the last are the pin's own errors, in its words.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DottedIdentError {
    NotAtomic {
        id: Name,
    },
    ExpectedTypeUnknown {
        id: Name,
    },
    TypeUniverse,
    NotConstantHeaded {
        id: Name,
    },
    UnknownConstant {
        name: Name,
        id: Name,
    },
    /// More than one global candidate: the pin elaborates each as an overload.
    OverloadUnsupported {
        id: Name,
        candidates: Vec<Name>,
    },
}

impl std::fmt::Display for DottedIdentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const PREFIX: &str = "Invalid dotted identifier notation: ";
        match self {
            Self::NotAtomic { id } => write!(
                f,
                "{PREFIX}The name `{}` must be atomic",
                id.to_display_string()
            ),
            Self::ExpectedTypeUnknown { id } => write!(
                f,
                "{PREFIX}The expected type of `.{}` could not be determined",
                id.to_display_string()
            ),
            // The pin also prints the sort, indented, on the next line.
            Self::TypeUniverse => write!(f, "{PREFIX}Not supported on type universe"),
            // The pin prints the expected type, indented, between these two halves.
            Self::NotConstantHeaded { id } => write!(
                f,
                "{PREFIX}The expected type of `.{}` is not of the form `C ...` or `... → C ...` where C is a constant",
                id.to_display_string()
            ),
            Self::UnknownConstant { name, id } => write!(
                f,
                "Unknown constant `{}`\n\nNote: Inferred this name from the expected resulting type of `.{}`",
                name.to_display_string(),
                id.to_display_string()
            ),
            Self::OverloadUnsupported { id, candidates } => write!(
                f,
                "`.{}` resolves to {} constants ({}); overloaded dotted identifiers are not implemented",
                id.to_display_string(),
                candidates.len(),
                candidates
                    .iter()
                    .map(Name::to_display_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

fn refuse(error: DottedIdentError) -> NatDefinitionElabError {
    failure(SourceInferenceError::DottedIdent(error))
}

impl Context {
    /// `.c` (the arguments of a `Term.dotIdent` node) under `expected`: the atom's expected
    /// type, or the whole application's when `.c` is its head.
    #[inline(never)]
    pub(super) fn dotted_identifier(
        &mut self,
        args: &[Syntax],
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let [dot, Syntax::Ident { val: id, .. }] = args else {
            return Err(failure(SourceInferenceError::Scope));
        };
        expect_atom(dot, ".", "dotted identifier")?;
        if id.is_anonymous() || !id.parent().is_anonymous() {
            return Err(refuse(DottedIdentError::NotAtomic { id: id.clone() }));
        }
        let Some(expected) = expected else {
            return Err(refuse(DottedIdentError::ExpectedTypeUnknown {
                id: id.clone(),
            }));
        };
        let expected = self.instantiate(expected)?;
        let expected_unknown =
            matches!(operators::spine(&expected).0.node(), ExprNode::MVar { .. });
        let mut result = self.dotted_result_type(&expected)?;
        let mut first = None;
        loop {
            self.tick()?;
            let (head, _) = operators::spine(&result);
            let attempt = match head.node() {
                ExprNode::Const { name, .. } => self.dotted_lookup(name, id)?,
                ExprNode::Sort { .. } => Err(DottedIdentError::TypeUniverse),
                _ if expected_unknown => {
                    Err(DottedIdentError::ExpectedTypeUnknown { id: id.clone() })
                }
                _ => Err(DottedIdentError::NotConstantHeaded { id: id.clone() }),
            };
            match attempt {
                Ok(term) => return Ok(term),
                Err(error) => {
                    let first = first.get_or_insert(error).clone();
                    match self.unfold_head_definition(&result)? {
                        Some(unfolded) => result = self.dotted_result_type(&unfolded)?,
                        None => return Err(refuse(first)),
                    }
                }
            }
        }
    }

    /// `withForallBody`: `whnfCore`, then the body of every `∀`. A body that still has loose
    /// bound variables is read structurally; only its head is consulted.
    fn dotted_result_type(&mut self, type_: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let mut type_ = self.whnf_with_transparency(type_, UnificationTransparency::None, false)?;
        while let ExprNode::ForallE { body, .. } = type_.node() {
            self.tick()?;
            let body = body.clone();
            type_ = if body.has_loose_bvars() {
                body
            } else {
                self.whnf_with_transparency(&body, UnificationTransparency::None, false)?
            };
        }
        Ok(type_)
    }

    /// `C.c`, resolved with no current namespace and the open namespaces, then as a local.
    fn dotted_lookup(
        &mut self,
        head: &Name,
        id: &Name,
    ) -> Result<Result<Typed, DottedIdentError>, NatDefinitionElabError> {
        let full = head.append_core(id);
        let aliases = self
            .alias_cache
            .read(&self.txn.env)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let protected = self
            .protected_cache
            .read(&self.txn.env)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let root = SourceScope {
            opened: self.source_scope.opened.clone(),
            ..SourceScope::default()
        };
        for _ in 0..root.opened.len().saturating_add(1) {
            self.tick()?;
        }
        match root.resolve_with_aliases(
            &full,
            |candidate| self.txn.env.contains(candidate),
            &aliases,
            &protected,
        ) {
            Ok(Some(name)) => return Ok(Ok(self.constant(&name)?)),
            Ok(None) => {}
            Err(scope::ScopeError::Ambiguous(_, candidates)) => {
                return Ok(Err(DottedIdentError::OverloadUnsupported {
                    id: id.clone(),
                    candidates,
                }));
            }
            Err(_) => return Err(failure(SourceInferenceError::Scope)),
        }
        if let Some(local) = self.txn.lctx.find_by_user_name(&full) {
            return Ok(Ok(Typed {
                value: self
                    .matrix_aliases
                    .get(&local.id)
                    .cloned()
                    .unwrap_or_else(|| Expr::fvar(local.id.clone())),
                type_: local.type_.clone(),
            }));
        }
        Ok(Err(DottedIdentError::UnknownConstant {
            name: full,
            id: id.clone(),
        }))
    }

    /// `unfoldDefinition?` at the default transparency: when the head is a safe definition
    /// that is not `@[irreducible]`, its value at the head's levels, applied to the head's
    /// arguments.
    fn unfold_head_definition(
        &mut self,
        type_: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (head, arguments) = operators::spine(type_);
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        let irreducible = crate::reducibility::table(&self.txn.env)
            .map_err(|error| {
                failure(SourceInferenceError::Unification(Box::new(
                    UnificationError::Reducibility(error),
                )))
            })?
            .status(name)
            == crate::reducibility::Reducibility::Irreducible;
        if irreducible
            || definition.safety != DefinitionSafety::Safe
            || definition.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        let value =
            self.instantiate_params(&definition.value, &definition.base.level_params, levels)?;
        Ok(Some(arguments.into_iter().fold(value, Expr::app)))
    }
}
