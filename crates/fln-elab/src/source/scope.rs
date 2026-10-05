//! Explicit command scope for native source elaboration. It carries no admission
//! authority and never installs aliases or unchecked constants in the environment.
use super::*;
pub mod simp;
pub mod variables;
use crate::aliases::AliasTable;
use fln_core::name::LeafView;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceScope {
    pub namespace: Name,
    pub opened: Vec<Name>,
    pub universes: Vec<Name>,
    pub variables: variables::SectionVariables,
    pub instance_scopes: crate::instances::scoped::ActiveScopes,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeError {
    InvalidName,
    Ambiguous(Name, Vec<Name>),
    UnknownVariable(Name),
    OmittedVariable(Name),
    VariableSelectionLimit,
}
impl std::fmt::Display for ScopeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidName => write!(f, "invalid scoped declaration name"),
            Self::UnknownVariable(name) => write!(
                f,
                "section variable `{}` has not been declared in the current scope",
                name.to_display_string()
            ),
            Self::OmittedVariable(name) => write!(
                f,
                "cannot omit referenced section variable `{}`",
                name.to_display_string()
            ),
            Self::VariableSelectionLimit => write!(f, "section variable selection limit exceeded"),
            Self::Ambiguous(name, candidates) => {
                write!(f, "ambiguous name `{}`: ", name.to_display_string())?;
                for (i, candidate) in candidates.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", candidate.to_display_string())?;
                }
                Ok(())
            }
        }
    }
}
impl std::error::Error for ScopeError {}
fn error(error: ScopeError) -> NatDefinitionElabError {
    failure(SourceInferenceError::NameScope(error))
}

/// Return structural string components, never splitting an escaped dot. Source
/// names cannot contain numeric/internal components. Work is explicitly bounded.
pub fn components(name: &Name) -> Result<Vec<String>, ScopeError> {
    let mut current = name.clone();
    let mut parts = Vec::new();
    while !current.is_anonymous() {
        if parts.len() >= 256 {
            return Err(ScopeError::InvalidName);
        }
        let LeafView::Str(part) = current.leaf_view() else {
            return Err(ScopeError::InvalidName);
        };
        if part.is_empty() {
            return Err(ScopeError::InvalidName);
        }
        parts.push(part.to_owned());
        current = current.parent();
    }
    parts.reverse();
    Ok(parts)
}

/// Whether `name` is written `_root_.…`. Such a name denotes a global: the
/// pin matches a regular local only by the name as given (`matchLocalDecl?`,
/// vendored `ResolveName.lean:466`), so `_root_.x` never reaches a local `x`.
pub(super) fn is_root_qualified(name: &Name) -> bool {
    if name.is_anonymous() {
        return false;
    }
    let mut first = name.clone();
    while !first.parent().is_anonymous() {
        first = first.parent();
    }
    first == Name::from_components(["_root_"])
}

impl SourceScope {
    pub fn declaration_name(&self, name: &Name) -> Result<Name, ScopeError> {
        let parts = components(name)?;
        if parts.is_empty() {
            return Err(ScopeError::InvalidName);
        }
        if parts[0] == "_root_" {
            if parts.len() == 1 {
                return Err(ScopeError::InvalidName);
            }
            Ok(Name::from_components(parts[1..].iter().map(String::as_str)))
        } else {
            Ok(self.namespace.append_core(name))
        }
    }

    /// The current namespace (and its parents) wins before opened namespaces.
    /// All open candidates are retained: a tie is a refusal, never an arbitrary
    /// insertion-order choice. Expected-type overload resolution is separate.
    pub fn resolve(
        &self,
        name: &Name,
        exists: impl FnMut(&Name) -> bool,
    ) -> Result<Option<Name>, ScopeError> {
        self.resolve_with_aliases(name, exists, &AliasTable::default())
    }

    /// [`Self::resolve`], with imported `export` aliases beside declarations, as
    /// the pin's `resolveGlobalName` consults `getAliases` at each namespace and
    /// in each opened namespace (vendored `src/Lean/ResolveName.lean`). At one
    /// namespace a real declaration (or local) wins; there an alias with two
    /// targets is a refusal, never a choice. `_root_.x` names `x` exactly, as
    /// the pin's `resolveExact` does. Not modelled: the pin skips aliases to
    /// `protected` declarations for an atomic name, and this table records no
    /// protection.
    pub fn resolve_with_aliases(
        &self,
        name: &Name,
        mut exists: impl FnMut(&Name) -> bool,
        aliases: &AliasTable,
    ) -> Result<Option<Name>, ScopeError> {
        let parts = components(name)?;
        if parts.first().is_some_and(|p| p == "_root_") {
            let absolute = Name::from_components(parts[1..].iter().map(String::as_str));
            return Ok(exists(&absolute).then_some(absolute));
        }
        let mut namespace = self.namespace.clone();
        loop {
            let candidate = namespace.append_core(name);
            if exists(&candidate) {
                return Ok(Some(candidate));
            }
            match aliases.targets(&candidate) {
                [] => {}
                [target] => return Ok(Some(target.clone())),
                targets => return Err(ScopeError::Ambiguous(name.clone(), targets.to_vec())),
            }
            if namespace.is_anonymous() {
                break;
            }
            namespace = namespace.parent();
        }
        let mut candidates = Vec::new();
        for opened in self.opened.iter().rev() {
            let candidate = opened.append_core(name);
            if exists(&candidate) && !candidates.contains(&candidate) {
                candidates.push(candidate.clone());
            }
            for target in aliases.targets(&candidate) {
                if !candidates.contains(target) {
                    candidates.push(target.clone());
                }
            }
        }
        match candidates.len() {
            0 => Ok(None),
            1 => Ok(candidates.pop()),
            _ => Err(ScopeError::Ambiguous(name.clone(), candidates)),
        }
    }
}

impl Context {
    pub(super) fn scoped(env: &Environment, kernel: Budget, scope: &SourceScope) -> Self {
        let mut context = Self::new(env, kernel);
        context.source_scope = scope.clone();
        context.txn.lctx = scope.variables.locals().clone();
        context.next = scope.variables.next();
        context
    }

    pub(super) fn resolve_source_name(
        &mut self,
        name: &Name,
    ) -> Result<Option<Name>, NatDefinitionElabError> {
        // The scope is externally supplied through the embeddable API as well.
        // Charge its complete search width before scanning even an empty env.
        for _ in 0..self
            .source_scope
            .opened
            .len()
            .saturating_add(
                components(&self.source_scope.namespace)
                    .map_err(error)?
                    .len(),
            )
            .saturating_add(1)
        {
            self.tick()?;
        }
        let aliases = self
            .alias_cache
            .read(&self.txn.env)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        self.source_scope
            .resolve_with_aliases(
                name,
                |candidate| {
                    self.txn.env.contains(candidate)
                        || self.txn.lctx.find_by_user_name(candidate).is_some()
                        || self
                            .recursion
                            .as_ref()
                            .is_some_and(|r| &r.name == candidate)
                },
                &aliases,
            )
            .map_err(error)
    }

    pub(super) fn enter_declaration(
        &mut self,
        name: &Name,
    ) -> Result<Name, NatDefinitionElabError> {
        self.tick()?;
        let name = self.source_scope.declaration_name(name).map_err(error)?;
        self.source_scope.namespace = name.parent();
        Ok(name)
    }
}

/// Candidates only. The caller must use the same kernel/council publication as
/// an unscoped declaration; scope resolution cannot mint a checked declaration.
pub fn elaborate_definition(
    syntax: &Syntax,
    env: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    super::definition_scoped(syntax, env, kernel, scope)
}

/// Elaborate an anonymous example as a definition candidate of any sort.
///
/// The pin's `mkDefViewOfExample` reuses ordinary definition elaboration, and
/// `elabMutualDef` discards its entire successor environment. This function
/// supplies only the candidate: callers must dual-check it in a scratch
/// successor, never publish it. The original example syntax remains intact.
pub fn elaborate_example(
    syntax: &Syntax,
    name: Name,
    env: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};

    if !name.parent().is_anonymous() || !matches!(name.leaf_view(), LeafView::Num(_)) {
        return Err(NatDefinitionElabError::InvalidGeneratedCheckName);
    }
    let declaration = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "example declaration",
    )?;
    let modifiers = expect_node(
        &declaration[0],
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "example modifiers",
    )?;
    // Attribute execution is a separate effect. Refuse unsupported modifiers
    // instead of silently losing an attribute failure when the scratch closes.
    for modifier in modifiers {
        expect_empty_null(modifier, "unmodified example")?;
    }
    let example = expect_node(
        &declaration[1],
        &parser_kind(&["Command", "example"]),
        3,
        "example",
    )?;
    expect_atom(&example[0], "example", "example keyword")?;
    let empty = || Syntax::node(Name::from_components(["null"]), Vec::new());
    let id = Syntax::node(
        parser_kind(&["Command", "declId"]),
        vec![
            Syntax::Ident {
                info: SourceInfo::None,
                raw_val: ByteSpan::empty_at(BytePos(0)),
                val: name.clone(),
                preresolved: Vec::new(),
            },
            empty(),
        ],
    );
    let definition = Syntax::node(
        parser_kind(&["Command", "definition"]),
        vec![
            Syntax::Atom {
                info: SourceInfo::None,
                val: "def".into(),
            },
            id,
            example[1].clone(),
            example[2].clone(),
            empty(),
        ],
    );
    let candidate = Syntax::node(
        parser_kind(&["Command", "declaration"]),
        vec![declaration[0].clone(), definition],
    );
    let mut context = Context::scoped(env, kernel, scope);
    super::definition_in_context_named(&candidate, &mut context, Some(name))
}

/// Recognize the canonical command shape; elaboration still validates its body.
pub fn is_example(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Command", "declaration"])
            && args.get(1).and_then(Syntax::kind)
                == Some(&parser_kind(&["Command", "example"])))
}

pub fn elaborate_record(
    syntax: &Syntax,
    env: &Environment,
    kernel: Budget,
    budget: crate::records::RecordBudget,
    scope: &SourceScope,
) -> Result<SourceRecord, NatDefinitionElabError> {
    record::elaborate_record_scoped(syntax, env, kernel, budget, scope)
}

pub fn elaborate_inductive(
    syntax: &Syntax,
    env: &Environment,
    kernel: Budget,
    budget: crate::records::RecordBudget,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    inductive::elaborate_inductive_scoped(syntax, env, kernel, budget, scope)
}

/// Elaborate a mutual family group into one candidate, with no provisional
/// global declarations. The caller must admit the whole result atomically.
pub fn elaborate_mutual_inductives(
    syntax: &[Syntax],
    env: &Environment,
    kernel: Budget,
    budget: crate::records::RecordBudget,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    inductive::elaborate_mutual(syntax, env, kernel, budget, scope)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn n(s: &str) -> Name {
        Name::from_components(s.split('.'))
    }
    /// The pin's `resolveGlobalName` consults `getAliases` beside declarations
    /// at each namespace and in each opened namespace; `_root_.x` is exact.
    #[test]
    fn export_aliases_resolve_beside_declarations_at_each_namespace() {
        let scope = SourceScope {
            namespace: n("Outer"),
            opened: vec![n("O")],
            universes: vec![],
            variables: variables::SectionVariables::default(),
            instance_scopes: crate::instances::scoped::ActiveScopes::default(),
        };
        let env = [
            "Decidable.decide",
            "Outer.mine",
            "Bool.not",
            "Other.not",
            "X.one",
            "Y.one",
        ]
        .into_iter()
        .fold(fln_env::environment::Environment::new(), |env, name| {
            env.add_decl(fln_env::constants::ConstantInfo::Axiom(
                fln_env::constants::AxiomVal {
                    base: fln_env::constants::ConstantVal {
                        name: n(name),
                        level_params: Vec::new(),
                        type_: fln_core::expr::Expr::sort(fln_core::level::Level::one()),
                    },
                    is_unsafe: false,
                },
            ))
            .unwrap()
        });
        let env = [
            ("decide", "Decidable.decide"),
            ("Outer.mine", "Bool.not"),
            ("O.neg", "Other.not"),
            ("two", "X.one"),
            ("two", "Y.one"),
        ]
        .into_iter()
        .fold(env, |env, (alias, target)| {
            crate::aliases::register(&env, &n(alias), &n(target)).unwrap()
        });
        let aliases = AliasTable::read(&env).unwrap();
        let resolve =
            |name: &str| scope.resolve_with_aliases(&n(name), |x| env.contains(x), &aliases);
        // A root alias, as `export Decidable (decide)` in the root namespace.
        assert_eq!(resolve("decide").unwrap(), Some(n("Decidable.decide")));
        // At one namespace the real declaration wins over an alias there.
        assert_eq!(resolve("mine").unwrap(), Some(n("Outer.mine")));
        // An alias in an opened namespace is a candidate like a declaration.
        assert_eq!(resolve("neg").unwrap(), Some(n("Other.not")));
        // Two targets for one alias are a refusal, never a choice.
        assert!(matches!(resolve("two"), Err(ScopeError::Ambiguous(_, xs)) if xs.len() == 2));
        // `_root_.decide` names `decide` exactly: no declaration, so nothing.
        assert_eq!(resolve("_root_.decide").unwrap(), None);
        // The alias-free form is unchanged.
        assert_eq!(
            scope.resolve(&n("decide"), |x| env.contains(x)).unwrap(),
            None
        );
    }

    #[test]
    fn namespace_prefixes_root_escapes_and_ambiguous_opens_have_distinct_rules() {
        let scope = SourceScope {
            namespace: n("Outer.Inner"),
            opened: vec![n("A"), n("B"), n("A")],
            universes: vec![],
            variables: variables::SectionVariables::default(),
            instance_scopes: crate::instances::scoped::ActiveScopes::default(),
        };
        let names = [n("Outer.x"), n("A.x"), n("B.x"), n("A.y"), n("B.y"), n("x")];
        let resolve = |name: &str| scope.resolve(&n(name), |x| names.contains(x));
        assert_eq!(resolve("x").unwrap(), Some(n("Outer.x")));
        assert_eq!(resolve("_root_.x").unwrap(), Some(n("x")));
        assert!(matches!(resolve("y"), Err(ScopeError::Ambiguous(_, xs)) if xs.len() == 2));
        assert_eq!(
            scope.declaration_name(&n("Nested.f")).unwrap(),
            n("Outer.Inner.Nested.f")
        );
        assert_eq!(scope.declaration_name(&n("_root_.f")).unwrap(), n("f"));
        assert_eq!(
            components(&Name::from_components(["A.B"])).unwrap(),
            vec!["A.B"]
        );
    }
}
