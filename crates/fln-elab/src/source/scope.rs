//! Explicit command scope for native source elaboration. It carries no admission
//! authority and never installs aliases or unchecked constants in the environment.
use super::*;
use fln_core::name::LeafView;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceScope {
    pub namespace: Name,
    pub opened: Vec<Name>,
    pub universes: Vec<Name>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeError {
    InvalidName,
    Ambiguous(Name, Vec<Name>),
}
impl std::fmt::Display for ScopeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidName => write!(f, "invalid scoped declaration name"),
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
        mut exists: impl FnMut(&Name) -> bool,
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
            if namespace.is_anonymous() {
                break;
            }
            namespace = namespace.parent();
        }
        let mut candidates = Vec::new();
        for opened in self.opened.iter().rev() {
            let candidate = opened.append_core(name);
            if exists(&candidate) && !candidates.contains(&candidate) {
                candidates.push(candidate);
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
        self.source_scope
            .resolve(name, |candidate| {
                self.txn.env.contains(candidate)
                    || self.txn.lctx.find_by_user_name(candidate).is_some()
                    || self
                        .recursion
                        .as_ref()
                        .is_some_and(|r| &r.name == candidate)
            })
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

#[cfg(test)]
mod tests {
    use super::*;
    fn n(s: &str) -> Name {
        Name::from_components(s.split('.'))
    }
    #[test]
    fn namespace_prefixes_root_escapes_and_ambiguous_opens_have_distinct_rules() {
        let scope = SourceScope {
            namespace: n("Outer.Inner"),
            opened: vec![n("A"), n("B"), n("A")],
            universes: vec![],
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
