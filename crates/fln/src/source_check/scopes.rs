//! Section lifetimes affect source resolution, not the checked environment. Ending
//! a section restores lookup/universe state but never removes its declarations.
use super::*;
use fln_elab::source::scope::{SourceScope, components};
use fln_parse::command_scope::ScopeCommand;
use std::collections::BTreeSet;

#[derive(Clone)]
struct Frame {
    label: Option<String>,
    saved: SourceScope,
}
#[derive(Default)]
pub(crate) struct Scopes {
    pub current: SourceScope,
    stack: Vec<Frame>,
    namespaces: BTreeSet<Name>,
}

pub(crate) enum TransitionError {
    Scope(String),
    Registry(fln_elab::instances::InstanceRegistryError),
}

impl TransitionError {
    /// The refusal as a message, for a front door without per-file coordinates.
    pub fn message(self) -> String {
        match self {
            Self::Scope(message) => message,
            Self::Registry(error) => format!("{error:?}"),
        }
    }
    pub fn into_source(self, file: usize, command: usize, offset: usize) -> SourceCheckError {
        match self {
            Self::Scope(message) => SourceCheckError::Scope {
                file,
                command,
                offset,
                message,
            },
            Self::Registry(error) => SourceCheckError::Command {
                file,
                command,
                offset,
                error: Box::new(EngineExecutionError::Frontend(
                    DefinitionFrontendError::Elaborate(
                        fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::InstanceRegistry(error),
                        ),
                    ),
                )),
            },
        }
    }
}

impl Scopes {
    /// Apply lexical effects against the exact predecessor environment. Keep
    /// activation times in each saved frame, not in the persistent registry.
    /// A failed command discards its enclosing private source-check batch.
    pub fn transition(
        &mut self,
        command: ScopeCommand,
        env: &Environment,
    ) -> Result<(), TransitionError> {
        match command {
            ScopeCommand::Namespace(name) => {
                let parts = components(&name).map_err(|e| TransitionError::Scope(e.to_string()))?;
                if parts.is_empty() || parts.iter().any(|part| part == "_root_") {
                    return Err(TransitionError::Scope("invalid namespace label".into()));
                }
                // `namespace A.B` is two scopes. Activate A before saving the
                // frame for B, so `end B` restores A's active instances.
                for part in parts {
                    self.apply(ScopeCommand::Namespace(Name::str(Name::anonymous(), part)))
                        .map_err(TransitionError::Scope)?;
                    self.current
                        .instance_scopes
                        .activate(env, &self.current.namespace)
                        .map_err(TransitionError::Registry)?;
                }
            }
            ScopeCommand::Open(names) => return self.transition_open(names, false, env),
            ScopeCommand::OpenScoped(names) => return self.transition_open(names, true, env),
            other => self.apply(other).map_err(TransitionError::Scope)?,
        }
        Ok(())
    }

    fn transition_open(
        &mut self,
        names: Vec<Name>,
        scoped_only: bool,
        env: &Environment,
    ) -> Result<(), TransitionError> {
        let mut next = self.current.clone();
        let registry =
            fln_elab::instances::InstanceRegistry::read(env).map_err(TransitionError::Registry)?;
        for namespace in registry.instance_namespaces() {
            self.namespaces.insert(namespace.clone());
            self.observe(namespace);
        }
        // The pin elaborates an open declaration left-to-right in a private
        // name-resolution state: `open Lean Elab` first makes `Lean.Elab`
        // available. No prefix of a failed command may escape that state.
        for name in names {
            let resolved = self
                .resolve_open_in(&next, &name)
                .map_err(TransitionError::Scope)?;
            for namespace in resolved {
                next.instance_scopes
                    .activate(env, &namespace)
                    .map_err(TransitionError::Registry)?;
                if !scoped_only {
                    Self::add_open(&mut next, namespace).map_err(TransitionError::Scope)?;
                }
            }
        }
        self.current = next;
        Ok(())
    }

    /// Namespace lookup is not global-constant lookup. The Reference's
    /// `resolveNamespace` pools the first enclosing/root namespace with every
    /// opened namespace's matching child. A plain `open` opens all those
    /// namespaces; only selective/renaming forms require a unique target.
    fn resolve_open_in(&self, scope: &SourceScope, name: &Name) -> Result<Vec<Name>, String> {
        let parts = components(name).map_err(|e| e.to_string())?;
        if parts.is_empty() || (parts[0] == "_root_" && parts.len() == 1) {
            return Err("invalid namespace name".into());
        }
        let absolute = if parts[0] == "_root_" {
            Name::from_components(parts[1..].iter().map(String::as_str))
        } else {
            name.clone()
        };
        let mut resolved = Vec::new();
        let mut enclosing = scope.namespace.clone();
        loop {
            let candidate = if enclosing.is_anonymous() {
                absolute.clone()
            } else {
                enclosing.append_core(name)
            };
            if self.namespaces.contains(&candidate) {
                resolved.push(candidate);
                break;
            }
            if enclosing.is_anonymous() {
                break;
            }
            enclosing = enclosing.parent();
        }
        for opened in scope.opened.iter().rev() {
            let candidate = opened.append_core(name);
            if self.namespaces.contains(&candidate) && !resolved.contains(&candidate) {
                resolved.push(candidate);
            }
        }
        if resolved.is_empty() {
            return Err(format!("unknown namespace `{}`", name.to_display_string()));
        }
        Ok(resolved)
    }

    fn add_open(scope: &mut SourceScope, namespace: Name) -> Result<(), String> {
        if !scope.opened.contains(&namespace) {
            // One short namespace can expand to many matches. Bound the
            // resulting state, not only the number of source identifiers.
            if scope.opened.len() >= 4096 {
                return Err("scope items limit exceeded".into());
            }
            scope.opened.push(namespace);
        }
        Ok(())
    }

    /// A file's initial scope. `mode` decides only whether its compiled declarations may
    /// apply recursors the pin's code generator refuses (frontier only, bead
    /// `franken_lean-z8j.1.6.6`).
    pub fn new(env: &Environment, mode: fln_core::mode::Mode) -> Self {
        let mut scopes = Self::default();
        scopes.current.frontier_recursors = mode.permits_frontier();
        for (name, _) in env.constants() {
            scopes.observe(name);
        }
        scopes
    }
    fn observe(&mut self, name: &Name) {
        let mut parent = name.parent();
        while !parent.is_anonymous() && self.namespaces.insert(parent.clone()) {
            parent = parent.parent();
        }
    }
    pub fn admitted(&mut self, declaration: &Declaration) {
        match declaration {
            Declaration::Axiom(v) => self.observe(&v.base.name),
            Declaration::Defn(v) => self.observe(&v.base.name),
            Declaration::Thm(v) => self.observe(&v.base.name),
            Declaration::Opaque(v) => self.observe(&v.base.name),
            Declaration::Mutual(vs) => {
                for v in vs {
                    self.observe(&v.base.name);
                }
            }
            Declaration::Inductive(block) => {
                for v in &block.types {
                    self.observe(&v.base.name);
                }
                for v in &block.ctors {
                    self.observe(&v.base.name);
                }
            }
            Declaration::Quotient(vs) => {
                for v in vs {
                    self.observe(&v.base.name);
                }
            }
        }
    }
    pub fn check_limits(&self, command: &ScopeCommand) -> Result<(), (&'static str, usize)> {
        const MAX_DEPTH: usize = 256;
        const MAX_ITEMS: usize = 4096;
        let added_scopes = match command {
            ScopeCommand::Namespace(name) | ScopeCommand::Section(Some(name)) => {
                components(name).map_or(MAX_DEPTH + 1, |parts| parts.len())
            }
            ScopeCommand::Section(None) => 1,
            _ => 0,
        };
        if self.stack.len().saturating_add(added_scopes) > MAX_DEPTH {
            return Err(("scope depth", MAX_DEPTH));
        }
        let (old, new) = match command {
            ScopeCommand::Open(names) => (self.current.opened.len(), names.len()),
            ScopeCommand::OpenScoped(names) => (0, names.len()),
            ScopeCommand::Universe(names) => (self.current.universes.len(), names.len()),
            ScopeCommand::Include(names) | ScopeCommand::Omit(names) => (0, names.len()),
            _ => (0, 0),
        };
        if old.saturating_add(new) > MAX_ITEMS {
            return Err(("scope items", MAX_ITEMS));
        }
        Ok(())
    }
    pub fn apply(&mut self, command: ScopeCommand) -> Result<(), String> {
        let namespace = matches!(command, ScopeCommand::Namespace(_));
        match command {
            ScopeCommand::Instance(_) => {
                return Err("instance attributes require an environment transition".into());
            }
            ScopeCommand::Reducibility(_) => {
                return Err("reducibility attributes require an environment transition".into());
            }
            ScopeCommand::OpenScoped(_) => {
                return Err("scoped opening requires an environment transition".into());
            }
            ScopeCommand::Variable(_) => {
                return Err("variable commands require checked telescope elaboration".into());
            }
            ScopeCommand::Include(names) => self
                .current
                .variables
                .select(&names, true)
                .map_err(|e| e.to_string())?,
            ScopeCommand::Omit(names) => self
                .current
                .variables
                .select(&names, false)
                .map_err(|e| e.to_string())?,
            ScopeCommand::Simp(_) => {
                return Err("simp attributes require an environment transition".into());
            }
            ScopeCommand::OpenIn { .. } => {
                return Err("`open … in` is expanded by the command loop, never applied".into());
            }
            ScopeCommand::Namespace(name) | ScopeCommand::Section(Some(name)) => {
                // Each structural component is its own scope at the Reference.
                // This permits `namespace A.B; end B; ...; end A`.
                let parts = components(&name).map_err(|e| e.to_string())?;
                if parts.is_empty() || parts.iter().any(|p| p == "_root_") {
                    return Err("invalid namespace or section label".into());
                }
                for part in parts {
                    self.stack.push(Frame {
                        label: Some(part.clone()),
                        saved: self.current.clone(),
                    });
                    if namespace {
                        self.current.namespace = Name::str(self.current.namespace.clone(), part);
                        self.namespaces.insert(self.current.namespace.clone());
                    }
                }
            }
            ScopeCommand::Section(None) => {
                self.stack.push(Frame {
                    label: None,
                    saved: self.current.clone(),
                });
            }
            ScopeCommand::End(label) => {
                let labels: Vec<_> = label
                    .as_ref()
                    .map(components)
                    .transpose()
                    .map_err(|e| e.to_string())?
                    .map_or_else(|| vec![None], |parts| parts.into_iter().map(Some).collect());
                if labels.len() > self.stack.len() || labels.is_empty() {
                    return Err("end has no matching open scope".into());
                }
                if !labels
                    .iter()
                    .rev()
                    .zip(self.stack.iter().rev())
                    .all(|(label, frame)| label == &frame.label)
                {
                    return Err("end label does not match the innermost scope(s)".into());
                }
                for _ in labels {
                    self.current = self.stack.pop().expect("validated end depth").saved;
                }
            }
            ScopeCommand::Open(names) => {
                let mut next = self.current.clone();
                for name in names {
                    for namespace in self.resolve_open_in(&next, &name)? {
                        Self::add_open(&mut next, namespace)?;
                    }
                }
                self.current = next;
            }
            ScopeCommand::Universe(names) => {
                let mut seen: BTreeSet<_> = self.current.universes.iter().cloned().collect();
                for name in &names {
                    if !seen.insert(name.clone()) {
                        return Err(format!("duplicate universe `{}`", name.to_display_string()));
                    }
                }
                self.current.universes.extend(names);
            }
            ScopeCommand::Trivia => {}
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(name: &str) -> Name {
        Name::from_components(name.split('.'))
    }

    fn scopes(namespaces: &[&str]) -> Scopes {
        Scopes {
            namespaces: namespaces.iter().map(|name| n(name)).collect(),
            ..Scopes::default()
        }
    }

    fn open(scopes: &mut Scopes, names: &[&str]) {
        scopes
            .transition(
                ScopeCommand::Open(names.iter().map(|name| n(name)).collect()),
                &Environment::new(),
            )
            .unwrap_or_else(|error| panic!("{}", error.message()));
    }

    #[test]
    fn dependent_namespace_names_resolve_left_to_right() {
        let mut scopes = scopes(&["Library", "Library.Parser", "Library.Parser.Term"]);
        open(&mut scopes, &["Library", "Parser", "Term"]);
        assert_eq!(
            scopes.current.opened,
            vec![n("Library"), n("Library.Parser"), n("Library.Parser.Term")]
        );
        assert_eq!(
            scopes.current.resolve(&n("value"), |name| name == &n("Library.Parser.Term.value")),
            Ok(Some(n("Library.Parser.Term.value")))
        );
    }

    #[test]
    fn namespace_open_pools_all_matching_namespaces() {
        let mut scopes = scopes(&["A", "B", "A.N", "B.N", "N"]);
        open(&mut scopes, &["A", "B", "N"]);
        assert_eq!(
            scopes.current.opened,
            vec![n("A"), n("B"), n("N"), n("B.N"), n("A.N")]
        );
    }

    #[test]
    fn an_enclosing_namespace_does_not_discard_opened_candidates() {
        let mut scopes = scopes(&["Outer.N", "N", "A", "A.N"]);
        scopes.current.namespace = n("Outer");
        open(&mut scopes, &["A", "N"]);
        assert_eq!(scopes.current.opened, vec![n("A"), n("Outer.N"), n("A.N")]);
    }

    #[test]
    fn failed_late_name_does_not_publish_earlier_opens() {
        let mut scopes = scopes(&["A", "A.B"]);
        let before = scopes.current.clone();
        let result = scopes.transition(
            ScopeCommand::Open(vec![n("A"), n("B"), n("Missing")]),
            &Environment::new(),
        );
        assert!(result.is_err());
        assert_eq!(scopes.current, before);
        assert!(scopes.apply(ScopeCommand::Open(vec![n("A"), n("Missing")])).is_err());
        assert_eq!(scopes.current, before);
    }

    #[test]
    fn scoped_open_does_not_make_names_available_to_later_items() {
        let mut scopes = scopes(&["A", "A.B"]);
        let before = scopes.current.clone();
        assert!(scopes.transition(
            ScopeCommand::OpenScoped(vec![n("A"), n("B")]),
            &Environment::new(),
        ).is_err());
        assert_eq!(scopes.current, before);
    }

    #[test]
    fn root_qualification_and_escaped_components_remain_structural() {
        let escaped = Name::from_components(["A.B"]);
        let mut scopes = scopes(&["Root", "Outer.Root"]);
        scopes.current.namespace = n("Outer");
        scopes.namespaces.insert(escaped.clone());
        open(&mut scopes, &["_root_.Root"]);
        scopes.apply(ScopeCommand::Open(vec![escaped.clone()])).unwrap();
        assert_eq!(scopes.current.opened, vec![n("Root"), escaped]);
    }

    #[test]
    fn ending_a_section_restores_all_open_effects() {
        let mut scopes = scopes(&["A", "A.B"]);
        let before = scopes.current.clone();
        scopes.apply(ScopeCommand::Section(None)).unwrap();
        open(&mut scopes, &["A", "B"]);
        scopes.apply(ScopeCommand::End(None)).unwrap();
        assert_eq!(scopes.current, before);
    }

    #[test]
    fn expanded_namespace_state_is_bounded_atomically() {
        let mut scopes = Scopes::default();
        scopes.current.opened = (0..4096)
            .map(|index| Name::str(Name::anonymous(), format!("N{index}")))
            .collect();
        scopes.namespaces.insert(n("New"));
        let before = scopes.current.clone();
        assert!(scopes.apply(ScopeCommand::Open(vec![n("New")])).is_err());
        assert_eq!(scopes.current, before);
    }
}
