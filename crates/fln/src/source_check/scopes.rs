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
pub(super) struct Scopes {
    pub current: SourceScope,
    stack: Vec<Frame>,
    namespaces: BTreeSet<Name>,
}
impl Scopes {
    pub fn new(env: &Environment) -> Self {
        let mut scopes = Self::default();
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
            ScopeCommand::Universe(names) => (self.current.universes.len(), names.len()),
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
                let mut resolved = Vec::new();
                for name in names {
                    let name = self
                        .current
                        .resolve(&name, |n| self.namespaces.contains(n))
                        .map_err(|e| e.to_string())?
                        .ok_or_else(|| {
                            format!("unknown namespace `{}`", name.to_display_string())
                        })?;
                    if !self.current.opened.contains(&name) && !resolved.contains(&name) {
                        resolved.push(name);
                    }
                }
                self.current.opened.extend(resolved);
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
