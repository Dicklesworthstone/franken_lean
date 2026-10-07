#!/usr/bin/env python3
"""Apply the reviewed native-open integration; never publish a Git ref.

The namespace-opens workflow compiles and tests this exact successor and exports
its source blobs. An explicit leased connector commit publishes those blobs.
All replacements must match exactly; no file is removed or unrelated edit staged.
"""
from pathlib import Path
import json
import re

PARSER = Path('crates/fln-parse/src/command_scope.rs')
RESOLVER = Path('crates/fln-elab/src/source/scope.rs')
SCOPES = Path('crates/fln/src/source_check/scopes.rs')
NEW_PARSER = Path('crates/fln-parse/src/command_scope/opens.rs')
NEW_RESOLVER = Path('crates/fln-elab/src/source/scope/opens.rs')
NEW_SCOPES = Path('crates/fln/src/source_check/scopes/opens.rs')
TEST = Path('crates/fln-cli/tests/namespace_opens.rs')


def main():
    if 'pub open_declarations: opens::OpenDeclarations,' in RESOLVER.read_text():
        if not all(p.is_file() for p in [NEW_PARSER, NEW_RESOLVER, NEW_SCOPES, TEST]):
            raise SystemExit('partial namespace-open integration: refusing to guess')
        print('Native restricted opens are already integrated; testing current source.')
        return
    pending = {}

    def replace(path, old, new, count=1):
        text = pending.get(path, path.read_text())
        if text.count(old) != count:
            raise SystemExit(f'anchor mismatch in {path}: expected {count}, found {text.count(old)}')
        pending[path] = text.replace(old, new)

    def create(path, text):
        if path.exists():
            raise SystemExit(f'refusing to replace existing module {path}')
        pending[path] = text.lstrip('\n')

    replace(PARSER, 'pub mod mutual;\n', 'pub mod mutual;\npub mod opens;\n')
    replace(PARSER, '    OpenScoped(Vec<Name>),\n', '    OpenScoped(Vec<Name>),\n    OpenRestricted(opens::RestrictedOpen),\n')
    replace(PARSER, '    if keyword == "variable" {\n', '''    if keyword == "open" {
        if let Some(command) = opens::parse(&view, &tokens)? {
            return Ok(Some(command));
        }
    }
    if keyword == "variable" {
''')
    # These three inputs cease to be grammar refusals; their malformed counterparts
    # remain in this test, and positive grammar/negative semantic tests are added.
    replace(PARSER, '            "open A (x)",\n', '            "open A (x",\n')
    replace(PARSER, '            "open A hiding x",\n', '            "open A hiding",\n')
    replace(PARSER, '            "open A renaming x -> y",\n', '            "open A renaming x ->",\n')

    create(NEW_PARSER, r'''
//! Restricted namespace opens. Ordinary and scoped opens keep their existing
//! parser. The pin's openOnly/openHiding/openRenaming all require a nonempty list.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Restriction {
    Only(Vec<Name>),
    Hiding(Vec<Name>),
    Renaming(Vec<(Name, Name)>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RestrictedOpen {
    pub namespace: Name,
    pub restriction: Restriction,
}

impl RestrictedOpen {
    pub fn item_count(&self) -> usize {
        match &self.restriction {
            Restriction::Only(names) | Restriction::Hiding(names) => names.len(),
            Restriction::Renaming(names) => names.len(),
        }
    }
}

pub(super) fn parse(
    view: &SourceView,
    tokens: &[LexedToken],
) -> Result<Option<ScopeCommand>, DefinitionParseError> {
    let Some(TokenKind::Ident(namespace)) = tokens.get(1).map(|t| &t.kind) else {
        return Ok(None);
    };
    let Some(TokenKind::Symbol(form)) = tokens.get(2).map(|t| &t.kind) else {
        return Ok(None);
    };
    if !matches!(form.as_str(), "(" | "hiding" | "renaming") {
        return Ok(None);
    }
    let bad = |index: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: tokens.get(index).map_or_else(
            || view.to_original(tokens.last().expect("open prefix").extent.end()),
            |token| view.to_original(token.extent.start()),
        ),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    let ident = |index: usize| match tokens.get(index).map(|t| &t.kind) {
        Some(TokenKind::Ident(name)) => Ok(name.clone()),
        _ => Err(bad(index)),
    };
    let symbol = |index: usize, text: &str| {
        matches!(tokens.get(index).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text)
    };
    let mut index = 3;
    let restriction = if form == "renaming" {
        let mut renames = Vec::new();
        loop {
            let from = ident(index)?;
            index += 1;
            if !symbol(index, "->") && !symbol(index, "→") {
                return Err(bad(index));
            }
            index += 1;
            let to = ident(index)?;
            index += 1;
            renames.push((from, to));
            if !symbol(index, ",") {
                break;
            }
            index += 1;
        }
        Restriction::Renaming(renames)
    } else {
        let mut names = vec![ident(index)?];
        index += 1;
        while matches!(tokens.get(index).map(|t| &t.kind), Some(TokenKind::Ident(_))) {
            names.push(ident(index)?);
            index += 1;
        }
        if form == "(" {
            if !symbol(index, ")") {
                return Err(bad(index));
            }
            index += 1;
            Restriction::Only(names)
        } else {
            Restriction::Hiding(names)
        }
    };
    // Command-local restricted opens are deliberately refused until every front
    // door can expand their scope. Never discard a trailing `in` or its body.
    if index != tokens.len() {
        return Err(bad(index));
    }
    Ok(Some(ScopeCommand::OpenRestricted(RestrictedOpen {
        namespace: namespace.clone(),
        restriction,
    })))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn n(s: &str) -> Name { Name::from_components(s.split('.')) }
    fn parsed(s: &str) -> RestrictedOpen {
        match super::super::parse(s.as_bytes()).unwrap() {
            Some(ScopeCommand::OpenRestricted(open)) => open,
            other => panic!("restricted open expected: {other:?}"),
        }
    }
    #[test]
    fn parses_all_three_restrictions_without_rewriting_names() {
        assert_eq!(parsed("open N (x y)").restriction, Restriction::Only(vec![n("x"), n("y")]));
        assert_eq!(parsed("open N hiding x y").restriction, Restriction::Hiding(vec![n("x"), n("y")]));
        assert_eq!(parsed("open N renaming x -> a, y → b").restriction,
            Restriction::Renaming(vec![(n("x"), n("a")), (n("y"), n("b"))]));
        let escaped = parsed("-- 😀\r\nopen A.«B.C» (/- nested /- comment -/ -/ «x.y» z)");
        assert_eq!(escaped.namespace, Name::from_components(["A", "B.C"]));
        assert_eq!(escaped.restriction, Restriction::Only(vec![Name::from_components(["x.y"]), n("z")]));
    }
    #[test]
    fn rejects_empty_lists_partial_renames_and_trailing_commands() {
        for text in ["open N ()", "open N hiding", "open N renaming", "open N renaming x",
            "open N renaming x ->", "open N renaming x -> a,", "open N (x) garbage",
            "open N hiding x, y", "open N (x) in def y := 1", "open N renaming x -> a in def y := 1"] {
            assert!(super::super::parse(text.as_bytes()).is_err(), "{text}");
        }
    }
    #[test]
    fn restricted_opens_are_single_byte_preserving_commands() {
        let source = "namespace N\r\nopen A (x y)\r\ndef value := x\r\nopen B renaming y → z\r\nend N";
        let commands = partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 5);
        assert!(matches!(super::super::parse(commands[1].1).unwrap(), Some(ScopeCommand::OpenRestricted(_))));
        assert_eq!(commands.iter().flat_map(|(_, bytes)| bytes.iter().copied()).collect::<Vec<_>>(), source.as_bytes());
    }
}
''')

    replace(RESOLVER, 'pub mod simp;\n', 'pub mod opens;\npub mod simp;\n')
    replace(RESOLVER, '    pub opened: Vec<Name>,\n', '''    pub opened: Vec<Name>,
    /// Lexical explicit and excluding opens, interleaved with `opened` in source order.
    /// They are not environment aliases and confer no declaration admission authority.
    pub open_declarations: opens::OpenDeclarations,
''')
    replace(RESOLVER, '''        for opened in self.opened.iter().rev() {
            let mut here = Vec::new();
            qualified(opened, &mut here, &mut exists);
            here.append(&mut found);
            found = here;
        }
''', '''        for opened in self.open_declarations.ordered(&self.opened).into_iter().rev() {
            let mut here = Vec::new();
            match opened {
                opens::OpenDeclRef::Simple { namespace, except } => {
                    if !except.contains(name) {
                        qualified(namespace, &mut here, &mut exists);
                    }
                }
                opens::OpenDeclRef::Explicit { alias, target } => {
                    if let Some(candidate) = opens::explicit_target(alias, target, name)? {
                        // Explicit opens deliberately bypass the protected-name test.
                        if exists(&candidate) {
                            here.push(candidate);
                        }
                    }
                }
            }
            here.append(&mut found);
            found = here;
        }
''')
    replace(RESOLVER, '''    /// Not modelled: `open X (y)`, `open X hiding y` and `open X renaming`, whose
    /// explicit names the pin resolves without the protection test, and the
    /// projection fallback (`loop p (s::projs)`), which field notation handles.
''', '''    /// Explicit opens also resolve structural name suffixes, bypassing the protected
    /// test. Hiding lists exclude exact names, not every name with that prefix.
    /// The projection fallback (`loop p (s::projs)`) is handled by field notation.
''')
    replace(RESOLVER, '''            .opened
            .len()
            .saturating_add(
''', '''            .opened
            .len()
            .saturating_add(self.source_scope.open_declarations.cost())
            .saturating_add(
''')
    create(NEW_RESOLVER, r'''
//! Lexical OpenDecl state; no environment aliases or checked declarations.
//! Restricted declarations remember how many legacy simple opens preceded them,
//! preserving candidate order without changing the embeddable `opened` API.
use super::{Name, ScopeError, components};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpenDecl {
    Simple { namespace: Name, except: Vec<Name> },
    Explicit { alias: Name, target: Name },
}

#[derive(Debug, Clone, Copy)]
pub enum OpenDeclRef<'a> {
    Simple { namespace: &'a Name, except: &'a [Name] },
    Explicit { alias: &'a Name, target: &'a Name },
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct OpenDeclarations {
    entries: Vec<(usize, OpenDecl)>,
    cost: usize,
}

impl OpenDeclarations {
    pub fn cost(&self) -> usize { self.cost }

    /// Append one already-resolved lexical declaration with a bounded search cost.
    /// The caller validates its target(s); this storage is never proof authority.
    pub fn push(&mut self, preceding_simple: usize, declaration: OpenDecl) -> Result<(), &'static str> {
        let weight = match &declaration {
            OpenDecl::Simple { except, .. } => 1usize.saturating_add(except.len()),
            OpenDecl::Explicit { .. } => 1,
        };
        let cost = self.cost.saturating_add(weight);
        if cost.saturating_add(preceding_simple) > 4096 {
            return Err("scope items limit exceeded");
        }
        if self.entries.last().is_some_and(|(at, _)| *at > preceding_simple) {
            return Err("inconsistent open declaration ordering");
        }
        self.entries.push((preceding_simple, declaration));
        self.cost = cost;
        Ok(())
    }

    pub fn ordered<'a>(&'a self, simple: &'a [Name]) -> Vec<OpenDeclRef<'a>> {
        let mut result = Vec::with_capacity(simple.len().saturating_add(self.entries.len()));
        let mut next = 0;
        for (at, declaration) in &self.entries {
            while next < (*at).min(simple.len()) {
                result.push(OpenDeclRef::Simple { namespace: &simple[next], except: &[] });
                next += 1;
            }
            result.push(match declaration {
                OpenDecl::Simple { namespace, except } => OpenDeclRef::Simple { namespace, except },
                OpenDecl::Explicit { alias, target } => OpenDeclRef::Explicit { alias, target },
            });
        }
        for namespace in &simple[next..] {
            result.push(OpenDeclRef::Simple { namespace, except: &[] });
        }
        result
    }
}

/// Exact aliases and structural prefix aliases, as in `T.mk` after `open N (T)`.
/// Escaped dots are single components; strings are never split to resolve names.
pub(super) fn explicit_target(alias: &Name, target: &Name, name: &Name) -> Result<Option<Name>, ScopeError> {
    let prefix = components(alias)?;
    let parts = components(name)?;
    if prefix.is_empty() || !parts.starts_with(&prefix) {
        return Ok(None);
    }
    let mut resolved = target.clone();
    for part in &parts[prefix.len()..] {
        resolved = Name::str(resolved, part.clone());
    }
    Ok(Some(resolved))
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::{SourceScope, AliasTable, ProtectedNames};
    fn n(s: &str) -> Name { Name::from_components(s.split('.')) }
    fn explicit(scope: &mut SourceScope, alias: &str, target: &str) {
        scope.open_declarations.push(scope.opened.len(), OpenDecl::Explicit { alias: n(alias), target: n(target) }).unwrap();
    }
    #[test]
    fn explicit_opens_resolve_protected_names_and_structural_suffixes() {
        let mut scope = SourceScope::default();
        explicit(&mut scope, "T", "N.T");
        let names = [n("N.T"), n("N.T.mk")];
        assert_eq!(scope.resolve(&n("T"), |x| names.contains(x)).unwrap(), Some(n("N.T")));
        assert_eq!(scope.resolve(&n("T.mk"), |x| names.contains(x)).unwrap(), Some(n("N.T.mk")));
        assert_eq!(scope.resolve(&n("T.missing"), |x| names.contains(x)).unwrap(), None);
        assert_eq!(scope.resolve(&n("_root_.T"), |x| names.contains(x)).unwrap(), None);
        // The protected table remains authoritative for ordinary opens, but an
        // explicit target need not be globally registered under its short name.
        let env = fln_env::environment::Environment::new();
        let env = crate::protected_names::register_module(&env, &[n("N.T")]).unwrap();
        let protected = ProtectedNames::read(&env).unwrap();
        assert_eq!(scope.resolve_with_aliases(&n("T"), |x| names.contains(x), &AliasTable::default(), &protected).unwrap(), Some(n("N.T")));
        let ordinary = SourceScope { opened: vec![n("N")], ..SourceScope::default() };
        assert_eq!(ordinary.resolve_with_aliases(&n("T"), |x| names.contains(x), &AliasTable::default(), &protected).unwrap(), None);
    }
    #[test]
    fn hiding_is_exact_and_does_not_erase_other_open_declarations() {
        let mut scope = SourceScope::default();
        scope.open_declarations.push(0, OpenDecl::Simple { namespace: n("N"), except: vec![n("T")] }).unwrap();
        let names = [n("N.T"), n("N.T.mk"), n("N.other")];
        assert_eq!(scope.resolve(&n("T"), |x| names.contains(x)).unwrap(), None);
        assert_eq!(scope.resolve(&n("T.mk"), |x| names.contains(x)).unwrap(), Some(n("N.T.mk")));
        assert_eq!(scope.resolve(&n("other"), |x| names.contains(x)).unwrap(), Some(n("N.other")));
        scope.opened.push(n("N"));
        assert_eq!(scope.resolve(&n("T"), |x| names.contains(x)).unwrap(), Some(n("N.T")));
    }
    #[test]
    fn mixed_open_kinds_preserve_overload_order_and_namespace_precedence() {
        let mut scope = SourceScope { opened: vec![n("A")], ..SourceScope::default() };
        explicit(&mut scope, "x", "B.x");
        scope.opened.push(n("C"));
        let names = [n("x"), n("A.x"), n("B.x"), n("C.x"), n("Inner.x")];
        assert_eq!(scope.resolve(&n("x"), |x| names.contains(x)), Err(ScopeError::Ambiguous(n("x"), vec![n("x"), n("C.x"), n("B.x"), n("A.x")])));
        scope.namespace = n("Inner");
        assert_eq!(scope.resolve(&n("x"), |x| names.contains(x)).unwrap(), Some(n("Inner.x")));
    }
    #[test]
    fn explicit_prefixes_do_not_split_escaped_dots_or_invent_members() {
        let alias = Name::from_components(["a.b"]);
        assert_eq!(explicit_target(&alias, &n("N.T"), &n("a.b")).unwrap(), None);
        let use_name = Name::from_components(["a.b", "mk"]);
        assert_eq!(explicit_target(&alias, &n("N.T"), &use_name).unwrap(), Some(n("N.T.mk")));
        let mut scope = SourceScope::default();
        explicit(&mut scope, "x", "Missing.x");
        assert_eq!(scope.resolve(&n("x"), |_| false).unwrap(), None);
    }
    #[test]
    fn insertion_refusals_leave_the_state_unchanged() {
        let mut opens = OpenDeclarations::default();
        let before = opens.clone();
        assert!(opens.push(4096, OpenDecl::Explicit { alias: n("x"), target: n("N.x") }).is_err());
        assert_eq!(opens, before);
        assert!(opens.push(0, OpenDecl::Simple { namespace: n("N"), except: vec![n("x"); 4096] }).is_err());
        assert_eq!(opens, before);
    }
}
''')

    replace(SCOPES, 'use std::collections::BTreeSet;\n', 'use std::collections::BTreeSet;\nmod opens;\n')
    replace(SCOPES, '            ScopeCommand::Open(names) => return self.transition_open(names, false, env),\n', '''            ScopeCommand::OpenRestricted(open) => return self.transition_restricted(open, env),
            ScopeCommand::Open(names) => return self.transition_open(names, false, env),
''')
    replace(SCOPES, '''        for opened in scope.opened.iter().rev() {
            let candidate = opened.append_core(name);
            if self.namespaces.contains(&candidate) && !resolved.contains(&candidate) {
                resolved.push(candidate);
            }
        }
''', '''        for opened in scope.open_declarations.ordered(&scope.opened).into_iter().rev() {
            // Explicit opens alias declarations, never namespaces.
            let fln_elab::source::scope::opens::OpenDeclRef::Simple { namespace, except } = opened else {
                continue;
            };
            let candidate = namespace.append_core(name);
            if !except.contains(name) && self.namespaces.contains(&candidate) && !resolved.contains(&candidate) {
                resolved.push(candidate);
            }
        }
''')
    replace(SCOPES, '            if scope.opened.len() >= 4096 {\n', '            if scope.opened.len().saturating_add(scope.open_declarations.cost()) >= 4096 {\n')
    replace(SCOPES, '            ScopeCommand::Open(names) => (self.current.opened.len(), names.len()),\n', '''            ScopeCommand::Open(names) => (self.current.opened.len().saturating_add(self.current.open_declarations.cost()), names.len()),
            ScopeCommand::OpenRestricted(open) => (
                self.current.opened.len().saturating_add(self.current.open_declarations.cost()),
                open.item_count().saturating_add(1),
            ),
''')
    replace(SCOPES, '''            ScopeCommand::OpenScoped(_) => {
                return Err("scoped opening requires an environment transition".into());
            }
''', '''            ScopeCommand::OpenScoped(_) => {
                return Err("scoped opening requires an environment transition".into());
            }
            ScopeCommand::OpenRestricted(_) => {
                return Err("restricted opening requires an environment transition".into());
            }
''')
    create(NEW_SCOPES, r'''
//! Validate an entire restricted open against its predecessor before publishing
//! lexical effects. A selection is not a persistent environment alias.
use super::*;
use fln_elab::aliases::AliasTable;
use fln_elab::protected_names::ProtectedNames;
use fln_elab::source::scope::opens::OpenDecl;
use fln_parse::command_scope::opens::{RestrictedOpen, Restriction};

impl Scopes {
    pub(super) fn transition_restricted(&mut self, open: RestrictedOpen, env: &Environment) -> Result<(), TransitionError> {
        let mut next = self.current.clone();
        let registry = fln_elab::instances::InstanceRegistry::read(env).map_err(TransitionError::Registry)?;
        for namespace in registry.instance_namespaces() {
            self.namespaces.insert(namespace.clone());
            self.observe(namespace);
        }
        let namespaces = self.resolve_open_in(&next, &open.namespace).map_err(TransitionError::Scope)?;
        let aliases = AliasTable::read(env).map_err(|e| TransitionError::Scope(format!("cannot read declaration aliases: {e:?}")))?;
        let protected = ProtectedNames::read(env).map_err(|e| TransitionError::Scope(format!("cannot read protected declarations: {e:?}")))?;
        let mut append = |declaration| {
            next.open_declarations.push(next.opened.len(), declaration)
                .map_err(|error| TransitionError::Scope(error.into()))
        };
        match open.restriction {
            Restriction::Only(names) => {
                for name in names {
                    let mut found = Vec::new();
                    for namespace in &namespaces {
                        if let Some(target) = member(&self.current, env, &aliases, &protected, namespace, &name)? {
                            found.push(target);
                        }
                    }
                    if found.len() != 1 {
                        return Err(TransitionError::Scope(format!("{} identifier `{}` in selective open", if found.is_empty() { "unknown" } else { "ambiguous" }, name.to_display_string())));
                    }
                    append(OpenDecl::Explicit { alias: name, target: found.pop().expect("one target") })?;
                }
            }
            Restriction::Renaming(renames) => {
                let namespace = unique(&namespaces, &open.namespace)?;
                for (from, to) in renames {
                    let target = required_member(&self.current, env, &aliases, &protected, namespace, &from)?;
                    append(OpenDecl::Explicit { alias: to, target })?;
                }
            }
            Restriction::Hiding(names) => {
                let namespace = unique(&namespaces, &open.namespace)?;
                for name in &names {
                    required_member(&self.current, env, &aliases, &protected, namespace, name)?;
                }
                append(OpenDecl::Simple { namespace: namespace.clone(), except: names })?;
                // Unlike selective/renamed opens, hiding also activates scoped instances.
                next.instance_scopes.activate(env, namespace).map_err(TransitionError::Registry)?;
            }
        }
        self.current = next;
        Ok(())
    }
}

fn unique<'a>(namespaces: &'a [Name], requested: &Name) -> Result<&'a Name, TransitionError> {
    if namespaces.len() != 1 {
        return Err(TransitionError::Scope(format!("ambiguous namespace `{}`", requested.to_display_string())));
    }
    Ok(&namespaces[0])
}

fn member(scope: &SourceScope, env: &Environment, aliases: &AliasTable, protected: &ProtectedNames, namespace: &Name, name: &Name) -> Result<Option<Name>, TransitionError> {
    let target = namespace.append_core(name);
    if env.contains(&target) {
        return Ok(Some(target));
    }
    // Export aliases are usable too. Resolve the qualified name only when no
    // declaration exists at that exact name, as the pin's OpenDecl.resolveId does.
    scope.resolve_with_aliases(&target, |n| env.contains(n), aliases, protected)
        .map_err(|e| TransitionError::Scope(e.to_string()))
}

fn required_member(scope: &SourceScope, env: &Environment, aliases: &AliasTable, protected: &ProtectedNames, namespace: &Name, name: &Name) -> Result<Name, TransitionError> {
    member(scope, env, aliases, protected, namespace, name)?.ok_or_else(|| TransitionError::Scope(format!("unknown declaration `{}.{}`", namespace.to_display_string(), name.to_display_string())))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn n(s: &str) -> Name { Name::from_components(s.split('.')) }
    fn environment(names: &[&str]) -> Environment {
        names.iter().fold(Environment::new(), |env, name| {
            env.add_decl(fln_env::constants::ConstantInfo::Axiom(fln_env::constants::AxiomVal {
                base: fln_env::constants::ConstantVal {
                    name: n(name), level_params: Vec::new(),
                    type_: fln_core::expr::Expr::sort(fln_core::level::Level::one()),
                }, is_unsafe: false,
            })).unwrap()
        })
    }
    fn scopes(env: &Environment) -> Scopes {
        let mut scopes = Scopes::default();
        for (name, _) in env.constants() { scopes.observe(name); }
        scopes
    }
    fn apply(scopes: &mut Scopes, env: &Environment, source: &str) -> Result<(), TransitionError> {
        scopes.transition(fln_parse::command_scope::parse(source.as_bytes()).unwrap().unwrap(), env)
    }
    #[test]
    fn selective_and_renamed_opens_do_not_expose_unselected_members() {
        let env = environment(&["N.x", "N.y"]);
        let mut scopes = scopes(&env);
        apply(&mut scopes, &env, "open N (x)").unwrap_or_else(|e| panic!("{}", e.message()));
        assert_eq!(scopes.current.resolve(&n("x"), |n| env.contains(n)).unwrap(), Some(n("N.x")));
        assert_eq!(scopes.current.resolve(&n("y"), |n| env.contains(n)).unwrap(), None);
        apply(&mut scopes, &env, "open N renaming y -> chosen").unwrap_or_else(|e| panic!("{}", e.message()));
        assert_eq!(scopes.current.resolve(&n("chosen"), |n| env.contains(n)).unwrap(), Some(n("N.y")));
        assert_eq!(scopes.current.resolve(&n("y"), |n| env.contains(n)).unwrap(), None);
        assert!(!env.contains(&n("chosen")));
    }
    #[test]
    fn invalid_late_members_do_not_leak_selections_or_hiding() {
        let env = environment(&["N.x", "N.y"]);
        let mut scopes = scopes(&env);
        let before = scopes.current.clone();
        for source in ["open N (x absent)", "open N renaming x -> selected, absent -> lost", "open N hiding x absent"] {
            assert!(apply(&mut scopes, &env, source).is_err(), "{source}");
            assert_eq!(scopes.current, before, "{source}");
        }
    }
    #[test]
    fn sections_restore_restrictions_and_hiding_affects_namespace_lookup() {
        let env = environment(&["N.x", "N.y", "N.Child", "N.Child.z"]);
        let mut scopes = scopes(&env);
        scopes.apply(ScopeCommand::Section(None)).unwrap();
        apply(&mut scopes, &env, "open N hiding Child x").unwrap_or_else(|e| panic!("{}", e.message()));
        assert_eq!(scopes.current.resolve(&n("y"), |n| env.contains(n)).unwrap(), Some(n("N.y")));
        assert!(apply(&mut scopes, &env, "open Child").is_err());
        scopes.apply(ScopeCommand::End(None)).unwrap();
        assert_eq!(scopes.current.resolve(&n("y"), |n| env.contains(n)).unwrap(), None);
    }
    #[test]
    fn namespace_ambiguity_is_allowed_only_for_unambiguous_selections() {
        let env = environment(&["A.N.x", "B.N.y", "A.N.both", "B.N.both"]);
        let mut scopes = scopes(&env);
        apply(&mut scopes, &env, "open A B").unwrap_or_else(|e| panic!("{}", e.message()));
        apply(&mut scopes, &env, "open N (x y)").unwrap_or_else(|e| panic!("{}", e.message()));
        let before = scopes.current.clone();
        for source in ["open N (both)", "open N hiding x", "open N renaming x -> picked"] {
            assert!(apply(&mut scopes, &env, source).is_err(), "{source}");
            assert_eq!(scopes.current, before);
        }
    }
}
''')

    create(TEST, r'''
//! Native CLI integration, not a claim of pinned-artifact differential evidence.
#![forbid(unsafe_code)]
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
static NEXT: AtomicU64 = AtomicU64::new(0);

fn check(source: &str) -> Output {
    let dir = std::env::temp_dir().join(format!("fln-namespace-opens-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("Main.lean");
    std::fs::write(&path, source).unwrap();
    Command::new(env!("CARGO_BIN_EXE_fln")).arg("check-source").arg(&path).output().unwrap()
}
fn expect(source: &str, accepted: bool) {
    let output = check(source);
    assert_eq!(output.status.success(), accepted, "source:\n{source}\nstdout:\n{}\nstderr:\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
    if !accepted { assert_eq!(output.status.code(), Some(1)); }
}
const PREFIX: &str = "namespace Library\ndef chosen : Nat := 7\ndef other : Nat := 8\nprotected def guarded : Nat := 9\nend Library\n";

#[test]
fn selections_and_renames_elaborate_real_source_declarations() {
    for tail in [
        "open Library (chosen)\ndef result : Nat := chosen\n",
        "open Library (guarded)\ndef result : Nat := guarded\n",
        "open Library renaming guarded -> exposed, chosen → renamed\ndef result : Nat := exposed + renamed\n",
        "open Library hiding other\ndef result : Nat := chosen\n",
    ] { expect(&format!("{PREFIX}{tail}"), true); }
}
#[test]
fn excluded_original_and_unselected_names_are_refused() {
    for tail in [
        "open Library (chosen)\ndef result : Nat := other\n",
        "open Library renaming chosen -> renamed\ndef result : Nat := chosen\n",
        "open Library hiding chosen\ndef result : Nat := chosen\n",
        "open Library hiding absent\ndef result : Nat := 1\n",
        "open Library (chosen absent)\ndef result : Nat := chosen\n",
        "open Library\ndef result : Nat := guarded\n",
    ] { expect(&format!("{PREFIX}{tail}"), false); }
}
#[test]
fn section_local_aliases_expire_without_erasing_checked_declarations() {
    let source = format!("{PREFIX}section\nopen Library renaming chosen -> temporary\ndef inside : Nat := temporary\nend\ndef outside : Nat := inside\n");
    expect(&source, true);
    expect(&format!("{source}def leak : Nat := temporary\n"), false);
}
#[test]
fn dependent_namespace_opens_reach_elaboration() {
    expect("namespace Library.Parser\ndef answer : Nat := 17\nend Library.Parser\nopen Library Parser\ndef result : Nat := answer\n", true);
}
''')

    # Existing SourceScope literals with all fields spelled out need the new
    # lexical state. This field uniquely belongs to SourceScope; compile all
    # workspace targets to check every literal rather than only this package.
    for path in Path('crates').rglob('*.rs'):
        text = pending.get(path, path.read_text())
        updated = re.sub(r'(?m)^(\s*)frontier_recursors: false,\n', r'\1open_declarations: Default::default(),\n\1frontier_recursors: false,\n', text)
        if updated != text:
            pending[path] = updated

    for path, text in sorted(pending.items()):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        print(f'integrated {path}')

    # Read the current work graph without editing it; keep related open work
    # visible beside this source run instead of claiming a broad bead closed.
    graph = Path('.beads/issues.jsonl')
    if graph.is_file():
        for line in graph.open():
            row = json.loads(line)
            title = row.get('title', '')
            if row.get('status') in ('open', 'in_progress') and any(word in title.lower() for word in ('namespace', 'name resolution', 'source grammar', 'ordinary lean')):
                print(json.dumps({'bead': row.get('id'), 'status': row.get('status'), 'title': title}))

if __name__ == '__main__':
    main()
