//! Explicit command scope for native source elaboration. It carries no admission
//! authority and never installs aliases or unchecked constants in the environment.
use super::*;
pub mod options;
mod reserved;
pub mod simp;
pub mod variables;
pub(super) mod visibility;
use crate::aliases::AliasTable;
use crate::protected_names::ProtectedNames;
use fln_core::name::LeafView;
use fln_syntax::source::{BytePos, SourceText};
use fln_syntax::view::SourceView;
pub use visibility::command_scope;

/// The source file and the original byte offset of the command being elaborated.
/// Syntax positions belong to the normalized view; the offset remains in the raw
/// file so partitioned commands and standalone commands use the same boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceSite {
    pub view: std::sync::Arc<SourceView>,
    pub offset: BytePos,
}

impl SourceSite {
    pub fn new(text: SourceText) -> Self {
        Self {
            view: std::sync::Arc::new(SourceView::of(&text)),
            offset: BytePos(0),
        }
    }

    pub fn at_offset(&self, offset: BytePos) -> Self {
        Self {
            view: self.view.clone(),
            offset,
        }
    }

    pub(super) fn syntax_offset(&self, local: BytePos) -> Option<BytePos> {
        let start = self.view.from_original(self.offset).or_else(|| {
            // A command slice may begin at the CR of a leading CRLF. Point
            // mapping rejects that removed byte, but this is a slice boundary:
            // it belongs at the normalized LF that the following byte retains.
            let next = self.offset.0.checked_add(1)?;
            self.view.from_original(BytePos(next))
        })?;
        let offset = start.0.checked_add(local.0)?;
        (offset <= self.view.normalized().len_bytes()).then_some(BytePos(offset))
    }
}

#[derive(Debug, Clone, Default, Eq)]
pub struct SourceScope {
    pub namespace: Name,
    /// A `module` file's declarations are private by default. This is the
    /// actual source module identity, not a namespace opened by the user.
    /// Private names follow the pin's `mkPrivateNameCore` encoding.
    pub private_module: Option<Name>,
    /// The source module's own name (the pin's `moduleNameOfFileName`), in a legacy file as in a
    /// `module` one. A legacy file's declarations stay public by default, but an explicit
    /// `private` one is named under this identity, as `mkPrivateName` names it.
    pub source_module: Option<Name>,
    /// Location used by source terms such as `panic!` that embed their own position.
    /// This is not an exported environment effect or admission authority.
    /// Scope equality excludes this presentation-only metadata.
    pub source_site: Option<SourceSite>,
    /// The enclosing public section's default, or the effective visibility of
    /// a single declaration after [`Self::for_declaration`]. Module identity is
    /// retained independently so private aliases still resolve locally.
    pub public_declarations: bool,
    /// `@[expose] section`'s inherited definition-body default. A declaration's
    /// own `expose`/`no_expose` attributes override this on its effective clone.
    pub expose_definitions: bool,
    /// The pin's inherited `noncomputable section`: declaration code-generation
    /// failures may mark the checked declaration noncomputable. Queries still
    /// require executable code, and successful definitions are not blanket-tagged.
    pub noncomputable_section: bool,
    pub opened: Vec<Name>,
    /// `open X (a b)`'s `OpenDecl.explicit a X.a`, each with `opened.len()` when it was added,
    /// so resolution reads simple and explicit open declarations in one order, as the pin's
    /// single `openDecls` list.
    pub explicit_opens: Vec<(usize, Name, Name)>,
    pub universes: Vec<Name>,
    pub variables: variables::SectionVariables,
    pub instance_scopes: crate::instances::scoped::ActiveScopes,
    /// `attribute [local simp] x`'s rules, in order: `simp`'s default set until this scope ends.
    /// They are never registered, as the pin keeps local attributes out of the `.olean`.
    pub local_simp: Vec<simp::SimpEntry>,
    /// Set only by an engine in `frontier` mode: a compiled declaration may then apply
    /// a recursor the pin's code generator refuses (`codegen.rs`, bead
    /// `franken_lean-z8j.1.6.6`). Not a lexical scope; every command inherits it.
    pub frontier_recursors: bool,
    /// The embedding engine's untrusted arithmetic accelerator. This capability
    /// is inherited by lexical scopes but is never exported as module metadata.
    pub arithmetic: Option<crate::arithmetic::ArithmeticProvider>,
    /// Options `set_option` set and [`options::admit`] honors, until the end of the enclosing
    /// section or namespace. Every elaboration in this scope starts with them.
    pub options: KVMap,
}

impl PartialEq for SourceScope {
    fn eq(&self, other: &Self) -> bool {
        // Destructure every field so adding a semantic scope effect requires an
        // explicit equality decision. A location alone must not change admission
        // dispatch through the existing `scope == SourceScope::default()` checks.
        let Self {
            namespace,
            private_module,
            source_module,
            source_site: _,
            public_declarations,
            expose_definitions,
            noncomputable_section,
            opened,
            explicit_opens,
            universes,
            variables,
            instance_scopes,
            local_simp,
            frontier_recursors,
            arithmetic,
            options,
        } = self;
        namespace == &other.namespace
            && private_module == &other.private_module
            && source_module == &other.source_module
            && public_declarations == &other.public_declarations
            && expose_definitions == &other.expose_definitions
            && noncomputable_section == &other.noncomputable_section
            && opened == &other.opened
            && explicit_opens == &other.explicit_opens
            && universes == &other.universes
            && variables == &other.variables
            && instance_scopes == &other.instance_scopes
            && local_simp == &other.local_simp
            && frontier_recursors == &other.frontier_recursors
            && arithmetic == &other.arithmetic
            && options == &other.options
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeError {
    InvalidName,
    Ambiguous(Name, Vec<Name>),
    UnknownVariable(Name),
    OmittedVariable(Name),
    VariableSelectionLimit,
    /// `protected` on an atomic name in the root namespace (the pin's `mkDeclName`).
    ProtectedOutsideNamespace,
    PrivateShadowsPublic(Name),
    PublicShadowsPrivate(Name),
    /// One of the pin's reserved-name predicates claims the name ([`reserved`]).
    ReservedName(Name),
    /// The pin declares this auxiliary with its definition (`reserved::is_declared_auxiliary`).
    AuxiliaryDeclared(Name),
    /// A definition's equation name is already declared (`ensureEqnReservedNamesAvailable`).
    ReservedNameTaken {
        declaration: Name,
        taken: Name,
    },
    /// A section variable used by a declaration whose binder elaborates differently in the
    /// declaration's scope than at its `variable` command (the pin elaborates it again there).
    ReinterpretedVariable(Name),
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
            Self::ProtectedOutsideNamespace => {
                write!(f, "protected declarations must be in a namespace")
            }
            Self::PrivateShadowsPublic(name) => write!(
                f,
                "private declaration `{}` conflicts with an existing public declaration",
                name.to_display_string()
            ),
            Self::PublicShadowsPrivate(name) => write!(
                f,
                "public declaration `{}` conflicts with an existing private declaration",
                name.to_display_string()
            ),
            Self::ReservedName(name) => {
                write!(f, "`{}` is a reserved name", name.to_display_string())
            }
            Self::AuxiliaryDeclared(name) => {
                write!(
                    f,
                    "`{}` has already been declared",
                    name.to_display_string()
                )
            }
            Self::ReservedNameTaken { declaration, taken } => write!(
                f,
                "failed to declare `{}` because `{}` has already been declared",
                declaration.to_display_string(),
                taken.to_display_string()
            ),
            Self::ReinterpretedVariable(name) => write!(
                f,
                "section variable `{}` elaborates differently here than at its `variable` command",
                name.to_display_string()
            ),
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

/// `eraseDups` (first occurrence kept), then one answer, none, or every candidate in
/// the order the pin's elaborator tries them: `resolveGlobalName`'s list reversed.
fn settle(name: &Name, found: Vec<Name>) -> Result<Option<Name>, ScopeError> {
    let mut unique: Vec<Name> = Vec::new();
    for candidate in found {
        if !unique.contains(&candidate) {
            unique.push(candidate);
        }
    }
    match unique.len() {
        0 => Ok(None),
        1 => Ok(unique.pop()),
        _ => {
            unique.reverse();
            Err(ScopeError::Ambiguous(name.clone(), unique))
        }
    }
}

impl SourceScope {
    pub fn declaration_name(&self, name: &Name) -> Result<Name, ScopeError> {
        self.user_declaration_name(name)
            .map(|name| self.visible_name(&name))
    }

    /// Apply effective visibility to an already qualified generated name. Only a `module`
    /// file's identity names declarations here: a legacy file's explicit `private` declaration
    /// carries its file's identity in `private_module` ([`Self::for_declaration`]), while its
    /// other commands, which may leave `public_declarations` unset, keep their plain names.
    pub(super) fn visible_name(&self, name: &Name) -> Name {
        match &self.private_module {
            Some(module) if !self.public_declarations => {
                Name::num(Name::from_components(["_private"]).append_core(module), 0)
                    .append_core(name)
            }
            _ => name.clone(),
        }
    }

    /// The module a `private` declaration here is named under: the `module` file's, or else a
    /// legacy file's own ([`Self::source_module`]). Resolution and user names read through it,
    /// so a legacy file's private declarations resolve and print as written.
    pub(super) fn private_identity(&self) -> Option<&Name> {
        self.private_module.as_ref().or(self.source_module.as_ref())
    }

    pub(super) fn private_name(&self, name: &Name) -> Name {
        self.private_identity().map_or_else(
            || name.clone(),
            |module| {
                Name::num(Name::from_components(["_private"]).append_core(module), 0)
                    .append_core(name)
            },
        )
    }

    /// Recover a local declaration's user-facing namespace for scope tracking.
    /// An unrelated module's private names are never aliases in this scope.
    pub fn user_name(&self, name: &Name) -> Name {
        let Some(module) = self.private_identity() else {
            return name.clone();
        };
        let prefix = Name::num(Name::from_components(["_private"]).append_core(module), 0);
        let mut cursor = name.clone();
        let mut suffix = Vec::new();
        while cursor != prefix {
            match cursor.leaf_view() {
                LeafView::Str(part) => suffix.push(part.to_owned()),
                _ => return name.clone(),
            }
            cursor = cursor.parent();
        }
        Name::from_components(suffix.iter().rev().map(String::as_str))
    }

    fn user_declaration_name(&self, name: &Name) -> Result<Name, ScopeError> {
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

    /// [`Self::resolve_with_aliases`] with no aliases and nothing protected.
    pub fn resolve(
        &self,
        name: &Name,
        exists: impl FnMut(&Name) -> bool,
    ) -> Result<Option<Name>, ScopeError> {
        self.resolve_with_aliases(
            name,
            exists,
            &AliasTable::default(),
            &ProtectedNames::default(),
        )
    }

    /// The pin's `resolveGlobalName` (vendored `src/Lean/ResolveName.lean:194-217`), in
    /// its three tiers:
    ///
    /// 1. `resolveUsingNamespace`: the current namespace and its parents, innermost
    ///    first, but never the root. At the first one where `resolveQualifiedName`
    ///    finds anything, everything it finds there is the answer.
    /// 2. `resolveExact`: a non-atomic name that names a declaration exactly is that
    ///    declaration, before any opened namespace (`_root_.x` names `x` exactly).
    /// 3. Otherwise every candidate is pooled: the root declaration of that name, each
    ///    opened namespace's `resolveQualifiedName` (`resolveOpenDecls`) and the root
    ///    aliases (`getAliases`). A root declaration is one candidate among them, never
    ///    a winner over an opened namespace's: under `open P`, `foo` names both
    ///    `_root_.foo` and `P.foo`, and only the elaborator's overload resolution by
    ///    type (`elabAppAux`) may choose.
    ///
    /// `resolveQualifiedName env ns id` is `ns ++ id`, unless an atomic `id` would reach
    /// a protected declaration that way, followed by the aliases named `ns ++ id`, with
    /// protected targets dropped when `id` is atomic (`skipProtected := id.isAtomic`).
    /// So under `open Nat` the atomic `add` does not reach the protected `Nat.add`,
    /// while `Nat.add`, or any other non-atomic name, still does. The root
    /// declaration is matched with no protection test, as the pin's
    /// `containsDeclOrReserved env id` is.
    ///
    /// Two or more candidates are [`ScopeError::Ambiguous`], listed in the order the
    /// pin's elaborator tries and reports them: the reverse of `resolveGlobalName`'s
    /// list after `eraseDups`, so the root declaration first, then the opened
    /// namespaces, most recently opened first.
    ///
    /// An explicit open (`open X (y)`, `OpenDecl.explicit y X.y`) answers `y` with `X.y`, and
    /// `y.z` with `X.y.z` when that exists, without the protection test.
    ///
    /// Not modelled: `open X hiding y` and `open X renaming`, and the projection fallback
    /// (`loop p (s::projs)`), which field notation handles.
    pub fn resolve_with_aliases(
        &self,
        name: &Name,
        exists: impl FnMut(&Name) -> bool,
        aliases: &AliasTable,
        protected: &ProtectedNames,
    ) -> Result<Option<Name>, ScopeError> {
        // A seed constant the pin does not have, under a name that resolves to nothing
        // there, is no candidate in any tier: naming it is the pin's "Unknown
        // identifier" (`crate::seed::protected::source_unreachable`).
        let mut declared = exists;
        let mut exists = |candidate: &Name| {
            !crate::seed::protected::source_unreachable(candidate) && declared(candidate)
        };
        // Internally generated field/method names may already carry this
        // module's private prefix. Do not prefix them a second time.
        if self.user_name(name) != *name {
            return Ok(exists(name).then(|| name.clone()));
        }
        let resolve = |candidate: &Name, exists: &mut dyn FnMut(&Name) -> bool| {
            let private = self.private_name(candidate);
            if private != *candidate && exists(&private) {
                Some(private)
            } else {
                exists(candidate).then(|| candidate.clone())
            }
        };
        let parts = components(name)?;
        if parts.first().is_some_and(|p| p == "_root_") {
            let absolute = Name::from_components(parts[1..].iter().map(String::as_str));
            return Ok(resolve(&absolute, &mut exists));
        }
        let atomic = parts.len() == 1;
        let qualified =
            |namespace: &Name, found: &mut Vec<Name>, exists: &mut dyn FnMut(&Name) -> bool| {
                let candidate = namespace.append_core(name);
                if let Some(target) = resolve(&candidate, exists)
                    && !(atomic && protected.contains(&target))
                {
                    found.push(target);
                }
                for target in aliases.targets(&candidate) {
                    if !(atomic && protected.contains(target)) {
                        found.push(target.clone());
                    }
                }
            };
        // 1. `resolveUsingNamespace env id ns`: never the root.
        let mut namespace = self.namespace.clone();
        while !namespace.is_anonymous() {
            let mut found = Vec::new();
            qualified(&namespace, &mut found, &mut exists);
            if !found.is_empty() {
                return settle(name, found);
            }
            namespace = namespace.parent();
        }
        // 2. `resolveExact env id`: only a non-atomic name.
        if !atomic && let Some(target) = resolve(name, &mut exists) {
            return Ok(Some(target));
        }
        // 3. The root declaration, then `resolveOpenDecls` over the open declarations,
        // most recent first, each prepending what it finds, then the root aliases.
        let mut found = Vec::new();
        if let Some(target) = resolve(name, &mut exists) {
            found.push(target);
        }
        // The open declarations in the order they were made: each explicit open recorded with
        // the number of simple opens before it.
        let mut decls: Vec<Result<&Name, (&Name, &Name)>> = Vec::new();
        for position in 0..=self.opened.len() {
            for (at, opened_id, resolved) in &self.explicit_opens {
                if *at == position {
                    decls.push(Err((opened_id, resolved)));
                }
            }
            if let Some(opened) = self.opened.get(position) {
                decls.push(Ok(opened));
            }
        }
        for decl in decls.into_iter().rev() {
            let mut here = Vec::new();
            match decl {
                Ok(opened) => qualified(opened, &mut here, &mut exists),
                // `resolveOpenDecls`'s `OpenDecl.explicit openedId resolvedId`.
                Err((opened_id, resolved)) => {
                    if opened_id == name {
                        here.push(resolved.clone());
                    } else if let Some(rest) = strip_name_prefix(name, opened_id) {
                        let candidate = resolved.append_core(&rest);
                        if exists(&candidate) {
                            here.push(candidate);
                        }
                    }
                }
            }
            here.append(&mut found);
            found = here;
        }
        let mut pooled: Vec<Name> = aliases
            .targets(name)
            .iter()
            .filter(|target| !(atomic && protected.contains(target)))
            .cloned()
            .collect();
        pooled.append(&mut found);
        settle(name, pooled)
    }
}

/// `name` with the strict prefix `prefix` removed (`Name.replacePrefix`'s test `isPrefixOf`).
fn strip_name_prefix(name: &Name, prefix: &Name) -> Option<Name> {
    let parts = components(name).ok()?;
    let head = components(prefix).ok()?;
    if head.is_empty() || parts.len() <= head.len() || parts[..head.len()] != head[..] {
        return None;
    }
    Some(Name::from_components(
        parts[head.len()..].iter().map(String::as_str),
    ))
}

impl Context {
    pub(super) fn scoped(env: &Environment, kernel: Budget, scope: &SourceScope) -> Self {
        let mut context = Self::new(env, kernel);
        context.source_scope = scope.clone();
        context.txn.options = scope.options.clone();
        context.txn.lctx = scope.variables.locals().clone();
        context.next = scope.variables.next();
        context
    }

    pub(super) fn resolve_source_name(
        &mut self,
        name: &Name,
    ) -> Result<Option<Name>, NatDefinitionElabError> {
        self.resolve_source_candidates(name)?
            .map_err(|candidates| error(ScopeError::Ambiguous(name.clone(), candidates)))
    }

    /// [`Self::resolve_source_name`], with the candidates of an ambiguous name handed
    /// back, in the order the pin's elaborator tries them, for overload resolution by
    /// type (`overload.rs`) rather than refused here.
    pub(super) fn resolve_source_candidates(
        &mut self,
        name: &Name,
    ) -> Result<Result<Option<Name>, Vec<Name>>, NatDefinitionElabError> {
        // A name a notation's template supplies carries the expansion's macro scopes
        // (`Name.addMacroScope`). The pin's `resolveName` matches locals by the scoped name,
        // which no binder of the use site has (the template's own binders were matched exactly
        // before resolution), and `resolveGlobalName` reads it with the scopes erased: so a
        // template's `f` means the global `f` even where the use site binds a local `f`.
        let hygienic = name.has_macro_scopes();
        let erased;
        let name = if hygienic {
            erased = name.erase_macro_scopes();
            &erased
        } else {
            name
        };
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
        // A journal that cannot be read is a refusal, never an empty set: that
        // would silently widen resolution to names the pin holds back.
        let protected = self
            .protected_cache
            .read(&self.txn.env)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        // A protected declaration's own recursive reference by its atomic name
        // is held back too: the pin names that local `<namespace>.<short>`.
        let user_name = self.source_scope.user_name(name);
        let atomic = components(&user_name).map_err(error)?.len() == 1 && user_name == *name;
        let held_back_recursion =
            |candidate: &Name| atomic && self.protected_declaration.as_ref() == Some(candidate);
        // The declaration being defined is a local of its own body at the pin (the
        // auxiliary declaration `elabMutualDef` adds), before its recursion context
        // exists here: `namespace A` / `def foo : Nat := foo` names `A.foo`, never a
        // root `foo`, and `open P` never makes `foo` mean `P.foo` there.
        let local = |candidate: &Name| {
            !hygienic && self.txn.lctx.find_by_user_name(candidate).is_some()
                || self
                    .recursion
                    .as_ref()
                    .is_some_and(|r| &r.name == candidate && !held_back_recursion(candidate))
                || self.well_founded.as_ref().is_some_and(|r| {
                    r.target(candidate).is_some() && !held_back_recursion(candidate)
                })
                || (self.defining.as_ref() == Some(candidate) && !held_back_recursion(candidate))
                || self
                    .partial
                    .as_ref()
                    .and_then(|state| state.group.as_ref())
                    .is_some_and(|group| group.names.contains(candidate))
        };
        // Locals first: the pin's `resolveLocalName` runs before `resolveGlobalName`
        // (vendored `src/Lean/Elab/Term.lean`, `resolveName`), so a local, or the
        // declaration's own recursive reference, named at the current namespace or a
        // parent is never one candidate among globals. `_root_.x` names no local.
        if !is_root_qualified(name) && !hygienic {
            let mut namespace = self.source_scope.namespace.clone();
            loop {
                let candidate = namespace.append_core(name);
                if local(&candidate) {
                    return Ok(Ok(Some(candidate)));
                }
                let private = self.source_scope.private_name(&candidate);
                if private != candidate && local(&private) {
                    return Ok(Ok(Some(private)));
                }
                if namespace.is_anonymous() {
                    break;
                }
                namespace = namespace.parent();
            }
        }
        match self.source_scope.resolve_with_aliases(
            name,
            |candidate| self.txn.env.contains(candidate) || local(candidate),
            &aliases,
            &protected,
        ) {
            Ok(found) => Ok(Ok(found)),
            Err(ScopeError::Ambiguous(_, candidates)) => Ok(Err(candidates)),
            Err(other) => Err(error(other)),
        }
    }

    /// The pin's `mkDeclName` for a `protected` declaration (vendored
    /// `src/Lean/Elab/DeclModifiers.lean`): an atomic short name in the root
    /// namespace is refused. `_root_.p.s` declares `s` in namespace `p`.
    pub(super) fn check_protected_declaration_name(
        &self,
        name: &Name,
    ) -> Result<(), NatDefinitionElabError> {
        let parts = components(name).map_err(error)?;
        let (root_namespace, atomic) = if parts.first().is_some_and(|p| p == "_root_") {
            (parts.len() <= 2, true)
        } else {
            (self.source_scope.namespace.is_anonymous(), parts.len() == 1)
        };
        if root_namespace && atomic {
            return Err(error(ScopeError::ProtectedOutsideNamespace));
        }
        Ok(())
    }

    pub(super) fn enter_declaration(
        &mut self,
        name: &Name,
    ) -> Result<Name, NatDefinitionElabError> {
        self.tick()?;
        let user_name = self
            .source_scope
            .user_declaration_name(name)
            .map_err(error)?;
        if self.source_scope.private_module.is_some()
            && !self.source_scope.public_declarations
            && self.txn.env.contains(&user_name)
        {
            return Err(error(ScopeError::PrivateShadowsPublic(user_name)));
        }
        self.source_scope
            .check_public_name(&user_name, &self.txn.env)?;
        let name = self.source_scope.declaration_name(name).map_err(error)?;
        let private = self.source_scope.private_name(&user_name);
        if reserved::is_declared_auxiliary(&self.txn.env, &name)
            || reserved::is_declared_auxiliary(&self.txn.env, &user_name)
        {
            return Err(error(ScopeError::AuxiliaryDeclared(name)));
        }
        if reserved::is_reserved(&self.txn.env, &user_name)
            || reserved::is_reserved(&self.txn.env, &private)
        {
            return Err(error(ScopeError::ReservedName(name)));
        }
        self.source_scope.namespace = user_name.parent();
        Ok(name)
    }

    /// `ensureEqnReservedNamesAvailable`, which the pin runs for every definition, theorem,
    /// abbreviation, instance and `opaque` (Lean/Elab/PreDefinition/Main.lean:306,
    /// Structural/Eqns.lean:159), not for an axiom or an inductive type.
    pub(super) fn ensure_equation_names_available(
        &mut self,
        declaration: &Name,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        match reserved::taken_equation_name(&self.txn.env, declaration) {
            Some(taken) => Err(error(ScopeError::ReservedNameTaken {
                declaration: declaration.clone(),
                taken,
            })),
            None => Ok(()),
        }
    }
}

/// Candidates only. The caller must use the same kernel/council publication as
/// an unscoped declaration; scope resolution cannot mint a checked declaration.
/// This raw candidate API omits source effects; source publication should use
/// [`elaborate_definition_with_effects`] instead.
pub fn elaborate_definition(
    syntax: &Syntax,
    env: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    super::definition_scoped(syntax, env, kernel, scope)
}

/// Elaborate the candidate and its explicit source effects in one transaction.
/// The caller must check the declaration before installing any returned effect.
pub fn elaborate_definition_with_effects(
    syntax: &Syntax,
    env: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<super::ElaboratedDeclaration, NatDefinitionElabError> {
    super::definition_scoped_with_effects(syntax, env, kernel, scope)
}

/// An `#eval` candidate (a generated definition) with names resolved in `scope`. As for
/// [`elaborate_definition`], only a candidate: the caller admits it like any other.
pub fn elaborate_evaluation(
    syntax: &Syntax,
    generated_name: Name,
    env: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<Declaration, NatDefinitionElabError> {
    super::query_scoped(syntax, generated_name, env, kernel, true, scope)
        .map(|(declaration, _)| declaration)
}

/// A `#check` candidate with names resolved in `scope`, closed over the section variables its
/// term uses, and their positions in [`variables::SectionVariables::declared`], outermost first. The
/// candidate's value and type begin with one binder per position; a printer opens them again
/// to show the term as the pin does, with those variables free.
pub fn elaborate_check(
    syntax: &Syntax,
    generated_name: Name,
    env: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<(Declaration, Vec<usize>), NatDefinitionElabError> {
    super::query_scoped(syntax, generated_name, env, kernel, false, scope)
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
    let mut context = Context::scoped(env, kernel, scope);
    example_in_context(syntax, name, &mut context)
}

pub(super) fn example_in_context(
    syntax: &Syntax,
    name: Name,
    context: &mut Context,
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
    super::doc_comment_slot(&modifiers[0])?;
    for (index, modifier) in modifiers.iter().enumerate().skip(1) {
        // `noncomputable example`: the pin's examples are never compiled anyway.
        if index == super::NONCOMPUTABLE_SLOT {
            super::noncomputable_slot(modifier)?;
            continue;
        }
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
    super::definition_in_context_named(&candidate, context, Some(name))
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

    #[test]
    fn source_locations_do_not_change_semantic_scope_equality() {
        let mut scope = SourceScope {
            source_site: Some(SourceSite::new(
                SourceText::from_utf8(b"\n#check Nat").unwrap(),
            )),
            ..SourceScope::default()
        };
        assert_eq!(scope, SourceScope::default());
        scope.source_site = Some(
            SourceSite::new(SourceText::from_utf8(b"\n\n#check Bool").unwrap())
                .at_offset(BytePos(2)),
        );
        assert_eq!(scope, SourceScope::default());
        scope.namespace = n("Different");
        assert_ne!(scope, SourceScope::default());
    }

    #[test]
    fn source_sites_map_normalized_syntax_after_original_crlf_boundaries() {
        let prefix = "-- π\r\n";
        let command = "#eval Id.run do\r\n  assert! false\r\n  return 42\r\n";
        let source = format!("{prefix}{command}");
        let site = SourceSite::new(SourceText::from_utf8(source.as_bytes()).unwrap())
            .at_offset(BytePos(prefix.len()));
        let local = BytePos(command.replace("\r\n", "\n").find("assert!").unwrap());
        let offset = site.syntax_offset(local).unwrap();
        let position = site.view.normalized().position_of(offset).unwrap();
        assert_eq!((position.line, position.scalar_column), (2, 2));
        assert_eq!(
            site.view.to_original(offset).0,
            source.find("assert!").unwrap()
        );
        assert_eq!(site.view.reconstruct_original(), source.as_bytes());

        let blank = SourceSite::new(SourceText::from_utf8(b"\r\n#check Nat").unwrap());
        let position = blank
            .view
            .normalized()
            .position_of(blank.syntax_offset(BytePos(1)).unwrap())
            .unwrap();
        assert_eq!((position.line, position.scalar_column), (1, 0));
    }

    /// The pin's `resolveGlobalName` consults `getAliases` beside declarations
    /// at each namespace and in each opened namespace; `_root_.x` is exact.
    #[test]
    fn export_aliases_resolve_beside_declarations_at_each_namespace() {
        let scope = SourceScope {
            namespace: n("Outer"),
            private_module: None,
            source_module: None,
            source_site: None,
            public_declarations: false,
            expose_definitions: false,
            noncomputable_section: false,
            opened: vec![n("O")],
            explicit_opens: Vec::new(),
            universes: vec![],
            variables: variables::SectionVariables::default(),
            instance_scopes: crate::instances::scoped::ActiveScopes::default(),
            local_simp: Vec::new(),
            frontier_recursors: false,
            arithmetic: None,
            options: KVMap::new(),
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
        let resolve = |name: &str| {
            scope.resolve_with_aliases(
                &n(name),
                |x| env.contains(x),
                &aliases,
                &ProtectedNames::default(),
            )
        };
        // A root alias, as `export Decidable (decide)` in the root namespace.
        assert_eq!(resolve("decide").unwrap(), Some(n("Decidable.decide")));
        // At one namespace a declaration and an alias there are both candidates
        // (`resolveQualifiedName` returns `resolvedId :: aliases`), listed alias
        // first as the pin reports them. Pinned `lean` v4.32.0, 2026-10-06:
        // `namespace Outer` / `def neg : Nat := 2` / `export Other (neg)` /
        // `def x : Nat := neg` is "Ambiguous term neg", interpretations
        // `Other.neg`, `Outer.neg`.
        assert_eq!(
            resolve("mine"),
            Err(ScopeError::Ambiguous(
                n("mine"),
                vec![n("Bool.not"), n("Outer.mine")]
            ))
        );
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

    /// The pin's `resolveGlobalName` tiers (vendored `src/Lean/ResolveName.lean:194-217`,
    /// bead `fln-wh2j`): the current namespace and its parents first, never the root;
    /// then a non-atomic name exactly; then the root declaration pooled with every opened
    /// namespace's, listed root first and then most recently opened first, as the pin
    /// lists "Possible interpretations" (pinned `lean` v4.32.0, 2026-10-06: `open P`,
    /// `open Q` gives `_root_.foo`, `Q.foo`, `P.foo`).
    #[test]
    fn a_root_declaration_is_one_candidate_among_the_opened_ones() {
        let env = ["foo", "P.foo", "Q.foo", "A.foo", "Q.P.foo", "R.only"]
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
        let scope = |namespace: &str, opened: &[&str]| SourceScope {
            namespace: if namespace.is_empty() {
                Name::anonymous()
            } else {
                n(namespace)
            },
            opened: opened.iter().map(|name| n(name)).collect(),
            ..SourceScope::default()
        };
        let resolve =
            |scope: &SourceScope, name: &str| scope.resolve(&n(name), |x| env.contains(x));
        // The root declaration and an opened one: both, root first.
        assert_eq!(
            resolve(&scope("", &["P"]), "foo"),
            Err(ScopeError::Ambiguous(n("foo"), vec![n("foo"), n("P.foo")]))
        );
        // Two opened namespaces: the most recently opened is listed first.
        assert_eq!(
            resolve(&scope("", &["P", "Q"]), "foo"),
            Err(ScopeError::Ambiguous(
                n("foo"),
                vec![n("foo"), n("Q.foo"), n("P.foo")]
            ))
        );
        // A name only an opened namespace provides, and one only the root provides.
        assert_eq!(resolve(&scope("", &["R"]), "only"), Ok(Some(n("R.only"))));
        assert_eq!(resolve(&scope("", &["R"]), "foo"), Ok(Some(n("foo"))));
        // The current namespace is found before the root and the opened namespaces.
        assert_eq!(resolve(&scope("A", &["P"]), "foo"), Ok(Some(n("A.foo"))));
        // A non-atomic name naming a declaration exactly is that declaration, before
        // an opened namespace's `Q.P.foo` (`resolveExact`).
        assert_eq!(resolve(&scope("", &["Q"]), "P.foo"), Ok(Some(n("P.foo"))));
        // `_root_.foo` names `foo` exactly.
        assert_eq!(
            resolve(&scope("", &["P"]), "_root_.foo"),
            Ok(Some(n("foo")))
        );
    }

    /// The pin's `resolveQualifiedName`: an atomic `id` never reaches a protected
    /// `ns ++ id` through the current namespace, its parents or an opened
    /// namespace, and `getAliases ... (skipProtected := id.isAtomic)` drops a
    /// protected alias target. Non-atomic names and the root's exact match are
    /// unaffected (vendored `src/Lean/ResolveName.lean`).
    #[test]
    fn protected_declarations_are_held_back_from_atomic_names_only() {
        let env = [
            "Nat.add",
            "Nat.pred",
            "Lean.SourceInfo.none",
            "Outer.Nat.sub",
            "top",
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
        let env = [("plus", "Nat.add"), ("Q.plus", "Nat.add")]
            .into_iter()
            .fold(env, |env, (alias, target)| {
                crate::aliases::register(&env, &n(alias), &n(target)).unwrap()
            });
        let env = crate::protected_names::register_module(
            &env,
            &[
                n("Nat.add"),
                n("Lean.SourceInfo.none"),
                n("Outer.Nat.sub"),
                n("top"),
            ],
        )
        .unwrap();
        let aliases = AliasTable::read(&env).unwrap();
        let protected = ProtectedNames::read(&env).unwrap();
        let scope = |namespace: &str, opened: &[&str]| SourceScope {
            private_module: None,
            source_module: None,
            source_site: None,
            public_declarations: false,
            expose_definitions: false,
            noncomputable_section: false,
            namespace: n(namespace),
            opened: opened.iter().map(|o| n(o)).collect(),
            explicit_opens: Vec::new(),
            universes: vec![],
            variables: variables::SectionVariables::default(),
            instance_scopes: crate::instances::scoped::ActiveScopes::default(),
            local_simp: Vec::new(),
            frontier_recursors: false,
            arithmetic: None,
            options: KVMap::new(),
        };
        let resolve = |scope: &SourceScope, name: &str, protected: &ProtectedNames| {
            scope.resolve_with_aliases(&n(name), |x| env.contains(x), &aliases, protected)
        };
        let none = ProtectedNames::default();
        // `open Nat`: `add` is held back, `pred` is not, `Nat.add` is exact.
        let open_nat = scope("", &["Nat"]);
        assert_eq!(resolve(&open_nat, "add", &protected).unwrap(), None);
        assert_eq!(
            resolve(&open_nat, "add", &none).unwrap(),
            Some(n("Nat.add"))
        );
        assert_eq!(
            resolve(&open_nat, "pred", &protected).unwrap(),
            Some(n("Nat.pred"))
        );
        assert_eq!(
            resolve(&open_nat, "Nat.add", &protected).unwrap(),
            Some(n("Nat.add"))
        );
        // Inside `namespace Nat` the same: the pin applies the test at each namespace.
        let in_nat = scope("Nat", &[]);
        assert_eq!(resolve(&in_nat, "add", &protected).unwrap(), None);
        assert_eq!(resolve(&in_nat, "add", &none).unwrap(), Some(n("Nat.add")));
        // A held-back name at an inner namespace does not stop the walk outward:
        // `Outer.Nat.sub` is protected, and `Nat.sub` (non-atomic) is unaffected.
        let in_outer_nat = scope("Outer.Nat", &[]);
        assert_eq!(resolve(&in_outer_nat, "sub", &protected).unwrap(), None);
        assert_eq!(
            resolve(&scope("Outer", &[]), "Nat.sub", &protected).unwrap(),
            Some(n("Outer.Nat.sub"))
        );
        // A non-atomic suffix reaches a protected declaration through `open`.
        let open_lean = scope("", &["Lean"]);
        assert_eq!(
            resolve(&open_lean, "SourceInfo.none", &protected).unwrap(),
            Some(n("Lean.SourceInfo.none"))
        );
        assert_eq!(
            resolve(&scope("", &["Lean.SourceInfo"]), "none", &protected).unwrap(),
            None
        );
        // An alias to a protected declaration is dropped for an atomic name only.
        assert_eq!(resolve(&open_nat, "plus", &protected).unwrap(), None);
        assert_eq!(
            resolve(&open_nat, "plus", &none).unwrap(),
            Some(n("Nat.add"))
        );
        assert_eq!(
            resolve(&open_nat, "Q.plus", &protected).unwrap(),
            Some(n("Nat.add"))
        );
        // The root's exact match has no protection test.
        assert_eq!(
            resolve(&open_nat, "top", &protected).unwrap(),
            Some(n("top"))
        );
    }

    #[test]
    fn namespace_prefixes_root_escapes_and_ambiguous_opens_have_distinct_rules() {
        let scope = SourceScope {
            private_module: None,
            source_module: None,
            source_site: None,
            public_declarations: false,
            expose_definitions: false,
            noncomputable_section: false,
            namespace: n("Outer.Inner"),
            opened: vec![n("A"), n("B"), n("A")],
            explicit_opens: Vec::new(),
            universes: vec![],
            variables: variables::SectionVariables::default(),
            instance_scopes: crate::instances::scoped::ActiveScopes::default(),
            local_simp: Vec::new(),
            frontier_recursors: false,
            arithmetic: None,
            options: KVMap::new(),
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
