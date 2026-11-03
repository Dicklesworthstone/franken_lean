//! Receipt-bound parser descriptions, independent of native source templates.
//!
//! This module consumes reconstructed data, not `.olean` bytes or executable
//! parser closures. The importer must bind every description to its checked
//! declaration. Here the complete ordered product is validated against the
//! parser's executable subset before any token, kind or production is added.

use super::*;

/// One decoded parser-extension row. Its scope and position in the module's
/// journal are retained, including token/kind rows without a parser row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportedSyntaxEntry {
    Token {
        scope: Option<Name>,
        token: String,
    },
    Kind {
        scope: Option<Name>,
        kind: Name,
    },
    Category {
        scope: Option<Name>,
        category: Name,
        declaration: Name,
        behavior: IdentBehavior,
    },
    /// The declaration's module and optional namespace are in `SyntaxDecl`.
    /// Descriptions must already contain resolved parser dependencies: an
    /// executable `Parser` constant is never resolved through the census.
    Parser(Arc<SyntaxDecl>),
}

/// The complete parser journal of an admitted module, in replay order. This
/// product grants no declaration authority and contains no source templates.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ImportedSyntaxModule {
    pub entries: Vec<ImportedSyntaxEntry>,
}

impl ImportedSyntaxModule {
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[derive(Default)]
pub(super) struct ArtifactGrammar {
    pub(super) imported: Vec<Arc<SyntaxDecl>>,
    scoped: BTreeMap<Name, Vec<Arc<SyntaxDecl>>>,
    pub(super) tokens: BTreeSet<String>,
    scoped_tokens: BTreeMap<Name, BTreeSet<String>>,
    pub(super) kinds: BTreeSet<Name>,
    scoped_kinds: BTreeMap<Name, BTreeSet<Name>>,
    pub(super) categories: BTreeSet<Name>,
    pub(super) owners: BTreeSet<Name>,
    pub(super) namespaces: BTreeSet<Name>,
    work: usize,
}

impl ArtifactGrammar {
    pub(super) fn activate(
        &self,
        namespace: &Name,
        tokens: &mut BTreeSet<String>,
        kinds: &mut BTreeSet<Name>,
        declarations: &mut Vec<Arc<SyntaxDecl>>,
    ) {
        if let Some(scoped) = self.scoped.get(namespace) {
            declarations.extend(scoped.iter().cloned());
        }
        if let Some(scoped) = self.scoped_tokens.get(namespace) {
            tokens.extend(scoped.iter().cloned());
        }
        if let Some(scoped) = self.scoped_kinds.get(namespace) {
            kinds.extend(scoped.iter().cloned());
        }
    }
}

/// A missing first-token set is a primitive production (for example `num` in
/// a custom category). It cannot coexist with another leading production in
/// this bounded adapter: their possible overlap has not been established.
#[derive(Default)]
struct Heads {
    tokens: BTreeMap<(Name, bool), BTreeSet<String>>,
    primitive: BTreeSet<(Name, bool)>,
}

impl Heads {
    fn existing(&mut self, declaration: &SyntaxDecl) {
        let Some(category) = &declaration.category else {
            return;
        };
        let body = match &declaration.descr {
            Descr::TrailingNode { body, .. } => body.as_ref(),
            other => other,
        };
        let tokens = heads(body, 0);
        let key = (category.clone(), declaration.leading);
        if tokens.is_empty() {
            self.primitive.insert(key);
        } else {
            self.tokens.entry(key).or_default().extend(tokens);
        }
    }

    fn add(&mut self, declaration: &SyntaxDecl, tokens: Vec<String>) -> Result<(), &'static str> {
        let category = declaration
            .category
            .as_ref()
            .ok_or("artifact parser registration without a category")?;
        let key = (category.clone(), declaration.leading);
        if self.primitive.contains(&key) {
            return Err("overlapping artifact parser productions");
        }
        if tokens.is_empty() {
            if self
                .tokens
                .get(&key)
                .is_some_and(|tokens| !tokens.is_empty())
            {
                return Err("overlapping artifact parser productions");
            }
            self.primitive.insert(key);
        } else {
            let occupied = self.tokens.entry(key).or_default();
            if tokens.iter().any(|token| occupied.contains(token)) {
                return Err("overlapping artifact parser productions");
            }
            occupied.extend(tokens);
        }
        Ok(())
    }
}

impl FileGrammar {
    /// Install a complete checked artifact's ordered parser product at the
    /// beginning of a file. A refusal leaves the grammar and its caches intact.
    ///
    /// The supported subset is data-only descriptions with native aliases,
    /// disjoint reserved first tokens, atom-bounded leading `term` syntax, ordinary
    /// symbol/term infix syntax, and leading/trailing custom-category syntax.
    /// A lone primitive production (such as `num`) is supported in a custom
    /// category. Unknown closures/aliases, scoped categories, ambiguous heads,
    /// contextual column checks, category quotation parsers and unsupported
    /// precedence forms are refused.
    /// Scoped tokens/kinds activate lexically and remain independent of their
    /// parser rows. No absent token or kind row is fabricated from a descriptor.
    ///
    /// Use `own_syntax_only` first. Census declarations do not supply missing
    /// artifact descriptions, category authority, aliases or owner bindings.
    /// These inputs are inherited grammar and never native source exports.
    pub fn import_artifact(&mut self, module: &ImportedSyntaxModule) -> Result<(), &'static str> {
        if module.is_empty() {
            return Ok(());
        }
        if self.imports_entered {
            return Err("artifact parsers require a grammar without census registrations");
        }
        if self.scopes.len() != 1
            || !self.top().trail.is_empty()
            || !self.declared.is_empty()
            || !self.declared_categories.is_empty()
        {
            return Err("artifact parsers must be installed before source scope transitions");
        }
        let mut remaining = MAX_TEMPLATE_NODES
            .checked_sub(self.artifact.work)
            .ok_or("artifact parser description work past the budget")?;
        if module.entries.len() > remaining {
            return Err("artifact parser description work past the budget");
        }
        let mut categories: BTreeSet<_> = self
            .native_categories
            .iter()
            .chain(self.declared_categories.keys())
            .chain(self.artifact.categories.iter())
            .cloned()
            .collect();
        let mut names = self.constants.clone();
        let mut occupied = Heads::default();
        for declaration in self
            .native_imported
            .iter()
            .chain(self.native_scoped.values().flatten())
            .chain(self.artifact.imported.iter())
            .chain(self.artifact.scoped.values().flatten())
            .chain(self.declared.iter())
            .chain(
                self.imported
                    .iter()
                    .filter(|decl| self.interpolation_kinds.contains(&decl.decl)),
            )
        {
            occupied.existing(declaration);
        }
        // The pass sees categories in journal order and checks every row,
        // including inactive scoped entries. Mutation begins only below.
        for entry in &module.entries {
            charge(&mut remaining)?;
            match entry {
                ImportedSyntaxEntry::Token { scope, token } => {
                    check_scope(scope)?;
                    check_token(token)?;
                }
                ImportedSyntaxEntry::Kind { scope, kind } => {
                    check_scope(scope)?;
                    if kind.is_anonymous() {
                        return Err("anonymous artifact syntax node kind");
                    }
                }
                ImportedSyntaxEntry::Category {
                    scope,
                    category,
                    declaration,
                    ..
                } => {
                    if scope.is_some() {
                        return Err("scoped artifact parser categories");
                    }
                    if !matches!(category.leaf_view(), LeafView::Str(name) if !name.is_empty())
                        || declaration.is_anonymous()
                    {
                        return Err("invalid artifact parser category name");
                    }
                    if unsupported_builtin_category(category) {
                        return Err("artifact registration for an unsupported builtin category");
                    }
                    if !builtin_category(category) {
                        categories.insert(category.clone());
                    }
                    names.insert(declaration.clone());
                }
                ImportedSyntaxEntry::Parser(declaration) => {
                    check_scope(&declaration.scope)?;
                    if declaration.module.is_anonymous() || declaration.decl.is_anonymous() {
                        return Err("artifact parser without a named module and declaration");
                    }
                    if !names.insert(declaration.decl.clone()) {
                        return Err("an artifact parser declaration is already declared");
                    }
                    let first = registration(declaration, &categories, &mut remaining)?;
                    occupied.add(declaration, first)?;
                }
            }
        }
        // Tokens and kinds are deliberately not collected from parser bodies.
        // ParserExtension.addEntryImpl registers them only through their rows.
        for entry in &module.entries {
            match entry {
                ImportedSyntaxEntry::Token { scope, token } => match scope {
                    Some(namespace) => {
                        self.artifact.namespaces.insert(namespace.clone());
                        self.artifact
                            .scoped_tokens
                            .entry(namespace.clone())
                            .or_default()
                            .insert(token.clone());
                    }
                    None => {
                        self.artifact.tokens.insert(token.clone());
                    }
                },
                ImportedSyntaxEntry::Kind { scope, kind } => match scope {
                    Some(namespace) => {
                        self.artifact.namespaces.insert(namespace.clone());
                        self.artifact
                            .scoped_kinds
                            .entry(namespace.clone())
                            .or_default()
                            .insert(kind.clone());
                    }
                    None => {
                        self.artifact.kinds.insert(kind.clone());
                    }
                },
                ImportedSyntaxEntry::Category {
                    category,
                    declaration,
                    behavior,
                    ..
                } => {
                    // Existing active categories win, exactly as extension
                    // replay does. Inactive census categories confer no state.
                    if !builtin_category(category)
                        && !self.native_categories.contains(category)
                        && !self.declared_categories.contains_key(category)
                        && self.artifact.categories.insert(category.clone())
                    {
                        self.categories.insert(category.clone(), *behavior);
                    }
                    self.constants.insert(declaration.clone());
                    self.artifact.owners.insert(declaration.clone());
                }
                ImportedSyntaxEntry::Parser(declaration) => {
                    self.constants.insert(declaration.decl.clone());
                    self.artifact.owners.insert(declaration.decl.clone());
                    match &declaration.scope {
                        Some(namespace) => {
                            self.artifact.namespaces.insert(namespace.clone());
                            self.artifact
                                .scoped
                                .entry(namespace.clone())
                                .or_default()
                                .push(Arc::clone(declaration));
                        }
                        None => self.artifact.imported.push(Arc::clone(declaration)),
                    }
                }
            }
        }
        self.artifact.work = MAX_TEMPLATE_NODES - remaining;
        self.generation += 1;
        self.cache.borrow_mut().clear();
        Ok(())
    }
}

fn check_scope(scope: &Option<Name>) -> Result<(), &'static str> {
    if scope.as_ref().is_some_and(Name::is_anonymous) {
        Err("anonymous artifact syntax scope")
    } else {
        Ok(())
    }
}

fn check_token(token: &str) -> Result<(), &'static str> {
    if token.is_empty() {
        Err("empty artifact syntax token")
    } else if token.len() > MAX_TEMPLATE_NODES {
        Err("artifact syntax token past the budget")
    } else {
        Ok(())
    }
}

fn charge(remaining: &mut usize) -> Result<(), &'static str> {
    *remaining = remaining
        .checked_sub(1)
        .ok_or("artifact parser description work past the budget")?;
    Ok(())
}

fn builtin_category(category: &Name) -> bool {
    matches!(
        simple(category).as_deref(),
        Some("term" | "tactic" | "attr" | "command")
    )
}

fn unsupported_builtin_category(category: &Name) -> bool {
    !builtin_category(category)
        && extension_census()
            .categories
            .get(category)
            .is_some_and(|(_, module)| module.is_none())
}

/// Validate the dispatch shape separately from descriptor constructors: the
/// native term tables intentionally implement only a subset of Pratt syntax.
fn registration(
    declaration: &SyntaxDecl,
    categories: &BTreeSet<Name>,
    remaining: &mut usize,
) -> Result<Vec<String>, &'static str> {
    let category = declaration
        .category
        .as_ref()
        .ok_or("artifact parser registration without a category")?;
    if !builtin_category(category) && !categories.contains(category) {
        return Err("artifact parser names an unavailable category");
    }
    charge(remaining)?;
    let term = simple(category).as_deref() == Some("term");
    let custom = !builtin_category(category);
    let (body, first) = match (&declaration.descr, declaration.leading) {
        (Descr::Node { kind, prec, body }, true) => {
            if kind.is_anonymous() || *prec > MAX_PREC {
                return Err("unsupported artifact leading-node precedence or kind");
            }
            check_root_kind(kind)?;
            if term && (*prec < LEAD_PREC || !ends_with_atom(body, 0)) {
                return Err("artifact term parser is not an atom-bounded leading production");
            }
            let first = heads(body, 0);
            if term && first.iter().any(|token| token.starts_with("`(")) {
                return Err(
                    "artifact category quotation parsers require their own supported registration",
                );
            }
            if first.is_empty() && !(custom && primitive(body)) {
                return Err("artifact leading parser has no supported first token");
            }
            if !first.is_empty() && !reserved_heads(body, 0) {
                return Err("artifact leading parser requires reserved first tokens");
            }
            (body.as_ref(), first)
        }
        (
            Descr::TrailingNode {
                kind,
                prec,
                lhs_prec,
                body,
            },
            false,
        ) => {
            if kind.is_anonymous() || *prec > MAX_PREC || *lhs_prec > MAX_PREC {
                return Err("unsupported artifact trailing-node precedence or kind");
            }
            check_root_kind(kind)?;
            if term {
                let Descr::Binary(alias, left, right) = body.as_ref() else {
                    return Err("artifact trailing term parser is not a supported infix");
                };
                let Descr::Cat(operand, rhs_prec) = right.as_ref() else {
                    return Err("artifact trailing term parser is not a supported infix");
                };
                if *prec >= 256
                    || simple(alias).as_deref() != Some("andthen")
                    || simple(operand).as_deref() != Some("term")
                    || *rhs_prec > MAX_PREC
                    || !matches!(left.as_ref(), Descr::Symbol(_) | Descr::UnicodeSymbol(..))
                {
                    return Err("artifact trailing term parser is not a supported infix");
                }
                charge(remaining)?; // andthen
                charge(remaining)?; // the RHS is dispatched by the infix Pratt parser
                descriptor(left, categories, remaining, 1)?;
                let first = heads(left, 0);
                if first
                    .iter()
                    .any(|token| builtin_tokens().contains(token.as_str()))
                {
                    return Err("artifact infix overlaps a builtin token");
                }
                return Ok(first);
            }
            if !custom {
                return Err("artifact trailing parser for an unsupported builtin category");
            }
            let first = heads(body, 0);
            if first.is_empty() || !reserved_heads(body, 0) {
                return Err("artifact trailing parser has no supported first token");
            }
            (body.as_ref(), first)
        }
        _ => {
            return Err(
                "artifact parser root disagrees with its leading/trailing declaration type",
            );
        }
    };
    if !custom
        && first
            .iter()
            .any(|token| builtin_tokens().contains(token.as_str()))
    {
        return Err("artifact leading parser overlaps a builtin token");
    }
    if descriptor(body, categories, remaining, 1)? {
        return Err("artifact parser production can succeed without consuming input");
    }
    Ok(first)
}

fn primitive(descr: &Descr) -> bool {
    matches!(descr, Descr::Const(name) if matches!(simple(name).as_deref(),
        Some("ident" | "num" | "str" | "char" | "scientific" | "name" | "hole")))
}

fn check_root_kind(kind: &Name) -> Result<(), &'static str> {
    // Some existing native parsers select a census notation by its active root
    // kind. A different artifact owner must not activate one by merely reusing
    // that kind for a newly spelled production. The census is a refusal set,
    // never a source of missing executable descriptions.
    if extension_census().decls.iter().any(|declaration| {
        matches!(&declaration.descr,
            Descr::Node { kind: known, .. } | Descr::TrailingNode { kind: known, .. }
                if known == kind)
    }) {
        Err("artifact parser kind overlaps census-backed native syntax")
    } else {
        Ok(())
    }
}

// `LeadingIdentBehavior` and `NonReservedSymbol.includeIdent` select different
// lookup tables. This adapter's disjoint reserved heads avoid those unsupported
// mixed identifier/keyword choices; non-reserved symbols remain usable inside
// an already selected production.
fn reserved_heads(descr: &Descr, depth: usize) -> bool {
    if depth > MAX_DESCR_DEPTH {
        return false;
    }
    match descr {
        Descr::Symbol(_) | Descr::UnicodeSymbol(..) => true,
        Descr::Node { body, .. } => reserved_heads(body, depth + 1),
        Descr::Unary(name, body) if transparent(name) => reserved_heads(body, depth + 1),
        Descr::Binary(name, left, right) => match simple(name).as_deref() {
            Some("andthen") => reserved_heads(left, depth + 1),
            Some("orelse") => reserved_heads(left, depth + 1) && reserved_heads(right, depth + 1),
            _ => false,
        },
        _ => false,
    }
}

/// Check every constructor and return whether it may consume no input. The
/// conservative test also prevents non-progressing repetitions from installing.
fn descriptor(
    descr: &Descr,
    categories: &BTreeSet<Name>,
    remaining: &mut usize,
    depth: usize,
) -> Result<bool, &'static str> {
    if depth > MAX_DESCR_DEPTH {
        return Err("artifact parser description depth past the budget");
    }
    charge(remaining)?;
    match descr {
        Descr::Symbol(token) | Descr::NonReservedSymbol(token, _) => {
            check_token(token.trim())?;
            Ok(false)
        }
        Descr::UnicodeSymbol(token, ascii, _) => {
            check_token(token.trim())?;
            check_token(ascii.trim())?;
            Ok(false)
        }
        Descr::Const(name) => match simple(name).as_deref() {
            Some(
                "ident" | "num" | "str" | "char" | "scientific" | "name" | "hole" | "tacticSeq",
            ) => Ok(false),
            Some(
                "noWs"
                | "ppSpace"
                | "ppLine"
                | "ppHardSpace"
                | "ppAllowUngrouped"
                | "ppHardLineUnlessUngrouped",
            ) => Ok(true),
            _ => Err("artifact parser uses an unsupported constant alias"),
        },
        Descr::Unary(name, body) => {
            let nullable = descriptor(body, categories, remaining, depth + 1)?;
            match simple(name).as_deref() {
                Some("optional" | "notFollowedBy") => Ok(true),
                Some(alias @ ("many" | "many1")) => {
                    if nullable {
                        return Err("artifact parser repeats a nullable production");
                    }
                    Ok(alias == "many")
                }
                Some(
                    "group" | "ppGroup" | "ppIndent" | "ppDedent" | "ppDedentIfGrouped"
                    | "ppRealFill" | "ppRealGroup",
                ) => Ok(nullable),
                _ => Err("artifact parser uses an unsupported unary alias"),
            }
        }
        Descr::Binary(name, left, right) => {
            let left = descriptor(left, categories, remaining, depth + 1)?;
            let right = descriptor(right, categories, remaining, depth + 1)?;
            match simple(name).as_deref() {
                Some("andthen") => Ok(left && right),
                Some("orelse") => Ok(left || right),
                _ => Err("artifact parser uses an unsupported binary alias"),
            }
        }
        Descr::Node { kind, prec, body } => {
            if kind.is_anonymous() || *prec > MAX_PREC {
                return Err("unsupported artifact nested-node precedence or kind");
            }
            descriptor(body, categories, remaining, depth + 1)
        }
        Descr::Cat(category, precedence) => {
            let builtin = simple(category);
            if *precedence > MAX_PREC
                || !(matches!(builtin.as_deref(), Some("term" | "tactic"))
                    || categories.contains(category))
            {
                return Err("artifact parser references an unavailable category or precedence");
            }
            if builtin.as_deref() == Some("term") && !matches!(*precedence, 0 | 1023 | 1024) {
                return Err("artifact term operands require zero, argument or maximum precedence");
            }
            Ok(false)
        }
        Descr::SepBy {
            item,
            separator,
            parser,
            at_least_one,
            ..
        } => {
            check_token(separator.trim())?;
            let item = descriptor(item, categories, remaining, depth + 1)?;
            let separator = descriptor(parser, categories, remaining, depth + 1)?;
            if item || separator {
                return Err("artifact separator parser contains a nullable production");
            }
            Ok(!at_least_one)
        }
        Descr::Parser(_) => {
            Err("artifact parser dependencies must be resolved from checked descriptions")
        }
        Descr::NodeWithAntiquot(..) => Err("artifact node-with-antiquotation descriptions"),
        Descr::TrailingNode { .. } => Err("nested artifact trailing-node description"),
    }
}

#[cfg(test)]
mod tests;
