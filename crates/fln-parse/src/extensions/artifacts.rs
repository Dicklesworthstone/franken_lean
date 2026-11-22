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
    /// Only a validated explicit parser row registers a category quoter.
    /// The key is its declaration, so ordinary scoped-parser activation also
    /// controls whether this native quotation route is available.
    pub(super) quotations: BTreeMap<Name, Name>,
    pub(super) owners: BTreeSet<Name>,
    pub(super) namespaces: BTreeSet<Name>,
    work: usize,
}

impl ArtifactGrammar {
    pub(super) fn scoped_command_heads(&self) -> BTreeSet<String> {
        let command = Name::from_components(["command"]);
        self.scoped
            .values()
            .flatten()
            .filter(|declaration| {
                declaration.leading && declaration.category.as_ref() == Some(&command)
            })
            .flat_map(|declaration| heads(&declaration.descr, 0))
            .collect()
    }

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

/// Parser routes whose competing declarations can share one head.
#[derive(Clone, Copy)]
enum ParserDispatch<'a> {
    Description {
        precedence: u32,
        body: &'a Descr,
    },
    Prefix {
        precedence: u32,
        operand: u32,
    },
    Category {
        precedence: u32,
        lhs_precedence: Option<u32>,
        body: &'a Descr,
    },
}

/// The scalar prefix stack reads one common operand. General leading terms
/// instead run their descriptions independently. Mixing those routes would
/// let the prefix stack hide a longer description.
fn parser_dispatch(declaration: &SyntaxDecl) -> Option<ParserDispatch<'_>> {
    let category = declaration.category.as_ref()?;
    if !builtin_category(category) {
        return match (&declaration.descr, declaration.leading) {
            (Descr::Node { prec, body, .. }, true) => Some(ParserDispatch::Category {
                precedence: *prec,
                lhs_precedence: None,
                body,
            }),
            (
                Descr::TrailingNode {
                    prec,
                    lhs_prec,
                    body,
                    ..
                },
                false,
            ) => Some(ParserDispatch::Category {
                precedence: *prec,
                lhs_precedence: Some(*lhs_prec),
                body,
            }),
            _ => None,
        };
    }
    if !declaration.leading || *category != Name::from_components(["term"]) {
        return None;
    }
    let Descr::Node { kind, prec, body } = &declaration.descr else {
        return None;
    };
    // Category quotations have a separate reader.
    if *kind == Name::from_components(["Lean", "Parser", "Term", "quot"]) {
        return None;
    }
    if let Descr::Binary(alias, left, right) = body.as_ref()
        && simple(alias).as_deref() == Some("andthen")
        && matches!(left.as_ref(), Descr::Symbol(_))
        && let Descr::Cat(category, minimum) = right.as_ref()
        && simple(category).as_deref() == Some("term")
        && *minimum < 256
    {
        return Some(ParserDispatch::Prefix {
            precedence: *prec,
            operand: *minimum,
        });
    }
    (*prec >= LEAD_PREC && (ends_with_atom(body, 0) || ends_with_term(body, 0))).then_some(
        ParserDispatch::Description {
            precedence: *prec,
            body,
        },
    )
}

/// Account for structural equality and prefix inspection before comparing
/// descriptors. Shared-head admission uses the same bounded work allowance
/// as descriptor validation, including candidates inherited from earlier imports.
fn charge_comparison(descr: &Descr, remaining: &mut usize) -> Result<(), &'static str> {
    let mut pending = vec![(descr, 0)];
    while let Some((descr, depth)) = pending.pop() {
        if depth > MAX_DESCR_DEPTH {
            return Err("artifact parser description depth past the budget");
        }
        charge(remaining)?;
        match descr {
            Descr::Unary(_, body)
            | Descr::Node { body, .. }
            | Descr::TrailingNode { body, .. }
            | Descr::NodeWithAntiquot(_, _, body) => pending.push((body, depth + 1)),
            Descr::Binary(_, left, right) => {
                pending.push((right, depth + 1));
                pending.push((left, depth + 1));
            }
            Descr::SepBy { item, parser, .. } => {
                pending.push((parser, depth + 1));
                pending.push((item, depth + 1));
            }
            _ => {}
        }
    }
    Ok(())
}

/// Collect only mandatory initial literals. The result says whether the
/// entire description was literal: a delimiter after a term is not an initial
/// discriminator. Optional, alternative and antiquotation readers stop this walk.
fn literal_prefix<'a>(descr: &'a Descr, prefix: &mut Vec<Vec<&'a str>>) -> bool {
    match descr {
        Descr::Symbol(token) => {
            prefix.push(vec![token.trim()]);
            true
        }
        Descr::UnicodeSymbol(token, ascii, _) => {
            prefix.push(vec![token.trim(), ascii.trim()]);
            true
        }
        Descr::Node { body, .. } => literal_prefix(body, prefix),
        Descr::Binary(alias, left, right) if simple(alias).as_deref() == Some("andthen") => {
            literal_prefix(left, prefix) && literal_prefix(right, prefix)
        }
        _ => false,
    }
}

fn compatible_dispatch(
    left: ParserDispatch<'_>,
    right: ParserDispatch<'_>,
    remaining: &mut usize,
) -> Result<bool, &'static str> {
    charge(remaining)?;
    match (left, right) {
        (
            ParserDispatch::Prefix {
                precedence: left,
                operand: left_operand,
            },
            ParserDispatch::Prefix {
                precedence: right,
                operand: right_operand,
            },
        ) => Ok(left == right && left_operand == right_operand),
        (
            ParserDispatch::Description {
                precedence: left_precedence,
                body: left,
            },
            ParserDispatch::Description {
                precedence: right_precedence,
                body: right,
            },
        ) if left_precedence == right_precedence => {
            charge_comparison(left, remaining)?;
            charge_comparison(right, remaining)?;
            if left == right {
                return Ok(true);
            }
            let mut left_prefix = Vec::new();
            let mut right_prefix = Vec::new();
            literal_prefix(left, &mut left_prefix);
            literal_prefix(right, &mut right_prefix);
            // A successful candidate consumes the distinguishing token, so a
            // sibling's mismatch there cannot outrank it by error progress.
            // Prefix-related descriptions do not have this guarantee.
            Ok(left_prefix
                .iter()
                .zip(&right_prefix)
                .any(|(left, right)| left.iter().all(|token| !right.contains(token))))
        }
        (
            ParserDispatch::Category {
                precedence: left_precedence,
                lhs_precedence: left_lhs,
                body: left,
            },
            ParserDispatch::Category {
                precedence: right_precedence,
                lhs_precedence: right_lhs,
                body: right,
            },
        ) if left_precedence == right_precedence && left_lhs == right_lhs => {
            // Identical bodies agree on both successful and failed progress.
            // Root kinds may differ: the category Pratt parser preserves their
            // equally successful readings as a choice for the macro consumer.
            charge_comparison(left, remaining)?;
            charge_comparison(right, remaining)?;
            Ok(left == right)
        }
        _ => Ok(false),
    }
}

type HeadDispatches<'a> = BTreeMap<String, Vec<Option<ParserDispatch<'a>>>>;

/// A primitive production without a first-token set cannot coexist with
/// another leading production: their possible overlap is not established.
#[derive(Default)]
struct Heads<'a> {
    tokens: BTreeMap<(Name, bool), HeadDispatches<'a>>,
    primitive: BTreeSet<(Name, bool)>,
}

impl<'a> Heads<'a> {
    fn existing(&mut self, declaration: &'a SyntaxDecl) {
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
            let dispatch = parser_dispatch(declaration);
            let occupied = self.tokens.entry(key).or_default();
            for token in tokens {
                occupied.entry(token).or_default().push(dispatch);
            }
        }
    }

    fn add(
        &mut self,
        declaration: &'a SyntaxDecl,
        tokens: Vec<String>,
        remaining: &mut usize,
    ) -> Result<(), &'static str> {
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
            let dispatch = parser_dispatch(declaration);
            for token in &tokens {
                if let Some(previous) = occupied.get(token) {
                    for previous in previous {
                        let (Some(previous), Some(dispatch)) = (*previous, dispatch) else {
                            return Err("overlapping artifact parser productions");
                        };
                        if !compatible_dispatch(previous, dispatch, remaining)? {
                            return Err("overlapping artifact parser productions");
                        }
                    }
                }
            }
            for token in tokens {
                occupied.entry(token).or_default().push(dispatch);
            }
        }
        Ok(())
    }
}

impl FileGrammar {
    /// Install a complete checked artifact's ordered parser product at the
    /// beginning of a file. A refusal leaves the grammar and its caches intact.
    ///
    /// The supported subset is data-only descriptions with native aliases,
    /// reserved first tokens, leading `term` syntax with an atom or term
    /// endpoint, simple Pratt prefixes, ordinary symbol/term infix syntax, and
    /// leading/trailing custom-category syntax.
    /// A lone primitive production (such as `num`) is supported in a custom
    /// category. Term operands admit every minimum through `max`; intermediate
    /// minima use the scalar Pratt parser's application and operator boundaries.
    /// Leading terms with equal precedence may share identical bodies or
    /// disjoint mandatory literal prefixes. Simple prefixes must share both
    /// binding powers. Priority and tied readings follow native dispatch.
    /// Custom-category productions may share identical bodies and binding
    /// powers; their distinct root kinds remain available to macro consumers.
    /// Unknown closures/aliases, scoped categories, unproved shared heads,
    /// contextual column checks and unsupported precedence forms are refused.
    /// The exact category quotation shape emitted by `declare_syntax_cat` uses
    /// the native quotation parser, with its original envelope and captures.
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
        let mut quotations = BTreeMap::new();
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
                    let (first, quotation) =
                        registration(declaration, &categories, &mut remaining)?;
                    occupied.add(declaration, first, &mut remaining)?;
                    if let Some(category) = quotation {
                        if self
                            .native_categories
                            .iter()
                            .any(|native| native.leaf_view() == category.leaf_view())
                        {
                            return Err(
                                "artifact quotation overlaps a native source category quoter",
                            );
                        }
                        quotations.insert(declaration.decl.clone(), category);
                    }
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
                    if let Some(category) = quotations.remove(&declaration.decl) {
                        self.artifact
                            .quotations
                            .insert(declaration.decl.clone(), category);
                    }
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
) -> Result<(Vec<String>, Option<Name>), &'static str> {
    let category = declaration
        .category
        .as_ref()
        .ok_or("artifact parser registration without a category")?;
    if !builtin_category(category) && !categories.contains(category) {
        return Err("artifact parser names an unavailable category");
    }
    charge(remaining)?;
    let term = simple(category).as_deref() == Some("term");
    let tactic = simple(category).as_deref() == Some("tactic");
    let custom = !builtin_category(category);
    if matches!(&declaration.descr, Descr::Node { kind, .. }
        if *kind == Name::from_components(["Lean", "Parser", "Term", "quot"]))
    {
        let (opener, category) = category_quotation(declaration, categories)?;
        let Descr::Node { body, .. } = &declaration.descr else {
            unreachable!("category quotation root checked above")
        };
        descriptor(body, categories, remaining, 1)?;
        return Ok((vec![opener], Some(category)));
    }
    let (body, first) = match (&declaration.descr, declaration.leading) {
        (Descr::Node { kind, prec, body }, true) => {
            if kind.is_anonymous() || *prec > MAX_PREC {
                return Err("unsupported artifact leading-node precedence or kind");
            }
            check_root_kind(kind)?;
            if term && !leading_term_supported(*prec, body) {
                return Err("artifact term parser is not a supported leading production");
            }
            let first = heads(body, 0);
            if term && first.iter().any(|token| token.starts_with("`(")) {
                return Err(
                    "artifact category quotation parsers require their own supported registration",
                );
            }
            if first.is_empty() && !(custom && primitive(body, 0)) {
                return Err("artifact leading parser has no supported first token");
            }
            if !first.is_empty() && !dispatchable_heads(body, 0, tactic) {
                return Err("artifact leading parser has unsupported first-token behavior");
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
                return Ok((first, None));
            }
            if !custom {
                return Err("artifact trailing parser for an unsupported builtin category");
            }
            let first = heads(body, 0);
            if first.is_empty() || !dispatchable_heads(body, 0, false) {
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
    Ok((first, None))
}

/// Match the two executable leading-term routes in `ActiveGrammar::new`.
/// General descriptions at `lead` or above use `Run`, whose final term obeys
/// its own minimum precedence and the enclosing delimiter. Lower-precedence
/// nodes must have the exact simple-prefix shape handled by the Pratt stack;
/// a compound parser at that precedence would otherwise install no dispatch.
fn leading_term_supported(precedence: u32, body: &Descr) -> bool {
    if precedence >= LEAD_PREC && (ends_with_atom(body, 0) || ends_with_term(body, 0)) {
        return true;
    }
    matches!(body, Descr::Binary(alias, left, right)
        if simple(alias).as_deref() == Some("andthen")
            && matches!(left.as_ref(), Descr::Symbol(_))
            && matches!(right.as_ref(), Descr::Cat(category, minimum)
                if simple(category).as_deref() == Some("term") && *minimum < 256))
}

/// `Lean.Elab.Command.declareSyntaxCatQuotParser` in the pinned Syntax.lean
/// emits one `term` parser with this exact node/sequence/category structure.
/// Its opening symbol includes a trailing pretty-printing space; token
/// matching trims that space just as ordinary ParserDescr.symbol does.
///
/// The native quotation reader builds precisely this envelope, including the
/// inner category kind and its pseudo-antiquotations. No other reuse of
/// `Term.quot`, category, delimiter, precedence or sequence is equivalent.
fn category_quotation(
    declaration: &SyntaxDecl,
    categories: &BTreeSet<Name>,
) -> Result<(String, Name), &'static str> {
    let malformed = "artifact category quotation does not match its generated parser shape";
    if !declaration.leading
        || declaration.category.as_ref() != Some(&Name::from_components(["term"]))
    {
        return Err(malformed);
    }
    let Descr::Node {
        prec: MAX_PREC,
        body,
        ..
    } = &declaration.descr
    else {
        return Err(malformed);
    };
    let Descr::Node {
        kind,
        prec: MAX_PREC,
        body,
    } = body.as_ref()
    else {
        return Err(malformed);
    };
    let Descr::Binary(first, open, rest) = body.as_ref() else {
        return Err(malformed);
    };
    let Descr::Binary(second, category, close) = rest.as_ref() else {
        return Err(malformed);
    };
    let (Descr::Symbol(open), Descr::Cat(category, 0), Descr::Symbol(close)) =
        (open.as_ref(), category.as_ref(), close.as_ref())
    else {
        return Err(malformed);
    };
    if simple(first).as_deref() != Some("andthen")
        || simple(second).as_deref() != Some("andthen")
        || builtin_category(category)
        || !categories.contains(category)
        || *kind != Name::str(category.clone(), "quot")
        || close.trim() != ")"
    {
        return Err(malformed);
    }
    let LeafView::Str(suffix) = category.leaf_view() else {
        return Err(malformed);
    };
    let opener = format!("`({suffix}|");
    if open.trim() != opener || builtin_tokens().contains(opener.as_str()) {
        return Err(malformed);
    }
    Ok((opener, category.clone()))
}

fn primitive(descr: &Descr, depth: usize) -> bool {
    if depth > MAX_DESCR_DEPTH {
        return false;
    }
    match descr {
        Descr::Const(name) => matches!(
            simple(name).as_deref(),
            Some("ident" | "num" | "str" | "char" | "scientific" | "name" | "hole")
        ),
        Descr::Node { body, .. } | Descr::NodeWithAntiquot(_, _, body) => {
            primitive(body, depth + 1)
        }
        _ => false,
    }
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

// The builtin tactic category uses LeadingIdentBehavior.symbol: ordinary
// `syntax "head" : tactic` therefore emits nonReservedSymbol head false.
// Its exact spelling is already a key in the native tactic dispatch table,
// without globally reserving that identifier. Other category behaviors and
// includeIdent=true still need different lookup semantics and remain refused.
fn dispatchable_heads(descr: &Descr, depth: usize, tactic: bool) -> bool {
    if depth > MAX_DESCR_DEPTH {
        return false;
    }
    match descr {
        Descr::Symbol(_) | Descr::UnicodeSymbol(..) => true,
        Descr::NonReservedSymbol(_, false) => tactic,
        Descr::Node { body, .. } | Descr::NodeWithAntiquot(_, _, body) => {
            dispatchable_heads(body, depth + 1, tactic)
        }
        Descr::Unary(name, body) if input_wrapper(name) => {
            dispatchable_heads(body, depth + 1, tactic)
        }
        Descr::Binary(name, left, right) => match simple(name).as_deref() {
            Some("andthen") => dispatchable_heads(left, depth + 1, tactic),
            Some("orelse") => {
                dispatchable_heads(left, depth + 1, tactic)
                    && dispatchable_heads(right, depth + 1, tactic)
            }
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
        Descr::NodeWithAntiquot(label, kind, body) => {
            check_token(label.trim())?;
            if kind.is_anonymous() {
                return Err("anonymous artifact node-with-antiquotation kind");
            }
            descriptor(body, categories, remaining, depth + 1)
        }
        Descr::Cat(category, precedence) => {
            let builtin = simple(category);
            if *precedence > MAX_PREC
                || !(matches!(builtin.as_deref(), Some("term" | "tactic" | "command"))
                    || categories.contains(category))
            {
                return Err("artifact parser references an unavailable category or precedence");
            }
            if builtin.as_deref() == Some("command") && *precedence != 0 {
                return Err("artifact command operands require zero precedence");
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
        Descr::TrailingNode { .. } => Err("nested artifact trailing-node description"),
    }
}

#[cfg(test)]
mod tests;
