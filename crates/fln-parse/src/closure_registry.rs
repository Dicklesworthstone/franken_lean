//! Per-closure syntax registry built from the extracted builtin set (`fln-vokf`)
//! plus decoded imported `.olean` parser-extension entries (`fln-notation-from-imports-0edr`).
//!
//! Unlike [`crate::extensions::FileGrammar::new`], this registry reads **only** the
//! pin-extracted builtin baseline (builtin tokens, builtin categories, builtin parser
//! registrations and precedences) from `contracts/REFERENCE_GRAMMAR_CENSUS.txt`; every
//! imported token, node kind, category, and `ParserDescr` comes strictly from the caller's
//! decoded [`ImportedSyntaxModule`] in canonical replay order.

use crate::extensions::{Descr, IdentBehavior, ImportedSyntaxEntry, ImportedSyntaxModule};
use crate::reference_tokens::{GRAMMAR_CENSUS, reference_census};
use fln_core::name::Name;
use fln_hash::domain::{Digest, Domain, hash};
use fln_syntax::token::TokenTable;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

const REGISTRY_DIGEST_SCHEMA: &[u8] = b"fln.closure-syntax-registry/1";

/// Where a registered parser production came from.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ParserOrigin {
    /// Compiled into the pinned Reference binary (`@[builtin_*_parser]`).
    Builtin,
    /// Decoded from an imported `.olean` module's `Lean.Parser.parserExtension` journal.
    Imported { module: Name },
}

/// One parser registration in a category table, carrying its exact dispatch metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegistryParserEntry {
    pub origin: ParserOrigin,
    pub category: Name,
    pub decl: Name,
    pub leading: bool,
    pub priority: u32,
    pub precedence: Option<u32>,
    pub lhs_precedence: Option<u32>,
    /// `None` for global registrations, `Some(ns)` for `scoped` entries dormant until `ns` opens.
    pub scope: Option<Name>,
    /// Decoded `ParserDescr` for imported entries (`None` for compiled builtins).
    pub descr: Option<Descr>,
}

/// Extracted builtin baseline (tokens, categories, and builtin parser rows from `fln-vokf`).
#[derive(Debug, Clone, PartialEq, Eq)]
struct BuiltinBaseline {
    tokens: BTreeSet<String>,
    categories: BTreeMap<Name, IdentBehavior>,
    parsers_by_category: BTreeMap<Name, Vec<RegistryParserEntry>>,
    builtin_parser_count: usize,
}

fn parse_name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn parse_opt_u32(field: &str, prefix: &str) -> Option<u32> {
    let raw = field.strip_prefix(prefix)?;
    if raw == "-" {
        None
    } else {
        raw.parse::<u32>().ok()
    }
}

fn builtin_baseline() -> &'static BuiltinBaseline {
    static BASELINE: OnceLock<BuiltinBaseline> = OnceLock::new();
    BASELINE.get_or_init(|| {
        let tokens: BTreeSet<String> = reference_census()
            .builtin_tokens()
            .map(str::to_owned)
            .collect();
        let mut categories = BTreeMap::new();
        let mut parsers_by_category: BTreeMap<Name, Vec<RegistryParserEntry>> = BTreeMap::new();
        let mut builtin_parser_count = 0usize;

        for raw in GRAMMAR_CENSUS.lines() {
            if raw.is_empty() || raw.starts_with('#') {
                continue;
            }
            let fields: Vec<&str> = raw.split('\t').collect();
            match fields.first().copied() {
                Some("category") if fields.len() >= 5 => {
                    let cat = parse_name(fields[1]);
                    let behavior = match fields[3] {
                        "symbol" => IdentBehavior::Symbol,
                        "both" => IdentBehavior::Both,
                        _ => IdentBehavior::Default,
                    };
                    categories.insert(cat, behavior);
                }
                Some("builtin-parser") if fields.len() >= 8 => {
                    let category = parse_name(fields[1]);
                    let decl = parse_name(fields[2]);
                    let leading = fields[3] == "leading";
                    let priority = parse_opt_u32(fields[4], "prio=").unwrap_or(1000);
                    let precedence = parse_opt_u32(fields[5], "prec=");
                    let lhs_precedence = parse_opt_u32(fields[6], "lhs-prec=");
                    parsers_by_category
                        .entry(category.clone())
                        .or_default()
                        .push(RegistryParserEntry {
                            origin: ParserOrigin::Builtin,
                            category,
                            decl,
                            leading,
                            priority,
                            precedence,
                            lhs_precedence,
                            scope: None,
                            descr: None,
                        });
                    builtin_parser_count += 1;
                }
                _ => {}
            }
        }

        // Canonical sort for the builtin half: leading before trailing, then decl name,
        // priority, and precedence.
        for entries in parsers_by_category.values_mut() {
            entries.sort_by(|a, b| {
                (
                    !a.leading,
                    &a.decl,
                    a.priority,
                    a.precedence,
                    a.lhs_precedence,
                )
                    .cmp(&(
                        !b.leading,
                        &b.decl,
                        b.priority,
                        b.precedence,
                        b.lhs_precedence,
                    ))
            });
        }

        BuiltinBaseline {
            tokens,
            categories,
            parsers_by_category,
            builtin_parser_count,
        }
    })
}

/// Per-closure syntax registry combining the pin-extracted builtin set with decoded `.olean`
/// parser-extension entries in canonical registration order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosureSyntaxRegistry {
    tokens: TokenTable,
    global_tokens: BTreeSet<String>,
    scoped_tokens: BTreeMap<Name, BTreeSet<String>>,
    global_kinds: BTreeSet<Name>,
    scoped_kinds: BTreeMap<Name, BTreeSet<Name>>,
    categories: BTreeMap<Name, IdentBehavior>,
    parsers_by_category: BTreeMap<Name, Vec<RegistryParserEntry>>,
    builtin_parser_count: usize,
    imported_parser_count: usize,
    digest: Digest,
}

impl ClosureSyntaxRegistry {
    /// Build a per-closure syntax registry from the extracted builtin baseline plus the
    /// decoded `.olean` entries in `imported`, preserving canonical replay order and computing
    /// a deterministic BLAKE3 digest over the full canonical state.
    pub fn from_imported(imported: &ImportedSyntaxModule) -> Self {
        let base = builtin_baseline();
        let mut global_tokens = base.tokens.clone();
        let mut scoped_tokens: BTreeMap<Name, BTreeSet<String>> = BTreeMap::new();
        let mut global_kinds = BTreeSet::new();
        let mut scoped_kinds: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
        let mut categories = base.categories.clone();
        let mut parsers_by_category = base.parsers_by_category.clone();
        let mut imported_parser_count = 0usize;

        for entry in &imported.entries {
            match entry {
                ImportedSyntaxEntry::Token { scope, token } => match scope {
                    None => {
                        global_tokens.insert(token.clone());
                    }
                    Some(namespace) => {
                        scoped_tokens
                            .entry(namespace.clone())
                            .or_default()
                            .insert(token.clone());
                    }
                },
                ImportedSyntaxEntry::Kind { scope, kind } => match scope {
                    None => {
                        global_kinds.insert(kind.clone());
                    }
                    Some(namespace) => {
                        scoped_kinds
                            .entry(namespace.clone())
                            .or_default()
                            .insert(kind.clone());
                    }
                },
                ImportedSyntaxEntry::Category {
                    category, behavior, ..
                } => {
                    categories.entry(category.clone()).or_insert(*behavior);
                }
                ImportedSyntaxEntry::Parser(decl) => {
                    let Some(category) = decl.category.clone() else {
                        continue;
                    };
                    let (precedence, lhs_precedence) = descr_precedences(&decl.descr);
                    parsers_by_category
                        .entry(category.clone())
                        .or_default()
                        .push(RegistryParserEntry {
                            origin: ParserOrigin::Imported {
                                module: decl.module.clone(),
                            },
                            category,
                            decl: decl.decl.clone(),
                            leading: decl.leading,
                            priority: decl.priority,
                            precedence,
                            lhs_precedence,
                            scope: decl.scope.clone(),
                            descr: Some(decl.descr.clone()),
                        });
                    imported_parser_count += 1;
                }
            }
        }

        let tokens = TokenTable::from_tokens(global_tokens.iter());
        let digest = compute_digest(
            &global_tokens,
            &scoped_tokens,
            &global_kinds,
            &scoped_kinds,
            &categories,
            &parsers_by_category,
        );

        Self {
            tokens,
            global_tokens,
            scoped_tokens,
            global_kinds,
            scoped_kinds,
            categories,
            parsers_by_category,
            builtin_parser_count: base.builtin_parser_count,
            imported_parser_count,
            digest,
        }
    }

    pub fn tokens(&self) -> &TokenTable {
        &self.tokens
    }

    pub fn global_tokens(&self) -> &BTreeSet<String> {
        &self.global_tokens
    }

    pub fn scoped_tokens(&self, namespace: &Name) -> Option<&BTreeSet<String>> {
        self.scoped_tokens.get(namespace)
    }

    pub fn has_token(&self, token: &str) -> bool {
        self.global_tokens.contains(token)
    }

    pub fn global_kinds(&self) -> &BTreeSet<Name> {
        &self.global_kinds
    }

    pub fn scoped_kinds(&self, namespace: &Name) -> Option<&BTreeSet<Name>> {
        self.scoped_kinds.get(namespace)
    }

    pub fn categories(&self) -> &BTreeMap<Name, IdentBehavior> {
        &self.categories
    }

    pub fn parsers_in_category(&self, category: &Name) -> &[RegistryParserEntry] {
        self.parsers_by_category
            .get(category)
            .map_or(&[], Vec::as_slice)
    }

    pub fn find_parser(&self, category: &Name, decl: &Name) -> Option<&RegistryParserEntry> {
        self.parsers_in_category(category)
            .iter()
            .find(|entry| entry.decl == *decl)
    }

    pub fn has_global_parser(&self, category: &Name, decl: &Name) -> bool {
        self.parsers_in_category(category)
            .iter()
            .any(|entry| entry.scope.is_none() && entry.decl == *decl)
    }

    /// Whether any active global imported parser in `category` mentions `symbol` directly in
    /// its decoded `ParserDescr` (for example `"+"` in `term`).
    pub fn has_global_symbol_in_category(&self, category: &Name, symbol: &str) -> bool {
        self.parsers_in_category(category).iter().any(|entry| {
            entry.scope.is_none()
                && entry
                    .descr
                    .as_ref()
                    .is_some_and(|descr| descr_contains_symbol(descr, symbol))
        })
    }

    pub fn builtin_parser_count(&self) -> usize {
        self.builtin_parser_count
    }

    pub fn imported_parser_count(&self) -> usize {
        self.imported_parser_count
    }

    /// Deterministic BLAKE3 digest over every token, kind, category, and parser row in canonical
    /// order.
    pub fn digest(&self) -> Digest {
        self.digest
    }
}

fn descr_precedences(descr: &Descr) -> (Option<u32>, Option<u32>) {
    match descr {
        Descr::Node { prec, .. } => (Some(*prec), None),
        Descr::TrailingNode { prec, lhs_prec, .. } => (Some(*prec), Some(*lhs_prec)),
        _ => (None, None),
    }
}

fn descr_contains_symbol(descr: &Descr, target: &str) -> bool {
    let mut stack = vec![descr];
    while let Some(node) = stack.pop() {
        match node {
            Descr::Symbol(s) | Descr::NonReservedSymbol(s, _) if s.trim() == target => {
                return true;
            }
            Descr::UnicodeSymbol(u, a, _) if u.trim() == target || a.trim() == target => {
                return true;
            }
            Descr::Unary(_, body)
            | Descr::Node { body, .. }
            | Descr::TrailingNode { body, .. }
            | Descr::NodeWithAntiquot(_, _, body) => stack.push(body),
            Descr::Binary(_, left, right) => {
                stack.push(right);
                stack.push(left);
            }
            Descr::SepBy {
                item,
                separator,
                parser,
                ..
            } => {
                if separator.trim() == target {
                    return true;
                }
                stack.push(parser);
                stack.push(item);
            }
            _ => {}
        }
    }
    false
}

fn push_len_bytes(buf: &mut Vec<u8>, bytes: &[u8]) {
    buf.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    buf.extend_from_slice(bytes);
}

fn push_opt_u32(buf: &mut Vec<u8>, value: Option<u32>) {
    match value {
        None => buf.push(0),
        Some(v) => {
            buf.push(1);
            buf.extend_from_slice(&v.to_le_bytes());
        }
    }
}

fn compute_digest(
    global_tokens: &BTreeSet<String>,
    scoped_tokens: &BTreeMap<Name, BTreeSet<String>>,
    global_kinds: &BTreeSet<Name>,
    scoped_kinds: &BTreeMap<Name, BTreeSet<Name>>,
    categories: &BTreeMap<Name, IdentBehavior>,
    parsers_by_category: &BTreeMap<Name, Vec<RegistryParserEntry>>,
) -> Digest {
    let mut buf = Vec::with_capacity(4096);
    push_len_bytes(&mut buf, REGISTRY_DIGEST_SCHEMA);

    buf.extend_from_slice(&(global_tokens.len() as u64).to_le_bytes());
    for token in global_tokens {
        push_len_bytes(&mut buf, token.as_bytes());
    }

    buf.extend_from_slice(&(scoped_tokens.len() as u64).to_le_bytes());
    for (ns, tokens) in scoped_tokens {
        push_len_bytes(&mut buf, ns.to_display_string().as_bytes());
        buf.extend_from_slice(&(tokens.len() as u64).to_le_bytes());
        for token in tokens {
            push_len_bytes(&mut buf, token.as_bytes());
        }
    }

    buf.extend_from_slice(&(global_kinds.len() as u64).to_le_bytes());
    for kind in global_kinds {
        push_len_bytes(&mut buf, kind.to_display_string().as_bytes());
    }

    buf.extend_from_slice(&(scoped_kinds.len() as u64).to_le_bytes());
    for (ns, kinds) in scoped_kinds {
        push_len_bytes(&mut buf, ns.to_display_string().as_bytes());
        buf.extend_from_slice(&(kinds.len() as u64).to_le_bytes());
        for kind in kinds {
            push_len_bytes(&mut buf, kind.to_display_string().as_bytes());
        }
    }

    buf.extend_from_slice(&(categories.len() as u64).to_le_bytes());
    for (cat, behavior) in categories {
        push_len_bytes(&mut buf, cat.to_display_string().as_bytes());
        buf.push(match behavior {
            IdentBehavior::Default => 0,
            IdentBehavior::Symbol => 1,
            IdentBehavior::Both => 2,
        });
    }

    buf.extend_from_slice(&(parsers_by_category.len() as u64).to_le_bytes());
    for (cat, entries) in parsers_by_category {
        push_len_bytes(&mut buf, cat.to_display_string().as_bytes());
        buf.extend_from_slice(&(entries.len() as u64).to_le_bytes());
        for entry in entries {
            match &entry.origin {
                ParserOrigin::Builtin => buf.push(0),
                ParserOrigin::Imported { module } => {
                    buf.push(1);
                    push_len_bytes(&mut buf, module.to_display_string().as_bytes());
                }
            }
            push_len_bytes(&mut buf, entry.decl.to_display_string().as_bytes());
            buf.push(u8::from(entry.leading));
            buf.extend_from_slice(&entry.priority.to_le_bytes());
            push_opt_u32(&mut buf, entry.precedence);
            push_opt_u32(&mut buf, entry.lhs_precedence);
            match &entry.scope {
                None => buf.push(0),
                Some(ns) => {
                    buf.push(1);
                    push_len_bytes(&mut buf, ns.to_display_string().as_bytes());
                }
            }
            match &entry.descr {
                None => buf.push(0),
                Some(descr) => {
                    buf.push(1);
                    let rendered = descr.to_string();
                    push_len_bytes(&mut buf, rendered.as_bytes());
                }
            }
        }
    }

    hash(Domain::CacheKey, &buf)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extensions::SyntaxDecl;
    use std::sync::Arc;

    fn name(s: &str) -> Name {
        Name::from_components(s.split('.'))
    }

    #[test]
    fn empty_imported_closure_contains_only_extracted_builtins_and_anonymous_ctor() {
        let registry = ClosureSyntaxRegistry::from_imported(&ImportedSyntaxModule::default());
        assert_eq!(registry.imported_parser_count(), 0);
        assert!(
            registry.builtin_parser_count() >= 200,
            "extracted builtin set must be populated"
        );
        assert!(
            registry.has_token("⟨") && registry.has_token("⟩"),
            "anonymous-constructor tokens come from the builtin set"
        );
        assert!(
            !registry.has_token("="),
            "`=` is imported notation, not a builtin token"
        );
        assert!(
            !registry.has_global_symbol_in_category(&name("term"), "+"),
            "`+` term operator is absent without imported notation"
        );
        assert!(
            registry
                .find_parser(&name("term"), &name("Lean.Parser.Term.anonymousCtor"))
                .is_some_and(|entry| entry.origin == ParserOrigin::Builtin
                    && entry.leading
                    && entry.precedence == Some(1024)),
            "builtin anonymousCtor registration carries its extracted precedence"
        );
    }

    #[test]
    fn imported_entries_extend_tokens_categories_and_change_canonical_digest() {
        let base = ClosureSyntaxRegistry::from_imported(&ImportedSyntaxModule::default());
        let imported = ImportedSyntaxModule {
            entries: vec![
                ImportedSyntaxEntry::Token {
                    scope: None,
                    token: "⊕".to_owned(),
                },
                ImportedSyntaxEntry::Parser(Arc::new(SyntaxDecl {
                    module: name("User.Ops"),
                    decl: name("User.Ops.termPlus"),
                    category: Some(name("term")),
                    leading: false,
                    priority: 1000,
                    scope: None,
                    descr: Descr::TrailingNode {
                        kind: name("User.Ops.termPlus"),
                        prec: 65,
                        lhs_prec: 66,
                        body: Box::new(Descr::Symbol("⊕".to_owned())),
                    },
                })),
            ],
        };
        let extended = ClosureSyntaxRegistry::from_imported(&imported);
        assert!(extended.has_token("⊕"));
        assert!(extended.has_token("⟨"));
        assert!(extended.has_global_parser(&name("term"), &name("User.Ops.termPlus")));
        assert!(extended.has_global_symbol_in_category(&name("term"), "⊕"));
        assert_eq!(
            extended
                .find_parser(&name("term"), &name("User.Ops.termPlus"))
                .map(|e| (e.leading, e.precedence, e.lhs_precedence)),
            Some((false, Some(65), Some(66)))
        );
        assert_ne!(base.digest(), extended.digest());
        assert_eq!(
            extended.digest(),
            ClosureSyntaxRegistry::from_imported(&imported).digest()
        );
    }
}
