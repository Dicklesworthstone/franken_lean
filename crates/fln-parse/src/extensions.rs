//! The pin's syntax extensions in the production parser (bead `franken_lean-z8j.1.10`, stages 3
//! and 4 of its plan, imported syntax extensions and source-level syntax commands; measured by
//! frontier A of `fln-pin-syntax-corpus-7b5b`).
//!
//! ## What is interpreted
//!
//! Every `syntax`, `notation`, `infix` and `macro` declaration compiles to a `ParserDescr`
//! constant, which the pin turns into a parser with `compileParserDescr`
//! (`Lean/Parser/Extension.lean`). Two sources supply them here:
//!
//! - **Imported modules.** `scripts/extract/gen_grammar_census.lean` evaluates the description
//!   of every declaration an Init or Std module makes and prints it (census rows `syntax-descr`,
//!   beside the `syntax-decl` row giving its category, priority and scope).
//! - **The file being parsed.** [`FileGrammar::declare`] translates a `syntax`, `notation` or
//!   mixfix command's tree into its description as the pin's elaborator does (`elabSyntax`,
//!   `toParserDescr` and `mkNameFromParserSyntax` in `Lean/Elab/Syntax.lean`, `elabNotation` in
//!   `Lean/Elab/Notation.lean`, `expandMixfix` in `Lean/Elab/Mixfix.lean`). The census is that
//!   translation's oracle: for an Init or Std file, every declaration it registers must be the
//!   census row of the same module and name.
//!
//! The descriptions run inside the hand-written parser ([`tactic`], [`infix`]), so a notation is
//! available because it was declared, not because it was transcribed.
//!
//! ## Which extensions are active
//!
//! As at the pin (`Lean/ScopedEnvExtension.lean`, `Lean/Elab/Open.lean`,
//! `Lean/Elab/BuiltinCommand.lean`):
//! - a `global` entry is active in every file whose import closure contains its module, and in
//!   the declaring file after its declaration;
//! - a `scoped` entry for namespace `N` is active only where `N` is activated: by `namespace`
//!   (`namespace A.B` activates `A`, then `A.B`), by `open N`, `open scoped N` and
//!   `open N hiding …` (not `open N (x)`), and by `open N in` for one command. A `section` or
//!   `namespace` scope restores the activation at its `end`;
//! - a `local` entry is active to the end of the declaring section or namespace.
//!
//! `open X` resolves `X` as `resolveNamespace` does (`Lean/ResolveName.lean`): the innermost
//! prefix `P` of the current namespace with `P.X` a namespace, then each earlier simple `open N`
//! with `N.X` a namespace. "A namespace" is decided among the namespaces that carry scoped
//! syntax, because the census does not record every namespace of the environment: where a
//! namespace without scoped syntax would shadow one that has it, this activates the latter. The
//! error can only add notation, never lose any.
//!
//! ## What is not interpreted yet
//!
//! - Leading `term` syntax, trailing syntax that is not an infix operator, and every category
//!   but `term` and `tactic`: such a declaration is registered but not run.
//! - Combinators outside [`Run::parse`]'s cases: a declaration using one fails as a candidate,
//!   so the parser refuses where it refused before.
//! - `macro` and `declare_syntax_cat` commands, which the hand parser does not read, and a
//!   `syntax` naming a hand-written `Parser` declaration: [`FileGrammar::declare`] refuses them.
//! - Two active parsers succeeding on the same input, where the pin builds a `choice` node:
//!   this refuses.
//!
//! Production does not enter a grammar yet: [`with_grammar`] is how a caller that knows a
//! file's imports and scopes (the frontier harness) parses under them, and without it every
//! function here answers as the implicit-`Init` table does.

use crate::build::Leaves;
use crate::command_scope::ScopeCommand;
use crate::reference_tokens::{GRAMMAR_CENSUS, UnknownModule, production_table, reference_census};
use crate::{DefinitionGrammar, null_node};
use fln_core::name::{LeafView, Name};
use fln_core::options::DataValue;
use fln_syntax::literal::{LiteralKind, decode_string};
use fln_syntax::run::{Event, LexRun, lex_run_from};
use fln_syntax::source::{BytePos, ByteSpan, SourceText};
use fln_syntax::token::{LexedToken, TokenKind, TokenTable};
use fln_syntax::tree::Syntax;
use fln_syntax::view::SourceView;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;
use std::rc::Rc;
use std::sync::{Arc, OnceLock};

mod modules;
pub use modules::NativeSyntaxModule;

/// A `ParserDescr` (`Init/Prelude.lean`, `inductive ParserDescr`), one variant per constructor,
/// fields in declaration order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Descr {
    /// A parser alias with no argument (`ident`, `num`, `ppSpace`, `colGt`, …).
    Const(Name),
    /// A one-argument alias (`optional`, `many`, `group`, `atomic`, …).
    Unary(Name, Box<Descr>),
    /// A two-argument alias: `andthen` (juxtaposition) and `orelse` (`<|>`).
    Binary(Name, Box<Descr>, Box<Descr>),
    Node {
        kind: Name,
        prec: u32,
        body: Box<Descr>,
    },
    TrailingNode {
        kind: Name,
        prec: u32,
        lhs_prec: u32,
        body: Box<Descr>,
    },
    Symbol(String),
    NonReservedSymbol(String, bool),
    Cat(Name, u32),
    Parser(Name),
    NodeWithAntiquot(String, Name, Box<Descr>),
    SepBy {
        item: Box<Descr>,
        separator: String,
        parser: Box<Descr>,
        trailing: bool,
        at_least_one: bool,
    },
    UnicodeSymbol(String, String, bool),
}

/// Why a `syntax-descr` field is not a description.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DescrError(pub &'static str);

/// Descriptions nest no deeper than this; the census's deepest is far shallower.
const MAX_DESCR_DEPTH: usize = 64;

enum Atom<'a> {
    Open,
    Close,
    Word(&'a str),
    Text(String),
}

struct Reader<'a> {
    text: &'a str,
    at: usize,
}

impl<'a> Reader<'a> {
    fn skip_spaces(&mut self) {
        while self.text[self.at..].starts_with(' ') {
            self.at += 1;
        }
    }

    fn next(&mut self) -> Result<Atom<'a>, DescrError> {
        self.skip_spaces();
        let rest = &self.text[self.at..];
        let Some(first) = rest.chars().next() else {
            return Err(DescrError("the description ends early"));
        };
        match first {
            '(' => {
                self.at += 1;
                Ok(Atom::Open)
            }
            ')' => {
                self.at += 1;
                Ok(Atom::Close)
            }
            '"' => {
                let (text, used) = json_string(rest)?;
                self.at += used;
                Ok(Atom::Text(text))
            }
            _ => {
                let used = rest.find([' ', '(', ')']).unwrap_or(rest.len());
                self.at += used;
                Ok(Atom::Word(&rest[..used]))
            }
        }
    }

    fn text(&mut self) -> Result<String, DescrError> {
        match self.next()? {
            Atom::Text(text) => Ok(text),
            _ => Err(DescrError("expected a string")),
        }
    }

    fn name(&mut self) -> Result<Name, DescrError> {
        rendered_name(&self.text()?).ok_or(DescrError("expected a name"))
    }

    fn number(&mut self) -> Result<u32, DescrError> {
        match self.next()? {
            Atom::Word(word) => word.parse().map_err(|_| DescrError("expected a number")),
            _ => Err(DescrError("expected a number")),
        }
    }

    fn flag(&mut self) -> Result<bool, DescrError> {
        match self.next()? {
            Atom::Word("true") => Ok(true),
            Atom::Word("false") => Ok(false),
            _ => Err(DescrError("expected true or false")),
        }
    }

    fn close(&mut self) -> Result<(), DescrError> {
        match self.next()? {
            Atom::Close => Ok(()),
            _ => Err(DescrError("expected `)`")),
        }
    }

    fn descr(&mut self, depth: usize) -> Result<Descr, DescrError> {
        if depth > MAX_DESCR_DEPTH {
            return Err(DescrError("the description nests too deeply"));
        }
        if !matches!(self.next()?, Atom::Open) {
            return Err(DescrError("expected `(`"));
        }
        let Atom::Word(constructor) = self.next()? else {
            return Err(DescrError("expected a constructor"));
        };
        let descr = match constructor {
            "const" => Descr::Const(self.name()?),
            "unary" => Descr::Unary(self.name()?, Box::new(self.descr(depth + 1)?)),
            "binary" => {
                let name = self.name()?;
                let left = self.descr(depth + 1)?;
                Descr::Binary(name, Box::new(left), Box::new(self.descr(depth + 1)?))
            }
            "node" => Descr::Node {
                kind: self.name()?,
                prec: self.number()?,
                body: Box::new(self.descr(depth + 1)?),
            },
            "trailingNode" => Descr::TrailingNode {
                kind: self.name()?,
                prec: self.number()?,
                lhs_prec: self.number()?,
                body: Box::new(self.descr(depth + 1)?),
            },
            "symbol" => Descr::Symbol(self.text()?),
            "nonReservedSymbol" => Descr::NonReservedSymbol(self.text()?, self.flag()?),
            "cat" => Descr::Cat(self.name()?, self.number()?),
            "parser" => Descr::Parser(self.name()?),
            "nodeWithAntiquot" => {
                let label = self.text()?;
                let kind = self.name()?;
                Descr::NodeWithAntiquot(label, kind, Box::new(self.descr(depth + 1)?))
            }
            "sepBy" | "sepBy1" => {
                let item = self.descr(depth + 1)?;
                let separator = self.text()?;
                let parser = self.descr(depth + 1)?;
                Descr::SepBy {
                    item: Box::new(item),
                    separator,
                    parser: Box::new(parser),
                    trailing: self.flag()?,
                    at_least_one: constructor == "sepBy1",
                }
            }
            "unicodeSymbol" => Descr::UnicodeSymbol(self.text()?, self.text()?, self.flag()?),
            _ => return Err(DescrError("unknown constructor")),
        };
        self.close()?;
        Ok(descr)
    }
}

/// A JSON string at the start of `text`: its value and the bytes it used.
fn json_string(text: &str) -> Result<(String, usize), DescrError> {
    let mut out = String::new();
    let mut chars = text.char_indices().skip(1);
    while let Some((at, c)) = chars.next() {
        match c {
            '"' => return Ok((out, at + 1)),
            '\\' => match chars.next().map(|(_, c)| c) {
                Some('"') => out.push('"'),
                Some('\\') => out.push('\\'),
                Some('/') => out.push('/'),
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some('r') => out.push('\r'),
                Some('b') => out.push('\u{8}'),
                Some('f') => out.push('\u{c}'),
                Some('u') => {
                    let hex: String = (0..4)
                        .filter_map(|_| chars.next().map(|(_, c)| c))
                        .collect();
                    let code = u32::from_str_radix(&hex, 16)
                        .map_err(|_| DescrError("a \\u escape needs four hex digits"))?;
                    out.push(
                        char::from_u32(code).ok_or(DescrError("a \\u escape is a surrogate"))?,
                    );
                }
                _ => return Err(DescrError("an unknown string escape")),
            },
            c => out.push(c),
        }
    }
    Err(DescrError("an unterminated string"))
}

impl Descr {
    /// Parse one description as `gen_grammar_census.lean`'s `descrRepr` prints it.
    pub fn parse(text: &str) -> Result<Descr, DescrError> {
        let mut reader = Reader { text, at: 0 };
        let descr = reader.descr(0)?;
        reader.skip_spaces();
        if reader.at != text.len() {
            return Err(DescrError("text after the description"));
        }
        Ok(descr)
    }

    /// The tokens the compiled parser adds to the token table (`ParserInfo.collectTokens`):
    /// every symbol, both spellings of a unicode symbol, and never a non-reserved symbol.
    fn collect_tokens(&self, out: &mut BTreeSet<String>) {
        let mut pending = vec![self];
        while let Some(descr) = pending.pop() {
            match descr {
                Descr::Symbol(text) => {
                    out.insert(text.trim().to_string());
                }
                Descr::UnicodeSymbol(text, ascii, _) => {
                    out.insert(text.trim().to_string());
                    out.insert(ascii.trim().to_string());
                }
                Descr::Unary(_, body)
                | Descr::Node { body, .. }
                | Descr::TrailingNode { body, .. }
                | Descr::NodeWithAntiquot(_, _, body) => pending.push(body),
                Descr::Binary(_, left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                Descr::SepBy { item, parser, .. } => {
                    pending.push(item);
                    pending.push(parser);
                }
                Descr::Const(_)
                | Descr::NonReservedSymbol(..)
                | Descr::Cat(..)
                | Descr::Parser(_) => {}
            }
        }
    }
}

impl std::fmt::Display for Descr {
    /// The census's own spelling (`descrRepr` in `gen_grammar_census.lean`).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let quote = |text: &str| {
            let mut out = String::from("\"");
            for c in text.chars() {
                match c {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    '\n' => out.push_str("\\n"),
                    c => out.push(c),
                }
            }
            out.push('"');
            out
        };
        let name = |name: &Name| quote(&name.to_display_string());
        match self {
            Descr::Const(alias) => write!(f, "(const {})", name(alias)),
            Descr::Unary(alias, body) => write!(f, "(unary {} {body})", name(alias)),
            Descr::Binary(alias, left, right) => {
                write!(f, "(binary {} {left} {right})", name(alias))
            }
            Descr::Node { kind, prec, body } => write!(f, "(node {} {prec} {body})", name(kind)),
            Descr::TrailingNode {
                kind,
                prec,
                lhs_prec,
                body,
            } => write!(f, "(trailingNode {} {prec} {lhs_prec} {body})", name(kind)),
            Descr::Symbol(text) => write!(f, "(symbol {})", quote(text)),
            Descr::NonReservedSymbol(text, ident) => {
                write!(f, "(nonReservedSymbol {} {ident})", quote(text))
            }
            Descr::Cat(category, rbp) => write!(f, "(cat {} {rbp})", name(category)),
            Descr::Parser(decl) => write!(f, "(parser {})", name(decl)),
            Descr::NodeWithAntiquot(label, kind, body) => {
                write!(
                    f,
                    "(nodeWithAntiquot {} {} {body})",
                    quote(label),
                    name(kind)
                )
            }
            Descr::SepBy {
                item,
                separator,
                parser,
                trailing,
                at_least_one,
            } => write!(
                f,
                "({} {item} {} {parser} {trailing})",
                if *at_least_one { "sepBy1" } else { "sepBy" },
                quote(separator)
            ),
            Descr::UnicodeSymbol(text, ascii, preserve) => {
                write!(
                    f,
                    "(unicodeSymbol {} {} {preserve})",
                    quote(text),
                    quote(ascii)
                )
            }
        }
    }
}

/// A name as `Name.toString` prints it: components joined by `.`, a component that needs it
/// escaped in `«»`.
pub fn rendered_name(text: &str) -> Option<Name> {
    let mut name = Name::anonymous();
    let mut rest = text;
    loop {
        let component;
        let escaped_component = rest.starts_with('«');
        if let Some(escaped) = rest.strip_prefix('«') {
            let close = escaped.find('»')?;
            component = &escaped[..close];
            rest = &escaped[close + '»'.len_utf8()..];
        } else {
            let end = rest.find('.').unwrap_or(rest.len());
            component = &rest[..end];
            rest = &rest[end..];
        }
        if component.is_empty() {
            return None;
        }
        // `Name.toString` prints a numeric component as its digits, and escapes a string one
        // that reads as digits (`«0»`), so unescaped digits are a number.
        name = match component.parse::<u64>() {
            Ok(number) if !escaped_component && component.bytes().all(|b| b.is_ascii_digit()) => {
                Name::num(name, number)
            }
            _ => Name::str(name, component),
        };
        if rest.is_empty() {
            return Some(name);
        }
        rest = rest.strip_prefix('.')?;
    }
}

fn components(name: &Name) -> Vec<String> {
    let mut out = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        out.push(match cursor.leaf_view() {
            LeafView::Str(component) => component.to_string(),
            LeafView::Num(component) => component.to_string(),
            LeafView::Anonymous => break,
        });
        cursor = cursor.parent();
    }
    out.reverse();
    out
}

fn simple(name: &Name) -> Option<String> {
    match components(name).as_slice() {
        [only] => Some(only.clone()),
        _ => None,
    }
}

/// `LeadingIdentBehavior` (`Lean/Parser/Basic.lean`): whether a category reads an identifier that
/// spells one of its productions' first atoms as that production.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdentBehavior {
    Default,
    Symbol,
    Both,
}

/// One syntax declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxDecl {
    pub module: Name,
    pub decl: Name,
    /// `None` for a syntax abbreviation (`syntax x := …`), which is referenced, never run.
    pub category: Option<Name>,
    pub leading: bool,
    pub priority: u32,
    /// `None` for a `global` entry, the activating namespace for a `scoped` one.
    pub scope: Option<Name>,
    pub descr: Descr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct AliasInfo {
    arity: usize,
    /// `stackSz?`: the nodes the parser pushes, `None` for the sum of its arguments'.
    stack: Option<usize>,
    auto_group: bool,
}

/// The census rows this module reads: syntax declarations with their descriptions, the parser
/// aliases, and the categories.
#[derive(Debug, Clone)]
pub struct ExtensionCensus {
    decls: Vec<Arc<SyntaxDecl>>,
    aliases: BTreeMap<String, AliasInfo>,
    /// Builtin categories, and categories declared by a module (`None` for builtin).
    categories: BTreeMap<Name, (IdentBehavior, Option<Name>)>,
}

/// Why the census's syntax rows are unusable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionCensusError {
    pub line: usize,
    pub reason: String,
}

fn behavior(text: &str) -> Option<IdentBehavior> {
    match text {
        "default" => Some(IdentBehavior::Default),
        "symbol" => Some(IdentBehavior::Symbol),
        "both" => Some(IdentBehavior::Both),
        _ => None,
    }
}

type DeclaredRow = (usize, Name, Option<Name>, bool, u32, Option<Name>);

impl ExtensionCensus {
    pub fn parse(text: &str) -> Result<ExtensionCensus, ExtensionCensusError> {
        let mut declared: BTreeMap<Name, DeclaredRow> = BTreeMap::new();
        let mut descrs: BTreeMap<Name, (usize, Descr)> = BTreeMap::new();
        let mut aliases = BTreeMap::new();
        let mut categories = BTreeMap::new();
        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        for (index, row) in text.lines().enumerate() {
            let line = index + 1;
            let fail = |reason: &str| ExtensionCensusError {
                line,
                reason: reason.to_string(),
            };
            let fields: Vec<&str> = row.split('\t').collect();
            match fields.as_slice() {
                [
                    "count",
                    what @ ("init-std-syntax-descrs" | "parser-aliases"),
                    n,
                ] => {
                    counts.insert(what, n.parse().map_err(|_| fail("a count is a numeral"))?);
                }
                [
                    "syntax-decl",
                    module,
                    decl,
                    category,
                    position,
                    priority,
                    _,
                    _,
                    scope,
                    _,
                ] => {
                    if *position == "parser-attribute" {
                        continue;
                    }
                    let module = rendered_name(module).ok_or_else(|| fail("module name"))?;
                    let decl = rendered_name(decl).ok_or_else(|| fail("declaration name"))?;
                    let category = match *category {
                        "-" => None,
                        category => Some(rendered_name(category).ok_or_else(|| fail("category"))?),
                    };
                    let priority = match priority.strip_prefix("prio=") {
                        Some("-") => 0,
                        Some(n) => n.parse().map_err(|_| fail("a priority is a numeral"))?,
                        None => return Err(fail("a syntax-decl row gives prio=")),
                    };
                    let scope = match *scope {
                        "global" | "-" => None,
                        scope => Some(
                            scope
                                .strip_prefix("scoped:")
                                .and_then(rendered_name)
                                .ok_or_else(|| fail("a scope is global or scoped:<ns>"))?,
                        ),
                    };
                    let leading = *position != "trailing";
                    if declared
                        .insert(
                            decl.clone(),
                            (line, module, category, leading, priority, scope),
                        )
                        .is_some()
                    {
                        return Err(fail("a syntax declaration appears twice"));
                    }
                }
                ["syntax-descr", _, decl, descr] => {
                    let decl = rendered_name(decl).ok_or_else(|| fail("declaration name"))?;
                    let descr = Descr::parse(descr).map_err(|DescrError(reason)| fail(reason))?;
                    if descrs.insert(decl, (line, descr)).is_some() {
                        return Err(fail("a syntax description appears twice"));
                    }
                }
                ["parser-alias", name, arity, _, stack, group, _] => {
                    let arity = match *arity {
                        "const" => 0,
                        "unary" => 1,
                        "binary" => 2,
                        _ => return Err(fail("an alias arity is const, unary or binary")),
                    };
                    let stack = match stack.strip_prefix("stack=") {
                        Some("-") => None,
                        Some(n) => Some(n.parse().map_err(|_| fail("a stack size is a numeral"))?),
                        None => return Err(fail("a parser-alias row gives stack=")),
                    };
                    let auto_group = match group.strip_prefix("auto-group=") {
                        Some("true") => true,
                        Some("false") => false,
                        _ => return Err(fail("a parser-alias row gives auto-group=")),
                    };
                    let info = AliasInfo {
                        arity,
                        stack,
                        auto_group,
                    };
                    if aliases.insert((*name).to_string(), info).is_some() {
                        return Err(fail("a parser alias appears twice"));
                    }
                }
                ["category", name, _, ident_behavior, _] => {
                    let name = rendered_name(name).ok_or_else(|| fail("category name"))?;
                    let ident_behavior =
                        behavior(ident_behavior).ok_or_else(|| fail("behavior"))?;
                    categories.insert(name, (ident_behavior, None));
                }
                ["module-category", module, name, _, ident_behavior, _] => {
                    let module = rendered_name(module).ok_or_else(|| fail("module name"))?;
                    let name = rendered_name(name).ok_or_else(|| fail("category name"))?;
                    let ident_behavior =
                        behavior(ident_behavior).ok_or_else(|| fail("behavior"))?;
                    categories.insert(name, (ident_behavior, Some(module)));
                }
                [tag, ..]
                    if matches!(
                        *tag,
                        "syntax-decl"
                            | "syntax-descr"
                            | "parser-alias"
                            | "category"
                            | "module-category"
                    ) =>
                {
                    return Err(fail("a syntax row has the wrong number of fields"));
                }
                _ => {}
            }
        }
        for (what, found) in [
            ("init-std-syntax-descrs", descrs.len()),
            ("parser-aliases", aliases.len()),
        ] {
            if counts.get(what) != Some(&found) {
                return Err(ExtensionCensusError {
                    line: 0,
                    reason: format!(
                        "count {what} declares {:?}, rows give {found}",
                        counts.get(what)
                    ),
                });
            }
        }
        let mut decls = Vec::new();
        for (decl, (line, descr)) in descrs {
            let Some((_, module, category, leading, priority, scope)) = declared.remove(&decl)
            else {
                return Err(ExtensionCensusError {
                    line,
                    reason: "a description without its syntax-decl row".to_string(),
                });
            };
            decls.push(Arc::new(SyntaxDecl {
                module,
                decl,
                category,
                leading,
                priority,
                scope,
                descr,
            }));
        }
        if let Some((_, (line, ..))) = declared.into_iter().next() {
            return Err(ExtensionCensusError {
                line,
                reason: "a syntax declaration without its description".to_string(),
            });
        }
        Ok(ExtensionCensus {
            decls,
            aliases,
            categories,
        })
    }

    pub fn decls(&self) -> &[Arc<SyntaxDecl>] {
        &self.decls
    }
}

/// The checked-in census's syntax rows, parsed once.
pub fn extension_census() -> &'static ExtensionCensus {
    static CENSUS: OnceLock<ExtensionCensus> = OnceLock::new();
    CENSUS.get_or_init(|| {
        ExtensionCensus::parse(GRAMMAR_CENSUS).unwrap_or_else(|error| {
            panic!("invariant: contracts/REFERENCE_GRAMMAR_CENSUS.txt's syntax rows are unusable: {error:?}")
        })
    })
}

/// The active trailing `term` declarations of the infix shape `trailingNode k p lhs (andthen
/// (symbol s) (cat term rhs))` spelled by one symbol: what `infixl`, `infixr`, `infix` and
/// `notation:p a:lhs s b:rhs` compile to. Copy, so the bounded term parser's operator stack can
/// hold it; `id` indexes the active grammar's kinds for the symbol (several when several such
/// declarations are active, as two namespaces' `~m` are under `namespace Std.DTreeMap.Raw`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ExtensionInfix {
    pub(crate) id: u32,
    pub(crate) prec: u8,
    pub(crate) lhs_prec: u16,
    pub(crate) rhs_prec: u16,
}

impl ExtensionInfix {
    /// `infixr:p`: the left operand binds tighter, the right one admits the operator again.
    pub(crate) const fn is_right_associative(self) -> bool {
        self.lhs_prec == self.prec as u16 + 1 && self.rhs_prec == self.prec as u16
    }

    /// `infix:p`: neither operand admits the operator.
    pub(crate) const fn is_non_associative(self) -> bool {
        self.lhs_prec == self.prec as u16 + 1 && self.rhs_prec == self.prec as u16 + 1
    }
}

/// The grammar one command is parsed under: its token table and the active declarations.
#[derive(Debug)]
pub struct ActiveGrammar {
    table: TokenTable,
    decls: Vec<Arc<SyntaxDecl>>,
    infix: BTreeMap<String, ExtensionInfix>,
    /// Each [`ExtensionInfix`]'s node kinds, the most recently added parser first.
    infix_kinds: Vec<Vec<Name>>,
    /// Leading `tactic` declarations by the text of their first atom, highest priority first.
    tactics: BTreeMap<String, Vec<usize>>,
    /// Leading `term` declarations that read as an atom: at `lead` precedence or above, from a
    /// first atom to a last one (`syntax "⌜" term "⌝"`, `notation "-[" n "+1]"`, `notation "⊤"`),
    /// or, at `lead` or above, from a first atom to one argument (`prefix:max "√" => f`,
    /// `syntax "dbl " term:max : term`).
    terms: BTreeMap<String, Vec<usize>>,
    /// The atoms an `interpolatedStr` follows (`syntax "s!" interpolatedStr(term) : term`): the
    /// string after one is read by `interpolatedStrFn`, not as one string literal.
    interpolated: BTreeSet<String>,
    /// Every active declaration's node kind.
    kinds: BTreeSet<Name>,
    /// Leading `term` declarations of the prefix shape `node k p (andthen (symbol s) (cat term
    /// q))` (`notation:25 "⊢ₛ " p:25`): by symbol, the kind and the operand's precedence `q`.
    prefixes: BTreeMap<String, (Name, u8)>,
    /// Leading `attr` declarations by the text of their first atom.
    attrs: BTreeMap<String, Vec<usize>>,
    /// Leading `command` declarations by the text of their first atom.
    commands: BTreeMap<String, Vec<usize>>,
    /// Whether the imports' syntax is entered (see [`FileGrammar::own_syntax_only`]): only then
    /// does a census declaration missing here mean the file lacks it.
    imports_entered: bool,
    /// The file's notation expansion, when built from a [`FileGrammar`].
    expander: Option<Expander>,
    /// The doc-comment options in effect.
    docs: DocOptions,
}

/// The options that change how a doc comment parses (`Lean.Doc.Parser.ifVerso`,
/// `ifVersoModuleDocs`): `doc.verso`, and `doc.verso.module` for a module doc where it is set.
/// `set_option … in` does not change them for the command after it: the pin parses that command
/// before the option is set (the pin keeps its doc plain, 2026-10-09).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct DocOptions {
    verso: bool,
    verso_module: Option<bool>,
}

impl DocOptions {
    /// Whether a doc comment's body (`/--`), or a module doc's (`/-!`), is read as Verso.
    pub fn verso(self, module_doc: bool) -> bool {
        match self.verso_module {
            Some(verso) if module_doc => verso,
            _ => self.verso,
        }
    }
}

/// The doc-comment options of the grammar in effect; none set outside one.
pub(crate) fn doc_options() -> DocOptions {
    active().map_or_else(DocOptions::default, |grammar| grammar.docs)
}

impl ActiveGrammar {
    fn new(tokens: BTreeSet<String>, decls: Vec<Arc<SyntaxDecl>>) -> ActiveGrammar {
        let mut operators: BTreeMap<String, Vec<(ExtensionInfix, Name)>> = BTreeMap::new();
        let mut tactics: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        let mut terms: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        let mut attrs: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        let mut commands: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        let mut interpolated = BTreeSet::new();
        let kinds = decls
            .iter()
            .filter_map(|decl| match &decl.descr {
                Descr::Node { kind, .. } | Descr::TrailingNode { kind, .. } => Some(kind.clone()),
                _ => None,
            })
            .collect();
        let term = Name::from_components(["term"]);
        let tactic = Name::from_components(["tactic"]);
        let attr = Name::from_components(["attr"]);
        let command = Name::from_components(["command"]);
        let mut prefixes: BTreeMap<String, Vec<(Name, u8)>> = BTreeMap::new();
        for decl in &decls {
            if let (Some(category), true, Descr::Node { kind, body, .. }) =
                (&decl.category, decl.leading, &decl.descr)
                && *category == term
                && let Descr::Binary(andthen, left, right) = body.as_ref()
                && simple(andthen).as_deref() == Some("andthen")
                && let (Descr::Symbol(head), Descr::Cat(operand, rbp)) =
                    (left.as_ref(), right.as_ref())
                && *operand == term
                && *rbp < 256
                && !builtin_tokens().contains(head.trim())
            {
                prefixes
                    .entry(head.trim().to_string())
                    .or_default()
                    .push((kind.clone(), *rbp as u8));
            }
        }
        // One reading per symbol: two prefix notations on one symbol are the pin's `choice`, not
        // built here.
        let prefixes = prefixes
            .into_iter()
            .filter_map(|(symbol, mut entries)| {
                (entries.len() == 1).then(|| (symbol, entries.remove(0)))
            })
            .collect();
        for (index, decl) in decls.iter().enumerate() {
            if let (Some(category), true, Descr::Node { body, .. }) =
                (&decl.category, decl.leading, &decl.descr)
                && *category == term
                && let Descr::Binary(andthen, left, right) = body.as_ref()
                && simple(andthen).as_deref() == Some("andthen")
                && let (Descr::Symbol(head), Descr::Unary(alias, _)) =
                    (left.as_ref(), right.as_ref())
                && simple(alias).as_deref() == Some("interpolatedStr")
            {
                interpolated.insert(head.trim().to_string());
            }
            match (&decl.category, decl.leading, &decl.descr) {
                (
                    Some(category),
                    false,
                    Descr::TrailingNode {
                        kind,
                        prec,
                        lhs_prec,
                        body,
                    },
                ) if *category == term && *prec < 256 => {
                    let Descr::Binary(andthen, left, right) = body.as_ref() else {
                        continue;
                    };
                    let Descr::Cat(operand, rhs_prec) = right.as_ref() else {
                        continue;
                    };
                    // The operator's spellings: one symbol, or both of a unicode one
                    // (`unicode(" ≤ ", " <= ")`), each the same notation.
                    let spellings = match left.as_ref() {
                        Descr::Symbol(symbol) => vec![symbol.trim().to_string()],
                        Descr::UnicodeSymbol(text, ascii, _) => {
                            vec![text.trim().to_string(), ascii.trim().to_string()]
                        }
                        _ => continue,
                    };
                    if simple(andthen).as_deref() != Some("andthen") || *operand != term {
                        continue;
                    }
                    for spelling in spellings {
                        operators.entry(spelling).or_default().push((
                            ExtensionInfix {
                                id: 0,
                                prec: *prec as u8,
                                lhs_prec: (*lhs_prec).min(u32::from(u16::MAX)) as u16,
                                rhs_prec: (*rhs_prec).min(u32::from(u16::MAX)) as u16,
                            },
                            kind.clone(),
                        ));
                    }
                }
                (Some(category), true, descr) if *category == tactic => {
                    for head in heads(descr, 0) {
                        tactics.entry(head).or_default().push(index);
                    }
                }
                (Some(category), true, descr) if *category == attr => {
                    for head in heads(descr, 0) {
                        attrs.entry(head).or_default().push(index);
                    }
                }
                (Some(category), true, descr) if *category == command => {
                    for head in heads(descr, 0) {
                        commands.entry(head).or_default().push(index);
                    }
                }
                (Some(category), true, descr @ Descr::Node { prec, body, .. })
                    if *category == term
                        && *prec >= LEAD_PREC
                        && (ends_with_atom(body, 0) || symbol_then_argument(body)) =>
                {
                    // A named syntax abbreviation keeps `lead` as the default precedence even
                    // when its resolved description ends in an atom (`elabSyntax`). Its node
                    // still obeys the separate application and category precedence checks.
                    // A head that is a builtin token may also start a builtin term parser
                    // (`{` the structure instance, beside `«term{_}»`), which the pin runs too and
                    // which is not run here: such a notation is left to the hand grammar.
                    for head in heads(descr, 0) {
                        if !builtin_tokens().contains(head.as_str()) {
                            terms.entry(head).or_default().push(index);
                        }
                    }
                }
                _ => {}
            }
        }
        for candidates in tactics.values_mut() {
            candidates.sort_by_key(|&index| std::cmp::Reverse(decls[index].priority));
        }
        // Operators sharing a symbol and precedences read the same input, and the pin's
        // `longestMatchFn` keeps every one: a `choice` node whose alternatives come in the
        // trailing table's order, the most recently added first (`addTrailingParser` conses).
        // Different precedences would parse differently, which is not built here.
        let mut infix = BTreeMap::new();
        let mut infix_kinds = Vec::new();
        for (symbol, entries) in operators {
            let (first, _) = entries[0];
            if entries.iter().any(|(entry, _)| {
                (entry.prec, entry.lhs_prec, entry.rhs_prec)
                    != (first.prec, first.lhs_prec, first.rhs_prec)
            }) {
                continue;
            }
            infix.insert(
                symbol,
                ExtensionInfix {
                    id: infix_kinds.len() as u32,
                    ..first
                },
            );
            infix_kinds.push(entries.into_iter().rev().map(|(_, kind)| kind).collect());
        }
        ActiveGrammar {
            table: TokenTable::from_tokens(tokens),
            decls,
            infix,
            infix_kinds,
            tactics,
            terms,
            interpolated,
            kinds,
            prefixes,
            attrs,
            commands,
            imports_entered: true,
            expander: None,
            docs: DocOptions::default(),
        }
    }

    pub fn table(&self) -> &TokenTable {
        &self.table
    }
}

/// The atoms a description can start with, through the wrappers that add no input.
fn heads(descr: &Descr, depth: usize) -> Vec<String> {
    if depth > MAX_DESCR_DEPTH {
        return Vec::new();
    }
    match descr {
        Descr::Symbol(text) | Descr::NonReservedSymbol(text, _) => vec![text.trim().to_string()],
        Descr::UnicodeSymbol(text, ascii, _) => {
            vec![text.trim().to_string(), ascii.trim().to_string()]
        }
        Descr::Node { body, .. } | Descr::NodeWithAntiquot(_, _, body) => heads(body, depth + 1),
        Descr::Unary(name, body) if transparent(name) => heads(body, depth + 1),
        Descr::Binary(name, left, right) => match simple(name).as_deref() {
            Some("andthen") => heads(left, depth + 1),
            Some("orelse") => {
                let mut out = heads(left, depth + 1);
                out.extend(heads(right, depth + 1));
                out
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

/// The builtin token table (`builtinTokenTable`): every token some builtin parser reads.
fn builtin_tokens() -> &'static BTreeSet<&'static str> {
    static TOKENS: OnceLock<BTreeSet<&'static str>> = OnceLock::new();
    TOKENS.get_or_init(|| reference_census().builtin_tokens().collect())
}

/// `andthen (symbol s) (cat term q)` with `q` at `arg` or above (`prefix:max "√" => f`, which
/// `expandMixfix` makes `notation:max "√" arg:max`): its operand is one argument, so it reads as an
/// atom does.
fn symbol_then_argument(body: &Descr) -> bool {
    matches!(body, Descr::Binary(andthen, left, right)
        if simple(andthen).as_deref() == Some("andthen")
            && matches!(left.as_ref(), Descr::Symbol(_))
            && matches!(right.as_ref(), Descr::Cat(category, prec)
                if simple(category).as_deref() == Some("term") && *prec >= 1023))
}

/// Whether every input `descr` reads ends with an atom, so the parser it compiles to ends where
/// that atom does rather than where a trailing term would.
fn ends_with_atom(descr: &Descr, depth: usize) -> bool {
    if depth > MAX_DESCR_DEPTH {
        return false;
    }
    match descr {
        Descr::Symbol(_) | Descr::NonReservedSymbol(..) | Descr::UnicodeSymbol(..) => true,
        Descr::Node { body, .. } | Descr::NodeWithAntiquot(_, _, body) => {
            ends_with_atom(body, depth + 1)
        }
        Descr::Unary(name, body) if transparent(name) => ends_with_atom(body, depth + 1),
        // An interpolated string ends with its closing chunk.
        Descr::Unary(name, _) if simple(name).as_deref() == Some("interpolatedStr") => true,
        Descr::Binary(name, left, right) => match simple(name).as_deref() {
            Some("andthen") => ends_with_atom(right, depth + 1),
            Some("orelse") => ends_with_atom(left, depth + 1) && ends_with_atom(right, depth + 1),
            _ => false,
        },
        _ => false,
    }
}

/// The one-argument aliases that only shape pretty-printing, positions or backtracking: their
/// argument's syntax is theirs, unchanged.
fn transparent(name: &Name) -> bool {
    matches!(
        simple(name).as_deref(),
        Some(
            "atomic"
                | "patternIgnore"
                | "ppGroup"
                | "ppIndent"
                | "ppDedent"
                | "ppDedentIfGrouped"
                | "ppRealFill"
                | "ppRealGroup"
                | "withPosition"
                | "withoutPosition"
                | "withoutForbidden"
        )
    )
}

/// What one scope's trailing and leading tables hold beyond the imported global entries, in the
/// order it was added: the pin's tables are lists that `addParser` conses onto, so when several
/// parsers read the same input, the order of `choice`'s alternatives is this order reversed.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Trail {
    /// `activateScoped ns`: the imported entries for `ns`, then the file's own declared before
    /// this activation (indices below the count).
    Namespace(Name, usize),
    /// A declaration of this file, added where it was declared.
    Decl(usize),
}

#[derive(Debug, Clone)]
struct FileScope {
    namespace: Name,
    trail: Vec<Trail>,
    opens: Vec<Name>,
    docs: DocOptions,
}

impl FileScope {
    fn is_active(&self, namespace: &Name) -> bool {
        self.trail
            .iter()
            .any(|entry| matches!(entry, Trail::Namespace(active, _) if active == namespace))
    }
}

/// One file's syntax state: what its imports declare, what it has declared so far, and which
/// scoped namespaces its commands have activated.
pub struct FileGrammar {
    module: Option<Name>,
    base_tokens: BTreeSet<String>,
    imported: Vec<Arc<SyntaxDecl>>,
    /// Native source imports have both descriptions and expansions. They remain
    /// active when `own_syntax_only` omits the census's expansion-less parsers.
    native_imported: Vec<Arc<SyntaxDecl>>,
    native_scoped: BTreeMap<Name, Vec<Arc<SyntaxDecl>>>,
    native_abbreviations: BTreeSet<Name>,
    scoped: BTreeMap<Name, Vec<Arc<SyntaxDecl>>>,
    scoped_tokens: BTreeMap<Name, BTreeSet<String>>,
    /// The file's own `scoped` declarations, by namespace, indices into `declared`.
    scoped_declared: BTreeMap<Name, Vec<usize>>,
    categories: BTreeMap<Name, IdentBehavior>,
    abbreviations: BTreeMap<Name, Descr>,
    /// Declaration names taken by an imported or earlier syntax declaration (`elabSyntax`'s
    /// fresh-name loop checks the environment for them).
    constants: BTreeSet<Name>,
    declared: Vec<Arc<SyntaxDecl>>,
    local_declared: BTreeSet<Name>,
    declared_categories: BTreeMap<Name, IdentBehavior>,
    native_export_refusal: Option<&'static str>,
    /// Tokens declared other than by a parser: a declared category's quotation opener.
    declared_tokens: BTreeSet<String>,
    /// Bumped by every declaration, so a cached grammar never outlives one.
    generation: usize,
    /// What the file's notations expand to, by node kind.
    rules: Arc<BTreeMap<Name, Arc<NotationRule>>>,
    /// Expansions made so far, shared with every grammar built from this file: each takes the
    /// next macro scope.
    expansions: Rc<Cell<u64>>,
    /// Whether the imports' syntax is entered, or only the file's own ([`Self::own_syntax_only`]).
    imports_entered: bool,
    scopes: Vec<FileScope>,
    cache: RefCell<GrammarCache>,
}

/// Grammars already built, by the trail and the declaration generation they were built for.
type GrammarCache = BTreeMap<(Vec<Trail>, DocOptions, usize), Rc<ActiveGrammar>>;

impl FileGrammar {
    /// The state at the top of a file with this header. `module`, the file's own module name,
    /// names its `local` syntax (`mkPrivateName`); without it a `local` declaration is refused.
    pub fn new(
        prelude: bool,
        imports: &[Name],
        module: Option<Name>,
    ) -> Result<FileGrammar, UnknownModule> {
        let tokens = reference_census();
        let closure = tokens.closure(prelude, imports)?;
        let census = extension_census();
        let mut imported = Vec::new();
        let mut scoped: BTreeMap<Name, Vec<Arc<SyntaxDecl>>> = BTreeMap::new();
        let mut scoped_tokens: BTreeMap<Name, BTreeSet<String>> = BTreeMap::new();
        let mut abbreviations = BTreeMap::new();
        let mut constants = BTreeSet::new();
        for decl in &census.decls {
            if !closure.contains(&decl.module) {
                continue;
            }
            constants.insert(decl.decl.clone());
            if decl.category.is_none() {
                abbreviations.insert(decl.decl.clone(), decl.descr.clone());
                continue;
            }
            match &decl.scope {
                None => imported.push(Arc::clone(decl)),
                Some(namespace) => {
                    scoped
                        .entry(namespace.clone())
                        .or_default()
                        .push(Arc::clone(decl));
                    scoped_tokens.entry(namespace.clone()).or_default().extend(
                        tokens
                            .scoped_tokens(&decl.module, namespace)
                            .map(str::to_string),
                    );
                }
            }
        }
        let categories = census
            .categories
            .iter()
            .filter(|(_, (_, module))| {
                module
                    .as_ref()
                    .is_none_or(|module| closure.contains(module))
            })
            .map(|(name, (ident_behavior, _))| (name.clone(), *ident_behavior))
            .collect();
        Ok(FileGrammar {
            module,
            base_tokens: tokens.tokens_for(prelude, imports)?,
            imported,
            native_imported: Vec::new(),
            native_scoped: BTreeMap::new(),
            native_abbreviations: BTreeSet::new(),
            scoped,
            scoped_tokens,
            scoped_declared: BTreeMap::new(),
            categories,
            abbreviations,
            constants,
            declared: Vec::new(),
            local_declared: BTreeSet::new(),
            declared_categories: BTreeMap::new(),
            native_export_refusal: None,
            declared_tokens: BTreeSet::new(),
            generation: 0,
            rules: Arc::new(BTreeMap::new()),
            expansions: Rc::new(Cell::new(0)),
            imports_entered: true,
            scopes: vec![FileScope {
                namespace: Name::anonymous(),
                trail: Vec::new(),
                opens: Vec::new(),
                docs: DocOptions::default(),
            }],
            cache: RefCell::new(BTreeMap::new()),
        })
    }

    /// This state with only the file's own declarations entered, over the import closure's
    /// token table: the imports' notations and syntax (scoped ones too) are not, so the parser
    /// reads their uses as it does without a grammar. For a path whose elaborator expands the
    /// file's notations but has no expansion for an imported one: entering Init's `«term{}»`
    /// would make `{}` the pin's `choice`, which that elaborator cannot resolve.
    pub fn own_syntax_only(mut self) -> FileGrammar {
        self.imports_entered = false;
        self.cache.borrow_mut().clear();
        self
    }

    fn top(&self) -> &FileScope {
        self.scopes.last().expect("the file scope is never popped")
    }

    fn top_mut(&mut self) -> &mut FileScope {
        self.scopes
            .last_mut()
            .expect("the file scope is never popped")
    }

    /// The declarations this file has registered so far, in order.
    pub fn declared(&self) -> &[Arc<SyntaxDecl>] {
        &self.declared
    }

    /// Whether `namespace` carries scoped syntax, imported or this file's.
    fn has_scoped(&self, namespace: &Name) -> bool {
        self.scoped.contains_key(namespace)
            || self.native_scoped.contains_key(namespace)
            || self.scoped_declared.contains_key(namespace)
    }

    /// `resolveNamespace` (`Lean/ResolveName.lean`) over the namespaces with scoped syntax.
    fn resolve(&self, name: &Name) -> Vec<Name> {
        let top = self.top();
        let mut out = Vec::new();
        let mut prefix = top.namespace.clone();
        loop {
            let candidate = prefix.append_core(name);
            if self.has_scoped(&candidate) {
                out.push(candidate);
                break;
            }
            if prefix.is_anonymous() {
                break;
            }
            prefix = prefix.parent();
        }
        for open in top.opens.iter().rev() {
            let candidate = open.append_core(name);
            if self.has_scoped(&candidate) && !out.contains(&candidate) {
                out.push(candidate);
            }
        }
        out
    }

    /// `activateScoped`: a namespace already active in the scope adds nothing.
    fn activate_in(&self, scope: &mut FileScope, namespace: Name) {
        if !scope.is_active(&namespace) {
            scope
                .trail
                .push(Trail::Namespace(namespace, self.declared.len()));
        }
    }

    fn activate(&mut self, names: &[Name], simple: bool) {
        let resolved: Vec<Name> = names.iter().flat_map(|name| self.resolve(name)).collect();
        let mut top = self.top().clone();
        for namespace in resolved {
            self.activate_in(&mut top, namespace);
        }
        if simple {
            top.opens.extend(names.iter().cloned());
        }
        *self.top_mut() = top;
    }

    fn push(&mut self, namespace: Name, activate: bool) {
        let mut scope = self.top().clone();
        if activate {
            self.activate_in(&mut scope, namespace.clone());
        }
        scope.namespace = namespace;
        self.scopes.push(scope);
    }

    /// Advance past one scope command, as the pin's elaborator does.
    pub fn apply(&mut self, command: &ScopeCommand) {
        match command {
            ScopeCommand::Namespace(name) => {
                for component in components(name) {
                    let namespace = Name::str(self.top().namespace.clone(), component);
                    self.push(namespace, true);
                }
            }
            ScopeCommand::Section(name) | ScopeCommand::SectionWithModifiers { name, .. } => {
                let count = name
                    .as_ref()
                    .map_or(1, |name| components(name).len().max(1));
                for _ in 0..count {
                    self.push(self.top().namespace.clone(), false);
                }
            }
            ScopeCommand::End(name) => {
                let count = name
                    .as_ref()
                    .map_or(1, |name| components(name).len().max(1));
                for _ in 0..count {
                    if self.scopes.len() > 1 {
                        self.scopes.pop();
                    }
                }
            }
            ScopeCommand::Open(names) => self.activate(names, true),
            ScopeCommand::OpenScoped(names) => self.activate(names, false),
            ScopeCommand::SetOption {
                name,
                value: DataValue::OfBool(value),
            } => {
                let docs = &mut self.top_mut().docs;
                if *name == Name::from_components(["doc", "verso"]) {
                    docs.verso = *value;
                } else if *name == Name::from_components(["doc", "verso", "module"]) {
                    docs.verso_module = Some(*value);
                }
            }
            _ => {}
        }
    }

    /// The grammar the next command is parsed under.
    pub fn grammar(&self) -> Rc<ActiveGrammar> {
        self.grammar_for(self.top().trail.clone(), self.top().docs)
    }

    /// The grammar of the command after `open names in`.
    pub fn grammar_opening(&self, names: &[Name]) -> Rc<ActiveGrammar> {
        let mut scope = self.top().clone();
        for namespace in names.iter().flat_map(|name| self.resolve(name)) {
            self.activate_in(&mut scope, namespace);
        }
        self.grammar_for(scope.trail, scope.docs)
    }

    fn grammar_for(&self, trail: Vec<Trail>, docs: DocOptions) -> Rc<ActiveGrammar> {
        let key = (trail, docs, self.generation);
        if let Some(grammar) = self.cache.borrow().get(&key) {
            return Rc::clone(grammar);
        }
        let mut tokens = self.base_tokens.clone();
        tokens.extend(self.declared_tokens.iter().cloned());
        let mut decls = if self.imports_entered {
            self.imported.clone()
        } else {
            Vec::new()
        };
        decls.extend(self.native_imported.iter().cloned());
        let own =
            |index: usize, tokens: &mut BTreeSet<String>, decls: &mut Vec<Arc<SyntaxDecl>>| {
                let decl = &self.declared[index];
                if decl.category.is_some() {
                    decl.descr.collect_tokens(tokens);
                    decls.push(Arc::clone(decl));
                }
            };
        for entry in &key.0 {
            match entry {
                Trail::Namespace(namespace, declared_before) => {
                    if self.imports_entered {
                        if let Some(scoped) = self.scoped.get(namespace) {
                            decls.extend(scoped.iter().cloned());
                        }
                        if let Some(scoped) = self.scoped_tokens.get(namespace) {
                            tokens.extend(scoped.iter().cloned());
                        }
                    }
                    if let Some(scoped) = self.native_scoped.get(namespace) {
                        for decl in scoped {
                            decl.descr.collect_tokens(&mut tokens);
                            decls.push(Arc::clone(decl));
                        }
                    }
                    for &index in self.scoped_declared.get(namespace).into_iter().flatten() {
                        if index < *declared_before {
                            own(index, &mut tokens, &mut decls);
                        }
                    }
                }
                Trail::Decl(index) => own(*index, &mut tokens, &mut decls),
            }
        }
        let mut grammar = ActiveGrammar::new(tokens, decls);
        grammar.imports_entered = self.imports_entered;
        grammar.expander = Some(self.expander());
        grammar.docs = docs;
        let grammar = Rc::new(grammar);
        self.cache.borrow_mut().insert(key, Rc::clone(&grammar));
        grammar
    }

    /// Register the syntax a `syntax`, syntax abbreviation, `notation` or mixfix command
    /// declares, as the pin's elaborator does. `Ok(None)` for any other command; `Err` names
    /// what is not translated, and nothing is registered then.
    pub fn declare(&mut self, command: &Syntax) -> Result<Option<Arc<SyntaxDecl>>, &'static str> {
        let Syntax::Node { kind, args, .. } = command else {
            return Ok(None);
        };
        let command_kind = components(kind);
        let parts: Vec<&str> = command_kind.iter().map(String::as_str).collect();
        let mut rule = None;
        let declaration = match parts.as_slice() {
            ["Lean", "Parser", "Command", "syntax"] => {
                let [
                    _,
                    _,
                    attr_kind,
                    _,
                    precedence,
                    name,
                    priority,
                    items,
                    _,
                    category,
                ] = args.as_slice()
                else {
                    return Err("a syntax command's shape");
                };
                let items = null_args(items).ok_or("syntax items")?;
                let items = items.iter().map(stx_item).collect::<Result<Vec<_>, _>>()?;
                let category = ident_name(category).ok_or("a syntax category")?;
                Declaration {
                    attr_kind: attr_kind_of(attr_kind)?,
                    precedence: optional_precedence(precedence)?,
                    name: named(name, ident_name)?,
                    priority: named(priority, prio_value)?,
                    items,
                    category,
                }
            }
            ["Lean", "Parser", "Command", "syntaxAbbrev"] => {
                self.generation += 1;
                return self.declare_abbreviation(args).map(Some);
            }
            ["Lean", "Parser", "Command", "syntaxCat"] => {
                self.declare_category(args)?;
                return Ok(None);
            }
            ["Lean", "Parser", "Command", "notation"] => {
                let [
                    _,
                    _,
                    attr_kind,
                    _,
                    precedence,
                    name,
                    priority,
                    items,
                    _,
                    rhs,
                ] = args.as_slice()
                else {
                    return Err("a notation command's shape");
                };
                let items = null_args(items).ok_or("notation items")?;
                // `elabNotation`'s `macro_rules`: each `identPrec` item is the variable its child
                // binds, the right-hand side the template.
                let variables = items
                    .iter()
                    .enumerate()
                    .filter(|(_, item)| kind_is(item, &["Lean", "Parser", "Command", "identPrec"]))
                    .map(|(position, item)| match item {
                        Syntax::Node { args, .. } => args
                            .first()
                            .and_then(ident_name)
                            .map(|name| (position, name))
                            .ok_or("a notation variable"),
                        _ => Err("a notation variable"),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                rule = Some(NotationRule {
                    variables,
                    rhs: rhs.clone(),
                    prechecked: true,
                });
                Declaration {
                    attr_kind: attr_kind_of(attr_kind)?,
                    precedence: optional_precedence(precedence)?,
                    name: named(name, ident_name)?,
                    priority: Some(named(priority, prio_value)?.unwrap_or(DEFAULT_PRIORITY)),
                    items: items
                        .iter()
                        .map(notation_item)
                        .collect::<Result<Vec<_>, _>>()?,
                    category: Name::from_components(["term"]),
                }
            }
            ["Lean", "Parser", "Command", "mixfix"] => {
                let [
                    _,
                    _,
                    attr_kind,
                    fixity,
                    precedence,
                    name,
                    priority,
                    op,
                    _,
                    function,
                ] = args.as_slice()
                else {
                    return Err("a mixfix command's shape");
                };
                let fixity = match fixity {
                    Syntax::Node { kind, .. } => {
                        components(kind).last().cloned().unwrap_or_default()
                    }
                    _ => return Err("a mixfix keyword"),
                };
                let prec = precedence_value(precedence).ok_or("a mixfix precedence")?;
                let op = notation_item(op)?;
                let operand = |prec| StxItem::Cat(Name::from_components(["term"]), Some(prec));
                // `expandMixfix` (`Lean/Elab/Mixfix.lean`): each fixity as the notation it is.
                let items = match fixity.as_str() {
                    "infixl" => vec![operand(prec), op, operand(prec + 1)],
                    "infix" => vec![operand(prec + 1), op, operand(prec + 1)],
                    "infixr" => vec![operand(prec + 1), op, operand(prec)],
                    "prefix" => vec![op, operand(prec)],
                    "postfix" => vec![operand(prec), op],
                    _ => return Err("a mixfix keyword"),
                };
                // `expandMixfix`'s notation: `f lhs rhs` (or `f arg`) over the operand children,
                // its variables the macro's own hygienic names.
                let variables: Vec<(usize, Name)> = match fixity.as_str() {
                    "prefix" => vec![(1, mixfix_variable("arg"))],
                    "postfix" => vec![(0, mixfix_variable("arg"))],
                    _ => vec![(0, mixfix_variable("lhs")), (2, mixfix_variable("rhs"))],
                };
                let arguments = variables
                    .iter()
                    .map(|(_, name)| synthetic_ident(name.clone()))
                    .collect();
                rule = Some(NotationRule {
                    rhs: Syntax::node(
                        Name::from_components(["Lean", "Parser", "Term", "app"]),
                        vec![function.clone(), null_node(arguments)],
                    ),
                    variables,
                    prechecked: true,
                });
                Declaration {
                    attr_kind: attr_kind_of(attr_kind)?,
                    precedence: Some(prec),
                    name: named(name, ident_name)?,
                    priority: Some(named(priority, prio_value)?.unwrap_or(DEFAULT_PRIORITY)),
                    items,
                    category: Name::from_components(["term"]),
                }
            }
            ["Lean", "Parser", "Command", "macro"] => {
                let [
                    _,
                    _,
                    attr_kind,
                    _,
                    precedence,
                    name,
                    priority,
                    arguments,
                    tail,
                ] = args.as_slice()
                else {
                    return Err("a macro command's shape");
                };
                // `elabMacro`: the `syntax` its arguments spell, and a `macro_rules` whose pattern
                // binds each named argument's child.
                let mut items = Vec::new();
                let mut variables = Vec::new();
                for (position, argument) in null_args(arguments)
                    .ok_or("macro arguments")?
                    .iter()
                    .enumerate()
                {
                    let Some([binder, item]) = node_args(argument) else {
                        return Err("a macro argument");
                    };
                    let named = if let Some([variable, _]) = null_args(binder) {
                        let variable = ident_name(variable).ok_or("a macro variable")?;
                        variables.push((position, macro_variable(&variable)));
                        true
                    } else {
                        false
                    };
                    items.push(macro_item(stx_item(item)?, named));
                }
                let Some([_, category, _, rhs]) = node_args(tail) else {
                    return Err("a macro's tail");
                };
                let category = ident_name(category).ok_or("a macro category")?;
                let template = node_args(rhs)
                    .and_then(|rhs| rhs.first())
                    .ok_or("a macro's right-hand side")?;
                // A template this does not translate leaves the syntax without a rule: its uses
                // reach the elaborator unexpanded and are refused there.
                rule = macro_template(template, &category, &variables)
                    .ok()
                    .map(|rhs| NotationRule {
                        variables,
                        rhs,
                        prechecked: false,
                    });
                Declaration {
                    attr_kind: attr_kind_of(attr_kind)?,
                    precedence: optional_precedence(precedence)?,
                    name: named(name, ident_name)?,
                    priority: named(priority, prio_value)?,
                    items,
                    category,
                }
            }
            ["Lean", "Parser", "Command", "macro_rules"] => {
                self.declare_macro_rules(args);
                return Ok(None);
            }
            _ => return Ok(None),
        };
        self.generation += 1;
        let decl = self.elab_syntax(declaration)?;
        if let Some(rule) = rule {
            Arc::make_mut(&mut self.rules).insert(decl.decl.clone(), Arc::new(rule));
        }
        Ok(Some(decl))
    }

    /// `macro_rules` for a syntax this file declared: one alternative, its pattern the kind's
    /// node with each child an atom or an antiquotation, its right-hand side a quotation. The
    /// pin tries a kind's rules newest first, falling back on failure; this keeps one rule per
    /// kind, so a second one for a kind (or one this does not translate, for a kind with a rule)
    /// removes the rule, and the kind's uses are refused unexpanded rather than read by an older
    /// rule. Rules for other kinds are not this file's to read here.
    fn declare_macro_rules(&mut self, args: &[Syntax]) {
        let [_, _, attr_kind, _, opt_kind, alternatives] = args else {
            return;
        };
        if attr_kind_of(attr_kind) != Ok(AttrKind::Global) {
            // The current single-rule expander has no independent scoped rule
            // stack. Do not export a local/scoped override as a global macro.
            self.native_export_refusal =
                Some("source module export of scoped or local macro_rules");
        }
        let target = node_args(alternatives)
            .and_then(<[Syntax]>::first)
            .and_then(null_args)
            .and_then(|alternatives| match alternatives {
                [alternative] => Some(alternative),
                _ => None,
            })
            .and_then(node_args)
            .and_then(|alternative| match alternative {
                [_, groups, _, rhs] => Some((groups, rhs)),
                _ => None,
            })
            .and_then(|(groups, rhs)| match null_args(groups) {
                Some([group]) => match null_args(group) {
                    Some([pattern]) => Some((pattern, rhs)),
                    _ => None,
                },
                _ => None,
            });
        let kind = target.and_then(|(pattern, _)| quotation_root(pattern).map(|(kind, ..)| kind));
        let rule = (null_args(opt_kind).is_some_and(<[Syntax]>::is_empty))
            .then_some(target)
            .flatten()
            .and_then(|(pattern, rhs)| {
                let (kind, category, children) = quotation_root(pattern)?;
                let mut variables = Vec::new();
                for (position, child) in children.iter().enumerate() {
                    match child {
                        Syntax::Atom { .. } => {}
                        _ => {
                            variables.push((position, macro_variable(&antiquotation_name(child)?)))
                        }
                    }
                }
                let rhs = macro_template(rhs, &category, &variables).ok()?;
                Some((
                    kind,
                    NotationRule {
                        variables,
                        rhs,
                        prechecked: false,
                    },
                ))
            });
        if kind.as_ref().is_some_and(|kind| {
            self.constants.contains(kind) && !self.declared.iter().any(|decl| decl.decl == *kind)
        }) {
            self.native_export_refusal =
                Some("source module export of macro_rules for imported syntax");
        }
        let Some(kind) = kind.filter(|kind| self.declared.iter().any(|decl| decl.decl == *kind))
        else {
            return;
        };
        self.generation += 1;
        let rules = Arc::make_mut(&mut self.rules);
        match rule {
            Some((_, rule)) if !rules.contains_key(&kind) => {
                rules.insert(kind, Arc::new(rule));
            }
            _ => {
                rules.remove(&kind);
            }
        }
    }

    fn expander(&self) -> Expander {
        Expander {
            rules: Arc::clone(&self.rules),
            expansions: Rc::clone(&self.expansions),
            context: self.module.clone().unwrap_or_else(Name::anonymous),
        }
    }

    /// Expand every node of a notation this file declared, as its `macro_rules` would (see
    /// [`Expander::expand`]).
    pub fn expand(&mut self, syntax: &Syntax) -> Result<Syntax, &'static str> {
        self.expander().expand(syntax)
    }

    /// Replace the template of the rule for `kind`: the caller's pre-resolved copy, its
    /// identifiers naming what they named where the notation was declared. `false` when no rule
    /// expands `kind`.
    pub fn set_rule_template(&mut self, kind: &Name, rhs: Syntax) -> bool {
        let Some(rule) = Arc::make_mut(&mut self.rules).get_mut(kind) else {
            return false;
        };
        Arc::make_mut(rule).rhs = rhs;
        self.generation += 1;
        true
    }

    /// The notation rules this file has declared, by node kind.
    pub fn rules(&self) -> impl Iterator<Item = (&Name, &NotationRule)> {
        self.rules.iter().map(|(kind, rule)| (kind, rule.as_ref()))
    }

    /// `elabDeclareSyntaxCat`: the category, under the name as written, with its identifier
    /// behavior; its quotation parser `` `(cat| … ) `` (`declareSyntaxCatQuotParser`) brings the
    /// opener's token.
    fn declare_category(&mut self, args: &[Syntax]) -> Result<(), &'static str> {
        let [_, _, name, behavior] = args else {
            return Err("a declare_syntax_cat command's shape");
        };
        let name = ident_name(name).ok_or("a category name")?;
        let behavior = match null_args(behavior) {
            Some([]) => IdentBehavior::Default,
            Some([_, _, _, value, _])
                if kind_is(value, &["Lean", "Parser", "Command", "catBehaviorBoth"]) =>
            {
                IdentBehavior::Both
            }
            Some([_, _, _, value, _])
                if kind_is(value, &["Lean", "Parser", "Command", "catBehaviorSymbol"]) =>
            {
                IdentBehavior::Symbol
            }
            _ => return Err("a category behavior"),
        };
        let suffix = match name.leaf_view() {
            LeafView::Str(suffix) => suffix.to_string(),
            _ => return Err("a category name"),
        };
        self.declared_categories.insert(name.clone(), behavior);
        self.categories.insert(name, behavior);
        self.declared_tokens.insert(format!("`({suffix}|"));
        self.generation += 1;
        Ok(())
    }

    fn declare_abbreviation(&mut self, args: &[Syntax]) -> Result<Arc<SyntaxDecl>, &'static str> {
        // `elabSyntaxAbbrev`: `syntax x := items` is the description
        // `nodeWithAntiquot "x" (ns ++ x) items`, with no category.
        let [_, visibility, _, name, _, items] = args else {
            return Err("a syntax abbreviation's shape");
        };
        let name = ident_name(name).ok_or("an abbreviation name")?;
        let items = null_args(items).ok_or("abbreviation items")?;
        let items = items.iter().map(stx_item).collect::<Result<Vec<_>, _>>()?;
        let context = Context {
            category: Name::anonymous(),
            first: true,
            left_recursive: true,
            behavior: IdentBehavior::Default,
        };
        let mut trailing = None;
        let (descr, _) = self.process_seq(&items, &context, &mut trailing)?;
        let decl_name = self.top().namespace.append_core(&name);
        if null_args(visibility).is_some_and(|values| {
            values
                .iter()
                .any(|value| kind_is(value, &["Lean", "Parser", "Command", "private"]))
        }) {
            self.local_declared.insert(decl_name.clone());
        }
        let descr =
            Descr::NodeWithAntiquot(name.to_display_string(), decl_name.clone(), Box::new(descr));
        self.abbreviations.insert(decl_name.clone(), descr.clone());
        self.constants.insert(decl_name.clone());
        let decl = Arc::new(SyntaxDecl {
            module: self.module.clone().unwrap_or_else(Name::anonymous),
            decl: decl_name,
            category: None,
            leading: true,
            priority: 0,
            scope: None,
            descr,
        });
        self.declared.push(Arc::clone(&decl));
        Ok(decl)
    }

    /// `elabSyntax` (`Lean/Elab/Syntax.lean`).
    fn elab_syntax(&mut self, declaration: Declaration) -> Result<Arc<SyntaxDecl>, &'static str> {
        let behavior = *self
            .categories
            .get(&declaration.category)
            .ok_or("an unknown syntax category")?;
        let prec = declaration.precedence.unwrap_or_else(|| {
            if atom_like_seq(&declaration.items) {
                MAX_PREC
            } else {
                LEAD_PREC
            }
        });
        let namespace = self.top().namespace.clone();
        let name = match declaration.name {
            Some(name) => name,
            None => {
                let base = format!(
                    "{}{}",
                    simple(&declaration.category).ok_or("a dotted category")?,
                    name_from_items(&declaration.items)
                );
                let mut name = Name::str(Name::anonymous(), base.as_str());
                let mut index = 1;
                while self.constants.contains(&namespace.append_core(&name)) {
                    name = Name::str(Name::anonymous(), format!("{base}_{index}"));
                    index += 1;
                }
                name
            }
        };
        let context = Context {
            category: declaration.category.clone(),
            first: true,
            left_recursive: true,
            behavior,
        };
        let mut trailing = None;
        let (body, _) = self.process_seq(&declaration.items, &context, &mut trailing)?;
        let full_name = namespace.append_core(&name);
        let (kind, scope) = match declaration.attr_kind {
            AttrKind::Global => (full_name.clone(), None),
            AttrKind::Scoped => (full_name.clone(), Some(namespace)),
            AttrKind::Local => {
                let module = self
                    .module
                    .clone()
                    .ok_or("a local declaration with no module name")?;
                let kind = private_name(&module, &full_name);
                self.local_declared.insert(kind.clone());
                (kind, None)
            }
        };
        let descr = match trailing {
            Some(lhs_prec) => Descr::TrailingNode {
                kind: kind.clone(),
                prec,
                lhs_prec,
                body: Box::new(body),
            },
            None => Descr::Node {
                kind: kind.clone(),
                prec,
                body: Box::new(body),
            },
        };
        self.constants.insert(full_name);
        let decl = Arc::new(SyntaxDecl {
            module: self.module.clone().unwrap_or_else(Name::anonymous),
            decl: kind,
            category: Some(declaration.category),
            leading: trailing.is_none(),
            priority: declaration.priority.unwrap_or(DEFAULT_PRIORITY),
            scope: scope.clone(),
            descr,
        });
        let index = self.declared.len();
        self.declared.push(Arc::clone(&decl));
        // `ScopedEnvExtension` (`Lean/ScopedEnvExtension.lean`): a global entry joins every
        // state on the scope stack, a local one the current state, and a scoped one every state
        // where its namespace is active (`addScopedEntry`) and every later activation of it.
        match scope {
            Some(namespace) => {
                for scope in &mut self.scopes {
                    if scope.is_active(&namespace) {
                        scope.trail.push(Trail::Decl(index));
                    }
                }
                self.scoped_declared
                    .entry(namespace)
                    .or_default()
                    .push(index);
            }
            None if declaration.attr_kind == AttrKind::Local => {
                self.top_mut().trail.push(Trail::Decl(index));
            }
            None => {
                for scope in &mut self.scopes {
                    scope.trail.push(Trail::Decl(index));
                }
            }
        }
        Ok(decl)
    }

    /// `toParserDescr.processSeq`: a sequence, left-recursive when its first item is the
    /// category itself.
    fn process_seq(
        &self,
        items: &[StxItem],
        context: &Context,
        trailing: &mut Option<u32>,
    ) -> Result<(Descr, usize), &'static str> {
        let mut parts = Vec::new();
        let mut rest = items;
        if context.first
            && let Some(StxItem::Cat(name, prec)) = items.first()
            && *name == context.category
        {
            if !context.left_recursive || items.len() == 1 {
                return Err("left-recursive syntax the pin refuses");
            }
            *trailing = Some(prec.unwrap_or(0));
            rest = &items[1..];
            let nested = context.nested();
            for item in rest {
                parts.push(self.process(item, &nested, trailing)?);
            }
            return parser_seq(parts);
        }
        for (index, item) in rest.iter().enumerate() {
            let mut item_context = context.clone();
            item_context.first = context.first && index == 0;
            parts.push(self.process(item, &item_context, trailing)?);
        }
        parser_seq(parts)
    }

    fn process(
        &self,
        item: &StxItem,
        context: &Context,
        trailing: &mut Option<u32>,
    ) -> Result<(Descr, usize), &'static str> {
        match item {
            StxItem::Paren(items) => self.process_seq(items, context, trailing),
            StxItem::Atom(text) => {
                valid_atom(text)?;
                // `processAtom`: in a category whose identifiers can name productions, the first
                // atom is non-reserved.
                if context.behavior != IdentBehavior::Default && context.first {
                    Ok((Descr::NonReservedSymbol(text.clone(), false), 1))
                } else {
                    Ok((Descr::Symbol(text.clone()), 1))
                }
            }
            StxItem::NonReserved(text) => {
                valid_atom(text)?;
                Ok((Descr::NonReservedSymbol(text.clone(), false), 1))
            }
            StxItem::Unicode(text, ascii, preserve) => {
                valid_atom(text)?;
                valid_atom(ascii)?;
                Ok((
                    Descr::UnicodeSymbol(text.clone(), ascii.clone(), *preserve),
                    1,
                ))
            }
            StxItem::Cat(name, prec) => self.process_name(name, *prec, context),
            StxItem::Unary(alias, items) => {
                self.process_alias(alias, &[StxItem::Paren(items.clone())], trailing)
            }
            StxItem::Binary(alias, left, right) => self.process_alias(
                alias,
                &[StxItem::Paren(left.clone()), StxItem::Paren(right.clone())],
                trailing,
            ),
            StxItem::SepBy {
                items,
                separator,
                printed,
                trailing: allow_trailing,
                at_least_one,
            } => {
                let nested = context.nested();
                let item = ensure_unary(self.process_seq(items, &nested, trailing)?);
                let parser = match printed {
                    None => Descr::Symbol(separator.clone()),
                    Some(printed) => ensure_unary(self.process_seq(printed, &nested, trailing)?),
                };
                Ok((
                    Descr::SepBy {
                        item: Box::new(item),
                        separator: separator.clone(),
                        parser: Box::new(parser),
                        trailing: *allow_trailing,
                        at_least_one: *at_least_one,
                    },
                    1,
                ))
            }
            // The `stx` macros of `Init/Notation.lean`, expanded as `toParserDescr` expands them.
            StxItem::Postfix(postfix, operand) => {
                let operand = vec![operand.as_ref().clone()];
                let alias = |name: &str| Name::from_components([name]);
                let expanded = match postfix.as_str() {
                    "*" => StxItem::Unary(alias("many"), operand),
                    "+" => StxItem::Unary(alias("many1"), operand),
                    "?" => StxItem::Unary(alias("optional"), operand),
                    ",*" | ",+" | ",*,?" | ",+,?" => StxItem::SepBy {
                        items: operand,
                        separator: ",".to_string(),
                        printed: Some(vec![StxItem::Atom(", ".to_string())]),
                        trailing: postfix.ends_with(",?"),
                        at_least_one: postfix.starts_with(",+"),
                    },
                    _ => return Err("an unknown stx postfix"),
                };
                self.process(&expanded, context, trailing)
            }
            StxItem::OrElse(left, right) => self.process(
                &StxItem::Binary(
                    Name::from_components(["orelse"]),
                    vec![left.as_ref().clone()],
                    vec![right.as_ref().clone()],
                ),
                context,
                trailing,
            ),
            StxItem::Not(operand) => self.process(
                &StxItem::Unary(
                    Name::from_components(["notFollowedBy"]),
                    vec![operand.as_ref().clone()],
                ),
                context,
                trailing,
            ),
        }
    }

    /// `processNullaryOrCat`: a category, a syntax abbreviation, or an alias. A name that resolves to
    /// a hand-written `Parser` declaration (`ParserDescr.parser`) is not known here: the census
    /// records no such declarations, so one that shares an alias's name reads as the alias.
    fn process_name(
        &self,
        name: &Name,
        prec: Option<u32>,
        context: &Context,
    ) -> Result<(Descr, usize), &'static str> {
        if self.categories.contains_key(name) {
            if context.first && *name == context.category {
                return Err("left-recursive syntax the pin refuses");
            }
            return Ok((Descr::Cat(name.clone(), prec.unwrap_or(0)), 1));
        }
        if prec.is_some() {
            return Err("a precedence on a parser that is not a category");
        }
        // `resolveParserNameCore`: scope-aware declarations before aliases, which are global.
        if let Some(descr) = self.abbreviation(name) {
            return Ok((descr.clone(), 1));
        }
        if let Some(alias) = simple(name)
            && extension_census().aliases.contains_key(&alias)
        {
            return self.process_alias(name, &[], &mut None);
        }
        Err("a parser declaration that is neither a category, an alias nor a syntax abbreviation")
    }

    /// A syntax abbreviation `name` resolves to from the current namespace and `open`s.
    fn abbreviation(&self, name: &Name) -> Option<&Descr> {
        let top = self.top();
        let mut prefix = top.namespace.clone();
        loop {
            if let Some(descr) = self.abbreviations.get(&prefix.append_core(name)) {
                return Some(descr);
            }
            if prefix.is_anonymous() {
                break;
            }
            prefix = prefix.parent();
        }
        top.opens
            .iter()
            .rev()
            .find_map(|open| self.abbreviations.get(&open.append_core(name)))
    }

    /// `processAlias`.
    fn process_alias(
        &self,
        alias: &Name,
        args: &[StxItem],
        trailing: &mut Option<u32>,
    ) -> Result<(Descr, usize), &'static str> {
        let alias_name = simple(alias).ok_or("a dotted parser alias")?;
        let info = *extension_census()
            .aliases
            .get(&alias_name)
            .ok_or("an unknown parser alias")?;
        if info.arity != args.len() {
            return Err("a parser alias applied to the wrong number of arguments");
        }
        let nested = Context {
            category: Name::anonymous(),
            first: false,
            left_recursive: false,
            behavior: IdentBehavior::Default,
        };
        let mut processed = Vec::new();
        for arg in args {
            let (descr, stack) = self.process(arg, &nested, trailing)?;
            // `orelse` wraps a lone string in its own node (lean4#1275).
            let lone = match arg {
                StxItem::Paren(items) => match items.as_slice() {
                    [StxItem::Atom(text) | StxItem::NonReserved(text)] => Some(text.clone()),
                    _ => None,
                },
                _ => None,
            };
            match lone.filter(|_| alias_name == "orelse") {
                Some(text) => processed.push((
                    Descr::NodeWithAntiquot(
                        text.clone(),
                        Name::str(Name::from_components(["token"]), text),
                        Box::new(descr),
                    ),
                    1,
                )),
                None => processed.push((descr, stack)),
            }
        }
        let (args, stack): (Vec<Descr>, usize) = match info.stack {
            Some(stack) if info.auto_group => {
                (processed.into_iter().map(ensure_unary).collect(), stack)
            }
            Some(stack) => (
                processed.into_iter().map(|(descr, _)| descr).collect(),
                stack,
            ),
            None => {
                let stack = processed.iter().map(|(_, stack)| stack).sum();
                (
                    processed.into_iter().map(|(descr, _)| descr).collect(),
                    stack,
                )
            }
        };
        let mut args = args.into_iter();
        let descr = match (args.next(), args.next()) {
            (None, _) => Descr::Const(alias.clone()),
            (Some(only), None) => Descr::Unary(alias.clone(), Box::new(only)),
            (Some(left), Some(right)) => {
                Descr::Binary(alias.clone(), Box::new(left), Box::new(right))
            }
        };
        Ok((descr, stack))
    }
}

/// The expansion of a file's notations, shared by the [`FileGrammar`] and every
/// [`ActiveGrammar`] built from it, so a caller that only enters a grammar can expand too.
#[derive(Debug, Clone)]
pub struct Expander {
    rules: Arc<BTreeMap<Name, Arc<NotationRule>>>,
    expansions: Rc<Cell<u64>>,
    context: Name,
}

impl Expander {
    /// Expand every node of a notation this file declared, as its `macro_rules` would: the
    /// template with the node's children in place of its variables, and every other identifier
    /// of the template given a fresh macro scope (`Name.addMacroScope`), so it refers to what the
    /// declaration referred to rather than to a binder at the use. Notation inside an expansion
    /// is expanded too, to a bounded depth.
    pub fn expand(&self, syntax: &Syntax) -> Result<Syntax, &'static str> {
        if self.rules.is_empty() {
            return Ok(syntax.clone());
        }
        self.expand_at(syntax, 0)
    }

    fn expand_at(&self, syntax: &Syntax, depth: usize) -> Result<Syntax, &'static str> {
        if depth > MAX_EXPANSION_DEPTH {
            return Err("notation expands past the expansion depth");
        }
        // Children first, by an explicit stack: a term's depth is the user's.
        enum Task<'a> {
            Visit(&'a Syntax),
            Build(fln_syntax::source::SourceInfo, &'a Name, usize),
        }
        let mut tasks = vec![Task::Visit(syntax)];
        let mut built: Vec<Syntax> = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Syntax::Node { info, kind, args }) => {
                    tasks.push(Task::Build(*info, kind, args.len()));
                    tasks.extend(args.iter().rev().map(Task::Visit));
                }
                Task::Visit(leaf) => built.push(leaf.clone()),
                Task::Build(info, kind, count) => {
                    let args = built.split_off(built.len() - count);
                    let node = match self.rules.get(kind).cloned() {
                        Some(rule) => {
                            let expansion = self.instantiate(&rule, &args)?;
                            self.expand_at(&expansion, depth + 1)?
                        }
                        None => Syntax::Node {
                            info,
                            kind: kind.clone(),
                            args,
                        },
                    };
                    built.push(node);
                }
            }
        }
        built.pop().ok_or("an empty expansion")
    }

    /// One use of `rule`: its template with `args` (the node's children) in place of the
    /// variables, under a fresh macro scope.
    fn instantiate(&self, rule: &NotationRule, args: &[Syntax]) -> Result<Syntax, &'static str> {
        let scope = self.expansions.get() + 1;
        self.expansions.set(scope);
        let context = &self.context;
        let bound: BTreeMap<&Name, &Syntax> = rule
            .variables
            .iter()
            .map(|(position, name)| {
                args.get(*position)
                    .map(|child| (name, child))
                    .ok_or("a notation node without its operand")
            })
            .collect::<Result<_, _>>()?;
        let mut leaves = Vec::new();
        // Rebuild the template bottom-up with the substitutions applied.
        enum Step<'a> {
            Visit(&'a Syntax),
            Build(fln_syntax::source::SourceInfo, &'a Name, usize),
        }
        let mut steps = vec![Step::Visit(&rule.rhs)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(Syntax::Node { info, kind, args }) => {
                    steps.push(Step::Build(*info, kind, args.len()));
                    steps.extend(args.iter().rev().map(Step::Visit));
                }
                Step::Visit(Syntax::Ident { val, .. }) if bound.contains_key(val) => {
                    leaves.push(bound[val].clone());
                }
                // `hygieneInfo`'s anonymous identifier (a parenthesis's) takes no scope.
                Step::Visit(ident @ Syntax::Ident { val, .. }) if val.is_anonymous() => {
                    leaves.push(ident.clone());
                }
                Step::Visit(Syntax::Ident {
                    info,
                    raw_val,
                    val,
                    preresolved,
                }) => leaves.push(Syntax::Ident {
                    info: *info,
                    raw_val: *raw_val,
                    val: fln_syntax::hygiene::add_macro_scope(context, val, scope)
                        .map_err(|_| "a template name that cannot take a macro scope")?,
                    preresolved: preresolved.clone(),
                }),
                Step::Visit(leaf) => leaves.push(leaf.clone()),
                Step::Build(info, kind, count) => {
                    let args = leaves.split_off(leaves.len() - count);
                    leaves.push(Syntax::Node {
                        info,
                        kind: kind.clone(),
                        args,
                    });
                }
            }
        }
        leaves.pop().ok_or("an empty template")
    }
}

/// What a node of a notation the file declared expands to: `elabNotation`'s `macro_rules` (the
/// right-hand side, each variable standing for the child it binds), or for a mixfix command
/// `expandMixfix`'s notation (`f lhs rhs`, `f arg`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NotationRule {
    /// Child position, and the variable it binds.
    pub variables: Vec<(usize, Name)>,
    pub rhs: Syntax,
    /// Whether the pin prechecks the template's names where it is declared: a notation's are,
    /// a `macro`'s or `macro_rules`' are not (an unknown name is refused only where it is used).
    pub prechecked: bool,
}

/// Expansions nest no deeper: a notation whose template reaches itself is refused.
const MAX_EXPANSION_DEPTH: usize = 32;

/// `expandMixfix`'s operand names, hygienic in its quotation: they can meet no user name.
fn mixfix_variable(base: &str) -> Name {
    fln_syntax::hygiene::add_macro_scope(
        &Name::from_components(["Lean", "Elab", "Command", "expandMixfix"]),
        &Name::from_components([base]),
        1,
    )
    .expect("invariant: a plain name takes a macro scope")
}

/// `expandMacroArg`'s syntax for one argument (`Lean/Elab/MacroArgUtil.lean`): an unnamed
/// argument is wrapped in `group` to give it arity one (`noWs`, `optConfig`), unless it is a
/// string atom, a repetition, an option or a separated list (the postfix forms are macros for
/// those), or an interpolated string; `withPosition` is looked through.
fn macro_item(item: StxItem, named: bool) -> StxItem {
    match item {
        StxItem::Atom(_)
        | StxItem::NonReserved(_)
        | StxItem::SepBy { .. }
        | StxItem::Postfix(..) => item,
        StxItem::Unary(name, inner)
            if matches!(
                simple(&name).as_deref(),
                Some("optional" | "many" | "many1" | "interpolatedStr")
            ) =>
        {
            StxItem::Unary(name, inner)
        }
        StxItem::Unary(name, mut inner)
            if simple(&name).as_deref() == Some("withPosition") && inner.len() == 1 =>
        {
            let only = inner.remove(0);
            StxItem::Unary(name, vec![macro_item(only, named)])
        }
        item if named => item,
        item => StxItem::Unary(Name::from_components(["group"]), vec![item]),
    }
}

/// A `macro`'s or `macro_rules`' variable `x` (`$x` in its quotations), hygienic: it can meet no
/// name the template or the use writes.
fn macro_variable(base: &Name) -> Name {
    fln_syntax::hygiene::add_macro_scope(
        &Name::from_components(["Lean", "Elab", "Command", "elabMacro"]),
        base,
        1,
    )
    .unwrap_or_else(|_| base.clone())
}

/// The node a quotation pattern holds (`` `(k $x "a" $y) ``, `` `(tactic| k $x) ``): its kind,
/// the quotation's category, and its children.
fn quotation_root(pattern: &Syntax) -> Option<(Name, Name, &[Syntax])> {
    let category = if kind_is(pattern, &["Lean", "Parser", "Term", "quot"]) {
        "term"
    } else if kind_is(pattern, &["Lean", "Parser", "Tactic", "quot"]) {
        "tactic"
    } else {
        return None;
    };
    match node_args(pattern)? {
        [_, Syntax::Node { kind, args, .. }, _] => Some((
            kind.clone(),
            Name::from_components([category]),
            args.as_slice(),
        )),
        _ => None,
    }
}

/// The variable an antiquotation `$x` (any kind, named or not) binds; `None` for anything else
/// (a nested expression `$(e)`, an escaped `$$x`, a splice).
fn antiquotation_name(syntax: &Syntax) -> Option<Name> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return None;
    };
    if components(kind).last().map(String::as_str) != Some("antiquot") {
        return None;
    }
    match args.as_slice() {
        [Syntax::Atom { .. }, escapes, Syntax::Ident { val, .. }, _]
            if null_args(escapes).is_some_and(<[Syntax]>::is_empty) =>
        {
            Some(val.clone())
        }
        _ => None,
    }
}

/// A macro's template: the quotation of its category (`` `(…) `` for `term`, `` `(tactic| …) ``
/// for one tactic), its contents with each antiquotation `$x` the variable `x` binds. A
/// quotation of another category, a sequence of tactics, a nested quotation, an antiquotation of
/// no variable or of an expression, are not translated.
fn macro_template(
    rhs: &Syntax,
    category: &Name,
    variables: &[(usize, Name)],
) -> Result<Syntax, &'static str> {
    let quotation = match components(category).as_slice() {
        [term] if term == "term" => ["Lean", "Parser", "Term", "quot"],
        [tactic] if tactic == "tactic" => ["Lean", "Parser", "Tactic", "quot"],
        _ => return Err("a macro of a category other than term or tactic"),
    };
    if !kind_is(rhs, &quotation) {
        return Err("a macro whose right-hand side is not a quotation of its category");
    }
    let Some([_, contents, _]) = node_args(rhs) else {
        return Err("a quotation's shape");
    };
    let mut pending = vec![contents];
    let mut checked = 0_usize;
    while let Some(syntax) = pending.pop() {
        checked += 1;
        if checked > MAX_TEMPLATE_NODES {
            return Err("a macro template past the node budget");
        }
        if let Syntax::Node { kind, args, .. } = syntax {
            let leaf = components(kind).last().cloned().unwrap_or_default();
            if leaf == "antiquot" {
                let name = antiquotation_name(syntax).ok_or("an antiquotation of an expression")?;
                if !variables
                    .iter()
                    .any(|(_, variable)| *variable == macro_variable(&name))
                {
                    return Err("an antiquotation of no macro variable");
                }
                continue;
            }
            if leaf.contains("antiquot") || matches!(leaf.as_str(), "quot" | "quotSeq") {
                return Err("a splice or a nested quotation in a macro template");
            }
            pending.extend(args);
        }
    }
    Ok(replace_antiquotations(contents))
}

/// Template nodes [`macro_template`] walks before refusing.
const MAX_TEMPLATE_NODES: usize = 4096;

/// `contents` with each antiquotation replaced by its variable's identifier (bottom-up, by an
/// explicit stack).
fn replace_antiquotations(contents: &Syntax) -> Syntax {
    enum Step<'a> {
        Visit(&'a Syntax),
        Build(&'a Syntax, usize),
    }
    let mut steps = vec![Step::Visit(contents)];
    let mut built: Vec<Syntax> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(syntax) => match (antiquotation_name(syntax), syntax) {
                (Some(name), _) => built.push(synthetic_ident(macro_variable(&name))),
                (None, node @ Syntax::Node { args, .. }) => {
                    steps.push(Step::Build(node, args.len()));
                    steps.extend(args.iter().rev().map(Step::Visit));
                }
                (None, leaf) => built.push(leaf.clone()),
            },
            Step::Build(Syntax::Node { info, kind, .. }, count) => {
                let args = built.split_off(built.len() - count);
                built.push(Syntax::Node {
                    info: *info,
                    kind: kind.clone(),
                    args,
                });
            }
            Step::Build(leaf, _) => built.push(leaf.clone()),
        }
    }
    built.pop().unwrap_or(Syntax::Missing)
}

/// An identifier the template itself supplies: no source position of its own.
fn synthetic_ident(name: Name) -> Syntax {
    Syntax::Ident {
        info: fln_syntax::source::SourceInfo::None,
        raw_val: ByteSpan::empty_at(BytePos(0)),
        val: name,
        preresolved: Vec::new(),
    }
}

const MAX_PREC: u32 = 1024;
const LEAD_PREC: u32 = 1022;
const DEFAULT_PRIORITY: u32 = 1000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AttrKind {
    Global,
    Scoped,
    Local,
}

struct Declaration {
    attr_kind: AttrKind,
    precedence: Option<u32>,
    name: Option<Name>,
    priority: Option<u32>,
    items: Vec<StxItem>,
    category: Name,
}

/// `ToParserDescrContext`.
#[derive(Debug, Clone)]
struct Context {
    category: Name,
    first: bool,
    left_recursive: bool,
    behavior: IdentBehavior,
}

impl Context {
    /// `withNestedParser`.
    fn nested(&self) -> Context {
        Context {
            first: false,
            left_recursive: false,
            ..self.clone()
        }
    }
}

/// One item of a `syntax` command (category `stx`), as its tree spells it.
#[derive(Debug, Clone, PartialEq, Eq)]
enum StxItem {
    Atom(String),
    NonReserved(String),
    Unicode(String, String, bool),
    Cat(Name, Option<u32>),
    Paren(Vec<StxItem>),
    Unary(Name, Vec<StxItem>),
    Binary(Name, Vec<StxItem>, Vec<StxItem>),
    SepBy {
        items: Vec<StxItem>,
        separator: String,
        printed: Option<Vec<StxItem>>,
        trailing: bool,
        at_least_one: bool,
    },
    /// `p*`, `p+`, `p?`, `p,*`, `p,+`, `p,*,?`, `p,+,?`.
    Postfix(String, Box<StxItem>),
    OrElse(Box<StxItem>, Box<StxItem>),
    Not(Box<StxItem>),
}

fn private_name(module: &Name, name: &Name) -> Name {
    // `mkPrivateName`: `_private` ++ the module ++ `0` ++ the name.
    let header = Name::str(Name::anonymous(), "_private").append_core(module);
    Name::num(header, 0).append_core(name)
}

/// `mkParserSeq`: juxtaposition, left-nested.
fn parser_seq(parts: Vec<(Descr, usize)>) -> Result<(Descr, usize), &'static str> {
    let mut parts = parts.into_iter();
    let (mut descr, mut stack) = parts.next().ok_or("an empty syntax sequence")?;
    for (next, size) in parts {
        descr = Descr::Binary(
            Name::from_components(["andthen"]),
            Box::new(descr),
            Box::new(next),
        );
        stack += size;
    }
    Ok((descr, stack))
}

/// `ensureUnaryOutput`.
fn ensure_unary((descr, stack): (Descr, usize)) -> Descr {
    if stack == 1 {
        descr
    } else {
        Descr::Unary(Name::from_components(["group"]), Box::new(descr))
    }
}

/// `isValidAtom`.
fn valid_atom(text: &str) -> Result<(), &'static str> {
    let trimmed = text.trim_matches(|c: char| c.is_ascii_whitespace());
    let mut chars = trimmed.chars();
    let Some(first) = chars.next() else {
        return Err("an empty atom");
    };
    let second = chars.next();
    let valid = (first != '\'' || trimmed.starts_with("''"))
        && first != '"'
        && first != '«'
        && !(first == '`' && second.is_none_or(|c| fln_syntax::token::is_id_first(c) || c == '«'))
        && !first.is_ascii_digit()
        && !trimmed.chars().any(char::is_whitespace);
    if valid {
        Ok(())
    } else {
        Err("an atom the pin refuses")
    }
}

/// `isAtomLikeSyntax` over a sequence.
fn atom_like_seq(items: &[StxItem]) -> bool {
    match (items.first(), items.last()) {
        (Some(first), Some(last)) => atom_like(first) && atom_like(last),
        _ => false,
    }
}

fn atom_like(item: &StxItem) -> bool {
    match item {
        StxItem::Atom(_) => true,
        StxItem::Paren(items) => atom_like_seq(items),
        _ => false,
    }
}

/// `mkNameFromParserSyntax`'s visit, after the category's name: each string atom of the tree
/// trimmed, its whitespace made `_` and capitalized; each category `_`.
fn name_from_items(items: &[StxItem]) -> String {
    let mut out = String::new();
    for item in items {
        name_from_item(item, &mut out);
    }
    out
}

fn push_name_atom(text: &str, out: &mut String) {
    let trimmed = text.trim_matches(|c: char| c.is_ascii_whitespace());
    let mut chars = trimmed.chars();
    if let Some(first) = chars.next() {
        out.push(first.to_ascii_uppercase());
        out.extend(chars.map(|c| if c.is_whitespace() { '_' } else { c }));
    }
}

fn name_from_item(item: &StxItem, out: &mut String) {
    match item {
        StxItem::Atom(text) | StxItem::NonReserved(text) | StxItem::Unicode(text, _, _) => {
            push_name_atom(text, out);
        }
        StxItem::Cat(..) => out.push('_'),
        StxItem::Paren(items) | StxItem::Unary(_, items) => {
            items.iter().for_each(|item| name_from_item(item, out));
        }
        StxItem::Binary(_, left, right) => {
            left.iter()
                .chain(right)
                .for_each(|item| name_from_item(item, out));
        }
        // The tree's string children in order: the items, the separator literal, then the
        // printed separator's items.
        StxItem::SepBy {
            items,
            separator,
            printed,
            ..
        } => {
            items.iter().for_each(|item| name_from_item(item, out));
            push_name_atom(separator, out);
            printed
                .iter()
                .flatten()
                .for_each(|item| name_from_item(item, out));
        }
        StxItem::Postfix(_, operand) | StxItem::Not(operand) => name_from_item(operand, out),
        StxItem::OrElse(left, right) => {
            name_from_item(left, out);
            name_from_item(right, out);
        }
    }
}

fn null_args(syntax: &Syntax) -> Option<&[Syntax]> {
    match syntax {
        Syntax::Node { kind, args, .. } if components(kind) == ["null"] => Some(args),
        _ => None,
    }
}

/// Any node's children.
fn node_args(syntax: &Syntax) -> Option<&[Syntax]> {
    match syntax {
        Syntax::Node { args, .. } => Some(args),
        _ => None,
    }
}

fn kind_is(syntax: &Syntax, path: &[&str]) -> bool {
    matches!(syntax, Syntax::Node { kind, .. } if components(kind) == path)
}

fn ident_name(syntax: &Syntax) -> Option<Name> {
    match syntax {
        Syntax::Ident { val, .. } => Some(val.clone()),
        _ => None,
    }
}

/// A `str` node's value.
fn string_value(syntax: &Syntax) -> Option<String> {
    match syntax {
        Syntax::Node { kind, args, .. } if components(kind) == ["str"] => match args.as_slice() {
            [Syntax::Atom { val, .. }] => decode_string(val),
            _ => None,
        },
        _ => None,
    }
}

fn number_value(syntax: &Syntax) -> Option<u32> {
    match syntax {
        Syntax::Node { kind, args, .. } if components(kind) == ["num"] => match args.as_slice() {
            [Syntax::Atom { val, .. }] => val.parse().ok(),
            _ => None,
        },
        _ => None,
    }
}

fn attr_kind_of(syntax: &Syntax) -> Result<AttrKind, &'static str> {
    let Syntax::Node { args, .. } = syntax else {
        return Err("an attribute kind");
    };
    let [slot] = args.as_slice() else {
        return Err("an attribute kind");
    };
    match null_args(slot) {
        Some([]) => Ok(AttrKind::Global),
        Some([modifier]) if kind_is(modifier, &["Lean", "Parser", "Term", "scoped"]) => {
            Ok(AttrKind::Scoped)
        }
        Some([modifier]) if kind_is(modifier, &["Lean", "Parser", "Term", "local"]) => {
            Ok(AttrKind::Local)
        }
        _ => Err("an attribute kind"),
    }
}

/// `evalPrec` over the `prec` category's builtin forms.
fn prec_value(syntax: &Syntax) -> Option<u32> {
    if let Some(n) = number_value(syntax) {
        return Some(n);
    }
    let Syntax::Node { kind, args, .. } = syntax else {
        return None;
    };
    let path = components(kind);
    match path
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .as_slice()
    {
        ["precMax"] => Some(1024),
        ["precArg"] => Some(1023),
        ["precLead"] => Some(1022),
        ["precMin"] => Some(10),
        ["precMin1"] => Some(11),
        ["prec(_)"] => prec_value(args.get(1)?),
        ["Lean", "Parser", "Syntax", "addPrec"] => {
            prec_value(args.first()?)?.checked_add(prec_value(args.get(2)?)?)
        }
        ["Lean", "Parser", "Syntax", "subPrec"] => {
            Some(prec_value(args.first()?)?.saturating_sub(prec_value(args.get(2)?)?))
        }
        _ => None,
    }
}

/// `evalPrio` over the `prio` category's builtin forms.
fn prio_value(syntax: &Syntax) -> Option<u32> {
    if let Some(n) = number_value(syntax) {
        return Some(n);
    }
    let Syntax::Node { kind, args, .. } = syntax else {
        return None;
    };
    let path = components(kind);
    match path
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .as_slice()
    {
        ["prioDefault"] => Some(1000),
        ["prioLow"] => Some(100),
        ["prioMid"] => Some(500),
        ["prioHigh"] => Some(10000),
        ["Lean", "Parser", "Syntax", "addPrio"] => {
            prio_value(args.first()?)?.checked_add(prio_value(args.get(2)?)?)
        }
        ["Lean", "Parser", "Syntax", "subPrio"] => {
            Some(prio_value(args.first()?)?.saturating_sub(prio_value(args.get(2)?)?))
        }
        _ => None,
    }
}

/// A `precedence` node (`":" prec`).
fn precedence_value(syntax: &Syntax) -> Option<u32> {
    match syntax {
        Syntax::Node { args, .. } if kind_is(syntax, &["Lean", "Parser", "precedence"]) => {
            prec_value(args.get(1)?)
        }
        _ => None,
    }
}

/// `optPrecedence`: a null node holding a `precedence`, or nothing.
fn optional_precedence(syntax: &Syntax) -> Result<Option<u32>, &'static str> {
    match null_args(syntax) {
        Some([]) => Ok(None),
        Some([precedence]) => precedence_value(precedence)
            .map(Some)
            .ok_or("a precedence this does not evaluate"),
        _ => Err("an optional precedence"),
    }
}

/// `optNamedName` / `optNamedPrio`: `(name := x)` or `(priority := p)`, read by `value`.
fn named<T>(syntax: &Syntax, value: fn(&Syntax) -> Option<T>) -> Result<Option<T>, &'static str> {
    match null_args(syntax) {
        Some([]) => Ok(None),
        Some([Syntax::Node { args, .. }]) => match args.as_slice() {
            [_, _, _, found, _] => value(found).map(Some).ok_or("a named argument's value"),
            _ => Err("a named argument"),
        },
        _ => Err("a named argument"),
    }
}

/// One `stx` tree, as `syntax_decls` builds it.
fn stx_item(syntax: &Syntax) -> Result<StxItem, &'static str> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return Err("an stx item");
    };
    let path = components(kind);
    let path: Vec<&str> = path.iter().map(String::as_str).collect();
    let items = |syntax: &Syntax| -> Result<Vec<StxItem>, &'static str> {
        null_args(syntax)
            .ok_or("an stx sequence")?
            .iter()
            .map(stx_item)
            .collect()
    };
    Ok(match (path.as_slice(), args.as_slice()) {
        (["Lean", "Parser", "Syntax", "atom"], [string]) => {
            StxItem::Atom(string_value(string).ok_or("an atom's string")?)
        }
        (["Lean", "Parser", "Syntax", "nonReserved"], [_, string]) => {
            StxItem::NonReserved(string_value(string).ok_or("an atom's string")?)
        }
        (["Lean", "Parser", "Syntax", "unicodeAtom"], [_, text, _, ascii, preserve, _]) => {
            StxItem::Unicode(
                string_value(text).ok_or("a unicode atom")?,
                string_value(ascii).ok_or("a unicode atom")?,
                null_args(preserve).is_some_and(|args| !args.is_empty()),
            )
        }
        (["Lean", "Parser", "Syntax", "cat"], [name, precedence]) => StxItem::Cat(
            ident_name(name).ok_or("a parser name")?,
            optional_precedence(precedence)?,
        ),
        (["Lean", "Parser", "Syntax", "paren"], [_, inner, _]) => StxItem::Paren(items(inner)?),
        (["Lean", "Parser", "Syntax", "unary"], [name, _, inner, _]) => {
            StxItem::Unary(ident_name(name).ok_or("an alias name")?, items(inner)?)
        }
        (["Lean", "Parser", "Syntax", "binary"], [name, _, left, _, right, _]) => StxItem::Binary(
            ident_name(name).ok_or("an alias name")?,
            items(left)?,
            items(right)?,
        ),
        (
            ["Lean", "Parser", "Syntax", which @ ("sepBy" | "sepBy1")],
            [_, inner, _, separator, printed, trailing, _],
        ) => StxItem::SepBy {
            items: items(inner)?,
            separator: string_value(separator).ok_or("a separator")?,
            printed: match null_args(printed) {
                Some([]) => None,
                Some([_, sequence]) => Some(items(sequence)?),
                _ => return Err("a printed separator"),
            },
            trailing: null_args(trailing).is_some_and(|args| !args.is_empty()),
            at_least_one: *which == "sepBy1",
        },
        ([postfix], [operand, _]) if postfix.starts_with("stx_") && *postfix != "stx_<|>_" => {
            StxItem::Postfix(
                postfix["stx_".len()..].to_string(),
                Box::new(stx_item(operand)?),
            )
        }
        (["stx_<|>_"], [left, _, right]) => {
            StxItem::OrElse(Box::new(stx_item(left)?), Box::new(stx_item(right)?))
        }
        (["stx!_"], [_, operand]) => StxItem::Not(Box::new(stx_item(operand)?)),
        _ => return Err("an stx item this does not translate"),
    })
}

/// `expandNotationItemIntoSyntaxItem`: an identifier becomes `term` at its precedence.
fn notation_item(syntax: &Syntax) -> Result<StxItem, &'static str> {
    if let Some(text) = string_value(syntax) {
        return Ok(StxItem::Atom(text));
    }
    match syntax {
        Syntax::Node { args, .. }
            if kind_is(syntax, &["Lean", "Parser", "Command", "identPrec"]) =>
        {
            let [_, precedence] = args.as_slice() else {
                return Err("a notation item");
            };
            Ok(StxItem::Cat(
                Name::from_components(["term"]),
                optional_precedence(precedence)?,
            ))
        }
        _ if kind_is(syntax, &["Lean", "Parser", "Syntax", "unicodeAtom"]) => stx_item(syntax),
        _ => Err("a notation item"),
    }
}

thread_local! {
    static ACTIVE: RefCell<Vec<Rc<ActiveGrammar>>> = const { RefCell::new(Vec::new()) };
}

struct Entered;

impl Drop for Entered {
    fn drop(&mut self) {
        ACTIVE.with(|active| active.borrow_mut().pop());
    }
}

/// Run `parse` with `grammar` in effect: the lexer uses its table and the parser consults its
/// declarations.
pub fn with_grammar<R>(grammar: &Rc<ActiveGrammar>, parse: impl FnOnce() -> R) -> R {
    ACTIVE.with(|active| active.borrow_mut().push(Rc::clone(grammar)));
    let _entered = Entered;
    parse()
}

fn active() -> Option<Rc<ActiveGrammar>> {
    ACTIVE.with(|active| active.borrow().last().cloned())
}

/// Call `lex` with the token table in effect: the active grammar's, or production's.
pub(crate) fn with_token_table<R>(lex: impl FnOnce(&TokenTable) -> R) -> R {
    match active() {
        Some(grammar) => lex(&grammar.table),
        None => lex(production_table()),
    }
}

/// `interpolatedStrFn` (`Lean/Parser/Basic.lean`) for the active grammar: the string after an
/// interpolation head (`s!`) is not one string literal but chunks (`"a{`, `}b{`, `}"`, each a
/// string-literal token here) around terms lexed with the table, each term ending at the `}` that
/// closes its brace. The plain lexer read such a string as one literal, or, with a `"` inside a
/// hole, as several, so the run is re-lexed from the string on. A string this cannot read (no
/// closing quote, a refused token in a hole) is left as the plain lexer read it.
pub(crate) fn interpolate(text: &SourceText, table: &TokenTable, run: LexRun) -> LexRun {
    let Some(grammar) = active() else {
        return run;
    };
    if grammar.interpolated.is_empty() {
        return run;
    }
    let mut events = Vec::with_capacity(run.events.len());
    let mut pending = run.events;
    let mut index = 0;
    while index < pending.len() {
        let event = pending[index].clone();
        index += 1;
        let head = matches!(&event, Event::Token(LexedToken { kind: TokenKind::Symbol(symbol), .. })
            if grammar.interpolated.contains(symbol.as_str()));
        events.push(event);
        if !head {
            continue;
        }
        // Trivia, then the string the head reads.
        let mut next = index;
        while matches!(pending.get(next), Some(Event::Trivia(_))) {
            next += 1;
        }
        // The plain lexer may have refused the string: an interpolated string's escapes
        // (`\{`) are no plain string's.
        let start = match pending.get(next) {
            Some(Event::Token(string)) => string.extent.start(),
            Some(Event::Refused { skipped, .. }) => skipped.start(),
            _ => continue,
        };
        if !text.as_str()[start.0..].starts_with('"') {
            continue;
        }
        let Some((chunks, end)) = interpolated_string(text, table, start) else {
            continue;
        };
        events.extend(pending[index..next].iter().cloned());
        events.extend(chunks);
        pending = lex_run_from(text, table, end).events;
        index = 0;
    }
    LexRun { events }
}

/// The events of one interpolated string at `start` (its opening quote), and where it ends.
fn interpolated_string(
    text: &SourceText,
    table: &TokenTable,
    start: BytePos,
) -> Option<(Vec<Event>, BytePos)> {
    let source = text.as_str();
    let chunk = |from: usize, to: usize| {
        ByteSpan::new(BytePos(from), BytePos(to)).map(|extent| {
            Event::Token(LexedToken {
                kind: TokenKind::Literal(LiteralKind::Str),
                extent,
            })
        })
    };
    let mut out = Vec::new();
    let mut chunk_start = start.0;
    let mut at = start.0 + 1;
    loop {
        let c = source[at..].chars().next()?;
        match c {
            '\\' => {
                at += 1;
                at += source[at..].chars().next()?.len_utf8();
            }
            '"' => {
                out.push(chunk(chunk_start, at + 1)?);
                return Some((out, BytePos(at + 1)));
            }
            '{' => {
                out.push(chunk(chunk_start, at + 1)?);
                let mut depth = 0usize;
                let mut close = None;
                // An interpolated string inside the hole (`{… s!"x{i}" …}`) is read as one too;
                // its chunks are literals, so the braces counted here stay the hole's.
                for event in
                    interpolate(text, table, lex_run_from(text, table, BytePos(at + 1))).events
                {
                    match &event {
                        Event::Refused { .. } => return None,
                        Event::Token(LexedToken {
                            kind: TokenKind::Symbol(symbol),
                            extent,
                        }) if symbol == "}" => {
                            if depth == 0 {
                                close = Some(extent.start().0);
                                break;
                            }
                            depth -= 1;
                        }
                        Event::Token(LexedToken {
                            kind: TokenKind::Symbol(symbol),
                            ..
                        }) if symbol == "{" => depth += 1,
                        _ => {}
                    }
                    out.push(event);
                }
                chunk_start = close?;
                at = chunk_start + 1;
            }
            c => at += c.len_utf8(),
        }
    }
}

/// Expand the notations of the entered grammar's file in `syntax` ([`Expander::expand`]):
/// `None` when no grammar is entered or its file declared none, so the caller keeps its tree.
pub fn expand_active(syntax: &Syntax) -> Result<Option<Syntax>, &'static str> {
    let Some(grammar) = active() else {
        return Ok(None);
    };
    match &grammar.expander {
        Some(expander) if !expander.rules.is_empty() => expander.expand(syntax).map(Some),
        _ => Ok(None),
    }
}

/// The active infix declarations spelled `symbol`.
pub(crate) fn infix(symbol: &str) -> Option<ExtensionInfix> {
    active()?.infix.get(symbol).copied()
}

/// The node an [`ExtensionInfix`] of the active grammar builds over its operands: its kind's, or
/// the `choice` of each active declaration's.
pub(crate) fn infix_node(
    operator: ExtensionInfix,
    left: Syntax,
    atom: Syntax,
    right: Syntax,
) -> Syntax {
    let grammar =
        active().expect("invariant: an extension operator is built and reduced under one grammar");
    let kinds = &grammar.infix_kinds[operator.id as usize];
    let args = vec![left, atom, right];
    match kinds.as_slice() {
        [kind] => Syntax::node(kind.clone(), args),
        _ => Syntax::node(
            Name::from_components(["choice"]),
            kinds
                .iter()
                .map(|kind| Syntax::node(kind.clone(), args.clone()))
                .collect(),
        ),
    }
}

/// A tactic whose first token names an active `tactic` declaration: `None` when none does,
/// otherwise the one declaration that reads exactly `range`.
pub(crate) fn tactic(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Option<Syntax> {
    let grammar = active()?;
    let head = token_text(tokens.get(range.start)?)?;
    let candidates = grammar.tactics.get(head.as_str())?;
    let run = Run {
        leaves,
        view,
        tokens,
    };
    let mut parsed = None;
    for &index in candidates {
        let descr = &grammar.decls[index].descr;
        if let Some((items, end)) = run.parse(descr, range.start, range.end, &Follow::End, 0)
            && end == range.end
            && let [syntax] = items.as_slice()
        {
            if parsed.is_some() {
                // Two parsers read the same input: the pin's `choice` node, not built here.
                return None;
            }
            parsed = Some(syntax.clone());
        }
    }
    parsed
}

/// An atom-like `term` notation of the active grammar at `index`, read up to `end` at most: its
/// node and the index after it. The longest reading wins, as `longestMatchFn` picks; two of the
/// same length are the pin's `choice`, not built here.
pub(crate) fn leading_term(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    index: usize,
    end: usize,
) -> Option<(Syntax, usize)> {
    let grammar = active()?;
    let head = token_text(tokens.get(index)?)?;
    let candidates = grammar.terms.get(head.as_str())?;
    let run = Run {
        leaves,
        view,
        tokens,
    };
    let mut parsed: Option<(Syntax, usize)> = None;
    let mut tied = false;
    for &candidate in candidates {
        let descr = &grammar.decls[candidate].descr;
        let Some((items, next)) = run.parse(descr, index, end, &Follow::End, 0) else {
            continue;
        };
        let [syntax] = items.as_slice() else {
            continue;
        };
        match &parsed {
            Some((_, longest)) if *longest > next => {}
            Some((_, longest)) if *longest == next => tied = true,
            _ => {
                parsed = Some((syntax.clone(), next));
                tied = false;
            }
        }
    }
    if tied { None } else { parsed }
}

/// The prefix notation of the active grammar spelled `symbol`: its kind and the precedence its
/// operand is read at.
pub(crate) fn prefix(symbol: &str) -> Option<(Name, u8)> {
    active()?.prefixes.get(symbol).cloned()
}

/// The `attr` syntax the census declares for an attribute named `head`, under a grammar that
/// enters the imports' syntax: `Some(true)` when the file has it, `Some(false)` when an import it
/// lacks declares it (`@[simp]` in `Init.Prelude`, before `Init.Tactics`), where the pin reads the
/// attribute as `Attr.simple`; `None` when no such grammar is entered or the census declares no
/// such attribute (a builtin parser's, such as `instance`).
pub(crate) fn attribute_syntax(head: &str) -> Option<bool> {
    static HEADS: OnceLock<BTreeSet<String>> = OnceLock::new();
    let grammar = active().filter(|grammar| grammar.imports_entered)?;
    if grammar.attrs.contains_key(head) {
        return Some(true);
    }
    let attr = Name::from_components(["attr"]);
    HEADS
        .get_or_init(|| {
            extension_census()
                .decls
                .iter()
                .filter(|decl| decl.leading && decl.category.as_ref() == Some(&attr))
                .flat_map(|decl| heads(&decl.descr, 0))
                .collect()
        })
        .contains(head)
        .then_some(false)
}

/// Whether `symbol` begins a `command` declaration of the active grammar (`norm_cast_add_elim`):
/// a line it starts starts a command.
pub(crate) fn is_command_keyword(symbol: &str) -> bool {
    active().is_some_and(|grammar| grammar.commands.contains_key(symbol))
}

/// The command in `range` read by the active `command` declaration its first token names (`seal`,
/// `declare_simp_like_tactic`): `None` unless exactly one such declaration reads exactly `range`.
pub(crate) fn command(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Option<Syntax> {
    let grammar = active()?;
    let head = token_text(tokens.get(range.start)?)?;
    let run = Run {
        leaves,
        view,
        tokens,
    };
    let mut parsed = None;
    for &index in grammar.commands.get(head.as_str())? {
        if let Some((items, end)) = run.parse(
            &grammar.decls[index].descr,
            range.start,
            range.end,
            &Follow::End,
            0,
        ) && end == range.end
            && let [syntax] = items.as_slice()
        {
            if parsed.is_some() {
                return None;
            }
            parsed = Some(syntax.clone());
        }
    }
    parsed
}

/// The attribute in `range` read by the active `attr` declaration its first token names: `None`
/// unless exactly one such declaration reads exactly `range`.
pub(crate) fn attribute(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Option<Syntax> {
    let grammar = active()?;
    let head = token_text(tokens.get(range.start)?)?;
    let run = Run {
        leaves,
        view,
        tokens,
    };
    let mut parsed = None;
    for &index in grammar.attrs.get(head.as_str())? {
        if let Some((items, end)) = run.parse(
            &grammar.decls[index].descr,
            range.start,
            range.end,
            &Follow::End,
            0,
        ) && end == range.end
            && let [syntax] = items.as_slice()
        {
            if parsed.is_some() {
                return None;
            }
            parsed = Some(syntax.clone());
        }
    }
    parsed
}

/// Whether `kind`, a term notation of the active grammar, may stand as an application's argument:
/// its node is at `arg` precedence or above. `syntax "dbl " term:max : term` is at `lead`, so
/// `f dbl x` is no application at the pin.
pub(crate) fn is_argument_notation(kind: &Name) -> bool {
    active().is_some_and(|grammar| {
        grammar.terms.values().flatten().any(|&index| {
            matches!(&grammar.decls[index].descr,
                Descr::Node { kind: declared, prec, .. } if declared == kind && *prec >= 1023)
        })
    })
}

/// Whether a declaration of the active grammar builds `kind`.
pub(crate) fn is_active_kind(kind: &Name) -> bool {
    active().is_some_and(|grammar| grammar.kinds.contains(kind))
}

/// Whether `kind` is an atom-like notation of the active grammar at `max` precedence, so its node
/// can head an application.
pub(crate) fn is_max_prec_notation(kind: &Name) -> bool {
    active().is_some_and(|grammar| {
        grammar.terms.values().flatten().any(|&index| {
            matches!(&grammar.decls[index].descr,
                Descr::Node { kind: declared, prec, .. } if declared == kind && *prec >= MAX_PREC)
        })
    })
}

fn token_text(token: &LexedToken) -> Option<String> {
    match &token.kind {
        TokenKind::Symbol(symbol) => Some(symbol.clone()),
        TokenKind::Ident(name) => Some(name.to_display_string()),
        TokenKind::Literal(_) => None,
    }
}

/// What may follow the parser being run, which is how a `term` inside a description finds its
/// end: the texts that stop it at depth zero (and whether the enclosing range's end may come
/// first), the end of the enclosing range, or nothing this module can bound a term by.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Follow {
    End,
    Texts(BTreeSet<String>, bool),
    Unknown,
}

impl Follow {
    /// `self` followed by what may follow the whole sequence.
    fn then(self, outer: &Follow) -> Follow {
        match self {
            Follow::Texts(texts, false) => Follow::Texts(texts, false),
            Follow::Texts(mut texts, true) => match outer {
                Follow::End => Follow::Texts(texts, true),
                Follow::Texts(more, at_end) => {
                    texts.extend(more.iter().cloned());
                    Follow::Texts(texts, *at_end)
                }
                Follow::Unknown => Follow::Unknown,
            },
            Follow::End => outer.clone(),
            Follow::Unknown => Follow::Unknown,
        }
    }
}

const OPENERS: [&str; 7] = ["(", "[", "{", "⟨", "⦃", "#[", "%["];
const CLOSERS: [&str; 5] = [")", "]", "}", "⟩", "⦄"];

struct Run<'a> {
    leaves: &'a Leaves,
    view: &'a SourceView,
    tokens: &'a [LexedToken],
}

type Parsed = Option<(Vec<Syntax>, usize)>;

/// Aliases that read no input and always succeed: formatting hints, and the column checks
/// (`colGt`, `colGe`, `colEq`), which are not evaluated because the enclosing tactic's extent,
/// fixed by the sequence splitter from the same columns, bounds what follows them.
fn no_input(alias: &str) -> bool {
    matches!(
        alias,
        "ppSpace"
            | "ppLine"
            | "ppHardSpace"
            | "ppAllowUngrouped"
            | "ppHardLineUnlessUngrouped"
            | "colGt"
            | "colGe"
            | "colEq"
    )
}

impl Run<'_> {
    fn text(&self, at: usize) -> Option<String> {
        self.tokens.get(at).and_then(token_text)
    }

    fn atom(&self, at: usize, val: &str) -> Option<Syntax> {
        let info = self.leaves.leaf(at).ok()?.info();
        Some(Syntax::Atom {
            info,
            val: val.to_string(),
        })
    }

    /// The texts `descr` can start with, and whether it can read nothing.
    fn first(&self, descr: &Descr, depth: usize) -> Follow {
        if depth > MAX_DESCR_DEPTH {
            return Follow::Unknown;
        }
        let texts = |items: &[&str], nullable| {
            Follow::Texts(
                items.iter().map(|s| s.trim().to_string()).collect(),
                nullable,
            )
        };
        match descr {
            Descr::Symbol(text) | Descr::NonReservedSymbol(text, _) => texts(&[text], false),
            Descr::UnicodeSymbol(text, ascii, _) => texts(&[text, ascii], false),
            Descr::Const(name) => match simple(name).as_deref() {
                Some(alias) if no_input(alias) || alias == "noWs" => Follow::End,
                _ => Follow::Unknown,
            },
            Descr::Node { body, .. } | Descr::NodeWithAntiquot(_, _, body) => {
                self.first(body, depth + 1)
            }
            Descr::Unary(name, body) => match simple(name).as_deref() {
                Some("optional" | "many") => match self.first(body, depth + 1) {
                    Follow::Texts(texts, _) => Follow::Texts(texts, true),
                    Follow::End => Follow::End,
                    Follow::Unknown => Follow::Unknown,
                },
                Some("notFollowedBy") => Follow::End,
                Some("many1" | "group") => self.first(body, depth + 1),
                _ if transparent(name) => self.first(body, depth + 1),
                _ => Follow::Unknown,
            },
            Descr::Binary(name, left, right) => match simple(name).as_deref() {
                Some("andthen") => self
                    .first(left, depth + 1)
                    .then(&self.first(right, depth + 1)),
                Some("orelse") => match (self.first(left, depth + 1), self.first(right, depth + 1))
                {
                    (Follow::Texts(mut a, x), Follow::Texts(b, y)) => {
                        a.extend(b);
                        Follow::Texts(a, x || y)
                    }
                    _ => Follow::Unknown,
                },
                _ => Follow::Unknown,
            },
            Descr::SepBy {
                item, at_least_one, ..
            } => match self.first(item, depth + 1) {
                Follow::Texts(texts, nullable) => Follow::Texts(texts, nullable || !at_least_one),
                other => other,
            },
            Descr::Cat(..) | Descr::Parser(_) | Descr::TrailingNode { .. } => Follow::Unknown,
        }
    }

    /// Where a term starting at `at` ends: at the first depth-zero token `follow` stops at,
    /// else at `end`; for a term at `max`/`arg` precedence, after one atom or bracket.
    fn term_end(&self, at: usize, end: usize, prec: u32, follow: &Follow) -> Option<usize> {
        if at >= end {
            return None;
        }
        if prec >= 1023 {
            // A literal (`21`, `"s"`) is one argument.
            let Some(opener) = self.text(at) else {
                return Some(at + 1);
            };
            // Inside a quotation an antiquotation (`$x`, `$x:k`, `$(e)`) is one argument.
            if opener == "$"
                && let Ok(Some((_, next))) = crate::quotations::antiquotation(
                    self.leaves,
                    self.view,
                    self.tokens,
                    at,
                    end,
                    crate::quotations::Position::Term,
                )
            {
                return Some(next);
            }
            if !OPENERS.contains(&opener.as_str()) {
                return Some(at + 1);
            }
            let mut depth = 0usize;
            for index in at..end {
                let text = self.text(index).unwrap_or_default();
                if OPENERS.contains(&text.as_str()) {
                    depth += 1;
                } else if CLOSERS.contains(&text.as_str()) {
                    depth -= 1;
                    if depth == 0 {
                        return Some(index + 1);
                    }
                }
            }
            return None;
        }
        let stops = match follow {
            Follow::End => None,
            Follow::Texts(texts, _) => Some(texts),
            Follow::Unknown => return None,
        };
        let mut depth = 0usize;
        for index in at..end {
            let text = self.text(index).unwrap_or_default();
            if depth == 0 && index > at && stops.is_some_and(|stops| stops.contains(&text)) {
                return Some(index);
            }
            if OPENERS.contains(&text.as_str()) {
                depth += 1;
            } else if CLOSERS.contains(&text.as_str()) {
                if depth == 0 {
                    return Some(index);
                }
                depth -= 1;
            }
        }
        Some(end)
    }

    fn parse(&self, descr: &Descr, at: usize, end: usize, follow: &Follow, depth: usize) -> Parsed {
        if depth > MAX_DESCR_DEPTH {
            return None;
        }
        match descr {
            Descr::Node { kind, body, .. } | Descr::NodeWithAntiquot(_, kind, body) => {
                let (items, next) = self.parse(body, at, end, follow, depth + 1)?;
                Some((vec![Syntax::node(kind.clone(), items)], next))
            }
            Descr::Symbol(text) | Descr::NonReservedSymbol(text, _) => {
                let text = text.trim();
                if at >= end || self.text(at)? != text {
                    return None;
                }
                Some((vec![self.atom(at, text)?], at + 1))
            }
            Descr::UnicodeSymbol(text, ascii, _) => {
                if at >= end {
                    return None;
                }
                let found = self.text(at)?;
                if found != text.trim() && found != ascii.trim() {
                    return None;
                }
                Some((vec![self.atom(at, &found)?], at + 1))
            }
            Descr::Const(name) => self.alias(name, at, end, follow),
            Descr::Unary(name, body) => self.unary(name, body, at, end, follow, depth),
            Descr::Binary(name, left, right) => match simple(name).as_deref() {
                Some("andthen") => {
                    let inner = self.first(right, depth + 1).then(follow);
                    let (mut items, middle) = self.parse(left, at, end, &inner, depth + 1)?;
                    let (more, next) = self.parse(right, middle, end, follow, depth + 1)?;
                    items.extend(more);
                    Some((items, next))
                }
                Some("orelse") => self
                    .parse(left, at, end, follow, depth + 1)
                    .or_else(|| self.parse(right, at, end, follow, depth + 1)),
                _ => None,
            },
            Descr::SepBy {
                item,
                parser,
                trailing,
                at_least_one,
                ..
            } => {
                let item_follow = self.first(parser, depth + 1).then(follow);
                let mut items = Vec::new();
                let mut next = at;
                loop {
                    let Some((parsed, after)) =
                        self.parse(item, next, end, &item_follow, depth + 1)
                    else {
                        if items.is_empty() || *trailing {
                            break;
                        }
                        return None;
                    };
                    items.extend(parsed);
                    next = after;
                    match self.parse(parser, next, end, follow, depth + 1) {
                        Some((separator, after)) if after > next => {
                            items.extend(separator);
                            next = after;
                        }
                        _ => break,
                    }
                }
                if items.is_empty() && *at_least_one {
                    return None;
                }
                Some((vec![null_node(items)], next))
            }
            Descr::Cat(category, prec) => {
                let stop = self.term_end(at, end, *prec, follow)?;
                let syntax = match simple(category).as_deref() {
                    Some("term") => {
                        let syntax = crate::bounded_term(
                            self.leaves,
                            self.view,
                            self.tokens,
                            at..stop,
                            DefinitionGrammar::Scalar,
                        )
                        .ok()?;
                        // `leadingNode` checks the category's requested minimum precedence.
                        // A one-token extension can fit `term_end` without meeting it; a
                        // parenthesized extension instead has the builtin parenthesis root.
                        if let Some(kind) = syntax.kind()
                            && active().is_some_and(|grammar| {
                                grammar.terms.values().flatten().any(|&index| {
                                    matches!(&grammar.decls[index].descr,
                                        Descr::Node { kind: declared, prec: node_prec, .. }
                                            if declared == kind && node_prec < prec)
                                })
                            })
                        {
                            return None;
                        }
                        syntax
                    }
                    Some("tactic") => {
                        crate::proofs::tactic(self.leaves, self.view, self.tokens, at..stop).ok()?
                    }
                    _ => return None,
                };
                Some((vec![syntax], stop))
            }
            Descr::Parser(_) | Descr::TrailingNode { .. } => None,
        }
    }

    fn unary(
        &self,
        name: &Name,
        body: &Descr,
        at: usize,
        end: usize,
        follow: &Follow,
        depth: usize,
    ) -> Parsed {
        match simple(name).as_deref() {
            Some("optional") => Some(match self.parse(body, at, end, follow, depth + 1) {
                Some((items, next)) => (vec![null_node(items)], next),
                None => (vec![null_node(Vec::new())], at),
            }),
            Some(alias @ ("many" | "many1")) => {
                let repeat = self.first(body, depth + 1).then(follow);
                let mut items = Vec::new();
                let mut next = at;
                let mut count = 0;
                while let Some((parsed, after)) = self.parse(body, next, end, &repeat, depth + 1) {
                    if after == next {
                        break;
                    }
                    items.extend(parsed);
                    next = after;
                    count += 1;
                }
                if alias == "many1" && count == 0 {
                    return None;
                }
                Some((vec![null_node(items)], next))
            }
            // `group(p) := node groupKind p`: a `group` node, not a null one.
            Some("group") => {
                let (items, next) = self.parse(body, at, end, follow, depth + 1)?;
                Some((
                    vec![Syntax::node(Name::from_components(["group"]), items)],
                    next,
                ))
            }
            Some("notFollowedBy") => match self.parse(body, at, end, &Follow::Unknown, depth + 1) {
                Some(_) => None,
                None => Some((Vec::new(), at)),
            },
            Some("interpolatedStr") => self.interpolated(body, at, end, depth),
            _ if transparent(name) => self.parse(body, at, end, follow, depth + 1),
            _ => None,
        }
    }

    /// `interpolatedStr(p)` over the chunks [`interpolate`] made: `interpolatedStrKind` holding
    /// each chunk as an `interpolatedStrLitKind` and each hole as `p`.
    fn interpolated(&self, body: &Descr, at: usize, end: usize, depth: usize) -> Parsed {
        let chunk = |index: usize| {
            matches!(
                self.tokens.get(index).map(|token| &token.kind),
                Some(TokenKind::Literal(LiteralKind::Str))
            ) && index < end
        };
        let source = self.view.normalized().as_str();
        let spelling = |index: usize| {
            let extent = self.tokens[index].extent;
            &source[extent.start().0..extent.end().0]
        };
        if !chunk(at) || !spelling(at).starts_with('"') {
            return None;
        }
        let literal = |index: usize| -> Option<Syntax> {
            Some(Syntax::node(
                Name::from_components(["interpolatedStrLitKind"]),
                vec![self.leaves.leaf(index).ok()?],
            ))
        };
        let mut items = vec![literal(at)?];
        let mut next = at;
        // A chunk ends at an unescaped `{` (a hole follows) or at the closing quote.
        while spelling(next).ends_with('{') {
            // The hole ends at the first chunk that continues this string, past any interpolated
            // string nested in the hole (its own chunks open with `"…{` and close with `}…"`).
            let mut nested = 0usize;
            let close = (next + 1..end).find(|&index| {
                if !chunk(index) {
                    return false;
                }
                let text = spelling(index);
                if text.starts_with('"') {
                    // A chunk ends only at an unescaped `{`.
                    nested += usize::from(text.ends_with('{'));
                    return false;
                }
                if !text.starts_with('}') {
                    return false;
                }
                if nested == 0 {
                    return true;
                }
                if text.ends_with('"') {
                    nested -= 1;
                }
                false
            })?;
            let (hole, after) = self.parse(body, next + 1, close, &Follow::End, depth + 1)?;
            if after != close {
                return None;
            }
            items.extend(hole);
            items.push(literal(close)?);
            next = close;
        }
        Some((
            vec![Syntax::node(
                Name::from_components(["interpolatedStrKind"]),
                items,
            )],
            next + 1,
        ))
    }

    fn alias(&self, name: &Name, at: usize, end: usize, follow: &Follow) -> Parsed {
        let alias = simple(name)?;
        if no_input(&alias) {
            return Some((Vec::new(), at));
        }
        if alias == "noWs" {
            // `checkNoWsBefore`: the previous token ends where this one starts.
            let joined = at > 0
                && at < self.tokens.len()
                && self.tokens[at - 1].extent.end() == self.tokens[at].extent.start();
            return joined.then(|| (Vec::new(), at));
        }
        if at >= end {
            return None;
        }
        let token = &self.tokens[at];
        match (alias.as_str(), &token.kind) {
            ("ident", TokenKind::Ident(_)) => Some((vec![self.leaves.leaf(at).ok()?], at + 1)),
            ("num", TokenKind::Literal(LiteralKind::Nat)) => Some((
                vec![Syntax::node(
                    Name::str(Name::anonymous(), "num"),
                    vec![self.leaves.leaf(at).ok()?],
                )],
                at + 1,
            )),
            ("str", TokenKind::Literal(LiteralKind::Str)) => Some((
                vec![Syntax::node(
                    Name::str(Name::anonymous(), "str"),
                    vec![self.leaves.leaf(at).ok()?],
                )],
                at + 1,
            )),
            ("hole", TokenKind::Symbol(symbol)) if symbol == "_" => Some((
                vec![Syntax::node(
                    Name::from_components(["Lean", "Parser", "Term", "hole"]),
                    vec![self.atom(at, "_")?],
                )],
                at + 1,
            )),
            ("tacticSeq", _) => {
                let stop = self.term_end(at, end, 0, follow)?;
                let sequence =
                    crate::proofs::tactic_seq(self.leaves, self.view, self.tokens, at..stop)
                        .ok()?;
                Some((vec![sequence], stop))
            }
            _ => None,
        }
    }
}
