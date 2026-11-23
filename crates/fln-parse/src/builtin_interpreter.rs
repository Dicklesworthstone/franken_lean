//! Combinator AST interpreter over the pin-extracted builtin parser table
//! (Steps 2b & 3 of `fln-generated-builtin-grammar-spike-kcvj`, Rules D1/D5/D8).
//!
//! Compiles every zero-parameter generatable parser and helper in
//! [`crate::builtin_table::BuiltinParserTable`] into a flat executable
//! combinator IR, derives `FirstTokens` directly from the AST (matching
//! `Lean/Parser/Types.lean` and `Lean/Parser/Extension.lean:106-140`), builds
//! all 10 builtin syntax categories with their exact `LeadingIdentBehavior`,
//! and executes them against `fln-syntax`'s pin-faithful lexer and trivia
//! scanner with `withCache` memoization and bounded step fuel (`FL-INV-07`).

use crate::builtin_table::{
    BuiltinParserTable, CombinatorAst, GeneratableEntry, GeneratableRole,
    reference_builtin_parser_table,
};
use crate::category::LeadingIdentBehavior;
use crate::reference_tokens::{header_table, reference_census};
use fln_core::name::{LeafView, Name};
use fln_syntax::literal::LiteralKind;
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo, SourceText};
use fln_syntax::token::{TokenKind, TokenTable, lex_token};
use fln_syntax::tree::Syntax;
use fln_syntax::trivia::scan_trivia;
use fln_syntax::view::SourceView;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::{Arc, OnceLock};

mod descr;
mod vm;
pub(crate) use descr::ParserInput;
pub use descr::{ParserFailure, ParserResourceLimit};

const MAX_PREC: u32 = 1024;
const ARG_PREC: u32 = 1023;
const LEAD_PREC: u32 = 1022;
const MIN_PREC: u32 = 10;

/// Default step budget per top-level parse invocation (FL-INV-07).
pub const DEFAULT_STEP_BUDGET: usize = 50_000_000;

/// Default non-tail category recursion depth bound per parse invocation (FL-INV-07).
///
/// The execution VM (`vm.rs`) runs entirely on heap-allocated frames with O(1)
/// native stack usage, so deep legitimate syntax (thousands of nested terms)
/// completes on small threads while adversarial nesting still terminates with
/// a typed [`ParserResourceLimit::Depth`] stop.
pub const DEFAULT_MAX_DEPTH: usize = 16_384;

/// Default maximum materialized syntax tree node count per parse invocation (FL-INV-07).
///
/// Tracks the unfolded tree size of `VmNode` DAGs in O(1) per node construction so
/// exponentially ambiguous `choice` chains (`2^N` shared subtrees) hit a deterministic
/// `ParserResourceLimit::Steps` refusal in microseconds instead of expanding into
/// gigabytes during owned `Syntax` materialization.
pub const DEFAULT_MAX_TREE_NODES: usize = 1_000_000;

/// Error compiling a `BuiltinParserTable` into an executable interpreter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompileError {
    UnresolvedDecl(String),
    UnboundVar { owner: String, idx: usize },
    TypeMismatch { owner: String, detail: String },
    ArityMismatch { owner: String, func: String },
    DepthExceeded(String),
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnresolvedDecl(name) => write!(f, "unresolved parser declaration {name:?}"),
            Self::UnboundVar { owner, idx } => {
                write!(f, "unbound de Bruijn variable #{idx} in {owner:?}")
            }
            Self::TypeMismatch { owner, detail } => {
                write!(f, "combinator type mismatch in {owner:?}: {detail}")
            }
            Self::ArityMismatch { owner, func } => {
                write!(f, "arity mismatch calling {func:?} inside {owner:?}")
            }
            Self::DepthExceeded(owner) => {
                write!(f, "combinator specialization depth exceeded in {owner:?}")
            }
        }
    }
}

impl std::error::Error for CompileError {}

/// Upstream `Lean.Parser.FirstTokens` (`Types.lean:459-487`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FirstTokens {
    Epsilon,
    Unknown,
    Tokens(Vec<String>),
    OptTokens(Vec<String>),
}

impl FirstTokens {
    fn seq(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Epsilon, tks) => tks.clone(),
            (Self::OptTokens(s1), Self::OptTokens(s2)) => Self::OptTokens(concat_dedup(s1, s2)),
            (Self::OptTokens(s1), Self::Tokens(s2)) => Self::Tokens(concat_dedup(s1, s2)),
            (Self::OptTokens(_), Self::Unknown) => Self::Unknown,
            (tks, _) => tks.clone(),
        }
    }

    fn to_optional(&self) -> Self {
        match self {
            Self::Tokens(tks) => Self::OptTokens(tks.clone()),
            other => other.clone(),
        }
    }

    fn merge(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Epsilon, tks) | (tks, Self::Epsilon) => tks.to_optional(),
            (Self::Tokens(s1), Self::Tokens(s2)) => Self::Tokens(concat_dedup(s1, s2)),
            (Self::OptTokens(s1), Self::OptTokens(s2))
            | (Self::Tokens(s1), Self::OptTokens(s2))
            | (Self::OptTokens(s1), Self::Tokens(s2)) => Self::OptTokens(concat_dedup(s1, s2)),
            _ => Self::Unknown,
        }
    }

    fn indexed_tokens(&self) -> Option<&[String]> {
        match self {
            Self::Tokens(tks) | Self::OptTokens(tks) => Some(tks.as_slice()),
            Self::Epsilon | Self::Unknown => None,
        }
    }
}

fn concat_dedup(a: &[String], b: &[String]) -> Vec<String> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    for item in a.iter().chain(b.iter()) {
        if !out.contains(item) {
            out.push(item.clone());
        }
    }
    out
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SyntaxPred {
    IsIdent,
    IsIdentOrDotIdentOrProj,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OrElseAntiquotBehavior {
    AcceptLhs,
    TakeLongest,
    Merge,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ContextTransform {
    WithoutPosition,
    WithForbidden(String),
    WithoutForbidden,
    SuppressInsideQuot,
    AddQuotDepth(i32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CharPred {
    IsWhitespace,
    WhitespaceOrDelim,
    WhitespaceOrChars(Vec<char>),
}

impl CharPred {
    fn matches(&self, ch: char) -> bool {
        match self {
            Self::IsWhitespace => is_lean_whitespace(ch),
            Self::WhitespaceOrDelim => {
                is_lean_whitespace(ch) || matches!(ch, '(' | ')' | ':' | '{' | '}' | '|')
            }
            Self::WhitespaceOrChars(chars) => is_lean_whitespace(ch) || chars.contains(&ch),
        }
    }
}

/// Executable combinator IR node produced by evaluating a `CombinatorAst` definition.
#[derive(Debug, Clone)]
enum ParserOp {
    /// Indirect call to a compiled zero-arg generatable definition by index.
    Ref(usize),
    Skip,
    PushNone,
    Eoi,
    Symbol(String),
    NonReservedSymbol {
        sym: String,
        include_ident: bool,
    },
    UnicodeSymbol {
        sym: String,
        ascii_sym: String,
    },
    RawCh {
        ch: char,
        trailing_ws: bool,
    },
    Ident,
    RawIdent,
    NumLit,
    HexNum,
    ScientificLit,
    StrLit,
    CharLit,
    NameLit,
    FieldIdx,
    HygieneInfo,
    CommentBody,
    VersoCommentBody,
    IfVerso {
        module_docs: bool,
        verso: Arc<ParserOp>,
        plain: Arc<ParserOp>,
    },
    WithoutVersoSyntax(Arc<ParserOp>),
    InterpolatedStr(Arc<ParserOp>),
    Seq(Vec<Arc<ParserOp>>),
    OrElse(Vec<Arc<ParserOp>>),
    Node(Name, Arc<ParserOp>),
    TrailingNodeAux(Name, Arc<ParserOp>),
    Atomic(Arc<ParserOp>),
    Optional(Arc<ParserOp>),
    Many(Arc<ParserOp>),
    Many1(Arc<ParserOp>),
    Many1Unbox(Arc<ParserOp>),
    SepBy {
        elem: Arc<ParserOp>,
        sep: Arc<ParserOp>,
        allow_trailing: bool,
    },
    SepBy1 {
        elem: Arc<ParserOp>,
        sep: Arc<ParserOp>,
        allow_trailing: bool,
    },
    Lookahead(Arc<ParserOp>),
    NotFollowedBy(Arc<ParserOp>, String),
    WithCache(Name, Arc<ParserOp>),
    WithResetCache(Arc<ParserOp>),
    WithAntiquot {
        antiquot: Arc<ParserOp>,
        body: Arc<ParserOp>,
        is_cat: bool,
    },
    TokenWithAntiquot(Arc<ParserOp>),
    WithAntiquotSuffixSplice {
        kind: Name,
        body: Arc<ParserOp>,
        suffix: Arc<ParserOp>,
    },
    WithoutInfo(Arc<ParserOp>),
    SetExpected {
        expected: Vec<String>,
        body: Arc<ParserOp>,
    },
    CheckPrec(u32),
    CheckLhsPrec(u32),
    SetLhsPrec(u32),
    CheckColEq(String),
    CheckColGe(String),
    CheckColGt(String),
    CheckLineEq(String),
    CheckWsBefore(String),
    CheckNoWsBefore(String),
    CheckLinebreakBefore(String),
    CheckNoImmediateColon,
    CheckStackTop {
        pred: SyntaxPred,
        msg: String,
    },
    WithPosition(Arc<ParserOp>),
    WithPositionAfterLinebreak(Arc<ParserOp>),
    AdaptContext(ContextTransform, Arc<ParserOp>),
    WithOpen(Arc<ParserOp>),
    WithOpenDecl(Arc<ParserOp>),
    CategoryParser {
        cat: Name,
        prec: u32,
    },
    ParserOfStack {
        offset: usize,
        prec: u32,
    },
    Recover {
        parser: Arc<ParserOp>,
        handler: Arc<ParserOp>,
    },
    SkipUntil(CharPred),
    ErrorAtSavedPos {
        msg: String,
        delta: bool,
    },
    InhabitedDefault,
}

#[derive(Debug, Clone)]
struct CompiledParser {
    op: Arc<ParserOp>,
    first_tokens: FirstTokens,
}

#[derive(Debug, Clone)]
struct CategoryDispatch {
    name: Name,
    behavior: LeadingIdentBehavior,
    leading_table: BTreeMap<Name, Vec<(usize, u32)>>,
    leading_unindexed: Vec<(usize, u32)>,
    trailing_table: BTreeMap<Name, Vec<(usize, u32)>>,
    trailing_unindexed: Vec<(usize, u32)>,
    antiquot_parser: Arc<ParserOp>,
}

/// Compiled builtin parser interpreter ready to parse headers, commands, or categories.
#[derive(Debug, Clone)]
pub struct BuiltinInterpreter {
    defs: Vec<CompiledParser>,
    def_index: BTreeMap<Name, usize>,
    categories: BTreeMap<Name, CategoryDispatch>,
    builtin_tokens: TokenTable,
    header_tokens: TokenTable,
    module_header_id: usize,
    command_eoi_kind: Name,
    command_exit_kind: Name,
    command_import_kind: Name,
    null_kind: Name,
    choice_kind: Name,
    ident_kind: Name,
    num_lit_kind: Name,
    scientific_lit_kind: Name,
    str_lit_kind: Name,
    char_lit_kind: Name,
    name_lit_kind: Name,
    hexnum_kind: Name,
    field_idx_kind: Name,
    hygiene_info_kind: Name,
    interpolated_str_kind: Name,
    interpolated_str_lit_kind: Name,
    token_antiquot_kind: Name,
    dot_ident_kind: Name,
    proj_kind: Name,
    antiquot_expr_op: Arc<ParserOp>,
}

/// Cached singleton interpreter built from the checked-in `BUILTIN_PARSER_TABLE`.
pub fn reference_builtin_interpreter() -> &'static BuiltinInterpreter {
    static INTERP: OnceLock<BuiltinInterpreter> = OnceLock::new();
    INTERP.get_or_init(|| {
        // Initialize on an explicit 8 MiB stack so tiny caller threads (e.g.,
        // 96 KiB heap-frame regression threads) never overflow during one-time
        // builtin-table compilation.
        std::thread::Builder::new()
            .name("fln-builtin-interp-init".to_owned())
            .stack_size(8 * 1024 * 1024)
            .spawn(|| {
                BuiltinInterpreter::from_table(reference_builtin_parser_table())
                    .expect("checked-in builtin parser table must compile into an interpreter")
            })
            .expect("failed to spawn builtin interpreter init thread")
            .join()
            .expect("builtin interpreter init thread panicked")
    })
}

/// One diagnostic error produced by the interpreter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterpError {
    pub pos: usize,
    pub unexpected: String,
    pub expected: Vec<String>,
    pub(crate) lexical_message: Option<&'static str>,
}

impl InterpError {
    fn new(pos: usize, unexpected: impl Into<String>, expected: Vec<String>) -> Self {
        Self {
            pos,
            unexpected: unexpected.into(),
            expected,
            lexical_message: None,
        }
    }

    fn lexical(pos: usize, message: &'static str, expected: Vec<String>) -> Self {
        Self {
            pos,
            unexpected: message.to_owned(),
            expected,
            lexical_message: Some(message),
        }
    }

    fn merge(&self, newer: &Self) -> Self {
        let unexpected = if newer.unexpected.is_empty() {
            self.unexpected.clone()
        } else {
            newer.unexpected.clone()
        };
        let mut expected = self.expected.clone();
        expected.extend(newer.expected.iter().cloned());
        Self {
            pos: newer.pos,
            unexpected,
            expected,
            lexical_message: newer.lexical_message.or(self.lexical_message),
        }
    }
}

/// Result of parsing a complete Lean file (header + command sequence) via the builtin table.
#[derive(Debug, Clone)]
pub struct ParsedModule {
    pub header: Syntax,
    pub commands: Vec<Syntax>,
    pub errors: Vec<InterpError>,
    pub steps_used: usize,
    /// A sticky step or recursion-depth stop. Recovery cannot clear it.
    pub budget_exhausted: bool,
}

/// Value domain used while partially evaluating `CombinatorAst` helpers into `ParserOp`.
#[derive(Clone)]
enum EvalVal {
    Parser(Arc<ParserOp>),
    Str(String),
    Nat(u64),
    Int(i64),
    Bool(bool),
    Char(char),
    Name(Name),
    List(Vec<EvalVal>),
    OptionSome,
    OptionNone,
    Unit,
    SyntaxPred(SyntaxPred),
    Closure {
        body: Box<CombinatorAst>,
        env: Vec<EvalVal>,
    },
}

impl BuiltinInterpreter {
    /// Compile a validated [`BuiltinParserTable`] into an executable interpreter.
    pub fn from_table(table: &BuiltinParserTable) -> Result<Self, CompileError> {
        // Assign deterministic indices to all parser-valued generatable entries (`ParserDef`).
        // Helper functions (including eta-reduced `Parser -> Parser` aliases like `ppDedent := id`)
        // are specialized at their call sites rather than compiled as standalone zero-arg parsers.
        let mut def_index = BTreeMap::new();
        let mut parser_entries: Vec<&GeneratableEntry> = Vec::new();
        for (name, entry) in &table.generatables {
            if entry.role == GeneratableRole::ParserDef && entry.params.is_empty() {
                let id = parser_entries.len();
                def_index.insert(name.clone(), id);
                parser_entries.push(entry);
            }
        }

        // Compile every parser-valued definition to `ParserOp`.
        let mut raw_ops: Vec<(Name, Arc<ParserOp>)> = Vec::with_capacity(parser_entries.len());
        for entry in &parser_entries {
            let mut env = Vec::new();
            let val = eval_ast(table, &def_index, &entry.name, &entry.ast, &mut env, 0)?;
            let op = expect_parser(&entry.name, val)?;
            raw_ops.push((entry.name.clone(), op));
        }

        // Compute `FirstTokens` for every compiled definition with cycle guard.
        let mut first_cache: Vec<Option<FirstTokens>> = vec![None; raw_ops.len()];
        let mut visiting: Vec<bool> = vec![false; raw_ops.len()];
        for id in 0..raw_ops.len() {
            if first_cache[id].is_none() {
                let ft = compute_def_first_tokens(id, &raw_ops, &mut first_cache, &mut visiting);
                first_cache[id] = Some(ft);
            }
        }

        let defs: Vec<CompiledParser> = raw_ops
            .into_iter()
            .zip(first_cache)
            .map(|((_name, op), ft)| CompiledParser {
                op,
                first_tokens: ft.unwrap_or(FirstTokens::Unknown),
            })
            .collect();

        // Build all 10 builtin categories with pin-exact `LeadingIdentBehavior`.
        let mut categories = BTreeMap::new();
        for (cat_name, cat_regs) in &table.categories {
            let behavior = builtin_category_behavior(cat_name);
            let mut leading_table: BTreeMap<Name, Vec<(usize, u32)>> = BTreeMap::new();
            let mut leading_unindexed: Vec<(usize, u32)> = Vec::new();
            let mut trailing_table: BTreeMap<Name, Vec<(usize, u32)>> = BTreeMap::new();
            let mut trailing_unindexed: Vec<(usize, u32)> = Vec::new();

            for entry in &cat_regs.leading {
                let Some(&def_id) = def_index.get(&entry.decl) else {
                    return Err(CompileError::UnresolvedDecl(entry.decl.to_display_string()));
                };
                match defs[def_id].first_tokens.indexed_tokens() {
                    Some(tks) => {
                        for tk in tks {
                            let key = Name::str(Name::anonymous(), tk);
                            leading_table
                                .entry(key)
                                .or_default()
                                .push((def_id, entry.priority));
                        }
                    }
                    None => leading_unindexed.push((def_id, entry.priority)),
                }
            }

            for entry in &cat_regs.trailing {
                let Some(&def_id) = def_index.get(&entry.decl) else {
                    return Err(CompileError::UnresolvedDecl(entry.decl.to_display_string()));
                };
                match defs[def_id].first_tokens.indexed_tokens() {
                    Some(tks) => {
                        for tk in tks {
                            let key = Name::str(Name::anonymous(), tk);
                            trailing_table
                                .entry(key)
                                .or_default()
                                .push((def_id, entry.priority));
                        }
                    }
                    None => trailing_unindexed.push((def_id, entry.priority)),
                }
            }

            let antiquot_parser = build_category_antiquot_parser(cat_name);
            categories.insert(
                cat_name.clone(),
                CategoryDispatch {
                    name: cat_name.clone(),
                    behavior,
                    leading_table,
                    leading_unindexed,
                    trailing_table,
                    trailing_unindexed,
                    antiquot_parser,
                },
            );
        }

        let module_header_name = Name::from_components(["Lean", "Parser", "Module", "header"]);
        let &module_header_id = def_index
            .get(&module_header_name)
            .ok_or_else(|| CompileError::UnresolvedDecl(module_header_name.to_display_string()))?;

        let census = reference_census();
        let builtin_tokens = TokenTable::from_tokens(census.builtin_tokens());
        let header_tokens = header_table().clone();

        let antiquot_expr_name = Name::from_components(["Lean", "Parser", "antiquotExpr"]);
        let antiquot_expr_op = match def_index.get(&antiquot_expr_name) {
            Some(&id) => Arc::new(ParserOp::Ref(id)),
            None => Arc::new(ParserOp::Ident),
        };

        Ok(Self {
            defs,
            def_index,
            categories,
            builtin_tokens,
            header_tokens,
            module_header_id,
            command_eoi_kind: Name::from_components(["Lean", "Parser", "Command", "eoi"]),
            command_exit_kind: Name::from_components(["Lean", "Parser", "Command", "exit"]),
            command_import_kind: Name::from_components(["Lean", "Parser", "Command", "import"]),
            null_kind: Name::from_components(["null"]),
            choice_kind: Name::from_components(["choice"]),
            ident_kind: Name::from_components(["ident"]),
            num_lit_kind: Name::from_components(["num"]),
            scientific_lit_kind: Name::from_components(["scientific"]),
            str_lit_kind: Name::from_components(["str"]),
            char_lit_kind: Name::from_components(["char"]),
            name_lit_kind: Name::from_components(["name"]),
            hexnum_kind: Name::from_components(["hexnum"]),
            field_idx_kind: Name::from_components(["fieldIdx"]),
            hygiene_info_kind: Name::from_components(["hygieneInfo"]),
            interpolated_str_kind: Name::from_components(["interpolatedStrKind"]),
            interpolated_str_lit_kind: Name::from_components(["interpolatedStrLitKind"]),
            token_antiquot_kind: Name::from_components(["token_antiquot"]),
            dot_ident_kind: Name::from_components(["Lean", "Parser", "Term", "dotIdent"]),
            proj_kind: Name::from_components(["Lean", "Parser", "Term", "proj"]),
            antiquot_expr_op,
        })
    }

    /// Number of compiled zero-arg builtin parser definitions.
    pub fn def_count(&self) -> usize {
        self.defs.len()
    }

    /// Number of compiled syntax categories.
    pub fn category_count(&self) -> usize {
        self.categories.len()
    }

    /// Inspect the computed `FirstTokens` of a compiled parser definition.
    pub fn first_tokens_of(&self, name: &Name) -> Option<&FirstTokens> {
        self.def_index
            .get(name)
            .map(|&id| &self.defs[id].first_tokens)
    }

    /// Inspect category dispatch summary: `(indexed_leading_keys, unindexed_leading, indexed_trailing_keys, unindexed_trailing)`.
    pub fn category_summary(&self, cat: &Name) -> Option<(usize, usize, usize, usize)> {
        self.categories.get(cat).map(|c| {
            (
                c.leading_table.len(),
                c.leading_unindexed.len(),
                c.trailing_table.len(),
                c.trailing_unindexed.len(),
            )
        })
    }

    /// Parse a single input string in a given builtin category (e.g., `"term"`, `"command"`, `"level"`).
    pub fn parse_category(
        &self,
        cat: &str,
        source: &SourceText,
        max_steps: usize,
    ) -> Result<Syntax, InterpError> {
        let mut st = RuntimeState::new(source, false, max_steps);
        st.skip_whitespace();
        if let Some(err) = st.error.take() {
            return Err(err);
        }
        let cat_name = Name::from_components([cat]);
        let op = ParserOp::CategoryParser {
            cat: cat_name,
            prec: 0,
        };
        self.exec_op(&op, &mut st);
        if let Some(error) = st.resource_error() {
            return Err(error);
        }
        if let Some(error) = st.recovered_errors.first() {
            return Err(error.clone());
        }
        if let Some(err) = st.error {
            return Err(err);
        }
        if st.pos < source.len_bytes() {
            return Err(InterpError::new(
                st.pos,
                String::new(),
                vec!["end of input".to_owned()],
            ));
        }
        Ok(st.pop_or_missing().to_syntax())
    }

    /// Parse one complete top-level command through the unified registry engine,
    /// enforcing full-buffer consumption, lossless trivia tiling, CRLF-mapped
    /// error positions, and sticky `FL-INV-07` resource/recovery diagnostics.
    pub fn parse_single_command(
        &self,
        view: &SourceView,
        docs: crate::extensions::DocOptions,
        max_steps: usize,
    ) -> Result<(Syntax, ByteSpan, usize), crate::NatDefinitionParseError> {
        let source = view.normalized();
        if max_steps == 0 {
            return Err(crate::NatDefinitionParseError::GeneratedParser {
                at: view.to_original(BytePos(0)),
                error: ParserFailure::Resource(ParserResourceLimit::Steps),
            });
        }
        let mut st = RuntimeState::new(source, false, max_steps);
        st.ctx.verso_docs = docs.verso(false);
        st.ctx.verso_module_docs = docs.verso(true);
        st.skip_whitespace();
        if let Some(error) = st.error.take() {
            if let Some(message) = error.lexical_message {
                return Err(crate::NatDefinitionParseError::Lexical {
                    diagnostics: vec![crate::ParseDiagnostic {
                        message,
                        at: view.to_original(BytePos(error.pos)),
                    }],
                });
            }
            return Err(crate::NatDefinitionParseError::GeneratedParser {
                at: view.to_original(BytePos(error.pos)),
                error: ParserFailure::Syntax {
                    unexpected: error.unexpected,
                    expected: error.expected,
                },
            });
        }
        if st.pos >= source.len_bytes() {
            return Err(crate::NatDefinitionParseError::GeneratedParser {
                at: view.to_original(BytePos(st.pos)),
                error: ParserFailure::Syntax {
                    unexpected: "end of input".to_owned(),
                    expected: vec!["command".to_owned()],
                },
            });
        }
        let top_cmd_op = ParserOp::WithPosition(Arc::new(ParserOp::CategoryParser {
            cat: Name::from_components(["command"]),
            prec: 0,
        }));
        self.exec_op(&top_cmd_op, &mut st);
        if st.depth_exhausted || st.budget_exhausted {
            return Err(crate::NatDefinitionParseError::GeneratedParser {
                at: view.to_original(BytePos(st.pos)),
                error: ParserFailure::Resource(if st.depth_exhausted {
                    ParserResourceLimit::Depth
                } else {
                    ParserResourceLimit::Steps
                }),
            });
        }
        if let Some(error) = st.recovered_errors.first() {
            if let Some(message) = error.lexical_message {
                return Err(crate::NatDefinitionParseError::Lexical {
                    diagnostics: vec![crate::ParseDiagnostic {
                        message,
                        at: view.to_original(BytePos(error.pos)),
                    }],
                });
            }
            return Err(crate::NatDefinitionParseError::GeneratedParser {
                at: view.to_original(BytePos(error.pos)),
                error: ParserFailure::Recovered {
                    unexpected: error.unexpected.clone(),
                    expected: error.expected.clone(),
                },
            });
        }
        if let Some(error) = st.error.take() {
            if let Some(message) = error.lexical_message {
                return Err(crate::NatDefinitionParseError::Lexical {
                    diagnostics: vec![crate::ParseDiagnostic {
                        message,
                        at: view.to_original(BytePos(error.pos)),
                    }],
                });
            }
            return Err(crate::NatDefinitionParseError::GeneratedParser {
                at: view.to_original(BytePos(error.pos)),
                error: ParserFailure::Syntax {
                    unexpected: error.unexpected,
                    expected: error.expected,
                },
            });
        }
        if st.pos < source.len_bytes() {
            return Err(crate::NatDefinitionParseError::GeneratedParser {
                at: view.to_original(BytePos(st.pos)),
                error: ParserFailure::Syntax {
                    unexpected: "unexpected trailing input".to_owned(),
                    expected: vec!["end of input".to_owned()],
                },
            });
        }
        let mut cmd_stx = st.pop_or_missing().to_syntax();
        set_start_of_file_leading(&mut cmd_stx);
        let tail_end = match get_tail_info(&cmd_stx) {
            SourceInfo::Original { trailing, .. } => trailing.end(),
            _ => BytePos(source.len_bytes()),
        };
        let epilogue = ByteSpan::new(tail_end, BytePos(source.len_bytes()))
            .unwrap_or_else(|| ByteSpan::empty_at(BytePos(source.len_bytes())));
        Ok((cmd_stx, epilogue, st.steps))
    }

    /// Parse a complete Lean module (`header` + top-level commands until EOI),
    /// mirroring `Lean/Parser/Module.lean::{parseHeader, parseCommand}`.
    pub fn parse_module(&self, source: &SourceText, max_steps: usize) -> ParsedModule {
        let mut errors = Vec::new();
        let mut total_steps = 0usize;
        let mut budget_exhausted = false;

        // 1. Parse module header with header token table (`Module.lean:75-112`).
        let mut hst = RuntimeState::new(source, true, max_steps);
        hst.skip_whitespace();
        if !hst.has_error() {
            let op = ParserOp::Ref(self.module_header_id);
            self.exec_op(&op, &mut hst);
        }
        total_steps = total_steps.saturating_add(hst.steps);
        if let Some(error) = hst.resource_error() {
            budget_exhausted = true;
            errors.push(error);
        }
        let mut header = hst.back().map(VmNode::to_syntax).unwrap_or(Syntax::Missing);
        for err in hst.recovered_errors.drain(..) {
            errors.push(err);
        }
        if let Some(err) = hst.error.take()
            && !budget_exhausted
        {
            errors.push(err);
        }
        let is_leading_set = set_start_of_file_leading(&mut header);
        let mut pos = hst.pos;
        let mut recovering = !errors.is_empty();
        let mut has_leading = !is_leading_set;

        // 2. Parse commands one by one (`Module.lean:135-178`).
        let mut commands = Vec::new();
        let top_cmd_op = ParserOp::WithPosition(Arc::new(ParserOp::CategoryParser {
            cat: Name::from_components(["command"]),
            prec: 0,
        }));

        loop {
            if budget_exhausted {
                break;
            }
            let remaining = max_steps.saturating_sub(total_steps);
            if remaining == 0 {
                budget_exhausted = true;
                break;
            }
            if pos >= source.len_bytes() {
                let mut eoi_stx = self.mk_eoi_syntax(pos);
                if has_leading {
                    set_start_of_file_leading(&mut eoi_stx);
                }
                commands.push(eoi_stx);
                break;
            }

            let mut cmd_stx = Syntax::Missing;
            let mut produced = false;
            loop {
                if pos >= source.len_bytes() {
                    cmd_stx = self.mk_eoi_syntax(pos);
                    produced = true;
                    break;
                }
                let rem = max_steps.saturating_sub(total_steps);
                if rem == 0 {
                    budget_exhausted = true;
                    break;
                }
                let start_pos = pos;
                let mut st = RuntimeState::new(source, false, rem);
                st.pos = pos;
                st.skip_whitespace();
                if !st.has_error() {
                    self.exec_op(&top_cmd_op, &mut st);
                }
                total_steps = total_steps.saturating_add(st.steps);
                if let Some(error) = st.resource_error() {
                    budget_exhausted = true;
                    errors.push(error);
                    break;
                }
                for err in st.recovered_errors.drain(..) {
                    errors.push(err);
                }
                pos = st.pos;
                if recovering && st.back().is_some_and(is_antiquot_vm) {
                    continue;
                }
                match st.error.take() {
                    None => {
                        cmd_stx = st.back().map(VmNode::to_syntax).unwrap_or(Syntax::Missing);
                        recovering = false;
                        produced = true;
                        break;
                    }
                    Some(err) => {
                        if pos == start_pos {
                            pos = self.consume_one_token(source, pos);
                        }
                        let ignore = st.stack_size() == 0
                            || st.back().is_none_or(|s| first_pos_of_vm(s).is_none());
                        if !(recovering && ignore) {
                            errors.push(err);
                        }
                        recovering = true;
                        if ignore {
                            continue;
                        }
                        cmd_stx = st.back().map(VmNode::to_syntax).unwrap_or(Syntax::Missing);
                        produced = true;
                        break;
                    }
                }
            }

            if !produced {
                break;
            }
            if has_leading {
                set_start_of_file_leading(&mut cmd_stx);
                has_leading = false;
            }
            let terminal = self.is_terminal_command(&cmd_stx);
            commands.push(cmd_stx);
            if terminal {
                break;
            }
        }

        ParsedModule {
            header,
            commands,
            errors,
            steps_used: total_steps,
            budget_exhausted,
        }
    }

    /// Parse a complete Lean module (`header` + top-level commands until EOI) through
    /// the unified registry engine: pin-extracted builtin combinators composed with
    /// [`crate::extensions::FileGrammar`] (`Init`/`Std` imported `ParserDescr` rows,
    /// `namespace`/`section`/`end`/`open`/`open scoped`/`open ... in` scope activations,
    /// `doc.verso` / `doc.verso.module`, and the file's own `syntax`/`notation`/`macro`
    /// declarations). No hand-written seed grammar or `command_scope::partition` is used.
    pub fn parse_module_with_file_grammar(
        &self,
        source: &SourceText,
        module: Option<Name>,
        max_steps: usize,
    ) -> ParsedModule {
        let mut errors = Vec::new();
        let mut total_steps = 0usize;
        let mut budget_exhausted = false;

        // 1. Parse module header with header token table (`Module.lean:75-112`).
        let mut hst = RuntimeState::new(source, true, max_steps);
        hst.skip_whitespace();
        if !hst.has_error() {
            let op = ParserOp::Ref(self.module_header_id);
            self.exec_op(&op, &mut hst);
        }
        total_steps = total_steps.saturating_add(hst.steps);
        if let Some(error) = hst.resource_error() {
            budget_exhausted = true;
            errors.push(error);
        }
        let mut header = hst.back().map(VmNode::to_syntax).unwrap_or(Syntax::Missing);
        for err in hst.recovered_errors.drain(..) {
            errors.push(err);
        }
        if let Some(err) = hst.error.take()
            && !budget_exhausted
        {
            errors.push(err);
        }
        let is_leading_set = set_start_of_file_leading(&mut header);
        let mut pos = hst.pos;
        let mut recovering = !errors.is_empty();
        let mut has_leading = !is_leading_set;

        // 2. Construct the file's dynamic grammar from header prelude + imports.
        let (prelude, imports) = extract_header_prelude_and_imports(&header);
        let mut file_grammar = match crate::extensions::FileGrammar::new(prelude, &imports, module)
        {
            Ok(fg) => Some(fg),
            Err(err) => {
                errors.push(InterpError::new(
                    0,
                    format!(
                        "file grammar initialization failed: unknown module {}",
                        err.0.to_display_string()
                    ),
                    Vec::new(),
                ));
                None
            }
        };

        // 3. Parse commands one by one using the currently active grammar's compiled interpreter.
        let mut commands = Vec::new();
        let top_cmd_op = ParserOp::WithPosition(Arc::new(ParserOp::CategoryParser {
            cat: Name::from_components(["command"]),
            prec: 0,
        }));

        loop {
            if budget_exhausted {
                break;
            }
            let remaining = max_steps.saturating_sub(total_steps);
            if remaining == 0 {
                budget_exhausted = true;
                break;
            }
            if pos >= source.len_bytes() {
                let mut eoi_stx = self.mk_eoi_syntax(pos);
                if has_leading {
                    set_start_of_file_leading(&mut eoi_stx);
                }
                commands.push(eoi_stx);
                break;
            }

            let active_grammar = file_grammar.as_ref().map(|fg| fg.grammar());
            let active_interp_rc = match active_grammar.as_ref() {
                Some(grammar) => match grammar.generated_interpreter(self) {
                    Ok(interp) => Some(interp),
                    Err(err) => {
                        errors.push(InterpError::new(
                            pos,
                            format!("active ParserDescr compilation failed: {err}"),
                            Vec::new(),
                        ));
                        None
                    }
                },
                None => None,
            };
            let active_interp: &BuiltinInterpreter = active_interp_rc.as_deref().unwrap_or(self);
            let docs = active_grammar
                .as_ref()
                .map(|g| g.doc_options())
                .unwrap_or_default();

            let mut cmd_stx = Syntax::Missing;
            let mut produced = false;
            let mut had_cmd_error = false;
            loop {
                if pos >= source.len_bytes() {
                    cmd_stx = active_interp.mk_eoi_syntax(pos);
                    produced = true;
                    break;
                }
                let rem = max_steps.saturating_sub(total_steps);
                if rem == 0 {
                    budget_exhausted = true;
                    break;
                }
                let start_pos = pos;
                let mut st = RuntimeState::new(source, false, rem);
                st.pos = pos;
                st.ctx.verso_docs = docs.verso(false);
                st.ctx.verso_module_docs = docs.verso(true);
                if let Some(fg) = file_grammar.as_ref() {
                    st.open_context = Some((self, fg, fg.scope_snapshot()));
                }
                st.skip_whitespace();
                if !st.has_error() {
                    active_interp.exec_op(&top_cmd_op, &mut st);
                }
                total_steps = total_steps.saturating_add(st.steps);
                if let Some(error) = st.resource_error() {
                    budget_exhausted = true;
                    errors.push(error);
                    break;
                }
                for err in st.recovered_errors.drain(..) {
                    errors.push(err);
                }
                pos = st.pos;
                if recovering && st.back().is_some_and(is_antiquot_vm) {
                    continue;
                }
                match st.error.take() {
                    None => {
                        cmd_stx = st.back().map(VmNode::to_syntax).unwrap_or(Syntax::Missing);
                        recovering = false;
                        produced = true;
                        break;
                    }
                    Some(err) => {
                        had_cmd_error = true;
                        if pos == start_pos {
                            pos = active_interp.consume_one_token(source, pos);
                        }
                        let ignore = st.stack_size() == 0
                            || st.back().is_none_or(|s| first_pos_of_vm(s).is_none());
                        if !(recovering && ignore) {
                            errors.push(err);
                        }
                        recovering = true;
                        if ignore {
                            continue;
                        }
                        cmd_stx = st.back().map(VmNode::to_syntax).unwrap_or(Syntax::Missing);
                        produced = true;
                        break;
                    }
                }
            }

            if !produced {
                break;
            }
            if has_leading {
                set_start_of_file_leading(&mut cmd_stx);
                has_leading = false;
            }
            if !had_cmd_error && let Some(fg) = file_grammar.as_mut() {
                fg.apply_command_syntax(&cmd_stx);
                declare_command_or_in(fg, &cmd_stx);
            }
            let terminal = active_interp.is_terminal_command(&cmd_stx);
            commands.push(cmd_stx);
            if terminal {
                break;
            }
        }

        ParsedModule {
            header,
            commands,
            errors,
            steps_used: total_steps,
            budget_exhausted,
        }
    }

    fn mk_eoi_syntax(&self, pos: usize) -> Syntax {
        let bp = BytePos(pos);
        let empty = ByteSpan::empty_at(bp);
        let atom = Syntax::atom(
            SourceInfo::Original {
                leading: empty,
                pos: bp,
                trailing: empty,
                end_pos: bp,
            },
            "",
        );
        Syntax::node(self.command_eoi_kind.clone(), vec![atom])
    }

    fn is_terminal_command(&self, stx: &Syntax) -> bool {
        stx.kind().is_some_and(|k| {
            *k == self.command_eoi_kind
                || *k == self.command_exit_kind
                || *k == self.command_import_kind
        })
    }

    fn consume_one_token(&self, source: &SourceText, pos: usize) -> usize {
        let mut st = RuntimeState::new(source, false, 1024);
        st.pos = pos;
        self.token_fn(&[], &mut st);
        if st.has_error() || st.pos <= pos {
            advance_one_char(source.as_str(), pos)
        } else {
            st.pos
        }
    }

    #[inline(never)]
    fn exec_depth_exceeded(&self, st: &mut RuntimeState<'_>) {
        st.depth_exhausted = true;
        st.mk_unexpected_error(
            format!("parser recursion depth limit exceeded at byte {}", st.pos),
            Vec::new(),
            true,
        );
    }

    #[inline(never)]
    fn exec_push_none(&self, st: &mut RuntimeState<'_>) {
        st.push(VmNode::node(self.null_kind.clone(), Vec::new()));
    }

    #[inline(never)]
    fn exec_eoi(&self, st: &mut RuntimeState<'_>) {
        if st.pos < st.source.len_bytes() {
            st.mk_error("expected end of file");
        }
    }

    #[inline(never)]
    fn exec_check_leaf(&self, op: &ParserOp, st: &mut RuntimeState<'_>) {
        match op {
            ParserOp::CheckPrec(prec) => {
                if st.ctx.prec > *prec {
                    st.mk_unexpected_error(
                        "unexpected token at this precedence level; consider parenthesizing the term",
                        Vec::new(),
                        true,
                    );
                }
            }
            ParserOp::CheckLhsPrec(prec) => {
                if st.lhs_prec < *prec {
                    st.mk_unexpected_error(
                        "unexpected token at this precedence level; consider parenthesizing the term",
                        Vec::new(),
                        true,
                    );
                }
            }
            ParserOp::SetLhsPrec(prec) => {
                if !st.has_error() {
                    st.lhs_prec = *prec;
                }
            }
            ParserOp::CheckColEq(msg) => {
                if let Some(saved) = st.ctx.saved_pos
                    && scalar_col_of(st.source, st.pos) != scalar_col_of(st.source, saved)
                {
                    st.mk_error(msg);
                }
            }
            ParserOp::CheckColGe(msg) => {
                if let Some(saved) = st.ctx.saved_pos
                    && scalar_col_of(st.source, st.pos) < scalar_col_of(st.source, saved)
                {
                    st.mk_error(msg);
                }
            }
            ParserOp::CheckColGt(msg) => {
                if let Some(saved) = st.ctx.saved_pos
                    && scalar_col_of(st.source, st.pos) <= scalar_col_of(st.source, saved)
                {
                    st.mk_error(msg);
                }
            }
            ParserOp::CheckLineEq(msg) => {
                if let Some(saved) = st.ctx.saved_pos
                    && st.source.line_of(BytePos(st.pos)) != st.source.line_of(BytePos(saved))
                {
                    st.mk_error(msg);
                }
            }
            ParserOp::CheckWsBefore(msg) => {
                if !st.pick_non_none(&self.null_kind).is_some_and(check_tail_ws) {
                    st.mk_error(msg);
                }
            }
            ParserOp::CheckNoWsBefore(msg) => {
                if !st
                    .pick_non_none(&self.null_kind)
                    .is_some_and(check_tail_no_ws)
                {
                    st.mk_error(msg);
                }
            }
            ParserOp::CheckLinebreakBefore(msg) => {
                if !st
                    .back()
                    .is_some_and(|prev| check_tail_linebreak(st.source, prev))
                {
                    st.mk_error(msg);
                }
            }
            ParserOp::CheckNoImmediateColon
                if st.back().is_some_and(check_tail_no_ws)
                    && st.source.as_bytes().get(st.pos) == Some(&b':') =>
            {
                st.mk_unexpected_error("unexpected ':'", Vec::new(), true);
            }
            _ => {}
        }
    }

    #[inline(never)]
    fn exec_symbol(&self, sym: &str, st: &mut RuntimeState<'_>) {
        let expected = format!("'{sym}'");
        self.satisfy_symbol(|s| s == sym, std::slice::from_ref(&expected), st);
    }

    #[inline(never)]
    fn exec_non_reserved_symbol(&self, sym: &str, st: &mut RuntimeState<'_>) {
        let expected = format!("'{sym}'");
        let ini_pos = st.pos;
        self.token_fn(std::slice::from_ref(&expected), st);
        if st.has_error() {
            return;
        }
        match st.back().map(Deref::deref) {
            Some(VmSyntax::Atom { val, .. }) if val == sym => {}
            Some(VmSyntax::Ident { info, raw_val, .. }) if raw_val.text(st.source) == Some(sym) => {
                let info = *info;
                st.pop();
                st.push(VmNode::atom(info, sym.to_owned()));
            }
            _ => {
                st.mk_unexpected_token_errors(std::slice::from_ref(&expected), Some(ini_pos));
            }
        }
    }

    #[inline(never)]
    fn exec_unicode_symbol(&self, sym: &str, ascii_sym: &str, st: &mut RuntimeState<'_>) {
        let expected = format!("'{sym}', '{ascii_sym}'");
        self.satisfy_symbol(
            |s| s == sym || s == ascii_sym,
            std::slice::from_ref(&expected),
            st,
        );
    }

    #[inline(never)]
    fn exec_raw_ch(&self, ch: char, trailing_ws: bool, st: &mut RuntimeState<'_>) {
        let start_pos = st.pos;
        let rest = &st.source.as_str()[start_pos..];
        match rest.chars().next() {
            None => st.mk_eoi_error(&[]),
            Some(curr) if curr == ch => {
                st.pos = start_pos + curr.len_utf8();
                self.push_raw_atom(start_pos, trailing_ws, st);
            }
            Some(_) => st.mk_unexpected_error(format!("'{ch}'"), Vec::new(), true),
        }
    }

    #[inline(never)]
    fn exec_check_stack_top(&self, pred: SyntaxPred, msg: &str, st: &mut RuntimeState<'_>) {
        let ok = st.back().is_some_and(|top| match pred {
            SyntaxPred::IsIdent => is_ident_stx_vm(top),
            SyntaxPred::IsIdentOrDotIdentOrProj => {
                is_ident_stx_vm(top)
                    || top.kind() == Some(&self.dot_ident_kind)
                    || top.kind() == Some(&self.proj_kind)
            }
        });
        if !ok {
            st.mk_unexpected_error(msg.to_owned(), Vec::new(), true);
        }
    }

    #[inline(never)]
    fn exec_skip_until(&self, pred: &CharPred, st: &mut RuntimeState<'_>) {
        let s = st.source.as_str();
        let mut at = st.pos;
        while at < s.len() {
            let ch = s[at..].chars().next().unwrap_or('\0');
            if pred.matches(ch) {
                break;
            }
            at += ch.len_utf8();
        }
        while at < s.len() {
            let ch = s[at..].chars().next().unwrap_or('\0');
            if !is_lean_whitespace(ch) {
                break;
            }
            at += ch.len_utf8();
        }
        st.pos = at;
    }

    #[inline(never)]
    fn exec_error_at_saved_pos(&self, msg: &str, delta: bool, st: &mut RuntimeState<'_>) {
        if let Some(saved) = st.ctx.saved_pos {
            let pos = if delta {
                advance_one_char(st.source.as_str(), saved)
            } else {
                saved
            };
            st.pos = pos;
            st.mk_unexpected_error(msg.to_owned(), Vec::new(), true);
        }
    }

    fn indexed_lookup(
        &self,
        table: &BTreeMap<Name, Vec<(usize, u32)>>,
        behavior: LeadingIdentBehavior,
        st: &mut RuntimeState<'_>,
    ) -> Vec<(usize, u32)> {
        let Some(tok) = self.peek_token(st) else {
            return Vec::new();
        };
        let lookup = |k: &Name| table.get(k).cloned().unwrap_or_default();
        match &*tok {
            VmSyntax::Atom { val, .. } => lookup(&Name::str(Name::anonymous(), val.as_str())),
            VmSyntax::Ident { val, .. } => match behavior {
                LeadingIdentBehavior::Default => lookup(&self.ident_kind),
                LeadingIdentBehavior::Symbol => match table.get(val) {
                    Some(ps) => ps.clone(),
                    None => lookup(&self.ident_kind),
                },
                LeadingIdentBehavior::Both => match table.get(val) {
                    Some(ps) => {
                        if *val == self.ident_kind {
                            ps.clone()
                        } else {
                            let mut both = ps.clone();
                            if let Some(ident_ps) = table.get(&self.ident_kind) {
                                both.extend_from_slice(ident_ps);
                            }
                            both
                        }
                    }
                    None => lookup(&self.ident_kind),
                },
            },
            VmSyntax::Node { kind, .. } => lookup(kind),
            VmSyntax::Missing => Vec::new(),
        }
    }

    fn push_flattened_antiquots(&self, stx: VmNode, st: &mut RuntimeState<'_>) {
        if let VmSyntax::Node { kind, args, .. } = &*stx
            && *kind == self.choice_kind
        {
            for arg in args {
                st.push(arg.clone());
            }
            return;
        }
        st.push(stx);
    }

    fn peek_token(&self, st: &mut RuntimeState<'_>) -> Option<VmNode> {
        if let Some((start, _, ref forb, ref tok)) = st.token_cache
            && start == st.pos
            && *forb == st.ctx.forbidden_tk
        {
            return Some(tok.clone());
        }
        let ini_sz = st.stack_size();
        let ini_pos = st.pos;
        self.token_fn(&[], st);
        if st.has_error() {
            return None;
        }
        let tok = st.back_cloned();
        st.restore(ini_sz, ini_pos);
        tok
    }

    fn token_fn(&self, expected: &[String], st: &mut RuntimeState<'_>) {
        let start_pos = st.pos;
        if start_pos >= st.source.len_bytes() {
            st.mk_eoi_error(expected);
            return;
        }
        if let Some((c_start, c_stop, ref c_forb, ref c_tok)) = st.token_cache
            && c_start == start_pos
            && *c_forb == st.ctx.forbidden_tk
        {
            st.push(c_tok.clone());
            st.pos = c_stop;
            return;
        }

        let tokens = if st.use_header_tokens {
            &self.header_tokens
        } else {
            &self.builtin_tokens
        };
        match lex_token(st.source, tokens, BytePos(start_pos)) {
            Ok(lexed) => {
                if let TokenKind::Symbol(ref sym) = lexed.kind
                    && st.ctx.forbidden_tk.as_deref() == Some(sym.as_str())
                {
                    st.pos = start_pos;
                    st.mk_error("forbidden token");
                    return;
                }
                let stop_pos = lexed.extent.end();
                let ws_stop = match scan_trivia(st.source, stop_pos) {
                    Ok(ws) => ws,
                    Err(err) => {
                        st.pos = err.at().0;
                        st.mk_lexical_error(err.message(), Vec::new(), false);
                        return;
                    }
                };
                let info = SourceInfo::Original {
                    leading: ByteSpan::empty_at(lexed.extent.start()),
                    pos: lexed.extent.start(),
                    trailing: ByteSpan::new(stop_pos, ws_stop)
                        .expect("scan_trivia never moves backwards"),
                    end_pos: stop_pos,
                };
                let tok = match lexed.kind {
                    TokenKind::Symbol(sym) => VmNode::atom(info, sym),
                    TokenKind::Ident(val) => VmNode::ident(info, lexed.extent.into(), val),
                    TokenKind::Literal(lit_kind) => {
                        let kind = match lit_kind {
                            LiteralKind::Nat => self.num_lit_kind.clone(),
                            LiteralKind::Scientific => self.scientific_lit_kind.clone(),
                            LiteralKind::Str => self.str_lit_kind.clone(),
                            LiteralKind::Char => self.char_lit_kind.clone(),
                            LiteralKind::Name => self.name_lit_kind.clone(),
                        };
                        let raw = st
                            .source
                            .span_str(lexed.extent)
                            .unwrap_or_default()
                            .to_owned();
                        VmNode::node(kind, vec![VmNode::atom(info, raw)])
                    }
                };
                st.pos = ws_stop.0;
                st.token_cache = Some((
                    start_pos,
                    ws_stop.0,
                    st.ctx.forbidden_tk.clone(),
                    tok.clone(),
                ));
                st.push(tok);
            }
            Err(err) => {
                st.pos = err.at().0;
                st.mk_lexical_error(err.message(), expected.to_vec(), true);
            }
        }
    }

    fn satisfy_symbol(
        &self,
        pred: impl Fn(&str) -> bool,
        expected: &[String],
        st: &mut RuntimeState<'_>,
    ) {
        let ini_pos = st.pos;
        self.token_fn(expected, st);
        if st.has_error() {
            return;
        }
        if let Some(VmSyntax::Atom { val, .. }) = st.back().map(Deref::deref)
            && pred(val)
        {
            return;
        }
        st.mk_unexpected_token_errors(expected, Some(ini_pos));
    }

    fn expect_token_kind(&self, kind: &Name, desc: &str, st: &mut RuntimeState<'_>) {
        let expected = vec![desc.to_owned()];
        let ini_pos = st.pos;
        self.token_fn(&expected, st);
        if st.has_error() {
            return;
        }
        let matches = match st.back().map(Deref::deref) {
            Some(VmSyntax::Ident { .. }) => *kind == self.ident_kind,
            Some(VmSyntax::Node { kind: k, .. }) => k == kind,
            _ => false,
        };
        if !matches {
            st.mk_unexpected_token_errors(&expected, Some(ini_pos));
        }
    }

    fn raw_ident_fn(&self, st: &mut RuntimeState<'_>) {
        let start_pos = st.pos;
        if start_pos >= st.source.len_bytes() {
            st.mk_eoi_error(&[]);
            return;
        }
        static EMPTY_TABLE: OnceLock<TokenTable> = OnceLock::new();
        let empty = EMPTY_TABLE.get_or_init(TokenTable::new);
        match lex_token(st.source, empty, BytePos(start_pos)) {
            Ok(lexed) if matches!(lexed.kind, TokenKind::Ident(_)) => {
                let TokenKind::Ident(val) = lexed.kind else {
                    unreachable!();
                };
                let stop_pos = lexed.extent.end();
                let ws_stop = match scan_trivia(st.source, stop_pos) {
                    Ok(ws) => ws,
                    Err(err) => {
                        st.pos = err.at().0;
                        st.mk_lexical_error(err.message(), Vec::new(), false);
                        return;
                    }
                };
                let info = SourceInfo::Original {
                    leading: ByteSpan::empty_at(lexed.extent.start()),
                    pos: lexed.extent.start(),
                    trailing: ByteSpan::new(stop_pos, ws_stop)
                        .expect("scan_trivia never moves backwards"),
                    end_pos: stop_pos,
                };
                st.pos = ws_stop.0;
                st.push(VmNode::ident(info, lexed.extent.into(), val));
            }
            _ => {
                st.pos = start_pos;
                st.mk_error("token");
            }
        }
    }

    fn hexnum_fn(&self, st: &mut RuntimeState<'_>) {
        let start_pos = st.pos;
        let bytes = st.source.as_bytes();
        let mut at = start_pos;
        let mut need_digit = true;
        while at < bytes.len() {
            let b = bytes[at];
            if b == b'_' {
                need_digit = true;
                at += 1;
            } else if b.is_ascii_hexdigit() {
                need_digit = false;
                at += 1;
            } else {
                break;
            }
        }
        if need_digit {
            st.pos = at;
            st.mk_error("hexadecimal number");
            return;
        }
        st.pos = at;
        self.push_node_token(self.hexnum_kind.clone(), start_pos, true, st);
    }

    fn field_idx_fn(&self, st: &mut RuntimeState<'_>) {
        let ini_sz = st.stack_size();
        let ini_pos = st.pos;
        let bytes = st.source.as_bytes();
        let Some(&first) = bytes.get(ini_pos) else {
            st.shrink(ini_sz);
            st.pos = ini_pos;
            st.mk_error("field index");
            return;
        };
        if !first.is_ascii_digit() || first == b'0' {
            st.shrink(ini_sz);
            st.pos = ini_pos;
            st.mk_error("field index");
            return;
        }
        let mut at = ini_pos + 1;
        while at < bytes.len() && bytes[at].is_ascii_digit() {
            at += 1;
        }
        st.pos = at;
        self.push_node_token(self.field_idx_kind.clone(), ini_pos, true, st);
    }

    fn hygiene_info_fn(&self, st: &mut RuntimeState<'_>) {
        let finish = |st: &mut RuntimeState<'_>, pos: BytePos, trailing: ByteSpan| {
            let empty = ByteSpan::empty_at(pos);
            let info = SourceInfo::Original {
                leading: empty,
                pos,
                trailing,
                end_pos: pos,
            };
            let ident = VmNode::ident(info, empty.into(), Name::anonymous());
            st.push(VmNode::node(self.hygiene_info_kind.clone(), vec![ident]));
        };
        if let Some(mut prev) = st.pop() {
            if let SourceInfo::Original {
                leading,
                pos,
                trailing,
                end_pos,
            } = get_tail_info_vm(&prev)
            {
                let empty = ByteSpan::empty_at(end_pos);
                set_tail_info_vm(
                    &mut prev,
                    SourceInfo::Original {
                        leading,
                        pos,
                        trailing: empty,
                        end_pos,
                    },
                );
                st.push(prev);
                finish(st, end_pos, trailing);
                return;
            }
            st.push(prev);
        }
        let cur = BytePos(st.pos);
        finish(st, cur, ByteSpan::empty_at(cur));
    }

    fn comment_body_fn(&self, st: &mut RuntimeState<'_>) {
        let start_pos = st.pos;
        let bytes = st.source.as_bytes();
        let mut at = start_pos;
        let mut depth = 1usize;
        while depth > 0 {
            match (bytes.get(at), bytes.get(at + 1)) {
                (Some(b'-'), Some(b'/')) => {
                    depth -= 1;
                    at += 2;
                }
                (Some(b'/'), Some(b'-')) => {
                    depth += 1;
                    at += 2;
                }
                (Some(_), _) => at += 1,
                (None, _) => {
                    st.pos = at;
                    st.mk_unexpected_error("unterminated comment", Vec::new(), true);
                    return;
                }
            }
        }
        st.pos = at;
        self.push_raw_atom(start_pos, true, st);
    }

    fn verso_comment_body_fn(&self, st: &mut RuntimeState<'_>) {
        let start_pos = st.pos;
        let bytes = st.source.as_bytes();
        let mut at = start_pos;
        let mut depth = 1usize;
        while depth > 0 {
            match (bytes.get(at), bytes.get(at + 1)) {
                (Some(b'-'), Some(b'/')) => {
                    depth -= 1;
                    at += 2;
                }
                (Some(b'/'), Some(b'-')) => {
                    depth += 1;
                    at += 2;
                }
                (Some(_), _) => at += 1,
                (None, _) => {
                    st.pos = at;
                    st.mk_unexpected_error("unterminated comment", Vec::new(), true);
                    return;
                }
            }
        }
        let close = at.saturating_sub(2);
        let text = st.source.as_str();
        let Some(verso) = crate::verso::body(text, start_pos, close) else {
            st.pos = at;
            self.push_raw_atom(start_pos, true, st);
            return;
        };
        let ws_stop = match scan_trivia(st.source, BytePos(at)) {
            Ok(ws) => {
                st.pos = ws.0;
                ws
            }
            Err(err) => {
                st.pos = err.at().0;
                st.mk_unexpected_error(err.message(), Vec::new(), false);
                return;
            }
        };
        let document = match verso {
            crate::verso::Body::Blocks(blocks) => VmNode::from_syntax(&blocks),
            crate::verso::Body::Failure => VmNode::node(
                Name::from_components(["Lean", "Doc", "Syntax", "parseFailure"]),
                vec![VmNode::atom(
                    SourceInfo::Original {
                        leading: ByteSpan::empty_at(BytePos(start_pos)),
                        pos: BytePos(start_pos),
                        trailing: ByteSpan::empty_at(BytePos(close)),
                        end_pos: BytePos(close),
                    },
                    text[start_pos..close].to_owned(),
                )],
            ),
        };
        let closer = VmNode::atom(
            SourceInfo::Original {
                leading: ByteSpan::empty_at(BytePos(close)),
                pos: BytePos(close),
                trailing: ByteSpan::new(BytePos(at), ws_stop)
                    .expect("scan_trivia never moves backwards"),
                end_pos: BytePos(at),
            },
            "-/",
        );
        st.push(VmNode::node(
            Name::from_components(["Lean", "Parser", "Command", "versoCommentBody"]),
            vec![document, closer],
        ));
    }

    fn push_raw_atom(&self, start_pos: usize, trailing_ws: bool, st: &mut RuntimeState<'_>) {
        let stop_pos = st.pos;
        let val = st.source.as_str()[start_pos..stop_pos].to_owned();
        let ws_stop = if trailing_ws {
            match scan_trivia(st.source, BytePos(stop_pos)) {
                Ok(ws) => {
                    st.pos = ws.0;
                    ws
                }
                Err(err) => {
                    st.pos = err.at().0;
                    st.mk_lexical_error(err.message(), Vec::new(), false);
                    return;
                }
            }
        } else {
            BytePos(stop_pos)
        };
        let info = SourceInfo::Original {
            leading: ByteSpan::empty_at(BytePos(start_pos)),
            pos: BytePos(start_pos),
            trailing: ByteSpan::new(BytePos(stop_pos), ws_stop)
                .expect("scan_trivia never moves backwards"),
            end_pos: BytePos(stop_pos),
        };
        st.push(VmNode::atom(info, val));
    }

    fn push_node_token(
        &self,
        kind: Name,
        start_pos: usize,
        include_ws: bool,
        st: &mut RuntimeState<'_>,
    ) {
        if st.has_error() {
            return;
        }
        let stop_pos = st.pos;
        let val = st.source.as_str()[start_pos..stop_pos].to_owned();
        let ws_stop = if include_ws {
            match scan_trivia(st.source, BytePos(stop_pos)) {
                Ok(ws) => {
                    st.pos = ws.0;
                    ws
                }
                Err(err) => {
                    st.pos = err.at().0;
                    st.mk_lexical_error(err.message(), Vec::new(), false);
                    return;
                }
            }
        } else {
            BytePos(stop_pos)
        };
        let info = SourceInfo::Original {
            leading: ByteSpan::empty_at(BytePos(start_pos)),
            pos: BytePos(start_pos),
            trailing: ByteSpan::new(BytePos(stop_pos), ws_stop)
                .expect("scan_trivia never moves backwards"),
            end_pos: BytePos(stop_pos),
        };
        st.push(VmNode::node(kind, vec![VmNode::atom(info, val)]));
    }
}

fn skip_quoted_char_for_interp(st: &mut RuntimeState<'_>) -> bool {
    let i = st.pos;
    if i >= st.source.len_bytes() {
        st.mk_eoi_error(&[]);
        return false;
    }
    let ch = st.source.as_str()[i..].chars().next().unwrap_or('\0');
    if matches!(ch, '{' | '\\' | '"' | '\'' | 'r' | 'n' | 't') {
        st.pos = i + ch.len_utf8();
        true
    } else if ch == 'x' {
        let end = i + 1 + 2;
        if end <= st.source.len_bytes()
            && st.source.as_bytes()[i + 1..end]
                .iter()
                .all(u8::is_ascii_hexdigit)
        {
            st.pos = end;
            true
        } else {
            st.mk_unexpected_error("invalid hexadecimal numeral", Vec::new(), true);
            false
        }
    } else if ch == 'u' {
        let end = i + 1 + 4;
        if end <= st.source.len_bytes()
            && st.source.as_bytes()[i + 1..end]
                .iter()
                .all(u8::is_ascii_hexdigit)
        {
            st.pos = end;
            true
        } else {
            st.mk_unexpected_error("invalid hexadecimal numeral", Vec::new(), true);
            false
        }
    } else if ch == '\n' {
        let mut at = i + 1;
        let bytes = st.source.as_bytes();
        while at < bytes.len() {
            match bytes[at] {
                b'\n' => {
                    st.pos = at;
                    st.mk_unexpected_error(
                        "unexpected additional newline in string gap",
                        Vec::new(),
                        true,
                    );
                    return false;
                }
                b' ' | b'\t' | b'\r' => at += 1,
                _ => break,
            }
        }
        st.pos = at;
        true
    } else {
        st.mk_unexpected_error("invalid escape sequence", Vec::new(), true);
        false
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct CacheableCtx {
    prec: u32,
    quot_depth: u32,
    suppress_inside_quot: bool,
    saved_pos: Option<usize>,
    forbidden_tk: Option<String>,
    verso_docs: bool,
    verso_module_docs: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ParserCacheKey {
    ctx: CacheableCtx,
    parser_name: Name,
    pos: usize,
}

/// Reference-counted syntax tree node used internally by the parser VM so
/// packrat memoization (`parser_cache`) and Pratt/OrElse backtracking clone
/// subtrees in O(1) while iterative [`Drop`] keeps destruction O(1) on the
/// native stack even for 6,000+ deep trees on 96 KiB threads.
#[derive(Debug, Clone)]
pub(super) struct VmNode(Option<Rc<VmSyntax>>);

#[derive(Debug, Clone)]
pub(super) enum VmSyntax {
    Missing,
    Atom {
        info: SourceInfo,
        val: String,
    },
    Ident {
        info: SourceInfo,
        raw_val: fln_syntax::tree::RawIdentifier,
        val: Name,
        preresolved: Vec<fln_syntax::tree::Preresolved>,
    },
    Node {
        info: SourceInfo,
        kind: Name,
        args: Vec<VmNode>,
        tree_nodes: usize,
    },
}

impl Deref for VmNode {
    type Target = VmSyntax;
    #[inline]
    fn deref(&self) -> &Self::Target {
        const MISSING: &VmSyntax = &VmSyntax::Missing;
        self.0.as_deref().unwrap_or(MISSING)
    }
}

impl Drop for VmNode {
    fn drop(&mut self) {
        let Some(root) = self.0.take() else {
            return;
        };
        if Rc::strong_count(&root) > 1 {
            return;
        }
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            if let Ok(mut inner) = Rc::try_unwrap(node)
                && let VmSyntax::Node { args, .. } = &mut inner
            {
                for mut child in std::mem::take(args) {
                    if let Some(c) = child.0.take() {
                        work.push(c);
                    }
                }
            }
        }
    }
}

impl VmNode {
    #[inline]
    fn missing() -> Self {
        Self(Some(Rc::new(VmSyntax::Missing)))
    }

    #[inline]
    fn atom(info: SourceInfo, val: impl Into<String>) -> Self {
        Self(Some(Rc::new(VmSyntax::Atom {
            info,
            val: val.into(),
        })))
    }

    #[inline]
    fn ident(info: SourceInfo, raw_val: fln_syntax::tree::RawIdentifier, val: Name) -> Self {
        Self(Some(Rc::new(VmSyntax::Ident {
            info,
            raw_val,
            val,
            preresolved: Vec::new(),
        })))
    }

    #[inline]
    fn tree_nodes(&self) -> usize {
        match &**self {
            VmSyntax::Node { tree_nodes, .. } => *tree_nodes,
            VmSyntax::Missing | VmSyntax::Atom { .. } | VmSyntax::Ident { .. } => 1,
        }
    }

    #[inline]
    fn node(kind: Name, args: Vec<VmNode>) -> Self {
        let mut tree_nodes = 1usize;
        for arg in &args {
            tree_nodes = tree_nodes.saturating_add(arg.tree_nodes());
        }
        Self(Some(Rc::new(VmSyntax::Node {
            info: SourceInfo::None,
            kind,
            args,
            tree_nodes,
        })))
    }

    #[inline]
    fn kind(&self) -> Option<&Name> {
        match &**self {
            VmSyntax::Node { kind, .. } => Some(kind),
            _ => None,
        }
    }

    #[inline]
    fn make_mut(&mut self) -> &mut VmSyntax {
        let rc = self.0.get_or_insert_with(|| Rc::new(VmSyntax::Missing));
        Rc::make_mut(rc)
    }

    /// Iterative conversion from `&Syntax` into `VmNode`.
    fn from_syntax(root: &Syntax) -> Self {
        enum Step<'a> {
            Visit(&'a Syntax),
            FinishNode {
                info: SourceInfo,
                kind: Name,
                arity: usize,
            },
        }
        let mut work = vec![Step::Visit(root)];
        let mut out: Vec<VmNode> = Vec::new();
        while let Some(step) = work.pop() {
            match step {
                Step::Visit(Syntax::Missing) => out.push(VmNode::missing()),
                Step::Visit(Syntax::Atom { info, val }) => {
                    out.push(VmNode::atom(*info, val.clone()));
                }
                Step::Visit(Syntax::Ident {
                    info,
                    raw_val,
                    val,
                    preresolved,
                }) => out.push(Self(Some(Rc::new(VmSyntax::Ident {
                    info: *info,
                    raw_val: raw_val.clone(),
                    val: val.clone(),
                    preresolved: preresolved.clone(),
                })))),
                Step::Visit(Syntax::Node { info, kind, args }) => {
                    let arity = args.len();
                    work.push(Step::FinishNode {
                        info: *info,
                        kind: kind.clone(),
                        arity,
                    });
                    for arg in args.iter().rev() {
                        work.push(Step::Visit(arg));
                    }
                }
                Step::FinishNode { info, kind, arity } => {
                    let split = out.len().saturating_sub(arity);
                    let args = out.split_off(split);
                    let mut tree_nodes = 1usize;
                    for arg in &args {
                        tree_nodes = tree_nodes.saturating_add(arg.tree_nodes());
                    }
                    out.push(Self(Some(Rc::new(VmSyntax::Node {
                        info,
                        kind,
                        args,
                        tree_nodes,
                    }))));
                }
            }
        }
        out.pop().unwrap_or_else(VmNode::missing)
    }

    /// Iterative O(N) conversion from `VmNode` back to owned `Syntax`.
    pub(super) fn to_syntax(&self) -> Syntax {
        enum Step<'a> {
            Visit(&'a VmNode),
            FinishNode {
                info: SourceInfo,
                kind: Name,
                arity: usize,
            },
        }
        let mut work = vec![Step::Visit(self)];
        let mut out: Vec<Syntax> = Vec::new();
        while let Some(step) = work.pop() {
            match step {
                Step::Visit(node) => match &**node {
                    VmSyntax::Missing => out.push(Syntax::Missing),
                    VmSyntax::Atom { info, val } => out.push(Syntax::Atom {
                        info: *info,
                        val: val.clone(),
                    }),
                    VmSyntax::Ident {
                        info,
                        raw_val,
                        val,
                        preresolved,
                    } => out.push(Syntax::Ident {
                        info: *info,
                        raw_val: raw_val.clone(),
                        val: val.clone(),
                        preresolved: preresolved.clone(),
                    }),
                    VmSyntax::Node {
                        info,
                        kind,
                        args,
                        tree_nodes: _,
                    } => {
                        let arity = args.len();
                        work.push(Step::FinishNode {
                            info: *info,
                            kind: kind.clone(),
                            arity,
                        });
                        for arg in args.iter().rev() {
                            work.push(Step::Visit(arg));
                        }
                    }
                },
                Step::FinishNode { info, kind, arity } => {
                    let split = out.len().saturating_sub(arity);
                    let args = out.split_off(split);
                    out.push(Syntax::Node { info, kind, args });
                }
            }
        }
        out.pop().unwrap_or(Syntax::Missing)
    }
}

#[derive(Debug, Clone)]
struct ParserCacheEntry {
    stx: VmNode,
    lhs_prec: u32,
    new_pos: usize,
    error: Option<InterpError>,
}

struct RuntimeState<'a> {
    source: &'a SourceText,
    use_header_tokens: bool,
    open_context: Option<(
        &'a BuiltinInterpreter,
        &'a crate::extensions::FileGrammar,
        crate::extensions::FileScope,
    )>,
    ctx: CacheableCtx,
    stack: Vec<VmNode>,
    stack_drop: usize,
    lhs_prec: u32,
    pos: usize,
    error: Option<InterpError>,
    recovered_errors: Vec<InterpError>,
    token_cache: Option<(usize, usize, Option<String>, VmNode)>,
    parser_cache: HashMap<ParserCacheKey, ParserCacheEntry>,
    active_cache_keys: HashSet<ParserCacheKey>,
    depth: usize,
    max_depth: usize,
    max_op_depth: usize,
    max_tree_nodes: usize,
    steps: usize,
    max_steps: usize,
    budget_exhausted: bool,
    depth_exhausted: bool,
}

impl<'a> RuntimeState<'a> {
    fn new(source: &'a SourceText, use_header_tokens: bool, max_steps: usize) -> Self {
        Self {
            source,
            use_header_tokens,
            open_context: None,
            ctx: CacheableCtx {
                prec: 0,
                quot_depth: 0,
                suppress_inside_quot: false,
                saved_pos: None,
                forbidden_tk: None,
                verso_docs: false,
                verso_module_docs: false,
            },
            stack: Vec::new(),
            stack_drop: 0,
            lhs_prec: 0,
            pos: 0,
            error: None,
            recovered_errors: Vec::new(),
            token_cache: None,
            parser_cache: HashMap::new(),
            active_cache_keys: HashSet::new(),
            depth: 0,
            max_depth: DEFAULT_MAX_DEPTH,
            max_op_depth: 65_536,
            max_tree_nodes: DEFAULT_MAX_TREE_NODES,
            steps: 0,
            max_steps,
            budget_exhausted: false,
            depth_exhausted: false,
        }
    }

    #[inline]
    fn is_exhausted(&self) -> bool {
        self.depth_exhausted || self.budget_exhausted
    }

    fn resource_error(&self) -> Option<InterpError> {
        let message = if self.depth_exhausted {
            "parser recursion depth limit exceeded"
        } else if self.budget_exhausted {
            "parser step budget exhausted"
        } else {
            return None;
        };
        Some(InterpError::new(self.pos, message, Vec::new()))
    }

    #[inline]
    fn tick(&mut self) -> bool {
        if self.depth_exhausted {
            if self.error.is_none() {
                self.error = Some(InterpError::new(
                    self.pos,
                    "parser recursion depth limit exceeded",
                    Vec::new(),
                ));
            }
            return false;
        }
        if self.budget_exhausted || self.steps >= self.max_steps {
            self.budget_exhausted = true;
            if self.error.is_none() {
                self.error = Some(InterpError::new(
                    self.pos,
                    "parser step budget exhausted",
                    Vec::new(),
                ));
            }
            return false;
        }
        self.steps += 1;
        true
    }

    fn skip_whitespace(&mut self) {
        match scan_trivia(self.source, BytePos(self.pos)) {
            Ok(ws) => self.pos = ws.0,
            Err(err) => {
                self.pos = err.at().0;
                self.mk_lexical_error(err.message(), Vec::new(), false);
            }
        }
    }

    #[inline]
    fn has_error(&self) -> bool {
        self.error.is_some()
    }

    #[inline]
    fn raw_stack_len(&self) -> usize {
        self.stack.len()
    }

    #[inline]
    fn truncate_raw(&mut self, len: usize) {
        self.stack.truncate(len);
    }

    #[inline]
    fn stack_size(&self) -> usize {
        self.stack.len().saturating_sub(self.stack_drop)
    }

    #[inline]
    fn push(&mut self, stx: VmNode) {
        self.stack.push(stx);
    }

    #[inline]
    fn pop(&mut self) -> Option<VmNode> {
        if self.stack_size() > 0 {
            self.stack.pop()
        } else {
            None
        }
    }

    #[inline]
    fn pop_or_missing(&mut self) -> VmNode {
        self.pop().unwrap_or_else(VmNode::missing)
    }

    #[inline]
    fn back(&self) -> Option<&VmNode> {
        if self.stack_size() > 0 {
            self.stack.last()
        } else {
            None
        }
    }

    #[inline]
    fn back_cloned(&self) -> Option<VmNode> {
        self.back().cloned()
    }

    #[inline]
    fn get_visible(&self, idx: usize) -> Option<&VmNode> {
        if idx < self.stack_size() {
            self.stack.get(self.stack_drop + idx)
        } else {
            None
        }
    }

    #[inline]
    fn shrink(&mut self, n: usize) {
        self.stack.truncate(self.stack_drop + n);
    }

    #[inline]
    fn restore(&mut self, ini_sz: usize, ini_pos: usize) {
        self.shrink(ini_sz);
        self.pos = ini_pos;
        self.error = None;
    }

    fn keep_top(&mut self, start_sz: usize) {
        let top = self.pop_or_missing();
        self.shrink(start_sz);
        self.push(top);
    }

    fn pick_non_none(&self, null_kind: &Name) -> Option<&VmNode> {
        self.stack[self.stack_drop..]
            .iter()
            .rev()
            .find(|s| !is_none_stx_vm(s, null_kind))
    }

    fn mk_node(&mut self, kind: Name, ini_sz: usize) {
        if self.has_error() && self.stack_size() == ini_sz {
            self.push(VmNode::missing());
            return;
        }
        let split_at = (self.stack_drop + ini_sz).min(self.stack.len());
        let args = self.stack.split_off(split_at);
        let node = VmNode::node(kind, args);
        if node.tree_nodes() > self.max_tree_nodes {
            self.budget_exhausted = true;
            self.mk_unexpected_error(
                "syntax tree node budget exhausted".to_owned(),
                Vec::new(),
                true,
            );
            return;
        }
        self.push(node);
    }

    fn mk_trailing_node(&mut self, kind: Name, ini_sz: usize) {
        let split_at = (self.stack_drop + ini_sz.saturating_sub(1)).min(self.stack.len());
        let args = self.stack.split_off(split_at);
        let node = VmNode::node(kind, args);
        if node.tree_nodes() > self.max_tree_nodes {
            self.budget_exhausted = true;
            self.mk_unexpected_error(
                "syntax tree node budget exhausted".to_owned(),
                Vec::new(),
                true,
            );
            return;
        }
        self.push(node);
    }

    fn mk_error(&mut self, expected: &str) {
        self.error = Some(InterpError::new(
            self.pos,
            String::new(),
            vec![expected.to_owned()],
        ));
        self.push(VmNode::missing());
    }

    fn mk_unexpected_error(
        &mut self,
        unexpected: impl Into<String>,
        expected: Vec<String>,
        push_missing: bool,
    ) {
        self.error = Some(InterpError::new(self.pos, unexpected, expected));
        if push_missing {
            self.push(VmNode::missing());
        }
    }

    fn mk_lexical_error(
        &mut self,
        message: &'static str,
        expected: Vec<String>,
        push_missing: bool,
    ) {
        self.error = Some(InterpError::lexical(self.pos, message, expected));
        if push_missing {
            self.push(VmNode::missing());
        }
    }

    fn mk_eoi_error(&mut self, expected: &[String]) {
        self.mk_unexpected_error("unexpected end of input", expected.to_vec(), true);
    }

    fn mk_unexpected_token_errors(&mut self, expected: &[String], ini_pos: Option<usize>) {
        let tk = self.pop_or_missing();
        let pos = ini_pos.or_else(|| first_pos_of_vm(&tk)).unwrap_or(self.pos);
        self.pos = pos;
        let unexpected = match &*tk {
            VmSyntax::Ident { .. } => "unexpected identifier".to_owned(),
            VmSyntax::Atom { val, .. } => format!("unexpected token '{val}'"),
            _ => "unexpected token".to_owned(),
        };
        self.error = Some(InterpError::new(pos, unexpected, expected.to_vec()));
        self.push(VmNode::missing());
    }
}

fn builtin_category_behavior(cat: &Name) -> LeadingIdentBehavior {
    match cat.to_display_string().as_str() {
        "attr" => LeadingIdentBehavior::Symbol,
        "prio" | "stx" | "prec" | "tactic" => LeadingIdentBehavior::Both,
        _ => LeadingIdentBehavior::Default,
    }
}

/// Build `mkAntiquot cat.toString cat (anonymous := true) (isPseudoKind := true)`
/// (`Extension.lean:417-418`, `Basic.lean:1822-1833`).
fn build_category_antiquot_parser(cat: &Name) -> Arc<ParserOp> {
    build_mk_antiquot(&cat.to_display_string(), cat, true, true)
}

fn build_mk_antiquot(
    name: &str,
    kind: &Name,
    anonymous: bool,
    is_pseudo_kind: bool,
) -> Arc<ParserOp> {
    let mut full_kind = kind.clone();
    if is_pseudo_kind {
        full_kind = Name::str(full_kind, "pseudo");
    }
    full_kind = Name::str(full_kind, "antiquot");

    let colon = Arc::new(ParserOp::TokenWithAntiquot(Arc::new(ParserOp::Symbol(
        ":".to_owned(),
    ))));
    let name_sym = Arc::new(ParserOp::TokenWithAntiquot(Arc::new(
        ParserOp::NonReservedSymbol {
            sym: name.to_owned(),
            include_ident: false,
        },
    )));
    let name_p_core = Arc::new(ParserOp::Node(
        Name::from_components(["antiquotName"]),
        Arc::new(ParserOp::Seq(vec![
            Arc::new(ParserOp::CheckNoWsBefore(format!(
                "no space before ':{name}'"
            ))),
            colon,
            name_sym,
        ])),
    ));
    let name_p = if anonymous {
        Arc::new(ParserOp::OrElse(vec![
            name_p_core,
            Arc::new(ParserOp::Seq(vec![
                Arc::new(ParserOp::CheckNoImmediateColon),
                Arc::new(ParserOp::PushNone),
            ])),
        ]))
    } else {
        name_p_core
    };

    let dollar = Arc::new(ParserOp::TokenWithAntiquot(Arc::new(ParserOp::Symbol(
        "$".to_owned(),
    ))));
    let nested_expr = Arc::new(ParserOp::Node(
        Name::from_components(["antiquotNestedExpr"]),
        Arc::new(ParserOp::Seq(vec![
            Arc::new(ParserOp::Symbol("(".to_owned())),
            Arc::new(ParserOp::AdaptContext(
                ContextTransform::AddQuotDepth(-1),
                Arc::new(ParserOp::CategoryParser {
                    cat: Name::from_components(["term"]),
                    prec: 0,
                }),
            )),
            Arc::new(ParserOp::Symbol(")".to_owned())),
        ])),
    ));
    let antiquot_expr = Arc::new(ParserOp::OrElse(vec![
        Arc::new(ParserOp::Ident),
        Arc::new(ParserOp::Symbol("_".to_owned())),
        nested_expr,
    ]));

    let body = Arc::new(ParserOp::Atomic(Arc::new(ParserOp::Seq(vec![
        Arc::new(ParserOp::SetExpected {
            expected: Vec::new(),
            body: Arc::clone(&dollar),
        }),
        Arc::new(ParserOp::Many(Arc::new(ParserOp::Seq(vec![
            Arc::new(ParserOp::CheckNoWsBefore(String::new())),
            dollar,
        ])))),
        Arc::new(ParserOp::CheckNoWsBefore(
            "no space before spliced term".to_owned(),
        )),
        antiquot_expr,
        name_p,
    ]))));

    Arc::new(ParserOp::Seq(vec![
        Arc::new(ParserOp::CheckPrec(MAX_PREC)),
        Arc::new(ParserOp::Node(full_kind, body)),
        Arc::new(ParserOp::SetLhsPrec(MAX_PREC)),
    ]))
}

fn eval_ast(
    table: &BuiltinParserTable,
    def_index: &BTreeMap<Name, usize>,
    owner: &Name,
    ast: &CombinatorAst,
    env: &mut Vec<EvalVal>,
    depth: usize,
) -> Result<EvalVal, CompileError> {
    if depth > 128 {
        return Err(CompileError::DepthExceeded(owner.to_display_string()));
    }
    match ast {
        CombinatorAst::LitNat(n) => Ok(EvalVal::Nat(*n)),
        CombinatorAst::LitStr(s) => Ok(EvalVal::Str(s.clone())),
        CombinatorAst::LitName(n) => Ok(EvalVal::Name(n.clone())),
        CombinatorAst::LitBool(b) => Ok(EvalVal::Bool(*b)),
        CombinatorAst::LitChar(code) => Ok(EvalVal::Char(char::from_u32(*code).unwrap_or('\0'))),
        CombinatorAst::LitList(items) => {
            let mut vals = Vec::with_capacity(items.len());
            for item in items {
                vals.push(eval_ast(table, def_index, owner, item, env, depth + 1)?);
            }
            Ok(EvalVal::List(vals))
        }
        CombinatorAst::NoneVal => Ok(EvalVal::OptionNone),
        CombinatorAst::SomeVal(inner) => {
            let _ = eval_ast(table, def_index, owner, inner, env, depth + 1)?;
            Ok(EvalVal::OptionSome)
        }
        CombinatorAst::Var { idx, .. } => {
            if *idx >= env.len() {
                return Err(CompileError::UnboundVar {
                    owner: owner.to_display_string(),
                    idx: *idx,
                });
            }
            Ok(env[env.len() - 1 - *idx].clone())
        }
        CombinatorAst::Lam { body, .. } => Ok(EvalVal::Closure {
            body: Box::new((**body).clone()),
            env: env.clone(),
        }),
        CombinatorAst::Let { val, body, .. } => {
            let v = eval_ast(table, def_index, owner, val, env, depth + 1)?;
            env.push(v);
            let res = eval_ast(table, def_index, owner, body, env, depth + 1);
            env.pop();
            res
        }
        CombinatorAst::Seq(_, _) => eval_seq_spine(table, def_index, owner, ast, env, depth),
        CombinatorAst::OrElse(_, _) => eval_orelse_spine(table, def_index, owner, ast, env, depth),
        CombinatorAst::Append(lhs, rhs) => {
            let lv = eval_ast(table, def_index, owner, lhs, env, depth + 1)?;
            let rv = eval_ast(table, def_index, owner, rhs, env, depth + 1)?;
            match (lv, rv) {
                (EvalVal::Str(mut a), EvalVal::Str(b)) => {
                    a.push_str(&b);
                    Ok(EvalVal::Str(a))
                }
                (EvalVal::Name(a), EvalVal::Name(b)) => Ok(EvalVal::Name(append_name(a, &b))),
                _ => Err(CompileError::TypeMismatch {
                    owner: owner.to_display_string(),
                    detail: "unsupported Append operands".to_owned(),
                }),
            }
        }
        CombinatorAst::Beq(lhs, rhs) => {
            let lv = eval_ast(table, def_index, owner, lhs, env, depth + 1)?;
            let rv = eval_ast(table, def_index, owner, rhs, env, depth + 1)?;
            Ok(EvalVal::Bool(eval_val_eq(&lv, &rv)))
        }
        CombinatorAst::BoolOr(lhs, rhs) => {
            let lv = eval_ast(table, def_index, owner, lhs, env, depth + 1)?;
            let rv = eval_ast(table, def_index, owner, rhs, env, depth + 1)?;
            match (lv, rv) {
                (EvalVal::Bool(a), EvalVal::Bool(b)) => Ok(EvalVal::Bool(a || b)),
                _ => Err(CompileError::TypeMismatch {
                    owner: owner.to_display_string(),
                    detail: "BoolOr requires Bool operands".to_owned(),
                }),
            }
        }
        CombinatorAst::Ite {
            cond,
            then_branch,
            else_branch,
        } => {
            let cv = eval_ast(table, def_index, owner, cond, env, depth + 1)?;
            let b = expect_bool(owner, cv)?;
            if b {
                eval_ast(table, def_index, owner, then_branch, env, depth + 1)
            } else {
                eval_ast(table, def_index, owner, else_branch, env, depth + 1)
            }
        }
        CombinatorAst::Const(name) => eval_const(def_index, owner, name),
        CombinatorAst::Call { func, args } => {
            eval_call(table, def_index, owner, func, args, env, depth + 1)
        }
        CombinatorAst::App { func, args } => {
            let mut fv = eval_ast(table, def_index, owner, func, env, depth + 1)?;
            for arg in args {
                let av = eval_ast(table, def_index, owner, arg, env, depth + 1)?;
                fv = apply_closure(table, def_index, owner, fv, av, depth + 1)?;
            }
            Ok(fv)
        }
    }
}

#[inline(never)]
fn eval_seq_spine(
    table: &BuiltinParserTable,
    def_index: &BTreeMap<Name, usize>,
    owner: &Name,
    ast: &CombinatorAst,
    env: &mut Vec<EvalVal>,
    depth: usize,
) -> Result<EvalVal, CompileError> {
    let mut parts: Vec<(&CombinatorAst, bool)> = Vec::new();
    let mut stack: Vec<(&CombinatorAst, bool)> = vec![(ast, false)];
    while let Some((node, is_rhs)) = stack.pop() {
        if let CombinatorAst::Seq(l, r) = node {
            stack.push((r, true));
            stack.push((l, false));
        } else {
            parts.push((node, is_rhs));
        }
    }
    let mut items = Vec::with_capacity(parts.len());
    for (node, is_rhs) in parts {
        let v = if is_rhs {
            eval_thunk_or_ast(table, def_index, owner, node, env, depth + 1)?
        } else {
            eval_ast(table, def_index, owner, node, env, depth + 1)?
        };
        let p = expect_parser(owner, v)?;
        match p.as_ref() {
            ParserOp::Seq(xs) => items.extend(xs.iter().cloned()),
            _ => items.push(p),
        }
    }
    Ok(EvalVal::Parser(Arc::new(ParserOp::Seq(items))))
}

#[inline(never)]
fn eval_orelse_spine(
    table: &BuiltinParserTable,
    def_index: &BTreeMap<Name, usize>,
    owner: &Name,
    ast: &CombinatorAst,
    env: &mut Vec<EvalVal>,
    depth: usize,
) -> Result<EvalVal, CompileError> {
    let mut parts: Vec<(&CombinatorAst, bool)> = Vec::new();
    let mut stack: Vec<(&CombinatorAst, bool)> = vec![(ast, false)];
    while let Some((node, is_rhs)) = stack.pop() {
        if let CombinatorAst::OrElse(l, r) = node {
            stack.push((r, true));
            stack.push((l, false));
        } else {
            parts.push((node, is_rhs));
        }
    }
    let mut items = Vec::with_capacity(parts.len());
    for (node, is_rhs) in parts {
        let v = if is_rhs {
            eval_thunk_or_ast(table, def_index, owner, node, env, depth + 1)?
        } else {
            eval_ast(table, def_index, owner, node, env, depth + 1)?
        };
        let p = expect_parser(owner, v)?;
        match p.as_ref() {
            ParserOp::OrElse(xs) => items.extend(xs.iter().cloned()),
            _ => items.push(p),
        }
    }
    Ok(EvalVal::Parser(Arc::new(ParserOp::OrElse(items))))
}

fn eval_thunk_or_ast(
    table: &BuiltinParserTable,
    def_index: &BTreeMap<Name, usize>,
    owner: &Name,
    ast: &CombinatorAst,
    env: &mut Vec<EvalVal>,
    depth: usize,
) -> Result<EvalVal, CompileError> {
    if let CombinatorAst::Lam { body, .. } = ast {
        env.push(EvalVal::Unit);
        let res = eval_ast(table, def_index, owner, body, env, depth + 1);
        env.pop();
        res
    } else {
        eval_ast(table, def_index, owner, ast, env, depth + 1)
    }
}

fn apply_closure(
    table: &BuiltinParserTable,
    def_index: &BTreeMap<Name, usize>,
    owner: &Name,
    func: EvalVal,
    arg: EvalVal,
    depth: usize,
) -> Result<EvalVal, CompileError> {
    match func {
        EvalVal::Closure { body, mut env, .. } => {
            env.push(arg);
            eval_ast(table, def_index, owner, &body, &mut env, depth + 1)
        }
        _ => Err(CompileError::TypeMismatch {
            owner: owner.to_display_string(),
            detail: "attempted to apply non-closure".to_owned(),
        }),
    }
}

#[inline(never)]
fn eval_const(
    def_index: &BTreeMap<Name, usize>,
    owner: &Name,
    name: &Name,
) -> Result<EvalVal, CompileError> {
    if let Some(&id) = def_index.get(name) {
        return Ok(EvalVal::Parser(Arc::new(ParserOp::Ref(id))));
    }
    let s = name.to_display_string();
    match s.as_str() {
        // Primitive parser constants
        "Lean.Parser.skip" => Ok(EvalVal::Parser(Arc::new(ParserOp::Skip))),
        "Lean.Parser.pushNone" => Ok(EvalVal::Parser(Arc::new(ParserOp::PushNone))),
        "Lean.Parser.eoi" => Ok(EvalVal::Parser(Arc::new(ParserOp::Eoi))),
        "Lean.Parser.identNoAntiquot" => Ok(EvalVal::Parser(Arc::new(ParserOp::Ident))),
        "Lean.Parser.rawIdentNoAntiquot" => Ok(EvalVal::Parser(Arc::new(ParserOp::RawIdent))),
        "Lean.Parser.numLitNoAntiquot" => Ok(EvalVal::Parser(Arc::new(ParserOp::NumLit))),
        "Lean.Parser.hexnumNoAntiquot" => Ok(EvalVal::Parser(Arc::new(ParserOp::HexNum))),
        "Lean.Parser.scientificLitNoAntiquot" => {
            Ok(EvalVal::Parser(Arc::new(ParserOp::ScientificLit)))
        }
        "Lean.Parser.strLitNoAntiquot" => Ok(EvalVal::Parser(Arc::new(ParserOp::StrLit))),
        "Lean.Parser.charLitNoAntiquot" => Ok(EvalVal::Parser(Arc::new(ParserOp::CharLit))),
        "Lean.Parser.nameLitNoAntiquot" => Ok(EvalVal::Parser(Arc::new(ParserOp::NameLit))),
        "Lean.Parser.fieldIdx" => Ok(EvalVal::Parser(Arc::new(ParserOp::FieldIdx))),
        "Lean.Parser.hygieneInfoNoAntiquot" => Ok(EvalVal::Parser(Arc::new(ParserOp::HygieneInfo))),
        "Lean.Parser.checkNoImmediateColon" => {
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckNoImmediateColon)))
        }
        "Lean.Parser.Command.commentBody" => Ok(EvalVal::Parser(Arc::new(ParserOp::CommentBody))),
        "Lean.Parser.Command.versoCommentBody" => {
            Ok(EvalVal::Parser(Arc::new(ParserOp::VersoCommentBody)))
        }
        "Lean.Parser.instInhabitedParser.default" => {
            Ok(EvalVal::Parser(Arc::new(ParserOp::InhabitedDefault)))
        }
        // Precedence & kind constants
        "Lean.Parser.maxPrec" => Ok(EvalVal::Nat(u64::from(MAX_PREC))),
        "Lean.Parser.argPrec" => Ok(EvalVal::Nat(u64::from(ARG_PREC))),
        "Lean.Parser.leadPrec" => Ok(EvalVal::Nat(u64::from(LEAD_PREC))),
        "Lean.Parser.minPrec" => Ok(EvalVal::Nat(u64::from(MIN_PREC))),
        "Lean.nullKind" => Ok(EvalVal::Name(Name::from_components(["null"]))),
        "Lean.identKind" => Ok(EvalVal::Name(Name::from_components(["ident"]))),
        "Lean.numLitKind" => Ok(EvalVal::Name(Name::from_components(["num"]))),
        "Lean.scientificLitKind" => Ok(EvalVal::Name(Name::from_components(["scientific"]))),
        "Lean.strLitKind" => Ok(EvalVal::Name(Name::from_components(["str"]))),
        "Lean.charLitKind" => Ok(EvalVal::Name(Name::from_components(["char"]))),
        "Lean.nameLitKind" => Ok(EvalVal::Name(Name::from_components(["name"]))),
        "Lean.hexnumKind" => Ok(EvalVal::Name(Name::from_components(["hexnum"]))),
        "Lean.hygieneInfoKind" => Ok(EvalVal::Name(Name::from_components(["hygieneInfo"]))),
        "Lean.groupKind" => Ok(EvalVal::Name(Name::from_components(["group"]))),
        "Lean.interpolatedStrKind" => Ok(EvalVal::Name(Name::from_components([
            "interpolatedStrKind",
        ]))),
        // Syntax predicates & recovery helpers
        "Lean.Parser.Term.isIdent" => Ok(EvalVal::SyntaxPred(SyntaxPred::IsIdent)),
        "Lean.Parser.Term.isIdentOrDotIdentOrProj" => {
            Ok(EvalVal::SyntaxPred(SyntaxPred::IsIdentOrDotIdentOrProj))
        }
        "_private.Lean.Parser.Command.0.Lean.Parser.Command.skipUntilWsOrDelim" => Ok(
            EvalVal::Parser(Arc::new(ParserOp::SkipUntil(CharPred::WhitespaceOrDelim))),
        ),
        "Char" => Ok(EvalVal::Unit),
        _ => Err(CompileError::UnresolvedDecl(format!(
            "{s} (referenced by {})",
            owner.to_display_string()
        ))),
    }
}

#[inline(never)]
fn eval_call(
    table: &BuiltinParserTable,
    def_index: &BTreeMap<Name, usize>,
    owner: &Name,
    func: &Name,
    args: &[CombinatorAst],
    env: &mut Vec<EvalVal>,
    depth: usize,
) -> Result<EvalVal, CompileError> {
    let fname = func.to_display_string();

    // Non-strict special forms whose AST arguments cannot be evaluated eagerly.
    if fname == "Lean.Parser.recover'" && args.len() == 2 {
        let p = expect_parser(
            owner,
            eval_ast(table, def_index, owner, &args[0], env, depth)?,
        )?;
        let h = eval_thunk_or_ast(table, def_index, owner, &args[1], env, depth)?;
        let hp = expect_parser(owner, h)?;
        return Ok(EvalVal::Parser(Arc::new(ParserOp::Recover {
            parser: p,
            handler: hp,
        })));
    }
    if fname == "_private.Lean.Parser.Command.0.Lean.Parser.Command.skipUntil" && args.len() == 1 {
        let pred = extract_skip_until_pred(&args[0]);
        return Ok(EvalVal::Parser(Arc::new(ParserOp::SkipUntil(pred))));
    }

    // Strict intercepts take precedence over `table.generatables` entries.
    if is_strict_intercept_call(&fname, args.len()) {
        let mut vals = Vec::with_capacity(args.len());
        for arg in args {
            vals.push(eval_ast(table, def_index, owner, arg, env, depth)?);
        }
        return eval_primitive_call(owner, &fname, vals);
    }

    // Parameterized (and eta-reduced) generatable helpers in the table.
    if let Some(helper) = table.generatables.get(func) {
        if helper.params.len() <= args.len() {
            let mut helper_env = Vec::with_capacity(helper.params.len());
            for arg in &args[..helper.params.len()] {
                helper_env.push(eval_ast(table, def_index, owner, arg, env, depth)?);
            }
            let mut val = eval_ast(
                table,
                def_index,
                &helper.name,
                &helper.ast,
                &mut helper_env,
                depth,
            )?;
            for extra in &args[helper.params.len()..] {
                let av = eval_ast(table, def_index, owner, extra, env, depth)?;
                val = apply_closure(table, def_index, owner, val, av, depth)?;
            }
            return Ok(val);
        }
        if args.is_empty()
            && let Some(&id) = def_index.get(func)
        {
            return Ok(EvalVal::Parser(Arc::new(ParserOp::Ref(id))));
        }
        return Err(CompileError::ArityMismatch {
            owner: owner.to_display_string(),
            func: fname,
        });
    }

    // Evaluate arguments for primitive combinators & external functions.
    let mut vals = Vec::with_capacity(args.len());
    for arg in args {
        vals.push(eval_ast(table, def_index, owner, arg, env, depth)?);
    }
    eval_primitive_call(owner, &fname, vals)
}

fn is_strict_intercept_call(fname: &str, arity: usize) -> bool {
    matches!(
        (fname, arity),
        ("Lean.Parser.withForbidden", 2)
            | ("Lean.Parser.withoutForbidden", 1)
            | ("Lean.Parser.withoutPosition", 1)
            | ("Lean.Parser.suppressInsideQuot", 1)
            | ("Lean.Parser.incQuotDepth", 1)
            | ("Lean.Parser.decQuotDepth", 1)
            | ("_private.Lean.Parser.Basic.0.Lean.Parser.addQuotDepth", 2)
            | ("Lean.Parser.many1Unbox", 1)
            | ("Lean.Parser.recover", 2)
            | ("Lean.Doc.Parser.ifVerso", 2)
            | ("Lean.Doc.Parser.ifVersoModuleDocs", 2)
            | ("Lean.Doc.Parser.withoutVersoSyntax", 1)
    )
}

#[inline(never)]
fn eval_primitive_call(
    owner: &Name,
    fname: &str,
    mut vals: Vec<EvalVal>,
) -> Result<EvalVal, CompileError> {
    match fname {
        "Lean.Parser.withForbidden" if vals.len() == 2 => {
            let tk = expect_str(owner, vals.remove(0))?;
            let p = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::WithForbidden(tk),
                p,
            ))))
        }
        "Lean.Parser.withoutForbidden" if vals.len() == 1 => {
            let p = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::WithoutForbidden,
                p,
            ))))
        }
        "Lean.Parser.withoutPosition" if vals.len() == 1 => {
            let p = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::WithoutPosition,
                p,
            ))))
        }
        "Lean.Parser.suppressInsideQuot" if vals.len() == 1 => {
            let p = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::SuppressInsideQuot,
                p,
            ))))
        }
        "Lean.Parser.incQuotDepth" if vals.len() == 1 => {
            let p = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::AddQuotDepth(1),
                p,
            ))))
        }
        "Lean.Parser.decQuotDepth" if vals.len() == 1 => {
            let p = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::AddQuotDepth(-1),
                p,
            ))))
        }
        "_private.Lean.Parser.Basic.0.Lean.Parser.addQuotDepth" if vals.len() == 2 => {
            let delta = expect_int(owner, vals.remove(0))?;
            let p = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::AddQuotDepth(delta as i32),
                p,
            ))))
        }
        "Lean.Parser.many1Unbox" if vals.len() == 1 => {
            let p = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::Many1Unbox(p))))
        }
        "Lean.Parser.recover" if vals.len() == 2 => {
            let p = expect_parser(owner, vals.remove(0))?;
            let h = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::Recover {
                parser: p,
                handler: h,
            })))
        }
        "Lean.Doc.Parser.ifVerso" if vals.len() == 2 => {
            let verso = expect_parser(owner, vals.remove(0))?;
            let plain = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::IfVerso {
                module_docs: false,
                verso,
                plain,
            })))
        }
        "Lean.Doc.Parser.ifVersoModuleDocs" if vals.len() == 2 => {
            let verso = expect_parser(owner, vals.remove(0))?;
            let plain = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::IfVerso {
                module_docs: true,
                verso,
                plain,
            })))
        }
        "Lean.Doc.Parser.withoutVersoSyntax" if vals.len() == 1 => {
            let inner = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::WithoutVersoSyntax(
                inner,
            ))))
        }
        // Core primitive combinators
        "Lean.Parser.withAntiquot" if vals.len() == 2 => {
            let antiq = expect_parser(owner, vals.remove(0))?;
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::WithAntiquot {
                antiquot: antiq,
                body,
                is_cat: false,
            })))
        }
        "Lean.Parser.withCache" if vals.len() == 2 => {
            let name = expect_name(owner, vals.remove(0))?;
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::WithCache(name, body))))
        }
        "Lean.Parser.withResetCache" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::WithResetCache(body))))
        }
        "Lean.Parser.atomic" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::Atomic(body))))
        }
        "Lean.Parser.node" if vals.len() == 2 => {
            let kind = expect_name(owner, vals.remove(0))?;
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::Node(kind, body))))
        }
        "Lean.Parser.trailingNodeAux" if vals.len() == 2 => {
            let kind = expect_name(owner, vals.remove(0))?;
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::TrailingNodeAux(
                kind, body,
            ))))
        }
        "Lean.Parser.symbolNoAntiquot" if vals.len() == 1 => {
            let sym = expect_str(owner, vals.remove(0))?.trim_ascii().to_owned();
            Ok(EvalVal::Parser(Arc::new(ParserOp::Symbol(sym))))
        }
        "Lean.Parser.nonReservedSymbolNoAntiquot" if vals.len() == 2 => {
            let sym = expect_str(owner, vals.remove(0))?.trim_ascii().to_owned();
            let include_ident = expect_bool(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::NonReservedSymbol {
                sym,
                include_ident,
            })))
        }
        "Lean.Parser.unicodeSymbolNoAntiquot" if vals.len() == 3 => {
            let sym = expect_str(owner, vals.remove(0))?.trim_ascii().to_owned();
            let ascii_sym = expect_str(owner, vals.remove(0))?.trim_ascii().to_owned();
            let _preserve_pp = expect_bool(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::UnicodeSymbol {
                sym,
                ascii_sym,
            })))
        }
        "Lean.Parser.rawCh" if vals.len() == 2 => {
            let ch = expect_char(owner, vals.remove(0))?;
            let trailing_ws = expect_bool(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::RawCh {
                ch,
                trailing_ws,
            })))
        }
        "Lean.Parser.tokenWithAntiquot" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::TokenWithAntiquot(body))))
        }
        "Lean.Parser.withAntiquotSuffixSplice" if vals.len() == 3 => {
            let kind = expect_name(owner, vals.remove(0))?;
            let body = expect_parser(owner, vals.remove(0))?;
            let suffix = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(
                ParserOp::WithAntiquotSuffixSplice { kind, body, suffix },
            )))
        }
        "Lean.Parser.withoutInfo" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::WithoutInfo(body))))
        }
        "Lean.Parser.setExpected" if vals.len() == 2 => {
            let list = expect_str_list(owner, vals.remove(0))?;
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::SetExpected {
                expected: list,
                body,
            })))
        }
        "Lean.Parser.optionalNoAntiquot" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::Optional(body))))
        }
        "Lean.Parser.manyNoAntiquot" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::Many(body))))
        }
        "Lean.Parser.many1NoAntiquot" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::Many1(body))))
        }
        "Lean.Parser.sepByNoAntiquot" if vals.len() == 3 => {
            let elem = expect_parser(owner, vals.remove(0))?;
            let sep = expect_parser(owner, vals.remove(0))?;
            let allow_trailing = expect_bool(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::SepBy {
                elem,
                sep,
                allow_trailing,
            })))
        }
        "Lean.Parser.sepBy1NoAntiquot" if vals.len() == 3 => {
            let elem = expect_parser(owner, vals.remove(0))?;
            let sep = expect_parser(owner, vals.remove(0))?;
            let allow_trailing = expect_bool(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::SepBy1 {
                elem,
                sep,
                allow_trailing,
            })))
        }
        "Lean.Parser.lookahead" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::Lookahead(body))))
        }
        "Lean.Parser.notFollowedBy" if vals.len() == 2 => {
            let body = expect_parser(owner, vals.remove(0))?;
            let msg = expect_str(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::NotFollowedBy(
                body, msg,
            ))))
        }
        "Lean.Parser.checkPrec" if vals.len() == 1 => {
            let prec = expect_nat(owner, vals.remove(0))? as u32;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckPrec(prec))))
        }
        "Lean.Parser.checkLhsPrec" if vals.len() == 1 => {
            let prec = expect_nat(owner, vals.remove(0))? as u32;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckLhsPrec(prec))))
        }
        "Lean.Parser.setLhsPrec" if vals.len() == 1 => {
            let prec = expect_nat(owner, vals.remove(0))? as u32;
            Ok(EvalVal::Parser(Arc::new(ParserOp::SetLhsPrec(prec))))
        }
        "Lean.Parser.checkColEq" if vals.len() == 1 => {
            let msg = expect_str(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckColEq(msg))))
        }
        "Lean.Parser.checkColGe" if vals.len() == 1 => {
            let msg = expect_str(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckColGe(msg))))
        }
        "Lean.Parser.checkColGt" if vals.len() == 1 => {
            let msg = expect_str(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckColGt(msg))))
        }
        "Lean.Parser.checkLineEq" if vals.len() == 1 => {
            let msg = expect_str(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckLineEq(msg))))
        }
        "Lean.Parser.checkWsBefore" if vals.len() == 1 => {
            let msg = expect_str(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckWsBefore(msg))))
        }
        "Lean.Parser.checkNoWsBefore" if vals.len() == 1 => {
            let msg = expect_str(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckNoWsBefore(msg))))
        }
        "Lean.Parser.checkLinebreakBefore" if vals.len() == 1 => {
            let msg = expect_str(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckLinebreakBefore(
                msg,
            ))))
        }
        "Lean.Parser.checkStackTop" if vals.len() == 2 => {
            let pred = match vals.remove(0) {
                EvalVal::SyntaxPred(p) => p,
                _ => {
                    return Err(CompileError::TypeMismatch {
                        owner: owner.to_display_string(),
                        detail: "checkStackTop expects SyntaxPred".to_owned(),
                    });
                }
            };
            let msg = expect_str(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CheckStackTop {
                pred,
                msg,
            })))
        }
        "Lean.Parser.withPosition" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::WithPosition(body))))
        }
        "Lean.Parser.withPositionAfterLinebreak" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(
                ParserOp::WithPositionAfterLinebreak(body),
            )))
        }
        "Lean.Parser.withOpen" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::WithOpen(body))))
        }
        "Lean.Parser.withOpenDecl" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::WithOpenDecl(body))))
        }
        "Lean.Parser.categoryParser" if vals.len() == 2 => {
            let cat = expect_name(owner, vals.remove(0))?;
            let prec = expect_nat(owner, vals.remove(0))? as u32;
            Ok(EvalVal::Parser(Arc::new(ParserOp::CategoryParser {
                cat,
                prec,
            })))
        }
        "Lean.Parser.parserOfStack" if vals.len() == 2 => {
            let offset = expect_nat(owner, vals.remove(0))? as usize;
            let prec = expect_nat(owner, vals.remove(0))? as u32;
            Ok(EvalVal::Parser(Arc::new(ParserOp::ParserOfStack {
                offset,
                prec,
            })))
        }
        "Lean.Parser.interpolatedStrNoAntiquot" if vals.len() == 1 => {
            let body = expect_parser(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::InterpolatedStr(body))))
        }
        "Lean.Parser.errorAtSavedPos" if vals.len() == 2 => {
            let msg = expect_str(owner, vals.remove(0))?;
            let delta = expect_bool(owner, vals.remove(0))?;
            Ok(EvalVal::Parser(Arc::new(ParserOp::ErrorAtSavedPos {
                msg,
                delta,
            })))
        }
        // Small external pure helpers used by parser helpers
        "String.trimAscii" if vals.len() == 1 => {
            let s = expect_str(owner, vals.remove(0))?;
            Ok(EvalVal::Str(s.trim_ascii().to_owned()))
        }
        "String.Slice.copy" if vals.len() == 1 => Ok(vals.remove(0)),
        "Eq" if vals.len() == 2 => Ok(EvalVal::Bool(eval_val_eq(&vals[0], &vals[1]))),
        "Decidable.decide" if vals.len() == 1 => Ok(vals.remove(0)),
        "Neg.neg" if vals.len() == 1 => match vals.remove(0) {
            EvalVal::Nat(n) => Ok(EvalVal::Int(-(n as i64))),
            EvalVal::Int(n) => Ok(EvalVal::Int(-n)),
            _ => Err(CompileError::TypeMismatch {
                owner: owner.to_display_string(),
                detail: "Neg.neg expects Nat or Int".to_owned(),
            }),
        },
        "id" if vals.is_empty() => Ok(EvalVal::Closure {
            body: Box::new(CombinatorAst::Var {
                name: "x".to_owned(),
                idx: 0,
            }),
            env: Vec::new(),
        }),
        "id" if vals.len() == 1 => Ok(vals.remove(0)),
        _ => Err(CompileError::UnresolvedDecl(format!(
            "call {fname} (arity {}) inside {}",
            vals.len(),
            owner.to_display_string()
        ))),
    }
}

fn extract_skip_until_pred(ast: &CombinatorAst) -> CharPred {
    let mut chars = Vec::new();
    collect_char_lits(ast, &mut chars);
    if chars.is_empty() {
        CharPred::IsWhitespace
    } else {
        CharPred::WhitespaceOrChars(chars)
    }
}

fn collect_char_lits(ast: &CombinatorAst, out: &mut Vec<char>) {
    match ast {
        CombinatorAst::LitChar(c) => {
            if let Some(ch) = char::from_u32(*c)
                && !out.contains(&ch)
            {
                out.push(ch);
            }
        }
        CombinatorAst::LitList(items) => {
            for item in items {
                collect_char_lits(item, out);
            }
        }
        CombinatorAst::Call { args, .. } => {
            for a in args {
                collect_char_lits(a, out);
            }
        }
        CombinatorAst::Lam { body, .. } | CombinatorAst::SomeVal(body) => {
            collect_char_lits(body, out);
        }
        CombinatorAst::Seq(a, b)
        | CombinatorAst::OrElse(a, b)
        | CombinatorAst::Append(a, b)
        | CombinatorAst::Beq(a, b)
        | CombinatorAst::BoolOr(a, b) => {
            collect_char_lits(a, out);
            collect_char_lits(b, out);
        }
        CombinatorAst::Let { val, body, .. } => {
            collect_char_lits(val, out);
            collect_char_lits(body, out);
        }
        CombinatorAst::Ite {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_char_lits(cond, out);
            collect_char_lits(then_branch, out);
            collect_char_lits(else_branch, out);
        }
        CombinatorAst::App { func, args } => {
            collect_char_lits(func, out);
            for a in args {
                collect_char_lits(a, out);
            }
        }
        _ => {}
    }
}

fn compute_def_first_tokens(
    id: usize,
    raw_ops: &[(Name, Arc<ParserOp>)],
    cache: &mut [Option<FirstTokens>],
    visiting: &mut [bool],
) -> FirstTokens {
    if let Some(ft) = &cache[id] {
        return ft.clone();
    }
    if visiting[id] {
        return FirstTokens::Unknown;
    }
    visiting[id] = true;
    let ft = compute_op_first_tokens(&raw_ops[id].1, raw_ops, cache, visiting);
    visiting[id] = false;
    cache[id] = Some(ft.clone());
    ft
}

fn compute_op_first_tokens(
    op: &ParserOp,
    raw_ops: &[(Name, Arc<ParserOp>)],
    cache: &mut [Option<FirstTokens>],
    visiting: &mut [bool],
) -> FirstTokens {
    match op {
        ParserOp::Ref(id) => compute_def_first_tokens(*id, raw_ops, cache, visiting),
        ParserOp::Symbol(sym) => FirstTokens::Tokens(vec![sym.clone()]),
        ParserOp::NonReservedSymbol { sym, include_ident } => {
            if *include_ident {
                FirstTokens::Tokens(vec![sym.clone(), "ident".to_owned()])
            } else {
                FirstTokens::Tokens(vec![sym.clone()])
            }
        }
        ParserOp::UnicodeSymbol { sym, ascii_sym } => {
            FirstTokens::Tokens(vec![sym.clone(), ascii_sym.clone()])
        }
        ParserOp::Ident => FirstTokens::Tokens(vec!["ident".to_owned()]),
        ParserOp::NumLit => FirstTokens::Tokens(vec!["num".to_owned()]),
        ParserOp::HexNum => FirstTokens::Tokens(vec!["hexnum".to_owned()]),
        ParserOp::ScientificLit => FirstTokens::Tokens(vec!["scientific".to_owned()]),
        ParserOp::StrLit => FirstTokens::Tokens(vec!["str".to_owned()]),
        ParserOp::CharLit => FirstTokens::Tokens(vec!["char".to_owned()]),
        ParserOp::NameLit => FirstTokens::Tokens(vec!["name".to_owned()]),
        ParserOp::FieldIdx => FirstTokens::Tokens(vec!["fieldIdx".to_owned()]),
        ParserOp::InterpolatedStr(_) => FirstTokens::Tokens(vec!["interpolatedStr".to_owned()]),
        // Exact `epsilonInfo` primitives from `Lean/Parser/Basic.lean`
        ParserOp::Skip
        | ParserOp::HygieneInfo
        | ParserOp::CheckPrec(_)
        | ParserOp::CheckLhsPrec(_)
        | ParserOp::SetLhsPrec(_)
        | ParserOp::CheckColGe(_)
        | ParserOp::CheckWsBefore(_)
        | ParserOp::CheckNoWsBefore(_)
        | ParserOp::CheckLinebreakBefore(_)
        | ParserOp::CheckStackTop { .. } => FirstTokens::Epsilon,
        // Combinators that inherit inner `firstTokens`
        ParserOp::Node(_, p)
        | ParserOp::TrailingNodeAux(_, p)
        | ParserOp::Atomic(p)
        | ParserOp::Lookahead(p)
        | ParserOp::Many1(p)
        | ParserOp::SepBy1 { elem: p, .. }
        | ParserOp::WithPosition(p)
        | ParserOp::WithPositionAfterLinebreak(p)
        | ParserOp::AdaptContext(_, p)
        | ParserOp::WithCache(_, p)
        | ParserOp::WithResetCache(p)
        | ParserOp::WithOpen(p)
        | ParserOp::WithOpenDecl(p)
        | ParserOp::WithoutVersoSyntax(p)
        | ParserOp::SetExpected { body: p, .. }
        | ParserOp::TokenWithAntiquot(p)
        | ParserOp::Recover { parser: p, .. } => {
            compute_op_first_tokens(p, raw_ops, cache, visiting)
        }
        ParserOp::Optional(p) => compute_op_first_tokens(p, raw_ops, cache, visiting).to_optional(),
        ParserOp::Seq(steps) => {
            let mut acc = FirstTokens::Epsilon;
            for step in steps {
                let f = compute_op_first_tokens(step, raw_ops, cache, visiting);
                acc = acc.seq(&f);
            }
            acc
        }
        ParserOp::WithAntiquotSuffixSplice {
            body: a, suffix: b, ..
        } => {
            let fa = compute_op_first_tokens(a, raw_ops, cache, visiting);
            let fb = compute_op_first_tokens(b, raw_ops, cache, visiting);
            fa.seq(&fb)
        }
        ParserOp::OrElse(alts) => {
            let Some((first, rest)) = alts.split_first() else {
                return FirstTokens::Unknown;
            };
            let mut acc = compute_op_first_tokens(first, raw_ops, cache, visiting);
            for alt in rest {
                let f = compute_op_first_tokens(alt, raw_ops, cache, visiting);
                acc = acc.merge(&f);
            }
            acc
        }
        ParserOp::WithAntiquot {
            antiquot: a,
            body: b,
            ..
        } => {
            let fa = compute_op_first_tokens(a, raw_ops, cache, visiting);
            let fb = compute_op_first_tokens(b, raw_ops, cache, visiting);
            fa.merge(&fb)
        }
        ParserOp::IfVerso { verso, plain, .. } => {
            let fv = compute_op_first_tokens(verso, raw_ops, cache, visiting);
            let fp = compute_op_first_tokens(plain, raw_ops, cache, visiting);
            fv.merge(&fp)
        }
        // `FirstTokens.unknown` primitives (exact match to `Basic.lean`)
        ParserOp::PushNone
        | ParserOp::Eoi
        | ParserOp::RawCh { .. }
        | ParserOp::RawIdent
        | ParserOp::CommentBody
        | ParserOp::VersoCommentBody
        | ParserOp::Many(_)
        | ParserOp::Many1Unbox(_)
        | ParserOp::SepBy { .. }
        | ParserOp::NotFollowedBy(_, _)
        | ParserOp::WithoutInfo(_)
        | ParserOp::CheckColEq(_)
        | ParserOp::CheckColGt(_)
        | ParserOp::CheckLineEq(_)
        | ParserOp::CheckNoImmediateColon
        | ParserOp::CategoryParser { .. }
        | ParserOp::ParserOfStack { .. }
        | ParserOp::SkipUntil(_)
        | ParserOp::ErrorAtSavedPos { .. }
        | ParserOp::InhabitedDefault => FirstTokens::Unknown,
    }
}

fn extract_header_prelude_and_imports(header: &Syntax) -> (bool, Vec<Name>) {
    let Syntax::Node { args, .. } = header else {
        return (false, Vec::new());
    };
    let prelude = matches!(
        args.get(1),
        Some(Syntax::Node { args: items, .. }) if !items.is_empty()
    );
    let mut imports = Vec::new();
    if let Some(Syntax::Node {
        args: import_nodes, ..
    }) = args.get(2)
    {
        for import in import_nodes {
            if let Syntax::Node { args: parts, .. } = import
                && let Some(Syntax::Ident { val, .. }) = parts.get(4)
            {
                imports.push(val.clone());
            }
        }
    }
    (prelude, imports)
}

fn declare_command_or_in(fg: &mut crate::extensions::FileGrammar, cmd: &Syntax) {
    let _ = fg.declare(cmd);
    if let Syntax::Node { kind, args, .. } = cmd
        && *kind == Name::from_components(["Lean", "Parser", "Command", "in"])
        && let Some(rhs) = args.get(2)
    {
        declare_command_or_in(fg, rhs);
    }
}

fn expect_parser(owner: &Name, v: EvalVal) -> Result<Arc<ParserOp>, CompileError> {
    match v {
        EvalVal::Parser(p) => Ok(p),
        _ => Err(CompileError::TypeMismatch {
            owner: owner.to_display_string(),
            detail: "expected Parser".to_owned(),
        }),
    }
}

fn expect_str(owner: &Name, v: EvalVal) -> Result<String, CompileError> {
    match v {
        EvalVal::Str(s) => Ok(s),
        _ => Err(CompileError::TypeMismatch {
            owner: owner.to_display_string(),
            detail: "expected String".to_owned(),
        }),
    }
}

fn expect_nat(owner: &Name, v: EvalVal) -> Result<u64, CompileError> {
    match v {
        EvalVal::Nat(n) => Ok(n),
        EvalVal::Int(n) if n >= 0 => Ok(n as u64),
        _ => Err(CompileError::TypeMismatch {
            owner: owner.to_display_string(),
            detail: "expected Nat".to_owned(),
        }),
    }
}

fn expect_int(owner: &Name, v: EvalVal) -> Result<i64, CompileError> {
    match v {
        EvalVal::Int(n) => Ok(n),
        EvalVal::Nat(n) => Ok(n as i64),
        _ => Err(CompileError::TypeMismatch {
            owner: owner.to_display_string(),
            detail: "expected Int".to_owned(),
        }),
    }
}

fn expect_bool(owner: &Name, v: EvalVal) -> Result<bool, CompileError> {
    match v {
        EvalVal::Bool(b) => Ok(b),
        _ => Err(CompileError::TypeMismatch {
            owner: owner.to_display_string(),
            detail: "expected Bool".to_owned(),
        }),
    }
}

fn expect_char(owner: &Name, v: EvalVal) -> Result<char, CompileError> {
    match v {
        EvalVal::Char(c) => Ok(c),
        _ => Err(CompileError::TypeMismatch {
            owner: owner.to_display_string(),
            detail: "expected Char".to_owned(),
        }),
    }
}

fn expect_name(owner: &Name, v: EvalVal) -> Result<Name, CompileError> {
    match v {
        EvalVal::Name(n) => Ok(n),
        _ => Err(CompileError::TypeMismatch {
            owner: owner.to_display_string(),
            detail: "expected Name".to_owned(),
        }),
    }
}

fn expect_str_list(owner: &Name, v: EvalVal) -> Result<Vec<String>, CompileError> {
    match v {
        EvalVal::List(items) => {
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                out.push(expect_str(owner, item)?);
            }
            Ok(out)
        }
        _ => Err(CompileError::TypeMismatch {
            owner: owner.to_display_string(),
            detail: "expected List String".to_owned(),
        }),
    }
}

fn eval_val_eq(a: &EvalVal, b: &EvalVal) -> bool {
    match (a, b) {
        (EvalVal::Str(x), EvalVal::Str(y)) => x == y,
        (EvalVal::Nat(x), EvalVal::Nat(y)) => x == y,
        (EvalVal::Int(x), EvalVal::Int(y)) => x == y,
        (EvalVal::Bool(x), EvalVal::Bool(y)) => x == y,
        (EvalVal::Char(x), EvalVal::Char(y)) => x == y,
        (EvalVal::Name(x), EvalVal::Name(y)) => x == y,
        (EvalVal::OptionSome, EvalVal::OptionSome) | (EvalVal::OptionNone, EvalVal::OptionNone) => {
            true
        }
        (EvalVal::Unit, EvalVal::Unit) => true,
        _ => false,
    }
}

fn append_name(mut base: Name, suffix: &Name) -> Name {
    enum Comp {
        Str(String),
        Num(u64),
    }
    let mut parts = Vec::new();
    let mut cur = suffix.clone();
    while !cur.is_anonymous() {
        match cur.leaf_view() {
            LeafView::Str(s) => parts.push(Comp::Str(s.to_owned())),
            LeafView::Num(n) => parts.push(Comp::Num(n)),
            LeafView::Anonymous => break,
        }
        cur = cur.parent();
    }
    for part in parts.into_iter().rev() {
        base = match part {
            Comp::Str(s) => Name::str(base, s),
            Comp::Num(n) => Name::num(base, n),
        };
    }
    base
}

fn is_lean_whitespace(ch: char) -> bool {
    matches!(ch, ' ' | '\t' | '\r' | '\n')
}

fn advance_one_char(s: &str, pos: usize) -> usize {
    if pos >= s.len() {
        return s.len();
    }
    let ch = s[pos..].chars().next().unwrap_or('\0');
    (pos + ch.len_utf8()).min(s.len())
}

fn scalar_col_of(source: &SourceText, pos: usize) -> usize {
    source
        .position_of(BytePos(pos.min(source.len_bytes())))
        .map_or(0, |p| p.scalar_column)
}

fn is_none_stx_vm(stx: &VmNode, null_kind: &Name) -> bool {
    matches!(&**stx, VmSyntax::Node { kind, args, .. } if kind == null_kind && args.is_empty())
}

fn is_antiquot_vm(stx: &VmNode) -> bool {
    matches!(&**stx, VmSyntax::Node { kind, .. } if matches!(kind.leaf_view(), LeafView::Str("antiquot")))
}

fn is_antiquots(stx: &VmNode, choice_kind: &Name) -> bool {
    let mut stack = vec![stx];
    while let Some(node) = stack.pop() {
        if is_antiquot_vm(node) {
            continue;
        }
        if let VmSyntax::Node { kind, args, .. } = &**node
            && kind == choice_kind
            && !args.is_empty()
        {
            stack.extend(args);
            continue;
        }
        return false;
    }
    true
}

fn is_ident_stx_vm(stx: &VmNode) -> bool {
    matches!(&**stx, VmSyntax::Ident { .. }) || is_antiquot_vm(stx)
}

fn get_tail_info_vm(stx: &VmNode) -> SourceInfo {
    let mut stack: Vec<(&VmNode, Option<SourceInfo>)> = vec![(stx, None)];
    while let Some((node, fallback)) = stack.pop() {
        if let Some(info) = fallback {
            if !matches!(info, SourceInfo::None) {
                return info;
            }
            continue;
        }
        match &**node {
            VmSyntax::Missing => {}
            VmSyntax::Atom { info, .. } | VmSyntax::Ident { info, .. } => {
                if !matches!(info, SourceInfo::None) {
                    return *info;
                }
            }
            VmSyntax::Node { info, args, .. } => {
                if !matches!(info, SourceInfo::None) {
                    stack.push((node, Some(*info)));
                }
                for arg in args {
                    stack.push((arg, None));
                }
            }
        }
    }
    SourceInfo::None
}

fn set_tail_info_vm(stx: &mut VmNode, new_info: SourceInfo) -> bool {
    // 1. Find the rightmost child-index path to the non-`None` `SourceInfo` iteratively.
    let mut path: Vec<usize> = Vec::new();
    let mut found = false;
    enum Step<'a> {
        Enter(&'a VmNode, usize),
        CheckSelf(&'a VmNode),
        Pop,
    }
    let mut work: Vec<Step<'_>> = vec![Step::Enter(stx, usize::MAX)];
    while let Some(step) = work.pop() {
        match step {
            Step::Pop => {
                path.pop();
            }
            Step::CheckSelf(node) => {
                if let VmSyntax::Node { info, .. } = &**node
                    && !matches!(info, SourceInfo::None)
                {
                    found = true;
                    break;
                }
            }
            Step::Enter(node, idx) => {
                if idx != usize::MAX {
                    path.push(idx);
                    work.push(Step::Pop);
                }
                match &**node {
                    VmSyntax::Missing => {}
                    VmSyntax::Atom { info, .. } | VmSyntax::Ident { info, .. } => {
                        if !matches!(info, SourceInfo::None) {
                            found = true;
                            break;
                        }
                    }
                    VmSyntax::Node { info, args, .. } => {
                        if !matches!(info, SourceInfo::None) {
                            work.push(Step::CheckSelf(node));
                        }
                        for (i, arg) in args.iter().enumerate() {
                            work.push(Step::Enter(arg, i));
                        }
                    }
                }
            }
        }
    }
    if !found {
        return false;
    }
    // 2. Mutate only along the discovered path (copy-on-write via `Rc::make_mut`).
    let mut cur = stx;
    for idx in path {
        match cur.make_mut() {
            VmSyntax::Node { args, .. } => cur = &mut args[idx],
            _ => return false,
        }
    }
    match cur.make_mut() {
        VmSyntax::Atom { info, .. }
        | VmSyntax::Ident { info, .. }
        | VmSyntax::Node { info, .. } => {
            *info = new_info;
            true
        }
        VmSyntax::Missing => false,
    }
}

fn get_head_info_vm(stx: &VmNode) -> Option<SourceInfo> {
    let mut stack = vec![stx];
    while let Some(node) = stack.pop() {
        match &**node {
            VmSyntax::Missing => {}
            VmSyntax::Atom { info, .. } | VmSyntax::Ident { info, .. } => {
                if !matches!(info, SourceInfo::None) {
                    return Some(*info);
                }
            }
            VmSyntax::Node { info, args, .. } => {
                if !matches!(info, SourceInfo::None) {
                    return Some(*info);
                }
                for arg in args.iter().rev() {
                    stack.push(arg);
                }
            }
        }
    }
    None
}

fn first_pos_of_vm(stx: &VmNode) -> Option<usize> {
    get_head_info_vm(stx).and_then(|info| info.pos(false).map(|p| p.0))
}

fn get_tail_info(stx: &Syntax) -> SourceInfo {
    let mut stack: Vec<(&Syntax, Option<SourceInfo>)> = vec![(stx, None)];
    while let Some((node, fallback)) = stack.pop() {
        if let Some(info) = fallback {
            if !matches!(info, SourceInfo::None) {
                return info;
            }
            continue;
        }
        match node {
            Syntax::Missing => {}
            Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
                if !matches!(info, SourceInfo::None) {
                    return *info;
                }
            }
            Syntax::Node { info, args, .. } => {
                if !matches!(info, SourceInfo::None) {
                    stack.push((node, Some(*info)));
                }
                for arg in args {
                    stack.push((arg, None));
                }
            }
        }
    }
    SourceInfo::None
}

fn get_head_info(stx: &Syntax) -> Option<SourceInfo> {
    let mut stack = vec![stx];
    while let Some(node) = stack.pop() {
        match node {
            Syntax::Missing => {}
            Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
                if !matches!(info, SourceInfo::None) {
                    return Some(*info);
                }
            }
            Syntax::Node { info, args, .. } => {
                if !matches!(info, SourceInfo::None) {
                    return Some(*info);
                }
                for arg in args.iter().rev() {
                    stack.push(arg);
                }
            }
        }
    }
    None
}

fn set_head_info(stx: &mut Syntax, new_info: SourceInfo) -> bool {
    let mut stack = vec![stx];
    while let Some(node) = stack.pop() {
        match node {
            Syntax::Missing => {}
            Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
                if !matches!(info, SourceInfo::None) {
                    *info = new_info;
                    return true;
                }
            }
            Syntax::Node { info, args, .. } => {
                if !matches!(info, SourceInfo::None) {
                    *info = new_info;
                    return true;
                }
                for arg in args.iter_mut().rev() {
                    stack.push(arg);
                }
            }
        }
    }
    false
}

fn set_start_of_file_leading(stx: &mut Syntax) -> bool {
    let Some(SourceInfo::Original {
        leading,
        pos,
        trailing,
        end_pos,
    }) = get_head_info(stx)
    else {
        return false;
    };
    let widened = ByteSpan::new(BytePos(0), leading.end()).unwrap_or(leading);
    set_head_info(
        stx,
        SourceInfo::Original {
            leading: widened,
            pos,
            trailing,
            end_pos,
        },
    )
}

pub(crate) fn syntax_token_span(stx: &Syntax) -> Option<ByteSpan> {
    let start = get_head_info(stx).and_then(|info| info.pos(false))?;
    let end = match get_tail_info(stx) {
        SourceInfo::Original { end_pos, .. } => end_pos,
        _ => return None,
    };
    ByteSpan::new(start, end)
}

fn check_tail_ws(prev: &VmNode) -> bool {
    matches!(
        get_tail_info_vm(prev),
        SourceInfo::Original { trailing, .. } if trailing.end().0 > trailing.start().0
    )
}

fn check_tail_no_ws(prev: &VmNode) -> bool {
    matches!(
        get_tail_info_vm(prev),
        SourceInfo::Original { trailing, .. } if trailing.end().0 == trailing.start().0
    )
}

fn check_tail_linebreak(source: &SourceText, prev: &VmNode) -> bool {
    matches!(
        get_tail_info_vm(prev),
        SourceInfo::Original { trailing, .. }
            if source.span_str(trailing).is_some_and(|s| s.contains('\n'))
    )
}

/// Compare two `Syntax` trees structurally (including node kinds, atoms, identifiers,
/// and exact `SourceInfo` spans), returning the first mismatch path if any.
pub fn first_syntax_diff(actual: &Syntax, expected: &Syntax) -> Option<String> {
    let mut stack = vec![("root".to_owned(), actual, expected)];
    while let Some((path, a, b)) = stack.pop() {
        if a == b {
            continue;
        }
        match (a, b) {
            (
                Syntax::Node {
                    info: ai,
                    kind: ak,
                    args: aa,
                },
                Syntax::Node {
                    info: bi,
                    kind: bk,
                    args: ba,
                },
            ) => {
                if ak != bk {
                    return Some(format!(
                        "{path}: kind {} != {}",
                        ak.to_display_string(),
                        bk.to_display_string()
                    ));
                }
                if ai != bi {
                    return Some(format!(
                        "{path}({}): node info {ai:?} != {bi:?}",
                        ak.to_display_string()
                    ));
                }
                if aa.len() != ba.len() {
                    return Some(format!(
                        "{path}({}): arity {} != {}",
                        ak.to_display_string(),
                        aa.len(),
                        ba.len()
                    ));
                }
                for (i, (ca, cb)) in aa.iter().zip(ba.iter()).enumerate().rev() {
                    stack.push((format!("{path}/{}[{i}]", ak.to_display_string()), ca, cb));
                }
            }
            (Syntax::Atom { info: ai, val: av }, Syntax::Atom { info: bi, val: bv }) => {
                return Some(format!("{path}: atom ({av:?}, {ai:?}) != ({bv:?}, {bi:?})"));
            }
            (
                Syntax::Ident {
                    info: ai,
                    raw_val: ar,
                    val: av,
                    ..
                },
                Syntax::Ident {
                    info: bi,
                    raw_val: br,
                    val: bv,
                    ..
                },
            ) => {
                return Some(format!(
                    "{path}: ident ({}, {ar:?}, {ai:?}) != ({}, {br:?}, {bi:?})",
                    av.to_display_string(),
                    bv.to_display_string()
                ));
            }
            _ => {
                return Some(format!(
                    "{path}: shape {:?} != {:?}",
                    syntax_tag(a),
                    syntax_tag(b)
                ));
            }
        }
    }
    None
}

fn syntax_tag(stx: &Syntax) -> String {
    match stx {
        Syntax::Missing => "Missing".to_owned(),
        Syntax::Node { kind, args, .. } => {
            format!("Node({}, len={})", kind.to_display_string(), args.len())
        }
        Syntax::Atom { val, .. } => format!("Atom({val:?})"),
        Syntax::Ident { val, .. } => format!("Ident({})", val.to_display_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_syntax::pin_syntax;

    #[test]
    fn checked_in_builtin_table_compiles_all_defs_and_categories() {
        let interp = reference_builtin_interpreter();
        assert_eq!(interp.def_count(), 480);
        assert_eq!(interp.category_count(), 10);
        // Verify FirstTokens indexing worked on core categories (not all dumped to unindexed).
        let (cmd_lead_idx, _cmd_lead_unidx, _, _) = interp
            .category_summary(&Name::from_components(["command"]))
            .expect("command category");
        assert!(
            cmd_lead_idx >= 30,
            "expected >= 30 indexed leading command tokens, got {cmd_lead_idx}"
        );
        let (term_lead_idx, _, term_trail_idx, _) = interp
            .category_summary(&Name::from_components(["term"]))
            .expect("term category");
        assert!(
            term_lead_idx >= 30 && term_trail_idx >= 5,
            "expected rich term tables, got lead={term_lead_idx} trail={term_trail_idx}"
        );
    }

    #[test]
    fn parses_core_prelude_constructs_from_generated_table() {
        let interp = reference_builtin_interpreter();
        let src = SourceText::from_utf8(
            b"module\nprelude\n\n\
              universe u v\n\
              inductive MyNat : Type where\n\
                | zero : MyNat\n\
                | succ (n : MyNat) : MyNat\n\
              def idFn {a : Sort u} (x : a) : a := x\n",
        )
        .expect("utf8");
        let parsed = interp.parse_module(&src, DEFAULT_STEP_BUDGET);
        assert!(
            parsed.errors.is_empty(),
            "unexpected parse errors: {:?}",
            parsed.errors
        );
        assert!(!parsed.budget_exhausted);
        assert_eq!(
            parsed.header.kind().map(Name::to_display_string).as_deref(),
            Some("Lean.Parser.Module.header")
        );
        // universe + inductive + def + eoi = 4 commands
        assert_eq!(parsed.commands.len(), 4);
        assert_eq!(
            parsed.commands[0]
                .kind()
                .map(Name::to_display_string)
                .as_deref(),
            Some("Lean.Parser.Command.universe")
        );
        assert_eq!(
            parsed.commands[1]
                .kind()
                .map(Name::to_display_string)
                .as_deref(),
            Some("Lean.Parser.Command.declaration")
        );
        assert_eq!(
            parsed.commands[2]
                .kind()
                .map(Name::to_display_string)
                .as_deref(),
            Some("Lean.Parser.Command.declaration")
        );
        assert_eq!(
            parsed.commands[3]
                .kind()
                .map(Name::to_display_string)
                .as_deref(),
            Some("Lean.Parser.Command.eoi")
        );
    }

    #[test]
    fn parses_vendored_init_prelude_end_to_end() {
        let prelude_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../vendor/lean4-src/src/Init/Prelude.lean");
        if !prelude_path.exists() {
            eprintln!(
                "SKIP: vendored Init/Prelude.lean absent at {}",
                prelude_path.display()
            );
            return;
        }
        let src_bytes = std::fs::read(&prelude_path).expect("read Prelude.lean");
        let src = SourceText::from_utf8(&src_bytes).expect("Prelude utf8");
        let interp = reference_builtin_interpreter();
        let parsed = interp.parse_module(&src, 500_000_000);
        eprintln!(
            "VENDORED PRELUDE PARSE: header={:?} commands={} errors={} steps={} budget_exhausted={}",
            parsed.header.kind().map(Name::to_display_string),
            parsed.commands.len(),
            parsed.errors.len(),
            parsed.steps_used,
            parsed.budget_exhausted,
        );
        for e in parsed.errors.iter().take(15) {
            let line = src.line_of(BytePos(e.pos.min(src.len_bytes()))) + 1;
            eprintln!(
                "  ERR line {line} byte {}: unexpected={:?} expected={:?}",
                e.pos, e.unexpected, e.expected
            );
        }
        assert!(
            !parsed.budget_exhausted,
            "Prelude parse exhausted step budget"
        );
        assert!(
            parsed.errors.is_empty(),
            "expected 0 parse errors on vendored Init/Prelude.lean, got {}",
            parsed.errors.len()
        );
        assert_eq!(
            parsed.commands.len(),
            775,
            "expected all 775 pinned Init/Prelude.lean commands, got {}",
            parsed.commands.len()
        );
    }

    #[test]
    fn layout_indentation_and_syntax_diff_mutants_are_enforced() {
        let interp = reference_builtin_interpreter();
        // Positive: properly aligned match arm parses with 0 errors.
        let good = SourceText::from_utf8(
            b"def f (n : Nat) : Nat :=\n  match n with\n  | 0 => 0\n  | k => k\n",
        )
        .expect("utf8");
        let parsed_good = interp.parse_module(&good, DEFAULT_STEP_BUDGET);
        assert!(
            parsed_good.errors.is_empty(),
            "aligned match should parse cleanly: {:?}",
            parsed_good.errors
        );

        // Negative (fln-match-alt-column-false-accept-u3fv): RHS starting left of `|`
        // violates the pin's `checkColGe` layout rule and must produce a parse error.
        let misaligned =
            SourceText::from_utf8(b"def f (n : Nat) : Nat :=\n  match n with\n  | 0 =>\n0\n")
                .expect("utf8");
        let parsed_bad = interp.parse_module(&misaligned, DEFAULT_STEP_BUDGET);
        assert!(
            !parsed_bad.errors.is_empty(),
            "misaligned match RHS left of `|` must be rejected by checkColGe"
        );

        // Mutant guard: a single-character atom mutation must be detected by `first_syntax_diff`.
        let mut mutated = parsed_good.commands[0].clone();
        fn mutate_first_atom(stx: &mut Syntax) -> bool {
            match stx {
                Syntax::Atom { val, .. } => {
                    val.push('!');
                    true
                }
                Syntax::Node { args, .. } => args.iter_mut().any(mutate_first_atom),
                _ => false,
            }
        }
        assert!(mutate_first_atom(&mut mutated));
        assert!(
            first_syntax_diff(&mutated, &parsed_good.commands[0]).is_some(),
            "mutant guard: first_syntax_diff must detect atom mutation"
        );
    }

    #[test]
    fn optional_prelude_full_lossless_oracle_comparison() {
        let Ok(oracle_path) = std::env::var("FLN_PRELUDE_ORACLE") else {
            eprintln!("SKIP: set FLN_PRELUDE_ORACLE to run 775-command Prelude oracle comparison");
            return;
        };
        let prelude_path = std::env::var("FLN_PRELUDE_SRC")
            .unwrap_or_else(|_| "vendor/lean4-src/src/Init/Prelude.lean".to_owned());
        let src_bytes = std::fs::read(&prelude_path).expect("read Prelude.lean");
        let oracle_text = std::fs::read_to_string(&oracle_path).expect("read oracle dump");
        let oracle = pin_syntax::read(&oracle_text, &src_bytes).expect("parse oracle dump");
        let src = SourceText::from_utf8(&src_bytes).expect("Prelude utf8");

        let interp = reference_builtin_interpreter();
        let parsed = interp.parse_module(&src, 500_000_000);

        let header_exact = parsed.header == oracle.header;
        if !header_exact {
            eprintln!(
                "HEADER DIFF: {:?}",
                first_syntax_diff(&parsed.header, &oracle.header)
            );
        }

        let paired = parsed.commands.len().min(oracle.commands.len());
        let mut exact_cmds = 0usize;
        let mut exact_kinds = 0usize;
        let mut first_diffs: Vec<String> = Vec::new();
        let mut diff_classes: BTreeMap<String, usize> = BTreeMap::new();
        for i in 0..paired {
            if parsed.commands[i] == oracle.commands[i] {
                exact_cmds += 1;
                exact_kinds += 1;
            } else {
                if parsed.commands[i].kind() == oracle.commands[i].kind() {
                    exact_kinds += 1;
                }
                let diff = first_syntax_diff(&parsed.commands[i], &oracle.commands[i])
                    .unwrap_or_else(|| "unknown".to_owned());
                let class_key = diff
                    .split_once(':')
                    .map_or_else(|| diff.clone(), |(p, _)| p.to_owned());
                *diff_classes.entry(class_key).or_default() += 1;
                if first_diffs.len() < 20 {
                    first_diffs.push(format!("CMD {i}: {diff}"));
                }
            }
        }
        eprintln!(
            "PRELUDE ORACLE REPORT: header_exact={header_exact} parsed_cmds={} oracle_cmds={} \
             exact_cmds={exact_cmds}/{} ({:.2}%) exact_kinds={exact_kinds}/{} \
             errors={} steps={} budget_exhausted={}",
            parsed.commands.len(),
            oracle.commands.len(),
            oracle.commands.len(),
            100.0 * (exact_cmds as f64) / (oracle.commands.len().max(1) as f64),
            oracle.commands.len(),
            parsed.errors.len(),
            parsed.steps_used,
            parsed.budget_exhausted,
        );
        for d in &first_diffs {
            eprintln!("  DIFF: {d}");
        }
        for e in parsed.errors.iter().take(10) {
            let line = src.line_of(BytePos(e.pos.min(src.len_bytes()))) + 1;
            eprintln!(
                "  ERR line {line} byte {}: unexpected={:?} expected={:?}",
                e.pos, e.unexpected, e.expected
            );
        }
        // Assert spike decision gate: >= 90% lossless match (exact Syntax equality!).
        let pct = 100.0 * (exact_cmds as f64) / (oracle.commands.len().max(1) as f64);
        assert!(
            header_exact && pct >= 90.0,
            "Prelude builtin-interpreter exact lossless match {exact_cmds}/{} ({pct:.2}%) below 90% spike gate",
            oracle.commands.len()
        );
    }
}
