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
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, OnceLock};

const MAX_PREC: u32 = 1024;
const ARG_PREC: u32 = 1023;
const LEAD_PREC: u32 = 1022;
const MIN_PREC: u32 = 10;

/// Default step budget per top-level parse invocation (FL-INV-07).
pub const DEFAULT_STEP_BUDGET: usize = 50_000_000;

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
        BuiltinInterpreter::from_table(reference_builtin_parser_table())
            .expect("checked-in builtin parser table must compile into an interpreter")
    })
}

/// One diagnostic error produced by the interpreter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterpError {
    pub pos: usize,
    pub unexpected: String,
    pub expected: Vec<String>,
}

impl InterpError {
    fn new(pos: usize, unexpected: impl Into<String>, expected: Vec<String>) -> Self {
        Self {
            pos,
            unexpected: unexpected.into(),
            expected,
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
        body: CombinatorAst,
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
            interpolated_str_kind: Name::from_components(["interpolatedStr"]),
            interpolated_str_lit_kind: Name::from_components(["interpolatedStrLit"]),
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
        let mut st = RuntimeState::new(source, &self.builtin_tokens, max_steps);
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
        Ok(st.pop_or_missing())
    }

    /// Parse a complete Lean module (`header` + top-level commands until EOI),
    /// mirroring `Lean/Parser/Module.lean::{parseHeader, parseCommand}`.
    pub fn parse_module(&self, source: &SourceText, max_steps: usize) -> ParsedModule {
        let mut errors = Vec::new();
        let mut total_steps = 0usize;
        let mut budget_exhausted = false;

        // 1. Parse module header with header token table (`Module.lean:75-112`).
        let mut hst = RuntimeState::new(source, &self.header_tokens, max_steps);
        hst.skip_whitespace();
        if !hst.has_error() {
            let op = ParserOp::Ref(self.module_header_id);
            self.exec_op(&op, &mut hst);
        }
        total_steps = total_steps.saturating_add(hst.steps);
        if hst.budget_exhausted {
            budget_exhausted = true;
        }
        let mut header = hst.back_cloned().unwrap_or(Syntax::Missing);
        for err in hst.recovered_errors.drain(..) {
            errors.push(err);
        }
        if let Some(err) = hst.error.take() {
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
                let mut st = RuntimeState::new(source, &self.builtin_tokens, rem);
                st.pos = pos;
                st.skip_whitespace();
                if !st.has_error() {
                    self.exec_op(&top_cmd_op, &mut st);
                }
                total_steps = total_steps.saturating_add(st.steps);
                if st.budget_exhausted {
                    budget_exhausted = true;
                    break;
                }
                for err in st.recovered_errors.drain(..) {
                    errors.push(err);
                }
                pos = st.pos;
                if recovering && st.back().is_some_and(is_antiquot) {
                    continue;
                }
                match st.error.take() {
                    None => {
                        cmd_stx = st.back_cloned().unwrap_or(Syntax::Missing);
                        recovering = false;
                        produced = true;
                        break;
                    }
                    Some(err) => {
                        if pos == start_pos {
                            pos = self.consume_one_token(source, pos);
                        }
                        let ignore = st.stack_size() == 0
                            || st.back().is_none_or(|s| first_pos_of(s).is_none());
                        if !(recovering && ignore) {
                            errors.push(err);
                        }
                        recovering = true;
                        if ignore {
                            continue;
                        }
                        cmd_stx = st.back_cloned().unwrap_or(Syntax::Missing);
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
        let mut st = RuntimeState::new(source, &self.builtin_tokens, 1024);
        st.pos = pos;
        self.token_fn(&[], &mut st);
        if st.has_error() || st.pos <= pos {
            advance_one_char(source.as_str(), pos)
        } else {
            st.pos
        }
    }

    fn exec_op(&self, op: &ParserOp, st: &mut RuntimeState<'_>) {
        if !st.tick() {
            return;
        }
        if st.depth >= st.max_depth {
            st.mk_unexpected_error(
                format!("parser recursion depth limit exceeded at byte {}", st.pos),
                Vec::new(),
                true,
            );
            return;
        }
        st.depth += 1;
        self.exec_op_inner(op, st);
        st.depth -= 1;
    }

    fn exec_op_inner(&self, op: &ParserOp, st: &mut RuntimeState<'_>) {
        match op {
            ParserOp::Ref(id) => self.exec_op(&self.defs[*id].op, st),
            ParserOp::Skip | ParserOp::InhabitedDefault => {}
            ParserOp::PushNone => st.push(Syntax::node(self.null_kind.clone(), Vec::new())),
            ParserOp::Eoi => {
                if st.pos < st.source.len_bytes() {
                    st.mk_error("expected end of file");
                }
            }
            ParserOp::Symbol(sym) => self.exec_symbol(sym, st),
            ParserOp::NonReservedSymbol { sym, .. } => self.exec_non_reserved_symbol(sym, st),
            ParserOp::UnicodeSymbol { sym, ascii_sym } => {
                self.exec_unicode_symbol(sym, ascii_sym, st);
            }
            ParserOp::RawCh { ch, trailing_ws } => self.exec_raw_ch(*ch, *trailing_ws, st),
            ParserOp::Ident => self.expect_token_kind(&self.ident_kind, "identifier", st),
            ParserOp::RawIdent => self.raw_ident_fn(st),
            ParserOp::NumLit => self.expect_token_kind(&self.num_lit_kind, "numeral", st),
            ParserOp::HexNum => self.hexnum_fn(st),
            ParserOp::ScientificLit => {
                self.expect_token_kind(&self.scientific_lit_kind, "scientific number", st)
            }
            ParserOp::StrLit => self.expect_token_kind(&self.str_lit_kind, "string literal", st),
            ParserOp::CharLit => {
                self.expect_token_kind(&self.char_lit_kind, "character literal", st)
            }
            ParserOp::NameLit => self.expect_token_kind(&self.name_lit_kind, "Name literal", st),
            ParserOp::FieldIdx => self.field_idx_fn(st),
            ParserOp::HygieneInfo => self.hygiene_info_fn(st),
            ParserOp::CommentBody => self.comment_body_fn(st),
            ParserOp::InterpolatedStr(inner) => self.interpolated_str_fn(inner, st),
            ParserOp::Seq(steps) => {
                for step in steps {
                    self.exec_op(step, st);
                    if st.has_error() {
                        break;
                    }
                }
            }
            ParserOp::OrElse(alts) => self.orelse_chain(alts, st),
            ParserOp::Node(kind, inner) => {
                let ini_sz = st.stack_size();
                self.exec_op(inner, st);
                st.mk_node(kind.clone(), ini_sz);
            }
            ParserOp::TrailingNodeAux(kind, inner) => {
                let ini_sz = st.stack_size();
                self.exec_op(inner, st);
                st.mk_trailing_node(kind.clone(), ini_sz);
            }
            ParserOp::Atomic(inner) => {
                let ini_pos = st.pos;
                self.exec_op(inner, st);
                if st.has_error() {
                    st.pos = ini_pos;
                }
            }
            ParserOp::Optional(inner) => {
                let ini_sz = st.stack_size();
                let ini_pos = st.pos;
                self.exec_op(inner, st);
                if st.has_error() && st.pos == ini_pos {
                    st.restore(ini_sz, ini_pos);
                }
                st.mk_node(self.null_kind.clone(), ini_sz);
            }
            ParserOp::Many(inner) => {
                let ini_sz = st.stack_size();
                self.many_aux(inner, st);
                st.mk_node(self.null_kind.clone(), ini_sz);
            }
            ParserOp::Many1(inner) => {
                let ini_sz = st.stack_size();
                self.exec_op(inner, st);
                if !st.has_error() {
                    self.many_aux(inner, st);
                }
                st.mk_node(self.null_kind.clone(), ini_sz);
            }
            ParserOp::Many1Unbox(inner) => self.exec_many1_unbox(inner, st),
            ParserOp::SepBy {
                elem,
                sep,
                allow_trailing,
            } => {
                let ini_sz = st.stack_size();
                self.sep_by_aux(elem, sep, *allow_trailing, ini_sz, true, st);
            }
            ParserOp::SepBy1 {
                elem,
                sep,
                allow_trailing,
            } => {
                let ini_sz = st.stack_size();
                self.sep_by_aux(elem, sep, *allow_trailing, ini_sz, false, st);
            }
            ParserOp::Lookahead(inner) => {
                let ini_sz = st.stack_size();
                let ini_pos = st.pos;
                self.exec_op(inner, st);
                if !st.has_error() {
                    st.restore(ini_sz, ini_pos);
                }
            }
            ParserOp::NotFollowedBy(inner, msg) => self.exec_not_followed_by(inner, msg, st),
            ParserOp::WithCache(name, inner) => self.exec_with_cache(name, inner, st),
            ParserOp::WithResetCache(inner) => self.exec_with_reset_cache(inner, st),
            ParserOp::WithAntiquot {
                antiquot,
                body,
                is_cat,
            } => {
                if st.source.as_bytes().get(st.pos) == Some(&b'$') {
                    let behavior = if *is_cat {
                        OrElseAntiquotBehavior::AcceptLhs
                    } else {
                        OrElseAntiquotBehavior::TakeLongest
                    };
                    self.orelse_core(antiquot, body, behavior, st);
                } else {
                    self.exec_op(body, st);
                }
            }
            ParserOp::TokenWithAntiquot(inner) => {
                self.exec_op(inner, st);
                if !st.has_error() && st.source.as_bytes().get(st.pos) == Some(&b'%') {
                    self.token_antiquot_fn(st);
                }
            }
            ParserOp::WithAntiquotSuffixSplice { kind, body, suffix } => {
                self.exec_with_antiquot_suffix_splice(kind, body, suffix, st);
            }
            ParserOp::WithoutInfo(inner) => self.exec_op(inner, st),
            ParserOp::SetExpected { expected, body } => {
                self.exec_op(body, st);
                if let Some(err) = &mut st.error {
                    err.expected = expected.clone();
                }
            }
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
            ParserOp::CheckNoImmediateColon => {
                if st.back().is_some_and(check_tail_no_ws)
                    && st.source.as_bytes().get(st.pos) == Some(&b':')
                {
                    st.mk_unexpected_error("unexpected ':'", Vec::new(), true);
                }
            }
            ParserOp::CheckStackTop { pred, msg } => self.exec_check_stack_top(*pred, msg, st),
            ParserOp::WithPosition(inner) => {
                let saved = st.ctx.saved_pos;
                st.ctx.saved_pos = Some(st.pos);
                self.exec_op(inner, st);
                st.ctx.saved_pos = saved;
            }
            ParserOp::WithPositionAfterLinebreak(inner) => {
                let saved = st.ctx.saved_pos;
                if st
                    .back()
                    .is_some_and(|prev| check_tail_linebreak(st.source, prev))
                {
                    st.ctx.saved_pos = Some(st.pos);
                }
                self.exec_op(inner, st);
                st.ctx.saved_pos = saved;
            }
            ParserOp::AdaptContext(transform, inner) => {
                self.exec_adapt_context(transform, inner, st);
            }
            ParserOp::WithOpen(inner) | ParserOp::WithOpenDecl(inner) => {
                self.exec_with_reset_cache(inner, st);
            }
            ParserOp::CategoryParser { cat, prec } => self.exec_category_parser(cat, *prec, st),
            ParserOp::ParserOfStack { offset, prec } => {
                self.exec_parser_of_stack(*offset, *prec, st);
            }
            ParserOp::Recover { parser, handler } => self.exec_recover(parser, handler, st),
            ParserOp::SkipUntil(pred) => self.exec_skip_until(pred, st),
            ParserOp::ErrorAtSavedPos { msg, delta } => {
                self.exec_error_at_saved_pos(msg, *delta, st);
            }
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
        match st.back() {
            Some(Syntax::Atom { val, .. }) if val == sym => {}
            Some(Syntax::Ident { info, raw_val, .. }) if raw_val.text(st.source) == Some(sym) => {
                let info = *info;
                st.pop();
                st.push(Syntax::atom(info, sym.to_owned()));
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
    fn exec_many1_unbox(&self, inner: &ParserOp, st: &mut RuntimeState<'_>) {
        let ini_sz = st.stack_size();
        self.exec_op(inner, st);
        if !st.has_error() {
            self.many_aux(inner, st);
        }
        st.mk_node(self.null_kind.clone(), ini_sz);
        if !st.has_error()
            && let Some(mut popped) = st.pop()
        {
            if let Syntax::Node { args, .. } = &mut popped
                && args.len() == 1
            {
                st.push(args.pop().unwrap_or(Syntax::Missing));
            } else {
                st.push(popped);
            }
        }
    }

    #[inline(never)]
    fn exec_not_followed_by(&self, inner: &ParserOp, msg: &str, st: &mut RuntimeState<'_>) {
        let ini_sz = st.stack_size();
        let ini_pos = st.pos;
        self.exec_op(inner, st);
        if st.has_error() {
            st.restore(ini_sz, ini_pos);
        } else {
            st.restore(ini_sz, ini_pos);
            st.mk_unexpected_error(format!("unexpected {msg}"), Vec::new(), true);
        }
    }

    #[inline(never)]
    fn exec_with_cache(&self, name: &Name, inner: &ParserOp, st: &mut RuntimeState<'_>) {
        let key = ParserCacheKey {
            ctx: st.ctx.clone(),
            parser_name: name.clone(),
            pos: st.pos,
        };
        if let Some(entry) = st.parser_cache.get(&key).cloned() {
            st.push(entry.stx);
            st.lhs_prec = entry.lhs_prec;
            st.pos = entry.new_pos;
            st.error = entry.error;
            return;
        }
        if !st.active_cache_keys.insert(key.clone()) {
            st.mk_unexpected_error(
                format!(
                    "left-recursive cycle in parser {} at byte {}",
                    name.to_display_string(),
                    st.pos
                ),
                Vec::new(),
                true,
            );
            return;
        }
        let init_raw_sz = st.raw_stack_len();
        let old_drop = st.stack_drop;
        st.stack_drop = init_raw_sz;
        st.lhs_prec = 0;
        st.error = None;
        self.exec_op(inner, st);
        st.stack_drop = old_drop;
        st.active_cache_keys.remove(&key);
        if st.raw_stack_len() == init_raw_sz + 1
            && let Some(top) = st.back_cloned()
        {
            st.parser_cache.insert(
                key,
                ParserCacheEntry {
                    stx: top,
                    lhs_prec: st.lhs_prec,
                    new_pos: st.pos,
                    error: st.error.clone(),
                },
            );
        }
    }

    #[inline(never)]
    fn exec_with_reset_cache(&self, inner: &ParserOp, st: &mut RuntimeState<'_>) {
        let old_drop = st.stack_drop;
        let saved_cache = std::mem::take(&mut st.parser_cache);
        st.stack_drop = 0;
        self.exec_op(inner, st);
        st.stack_drop = old_drop;
        st.parser_cache = saved_cache;
    }

    #[inline(never)]
    fn exec_with_antiquot_suffix_splice(
        &self,
        kind: &Name,
        body: &ParserOp,
        suffix: &ParserOp,
        st: &mut RuntimeState<'_>,
    ) {
        self.exec_op(body, st);
        if !st.has_error()
            && st
                .back()
                .is_some_and(|s| is_antiquots(s, &self.choice_kind))
        {
            let ini_sz = st.stack_size();
            let ini_pos = st.pos;
            self.exec_op(suffix, st);
            if st.has_error() {
                st.restore(ini_sz, ini_pos);
            } else {
                let splice_kind = Name::str(kind.clone(), "antiquot_suffix_splice");
                let target_sz = st.stack_size().saturating_sub(2);
                st.mk_node(splice_kind, target_sz);
            }
        }
    }

    #[inline(never)]
    fn exec_check_stack_top(&self, pred: SyntaxPred, msg: &str, st: &mut RuntimeState<'_>) {
        let ok = st.back().is_some_and(|top| match pred {
            SyntaxPred::IsIdent => is_ident_stx(top),
            SyntaxPred::IsIdentOrDotIdentOrProj => {
                is_ident_stx(top)
                    || top.kind() == Some(&self.dot_ident_kind)
                    || top.kind() == Some(&self.proj_kind)
            }
        });
        if !ok {
            st.mk_unexpected_error(msg.to_owned(), Vec::new(), true);
        }
    }

    #[inline(never)]
    fn exec_adapt_context(
        &self,
        transform: &ContextTransform,
        inner: &ParserOp,
        st: &mut RuntimeState<'_>,
    ) {
        let saved = st.ctx.clone();
        match transform {
            ContextTransform::WithoutPosition => st.ctx.saved_pos = None,
            ContextTransform::WithForbidden(tk) => st.ctx.forbidden_tk = Some(tk.clone()),
            ContextTransform::WithoutForbidden => st.ctx.forbidden_tk = None,
            ContextTransform::SuppressInsideQuot => {
                if st.ctx.quot_depth == 0 {
                    st.ctx.suppress_inside_quot = true;
                }
            }
            ContextTransform::AddQuotDepth(delta) => {
                st.ctx.quot_depth = (st.ctx.quot_depth as i64 + i64::from(*delta)).max(0) as u32;
            }
        }
        self.exec_op(inner, st);
        st.ctx = saved;
    }

    #[inline(never)]
    fn exec_category_parser(&self, cat: &Name, prec: u32, st: &mut RuntimeState<'_>) {
        let saved_prec = st.ctx.prec;
        st.ctx.prec = prec;
        let canonical_cat = if cat.to_display_string() == "syntax" {
            Name::from_components(["stx"])
        } else {
            cat.clone()
        };
        let key = ParserCacheKey {
            ctx: st.ctx.clone(),
            parser_name: canonical_cat.clone(),
            pos: st.pos,
        };
        if let Some(entry) = st.parser_cache.get(&key).cloned() {
            st.push(entry.stx);
            st.lhs_prec = entry.lhs_prec;
            st.pos = entry.new_pos;
            st.error = entry.error;
            st.ctx.prec = saved_prec;
            return;
        }
        if !st.active_cache_keys.insert(key.clone()) {
            st.mk_unexpected_error(
                format!(
                    "left-recursive cycle in category {} at byte {}",
                    canonical_cat.to_display_string(),
                    st.pos
                ),
                Vec::new(),
                true,
            );
            st.ctx.prec = saved_prec;
            return;
        }
        let init_raw_sz = st.raw_stack_len();
        let old_drop = st.stack_drop;
        st.stack_drop = init_raw_sz;
        st.lhs_prec = 0;
        st.error = None;
        self.pratt_category(&canonical_cat, st);
        st.stack_drop = old_drop;
        st.active_cache_keys.remove(&key);
        if st.raw_stack_len() == init_raw_sz + 1
            && let Some(top) = st.back_cloned()
        {
            st.parser_cache.insert(
                key,
                ParserCacheEntry {
                    stx: top,
                    lhs_prec: st.lhs_prec,
                    new_pos: st.pos,
                    error: st.error.clone(),
                },
            );
        }
        st.ctx.prec = saved_prec;
    }

    #[inline(never)]
    fn exec_parser_of_stack(&self, offset: usize, prec: u32, st: &mut RuntimeState<'_>) {
        let sz = st.stack_size();
        if sz < offset + 1 {
            st.mk_unexpected_error(
                "failed to determine parser using syntax stack, stack is too small",
                Vec::new(),
                true,
            );
            return;
        }
        let Some(Syntax::Ident { val, .. }) = st.get_visible(sz - offset - 1) else {
            st.mk_unexpected_error(
                "failed to determine parser using syntax stack, the specified element on the stack is not an identifier",
                Vec::new(),
                true,
            );
            return;
        };
        let cat = val.clone();
        self.exec_category_parser(&cat, prec, st);
    }

    #[inline(never)]
    fn exec_recover(&self, parser: &ParserOp, handler: &ParserOp, st: &mut RuntimeState<'_>) {
        self.exec_op(parser, st);
        if let Some(msg) = st.error.take() {
            let saved_pos = st.pos;
            let saved_stack_len = st.raw_stack_len();
            let saved_lhs = st.lhs_prec;
            self.exec_op(handler, st);
            if st.has_error() {
                st.pos = saved_pos;
                st.truncate_raw(saved_stack_len);
                st.lhs_prec = saved_lhs;
                st.error = Some(msg);
            } else {
                st.recovered_errors.push(msg);
            }
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

    fn pratt_category(&self, cat_name: &Name, st: &mut RuntimeState<'_>) {
        let Some(cat) = self.categories.get(cat_name) else {
            st.mk_unexpected_error(
                format!("unknown parser category '{}'", cat_name.to_display_string()),
                Vec::new(),
                true,
            );
            return;
        };

        // 1. Leading parser with category antiquot (`Basic.lean:1923-1924`).
        if st.source.as_bytes().get(st.pos) == Some(&b'$') {
            let ini_sz = st.stack_size();
            let ini_pos = st.pos;
            self.exec_op(&cat.antiquot_parser, st);
            if let Some(err1) = st.error.take() {
                if st.pos == ini_pos {
                    st.restore(ini_sz, ini_pos);
                    self.leading_parser_aux(cat, st);
                    if st.pos == ini_pos
                        && let Some(err2) = st.error.take()
                    {
                        st.error = Some(err1.merge(&err2));
                    }
                } else {
                    st.error = Some(err1);
                }
            }
        } else {
            self.leading_parser_aux(cat, st);
        }

        if st.has_error() {
            return;
        }

        // 2. Trailing loop (`Basic.lean:1929-1947`).
        loop {
            if !st.tick() {
                return;
            }
            let ini_sz = st.stack_size();
            let ini_pos = st.pos;
            let indexed =
                self.indexed_lookup(&cat.trailing_table, LeadingIdentBehavior::Default, st);
            if st.has_error() {
                st.restore(ini_sz, ini_pos);
                return;
            }
            if indexed.is_empty() && cat.trailing_unindexed.is_empty() {
                return;
            }
            let Some(left) = st.pop() else {
                return;
            };
            let mut candidates = indexed;
            candidates.extend_from_slice(&cat.trailing_unindexed);
            self.longest_match(Some(&left), &candidates, st);
            if st.has_error() {
                if st.pos == ini_pos {
                    st.restore(ini_sz.saturating_sub(1), ini_pos);
                    st.push(left);
                }
                return;
            }
            if st.pos == ini_pos {
                return;
            }
        }
    }

    fn leading_parser_aux(&self, cat: &CategoryDispatch, st: &mut RuntimeState<'_>) {
        let ini_sz = st.stack_size();
        let indexed = self.indexed_lookup(&cat.leading_table, cat.behavior, st);
        if st.has_error() {
            return;
        }
        let mut candidates = cat.leading_unindexed.clone();
        candidates.extend(indexed);
        if candidates.is_empty() {
            let expected = vec![cat.name.to_display_string()];
            let ini_pos = st.pos;
            self.token_fn(&expected, st);
            if st.has_error() {
                return;
            }
            st.mk_unexpected_token_errors(&expected, Some(ini_pos));
            return;
        }
        self.longest_match(None, &candidates, st);
        if st.stack_size() != ini_sz + 1 {
            st.mk_node(self.null_kind.clone(), ini_sz);
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
        match &tok {
            Syntax::Atom { val, .. } => lookup(&Name::str(Name::anonymous(), val.as_str())),
            Syntax::Ident { val, .. } => match behavior {
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
            Syntax::Node { kind, .. } => lookup(kind),
            Syntax::Missing => Vec::new(),
        }
    }

    fn run_longest_match_parser(
        &self,
        left: Option<&Syntax>,
        start_lhs_prec: u32,
        def_id: usize,
        st: &mut RuntimeState<'_>,
    ) {
        st.lhs_prec = if left.is_some() {
            start_lhs_prec
        } else {
            MAX_PREC
        };
        let start_sz = st.stack_size();
        if let Some(l) = left {
            st.push(l.clone());
        }
        let op = Arc::clone(&self.defs[def_id].op);
        self.exec_op(&op, st);
        if st.stack_size() == start_sz + 1 {
            return;
        }
        if st.has_error() {
            st.shrink(start_sz);
            st.push(Syntax::Missing);
        } else {
            st.mk_error("longestMatch parsers must generate exactly one Syntax node");
        }
    }

    fn longest_match(
        &self,
        left: Option<&Syntax>,
        candidates: &[(usize, u32)],
        st: &mut RuntimeState<'_>,
    ) {
        let Some(&(first_id, first_prio)) = candidates.first() else {
            st.mk_error("longestMatch: empty list");
            return;
        };
        if candidates.len() == 1 {
            let start_lhs = st.lhs_prec;
            self.run_longest_match_parser(left, start_lhs, first_id, st);
            return;
        }
        let start_sz = st.stack_size();
        let start_lhs = st.lhs_prec;
        let start_pos = st.pos;
        self.run_longest_match_parser(left, start_lhs, first_id, st);
        let mut prev_prio = first_prio;

        for &(def_id, prio) in &candidates[1..] {
            let prev_score = (st.pos, u8::from(!st.has_error()), prev_prio);
            let prev_err = st.error.clone();
            let prev_pos = st.pos;
            let prev_sz = st.stack_size();
            let prev_lhs = st.lhs_prec;

            st.restore(prev_sz, start_pos);
            self.run_longest_match_parser(left, start_lhs, def_id, st);
            let cur_score = (st.pos, u8::from(!st.has_error()), prio);

            match prev_score.cmp(&cur_score) {
                std::cmp::Ordering::Less => {
                    st.keep_top(start_sz);
                    prev_prio = prio;
                }
                std::cmp::Ordering::Greater => {
                    st.shrink(prev_sz);
                    st.lhs_prec = prev_lhs;
                    st.pos = prev_pos;
                    st.error = prev_err;
                }
                std::cmp::Ordering::Equal => match prev_err {
                    None => {
                        st.lhs_prec = st.lhs_prec.min(prev_lhs);
                        prev_prio = prio;
                    }
                    Some(old_err) => {
                        st.shrink(prev_sz);
                        if let Some(cur_err) = &st.error
                            && *cur_err != old_err
                        {
                            st.error = Some(old_err.merge(cur_err));
                        }
                        prev_prio = prio;
                    }
                },
            }
        }

        if st.stack_size() > start_sz + 1 {
            st.mk_node(self.choice_kind.clone(), start_sz);
        }
    }

    fn orelse_chain(&self, alts: &[Arc<ParserOp>], st: &mut RuntimeState<'_>) {
        let Some((first, rest)) = alts.split_first() else {
            return;
        };
        if rest.is_empty() {
            self.exec_op(first, st);
            return;
        }
        let ini_sz = st.stack_size();
        let ini_pos = st.pos;
        self.exec_op(first, st);
        for alt in rest {
            if let Some(err1) = st.error.take() {
                if st.pos == ini_pos {
                    st.restore(ini_sz, ini_pos);
                    self.exec_op(alt, st);
                    if st.pos == ini_pos
                        && let Some(err2) = st.error.take()
                    {
                        st.error = Some(err1.merge(&err2));
                    }
                    continue;
                }
                st.error = Some(err1);
                return;
            }
            let Some(p_back) = st.back_cloned() else {
                return;
            };
            if st.stack_size() != ini_sz + 1 || !is_antiquots(&p_back, &self.choice_kind) {
                return;
            }
            let p_pos = st.pos;
            st.restore(ini_sz, ini_pos);
            self.exec_op(alt, st);
            if st.has_error() {
                st.restore(ini_sz, p_pos);
                st.push(p_back);
                continue;
            }
            if st.pos > p_pos {
                continue;
            }
            if st.pos < p_pos
                || st.stack_size() != ini_sz + 1
                || !st
                    .back()
                    .is_some_and(|b| is_antiquots(b, &self.choice_kind))
            {
                st.restore(ini_sz, p_pos);
                st.push(p_back);
                continue;
            }
            let q_back = st.pop_or_missing();
            self.push_flattened_antiquots(p_back, st);
            self.push_flattened_antiquots(q_back, st);
            st.mk_node(self.choice_kind.clone(), ini_sz);
        }
    }

    fn orelse_core(
        &self,
        lhs: &ParserOp,
        rhs: &ParserOp,
        antiquot_behavior: OrElseAntiquotBehavior,
        st: &mut RuntimeState<'_>,
    ) {
        let ini_sz = st.stack_size();
        let ini_pos = st.pos;
        self.exec_op(lhs, st);
        if let Some(err1) = st.error.take() {
            if st.pos == ini_pos {
                st.restore(ini_sz, ini_pos);
                self.exec_op(rhs, st);
                if st.pos == ini_pos
                    && let Some(err2) = st.error.take()
                {
                    st.error = Some(err1.merge(&err2));
                }
            } else {
                st.error = Some(err1);
            }
            return;
        }
        let Some(p_back) = st.back_cloned() else {
            return;
        };
        if antiquot_behavior == OrElseAntiquotBehavior::AcceptLhs
            || st.stack_size() != ini_sz + 1
            || !is_antiquots(&p_back, &self.choice_kind)
        {
            return;
        }
        let p_pos = st.pos;
        st.restore(ini_sz, ini_pos);
        self.exec_op(rhs, st);
        if st.has_error() {
            st.restore(ini_sz, p_pos);
            st.push(p_back);
            return;
        }
        if st.pos > p_pos {
            return;
        }
        if st.pos < p_pos
            || antiquot_behavior != OrElseAntiquotBehavior::Merge
            || st.stack_size() != ini_sz + 1
            || !st
                .back()
                .is_some_and(|b| is_antiquots(b, &self.choice_kind))
        {
            st.restore(ini_sz, p_pos);
            st.push(p_back);
            return;
        }
        let q_back = st.pop_or_missing();
        self.push_flattened_antiquots(p_back, st);
        self.push_flattened_antiquots(q_back, st);
        st.mk_node(self.choice_kind.clone(), ini_sz);
    }

    fn push_flattened_antiquots(&self, stx: Syntax, st: &mut RuntimeState<'_>) {
        if let Syntax::Node { kind, args, .. } = &stx
            && *kind == self.choice_kind
        {
            for arg in args {
                st.push(arg.clone());
            }
            return;
        }
        st.push(stx);
    }

    fn many_aux(&self, inner: &ParserOp, st: &mut RuntimeState<'_>) {
        loop {
            if !st.tick() {
                return;
            }
            let ini_sz = st.stack_size();
            let ini_pos = st.pos;
            self.exec_op(inner, st);
            if st.has_error() {
                if st.pos == ini_pos {
                    st.restore(ini_sz, ini_pos);
                }
                return;
            }
            if st.pos == ini_pos {
                st.mk_unexpected_error(
                    "invalid 'many' parser combinator application, parser did not consume anything",
                    Vec::new(),
                    true,
                );
                return;
            }
            if st.stack_size() > ini_sz + 1 {
                st.mk_node(self.null_kind.clone(), ini_sz);
            }
        }
    }

    fn sep_by_aux(
        &self,
        elem: &ParserOp,
        sep: &ParserOp,
        allow_trailing: bool,
        ini_sz: usize,
        mut p_opt: bool,
        st: &mut RuntimeState<'_>,
    ) {
        loop {
            if !st.tick() {
                return;
            }
            let sz = st.stack_size();
            let pos = st.pos;
            self.exec_op(elem, st);
            if st.has_error() {
                if st.pos > pos {
                    st.mk_node(self.null_kind.clone(), ini_sz);
                    return;
                } else if p_opt {
                    st.restore(sz, pos);
                    st.mk_node(self.null_kind.clone(), ini_sz);
                    return;
                } else {
                    st.push(Syntax::Missing);
                    st.mk_node(self.null_kind.clone(), ini_sz);
                    return;
                }
            }
            if st.stack_size() > sz + 1 {
                st.mk_node(self.null_kind.clone(), sz);
            }
            let sz = st.stack_size();
            let pos = st.pos;
            self.exec_op(sep, st);
            if st.has_error() {
                st.restore(sz, pos);
                st.mk_node(self.null_kind.clone(), ini_sz);
                return;
            }
            if st.stack_size() > sz + 1 {
                st.mk_node(self.null_kind.clone(), sz);
            }
            p_opt = allow_trailing;
        }
    }

    fn token_antiquot_fn(&self, st: &mut RuntimeState<'_>) {
        let ini_sz = st.stack_size();
        let ini_pos = st.pos;
        if !st
            .pick_non_none(&self.null_kind)
            .is_some_and(check_tail_no_ws)
        {
            return;
        }
        self.satisfy_symbol(|s| s == "%", &["'%'".to_owned()], st);
        if st.has_error() {
            st.restore(ini_sz, ini_pos);
            return;
        }
        self.satisfy_symbol(|s| s == "$", &["'$'".to_owned()], st);
        if st.has_error() {
            st.restore(ini_sz, ini_pos);
            return;
        }
        if !st
            .pick_non_none(&self.null_kind)
            .is_some_and(check_tail_no_ws)
        {
            st.restore(ini_sz, ini_pos);
            return;
        }
        self.exec_op(&self.antiquot_expr_op, st);
        if st.has_error() {
            st.restore(ini_sz, ini_pos);
            return;
        }
        st.mk_node(self.token_antiquot_kind.clone(), ini_sz.saturating_sub(1));
    }

    fn peek_token(&self, st: &mut RuntimeState<'_>) -> Option<Syntax> {
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

        match lex_token(st.source, st.tokens, BytePos(start_pos)) {
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
                        st.mk_unexpected_error(err.message(), Vec::new(), false);
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
                    TokenKind::Symbol(sym) => Syntax::atom(info, sym),
                    TokenKind::Ident(val) => Syntax::Ident {
                        info,
                        raw_val: lexed.extent.into(),
                        val,
                        preresolved: Vec::new(),
                    },
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
                        Syntax::node(kind, vec![Syntax::atom(info, raw)])
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
                st.mk_unexpected_error(err.message(), expected.to_vec(), true);
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
        if let Some(Syntax::Atom { val, .. }) = st.back()
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
        let matches = match st.back() {
            Some(Syntax::Ident { .. }) => *kind == self.ident_kind,
            Some(Syntax::Node { kind: k, .. }) => k == kind,
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
                        st.mk_unexpected_error(err.message(), Vec::new(), false);
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
                st.push(Syntax::Ident {
                    info,
                    raw_val: lexed.extent.into(),
                    val,
                    preresolved: Vec::new(),
                });
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
            let ident = Syntax::Ident {
                info,
                raw_val: empty.into(),
                val: Name::anonymous(),
                preresolved: Vec::new(),
            };
            st.push(Syntax::node(self.hygiene_info_kind.clone(), vec![ident]));
        };
        if let Some(mut prev) = st.pop() {
            if let SourceInfo::Original {
                leading,
                pos,
                trailing,
                end_pos,
            } = get_tail_info(&prev)
            {
                let empty = ByteSpan::empty_at(end_pos);
                set_tail_info(
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

    fn interpolated_str_fn(&self, inner: &ParserOp, st: &mut RuntimeState<'_>) {
        let stack_sz = st.stack_size();
        let start_pos = st.pos;
        if start_pos >= st.source.len_bytes() {
            st.mk_eoi_error(&[]);
            return;
        }
        if st.source.as_bytes().get(start_pos) != Some(&b'"') {
            st.mk_error("interpolated string");
            return;
        }
        st.pos = start_pos + 1;
        let mut chunk_start = start_pos;
        let saved_pos_ctx = st.ctx.saved_pos;
        loop {
            if !st.tick() {
                return;
            }
            let i = st.pos;
            if i >= st.source.len_bytes() {
                st.mk_error("unterminated string literal");
                st.mk_node(self.interpolated_str_kind.clone(), stack_sz);
                return;
            }
            let ch = st.source.as_str()[i..].chars().next().unwrap_or('\0');
            st.pos = i + ch.len_utf8();
            if ch == '"' {
                self.push_node_token(
                    self.interpolated_str_lit_kind.clone(),
                    chunk_start,
                    true,
                    st,
                );
                st.mk_node(self.interpolated_str_kind.clone(), stack_sz);
                return;
            } else if ch == '\\' {
                if !skip_quoted_char_for_interp(st) {
                    st.mk_node(self.interpolated_str_kind.clone(), stack_sz);
                    return;
                }
            } else if ch == '{' {
                self.push_node_token(
                    self.interpolated_str_lit_kind.clone(),
                    chunk_start,
                    true,
                    st,
                );
                if st.has_error() {
                    return;
                }
                st.ctx.saved_pos = None;
                self.exec_op(inner, st);
                st.ctx.saved_pos = saved_pos_ctx;
                if st.has_error() {
                    return;
                }
                let brace_pos = st.pos;
                if st.source.as_bytes().get(brace_pos) == Some(&b'}') {
                    st.pos = brace_pos + 1;
                    chunk_start = brace_pos;
                } else {
                    st.mk_error("'}'");
                    st.mk_node(self.interpolated_str_kind.clone(), stack_sz);
                    return;
                }
            }
        }
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
                    st.mk_unexpected_error(err.message(), Vec::new(), false);
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
        st.push(Syntax::atom(info, val));
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
                    st.mk_unexpected_error(err.message(), Vec::new(), false);
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
        st.push(Syntax::node(kind, vec![Syntax::atom(info, val)]));
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ParserCacheKey {
    ctx: CacheableCtx,
    parser_name: Name,
    pos: usize,
}

#[derive(Debug, Clone)]
struct ParserCacheEntry {
    stx: Syntax,
    lhs_prec: u32,
    new_pos: usize,
    error: Option<InterpError>,
}

struct RuntimeState<'a> {
    source: &'a SourceText,
    tokens: &'a TokenTable,
    ctx: CacheableCtx,
    stack: Vec<Syntax>,
    stack_drop: usize,
    lhs_prec: u32,
    pos: usize,
    error: Option<InterpError>,
    recovered_errors: Vec<InterpError>,
    token_cache: Option<(usize, usize, Option<String>, Syntax)>,
    parser_cache: HashMap<ParserCacheKey, ParserCacheEntry>,
    active_cache_keys: HashSet<ParserCacheKey>,
    depth: usize,
    max_depth: usize,
    steps: usize,
    max_steps: usize,
    budget_exhausted: bool,
}

impl<'a> RuntimeState<'a> {
    fn new(source: &'a SourceText, tokens: &'a TokenTable, max_steps: usize) -> Self {
        Self {
            source,
            tokens,
            ctx: CacheableCtx {
                prec: 0,
                quot_depth: 0,
                suppress_inside_quot: false,
                saved_pos: None,
                forbidden_tk: None,
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
            max_depth: 256,
            steps: 0,
            max_steps,
            budget_exhausted: false,
        }
    }

    #[inline]
    fn tick(&mut self) -> bool {
        if self.steps >= self.max_steps {
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
                self.mk_unexpected_error(err.message(), Vec::new(), false);
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
    fn push(&mut self, stx: Syntax) {
        self.stack.push(stx);
    }

    #[inline]
    fn pop(&mut self) -> Option<Syntax> {
        if self.stack_size() > 0 {
            self.stack.pop()
        } else {
            None
        }
    }

    #[inline]
    fn pop_or_missing(&mut self) -> Syntax {
        self.pop().unwrap_or(Syntax::Missing)
    }

    #[inline]
    fn back(&self) -> Option<&Syntax> {
        if self.stack_size() > 0 {
            self.stack.last()
        } else {
            None
        }
    }

    #[inline]
    fn back_cloned(&self) -> Option<Syntax> {
        self.back().cloned()
    }

    #[inline]
    fn get_visible(&self, idx: usize) -> Option<&Syntax> {
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

    fn pick_non_none(&self, null_kind: &Name) -> Option<&Syntax> {
        self.stack[self.stack_drop..]
            .iter()
            .rev()
            .find(|s| !is_none_stx(s, null_kind))
    }

    fn mk_node(&mut self, kind: Name, ini_sz: usize) {
        if self.has_error() && self.stack_size() == ini_sz {
            self.push(Syntax::Missing);
            return;
        }
        let split_at = (self.stack_drop + ini_sz).min(self.stack.len());
        let args = self.stack.split_off(split_at);
        self.push(Syntax::node(kind, args));
    }

    fn mk_trailing_node(&mut self, kind: Name, ini_sz: usize) {
        let split_at = (self.stack_drop + ini_sz.saturating_sub(1)).min(self.stack.len());
        let args = self.stack.split_off(split_at);
        self.push(Syntax::node(kind, args));
    }

    fn mk_error(&mut self, expected: &str) {
        self.error = Some(InterpError::new(
            self.pos,
            String::new(),
            vec![expected.to_owned()],
        ));
        self.push(Syntax::Missing);
    }

    fn mk_unexpected_error(
        &mut self,
        unexpected: impl Into<String>,
        expected: Vec<String>,
        push_missing: bool,
    ) {
        self.error = Some(InterpError::new(self.pos, unexpected, expected));
        if push_missing {
            self.push(Syntax::Missing);
        }
    }

    fn mk_eoi_error(&mut self, expected: &[String]) {
        self.mk_unexpected_error("unexpected end of input", expected.to_vec(), true);
    }

    fn mk_unexpected_token_errors(&mut self, expected: &[String], ini_pos: Option<usize>) {
        let tk = self.pop_or_missing();
        let pos = ini_pos.or_else(|| first_pos_of(&tk)).unwrap_or(self.pos);
        self.pos = pos;
        let unexpected = match &tk {
            Syntax::Ident { .. } => "unexpected identifier".to_owned(),
            Syntax::Atom { val, .. } => format!("unexpected token '{val}'"),
            _ => "unexpected token".to_owned(),
        };
        self.error = Some(InterpError::new(pos, unexpected, expected.to_vec()));
        self.push(Syntax::Missing);
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

fn flatten_seq(lhs: Arc<ParserOp>, rhs: Arc<ParserOp>) -> Arc<ParserOp> {
    let mut items = Vec::new();
    match lhs.as_ref() {
        ParserOp::Seq(xs) => items.extend(xs.iter().cloned()),
        _ => items.push(lhs),
    }
    match rhs.as_ref() {
        ParserOp::Seq(xs) => items.extend(xs.iter().cloned()),
        _ => items.push(rhs),
    }
    Arc::new(ParserOp::Seq(items))
}

fn flatten_orelse(lhs: Arc<ParserOp>, rhs: Arc<ParserOp>) -> Arc<ParserOp> {
    let mut items = Vec::new();
    match lhs.as_ref() {
        ParserOp::OrElse(xs) => items.extend(xs.iter().cloned()),
        _ => items.push(lhs),
    }
    match rhs.as_ref() {
        ParserOp::OrElse(xs) => items.extend(xs.iter().cloned()),
        _ => items.push(rhs),
    }
    Arc::new(ParserOp::OrElse(items))
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
            body: (**body).clone(),
            env: env.clone(),
        }),
        CombinatorAst::Let { val, body, .. } => {
            let v = eval_ast(table, def_index, owner, val, env, depth + 1)?;
            env.push(v);
            let res = eval_ast(table, def_index, owner, body, env, depth + 1);
            env.pop();
            res
        }
        CombinatorAst::Seq(lhs, rhs) => {
            let lv = eval_ast(table, def_index, owner, lhs, env, depth + 1)?;
            let lp = expect_parser(owner, lv)?;
            let rv = eval_thunk_or_ast(table, def_index, owner, rhs, env, depth + 1)?;
            let rp = expect_parser(owner, rv)?;
            Ok(EvalVal::Parser(flatten_seq(lp, rp)))
        }
        CombinatorAst::OrElse(lhs, rhs) => {
            let lv = eval_ast(table, def_index, owner, lhs, env, depth + 1)?;
            let lp = expect_parser(owner, lv)?;
            let rv = eval_thunk_or_ast(table, def_index, owner, rhs, env, depth + 1)?;
            let rp = expect_parser(owner, rv)?;
            Ok(EvalVal::Parser(flatten_orelse(lp, rp)))
        }
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
        "Lean.Parser.Command.commentBody" | "Lean.Parser.Command.versoCommentBody" => {
            Ok(EvalVal::Parser(Arc::new(ParserOp::CommentBody)))
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
        "Lean.interpolatedStrKind" => Ok(EvalVal::Name(Name::from_components(["interpolatedStr"]))),
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

    // Direct specialized intercepts for context-adapting & syntax-transform helpers
    // whose bodies construct Lean lambdas over `CacheableParserContext` or `Syntax`.
    match fname.as_str() {
        "Lean.Parser.withForbidden" if args.len() == 2 => {
            let tk = expect_str(
                owner,
                eval_ast(table, def_index, owner, &args[0], env, depth)?,
            )?;
            let p = expect_parser(
                owner,
                eval_ast(table, def_index, owner, &args[1], env, depth)?,
            )?;
            return Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::WithForbidden(tk),
                p,
            ))));
        }
        "Lean.Parser.withoutForbidden" if args.len() == 1 => {
            let p = expect_parser(
                owner,
                eval_ast(table, def_index, owner, &args[0], env, depth)?,
            )?;
            return Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::WithoutForbidden,
                p,
            ))));
        }
        "Lean.Parser.withoutPosition" if args.len() == 1 => {
            let p = expect_parser(
                owner,
                eval_ast(table, def_index, owner, &args[0], env, depth)?,
            )?;
            return Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::WithoutPosition,
                p,
            ))));
        }
        "Lean.Parser.suppressInsideQuot" if args.len() == 1 => {
            let p = expect_parser(
                owner,
                eval_ast(table, def_index, owner, &args[0], env, depth)?,
            )?;
            return Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::SuppressInsideQuot,
                p,
            ))));
        }
        "Lean.Parser.incQuotDepth" if args.len() == 1 => {
            let p = expect_parser(
                owner,
                eval_ast(table, def_index, owner, &args[0], env, depth)?,
            )?;
            return Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::AddQuotDepth(1),
                p,
            ))));
        }
        "Lean.Parser.decQuotDepth" if args.len() == 1 => {
            let p = expect_parser(
                owner,
                eval_ast(table, def_index, owner, &args[0], env, depth)?,
            )?;
            return Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::AddQuotDepth(-1),
                p,
            ))));
        }
        "_private.Lean.Parser.Basic.0.Lean.Parser.addQuotDepth" if args.len() == 2 => {
            let delta = expect_int(
                owner,
                eval_ast(table, def_index, owner, &args[0], env, depth)?,
            )?;
            let p = expect_parser(
                owner,
                eval_ast(table, def_index, owner, &args[1], env, depth)?,
            )?;
            return Ok(EvalVal::Parser(Arc::new(ParserOp::AdaptContext(
                ContextTransform::AddQuotDepth(delta as i32),
                p,
            ))));
        }
        "Lean.Parser.many1Unbox" if args.len() == 1 => {
            let p = expect_parser(
                owner,
                eval_ast(table, def_index, owner, &args[0], env, depth)?,
            )?;
            return Ok(EvalVal::Parser(Arc::new(ParserOp::Many1Unbox(p))));
        }
        "Lean.Parser.recover" if args.len() == 2 => {
            let p = expect_parser(
                owner,
                eval_ast(table, def_index, owner, &args[0], env, depth)?,
            )?;
            let h = expect_parser(
                owner,
                eval_ast(table, def_index, owner, &args[1], env, depth)?,
            )?;
            return Ok(EvalVal::Parser(Arc::new(ParserOp::Recover {
                parser: p,
                handler: h,
            })));
        }
        "Lean.Parser.recover'" if args.len() == 2 => {
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
        "_private.Lean.Parser.Command.0.Lean.Parser.Command.skipUntil" if args.len() == 1 => {
            let pred = extract_skip_until_pred(&args[0]);
            return Ok(EvalVal::Parser(Arc::new(ParserOp::SkipUntil(pred))));
        }
        // Verso doc switches (default false on Prelude and standard Lean unless `doc.verso` is set)
        "Lean.Doc.Parser.ifVerso" | "Lean.Doc.Parser.ifVersoModuleDocs" if args.len() == 2 => {
            return eval_ast(table, def_index, owner, &args[1], env, depth);
        }
        "Lean.Doc.Parser.withoutVersoSyntax" if args.len() == 1 => {
            return eval_ast(table, def_index, owner, &args[0], env, depth);
        }
        _ => {}
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

    match fname.as_str() {
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
            body: CombinatorAst::Var {
                name: "x".to_owned(),
                idx: 0,
            },
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
        // `FirstTokens.unknown` primitives (exact match to `Basic.lean`)
        ParserOp::PushNone
        | ParserOp::Eoi
        | ParserOp::RawCh { .. }
        | ParserOp::RawIdent
        | ParserOp::CommentBody
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

fn is_none_stx(stx: &Syntax, null_kind: &Name) -> bool {
    matches!(stx, Syntax::Node { kind, args, .. } if kind == null_kind && args.is_empty())
}

fn is_antiquot(stx: &Syntax) -> bool {
    matches!(stx, Syntax::Node { kind, .. } if matches!(kind.leaf_view(), LeafView::Str("antiquot")))
}

fn is_antiquots(stx: &Syntax, choice_kind: &Name) -> bool {
    if is_antiquot(stx) {
        return true;
    }
    if let Syntax::Node { kind, args, .. } = stx
        && kind == choice_kind
        && !args.is_empty()
    {
        return args.iter().all(|a| is_antiquots(a, choice_kind));
    }
    false
}

fn is_ident_stx(stx: &Syntax) -> bool {
    matches!(stx, Syntax::Ident { .. }) || is_antiquot(stx)
}

fn get_tail_info(stx: &Syntax) -> SourceInfo {
    match stx {
        Syntax::Missing => SourceInfo::None,
        Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => *info,
        Syntax::Node { info, args, .. } => {
            for arg in args.iter().rev() {
                let tail = get_tail_info(arg);
                if !matches!(tail, SourceInfo::None) {
                    return tail;
                }
            }
            *info
        }
    }
}

fn set_tail_info(stx: &mut Syntax, new_info: SourceInfo) -> bool {
    match stx {
        Syntax::Missing => false,
        Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
            if matches!(info, SourceInfo::None) {
                false
            } else {
                *info = new_info;
                true
            }
        }
        Syntax::Node { info, args, .. } => {
            for arg in args.iter_mut().rev() {
                if set_tail_info(arg, new_info) {
                    return true;
                }
            }
            if matches!(info, SourceInfo::None) {
                false
            } else {
                *info = new_info;
                true
            }
        }
    }
}

fn get_head_info(stx: &Syntax) -> Option<SourceInfo> {
    match stx {
        Syntax::Missing => None,
        Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
            (!matches!(info, SourceInfo::None)).then_some(*info)
        }
        Syntax::Node { info, args, .. } => {
            if !matches!(info, SourceInfo::None) {
                return Some(*info);
            }
            for arg in args {
                if let Some(found) = get_head_info(arg) {
                    return Some(found);
                }
            }
            None
        }
    }
}

fn set_head_info(stx: &mut Syntax, new_info: SourceInfo) -> bool {
    match stx {
        Syntax::Missing => false,
        Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
            if matches!(info, SourceInfo::None) {
                false
            } else {
                *info = new_info;
                true
            }
        }
        Syntax::Node { info, args, .. } => {
            if !matches!(info, SourceInfo::None) {
                *info = new_info;
                return true;
            }
            for arg in args {
                if set_head_info(arg, new_info) {
                    return true;
                }
            }
            false
        }
    }
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

fn first_pos_of(stx: &Syntax) -> Option<usize> {
    get_head_info(stx).and_then(|info| info.pos(false).map(|p| p.0))
}

fn check_tail_ws(prev: &Syntax) -> bool {
    matches!(
        get_tail_info(prev),
        SourceInfo::Original { trailing, .. } if trailing.end().0 > trailing.start().0
    )
}

fn check_tail_no_ws(prev: &Syntax) -> bool {
    matches!(
        get_tail_info(prev),
        SourceInfo::Original { trailing, .. } if trailing.end().0 == trailing.start().0
    )
}

fn check_tail_linebreak(source: &SourceText, prev: &Syntax) -> bool {
    matches!(
        get_tail_info(prev),
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
