//! **fln-parse** — Vellum's engine — the extensible Pratt parser preserving
//! parse/elaborate interleaving, byte-exact positions, and error recovery that
//! never changes acceptance (plan §9).
//!
//! The general Pratt/category machinery lives in the modules below. The
//! [`parse_definition`] entry point is deliberately much smaller: it is the
//! first production command seam for `fln-elab` and accepts exact `Nat`/`String`
//! signatures followed by a matching literal, identifier, parenthesized first-order
//! application, pin-precedence bounded scalar infix expression (including
//! non-associative Nat/String `==`), or non-recursive
//! local let chain with optional exact scalar type ascriptions over those forms.
//! [`parse_source_command`] also builds the pin's canonical
//! `Lean.Parser.Command.eval` and `Lean.Parser.Command.check` trees for bounded
//! `#eval` and `#check` commands, so expressions reach elaboration without
//! fabricating and reparsing definition bytes.
//! [`parse_nat_definition`]
//! retains the original Nat-only authority. Both use the same source view,
//! lexer, attachment, and canonical `Syntax` shape as the general engine. Being
//! outside these seed grammars is a typed refusal, not a claim that the source is
//! invalid Lean.

#![forbid(unsafe_code)]

pub mod build;
pub mod category;
pub mod macro_expand;
pub mod macro_txn;
pub mod pratt;
pub mod recovery;
pub mod registry;
pub mod state;

use build::{BuildError, Leaves};
use fln_core::name::Name;
use fln_syntax::literal::LiteralKind;
use fln_syntax::run::{Event, lex_run};
pub use fln_syntax::source::BytePos;
use fln_syntax::source::{ByteSpan, SourceError, SourceInfo, SourceText};
use fln_syntax::token::{LexedToken, TokenKind, TokenTable};
use fln_syntax::tree::Syntax;
use fln_syntax::view::SourceView;

/// One lexical refusal, mapped back from the parser's normalized view to the
/// original source bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseDiagnostic {
    pub message: &'static str,
    pub at: BytePos,
}

/// The next form required by the first command grammar slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatDefinitionExpectation {
    ImportOrCommand,
    ImportedModule,
    EndOfImportCommand,
    DefinitionKeyword,
    DeclarationIdentifier,
    ParameterIdentifier,
    ParameterTypeAscription,
    NaturalType,
    ScalarType,
    ClosingParenthesis,
    Assignment,
    LocalIdentifier,
    LocalAssignment,
    LetSeparator,
    NaturalValue,
    ScalarValue,
    EndOfCommand,
}

/// Why the bounded source command parser refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatDefinitionParseError {
    Source(SourceError),
    /// The seed token table could not classify some bytes. This is a diagnostic
    /// from this bounded driver, not a proof that a complete Lean grammar would
    /// reject those bytes.
    Lexical {
        diagnostics: Vec<ParseDiagnostic>,
    },
    /// The bytes may be valid Lean; they are simply outside this first command
    /// grammar. No source-level rejection can be inferred from this variant.
    OutsideSeedGrammar {
        at: BytePos,
        expected: NatDefinitionExpectation,
    },
    Build(BuildError),
}

impl std::fmt::Display for NatDefinitionParseError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Source(error) => write!(formatter, "{error}"),
            Self::Lexical { diagnostics } => match diagnostics.first() {
                Some(first) => write!(
                    formatter,
                    "lexical analysis reported {} diagnostic(s); first {}: {}",
                    diagnostics.len(),
                    first.at,
                    first.message
                ),
                None => write!(
                    formatter,
                    "lexical analysis returned an empty diagnostic set"
                ),
            },
            Self::OutsideSeedGrammar { at, expected } => write!(
                formatter,
                "source is outside the bounded source grammar at {at}; expected {expected:?}"
            ),
            Self::Build(error) => write!(formatter, "syntax construction failed: {error:?}"),
        }
    }
}

impl std::error::Error for NatDefinitionParseError {}

impl NatDefinitionParseError {
    /// Rebase a command-local refusal into its containing source file.
    ///
    /// Partitioned commands are parsed as independent slices so their syntax
    /// retains the existing single-command shape. This projection keeps every
    /// source refusal in the original file's coordinate system. Internal syntax
    /// construction faults carry no user-facing parser position and are retained
    /// unchanged.
    pub fn with_original_offset(self, offset: BytePos) -> Self {
        let shifted = |at: BytePos| BytePos(at.0.saturating_add(offset.0));
        match self {
            Self::Source(SourceError::NotUtf8 { at }) => {
                Self::Source(SourceError::NotUtf8 { at: shifted(at) })
            }
            Self::Lexical { diagnostics } => Self::Lexical {
                diagnostics: diagnostics
                    .into_iter()
                    .map(|diagnostic| ParseDiagnostic {
                        message: diagnostic.message,
                        at: shifted(diagnostic.at),
                    })
                    .collect(),
            },
            Self::OutsideSeedGrammar { at, expected } => Self::OutsideSeedGrammar {
                at: shifted(at),
                expected,
            },
            Self::Build(error) => Self::Build(error),
        }
    }

    /// Rebase a refusal from a normalized command slice into the original file.
    ///
    /// Recovery parses each `def`…`def` slice as an independent buffer, so the
    /// seed parser's positions are slice-local and LF-normalized. Adding the
    /// original start as a raw offset is wrong once a later command still
    /// contains collapsed CRLF: the local coordinate is a view offset, and the
    /// original byte is [`SourceView::to_original`] of `start + local`.
    pub fn rebase_from_normalized_slice(self, view: &SourceView, start: BytePos) -> Self {
        let mapped = |at: BytePos| view.to_original(BytePos(start.0.saturating_add(at.0)));
        match self {
            Self::Source(SourceError::NotUtf8 { at }) => {
                Self::Source(SourceError::NotUtf8 { at: mapped(at) })
            }
            Self::Lexical { diagnostics } => Self::Lexical {
                diagnostics: diagnostics
                    .into_iter()
                    .map(|diagnostic| ParseDiagnostic {
                        message: diagnostic.message,
                        at: mapped(diagnostic.at),
                    })
                    .collect(),
            },
            Self::OutsideSeedGrammar { at, expected } => Self::OutsideSeedGrammar {
                at: mapped(at),
                expected,
            },
            Self::Build(error) => Self::Build(error),
        }
    }
}

impl From<BuildError> for NatDefinitionParseError {
    fn from(error: BuildError) -> Self {
        NatDefinitionParseError::Build(error)
    }
}

/// A command tree together with the normalized source coordinate system its
/// leaves name. Keeping the view makes both the byte-exact original and the
/// parser-visible text recoverable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedDefinition {
    source_view: SourceView,
    syntax: Syntax,
    epilogue: ByteSpan,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExplicitBinderTokens {
    open: usize,
    names: std::ops::Range<usize>,
    colon: usize,
    type_name: usize,
    close: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LetBindingTokens {
    keyword: usize,
    name: usize,
    explicit_type: Option<(usize, usize)>,
    assignment: usize,
    value: std::ops::Range<usize>,
    separator: usize,
}

struct BoundedTermFrame {
    open: Option<usize>,
    application: Vec<(Syntax, usize)>,
    operands: Vec<(Syntax, usize)>,
    operators: Vec<BoundedInfixToken>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundedInfix {
    ScalarBeq,
    NatLor,
    NatXor,
    NatLand,
    NatAdd,
    NatSub,
    StringAppend,
    NatMul,
    NatDiv,
    NatMod,
    NatShiftLeft,
    NatShiftRight,
    NatPow,
    NatDecLe,
    NatDecLt,
}

impl BoundedInfix {
    const fn symbol(self) -> &'static str {
        match self {
            Self::ScalarBeq => "==",
            Self::NatLor => "|||",
            Self::NatXor => "^^^",
            Self::NatLand => "&&&",
            Self::NatAdd => "+",
            Self::NatSub => "-",
            Self::StringAppend => "++",
            Self::NatMul => "*",
            Self::NatDiv => "/",
            Self::NatMod => "%",
            Self::NatShiftLeft => "<<<",
            Self::NatShiftRight => ">>>",
            Self::NatPow => "^",
            Self::NatDecLe => "<=",
            Self::NatDecLt => "<",
        }
    }
    const fn precedence(self) -> u8 {
        match self {
            Self::ScalarBeq => 50,
            Self::NatLor => 55,
            Self::NatXor => 58,
            Self::NatLand => 60,
            Self::NatAdd | Self::NatSub | Self::StringAppend => 65,
            Self::NatMul | Self::NatDiv | Self::NatMod => 70,
            Self::NatShiftLeft | Self::NatShiftRight => 75,
            Self::NatPow => 80,
            Self::NatDecLe | Self::NatDecLt => 50,
        }
    }

    const fn is_right_associative(self) -> bool {
        matches!(self, Self::NatPow)
    }

    const fn is_non_associative(self) -> bool {
        matches!(self, Self::ScalarBeq)
    }

    fn syntax_kind(self) -> Name {
        Name::str(Name::anonymous(), format!("term_{}_", self.symbol()))
    }
}

struct BoundedInfixToken {
    operator: BoundedInfix,
    syntax: Syntax,
    at: usize,
}

impl ParsedDefinition {
    pub fn syntax(&self) -> &Syntax {
        &self.syntax
    }

    pub fn source_view(&self) -> &SourceView {
        &self.source_view
    }

    pub const fn epilogue(&self) -> ByteSpan {
        self.epilogue
    }

    pub fn reconstruct_normalized(&self) -> Option<Vec<u8>> {
        self.syntax
            .reconstruct(self.source_view.normalized(), self.epilogue)
    }

    pub fn reconstruct_original(&self) -> Vec<u8> {
        self.source_view.reconstruct_original()
    }
}

/// The exact tree type returned by the original Nat-only source door.
///
/// The alias preserves that public API while [`parse_definition`] admits the
/// same canonical tree shape for the wider, still-bounded Nat/String slice.
pub type ParsedNatDefinition = ParsedDefinition;

/// Compatibility name for callers using the wider bounded source door.
pub type DefinitionParseError = NatDefinitionParseError;

/// Which supported source command produced a bounded command tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceCommandKind {
    Definition,
    Evaluation,
    Check,
}

/// One command accepted by the bounded source facade.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedSourceCommand {
    kind: SourceCommandKind,
    source_view: SourceView,
    syntax: Syntax,
    epilogue: ByteSpan,
    query_term: Option<ByteSpan>,
}

impl ParsedSourceCommand {
    pub const fn kind(&self) -> SourceCommandKind {
        self.kind
    }

    pub fn syntax(&self) -> &Syntax {
        &self.syntax
    }

    pub fn source_view(&self) -> &SourceView {
        &self.source_view
    }

    pub const fn epilogue(&self) -> ByteSpan {
        self.epilogue
    }

    pub fn reconstruct_normalized(&self) -> Option<Vec<u8>> {
        self.syntax
            .reconstruct(self.source_view.normalized(), self.epilogue)
    }

    pub fn reconstruct_original(&self) -> Vec<u8> {
        self.source_view.reconstruct_original()
    }

    /// Reconstruct the source-covered query term for `#eval` or `#check`.
    /// Definitions have no command-query payload and return `None`.
    pub fn query_term_normalized(&self) -> Option<&str> {
        if self.kind == SourceCommandKind::Definition {
            return None;
        }
        self.source_view.normalized().span_str(self.query_term?)
    }
}

/// One bounded source module split into its direct import names and command
/// slices.
///
/// This is a lexical command boundary, not a module resolver. In particular,
/// returning an import name grants it no environment authority; the caller must
/// resolve the complete import graph before any command is elaborated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartitionedSourceModule<'source> {
    pub imports: Vec<Name>,
    pub commands: Vec<(BytePos, &'source [u8])>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DefinitionGrammar {
    NatOnly,
    Scalar,
}

impl DefinitionGrammar {
    fn accepts_type(self, name: &Name) -> bool {
        name == &Name::from_components(["Nat"])
            || (self == Self::Scalar
                && (name == &Name::from_components(["String"])
                    || name == &Name::from_components(["Bool"])))
    }

    const fn type_expectation(self) -> NatDefinitionExpectation {
        match self {
            Self::NatOnly => NatDefinitionExpectation::NaturalType,
            Self::Scalar => NatDefinitionExpectation::ScalarType,
        }
    }

    const fn value_expectation(self) -> NatDefinitionExpectation {
        match self {
            Self::NatOnly => NatDefinitionExpectation::NaturalValue,
            Self::Scalar => NatDefinitionExpectation::ScalarValue,
        }
    }
}

fn parser_kind(components: &[&str]) -> Name {
    let mut name = Name::from_components(["Lean", "Parser"]);
    for component in components {
        name = Name::str(name, *component);
    }
    name
}

fn null_node(args: Vec<Syntax>) -> Syntax {
    Syntax::node(state::null_kind(), args)
}

fn nat_definition_token_table() -> TokenTable {
    TokenTable::from_tokens([
        "def", "let", "(", ")", ":", ":=", ";", "==", "|||", "^^^", "&&&", "+", "-", "++", "*",
        "/", "%", "<<<", ">>>", "^", "<=", "<",
    ])
}

fn source_module_token_table() -> TokenTable {
    TokenTable::from_tokens([
        "import", "def", "#eval", "#check", "let", "(", ")", ":", ":=", ";", "==", "|||", "^^^",
        "&&&", "+", "-", "++", "*", "/", "%", "<<<", ">>>", "^", "<=", "<",
    ])
}

fn bounded_infix(kind: Option<&TokenKind>, grammar: DefinitionGrammar) -> Option<BoundedInfix> {
    let Some(TokenKind::Symbol(symbol)) = kind else {
        return None;
    };
    match symbol.as_str() {
        "==" if grammar == DefinitionGrammar::Scalar => Some(BoundedInfix::ScalarBeq),
        "|||" => Some(BoundedInfix::NatLor),
        "^^^" => Some(BoundedInfix::NatXor),
        "&&&" => Some(BoundedInfix::NatLand),
        "+" => Some(BoundedInfix::NatAdd),
        "-" => Some(BoundedInfix::NatSub),
        "++" if grammar == DefinitionGrammar::Scalar => Some(BoundedInfix::StringAppend),
        "*" => Some(BoundedInfix::NatMul),
        "/" => Some(BoundedInfix::NatDiv),
        "%" => Some(BoundedInfix::NatMod),
        "<=" => Some(BoundedInfix::NatDecLe),
        "<" => Some(BoundedInfix::NatDecLt),
        "<<<" => Some(BoundedInfix::NatShiftLeft),
        ">>>" => Some(BoundedInfix::NatShiftRight),
        "^" => Some(BoundedInfix::NatPow),
        _ => None,
    }
}

fn original_position(view: &SourceView, tokens: &[LexedToken], index: usize) -> BytePos {
    let in_view = tokens
        .get(index)
        .map_or(BytePos(view.normalized().len_bytes()), |token| {
            token.extent.start()
        });
    view.to_original(in_view)
}

fn is_bounded_term_atom(kind: Option<&TokenKind>, grammar: DefinitionGrammar) -> bool {
    matches!(
        kind,
        Some(TokenKind::Literal(LiteralKind::Nat) | TokenKind::Ident(_))
    ) || (grammar == DefinitionGrammar::Scalar
        && matches!(kind, Some(TokenKind::Literal(LiteralKind::Str))))
}

fn bounded_term_leaf(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    index: usize,
    grammar: DefinitionGrammar,
) -> Result<Syntax, NatDefinitionParseError> {
    let leaf = leaves.leaf(index)?;
    match tokens.get(index).map(|token| &token.kind) {
        Some(TokenKind::Literal(LiteralKind::Nat)) => Ok(Syntax::node(
            Name::str(Name::anonymous(), "num"),
            vec![leaf],
        )),
        Some(TokenKind::Literal(LiteralKind::Str)) if grammar == DefinitionGrammar::Scalar => Ok(
            Syntax::node(Name::str(Name::anonymous(), "str"), vec![leaf]),
        ),
        Some(TokenKind::Ident(_)) => Ok(leaf),
        _ => Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, index),
            expected: grammar.value_expectation(),
        }),
    }
}

/// The let-body separator is the first `;` at parenthesis depth 0.
/// Scanning for the first `;` anywhere splits `let x := (1; 2); x` at the
/// inner semicolon, leaving `(1` as the value — fail-closed with the wrong
/// cut. Nested `let` in parens is outside the seed term grammar either way;
/// the depth walk makes the refusal land on the leftover token, not an
/// unclosed `(`.
fn find_let_separator(tokens: &[LexedToken], from: usize) -> Option<usize> {
    let mut depth = 0usize;
    for index in from..tokens.len() {
        match tokens.get(index).map(|token| &token.kind) {
            Some(TokenKind::Symbol(symbol)) if symbol == "(" => depth += 1,
            Some(TokenKind::Symbol(symbol)) if symbol == ")" => {
                depth = depth.saturating_sub(1);
            }
            Some(TokenKind::Symbol(symbol)) if symbol == ";" && depth == 0 => {
                return Some(index);
            }
            _ => {}
        }
    }
    None
}

fn bounded_let_bindings(
    view: &SourceView,
    tokens: &[LexedToken],
    mut body_start: usize,
    grammar: DefinitionGrammar,
) -> Result<(Vec<LetBindingTokens>, usize), NatDefinitionParseError> {
    let mut let_bindings = Vec::new();
    while matches!(
        tokens.get(body_start).map(|token| &token.kind),
        Some(TokenKind::Symbol(symbol)) if symbol == "let"
    ) {
        let keyword = body_start;
        let name = keyword + 1;
        if !matches!(
            tokens.get(name).map(|token| &token.kind),
            Some(TokenKind::Ident(_))
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(view, tokens, name),
                expected: NatDefinitionExpectation::LocalIdentifier,
            });
        }
        let mut declaration_cursor = name + 1;
        let explicit_type = if matches!(
            tokens.get(declaration_cursor).map(|token| &token.kind),
            Some(TokenKind::Symbol(symbol)) if symbol == ":"
        ) {
            let colon = declaration_cursor;
            declaration_cursor += 1;
            if !matches!(
                tokens.get(declaration_cursor).map(|token| &token.kind),
                Some(TokenKind::Ident(name)) if grammar.accepts_type(name)
            ) {
                return Err(NatDefinitionParseError::OutsideSeedGrammar {
                    at: original_position(view, tokens, declaration_cursor),
                    expected: grammar.type_expectation(),
                });
            }
            let type_name = declaration_cursor;
            declaration_cursor += 1;
            Some((colon, type_name))
        } else {
            None
        };
        let assignment = declaration_cursor;
        if !matches!(
            tokens.get(assignment).map(|token| &token.kind),
            Some(TokenKind::Symbol(symbol)) if symbol == ":="
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(view, tokens, assignment),
                expected: NatDefinitionExpectation::LocalAssignment,
            });
        }
        let value_start = assignment + 1;
        let Some(separator) = find_let_separator(tokens, value_start) else {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(view, tokens, tokens.len()),
                expected: NatDefinitionExpectation::LetSeparator,
            });
        };
        let_bindings.push(LetBindingTokens {
            keyword,
            name,
            explicit_type,
            assignment,
            value: value_start..separator,
            separator,
        });
        body_start = separator + 1;
    }
    Ok((let_bindings, body_start))
}

fn bounded_value_syntax(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    let_bindings: Vec<LetBindingTokens>,
    body_start: usize,
    grammar: DefinitionGrammar,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut value = bounded_term(leaves, view, tokens, body_start..tokens.len(), grammar)?;
    for binding in let_bindings.into_iter().rev() {
        let local_value = bounded_term(leaves, view, tokens, binding.value, grammar)?;
        let explicit_type = match binding.explicit_type {
            Some((colon, type_name)) => null_node(vec![Syntax::node(
                parser_kind(&["Term", "typeSpec"]),
                vec![leaves.leaf(colon)?, leaves.leaf(type_name)?],
            )]),
            None => null_node(Vec::new()),
        };
        let local_id = Syntax::node(
            parser_kind(&["Term", "letId"]),
            vec![leaves.leaf(binding.name)?],
        );
        let local_declaration = Syntax::node(
            parser_kind(&["Term", "letIdDecl"]),
            vec![
                local_id,
                null_node(Vec::new()),
                explicit_type,
                leaves.leaf(binding.assignment)?,
                local_value,
            ],
        );
        value = Syntax::node(
            parser_kind(&["Term", "let"]),
            vec![
                leaves.leaf(binding.keyword)?,
                Syntax::node(
                    parser_kind(&["Term", "letConfig"]),
                    vec![null_node(Vec::new())],
                ),
                Syntax::node(parser_kind(&["Term", "letDecl"]), vec![local_declaration]),
                leaves.leaf(binding.separator)?,
                value,
            ],
        );
    }
    Ok(value)
}

fn finish_bounded_application(
    view: &SourceView,
    tokens: &[LexedToken],
    mut terms: Vec<(Syntax, usize)>,
    grammar: DefinitionGrammar,
    empty_at: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    let Some((_, first_index)) = terms.first() else {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, empty_at),
            expected: grammar.value_expectation(),
        });
    };
    if terms.len() == 1 {
        return Ok(terms.pop().expect("the nonempty term has one member").0);
    }
    if !matches!(
        tokens.get(*first_index).map(|token| &token.kind),
        Some(TokenKind::Ident(_))
    ) {
        let at = terms.get(1).map_or(*first_index, |(_, index)| *index);
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, at),
            expected: NatDefinitionExpectation::EndOfCommand,
        });
    }
    let mut terms = terms.into_iter();
    let head = terms.next().expect("the nonempty application has a head").0;
    let arguments = terms.map(|(term, _)| term).collect();
    Ok(Syntax::node(
        parser_kind(&["Term", "app"]),
        vec![head, null_node(arguments)],
    ))
}

fn reduce_bounded_infix(
    view: &SourceView,
    tokens: &[LexedToken],
    frame: &mut BoundedTermFrame,
    grammar: DefinitionGrammar,
) -> Result<(), NatDefinitionParseError> {
    let Some(operator) = frame.operators.pop() else {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, tokens.len()),
            expected: grammar.value_expectation(),
        });
    };
    let Some((right, _)) = frame.operands.pop() else {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, operator.at),
            expected: grammar.value_expectation(),
        });
    };
    let Some((left, left_at)) = frame.operands.pop() else {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, operator.at),
            expected: grammar.value_expectation(),
        });
    };
    frame.operands.push((
        Syntax::node(
            operator.operator.syntax_kind(),
            vec![left, operator.syntax, right],
        ),
        left_at,
    ));
    Ok(())
}

fn push_bounded_operand(
    view: &SourceView,
    tokens: &[LexedToken],
    frame: &mut BoundedTermFrame,
    grammar: DefinitionGrammar,
    empty_at: usize,
) -> Result<(), NatDefinitionParseError> {
    let application = std::mem::take(&mut frame.application);
    let first_at = application.first().map_or(empty_at, |(_, at)| *at);
    let term = finish_bounded_application(view, tokens, application, grammar, empty_at)?;
    frame.operands.push((term, first_at));
    Ok(())
}

fn push_bounded_infix(
    view: &SourceView,
    tokens: &[LexedToken],
    frame: &mut BoundedTermFrame,
    grammar: DefinitionGrammar,
    operator: BoundedInfix,
    index: usize,
    syntax: Syntax,
) -> Result<(), NatDefinitionParseError> {
    push_bounded_operand(view, tokens, frame, grammar, index)?;
    while frame
        .operators
        .last()
        .is_some_and(|previous| previous.operator.precedence() > operator.precedence())
    {
        reduce_bounded_infix(view, tokens, frame, grammar)?;
    }
    if frame.operators.last().is_some_and(|previous| {
        previous.operator.precedence() == operator.precedence()
            && (previous.operator.is_non_associative() || operator.is_non_associative())
    }) {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, index),
            expected: NatDefinitionExpectation::EndOfCommand,
        });
    }
    while frame.operators.last().is_some_and(|previous| {
        previous.operator.precedence() == operator.precedence() && !operator.is_right_associative()
    }) {
        reduce_bounded_infix(view, tokens, frame, grammar)?;
    }
    frame.operators.push(BoundedInfixToken {
        operator,
        syntax,
        at: index,
    });
    Ok(())
}

fn finish_bounded_frame(
    view: &SourceView,
    tokens: &[LexedToken],
    mut frame: BoundedTermFrame,
    grammar: DefinitionGrammar,
    empty_at: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    push_bounded_operand(view, tokens, &mut frame, grammar, empty_at)?;
    while !frame.operators.is_empty() {
        reduce_bounded_infix(view, tokens, &mut frame, grammar)?;
    }
    if frame.operands.len() != 1 {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, empty_at),
            expected: grammar.value_expectation(),
        });
    }
    Ok(frame
        .operands
        .pop()
        .expect("the bounded frame has exactly one result")
        .0)
}

fn hygiene_ident() -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::empty_at(BytePos(0)),
        val: Name::anonymous(),
        preresolved: Vec::new(),
    }
}

fn hygienic_lparen(lparen: Syntax) -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "hygienicLParen"]),
        vec![
            lparen,
            Syntax::node(
                Name::str(Name::anonymous(), "hygieneInfo"),
                vec![hygiene_ident()],
            ),
        ],
    )
}

fn bounded_term(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: std::ops::Range<usize>,
    grammar: DefinitionGrammar,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut frames = vec![BoundedTermFrame {
        open: None,
        application: Vec::new(),
        operands: Vec::new(),
        operators: Vec::new(),
    }];
    for index in range.clone() {
        match tokens.get(index).map(|token| &token.kind) {
            kind if is_bounded_term_atom(kind, grammar) => {
                let term = bounded_term_leaf(leaves, view, tokens, index, grammar)?;
                frames
                    .last_mut()
                    .expect("the root term frame remains live")
                    .application
                    .push((term, index));
            }
            Some(TokenKind::Symbol(symbol)) if symbol == "(" => {
                frames.push(BoundedTermFrame {
                    open: Some(index),
                    application: Vec::new(),
                    operands: Vec::new(),
                    operators: Vec::new(),
                });
            }
            Some(TokenKind::Symbol(symbol)) if symbol == ")" => {
                if frames.len() == 1 {
                    return Err(NatDefinitionParseError::OutsideSeedGrammar {
                        at: original_position(view, tokens, index),
                        expected: NatDefinitionExpectation::EndOfCommand,
                    });
                }
                let frame = frames
                    .pop()
                    .expect("a closing parenthesis has an inner frame");
                let open = frame.open.expect("only the root frame lacks an opener");
                let inner = finish_bounded_frame(view, tokens, frame, grammar, index)?;
                let grouped = Syntax::node(
                    parser_kind(&["Term", "paren"]),
                    vec![
                        hygienic_lparen(leaves.leaf(open)?),
                        inner,
                        leaves.leaf(index)?,
                    ],
                );
                frames
                    .last_mut()
                    .expect("the parent term frame remains live")
                    .application
                    .push((grouped, open));
            }
            kind if bounded_infix(kind, grammar).is_some() => {
                let operator = bounded_infix(kind, grammar)
                    .expect("the guarded bounded infix remains recognized");
                let syntax = leaves.leaf(index)?;
                let frame = frames.last_mut().expect("the root term frame remains live");
                push_bounded_infix(view, tokens, frame, grammar, operator, index, syntax)?;
            }
            _ => {
                return Err(NatDefinitionParseError::OutsideSeedGrammar {
                    at: original_position(view, tokens, index),
                    expected: grammar.value_expectation(),
                });
            }
        }
    }
    if frames.len() != 1 {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(view, tokens, range.end),
            expected: NatDefinitionExpectation::ClosingParenthesis,
        });
    }
    let frame = frames.pop().expect("the bounded term has a root frame");
    finish_bounded_frame(view, tokens, frame, grammar, range.end)
}

/// Parse the first production command subset:
///
/// ```text
/// def <identifier> (<identifier>+ : Nat)* (: Nat)? := <natural-literal-or-identifier>
/// def <identifier> (<identifier>+ : Nat)* (: Nat)? := <identifier> <natural-literal-or-identifier>+
/// def <identifier> (<identifier>+ : Nat)* (: Nat)? :=
///   (let <identifier> (: Nat)? := <bounded-term>;)+ <bounded-term>
/// <bounded-term> ::= <application> | <bounded-term> <bounded-infix> <bounded-term>
/// <application> ::= <atom> | <identifier> <bounded-atom>+ | `(` <bounded-term> `)`
/// ```
///
pub fn parse_nat_definition(source: &[u8]) -> Result<ParsedNatDefinition, NatDefinitionParseError> {
    parse_definition_with_grammar(source, DefinitionGrammar::NatOnly)
}

/// Parse the bounded first-order source slice over exact `Nat`, `String`, and
/// `Bool` binder/result types, literals, references, applications, and local
/// lets.
///
/// This does not claim general Lean elaboration. Unsupported syntax remains a
/// typed [`NatDefinitionParseError::OutsideSeedGrammar`] refusal.
pub fn parse_definition(source: &[u8]) -> Result<ParsedDefinition, DefinitionParseError> {
    parse_definition_with_grammar(source, DefinitionGrammar::Scalar)
}

/// Parse one bounded `def`, `#eval`, or `#check` command.
///
/// `#eval <term>` and `#check <term>` become the pin's canonical command trees.
/// Evaluation is deliberately a terminal-command execution seam, not a second
/// evaluator: `fln-elab` gives the expression an unspellable generated
/// declaration identity before K1 admission, then the ordinary compiler and
/// Golem path execute the checked artifact. Checking retains the same source
/// term span but neither compiles nor executes it.
pub fn parse_source_command(source: &[u8]) -> Result<ParsedSourceCommand, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let run = lex_run(view.normalized(), &source_module_token_table());
    let diagnostics = run
        .diagnostics()
        .into_iter()
        .map(|(message, at)| ParseDiagnostic {
            message,
            at: view.to_original(at),
        })
        .collect::<Vec<_>>();
    if !diagnostics.is_empty() {
        return Err(NatDefinitionParseError::Lexical { diagnostics });
    }
    let first = run.events.iter().find_map(|event| match event {
        Event::Token(token) => Some(token),
        Event::Trivia(_) | Event::Refused { .. } => None,
    });
    match first {
        Some(token) => match &token.kind {
            TokenKind::Symbol(symbol) if symbol == "def" => {
                let parsed = parse_definition(source)?;
                Ok(ParsedSourceCommand {
                    kind: SourceCommandKind::Definition,
                    source_view: parsed.source_view,
                    syntax: parsed.syntax,
                    epilogue: parsed.epilogue,
                    query_term: None,
                })
            }
            TokenKind::Symbol(symbol) if symbol == "#eval" || symbol == "#check" => {
                let (kind, command_kind) = if symbol == "#eval" {
                    (SourceCommandKind::Evaluation, "eval")
                } else {
                    (SourceCommandKind::Check, "check")
                };
                let tokens = run
                    .events
                    .into_iter()
                    .filter_map(|event| match event {
                        Event::Token(token) => Some(token),
                        Event::Trivia(_) | Event::Refused { .. } => None,
                    })
                    .collect::<Vec<_>>();
                let (let_bindings, body_start) =
                    bounded_let_bindings(&view, &tokens, 1, DefinitionGrammar::Scalar)?;
                let leaves = Leaves::build(view.normalized(), &tokens)?;
                let epilogue = leaves.attachment().epilogue();
                let value = bounded_value_syntax(
                    &leaves,
                    &view,
                    &tokens,
                    let_bindings,
                    body_start,
                    DefinitionGrammar::Scalar,
                )?;
                let query_term = tokens
                    .get(1)
                    .zip(tokens.last())
                    .and_then(|(first, last)| {
                        ByteSpan::new(first.extent.start(), last.extent.end())
                    })
                    .ok_or(NatDefinitionParseError::OutsideSeedGrammar {
                        at: BytePos(source.len()),
                        expected: NatDefinitionExpectation::ScalarValue,
                    })?;
                Ok(ParsedSourceCommand {
                    kind,
                    source_view: view,
                    syntax: Syntax::node(
                        parser_kind(&["Command", command_kind]),
                        vec![leaves.leaf(0)?, value],
                    ),
                    epilogue,
                    query_term: Some(query_term),
                })
            }
            TokenKind::Ident(_) | TokenKind::Literal(_) | TokenKind::Symbol(_) => {
                Err(NatDefinitionParseError::OutsideSeedGrammar {
                    at: view.to_original(token.extent.start()),
                    expected: NatDefinitionExpectation::DefinitionKeyword,
                })
            }
        },
        None => Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: BytePos(source.len()),
            expected: NatDefinitionExpectation::DefinitionKeyword,
        }),
    }
}

fn parse_definition_with_grammar(
    source: &[u8],
    grammar: DefinitionGrammar,
) -> Result<ParsedDefinition, NatDefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let table = nat_definition_token_table();
    let run = lex_run(view.normalized(), &table);
    let diagnostics = run
        .diagnostics()
        .into_iter()
        .map(|(message, at)| ParseDiagnostic {
            message,
            at: view.to_original(at),
        })
        .collect::<Vec<_>>();
    if !diagnostics.is_empty() {
        return Err(NatDefinitionParseError::Lexical { diagnostics });
    }

    let tokens = run
        .events
        .into_iter()
        .filter_map(|event| match event {
            Event::Token(token) => Some(token),
            Event::Trivia(_) | Event::Refused { .. } => None,
        })
        .collect::<Vec<_>>();

    if !matches!(
        tokens.first().map(|token| &token.kind),
        Some(TokenKind::Symbol(symbol)) if symbol == "def"
    ) {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(&view, &tokens, 0),
            expected: NatDefinitionExpectation::DefinitionKeyword,
        });
    }
    if !matches!(
        tokens.get(1).map(|token| &token.kind),
        Some(TokenKind::Ident(_))
    ) {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(&view, &tokens, 1),
            expected: NatDefinitionExpectation::DeclarationIdentifier,
        });
    }
    let mut parameter_groups = Vec::new();
    let mut cursor = 2;
    while matches!(
        tokens.get(cursor).map(|token| &token.kind),
        Some(TokenKind::Symbol(symbol)) if symbol == "("
    ) {
        let open = cursor;
        cursor += 1;
        let names_start = cursor;
        while matches!(
            tokens.get(cursor).map(|token| &token.kind),
            Some(TokenKind::Ident(_))
        ) {
            cursor += 1;
        }
        if cursor == names_start {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, cursor),
                expected: NatDefinitionExpectation::ParameterIdentifier,
            });
        }
        if !matches!(
            tokens.get(cursor).map(|token| &token.kind),
            Some(TokenKind::Symbol(symbol)) if symbol == ":"
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, cursor),
                expected: NatDefinitionExpectation::ParameterTypeAscription,
            });
        }
        let colon = cursor;
        cursor += 1;
        if !matches!(
            tokens.get(cursor).map(|token| &token.kind),
            Some(TokenKind::Ident(name)) if grammar.accepts_type(name)
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, cursor),
                expected: grammar.type_expectation(),
            });
        }
        let type_name = cursor;
        cursor += 1;
        if !matches!(
            tokens.get(cursor).map(|token| &token.kind),
            Some(TokenKind::Symbol(symbol)) if symbol == ")"
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, cursor),
                expected: NatDefinitionExpectation::ClosingParenthesis,
            });
        }
        let close = cursor;
        cursor += 1;
        parameter_groups.push(ExplicitBinderTokens {
            open,
            names: names_start..colon,
            colon,
            type_name,
            close,
        });
    }
    let explicit_result_type = if matches!(
        tokens.get(cursor).map(|token| &token.kind),
        Some(TokenKind::Symbol(symbol)) if symbol == ":"
    ) {
        let colon = cursor;
        cursor += 1;
        if !matches!(
            tokens.get(cursor).map(|token| &token.kind),
            Some(TokenKind::Ident(name)) if grammar.accepts_type(name)
        ) {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: original_position(&view, &tokens, cursor),
                expected: grammar.type_expectation(),
            });
        }
        let type_name = cursor;
        cursor += 1;
        Some((colon, type_name))
    } else {
        None
    };
    let assignment_index = cursor;
    if !matches!(
        tokens.get(assignment_index).map(|token| &token.kind),
        Some(TokenKind::Symbol(symbol)) if symbol == ":="
    ) {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: original_position(&view, &tokens, assignment_index),
            expected: NatDefinitionExpectation::Assignment,
        });
    }
    let value_index = assignment_index + 1;
    let (let_bindings, body_start) = bounded_let_bindings(&view, &tokens, value_index, grammar)?;
    let leaves = Leaves::build(view.normalized(), &tokens)?;
    let epilogue = leaves.attachment().epilogue();
    let definition_keyword = leaves.leaf(0)?;
    let declaration_name = leaves.leaf(1)?;
    let assignment = leaves.leaf(assignment_index)?;

    let modifiers = Syntax::node(
        parser_kind(&["Command", "declModifiers"]),
        vec![
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
            null_node(Vec::new()),
        ],
    );
    let declaration_id = Syntax::node(
        parser_kind(&["Command", "declId"]),
        vec![declaration_name, null_node(Vec::new())],
    );
    let mut parameters = Vec::new();
    for group in parameter_groups {
        let names = group
            .names
            .map(|index| leaves.leaf(index))
            .collect::<Result<Vec<_>, _>>()?;
        parameters.push(Syntax::node(
            parser_kind(&["Term", "explicitBinder"]),
            vec![
                leaves.leaf(group.open)?,
                null_node(names),
                null_node(vec![
                    leaves.leaf(group.colon)?,
                    leaves.leaf(group.type_name)?,
                ]),
                null_node(Vec::new()),
                leaves.leaf(group.close)?,
            ],
        ));
    }
    let result_type = if let Some((colon, type_name)) = explicit_result_type {
        null_node(vec![Syntax::node(
            parser_kind(&["Term", "typeSpec"]),
            vec![leaves.leaf(colon)?, leaves.leaf(type_name)?],
        )])
    } else {
        null_node(Vec::new())
    };
    let optional_signature = Syntax::node(
        parser_kind(&["Command", "optDeclSig"]),
        vec![null_node(parameters), result_type],
    );
    let value = bounded_value_syntax(&leaves, &view, &tokens, let_bindings, body_start, grammar)?;
    let termination = Syntax::node(
        parser_kind(&["Termination", "suffix"]),
        vec![null_node(Vec::new()), null_node(Vec::new())],
    );
    let declaration_value = Syntax::node(
        parser_kind(&["Command", "declValSimple"]),
        vec![assignment, value, termination, null_node(Vec::new())],
    );
    let definition = Syntax::node(
        parser_kind(&["Command", "definition"]),
        vec![
            definition_keyword,
            declaration_id,
            optional_signature,
            declaration_value,
            null_node(Vec::new()),
        ],
    );
    let syntax = Syntax::node(
        parser_kind(&["Command", "declaration"]),
        vec![modifiers, definition],
    );

    Ok(ParsedDefinition {
        source_view: view,
        syntax,
        epilogue,
    })
}

/// Partition one source file into bounded `def`/`#eval`/`#check` command slices.
///
/// This is deliberately a lexical partition, not a second parser. In the seed
/// grammar neither command introducer can occur inside a term, while occurrences
/// in comments remain trivia, so every later introducer begins the next command.
/// Each returned slice is still parsed independently by [`parse_source_command`]
/// (or by the definition-only compatibility entries), which remains the
/// acceptance authority for the bounded source slice.
/// Boundaries are mapped back through [`SourceView`] before slicing, preserving
/// original CRLF bytes exactly.
///
/// A file containing zero or one command token is returned as one slice, including
/// an empty file. That keeps malformed or unsupported input on the parser's typed
/// refusal path instead of misclassifying it as an empty batch.
pub fn partition_definition_commands(
    source: &[u8],
) -> Result<Vec<(BytePos, &[u8])>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let table = source_module_token_table();
    let run = lex_run(view.normalized(), &table);
    let diagnostics = run
        .diagnostics()
        .into_iter()
        .map(|(message, at)| ParseDiagnostic {
            message,
            at: view.to_original(at),
        })
        .collect::<Vec<_>>();
    if !diagnostics.is_empty() {
        return Err(NatDefinitionParseError::Lexical { diagnostics });
    }

    let command_starts = run
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Token(LexedToken {
                kind: TokenKind::Symbol(symbol),
                extent,
            }) if symbol == "def" || symbol == "#eval" || symbol == "#check" => {
                Some(view.to_original(extent.start()).0)
            }
            Event::Trivia(_) | Event::Refused { .. } | Event::Token(_) => None,
        })
        .collect::<Vec<_>>();
    if command_starts.len() <= 1 {
        return Ok(vec![(BytePos(0), source)]);
    }

    let mut commands = Vec::with_capacity(command_starts.len());
    let mut start = 0;
    for next in command_starts.iter().copied().skip(1) {
        commands.push((BytePos(start), &source[start..next]));
        start = next;
    }
    commands.push((BytePos(start), &source[start..]));
    Ok(commands)
}

/// Parse the bounded source facade's module header and partition its commands.
///
/// The supported header is the ordinary Lean spelling `import A.B C`, with one
/// import command per physical line. The first non-import token starts the body;
/// the body remains opaque to this header parser and is partitioned for the
/// bounded command parser, which retains sole authority to accept `def`/`#eval`/`#check`
/// or refuse every other command shape.
/// Comments and blank lines are trivia. Requiring the command to end at its line
/// is deliberate for this first production slice: accepting a broader layout
/// without the complete command parser would guess at module boundaries.
///
/// Import names are returned exactly as structural [`Name`] values. This
/// function neither loads them nor makes them available to elaboration. A caller
/// that cannot prove it has a closed graph must refuse rather than execute the
/// returned commands.
pub fn partition_source_module(
    source: &[u8],
) -> Result<PartitionedSourceModule<'_>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let run = lex_run(view.normalized(), &source_module_token_table());
    let diagnostics = run
        .diagnostics()
        .into_iter()
        .map(|(message, at)| ParseDiagnostic {
            message,
            at: view.to_original(at),
        })
        .collect::<Vec<_>>();
    if !diagnostics.is_empty() {
        return Err(NatDefinitionParseError::Lexical { diagnostics });
    }

    let tokens = run
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Token(token) => Some(token),
            Event::Trivia(_) | Event::Refused { .. } => None,
        })
        .collect::<Vec<_>>();
    let at = |index: usize| {
        tokens.get(index).map_or_else(
            || BytePos(source.len()),
            |token| view.to_original(token.extent.start()),
        )
    };

    let mut imports = Vec::new();
    let mut cursor = 0_usize;
    let definition_start = loop {
        let Some(token) = tokens.get(cursor) else {
            break None;
        };
        match &token.kind {
            TokenKind::Symbol(symbol) if symbol == "import" => {
                let import_line = view.normalized().line_of(token.extent.start());
                cursor += 1;
                let first_module = imports.len();
                while let Some(module) = tokens.get(cursor) {
                    if view.normalized().line_of(module.extent.start()) != import_line {
                        break;
                    }
                    match &module.kind {
                        TokenKind::Ident(name) => imports.push(name.clone()),
                        TokenKind::Symbol(_) | TokenKind::Literal(_) => {
                            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                                at: at(cursor),
                                expected: NatDefinitionExpectation::EndOfImportCommand,
                            });
                        }
                    }
                    cursor += 1;
                }
                if imports.len() == first_module {
                    return Err(NatDefinitionParseError::OutsideSeedGrammar {
                        at: at(cursor),
                        expected: NatDefinitionExpectation::ImportedModule,
                    });
                }
            }
            TokenKind::Ident(_) | TokenKind::Literal(_) | TokenKind::Symbol(_) => {
                break Some(view.to_original(token.extent.start()).0);
            }
        }
    };

    let (body_start, mut commands) = if let Some(body_start) = definition_start {
        let commands = partition_definition_commands(&source[body_start..])
            .map_err(|error| error.with_original_offset(BytePos(body_start)))?;
        (body_start, commands)
    } else {
        // Reaching EOF after imports/trivia is a valid header-only module, not
        // one empty command for the command parser to reject.
        (source.len(), Vec::new())
    };
    for (offset, _) in &mut commands {
        offset.0 = offset.0.saturating_add(body_start);
    }
    Ok(PartitionedSourceModule { imports, commands })
}

/// Partition a Nat-only source file without changing the original parser's
/// acceptance authority.
pub fn partition_nat_definition_commands(
    source: &[u8],
) -> Result<Vec<(BytePos, &[u8])>, NatDefinitionParseError> {
    partition_definition_commands(source)
}

#[cfg(test)]
mod nat_definition_tests {
    use super::*;

    fn definition_value(parsed: &ParsedDefinition) -> &Syntax {
        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node { args: value, .. } = &definition[3] else {
            panic!("the definition value must use declValSimple");
        };
        &value[1]
    }

    fn operator_args<'a>(syntax: &'a Syntax, expected: &str) -> &'a [Syntax] {
        let Syntax::Node { kind, args, .. } = syntax else {
            panic!("expected bounded operator node {expected}");
        };
        assert_eq!(kind, &Name::str(Name::anonymous(), expected));
        args
    }

    #[test]
    fn command_slice_builds_the_canonical_tree_and_retains_both_source_views() {
        let source = b"def answer := 18446744073709551616\r\n";
        let parsed = parse_nat_definition(source).expect("the seed command parses");

        assert_eq!(
            parsed
                .syntax()
                .kind()
                .map(Name::to_display_string)
                .as_deref(),
            Some("Lean.Parser.Command.declaration")
        );
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(b"def answer := 18446744073709551616\n".as_slice())
        );
        assert_eq!(parsed.reconstruct_original(), source);
        assert_eq!(parsed.source_view().removed_count(), 1);
    }

    #[test]
    fn file_partition_uses_real_def_tokens_and_preserves_original_bytes() {
        let source =
            b"-- def hidden\r\ndef first := 1\r\n/- def alsoHidden -/\r\ndef second := first";
        let commands = partition_nat_definition_commands(source)
            .expect("comments and CRLFs are valid in the bounded source file");

        assert_eq!(commands.len(), 2);
        assert_eq!(commands[0].0, BytePos(0));
        assert!(commands[0].1.ends_with(b"/- def alsoHidden -/\r\n"));
        assert_eq!(commands[1].0, BytePos(53));
        assert_eq!(commands[1].1, b"def second := first");
        assert_eq!(
            commands
                .iter()
                .flat_map(|(_, command)| command.iter().copied())
                .collect::<Vec<_>>(),
            source
        );
        for (_, command) in commands {
            parse_nat_definition(command).expect("each partition is one accepted command");
        }
    }

    #[test]
    fn bounded_evaluation_builds_the_pinned_command_tree_and_keeps_positions() {
        let source = b"-- leading trivia\r\n#eval let x : Nat := 40; Nat.add x 2\r\n";
        let parsed = parse_source_command(source).expect("the bounded evaluation command parses");
        assert_eq!(parsed.kind(), SourceCommandKind::Evaluation);
        assert_eq!(
            parsed
                .syntax()
                .kind()
                .map(Name::to_display_string)
                .as_deref(),
            Some("Lean.Parser.Command.eval")
        );
        assert_eq!(parsed.reconstruct_original(), source);
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(b"-- leading trivia\n#eval let x : Nat := 40; Nat.add x 2\n".as_slice())
        );

        let refusal = parse_source_command(b"#eval 1 2")
            .expect_err("a literal-headed application remains outside the bounded grammar");
        assert!(matches!(
            refusal,
            NatDefinitionParseError::OutsideSeedGrammar {
                at: BytePos(8),
                expected: NatDefinitionExpectation::EndOfCommand,
            }
        ));
    }

    #[test]
    fn bounded_check_builds_the_pinned_command_tree_and_exposes_only_its_term() {
        let source = b"-- leading trivia\r\n#check Nat.add\r\n";
        let parsed = parse_source_command(source).expect("the bounded check command parses");
        assert_eq!(parsed.kind(), SourceCommandKind::Check);
        assert_eq!(
            parsed
                .syntax()
                .kind()
                .map(Name::to_display_string)
                .as_deref(),
            Some("Lean.Parser.Command.check")
        );
        assert_eq!(parsed.reconstruct_original(), source);
        assert_eq!(
            parsed
                .query_term_normalized()
                .expect("a check command carries a query term")
                .trim_ascii(),
            "Nat.add"
        );

        let refusal = parse_source_command(b"#check 1 2")
            .expect_err("a literal-headed application remains outside the bounded grammar");
        assert!(matches!(
            refusal,
            NatDefinitionParseError::OutsideSeedGrammar {
                at: BytePos(9),
                expected: NatDefinitionExpectation::EndOfCommand,
            }
        ));
    }

    #[test]
    fn command_partition_treats_checks_as_real_boundaries_but_not_comment_text() {
        let source = b"def first := 40\n-- #check hidden\n#check first\n#eval first\n";
        let commands = partition_definition_commands(source)
            .expect("the definition, check, and evaluation file partitions");
        assert_eq!(commands.len(), 3);
        assert!(commands[0].1.ends_with(b"-- #check hidden\n"));
        assert_eq!(
            commands
                .iter()
                .map(|(_, command)| parse_source_command(command).map(|parsed| parsed.kind()))
                .collect::<Result<Vec<_>, _>>()
                .expect("every partition remains a supported command"),
            vec![
                SourceCommandKind::Definition,
                SourceCommandKind::Check,
                SourceCommandKind::Evaluation,
            ]
        );
    }

    #[test]
    fn command_partition_distinguishes_real_evaluations_from_comment_text() {
        let source = b"def first := 40\n-- #eval hidden\n#eval Nat.add first 2\n";
        let commands = partition_definition_commands(source)
            .expect("the mixed bounded command file partitions");

        assert_eq!(commands.len(), 2);
        assert_eq!(commands[0].0, BytePos(0));
        assert!(commands[0].1.ends_with(b"-- #eval hidden\n"));
        assert_eq!(commands[1].1, b"#eval Nat.add first 2\n");
        assert_eq!(
            parse_source_command(commands[0].1)
                .expect("the definition command parses")
                .kind(),
            SourceCommandKind::Definition
        );
        assert_eq!(
            parse_source_command(commands[1].1)
                .expect("the evaluation command parses")
                .kind(),
            SourceCommandKind::Evaluation
        );
    }

    #[test]
    fn source_module_header_retains_structural_imports_and_original_command_offsets() {
        let source = b"-- module header\r\nimport Foundation.Nat Text.Tools\r\n\r\ndef first := 1\r\ndef answer := first";
        let module = partition_source_module(source).expect("the bounded import header parses");

        assert_eq!(
            module.imports,
            vec![
                Name::from_components(["Foundation", "Nat"]),
                Name::from_components(["Text", "Tools"]),
            ]
        );
        assert_eq!(module.commands.len(), 2);
        assert_eq!(module.commands[0].1, b"def first := 1\r\n");
        assert_eq!(module.commands[1].1, b"def answer := first");
        assert_eq!(
            &source[module.commands[0].0.0..module.commands[0].0.0 + module.commands[0].1.len()],
            module.commands[0].1
        );
        assert_eq!(
            &source[module.commands[1].0.0..module.commands[1].0.0 + module.commands[1].1.len()],
            module.commands[1].1
        );
    }

    #[test]
    fn source_module_header_accepts_an_evaluation_as_its_entry_command() {
        let source = b"import Foundation.Nat\n#eval Nat.add base 2\n";
        let module = partition_source_module(source)
            .expect("an imported bounded evaluation is a source-module command");

        assert_eq!(
            module.imports,
            vec![Name::from_components(["Foundation", "Nat"])]
        );
        assert_eq!(module.commands.len(), 1);
        assert_eq!(module.commands[0].1, b"#eval Nat.add base 2\n");
    }

    #[test]
    fn source_module_header_reports_zero_commands_for_an_import_only_module() {
        let module = partition_source_module(
            b"import Foundation.Nat\n\n-- importing a module is itself a valid Lean module\n",
        )
        .expect("an import-only module has a complete bounded header");

        assert_eq!(
            module.imports,
            vec![Name::from_components(["Foundation", "Nat"])]
        );
        assert!(module.commands.is_empty());

        let empty = partition_source_module(b"").expect("an empty module contains no commands");
        assert!(empty.imports.is_empty());
        assert!(empty.commands.is_empty());

        let unsupported = partition_source_module(b"theorem answer : Nat := 42")
            .expect("the header parser leaves an unsupported body to the command parser");
        assert!(unsupported.imports.is_empty());
        assert_eq!(unsupported.commands.len(), 1);
        assert!(matches!(
            parse_source_command(unsupported.commands[0].1),
            Err(NatDefinitionParseError::OutsideSeedGrammar { .. })
        ));
    }

    #[test]
    fn source_module_header_refuses_missing_and_trailing_import_terms() {
        let missing = partition_source_module(b"import\ndef answer := 1")
            .expect_err("an import command must name a module");
        assert!(matches!(
            missing,
            NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::ImportedModule,
                ..
            }
        ));

        let trailing = partition_source_module(b"import Foundation :\ndef answer := 1")
            .expect_err("punctuation cannot be guessed as part of an import");
        assert!(matches!(
            trailing,
            NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::EndOfImportCommand,
                ..
            }
        ));
    }

    #[test]
    fn source_module_header_keeps_late_imports_on_the_refusal_path() {
        let module = partition_source_module(b"def first := 1\nimport Later\ndef answer := first")
            .expect("header parsing stops exactly at the first definition");
        let error = parse_definition(module.commands[0].1)
            .expect_err("a later import remains visible to the definition parser");
        assert!(matches!(
            error,
            NatDefinitionParseError::OutsideSeedGrammar { .. }
                | NatDefinitionParseError::Lexical { .. }
        ));
    }

    #[test]
    fn file_partition_keeps_unsupported_single_commands_on_the_parser_path() {
        let source = b"theorem answer : Nat := 42";
        let commands = partition_nat_definition_commands(source)
            .expect("lexically valid unsupported input still partitions");
        assert_eq!(commands, vec![(BytePos(0), source.as_slice())]);
        assert!(matches!(
            parse_nat_definition(commands[0].1),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::DefinitionKeyword,
                ..
            })
        ));
    }

    #[test]
    fn file_partition_reports_lexical_positions_in_original_crlf_bytes() {
        let source = b"def first := 1\r\ndef second := first\rbroken";
        let error = partition_nat_definition_commands(source)
            .expect_err("an isolated carriage return must remain a lexical refusal");
        let NatDefinitionParseError::Lexical { diagnostics } = error else {
            panic!("the isolated carriage return must be classified lexically");
        };
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].at, BytePos(35));
        assert_eq!(source[diagnostics[0].at.0], b'\r');
    }

    #[test]
    fn partitioned_refusals_rebase_to_the_original_file() {
        let source = b"def first := 1\r\ndef second : String := first";
        let commands = partition_nat_definition_commands(source)
            .expect("the unsupported type remains lexically valid");
        let (start, second) = commands[1];
        let error = parse_nat_definition(second)
            .expect_err("String is outside the bounded Nat grammar")
            .with_original_offset(start);
        assert!(matches!(
            error,
            NatDefinitionParseError::OutsideSeedGrammar {
                at: BytePos(29),
                expected: NatDefinitionExpectation::NaturalType,
            }
        ));
        assert!(source[29..].starts_with(b"String"));
    }

    #[test]
    fn normalized_slice_rebase_accounts_for_crlf_inside_the_later_command() {
        let source = b"def first := 1\r\ndef second :\r\n String := first";
        let original = SourceText::from_utf8(source).expect("fixture is utf-8");
        let view = SourceView::of(&original);
        let start = BytePos(15);
        assert_eq!(view.normalized().as_str().as_bytes()[start.0], b'd');
        let error = parse_nat_definition(b"def second :\n String := first")
            .expect_err("String is outside the bounded Nat grammar")
            .rebase_from_normalized_slice(&view, start);
        assert!(matches!(
            error,
            NatDefinitionParseError::OutsideSeedGrammar {
                at: BytePos(31),
                expected: NatDefinitionExpectation::NaturalType,
            }
        ));
        assert_eq!(source[31], b'S');
        let naive = parse_nat_definition(b"def second :\n String := first")
            .expect_err("same refusal")
            .with_original_offset(view.to_original(start));
        let NatDefinitionParseError::OutsideSeedGrammar { at: naive_at, .. } = naive else {
            panic!("the naive offset path must stay a type-ascription refusal");
        };
        assert_ne!(
            naive_at.0, 31,
            "raw original-start plus view-local must not be mistaken for to_original(start+local)"
        );
    }

    #[test]
    fn command_slice_retains_an_identifier_value_as_the_canonical_leaf() {
        let source = b"def copy := answer";
        let parsed = parse_nat_definition(source).expect("the seed Nat reference parses");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );

        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node { args: value, .. } = &definition[3] else {
            panic!("the definition value must use declValSimple");
        };
        assert!(matches!(
            &value[1],
            Syntax::Ident { val, .. } if val.to_display_string() == "answer"
        ));
    }

    #[test]
    fn command_slice_builds_the_reference_application_shape_without_losing_source() {
        let source = b"def selected := first 17 29";
        let parsed = parse_nat_definition(source).expect("the bounded Nat application parses");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );

        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node { args: value, .. } = &definition[3] else {
            panic!("the definition value must use declValSimple");
        };
        let Syntax::Node {
            kind,
            args: application,
            ..
        } = &value[1]
        else {
            panic!("the source application must be a term node");
        };
        assert_eq!(kind, &parser_kind(&["Term", "app"]));
        assert!(matches!(
            &application[0],
            Syntax::Ident { val, .. } if val.to_display_string() == "first"
        ));
        let Syntax::Node {
            kind,
            args: arguments,
            ..
        } = &application[1]
        else {
            panic!("the application arguments must use the Reference null array shape");
        };
        assert_eq!(kind, &state::null_kind());
        assert_eq!(arguments.len(), 2);
        assert!(arguments.iter().all(|argument| matches!(
            argument,
            Syntax::Node { kind, args, .. }
                if kind == &Name::str(Name::anonymous(), "num") && args.len() == 1
        )));
    }

    #[test]
    fn bounded_infix_terms_match_the_pins_precedence_and_associativity() {
        let parsed = parse_definition(b"def answer := 1 + 1 == 2")
            .expect("bounded equality has the pin's lower precedence");
        let equality = operator_args(definition_value(&parsed), "term_==_");
        operator_args(&equality[0], "term_+_");

        let source = b"def answer := 2 + 3 * 4 ^ 2";
        let parsed = parse_definition(source).expect("the bounded arithmetic notation parses");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );
        let Syntax::Node {
            kind: add_kind,
            args: add,
            ..
        } = definition_value(&parsed)
        else {
            panic!("the outer addition must be a syntax node");
        };
        assert_eq!(add_kind, &Name::str(Name::anonymous(), "term_+_"));
        assert!(matches!(&add[1], Syntax::Atom { val, .. } if val == "+"));
        let Syntax::Node {
            kind: mul_kind,
            args: mul,
            ..
        } = &add[2]
        else {
            panic!("multiplication must bind inside addition");
        };
        assert_eq!(mul_kind, &Name::str(Name::anonymous(), "term_*_"));
        assert!(matches!(
            &mul[2],
            Syntax::Node { kind, .. } if kind == &Name::str(Name::anonymous(), "term_^_")
        ));

        let parsed = parse_definition(b"def answer := 20 - 3 - 2")
            .expect("subtraction notation parses left-associatively");
        let Syntax::Node {
            kind: outer_kind,
            args: outer,
            ..
        } = definition_value(&parsed)
        else {
            panic!("the outer subtraction must be a syntax node");
        };
        assert_eq!(outer_kind, &Name::str(Name::anonymous(), "term_-_"));
        assert!(matches!(
            &outer[0],
            Syntax::Node { kind, .. } if kind == &Name::str(Name::anonymous(), "term_-_")
        ));

        let parsed = parse_definition(b"def answer := 2 ^ 3 ^ 2")
            .expect("power notation parses right-associatively");
        let Syntax::Node {
            kind: outer_kind,
            args: outer,
            ..
        } = definition_value(&parsed)
        else {
            panic!("the outer power must be a syntax node");
        };
        assert_eq!(outer_kind, &Name::str(Name::anonymous(), "term_^_"));
        assert!(matches!(
            &outer[2],
            Syntax::Node { kind, .. } if kind == &Name::str(Name::anonymous(), "term_^_")
        ));

        let parsed = parse_definition(b"def answer := (2 + 3) * 4")
            .expect("parentheses override bounded infix precedence");
        let Syntax::Node { kind, args, .. } = definition_value(&parsed) else {
            panic!("the grouped multiplication must be a syntax node");
        };
        assert_eq!(kind, &Name::str(Name::anonymous(), "term_*_"));
        assert!(matches!(
            &args[0],
            Syntax::Node { kind, args, .. }
                if kind == &parser_kind(&["Term", "paren"])
                    && matches!(&args[1], Syntax::Node { kind, .. }
                        if kind == &Name::str(Name::anonymous(), "term_+_"))
        ));

        let parsed = parse_definition(b"def answer := 1 ||| 2 ^^^ 3 &&& 4 + 5 * 6 <<< 7 ^ 8")
            .expect("every distinct bounded precedence level composes");
        let lor = operator_args(definition_value(&parsed), "term_|||_");
        let xor = operator_args(&lor[2], "term_^^^_");
        let land = operator_args(&xor[2], "term_&&&_");
        let add = operator_args(&land[2], "term_+_");
        let mul = operator_args(&add[2], "term_*_");
        let shift = operator_args(&mul[2], "term_<<<_");
        operator_args(&shift[2], "term_^_");

        let parsed = parse_definition(b"def answer := 1 * 2 / 3 % 4")
            .expect("equal multiplicative precedences compose left-associatively");
        let modulo = operator_args(definition_value(&parsed), "term_%_");
        let divide = operator_args(&modulo[0], "term_/_");
        operator_args(&divide[0], "term_*_");

        let parsed = parse_definition(b"def answer := 1 <<< 2 >>> 3")
            .expect("equal shift precedences compose left-associatively");
        let shift_right = operator_args(definition_value(&parsed), "term_>>>_");
        operator_args(&shift_right[0], "term_<<<_");

        let parsed = parse_definition(b"def message := \"a\" ++ \"b\" ++ \"c\"")
            .expect("String append composes left-associatively");
        let outer_append = operator_args(definition_value(&parsed), "term_++_");
        operator_args(&outer_append[0], "term_++_");
    }

    #[test]
    fn bounded_infix_table_reconstructs_every_admitted_spelling() {
        for expression in [
            "1 == 2",
            "1 ||| 2",
            "1 ^^^ 2",
            "1 &&& 2",
            "1 + 2",
            "1 - 2",
            "1 * 2",
            "1 / 2",
            "1 % 2",
            "1 <<< 2",
            "1 >>> 2",
            "1 ^ 2",
            "1 <= 2",
            "1 < 2",
            "\"franken\" ++ \"lean\"",
        ] {
            let source = format!("def answer := {expression}");
            let parsed = parse_definition(source.as_bytes())
                .unwrap_or_else(|error| panic!("{expression:?} must parse: {error}"));
            assert_eq!(
                parsed.reconstruct_normalized().as_deref(),
                Some(source.as_bytes()),
                "source spelling {expression:?}"
            );
        }
    }

    #[test]
    fn malformed_or_out_of_slice_infix_terms_remain_typed_refusals() {
        for source in [
            b"def answer := + 1".as_slice(),
            b"def answer := 1 +".as_slice(),
            b"def answer := 1 + * 2".as_slice(),
        ] {
            assert!(matches!(
                parse_definition(source),
                Err(NatDefinitionParseError::OutsideSeedGrammar {
                    expected: NatDefinitionExpectation::ScalarValue,
                    ..
                })
            ));
        }
        assert!(matches!(
            parse_nat_definition(b"def answer := 1 ++ 2"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalValue,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer := 1 == 2"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalValue,
                ..
            })
        ));
        assert!(matches!(
            parse_definition(b"def answer := 1 == 2 == 3"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::EndOfCommand,
                ..
            })
        ));
        assert!(matches!(
            parse_definition(b"def answer := 1 == 2 + 3 == 4"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::EndOfCommand,
                ..
            })
        ));
    }

    #[test]
    fn command_slice_builds_the_reference_parenthesized_application_shape() {
        let source = b"def answer := Nat.sub (Nat.mul 9 5) 3";
        let parsed = parse_definition(source).expect("the bounded nested application parses");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );

        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node { args: value, .. } = &definition[3] else {
            panic!("the definition value must use declValSimple");
        };
        let Syntax::Node {
            kind,
            args: application,
            ..
        } = &value[1]
        else {
            panic!("the outer application must be a term node");
        };
        assert_eq!(kind, &parser_kind(&["Term", "app"]));
        let Syntax::Node {
            args: arguments, ..
        } = &application[1]
        else {
            panic!("the outer application must carry its arguments");
        };
        let Syntax::Node {
            kind: paren_kind,
            args: parenthesized,
            ..
        } = &arguments[0]
        else {
            panic!("the nested application must retain its parentheses");
        };
        assert_eq!(paren_kind, &parser_kind(&["Term", "paren"]));
        assert!(matches!(
            &parenthesized[..],
            [Syntax::Node { kind, args, .. }, Syntax::Node { kind: inner_kind, .. }, Syntax::Atom { val, .. }]
                if kind == &parser_kind(&["Term", "hygienicLParen"])
                    && args.len() == 2
                    && inner_kind == &parser_kind(&["Term", "app"])
                    && val == ")"
        ));
    }

    #[test]
    fn parenthesized_terms_keep_malformed_delimiters_and_nat_strings_typed() {
        assert!(matches!(
            parse_definition(b"def answer := Nat.add (40 2"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::ClosingParenthesis,
                ..
            })
        ));
        assert!(matches!(
            parse_definition(b"def answer := Nat.add () 2"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::ScalarValue,
                ..
            })
        ));
        assert!(matches!(
            parse_definition(b"def answer := Nat.add 40 2)"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::EndOfCommand,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer := identity (\"not Nat\")"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalValue,
                ..
            })
        ));
    }

    #[test]
    fn deeply_parenthesized_term_parses_without_host_stack_recursion() {
        const DEPTH: usize = 20_000;
        let mut source = b"def answer := ".to_vec();
        source.extend(std::iter::repeat_n(b'(', DEPTH));
        source.extend_from_slice(b"42");
        source.extend(std::iter::repeat_n(b')', DEPTH));
        let parsed =
            parse_nat_definition(&source).expect("parenthesis handling uses explicit work stacks");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );
    }

    #[test]
    fn long_left_associative_infix_chain_parses_without_host_stack_recursion() {
        const TERMS: usize = 10_000;
        let mut source = b"def answer := 1".to_vec();
        for _ in 1..TERMS {
            source.extend_from_slice(b" + 1");
        }
        let parsed = parse_nat_definition(&source)
            .expect("bounded infix parsing uses explicit operand and operator stacks");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );
    }

    #[test]
    fn command_slice_builds_the_reference_explicit_nat_binder_shape() {
        let source = b"def first (x y : Nat) : Nat := x";
        let parsed =
            parse_nat_definition(source).expect("grouped Nat parameters and explicit result parse");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );

        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node {
            kind,
            args: signature,
            ..
        } = &definition[2]
        else {
            panic!("the definition must carry an optional signature node");
        };
        assert_eq!(kind, &parser_kind(&["Command", "optDeclSig"]));
        let Syntax::Node {
            kind,
            args: binders,
            ..
        } = &signature[0]
        else {
            panic!("the signature binders must use the Reference null array shape");
        };
        assert_eq!(kind, &state::null_kind());
        let [Syntax::Node { kind, args, .. }] = &binders[..] else {
            panic!("the grouped parameters must share one explicit binder node");
        };
        assert_eq!(kind, &parser_kind(&["Term", "explicitBinder"]));
        assert_eq!(args.len(), 5);
        assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "("));
        assert!(matches!(
            &args[1],
            Syntax::Node { kind, args, .. }
                if kind == &state::null_kind()
                    && matches!(&args[..],
                        [Syntax::Ident { val: x, .. }, Syntax::Ident { val: y, .. }]
                        if x.to_display_string() == "x" && y.to_display_string() == "y")
        ));
        assert!(matches!(
            &args[2],
            Syntax::Node { kind, args, .. }
                if kind == &state::null_kind()
                    && matches!(&args[..],
                        [Syntax::Atom { val: colon, .. }, Syntax::Ident { val: ty, .. }]
                        if colon == ":" && ty.to_display_string() == "Nat")
        ));
        assert!(matches!(
            &args[3],
            Syntax::Node { kind, args, .. }
                if kind == &state::null_kind() && args.is_empty()
        ));
        assert!(matches!(&args[4], Syntax::Atom { val, .. } if val == ")"));

        assert!(matches!(
            &signature[1],
            Syntax::Node { kind, args, .. }
                if kind == &state::null_kind()
                    && matches!(&args[..],
                        [Syntax::Node { kind, args, .. }]
                        if kind == &parser_kind(&["Term", "typeSpec"])
                            && matches!(&args[..],
                                [Syntax::Atom { val: colon, .. }, Syntax::Ident { val: ty, .. }]
                                if colon == ":" && ty.to_display_string() == "Nat"))
        ));
    }

    #[test]
    fn command_slice_builds_the_pinned_let_shape_without_losing_source() {
        let source = b"def answer : Nat := let x := 41; x";
        let parsed = parse_nat_definition(source).expect("the bounded Nat let grammar parses");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );

        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node { args: value, .. } = &definition[3] else {
            panic!("the definition value must use declValSimple");
        };
        let Syntax::Node {
            kind,
            args: let_parts,
            ..
        } = &value[1]
        else {
            panic!("the source let must be a term node");
        };
        assert_eq!(kind, &parser_kind(&["Term", "let"]));
        assert_eq!(let_parts.len(), 5);
        assert!(matches!(&let_parts[0], Syntax::Atom { val, .. } if val == "let"));
        assert!(matches!(
            &let_parts[1],
            Syntax::Node { kind, args, .. }
                if kind == &parser_kind(&["Term", "letConfig"])
                    && matches!(&args[..], [Syntax::Node { kind, args, .. }]
                        if kind == &state::null_kind() && args.is_empty())
        ));
        let Syntax::Node {
            kind,
            args: let_declarations,
            ..
        } = &let_parts[2]
        else {
            panic!("the let declaration must use its Reference wrapper");
        };
        assert_eq!(kind, &parser_kind(&["Term", "letDecl"]));
        let [
            Syntax::Node {
                kind,
                args: local_declaration,
                ..
            },
        ] = &let_declarations[..]
        else {
            panic!("the let must contain one identifier declaration");
        };
        assert_eq!(kind, &parser_kind(&["Term", "letIdDecl"]));
        assert_eq!(local_declaration.len(), 5);
        assert!(matches!(
            &local_declaration[0],
            Syntax::Node { kind, args, .. }
                if kind == &parser_kind(&["Term", "letId"])
                    && matches!(&args[..], [Syntax::Ident { val, .. }]
                        if val.to_display_string() == "x")
        ));
        assert!(matches!(&local_declaration[3], Syntax::Atom { val, .. } if val == ":="));
        assert!(matches!(
            &local_declaration[4],
            Syntax::Node { kind, args, .. }
                if kind == &Name::str(Name::anonymous(), "num") && args.len() == 1
        ));
        assert!(matches!(&let_parts[3], Syntax::Atom { val, .. } if val == ";"));
        assert!(matches!(
            &let_parts[4],
            Syntax::Ident { val, .. } if val.to_display_string() == "x"
        ));
    }

    #[test]
    fn command_slice_preserves_the_pinned_explicit_let_type_shape() {
        let source = b"def message := let value : String := \"typed\"; value";
        let parsed = parse_definition(source).expect("an exact String let type is in the grammar");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );
        assert_eq!(parsed.reconstruct_original(), source);

        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node { args: value, .. } = &definition[3] else {
            panic!("the definition value must use declValSimple");
        };
        let Syntax::Node {
            args: let_parts, ..
        } = &value[1]
        else {
            panic!("the source let must be a term node");
        };
        let Syntax::Node {
            args: let_declarations,
            ..
        } = &let_parts[2]
        else {
            panic!("the let declaration must use its Reference wrapper");
        };
        let [
            Syntax::Node {
                args: local_declaration,
                ..
            },
        ] = &let_declarations[..]
        else {
            panic!("the let must contain one identifier declaration");
        };
        assert!(matches!(
            &local_declaration[2],
            Syntax::Node { kind, args, .. }
                if kind == &state::null_kind()
                    && matches!(&args[..],
                        [Syntax::Node { kind, args, .. }]
                        if kind == &parser_kind(&["Term", "typeSpec"])
                            && matches!(&args[..],
                                [Syntax::Atom { val: colon, .. }, Syntax::Ident { val: ty, .. }]
                                if colon == ":" && ty.to_display_string() == "String"))
        ));

        assert!(matches!(
            parse_definition(b"def bad := let value : Array := 1; value"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::ScalarType,
                ..
            })
        ));
        let bool_source = b"def answer : Bool := Nat.beq 42 42";
        let bool_definition =
            parse_definition(bool_source).expect("the bounded source grammar admits Bool types");
        assert_eq!(
            bool_definition.reconstruct_normalized().as_deref(),
            Some(bool_source.as_slice())
        );
        assert!(matches!(
            parse_nat_definition(b"def bad := let value : String := 1; value"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalType,
                ..
            })
        ));
    }

    #[test]
    fn command_slice_nests_a_let_chain_without_losing_source() {
        let source = b"def selected := let x := 17; let y := x; first y 29";
        let parsed = parse_nat_definition(source).expect("the bounded Nat let chain parses");
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(source.as_slice())
        );
        assert_eq!(parsed.reconstruct_original(), source);

        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("the command root must be a node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &args[1]
        else {
            panic!("the declaration payload must be a definition node");
        };
        let Syntax::Node { args: value, .. } = &definition[3] else {
            panic!("the definition value must use declValSimple");
        };
        let Syntax::Node {
            kind: outer_kind,
            args: outer,
            ..
        } = &value[1]
        else {
            panic!("the outer let must be a term node");
        };
        assert_eq!(outer_kind, &parser_kind(&["Term", "let"]));
        let Syntax::Node {
            kind: inner_kind,
            args: inner,
            ..
        } = &outer[4]
        else {
            panic!("the outer let body must be the inner let node");
        };
        assert_eq!(inner_kind, &parser_kind(&["Term", "let"]));
        assert!(matches!(
            &inner[4],
            Syntax::Node { kind, args, .. }
                if kind == &parser_kind(&["Term", "app"])
                    && matches!(&args[0], Syntax::Ident { val, .. }
                        if val.to_display_string() == "first")
        ));
    }

    #[test]
    fn source_and_seed_grammar_refusals_remain_typed() {
        assert!(matches!(
            parse_nat_definition(&[0xff]),
            Err(NatDefinitionParseError::Source(SourceError::NotUtf8 {
                at: BytePos(0)
            }))
        ));
        assert!(matches!(
            parse_nat_definition(b"theorem answer := 42"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::DefinitionKeyword,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer := 42 extra"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::EndOfCommand,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer := identity \"not a Nat\""),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalValue,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer (x : String) := x"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalType,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer : String := 42"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalType,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer (x : Nat := x"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::ClosingParenthesis,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer := let x := 41 x"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::LetSeparator,
                ..
            })
        ));
        assert!(matches!(
            parse_nat_definition(b"def answer := let x := 41; let y := x;"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalValue,
                ..
            })
        ));
        // Inner `;` is not the let separator. Splitting there left `(1` as
        // the value and reported an unclosed paren. The refusal is now the
        // leftover `;` inside the grouped term.
        assert!(matches!(
            parse_nat_definition(b"def answer := let x := (1; 2); x"),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalValue,
                ..
            })
        ));
        assert!(
            parse_nat_definition(b"def answer := let x := (1); x").is_ok(),
            "a grouped atom is still a legal let value"
        );
    }

    #[test]
    fn scalar_definition_door_accepts_string_without_widening_the_nat_door() {
        let source = b"def copy (value : String) : String := value";
        let parsed = parse_definition(source)
            .expect("the bounded scalar grammar accepts an exact String signature");
        assert_eq!(parsed.reconstruct_original(), source);
        assert!(matches!(
            parse_nat_definition(source),
            Err(NatDefinitionParseError::OutsideSeedGrammar {
                expected: NatDefinitionExpectation::NaturalType,
                ..
            })
        ));

        let literal = parse_definition(b"def message : String := \"line\\nheart \\u2665\"")
            .expect("the lexer-approved String literal reaches the canonical source tree");
        assert!(literal.reconstruct_normalized().is_some());
    }
}
