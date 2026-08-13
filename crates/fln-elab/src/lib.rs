//! **fln-elab** — Athanor — the elaborator: the monadic tower, the unifier's
//! approximation ladder, Synod (the instance engine), match compilation, the
//! native tactic framework, the Mirror façade registry, and the deterministic
//! dataflow scheduler (plan §10, §4.3).
//!
//! The full tower is not present yet. Bead `fln-5720` establishes its first
//! end-to-end production seam: one parsed bounded exact `Nat`/`String`/`Bool`
//! definition, explicit first-order function, parenthesized application, or
//! local let chain becomes a real [`Declaration::Defn`] and is handed to
//! Crucible's sole check authority. The original Nat-only door remains strict.
//! This is a subset of the final abstraction, not a substitute for unification,
//! expected-type propagation, transactions, macros, instances, or tactics.
//! Unsupported source is refused by an explicit variant.

#![forbid(unsafe_code)]

pub mod seed;

use fln_bignum::interop::literal_from_bignat;
use fln_bignum::nat::BigNat;
use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};
use fln_parse::{
    NatDefinitionParseError, ParsedDefinition, ParsedNatDefinition, parse_definition,
    parse_nat_definition,
};
use fln_syntax::tree::Syntax;

/// Why the first elaboration subset refused an otherwise parsed tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatDefinitionElabError {
    UnexpectedSyntax { expected: &'static str },
    AnonymousDeclarationName,
    AnonymousReferenceName,
    InvalidNaturalLiteral,
    InvalidStringLiteral,
    TooManyParameters,
}

impl std::fmt::Display for NatDefinitionElabError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedSyntax { expected } => {
                write!(formatter, "unexpected syntax; expected {expected}")
            }
            Self::AnonymousDeclarationName => write!(formatter, "declaration name is anonymous"),
            Self::AnonymousReferenceName => write!(formatter, "reference name is anonymous"),
            Self::InvalidNaturalLiteral => write!(formatter, "natural literal is invalid"),
            Self::InvalidStringLiteral => write!(formatter, "string literal is invalid"),
            Self::TooManyParameters => write!(formatter, "definition has too many parameters"),
        }
    }
}

impl std::error::Error for NatDefinitionElabError {}

/// A source-to-elaboration failure. Kernel rejections and non-answers are not
/// collapsed into this type; they remain in [`NatDefinitionCheck::outcome`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatDefinitionFrontendError {
    Parse(NatDefinitionParseError),
    Elaborate(NatDefinitionElabError),
}

/// Compatibility name for the wider bounded source door.
pub type DefinitionFrontendError = NatDefinitionFrontendError;

impl std::fmt::Display for NatDefinitionFrontendError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Parse(error) => write!(formatter, "parse refused source: {error}"),
            Self::Elaborate(error) => write!(formatter, "elaboration refused source: {error}"),
        }
    }
}

impl std::error::Error for NatDefinitionFrontendError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Parse(error) => Some(error),
            Self::Elaborate(error) => Some(error),
        }
    }
}

impl From<NatDefinitionParseError> for NatDefinitionFrontendError {
    fn from(error: NatDefinitionParseError) -> Self {
        NatDefinitionFrontendError::Parse(error)
    }
}

impl From<NatDefinitionElabError> for NatDefinitionFrontendError {
    fn from(error: NatDefinitionElabError) -> Self {
        NatDefinitionFrontendError::Elaborate(error)
    }
}

/// The complete first frontend seam. `outcome` is Crucible's authoritative
/// answer; this value does not publish the declaration into the environment.
#[derive(Debug, Clone, PartialEq)]
#[must_use = "the kernel outcome must not be discarded"]
pub struct NatDefinitionCheck {
    pub parsed: ParsedNatDefinition,
    pub declaration: Declaration,
    pub outcome: Outcome<Verdict>,
}

/// The wider bounded source seam's parsed tree, declaration, and authoritative
/// kernel answer. Publication remains outside this value.
#[derive(Debug, Clone, PartialEq)]
#[must_use = "the kernel outcome must not be discarded"]
pub struct DefinitionCheck {
    pub parsed: ParsedDefinition,
    pub declaration: Declaration,
    pub outcome: Outcome<Verdict>,
}

fn parser_kind(components: &[&str]) -> Name {
    let mut name = Name::from_components(["Lean", "Parser"]);
    for component in components {
        name = Name::str(name, *component);
    }
    name
}

fn expect_node<'a>(
    syntax: &'a Syntax,
    kind: &Name,
    arity: usize,
    expected: &'static str,
) -> Result<&'a [Syntax], NatDefinitionElabError> {
    let Syntax::Node {
        kind: actual, args, ..
    } = syntax
    else {
        return Err(NatDefinitionElabError::UnexpectedSyntax { expected });
    };
    if actual != kind || args.len() != arity {
        return Err(NatDefinitionElabError::UnexpectedSyntax { expected });
    }
    Ok(args)
}

fn expect_empty_null(
    syntax: &Syntax,
    expected: &'static str,
) -> Result<(), NatDefinitionElabError> {
    expect_node(syntax, &Name::str(Name::anonymous(), "null"), 0, expected).map(|_| ())
}

fn expect_null_args<'a>(
    syntax: &'a Syntax,
    expected: &'static str,
) -> Result<&'a [Syntax], NatDefinitionElabError> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return Err(NatDefinitionElabError::UnexpectedSyntax { expected });
    };
    if kind != &Name::str(Name::anonymous(), "null") {
        return Err(NatDefinitionElabError::UnexpectedSyntax { expected });
    }
    Ok(args)
}

fn expect_atom<'a>(
    syntax: &'a Syntax,
    value: &str,
    expected: &'static str,
) -> Result<&'a str, NatDefinitionElabError> {
    let Syntax::Atom { val, .. } = syntax else {
        return Err(NatDefinitionElabError::UnexpectedSyntax { expected });
    };
    if val != value {
        return Err(NatDefinitionElabError::UnexpectedSyntax { expected });
    }
    Ok(val)
}

fn natural_digit(byte: u8) -> Option<u64> {
    match byte {
        b'0'..=b'9' => Some(u64::from(byte - b'0')),
        b'a'..=b'f' => Some(u64::from(byte - b'a') + 10),
        b'A'..=b'F' => Some(u64::from(byte - b'A') + 10),
        _ => None,
    }
}

fn decode_natural(spelling: &str) -> Result<Literal, NatDefinitionElabError> {
    let (radix, digits) = match spelling.as_bytes() {
        [b'0', b'b' | b'B', digits @ ..] => (2, digits),
        [b'0', b'o' | b'O', digits @ ..] => (8, digits),
        [b'0', b'x' | b'X', digits @ ..] => (16, digits),
        digits => (10, digits),
    };
    if digits.is_empty()
        || digits.last() == Some(&b'_')
        || (radix == 10 && !digits.first().is_some_and(u8::is_ascii_digit))
    {
        return Err(NatDefinitionElabError::InvalidNaturalLiteral);
    }
    let compact = digits
        .iter()
        .copied()
        .filter(|byte| *byte != b'_')
        .collect::<Vec<_>>();
    if compact.is_empty() {
        return Err(NatDefinitionElabError::InvalidNaturalLiteral);
    }

    let value = if radix == 10 {
        let decimal = std::str::from_utf8(&compact)
            .map_err(|_| NatDefinitionElabError::InvalidNaturalLiteral)?;
        BigNat::from_decimal(decimal).ok_or(NatDefinitionElabError::InvalidNaturalLiteral)?
    } else {
        let scale = BigNat::from_u64(radix);
        let mut value = BigNat::zero();
        for byte in compact {
            let digit = natural_digit(byte).ok_or(NatDefinitionElabError::InvalidNaturalLiteral)?;
            if digit >= radix {
                return Err(NatDefinitionElabError::InvalidNaturalLiteral);
            }
            value = value.mul(&scale).add(&BigNat::from_u64(digit));
        }
        value
    };
    Ok(Literal::Nat(literal_from_bignat(&value)))
}

fn decode_hex_scalar(bytes: &[u8]) -> Result<char, NatDefinitionElabError> {
    let mut value = 0_u32;
    for byte in bytes {
        let digit = natural_digit(*byte).ok_or(NatDefinitionElabError::InvalidStringLiteral)?;
        value = value
            .checked_mul(16)
            .and_then(|value| value.checked_add(u32::try_from(digit).ok()?))
            .ok_or(NatDefinitionElabError::InvalidStringLiteral)?;
    }
    char::from_u32(value).ok_or(NatDefinitionElabError::InvalidStringLiteral)
}

fn decode_string(spelling: &str) -> Result<Literal, NatDefinitionElabError> {
    if spelling.starts_with('r') {
        let bytes = spelling.as_bytes();
        let mut opener = 1;
        while bytes.get(opener) == Some(&b'#') {
            opener += 1;
        }
        if bytes.get(opener) != Some(&b'"') {
            return Err(NatDefinitionElabError::InvalidStringLiteral);
        }
        let hashes = opener - 1;
        let suffix = 1_usize
            .checked_add(hashes)
            .ok_or(NatDefinitionElabError::InvalidStringLiteral)?;
        let content_start = opener + 1;
        let content_stop = spelling
            .len()
            .checked_sub(suffix)
            .filter(|stop| *stop >= content_start)
            .ok_or(NatDefinitionElabError::InvalidStringLiteral)?;
        if bytes.get(content_stop) != Some(&b'"')
            || bytes[content_stop + 1..].iter().any(|byte| *byte != b'#')
        {
            return Err(NatDefinitionElabError::InvalidStringLiteral);
        }
        return Ok(Literal::Str(
            spelling[content_start..content_stop].to_owned(),
        ));
    }

    let content = spelling
        .strip_prefix('"')
        .and_then(|spelling| spelling.strip_suffix('"'))
        .ok_or(NatDefinitionElabError::InvalidStringLiteral)?;
    let mut decoded = String::new();
    let mut chars = content.chars();
    while let Some(character) = chars.next() {
        if character != '\\' {
            decoded.push(character);
            continue;
        }
        let escaped = chars
            .next()
            .ok_or(NatDefinitionElabError::InvalidStringLiteral)?;
        match escaped {
            '\\' => decoded.push('\\'),
            '"' => decoded.push('"'),
            '\'' => decoded.push('\''),
            'r' => decoded.push('\r'),
            'n' => decoded.push('\n'),
            't' => decoded.push('\t'),
            'x' => {
                let digits = chars.by_ref().take(2).collect::<String>();
                if digits.len() != 2 {
                    return Err(NatDefinitionElabError::InvalidStringLiteral);
                }
                decoded.push(decode_hex_scalar(digits.as_bytes())?);
            }
            'u' => {
                let digits = chars.by_ref().take(4).collect::<String>();
                if digits.len() != 4 {
                    return Err(NatDefinitionElabError::InvalidStringLiteral);
                }
                decoded.push(decode_hex_scalar(digits.as_bytes())?);
            }
            // Pin `quotedCharCoreFn` (`Basic.lean:668`): a string gap starts
            // only on a newline after `\`. `stringGapFn` then eats pin
            // whitespace (`Char.isWhitespace`: space, tab, CR, LF) and
            // refuses a second newline. Unicode White_Space (NBSP, form
            // feed, …) is content, not gap.
            '\n' => loop {
                match chars.clone().next() {
                    Some('\n') => return Err(NatDefinitionElabError::InvalidStringLiteral),
                    Some(whitespace) if fln_syntax::literal::is_whitespace(whitespace) => {
                        chars.next();
                    }
                    _ => break,
                }
            },
            _ => return Err(NatDefinitionElabError::InvalidStringLiteral),
        }
    }
    Ok(Literal::Str(decoded))
}

fn scalar_type(name: &Name, allow_string: bool) -> Option<Expr> {
    if name == &Name::from_components(["Nat"])
        || (allow_string
            && (name == &Name::from_components(["String"])
                || name == &Name::from_components(["Bool"])))
    {
        Some(Expr::const_(name.clone(), Vec::new()))
    } else {
        None
    }
}

fn optional_scalar_type(
    syntax: &Syntax,
    allow_string: bool,
    optional_expected: &'static str,
    scalar_expected: &'static str,
) -> Result<Option<Expr>, NatDefinitionElabError> {
    let optional = expect_null_args(syntax, optional_expected)?;
    match optional {
        [] => Ok(None),
        [type_spec] => {
            let parts = expect_node(
                type_spec,
                &parser_kind(&["Term", "typeSpec"]),
                2,
                "Lean.Parser.Term.typeSpec",
            )?;
            expect_atom(&parts[0], ":", "explicit type ascription")?;
            let Syntax::Ident { val: type_name, .. } = &parts[1] else {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: scalar_expected,
                });
            };
            Ok(Some(scalar_type(type_name, allow_string).ok_or(
                NatDefinitionElabError::UnexpectedSyntax {
                    expected: scalar_expected,
                },
            )?))
        }
        _ => Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: optional_expected,
        }),
    }
}

/// Elaborate the exact canonical tree produced by
/// [`fln_parse::parse_nat_definition`].
///
/// This first slice has no expected-type input. It constructs only explicit
/// `Nat` binders, natural literals, references, local lets, and the parser's flat
/// first-order application spine, then declares a `Nat` result. The caller's
/// environment must already contain referenced constants; the kernel, not this
/// function, determines whether the function and arguments make the declaration
/// admissible.
pub fn elaborate_nat_definition(syntax: &Syntax) -> Result<Declaration, NatDefinitionElabError> {
    elaborate_definition_with_types(syntax, false, None)
}

/// Same as [`elaborate_nat_definition`], but omitted results may follow
/// already-checked constants in `environment`.
pub fn elaborate_nat_definition_in(
    syntax: &Syntax,
    environment: &Environment,
) -> Result<Declaration, NatDefinitionElabError> {
    elaborate_definition_with_types(syntax, false, Some(environment))
}

/// Elaborate the canonical bounded definition tree over exact `Nat` and
/// `String` types. K1 remains responsible for checking every reference,
/// application, literal type, and declared result before publication.
pub fn elaborate_definition(syntax: &Syntax) -> Result<Declaration, NatDefinitionElabError> {
    elaborate_definition_with_types(syntax, true, None)
}

/// Same as [`elaborate_definition`], consulting `environment` so an omitted
/// result on `def message := copy "hello"` becomes `String` when `copy` is
/// already a checked `String → String`.
pub fn elaborate_definition_in(
    syntax: &Syntax,
    environment: &Environment,
) -> Result<Declaration, NatDefinitionElabError> {
    elaborate_definition_with_types(syntax, true, Some(environment))
}

fn elaborate_definition_with_types(
    syntax: &Syntax,
    allow_string: bool,
    environment: Option<&Environment>,
) -> Result<Declaration, NatDefinitionElabError> {
    let declaration = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "Lean.Parser.Command.declaration",
    )?;
    let modifiers = expect_node(
        &declaration[0],
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "empty declaration modifiers",
    )?;
    for modifier in modifiers {
        expect_empty_null(modifier, "empty declaration modifier")?;
    }

    let definition = expect_node(
        &declaration[1],
        &parser_kind(&["Command", "definition"]),
        5,
        "Lean.Parser.Command.definition",
    )?;
    expect_atom(&definition[0], "def", "definition keyword")?;

    let declaration_id = expect_node(
        &definition[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "Lean.Parser.Command.declId",
    )?;
    let Syntax::Ident {
        val: declaration_name,
        ..
    } = &declaration_id[0]
    else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "declaration identifier",
        });
    };
    if declaration_name.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    expect_empty_null(&declaration_id[1], "absent declaration pre-parser")?;

    let signature = expect_node(
        &definition[2],
        &parser_kind(&["Command", "optDeclSig"]),
        2,
        "bounded Nat declaration signature",
    )?;
    let binders = expect_null_args(&signature[0], "explicit Nat binder array")?;
    let mut parameters = Vec::new();
    for binder in binders {
        let parts = expect_node(
            binder,
            &parser_kind(&["Term", "explicitBinder"]),
            5,
            "Lean.Parser.Term.explicitBinder",
        )?;
        expect_atom(&parts[0], "(", "explicit binder opener")?;
        let names = expect_null_args(&parts[1], "nonempty explicit binder identifiers")?;
        if names.is_empty() {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "nonempty explicit binder identifiers",
            });
        }
        let type_spec = expect_null_args(&parts[2], "explicit Nat binder type")?;
        let [
            colon,
            Syntax::Ident {
                val: parameter_type,
                ..
            },
        ] = type_spec
        else {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "explicit Nat binder type",
            });
        };
        expect_atom(colon, ":", "explicit binder type ascription")?;
        let Some(parameter_type) = scalar_type(parameter_type, allow_string) else {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "supported scalar parameter type",
            });
        };
        expect_empty_null(&parts[3], "absent explicit binder default")?;
        expect_atom(&parts[4], ")", "explicit binder closer")?;
        for name in names {
            let Syntax::Ident { val: parameter, .. } = name else {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "explicit binder identifier",
                });
            };
            if parameter.is_anonymous() {
                return Err(NatDefinitionElabError::AnonymousReferenceName);
            }
            parameters.push((parameter.clone(), parameter_type.clone()));
        }
    }
    let ascribed_result = optional_scalar_type(
        &signature[1],
        allow_string,
        "optional explicit result type",
        "supported scalar result type",
    )?;
    // Lets still need an expected type for un-inferable apps/consts. Nat is
    // the historical default; omitted declaration results are refined after
    // the body elaborates.
    let elaboration_result_type = ascribed_result
        .clone()
        .unwrap_or_else(|| Expr::const_(Name::from_components(["Nat"]), Vec::new()));

    let value = expect_node(
        &definition[3],
        &parser_kind(&["Command", "declValSimple"]),
        4,
        "Lean.Parser.Command.declValSimple",
    )?;
    expect_atom(&value[0], ":=", "definition assignment")?;
    let mut expression = elaborate_term(
        &value[1],
        &parameters,
        &elaboration_result_type,
        allow_string,
        environment,
    )?;

    let termination = expect_node(
        &value[2],
        &parser_kind(&["Termination", "suffix"]),
        2,
        "empty termination suffix",
    )?;
    for part in termination {
        expect_empty_null(part, "empty termination component")?;
    }
    expect_empty_null(&value[3], "absent declaration where clause")?;
    expect_empty_null(&definition[4], "absent definition clauses")?;

    let name = declaration_name.clone();
    let mut declaration_type = ascribed_result.unwrap_or_else(|| {
        infer_expr_type(&expression, &parameters, environment)
            .filter(|ty| acceptable_inferred(ty, allow_string))
            .unwrap_or_else(nat_const)
    });
    expression = eta_expand_nondependent(expression, &declaration_type)?;
    for (parameter, parameter_type) in parameters.iter().rev() {
        declaration_type = Expr::forall_e(
            parameter.clone(),
            parameter_type.clone(),
            declaration_type,
            BinderInfo::Default,
        );
        expression = Expr::lam(
            parameter.clone(),
            parameter_type.clone(),
            expression,
            BinderInfo::Default,
        );
    }
    Ok(Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_: declaration_type,
        },
        value: expression,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![name],
    }))
}

fn elaborate_nat_reference(
    name: &Name,
    locals: &[(Name, Expr)],
) -> Result<Expr, NatDefinitionElabError> {
    if name.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousReferenceName);
    }
    if let Some(index) = locals
        .iter()
        .rev()
        .position(|(parameter, _)| parameter == name)
    {
        let index = u32::try_from(index).map_err(|_| NatDefinitionElabError::TooManyParameters)?;
        return Expr::bvar(index).map_err(|_| NatDefinitionElabError::TooManyParameters);
    }
    Ok(Expr::const_(name.clone(), Vec::new()))
}

fn elaborate_atom(
    syntax: &Syntax,
    locals: &[(Name, Expr)],
    allow_string: bool,
) -> Result<Expr, NatDefinitionElabError> {
    Ok(match syntax {
        Syntax::Node { kind, args, .. }
            if kind == &Name::str(Name::anonymous(), "num") && args.len() == 1 =>
        {
            let Syntax::Atom { val: spelling, .. } = &args[0] else {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "natural numeral atom",
                });
            };
            Expr::lit(decode_natural(spelling)?)
        }
        Syntax::Node { kind, args, .. }
            if allow_string && kind == &Name::str(Name::anonymous(), "str") && args.len() == 1 =>
        {
            let Syntax::Atom { val: spelling, .. } = &args[0] else {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "string literal atom",
                });
            };
            Expr::lit(decode_string(spelling)?)
        }
        Syntax::Ident { val: name, .. } => elaborate_nat_reference(name, locals)?,
        _ => {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "supported scalar literal or constant identifier",
            });
        }
    })
}

fn parenthesized_inner(syntax: &Syntax) -> Result<Option<&Syntax>, NatDefinitionElabError> {
    let Syntax::Node { kind, .. } = syntax else {
        return Ok(None);
    };
    if kind != &parser_kind(&["Term", "paren"]) {
        return Ok(None);
    }
    let parts = expect_node(
        syntax,
        &parser_kind(&["Term", "paren"]),
        3,
        "Lean.Parser.Term.paren",
    )?;
    let opener = expect_node(
        &parts[0],
        &parser_kind(&["Term", "hygienicLParen"]),
        2,
        "Lean.Parser.Term.hygienicLParen",
    )?;
    expect_atom(&opener[0], "(", "parenthesized term opener")?;
    let hygiene = expect_node(
        &opener[1],
        &Name::str(Name::anonymous(), "hygieneInfo"),
        1,
        "parenthesized term hygiene information",
    )?;
    let [Syntax::Ident { val, .. }] = hygiene else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "anonymous parenthesis hygiene identifier",
        });
    };
    if !val.is_anonymous() {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "anonymous parenthesis hygiene identifier",
        });
    }
    expect_atom(&parts[2], ")", "parenthesized term closer")?;
    Ok(Some(&parts[1]))
}

fn elaborate_nonlet_term(
    syntax: &Syntax,
    locals: &[(Name, Expr)],
    allow_string: bool,
) -> Result<Expr, NatDefinitionElabError> {
    enum Task<'a> {
        Visit(&'a Syntax),
        Apply(usize),
    }

    let mut tasks = vec![Task::Visit(syntax)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(term) => {
                if let Some(inner) = parenthesized_inner(term)? {
                    tasks.push(Task::Visit(inner));
                    continue;
                }
                let Syntax::Node { kind, .. } = term else {
                    values.push(elaborate_atom(term, locals, allow_string)?);
                    continue;
                };
                if kind != &parser_kind(&["Term", "app"]) {
                    values.push(elaborate_atom(term, locals, allow_string)?);
                    continue;
                }
                let parts = expect_node(
                    term,
                    &parser_kind(&["Term", "app"]),
                    2,
                    "Lean.Parser.Term.app",
                )?;
                let Syntax::Ident { val: function, .. } = &parts[0] else {
                    return Err(NatDefinitionElabError::UnexpectedSyntax {
                        expected: "application function identifier",
                    });
                };
                if function.is_anonymous() {
                    return Err(NatDefinitionElabError::AnonymousReferenceName);
                }
                let arguments = expect_null_args(&parts[1], "nonempty application argument array")?;
                if arguments.is_empty() {
                    return Err(NatDefinitionElabError::UnexpectedSyntax {
                        expected: "nonempty application argument array",
                    });
                }
                tasks.push(Task::Apply(arguments.len()));
                for argument in arguments.iter().rev() {
                    tasks.push(Task::Visit(argument));
                }
                tasks.push(Task::Visit(&parts[0]));
            }
            Task::Apply(argument_count) => {
                let Some(start) = values.len().checked_sub(argument_count.saturating_add(1)) else {
                    return Err(NatDefinitionElabError::UnexpectedSyntax {
                        expected: "complete application operands",
                    });
                };
                let operands = values.split_off(start);
                let mut operands = operands.into_iter();
                let mut expression =
                    operands
                        .next()
                        .ok_or(NatDefinitionElabError::UnexpectedSyntax {
                            expected: "application function",
                        })?;
                for argument in operands {
                    expression = Expr::app(expression, argument);
                }
                values.push(expression);
            }
        }
    }
    let [expression] = values.as_slice() else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "one complete scalar term",
        });
    };
    Ok(expression.clone())
}

fn elaborate_term(
    syntax: &Syntax,
    locals: &[(Name, Expr)],
    result_type: &Expr,
    allow_string: bool,
    environment: Option<&Environment>,
) -> Result<Expr, NatDefinitionElabError> {
    if let Syntax::Node { kind, args, .. } = syntax
        && kind == &parser_kind(&["Term", "let"])
    {
        return elaborate_let(args, locals, result_type, allow_string, environment);
    }
    elaborate_nonlet_term(syntax, locals, allow_string)
}

fn nat_const() -> Expr {
    Expr::const_(Name::from_components(["Nat"]), Vec::new())
}

fn string_const() -> Expr {
    Expr::const_(Name::from_components(["String"]), Vec::new())
}

fn environment_constant_type(name: &Name, environment: Option<&Environment>) -> Option<Expr> {
    let info = environment?.find(name)?;
    let val = info.constant_val();
    if !val.level_params.is_empty() {
        return None;
    }
    Some(val.type_.clone())
}

fn acceptable_inferred(ty: &Expr, allow_string: bool) -> bool {
    match ty.node() {
        ExprNode::Const { name, levels } if levels.is_empty() => {
            name == &Name::from_components(["Nat"])
                || (allow_string
                    && (name == &Name::from_components(["String"])
                        || name == &Name::from_components(["Bool"])))
        }
        ExprNode::ForallE { body, .. } if !body.has_loose_bvars() => {
            acceptable_inferred(body, allow_string)
        }
        _ => false,
    }
}

/// The type a `let` binder — or an omitted declaration result — should carry.
/// Literals and already-bound names have an exact scalar type. Environment
/// constants and saturated first-order applications consult the snapshot when
/// one is provided; dependent remaining types stay with the declaration result.
fn infer_expr_type(
    value: &Expr,
    locals: &[(Name, Expr)],
    environment: Option<&Environment>,
) -> Option<Expr> {
    match value.node() {
        ExprNode::Lit {
            literal: Literal::Nat(_),
        } => Some(nat_const()),
        ExprNode::Lit {
            literal: Literal::Str(_),
        } => Some(string_const()),
        ExprNode::BVar { idx } => locals
            .iter()
            .rev()
            .nth(usize::try_from(*idx).ok()?)
            .map(|(_, ty)| ty.clone()),
        ExprNode::LetE { type_, body, .. } => {
            let mut extended = locals.to_vec();
            extended.push((Name::anonymous(), type_.clone()));
            infer_expr_type(body, &extended, environment)
        }
        ExprNode::Const { name, levels } if levels.is_empty() => {
            environment_constant_type(name, environment)
        }
        ExprNode::App { .. } => {
            let mut arity = 0_usize;
            let mut head = value;
            while let ExprNode::App { f, .. } = head.node() {
                arity = arity.checked_add(1)?;
                head = f;
            }
            let mut ty = match head.node() {
                ExprNode::Const { name, levels } if levels.is_empty() => {
                    environment_constant_type(name, environment)?
                }
                ExprNode::BVar { idx } => locals
                    .iter()
                    .rev()
                    .nth(usize::try_from(*idx).ok()?)?
                    .1
                    .clone(),
                _ => return None,
            };
            for _ in 0..arity {
                let ExprNode::ForallE { body, .. } = ty.node() else {
                    return None;
                };
                if body.has_loose_bvars() {
                    return None;
                }
                ty = body.clone();
            }
            Some(ty)
        }
        _ => None,
    }
}

/// Turn `alias := copy` into `fun x => copy x` when the inferred type is a
/// non-dependent first-order telescope. The source door has no expected-type
/// input, so this is the only way a function alias becomes a real lambda the
/// compiler catalog already knows how to publish and apply.
fn eta_expand_nondependent(value: Expr, inferred: &Expr) -> Result<Expr, NatDefinitionElabError> {
    if matches!(value.node(), ExprNode::Lam { .. }) {
        return Ok(value);
    }
    let mut binders = Vec::new();
    let mut remaining = inferred;
    while let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = remaining.node()
    {
        if body.has_loose_bvars() {
            return Ok(value);
        }
        binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
        remaining = body;
    }
    if binders.is_empty() {
        return Ok(value);
    }

    let extra = binders.len();
    let extra_u32 = u32::try_from(extra).map_err(|_| NatDefinitionElabError::TooManyParameters)?;
    let mut eta = value
        .lift_loose(0, extra_u32)
        .map_err(|_| NatDefinitionElabError::TooManyParameters)?;
    for index in (0..extra).rev() {
        let index = u32::try_from(index).map_err(|_| NatDefinitionElabError::TooManyParameters)?;
        let argument = Expr::bvar(index).map_err(|_| NatDefinitionElabError::TooManyParameters)?;
        eta = Expr::app(eta, argument);
    }
    for (binder_name, binder_type, binder_info) in binders.into_iter().rev() {
        eta = Expr::lam(binder_name, binder_type, eta, binder_info);
    }
    Ok(eta)
}

fn elaborate_let(
    parts: &[Syntax],
    locals: &[(Name, Expr)],
    result_type: &Expr,
    allow_string: bool,
    environment: Option<&Environment>,
) -> Result<Expr, NatDefinitionElabError> {
    let [keyword, config, declaration, separator, body] = parts else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "Lean.Parser.Term.let",
        });
    };
    expect_atom(keyword, "let", "let keyword")?;
    let config = expect_node(
        config,
        &parser_kind(&["Term", "letConfig"]),
        1,
        "empty Lean.Parser.Term.letConfig",
    )?;
    expect_empty_null(&config[0], "empty let configuration")?;
    let declaration = expect_node(
        declaration,
        &parser_kind(&["Term", "letDecl"]),
        1,
        "Lean.Parser.Term.letDecl",
    )?;
    let declaration = expect_node(
        &declaration[0],
        &parser_kind(&["Term", "letIdDecl"]),
        5,
        "Lean.Parser.Term.letIdDecl",
    )?;
    let local_id = expect_node(
        &declaration[0],
        &parser_kind(&["Term", "letId"]),
        1,
        "Lean.Parser.Term.letId",
    )?;
    let Syntax::Ident {
        val: local_name, ..
    } = &local_id[0]
    else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "let identifier",
        });
    };
    if local_name.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousReferenceName);
    }
    expect_empty_null(&declaration[1], "empty let binder array")?;
    let ascribed_type = optional_scalar_type(
        &declaration[2],
        allow_string,
        "optional explicit let type",
        "supported scalar let type",
    )?;
    expect_atom(&declaration[3], ":=", "let assignment")?;
    let value = elaborate_term(
        &declaration[4],
        locals,
        result_type,
        allow_string,
        environment,
    )?;
    expect_atom(separator, ";", "let body separator")?;

    let binder_type = ascribed_type.unwrap_or_else(|| {
        infer_expr_type(&value, locals, environment)
            .filter(|ty| acceptable_inferred(ty, allow_string))
            .unwrap_or_else(|| result_type.clone())
    });
    let mut body_locals = locals.to_vec();
    body_locals.push((local_name.clone(), binder_type.clone()));
    let body = elaborate_term(body, &body_locals, result_type, allow_string, environment)?;
    Ok(Expr::let_e(
        local_name.clone(),
        binder_type,
        value,
        body,
        false,
    ))
}

/// Parse, elaborate, and kernel-check one bounded Nat-valued definition.
///
/// The kernel outcome crosses this boundary unchanged, including
/// `Inconclusive` and `InternalFault` (FL-INV-07). No environment mutation is
/// performed; publication remains a separate checked-capability operation.
///
/// This seed does not yet have Athanor's final `ElabBudget`: source copying,
/// token collection, and bignum conversion remain unmetered. It is
/// therefore an executable bounded-language slice, not a resource-authoritative
/// elaboration entry point.
pub fn check_nat_definition_source(
    source: &[u8],
    environment: &Environment,
    budget: Budget,
) -> Result<NatDefinitionCheck, NatDefinitionFrontendError> {
    let parsed = parse_nat_definition(source)?;
    let declaration = elaborate_nat_definition_in(parsed.syntax(), environment)?;
    let outcome = check(environment, &declaration, budget);
    Ok(NatDefinitionCheck {
        parsed,
        declaration,
        outcome,
    })
}

/// Parse, elaborate, and kernel-check one bounded Nat/String/Bool definition.
///
/// Like the Nat-only door, this returns Crucible's typed outcome without
/// publishing anything into the supplied immutable environment.
pub fn check_definition_source(
    source: &[u8],
    environment: &Environment,
    budget: Budget,
) -> Result<DefinitionCheck, DefinitionFrontendError> {
    let parsed = parse_definition(source)?;
    let declaration = elaborate_definition_in(parsed.syntax(), environment)?;
    let outcome = check(environment, &declaration, budget);
    Ok(DefinitionCheck {
        parsed,
        declaration,
        outcome,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::{ExprNode, NatLit};
    use fln_core::level::Level;
    use fln_env::constants::AxiomVal;
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};
    use fln_kernel::verdict::RejectClass;
    use seed::bootstrap_nat_environment;

    fn nat_environment() -> Environment {
        bootstrap_nat_environment(Budget::DEFAULT).expect("the small Nat fixture must publish")
    }

    fn publish_test_axiom(environment: &Environment, name: &str, type_: Expr) -> Environment {
        let declaration = Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: Name::from_components([name]),
                level_params: Vec::new(),
                type_,
            },
            is_unsafe: false,
        });
        let Outcome::Complete(admitted) = admit(environment, declaration, Budget::DEFAULT) else {
            panic!("the bounded test axiom must reach a kernel verdict");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("the kernel-accepted test axiom must pass the empty council");
        };
        let Outcome::Complete(Published::Committed(DeclarationCommitted::Published(publication))) =
            checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            )
        else {
            panic!("the checked test axiom must publish exactly once");
        };
        publication.environment
    }

    #[test]
    fn source_text_becomes_an_arbitrary_precision_kernel_accepted_constant() {
        let source = b"def answer := 18446744073709551616";
        let result = check_nat_definition_source(source, &nat_environment(), Budget::DEFAULT)
            .expect("the bounded frontend accepts its seed grammar");

        assert!(matches!(
            result.outcome,
            Outcome::Complete(Verdict::Accepted { .. })
        ));
        let Declaration::Defn(definition) = &result.declaration else {
            panic!("the seed command must elaborate to a definition");
        };
        assert_eq!(definition.base.name.to_display_string(), "answer");
        assert_eq!(
            definition.base.type_,
            Expr::const_(Name::str(Name::anonymous(), "Nat"), Vec::new())
        );
        assert!(matches!(
            definition.value.node(),
            ExprNode::Lit {
                literal: Literal::Nat(value)
            } if value == &NatLit::from_limbs_le(vec![0, 1])
        ));
        assert_eq!(result.parsed.reconstruct_original(), source);
    }

    #[test]
    fn identifier_value_becomes_a_nat_typed_constant_reference() {
        let parsed = parse_nat_definition(b"def copy := answer")
            .expect("the bounded Nat reference grammar parses");
        let declaration = elaborate_nat_definition(parsed.syntax())
            .expect("the canonical identifier leaf elaborates");
        let Declaration::Defn(definition) = declaration else {
            panic!("the seed command must elaborate to a definition");
        };
        assert_eq!(definition.base.name.to_display_string(), "copy");
        assert_eq!(
            definition.base.type_,
            Expr::const_(Name::from_components(["Nat"]), Vec::new())
        );
        assert!(matches!(
            definition.value.node(),
            ExprNode::Const { name, levels }
                if name.to_display_string() == "answer" && levels.is_empty()
        ));
    }

    #[test]
    fn first_order_application_preserves_function_and_argument_order() {
        let parsed = parse_nat_definition(b"def selected := first 17 29")
            .expect("the bounded Nat application grammar parses");
        let declaration = elaborate_nat_definition(parsed.syntax())
            .expect("the canonical application node elaborates");
        let Declaration::Defn(definition) = declaration else {
            panic!("the seed command must elaborate to a definition");
        };
        let expected = Expr::app(
            Expr::app(
                Expr::const_(Name::from_components(["first"]), Vec::new()),
                Expr::lit(Literal::Nat(NatLit::from_u64(17))),
            ),
            Expr::lit(Literal::Nat(NatLit::from_u64(29))),
        );
        assert_eq!(definition.value, expected);
    }

    #[test]
    fn explicit_nat_parameters_become_dependent_type_and_lambda_binders() {
        let result = check_nat_definition_source(
            b"def first (x y : Nat) : Nat := x",
            &nat_environment(),
            Budget::DEFAULT,
        )
        .expect("the bounded explicit Nat function grammar elaborates");
        assert!(matches!(
            result.outcome,
            Outcome::Complete(Verdict::Accepted { .. })
        ));
        let Declaration::Defn(definition) = result.declaration else {
            panic!("the seed command must elaborate to a definition");
        };
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let expected_type = Expr::forall_e(
            Name::from_components(["x"]),
            nat.clone(),
            Expr::forall_e(
                Name::from_components(["y"]),
                nat.clone(),
                nat.clone(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let expected_value = Expr::lam(
            Name::from_components(["x"]),
            nat.clone(),
            Expr::lam(
                Name::from_components(["y"]),
                nat,
                Expr::bvar(1).expect("two Nat parameters fit the expression covenant"),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        assert_eq!(definition.base.type_, expected_type);
        assert_eq!(definition.value, expected_value);
    }

    #[test]
    fn source_let_chain_becomes_nested_nat_typed_core_let_expressions() {
        let result = check_nat_definition_source(
            b"def answer : Nat := let x := 41; let y := x; y",
            &nat_environment(),
            Budget::DEFAULT,
        )
        .expect("the bounded Nat let chain elaborates");
        assert!(matches!(
            result.outcome,
            Outcome::Complete(Verdict::Accepted { .. })
        ));
        let Declaration::Defn(definition) = result.declaration else {
            panic!("the seed command must elaborate to a definition");
        };
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        assert_eq!(
            definition.value,
            Expr::let_e(
                Name::from_components(["x"]),
                nat.clone(),
                Expr::lit(Literal::Nat(NatLit::from_u64(41))),
                Expr::let_e(
                    Name::from_components(["y"]),
                    nat,
                    Expr::bvar(0).expect("the outer local fits the expression covenant"),
                    Expr::bvar(0).expect("the inner local fits the expression covenant"),
                    false,
                ),
                false,
            )
        );
    }

    #[test]
    fn the_frontend_does_not_manufacture_the_nat_environment_or_a_verdict() {
        let result =
            check_nat_definition_source(b"def answer := 42", &Environment::new(), Budget::DEFAULT)
                .expect("parsing and elaboration still complete");
        assert!(matches!(
            result.outcome,
            Outcome::Complete(Verdict::Rejected {
                class: RejectClass::UnknownConstant,
                ..
            })
        ));
    }

    #[test]
    fn every_lexed_natural_radix_reaches_the_same_kernel_value() {
        for source in [
            b"def answer := 42".as_slice(),
            b"def answer := 0b10_1010".as_slice(),
            b"def answer := 0o52".as_slice(),
            b"def answer := 0x2A".as_slice(),
        ] {
            let result = check_nat_definition_source(source, &nat_environment(), Budget::DEFAULT)
                .expect("every natural-literal radix elaborates");
            assert!(matches!(
                result.outcome,
                Outcome::Complete(Verdict::Accepted { .. })
            ));
            let Declaration::Defn(definition) = result.declaration else {
                panic!("the seed command must elaborate to a definition");
            };
            assert!(matches!(
                definition.value.node(),
                ExprNode::Lit {
                    literal: Literal::Nat(value)
                } if value == &NatLit::from_u64(42)
            ));
        }
    }

    #[test]
    fn unsupported_or_malformed_trees_are_typed_refusals() {
        assert!(matches!(
            check_nat_definition_source(
                b"def answer := \"not a Nat\"",
                &nat_environment(),
                Budget::DEFAULT
            ),
            Err(NatDefinitionFrontendError::Parse(_))
        ));
        assert!(matches!(
            elaborate_nat_definition(&Syntax::Missing),
            Err(NatDefinitionElabError::UnexpectedSyntax { .. })
        ));
        assert!(matches!(
            elaborate_term(
                &Syntax::node(parser_kind(&["Term", "app"]), Vec::new()),
                &[],
                &Expr::const_(Name::from_components(["Nat"]), Vec::new()),
                false,
                None,
            ),
            Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "Lean.Parser.Term.app"
            })
        ));
        assert!(matches!(
            elaborate_term(
                &Syntax::node(parser_kind(&["Term", "paren"]), Vec::new()),
                &[],
                &Expr::const_(Name::from_components(["Nat"]), Vec::new()),
                false,
                None,
            ),
            Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "Lean.Parser.Term.paren"
            })
        ));
        for malformed in ["", "_1", "1_", "0x", "0x1_", "0b2"] {
            assert_eq!(
                decode_natural(malformed),
                Err(NatDefinitionElabError::InvalidNaturalLiteral)
            );
        }
    }

    #[test]
    fn deeply_parenthesized_term_elaborates_without_host_stack_recursion() {
        const DEPTH: usize = 20_000;
        let mut source = b"def answer := ".to_vec();
        source.extend(std::iter::repeat_n(b'(', DEPTH));
        source.extend_from_slice(b"42");
        source.extend(std::iter::repeat_n(b')', DEPTH));
        let parsed = parse_nat_definition(&source).expect("the bounded term parser is iterative");
        let declaration = elaborate_nat_definition(parsed.syntax())
            .expect("parenthesis elaboration uses an explicit work stack");
        let Declaration::Defn(definition) = declaration else {
            panic!("the nested source must elaborate to a definition");
        };
        assert!(matches!(
            definition.value.node(),
            ExprNode::Lit {
                literal: Literal::Nat(value)
            } if value == &fln_core::expr::NatLit::from_u64(42)
        ));
    }

    #[test]
    fn scalar_source_elaboration_decodes_reference_string_literals_exactly() {
        let parsed = parse_definition(b"def message : String := \"line\\nheart \\u2665\"")
            .expect("the bounded scalar source parses");
        let declaration = elaborate_definition(parsed.syntax())
            .expect("the canonical String tree elaborates without inventing authority");
        let Declaration::Defn(definition) = declaration else {
            panic!("the source command must elaborate to a definition");
        };
        assert_eq!(
            definition.base.type_,
            Expr::const_(Name::from_components(["String"]), Vec::new())
        );
        assert!(matches!(
            definition.value.node(),
            ExprNode::Lit {
                literal: Literal::Str(value)
            } if value == "line\nheart ♥"
        ));

        let nbsp = parse_definition("def message : String := \"left\\\n\u{00a0}right\"".as_bytes())
            .expect("NBSP after a string gap remains in the scalar grammar");
        let Declaration::Defn(nbsp) =
            elaborate_definition(nbsp.syntax()).expect("NBSP after a gap elaborates as content")
        else {
            panic!("the NBSP command must elaborate to a definition");
        };
        assert!(matches!(
            nbsp.value.node(),
            ExprNode::Lit {
                literal: Literal::Str(value)
            } if value == "left\u{00a0}right"
        ));

        let mixed = parse_definition(b"def message : String := let n := 1; \"ok\"")
            .expect("a Nat let inside a String definition is in the seed grammar");
        let Declaration::Defn(mixed) = elaborate_definition(mixed.syntax())
            .expect("the let binder must be Nat, not the String result type")
        else {
            panic!("the mixed let must elaborate to a definition");
        };
        let ExprNode::LetE {
            type_, value, body, ..
        } = mixed.value.node()
        else {
            panic!("the mixed command must be a let");
        };
        assert_eq!(
            type_,
            &Expr::const_(Name::from_components(["Nat"]), Vec::new())
        );
        assert!(matches!(
            value.node(),
            ExprNode::Lit {
                literal: Literal::Nat(_)
            }
        ));
        assert!(matches!(
            body.node(),
            ExprNode::Lit {
                literal: Literal::Str(value)
            } if value == "ok"
        ));

        let swapped = parse_definition(b"def answer : Nat := let s := \"hi\"; 1")
            .expect("a String let inside a Nat definition is in the seed grammar");
        let Declaration::Defn(swapped) = elaborate_definition(swapped.syntax())
            .expect("the let binder must be String, not the Nat result type")
        else {
            panic!("the swapped let must elaborate to a definition");
        };
        let ExprNode::LetE { type_, .. } = swapped.value.node() else {
            panic!("the swapped command must be a let");
        };
        assert_eq!(
            type_,
            &Expr::const_(Name::from_components(["String"]), Vec::new())
        );

        let typed = parse_definition(b"def typed := let value : String := \"explicit\"; value")
            .expect("an exact explicit String let type is in the scalar grammar");
        let Declaration::Defn(typed) = elaborate_definition(typed.syntax())
            .expect("the explicit let type elaborates into the core let")
        else {
            panic!("the typed let command must elaborate to a definition");
        };
        assert_eq!(
            typed.base.type_,
            Expr::const_(Name::from_components(["String"]), Vec::new())
        );
        let ExprNode::LetE { type_, value, .. } = typed.value.node() else {
            panic!("the typed command must be a let");
        };
        assert_eq!(
            type_,
            &Expr::const_(Name::from_components(["String"]), Vec::new())
        );
        assert!(matches!(
            value.node(),
            ExprNode::Lit {
                literal: Literal::Str(value)
            } if value == "explicit"
        ));

        let raw = parse_definition(b"def raw : String := r##\"left \\\\ right\"##")
            .expect("the lexer-approved raw String literal parses");
        let Declaration::Defn(raw) =
            elaborate_definition(raw.syntax()).expect("the raw String literal elaborates")
        else {
            panic!("the raw command must elaborate to a definition");
        };
        assert!(matches!(
            raw.value.node(),
            ExprNode::Lit {
                literal: Literal::Str(value)
            } if value == "left \\\\ right"
        ));

        assert_eq!(
            decode_string(r#""\\\"\'\r\n\t\x41\u2665""#),
            Ok(Literal::Str("\\\"'\r\n\tA♥".to_owned()))
        );
        assert_eq!(
            decode_string("\"left\\\n  right\""),
            Ok(Literal::Str("leftright".to_owned()))
        );
        assert_eq!(
            decode_string("\"left\\\n\t right\""),
            Ok(Literal::Str("leftright".to_owned())),
            "pin gap whitespace is space, tab, CR, LF"
        );
        assert_eq!(
            decode_string("\"left\\\n\u{00a0}right\""),
            Ok(Literal::Str("left\u{00a0}right".to_owned())),
            "NBSP after a gap is content, not Char.isWhitespace"
        );
        assert_eq!(
            decode_string("\"left\\\n\u{000c}right\""),
            Ok(Literal::Str("left\u{000c}right".to_owned())),
            "form feed after a gap is content"
        );
        for malformed in [
            "",
            "\"unterminated",
            "\"\\z\"",
            "r#\"extra closer\"##",
            "\"a\\ b\"",
            "\"left\\\n\n  right\"",
            "\"\\uD800\"",
        ] {
            assert_eq!(
                decode_string(malformed),
                Err(NatDefinitionElabError::InvalidStringLiteral)
            );
        }
        assert_eq!(
            decode_string("\"\\u0000\""),
            Ok(Literal::Str("\0".to_owned()))
        );
    }

    #[test]
    fn omitted_result_type_is_inferred_from_the_elaborated_value() {
        let string_ty = Expr::const_(Name::from_components(["String"]), Vec::new());
        let nat_ty = Expr::const_(Name::from_components(["Nat"]), Vec::new());

        let parsed = parse_definition(b"def message := \"hello\"")
            .expect("an un-ascribed String literal is in the scalar grammar");
        let Declaration::Defn(definition) = elaborate_definition(parsed.syntax())
            .expect("omitted String result must not be stamped Nat")
        else {
            panic!("the un-ascribed String command must elaborate to a definition");
        };
        assert_eq!(definition.base.type_, string_ty);
        assert!(matches!(
            definition.value.node(),
            ExprNode::Lit {
                literal: Literal::Str(value)
            } if value == "hello"
        ));

        let parsed = parse_definition(b"def message := let n := 1; \"ok\"")
            .expect("an un-ascribed let-of-String is in the scalar grammar");
        let Declaration::Defn(mixed) = elaborate_definition(parsed.syntax())
            .expect("the omitted result follows the let body, not the Nat binder")
        else {
            panic!("the un-ascribed mixed let must elaborate to a definition");
        };
        assert_eq!(mixed.base.type_, string_ty);
        let ExprNode::LetE {
            type_, value, body, ..
        } = mixed.value.node()
        else {
            panic!("the mixed command must be a let");
        };
        assert_eq!(type_, &nat_ty);
        assert!(matches!(
            value.node(),
            ExprNode::Lit {
                literal: Literal::Nat(_)
            }
        ));
        assert!(matches!(
            body.node(),
            ExprNode::Lit {
                literal: Literal::Str(value)
            } if value == "ok"
        ));

        let parsed = parse_definition(b"def copy (value : String) := value")
            .expect("an un-ascribed String parameter identity is in the scalar grammar");
        let Declaration::Defn(copy) = elaborate_definition(parsed.syntax())
            .expect("the omitted result follows the bound String parameter")
        else {
            panic!("the un-ascribed String identity must elaborate to a definition");
        };
        assert_eq!(
            copy.base.type_,
            Expr::forall_e(
                Name::from_components(["value"]),
                string_ty.clone(),
                string_ty,
                BinderInfo::Default,
            )
        );

        let parsed = parse_definition(b"def answer := 42")
            .expect("an un-ascribed Nat literal stays in the scalar grammar");
        let Declaration::Defn(answer) =
            elaborate_definition(parsed.syntax()).expect("omitted Nat result remains Nat")
        else {
            panic!("the un-ascribed Nat command must elaborate to a definition");
        };
        assert_eq!(answer.base.type_, nat_ty);
    }

    #[test]
    fn omitted_result_type_follows_environment_constants_and_applications() {
        let string_ty = Expr::const_(Name::from_components(["String"]), Vec::new());
        let copy_ty = Expr::forall_e(
            Name::from_components(["value"]),
            string_ty.clone(),
            string_ty.clone(),
            BinderInfo::Default,
        );
        let env = publish_test_axiom(&nat_environment(), "String", Expr::sort(Level::one()));
        let env = publish_test_axiom(&env, "greet", string_ty.clone());
        let env = publish_test_axiom(&env, "copy", copy_ty.clone());

        let parsed = parse_definition(b"def message := greet")
            .expect("an un-ascribed constant reference is in the scalar grammar");
        let Declaration::Defn(greet) = elaborate_definition_in(parsed.syntax(), &env)
            .expect("omitted result follows a String constant in the snapshot")
        else {
            panic!("the greet command must elaborate to a definition");
        };
        assert_eq!(greet.base.type_, string_ty);

        let parsed = parse_definition(b"def message := copy \"hello\"")
            .expect("an un-ascribed String application is in the scalar grammar");
        let Declaration::Defn(applied) = elaborate_definition_in(parsed.syntax(), &env)
            .expect("omitted result follows a saturated String function")
        else {
            panic!("the applied command must elaborate to a definition");
        };
        assert_eq!(applied.base.type_, string_ty);

        let parsed = parse_definition(b"def alias := copy")
            .expect("an un-ascribed function alias is in the scalar grammar");
        let Declaration::Defn(alias) = elaborate_definition_in(parsed.syntax(), &env)
            .expect("omitted result keeps a closed String function type")
        else {
            panic!("the alias command must elaborate to a definition");
        };
        assert_eq!(alias.base.type_, copy_ty);
        let ExprNode::Lam {
            binder_type, body, ..
        } = alias.value.node()
        else {
            panic!("a function alias must eta-expand to a lambda");
        };
        assert_eq!(binder_type, &string_ty);
        assert!(matches!(body.node(), ExprNode::App { .. }));

        let parsed = parse_definition(b"def message := let x := copy \"hi\"; x")
            .expect("an un-ascribed let of an application is in the scalar grammar");
        let Declaration::Defn(bound) = elaborate_definition_in(parsed.syntax(), &env)
            .expect("the let binder and omitted result both follow the application")
        else {
            panic!("the bound command must elaborate to a definition");
        };
        assert_eq!(bound.base.type_, string_ty);
        let ExprNode::LetE { type_, .. } = bound.value.node() else {
            panic!("the bound command must be a let");
        };
        assert_eq!(type_, &string_ty);

        let parsed = parse_definition(b"def message := copy \"hello\"")
            .expect("the env-less door still parses the same tree");
        let Declaration::Defn(without_env) = elaborate_definition(parsed.syntax())
            .expect("the env-less API remains the Nat default for applications")
        else {
            panic!("the env-less command must elaborate to a definition");
        };
        assert_eq!(
            without_env.base.type_,
            Expr::const_(Name::from_components(["Nat"]), Vec::new())
        );
    }
}
