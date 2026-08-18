//! **fln-elab** — Athanor — the elaborator: the monadic tower, the unifier's
//! approximation ladder, Synod (the instance engine), match compilation, the
//! native tactic framework, the Mirror façade registry, and the deterministic
//! dataflow scheduler (plan §10, §4.3).
//!
//! The full tower is not present yet. Bead `fln-5720` establishes its first
//! end-to-end production seam: one parsed bounded exact `Nat`/`String`/`Bool`
//! definition, explicit first-order function, parenthesized application,
//! pin-precedence bounded scalar infix expression (including type-directed
//! Nat/String `==`), local let chain, terminal bounded
//! `Lean.Parser.Command.eval` expression, or standalone bounded
//! `Lean.Parser.Command.check` query becomes
//! a real [`Declaration::Defn`] candidate and is handed to Crucible's sole check
//! authority. Evaluation and checking receive unspellable generated identities
//! directly; neither is reparsed as fabricated definition source, and checking
//! never reaches compilation or execution. The original Nat-only door remains
//! strict.
//! This is a subset of the final abstraction, not a substitute for unification,
//! expected-type propagation, transactions, macros, instances, or tactics.
//! Unsupported source is refused by an explicit variant.

#![forbid(unsafe_code)]

pub mod seed;

use fln_bignum::interop::literal_from_bignat;
use fln_bignum::nat::BigNat;
use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal};
use fln_core::name::{LeafView, Name};
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
    InvalidGeneratedEvaluationName,
    InvalidGeneratedCheckName,
    CannotInferCheckType,
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
            Self::InvalidGeneratedEvaluationName => write!(
                formatter,
                "evaluation name must be one numeric component below the anonymous root"
            ),
            Self::InvalidGeneratedCheckName => write!(
                formatter,
                "check name must be one numeric component below the anonymous root"
            ),
            Self::CannotInferCheckType => {
                write!(formatter, "bounded check term has no inferable type")
            }
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
    // Pin `decodeQuotedChar` (`Init/Meta/Defs.lean:1096-1105`) feeds the
    // digits to `Char.ofNat`. Invalid scalars (the UTF-16 surrogates a
    // four-digit `\u` can name) become `'\0'`, not a decode failure
    // (`Prelude.lean:2867-2870`). `char::from_u32` is the Rust refusal;
    // using it here rejected `"\uD800"` while the pin accepted a NUL.
    Ok(char::from_u32(value).unwrap_or('\0'))
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

/// Elaborate one canonical bounded `Lean.Parser.Command.eval` tree.
///
/// Evaluation commands do not enter elaboration by pretending to be user
/// definitions. The caller supplies an unspellable numeric identity, this
/// function elaborates the expression directly against `environment`, and the
/// engine then sends the resulting declaration through the ordinary kernel,
/// independent-checker, compiler, and VM path. Only a one-component numeric
/// name is accepted so this low-level door cannot publish an evaluation under a
/// source-spellable declaration identity.
pub fn elaborate_evaluation_in(
    syntax: &Syntax,
    generated_name: Name,
    environment: &Environment,
) -> Result<Declaration, NatDefinitionElabError> {
    if !generated_name.parent().is_anonymous()
        || !matches!(generated_name.leaf_view(), LeafView::Num(_))
    {
        return Err(NatDefinitionElabError::InvalidGeneratedEvaluationName);
    }
    let evaluation = expect_node(
        syntax,
        &parser_kind(&["Command", "eval"]),
        2,
        "Lean.Parser.Command.eval",
    )?;
    let [keyword, term] = evaluation else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "Lean.Parser.Command.eval",
        });
    };
    expect_atom(keyword, "#eval", "evaluation keyword")?;
    let mut expression = elaborate_term(term, &[], &nat_const(), true, Some(environment))?;
    let declaration_type = infer_expr_type(&expression, &[], Some(environment))
        .filter(|type_| acceptable_inferred(type_, true))
        .unwrap_or_else(nat_const);
    expression = eta_expand_nondependent(expression, &declaration_type)?;
    Ok(Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: generated_name.clone(),
            level_params: Vec::new(),
            type_: declaration_type,
        },
        value: expression,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![generated_name],
    }))
}

/// Elaborate one canonical bounded `Lean.Parser.Command.check` tree into a
/// definition candidate used only for dual-checker validation.
///
/// The generated identity is deliberately unspellable from source. The engine
/// may admit this candidate in a scratch successor to prove the inferred type,
/// but a `#check` query never executes the body and never exposes that successor
/// environment to its caller.
pub fn elaborate_check_in(
    syntax: &Syntax,
    generated_name: Name,
    environment: &Environment,
) -> Result<Declaration, NatDefinitionElabError> {
    if !generated_name.parent().is_anonymous()
        || !matches!(generated_name.leaf_view(), LeafView::Num(_))
    {
        return Err(NatDefinitionElabError::InvalidGeneratedCheckName);
    }
    let check = expect_node(
        syntax,
        &parser_kind(&["Command", "check"]),
        2,
        "Lean.Parser.Command.check",
    )?;
    let [keyword, term] = check else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "Lean.Parser.Command.check",
        });
    };
    expect_atom(keyword, "#check", "check keyword")?;
    let expression = elaborate_term(term, &[], &nat_const(), true, Some(environment))?;
    let declaration_type = infer_expr_type(&expression, &[], Some(environment))
        .ok_or(NatDefinitionElabError::CannotInferCheckType)?;
    Ok(Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: generated_name.clone(),
            level_params: Vec::new(),
            type_: declaration_type,
        },
        value: expression,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![generated_name],
    }))
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
    allow_bool_literals: bool,
    environment: Option<&Environment>,
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
    if allow_bool_literals && !environment.is_some_and(|environment| environment.contains(name)) {
        if name == &Name::from_components(["true"]) {
            return Ok(Expr::const_(
                Name::from_components(["Bool", "true"]),
                Vec::new(),
            ));
        }
        if name == &Name::from_components(["false"]) {
            return Ok(Expr::const_(
                Name::from_components(["Bool", "false"]),
                Vec::new(),
            ));
        }
    }
    Ok(Expr::const_(name.clone(), Vec::new()))
}

fn elaborate_atom(
    syntax: &Syntax,
    locals: &[(Name, Expr)],
    allow_string: bool,
    environment: Option<&Environment>,
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
        Syntax::Ident { val: name, .. } => {
            elaborate_nat_reference(name, locals, allow_string, environment)?
        }
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

enum BoundedInfixIntrinsic {
    Fixed {
        spelling: &'static str,
        intrinsic: Name,
    },
    ScalarBeq,
}

impl BoundedInfixIntrinsic {
    const fn spelling(&self) -> &'static str {
        match self {
            Self::Fixed { spelling, .. } => spelling,
            Self::ScalarBeq => "==",
        }
    }
}

fn bounded_infix_intrinsic(kind: &Name, allow_string: bool) -> Option<BoundedInfixIntrinsic> {
    if allow_string && kind == &Name::str(Name::anonymous(), "term_==_") {
        return Some(BoundedInfixIntrinsic::ScalarBeq);
    }
    let rows = [
        ("term_|||_", "|||", ["Nat", "lor"]),
        ("term_^^^_", "^^^", ["Nat", "xor"]),
        ("term_&&&_", "&&&", ["Nat", "land"]),
        ("term_+_", "+", ["Nat", "add"]),
        ("term_-_", "-", ["Nat", "sub"]),
        ("term_*_", "*", ["Nat", "mul"]),
        ("term_/_", "/", ["Nat", "div"]),
        ("term_%_", "%", ["Nat", "mod"]),
        ("term_<<<_", "<<<", ["Nat", "shiftLeft"]),
        ("term_>>>_", ">>>", ["Nat", "shiftRight"]),
        ("term_^_", "^", ["Nat", "pow"]),
    ];
    for (syntax_kind, spelling, constant) in rows {
        if kind == &Name::str(Name::anonymous(), syntax_kind) {
            return Some(BoundedInfixIntrinsic::Fixed {
                spelling,
                intrinsic: Name::from_components(constant),
            });
        }
    }
    if allow_string && kind == &Name::str(Name::anonymous(), "term_++_") {
        return Some(BoundedInfixIntrinsic::Fixed {
            spelling: "++",
            intrinsic: Name::from_components(["String", "append"]),
        });
    }
    None
}

fn elaborate_nonlet_term(
    syntax: &Syntax,
    locals: &[(Name, Expr)],
    allow_string: bool,
    environment: Option<&Environment>,
) -> Result<Expr, NatDefinitionElabError> {
    enum Task<'a> {
        Visit(&'a Syntax),
        Apply(usize),
        ApplyInfix {
            values_before: usize,
            intrinsic: BoundedInfixIntrinsic,
        },
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
                    values.push(elaborate_atom(term, locals, allow_string, environment)?);
                    continue;
                };
                if let Some(intrinsic) = bounded_infix_intrinsic(kind, allow_string) {
                    let parts = expect_node(term, kind, 3, "bounded scalar infix expression")?;
                    expect_atom(
                        &parts[1],
                        intrinsic.spelling(),
                        "bounded scalar infix operator",
                    )?;
                    tasks.push(Task::ApplyInfix {
                        values_before: values.len(),
                        intrinsic,
                    });
                    tasks.push(Task::Visit(&parts[2]));
                    tasks.push(Task::Visit(&parts[0]));
                    continue;
                }
                if kind != &parser_kind(&["Term", "app"]) {
                    values.push(elaborate_atom(term, locals, allow_string, environment)?);
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
            Task::ApplyInfix {
                values_before,
                intrinsic,
            } => {
                if values.len() != values_before.saturating_add(2) {
                    return Err(NatDefinitionElabError::UnexpectedSyntax {
                        expected: "complete bounded infix operands",
                    });
                }
                let right = values
                    .pop()
                    .ok_or(NatDefinitionElabError::UnexpectedSyntax {
                        expected: "bounded infix right operand",
                    })?;
                let left = values
                    .pop()
                    .ok_or(NatDefinitionElabError::UnexpectedSyntax {
                        expected: "bounded infix left operand",
                    })?;
                let intrinsic = match intrinsic {
                    BoundedInfixIntrinsic::Fixed { intrinsic, .. } => intrinsic,
                    BoundedInfixIntrinsic::ScalarBeq => {
                        let left_type = infer_expr_type(&left, locals, environment);
                        let right_type = infer_expr_type(&right, locals, environment);
                        let string = string_const();
                        if left_type.as_ref() == Some(&string)
                            && right_type.as_ref() == Some(&string)
                        {
                            Name::from_components(["String", "decEq"])
                        } else {
                            Name::from_components(["Nat", "beq"])
                        }
                    }
                };
                values.push(Expr::app(
                    Expr::app(Expr::const_(intrinsic, Vec::new()), left),
                    right,
                ));
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
    // Sequential seed lets are a right-nested `Term.let` spine the parser
    // builds with a heap fold. Recursing one frame per binder would stack-
    // fault a legal source file (FL-INV-07).
    let mut current = syntax;
    let mut locals = locals.to_vec();
    let mut bindings = Vec::new();
    while let Syntax::Node { kind, args, .. } = current
        && kind == &parser_kind(&["Term", "let"])
    {
        let (name, binder_type, value, body) =
            peel_let(args, &locals, result_type, allow_string, environment)?;
        locals.push((name.clone(), binder_type.clone()));
        bindings.push((name, binder_type, value));
        current = body;
    }
    let mut expression = elaborate_nonlet_term(current, &locals, allow_string, environment)?;
    for (name, binder_type, value) in bindings.into_iter().rev() {
        expression = Expr::let_e(name, binder_type, value, expression, false);
    }
    Ok(expression)
}

fn nat_const() -> Expr {
    Expr::const_(Name::from_components(["Nat"]), Vec::new())
}

fn string_const() -> Expr {
    Expr::const_(Name::from_components(["String"]), Vec::new())
}

fn bool_const() -> Expr {
    Expr::const_(Name::from_components(["Bool"]), Vec::new())
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
    let mut current = ty;
    while let ExprNode::ForallE { body, .. } = current.node() {
        if body.has_loose_bvars() {
            return false;
        }
        current = body;
    }
    match current.node() {
        ExprNode::Const { name, levels } if levels.is_empty() => {
            name == &Name::from_components(["Nat"])
                || (allow_string
                    && (name == &Name::from_components(["String"])
                        || name == &Name::from_components(["Bool"])))
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
    let mut extra = Vec::new();
    let mut current = value;
    while let ExprNode::LetE { type_, body, .. } = current.node() {
        extra.push(type_.clone());
        current = body;
    }
    let mut owned = None;
    let locals: &[(Name, Expr)] = if extra.is_empty() {
        locals
    } else {
        let extended = owned.insert(locals.to_vec());
        for type_ in extra {
            extended.push((Name::anonymous(), type_));
        }
        extended
    };
    match current.node() {
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
        ExprNode::Const { name, levels }
            if levels.is_empty()
                && (name == &Name::from_components(["Bool", "false"])
                    || name == &Name::from_components(["Bool", "true"])) =>
        {
            Some(bool_const())
        }
        ExprNode::Const { name, levels } if levels.is_empty() => {
            environment_constant_type(name, environment)
        }
        ExprNode::App { .. } => {
            let mut arity = 0_usize;
            let mut head = current;
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

fn peel_let<'a>(
    parts: &'a [Syntax],
    locals: &[(Name, Expr)],
    result_type: &Expr,
    allow_string: bool,
    environment: Option<&Environment>,
) -> Result<(Name, Expr, Expr, &'a Syntax), NatDefinitionElabError> {
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
    Ok((local_name.clone(), binder_type, value, body))
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
                name: Name::from_components(name.split('.')),
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

    fn binary_intrinsic(expression: &Expr) -> (&Name, &Expr, &Expr) {
        let ExprNode::App {
            f: partial,
            a: right,
        } = expression.node()
        else {
            panic!("the bounded infix must lower to a saturated application");
        };
        let ExprNode::App { f: head, a: left } = partial.node() else {
            panic!("the bounded infix must lower to a binary application");
        };
        let ExprNode::Const { name, levels } = head.node() else {
            panic!("the bounded infix head must be a constant");
        };
        assert!(levels.is_empty());
        (name, left, right)
    }

    fn lambda_body(expression: &Expr) -> &Expr {
        let ExprNode::Lam { body, .. } = expression.node() else {
            panic!("the bounded function must remain a lambda spine");
        };
        body
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
    fn bounded_infix_syntax_lowers_to_exact_checked_intrinsic_names() {
        let parsed = parse_definition(b"def answer := 2 + 3 * 4 ^ 2")
            .expect("the bounded infix expression parses");
        let Declaration::Defn(definition) =
            elaborate_definition(parsed.syntax()).expect("the bounded infix expression elaborates")
        else {
            panic!("the bounded infix command must elaborate to a definition");
        };
        let (add, left, multiplied) = binary_intrinsic(&definition.value);
        assert_eq!(add, &Name::from_components(["Nat", "add"]));
        assert!(matches!(
            left.node(),
            ExprNode::Lit {
                literal: Literal::Nat(value)
            } if value == &NatLit::from_u64(2)
        ));
        let (mul, three, powered) = binary_intrinsic(multiplied);
        assert_eq!(mul, &Name::from_components(["Nat", "mul"]));
        assert!(matches!(
            three.node(),
            ExprNode::Lit {
                literal: Literal::Nat(value)
            } if value == &NatLit::from_u64(3)
        ));
        let (pow, four, two) = binary_intrinsic(powered);
        assert_eq!(pow, &Name::from_components(["Nat", "pow"]));
        assert!(matches!(
            (four.node(), two.node()),
            (
                ExprNode::Lit {
                    literal: Literal::Nat(four)
                },
                ExprNode::Lit {
                    literal: Literal::Nat(two)
                }
            ) if four == &NatLit::from_u64(4) && two == &NatLit::from_u64(2)
        ));

        let parsed = parse_definition(b"def answer := 20 - 3 - 2")
            .expect("left-associated subtraction parses");
        let Declaration::Defn(definition) =
            elaborate_definition(parsed.syntax()).expect("left-associated subtraction elaborates")
        else {
            panic!("subtraction must elaborate to a definition");
        };
        let (outer_sub, inner_sub, _) = binary_intrinsic(&definition.value);
        assert_eq!(outer_sub, &Name::from_components(["Nat", "sub"]));
        assert_eq!(
            binary_intrinsic(inner_sub).0,
            &Name::from_components(["Nat", "sub"])
        );

        let parsed =
            parse_definition(b"def answer := 2 ^ 3 ^ 2").expect("right-associated power parses");
        let Declaration::Defn(definition) =
            elaborate_definition(parsed.syntax()).expect("right-associated power elaborates")
        else {
            panic!("power must elaborate to a definition");
        };
        let (outer_pow, _, inner_pow) = binary_intrinsic(&definition.value);
        assert_eq!(outer_pow, &Name::from_components(["Nat", "pow"]));
        assert_eq!(
            binary_intrinsic(inner_pow).0,
            &Name::from_components(["Nat", "pow"])
        );

        let parsed = parse_definition(b"def message : String := \"franken\" ++ \"lean\"")
            .expect("bounded String append notation parses");
        let Declaration::Defn(definition) = elaborate_definition(parsed.syntax())
            .expect("bounded String append notation elaborates")
        else {
            panic!("String append must elaborate to a definition");
        };
        assert_eq!(
            binary_intrinsic(&definition.value).0,
            &Name::from_components(["String", "append"])
        );

        let parsed = parse_definition(b"def answer : Bool := 40 + 2 == 42")
            .expect("bounded Nat equality notation parses");
        let Declaration::Defn(definition) = elaborate_definition(parsed.syntax())
            .expect("bounded Nat equality notation elaborates")
        else {
            panic!("Nat equality must elaborate to a definition");
        };
        let (beq, sum, expected) = binary_intrinsic(&definition.value);
        assert_eq!(beq, &Name::from_components(["Nat", "beq"]));
        assert_eq!(
            binary_intrinsic(sum).0,
            &Name::from_components(["Nat", "add"])
        );
        assert!(matches!(
            expected.node(),
            ExprNode::Lit {
                literal: Literal::Nat(value)
            } if value == &NatLit::from_u64(42)
        ));

        let parsed = parse_definition(b"def same (left right : String) : Bool := left == right")
            .expect("bounded String equality notation parses");
        let Declaration::Defn(definition) = elaborate_definition(parsed.syntax())
            .expect("bounded String equality notation elaborates")
        else {
            panic!("String equality must elaborate to a definition");
        };
        assert_eq!(
            binary_intrinsic(lambda_body(lambda_body(&definition.value))).0,
            &Name::from_components(["String", "decEq"])
        );

        let parsed = parse_definition(b"def answer := 1 + 2")
            .expect("the negative control starts from a canonical infix tree");
        let mut forged = parsed.syntax().clone();
        let Syntax::Node { args, .. } = &mut forged else {
            panic!("the command root must remain a syntax node");
        };
        let Syntax::Node {
            args: definition, ..
        } = &mut args[1]
        else {
            panic!("the declaration payload must remain a definition node");
        };
        let Syntax::Node { args: value, .. } = &mut definition[3] else {
            panic!("the definition value must remain a simple value node");
        };
        let Syntax::Node {
            args: infix_parts, ..
        } = &mut value[1]
        else {
            panic!("the bounded infix must remain a syntax node");
        };
        let Syntax::Atom { val, .. } = &mut infix_parts[1] else {
            panic!("the bounded infix token must remain an atom");
        };
        *val = "*".to_owned();
        assert_eq!(
            elaborate_definition(&forged),
            Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "bounded scalar infix operator"
            })
        );
    }

    #[test]
    fn long_infix_spine_elaborates_without_host_stack_recursion() {
        const TERMS: usize = 4_000;
        let mut source = b"def answer := 1".to_vec();
        for _ in 1..TERMS {
            source.extend_from_slice(b" + 1");
        }
        let parsed = parse_nat_definition(&source).expect("the long bounded expression parses");
        let Declaration::Defn(definition) = elaborate_nat_definition(parsed.syntax())
            .expect("bounded infix elaboration uses an explicit task stack")
        else {
            panic!("the long bounded expression must elaborate to a definition");
        };
        assert_eq!(
            definition.base.type_,
            Expr::const_(Name::from_components(["Nat"]), Vec::new())
        );
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
        // Pin `Char.ofNat`: a four-digit `\u` that names a surrogate is
        // `'\0'`, not a refused literal. The lexer already accepted the
        // hex digits; decode must not invent a refusal the pin does not.
        assert_eq!(
            decode_string("\"\\uD800\""),
            Ok(Literal::Str("\0".to_owned()))
        );
        assert_eq!(
            decode_string("\"\\uDFFF\""),
            Ok(Literal::Str("\0".to_owned()))
        );

        let parsed = parse_definition(br#"def s : String := "\uD800""#)
            .expect("the lexer accepts a four-digit surrogate escape");
        let Declaration::Defn(definition) = elaborate_definition(parsed.syntax())
            .expect("Char.ofNat maps the surrogate to NUL, so the definition elaborates")
        else {
            panic!("the surrogate escape must elaborate to a definition");
        };
        assert!(matches!(
            definition.value.node(),
            ExprNode::Lit {
                literal: Literal::Str(value)
            } if value == "\0"
        ));
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
    fn scalar_bool_literals_resolve_to_exact_constructor_names() {
        let bool_ty = Expr::const_(Name::from_components(["Bool"]), Vec::new());
        let env = publish_test_axiom(&nat_environment(), "Bool", Expr::sort(Level::one()));
        let env = publish_test_axiom(&env, "Bool.false", bool_ty.clone());
        let env = publish_test_axiom(&env, "Bool.true", bool_ty.clone());

        for (spelling, expected) in [
            ("true", "Bool.true"),
            ("false", "Bool.false"),
            ("Bool.true", "Bool.true"),
            ("Bool.false", "Bool.false"),
        ] {
            let source = format!("def answer := {spelling}");
            let parsed = parse_definition(source.as_bytes())
                .expect("the bounded parser accepts a Bool constructor reference");
            let Declaration::Defn(definition) = elaborate_definition_in(parsed.syntax(), &env)
                .expect("the bounded scalar elaborator resolves the Bool constructor")
            else {
                panic!("the Bool literal command must elaborate to a definition");
            };
            assert_eq!(definition.base.type_, bool_ty, "source spelling {spelling}");
            assert!(matches!(
                definition.value.node(),
                ExprNode::Const { name, levels }
                    if name.to_display_string() == expected && levels.is_empty()
            ));

            let Declaration::Defn(without_environment) = elaborate_definition(parsed.syntax())
                .expect("the environment-free helper still constructs a coherent candidate")
            else {
                panic!("the environment-free Bool command must elaborate to a definition");
            };
            assert_eq!(
                without_environment.base.type_, bool_ty,
                "source spelling {spelling}"
            );
        }
    }

    #[test]
    fn bool_literal_resolution_never_overrides_a_local_or_checked_global() {
        let parsed = parse_definition(b"def keep (true : Nat) := true")
            .expect("a parameter named true remains source-spellable");
        let Declaration::Defn(local) = elaborate_definition(parsed.syntax())
            .expect("a local named true takes precedence over exported Bool.true")
        else {
            panic!("the local-precedence command must elaborate to a definition");
        };
        let ExprNode::Lam { body, .. } = local.value.node() else {
            panic!("the checked local must become a lambda");
        };
        assert!(matches!(body.node(), ExprNode::BVar { idx } if *idx == 0));

        let nat_ty = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let env = publish_test_axiom(&nat_environment(), "true", nat_ty.clone());
        let parsed = parse_definition(b"def answer := true")
            .expect("an exact checked global named true remains source-spellable");
        let Declaration::Defn(global) = elaborate_definition_in(parsed.syntax(), &env)
            .expect("the exact checked global takes precedence over exported Bool.true")
        else {
            panic!("the global-precedence command must elaborate to a definition");
        };
        assert_eq!(global.base.type_, nat_ty);
        assert!(matches!(
            global.value.node(),
            ExprNode::Const { name, levels }
                if name.to_display_string() == "true" && levels.is_empty()
        ));

        let parsed = parse_nat_definition(b"def answer := true")
            .expect("the legacy Nat door still parses an ordinary identifier");
        let Declaration::Defn(legacy) = elaborate_nat_definition(parsed.syntax())
            .expect("the legacy Nat door does not acquire Bool literal semantics")
        else {
            panic!("the legacy Nat command must elaborate to a definition");
        };
        assert_eq!(legacy.base.type_, nat_ty);
        assert!(matches!(
            legacy.value.node(),
            ExprNode::Const { name, levels }
                if name.to_display_string() == "true" && levels.is_empty()
        ));
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

    #[test]
    fn evaluation_command_elaborates_its_expression_without_a_fake_definition() {
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let nat_add = Expr::forall_e(
            Name::from_components(["left"]),
            nat.clone(),
            Expr::forall_e(
                Name::from_components(["right"]),
                nat.clone(),
                nat.clone(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let environment = publish_test_axiom(&nat_environment(), "Nat.add", nat_add);
        let parsed = fln_parse::parse_source_command(b"#eval let x : Nat := 40; Nat.add x 2")
            .expect("the bounded evaluation command parses directly");
        let generated = Name::num(Name::anonymous(), 7);
        let Declaration::Defn(evaluation) =
            elaborate_evaluation_in(parsed.syntax(), generated.clone(), &environment)
                .expect("the canonical evaluation command elaborates")
        else {
            panic!("evaluation elaboration must produce a checked definition candidate"); // ubs:ignore — test-only diagnostic.
        };

        assert_eq!(evaluation.base.name, generated);
        assert_eq!(evaluation.base.type_, nat);
        assert_eq!(evaluation.all, vec![evaluation.base.name.clone()]);
        assert!(matches!(evaluation.value.node(), ExprNode::LetE { .. }));

        let source_name = Name::from_components(["pretendEval"]);
        assert_eq!(
            elaborate_evaluation_in(parsed.syntax(), source_name, &environment),
            Err(NatDefinitionElabError::InvalidGeneratedEvaluationName)
        );

        let fake_definition = parse_definition(b"def pretendEval := 42")
            .expect("the negative control is a valid definition tree");
        assert!(matches!(
            elaborate_evaluation_in(
                fake_definition.syntax(),
                Name::num(Name::anonymous(), 8),
                &environment,
            ),
            Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "Lean.Parser.Command.eval"
            })
        ));
    }

    #[test]
    fn check_command_infers_a_type_without_executing_or_guessing() {
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let nat_add = Expr::forall_e(
            Name::from_components(["left"]),
            nat.clone(),
            Expr::forall_e(
                Name::from_components(["right"]),
                nat.clone(),
                nat.clone(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let environment = publish_test_axiom(&nat_environment(), "Nat.add", nat_add.clone());

        let parsed = fln_parse::parse_source_command(b"#check Nat.add")
            .expect("the bounded check command parses directly");
        let generated = Name::num(Name::anonymous(), 9);
        let Declaration::Defn(check) =
            elaborate_check_in(parsed.syntax(), generated.clone(), &environment)
                .expect("the canonical check command elaborates")
        else {
            panic!("check elaboration must produce a checker candidate"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(check.base.name, generated);
        assert_eq!(check.base.type_, nat_add);
        assert!(
            matches!(check.value.node(), ExprNode::Const { name, .. } if name == &Name::from_components(["Nat", "add"]))
        );

        let type_query = fln_parse::parse_source_command(b"#check Nat")
            .expect("the bounded type check parses directly");
        let Declaration::Defn(type_check) = elaborate_check_in(
            type_query.syntax(),
            Name::num(Name::anonymous(), 10),
            &environment,
        )
        .expect("checking a type infers its universe") else {
            panic!("type check elaboration must produce a checker candidate"); // ubs:ignore — test-only diagnostic.
        };
        assert!(matches!(
            type_check.base.type_.node(),
            ExprNode::Sort { level } if level.to_nat() == Some(1)
        ));

        assert_eq!(
            elaborate_check_in(
                parsed.syntax(),
                Name::from_components(["sourceVisible"]),
                &environment,
            ),
            Err(NatDefinitionElabError::InvalidGeneratedCheckName)
        );
        let evaluation = fln_parse::parse_source_command(b"#eval 42")
            .expect("the negative control is a valid evaluation tree");
        assert!(matches!(
            elaborate_check_in(
                evaluation.syntax(),
                Name::num(Name::anonymous(), 11),
                &environment,
            ),
            Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "Lean.Parser.Command.check"
            })
        ));
    }

    #[test]
    fn sequential_lets_elaborate_without_stack_recursion() {
        // Sequential seed lets are a right-nested `Term.let` spine the parser
        // builds with a heap fold. Recursing one elaborator frame per binder
        // would stack-fault a legal source file (FL-INV-07).
        let mut source = String::from("def answer := ");
        for index in 0..400 {
            source.push_str(&format!("let x{index} := 1; "));
        }
        source.push_str("x399");
        let parsed = parse_definition(source.as_bytes())
            .expect("400 sequential lets are in the seed grammar");
        let Declaration::Defn(definition) =
            elaborate_definition(parsed.syntax()).expect("a deep let spine must not stack-fault")
        else {
            panic!("the deep let command must elaborate to a definition");
        };
        assert_eq!(
            definition.base.type_,
            Expr::const_(Name::from_components(["Nat"]), Vec::new()),
            "omitted result follows the last binder through the let spine"
        );
        let mut current = &definition.value;
        for _ in 0..400 {
            let ExprNode::LetE { body, .. } = current.node() else {
                panic!("expected a let spine of length 400");
            };
            current = body;
        }
        assert!(
            matches!(current.node(), ExprNode::BVar { idx } if *idx == 0),
            "the last name is the innermost binder"
        );
    }
}
