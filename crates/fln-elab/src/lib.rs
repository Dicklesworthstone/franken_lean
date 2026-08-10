//! **fln-elab** — Athanor — the elaborator: the monadic tower, the unifier's
//! approximation ladder, Synod (the instance engine), match compilation, the
//! native tactic framework, the Mirror façade registry, and the deterministic
//! dataflow scheduler (plan §10, §4.3).
//!
//! The full tower is not present yet. Bead `fln-5720` establishes its first
//! end-to-end production seam: one parsed
//! bounded Nat definition, explicit first-order `Nat` function, application, or
//! local let becomes a real [`Declaration::Defn`] and is handed to Crucible's
//! sole check authority.
//! This is a subset of the final abstraction, not a substitute for unification,
//! expected-type propagation, transactions, macros, instances, or tactics.
//! Unsupported source is refused by an explicit variant.

#![forbid(unsafe_code)]

pub mod seed;

use fln_bignum::interop::literal_from_bignat;
use fln_bignum::nat::BigNat;
use fln_core::expr::{BinderInfo, Expr, Literal};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};
use fln_parse::{NatDefinitionParseError, ParsedNatDefinition, parse_nat_definition};
use fln_syntax::tree::Syntax;

/// Why the first elaboration subset refused an otherwise parsed tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatDefinitionElabError {
    UnexpectedSyntax { expected: &'static str },
    AnonymousDeclarationName,
    AnonymousReferenceName,
    InvalidNaturalLiteral,
    TooManyParameters,
}

/// A source-to-elaboration failure. Kernel rejections and non-answers are not
/// collapsed into this type; they remain in [`NatDefinitionCheck::outcome`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatDefinitionFrontendError {
    Parse(NatDefinitionParseError),
    Elaborate(NatDefinitionElabError),
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
        if parameter_type != &Name::from_components(["Nat"]) {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "Nat parameter type",
            });
        }
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
            parameters.push(parameter.clone());
        }
    }
    let result_type = expect_null_args(&signature[1], "optional explicit result type")?;
    match result_type {
        [] => {}
        [result_type] => {
            let parts = expect_node(
                result_type,
                &parser_kind(&["Term", "typeSpec"]),
                2,
                "Lean.Parser.Term.typeSpec",
            )?;
            expect_atom(&parts[0], ":", "explicit result type ascription")?;
            let Syntax::Ident {
                val: result_type, ..
            } = &parts[1]
            else {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "Nat result type",
                });
            };
            if result_type != &Name::from_components(["Nat"]) {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "Nat result type",
                });
            }
        }
        _ => {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "optional explicit result type",
            });
        }
    }

    let value = expect_node(
        &definition[3],
        &parser_kind(&["Command", "declValSimple"]),
        4,
        "Lean.Parser.Command.declValSimple",
    )?;
    expect_atom(&value[0], ":=", "definition assignment")?;
    let mut expression = elaborate_nat_term(&value[1], &parameters)?;

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
    let nat = Name::str(Name::anonymous(), "Nat");
    let nat_type = Expr::const_(nat, Vec::new());
    let mut declaration_type = nat_type.clone();
    for parameter in parameters.iter().rev() {
        declaration_type = Expr::forall_e(
            parameter.clone(),
            nat_type.clone(),
            declaration_type,
            BinderInfo::Default,
        );
        expression = Expr::lam(
            parameter.clone(),
            nat_type.clone(),
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
    parameters: &[Name],
) -> Result<Expr, NatDefinitionElabError> {
    if name.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousReferenceName);
    }
    if let Some(index) = parameters
        .iter()
        .rev()
        .position(|parameter| parameter == name)
    {
        let index = u32::try_from(index).map_err(|_| NatDefinitionElabError::TooManyParameters)?;
        return Expr::bvar(index).map_err(|_| NatDefinitionElabError::TooManyParameters);
    }
    Ok(Expr::const_(name.clone(), Vec::new()))
}

fn elaborate_nat_atom(
    syntax: &Syntax,
    parameters: &[Name],
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
        Syntax::Ident { val: name, .. } => elaborate_nat_reference(name, parameters)?,
        _ => {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "natural literal or constant identifier",
            });
        }
    })
}

fn elaborate_nat_term(
    syntax: &Syntax,
    parameters: &[Name],
) -> Result<Expr, NatDefinitionElabError> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return elaborate_nat_atom(syntax, parameters);
    };
    if kind == &parser_kind(&["Term", "let"]) {
        return elaborate_nat_let(args, parameters);
    }
    if kind != &parser_kind(&["Term", "app"]) {
        return elaborate_nat_atom(syntax, parameters);
    }
    if args.len() != 2 {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "Lean.Parser.Term.app",
        });
    }
    let Syntax::Ident { val: function, .. } = &args[0] else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "application function identifier",
        });
    };
    if function.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousReferenceName);
    }
    let Syntax::Node {
        kind: argument_kind,
        args: arguments,
        ..
    } = &args[1]
    else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "nonempty application argument array",
        });
    };
    if argument_kind != &Name::str(Name::anonymous(), "null") || arguments.is_empty() {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "nonempty application argument array",
        });
    }

    let mut expression = elaborate_nat_reference(function, parameters)?;
    for argument in arguments {
        expression = Expr::app(expression, elaborate_nat_atom(argument, parameters)?);
    }
    Ok(expression)
}

fn elaborate_nat_let(
    parts: &[Syntax],
    parameters: &[Name],
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
    expect_empty_null(&declaration[2], "absent explicit let type")?;
    expect_atom(&declaration[3], ":=", "let assignment")?;
    let value = elaborate_nat_term(&declaration[4], parameters)?;
    expect_atom(separator, ";", "let body separator")?;

    let mut body_parameters = parameters.to_vec();
    body_parameters.push(local_name.clone());
    let body = elaborate_nat_term(body, &body_parameters)?;
    Ok(Expr::let_e(
        local_name.clone(),
        Expr::const_(Name::from_components(["Nat"]), Vec::new()),
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
    let declaration = elaborate_nat_definition(parsed.syntax())?;
    let outcome = check(environment, &declaration, budget);
    Ok(NatDefinitionCheck {
        parsed,
        declaration,
        outcome,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::{ExprNode, NatLit};
    use fln_kernel::verdict::RejectClass;
    use seed::bootstrap_nat_environment;

    fn nat_environment() -> Environment {
        bootstrap_nat_environment(Budget::DEFAULT).expect("the small Nat fixture must publish")
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
    fn source_let_becomes_a_nat_typed_core_let_expression() {
        let result = check_nat_definition_source(
            b"def answer : Nat := let x := 41; x",
            &nat_environment(),
            Budget::DEFAULT,
        )
        .expect("the bounded Nat let grammar elaborates");
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
                nat,
                Expr::lit(Literal::Nat(NatLit::from_u64(41))),
                Expr::bvar(0).expect("one local binder fits the expression covenant"),
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
            elaborate_nat_term(
                &Syntax::node(parser_kind(&["Term", "app"]), Vec::new()),
                &[],
            ),
            Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "Lean.Parser.Term.app"
            })
        ));
        for malformed in ["", "_1", "1_", "0x", "0x1_", "0b2"] {
            assert_eq!(
                decode_natural(malformed),
                Err(NatDefinitionElabError::InvalidNaturalLiteral)
            );
        }
    }
}
