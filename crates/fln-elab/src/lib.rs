//! **fln-elab** — Athanor — the elaborator: the monadic tower, the unifier's
//! approximation ladder, Synod (the instance engine), match compilation, the
//! native tactic framework, the Mirror façade registry, and the deterministic
//! dataflow scheduler (plan §10, §4.3).
//!
//! The full tower is not present yet. Bead `fln-5720` establishes its first
//! end-to-end production seam: one parsed
//! `def <ident> := <natural-literal-or-ident>` becomes a real
//! [`Declaration::Defn`] and is handed to Crucible's sole check authority. This
//! is a subset of the final abstraction, not a substitute for unification,
//! expected-type propagation, transactions, macros, instances, or tactics.
//! Unsupported source is refused by an explicit variant.

#![forbid(unsafe_code)]

pub mod seed;

use fln_bignum::interop::literal_from_bignat;
use fln_bignum::nat::BigNat;
use fln_core::expr::{Expr, Literal};
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
/// This first slice has no expected-type input, so both a natural literal and a
/// single constant reference synthesize `Nat` directly. The caller's
/// environment must already contain those constants; the kernel, not this
/// function, determines whether the resulting declaration is admissible.
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
        "absent declaration signature",
    )?;
    for part in signature {
        expect_empty_null(part, "absent declaration signature component")?;
    }

    let value = expect_node(
        &definition[3],
        &parser_kind(&["Command", "declValSimple"]),
        4,
        "Lean.Parser.Command.declValSimple",
    )?;
    expect_atom(&value[0], ":=", "definition assignment")?;
    let expression = match &value[1] {
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
        Syntax::Ident { val: name, .. } => {
            if name.is_anonymous() {
                return Err(NatDefinitionElabError::AnonymousReferenceName);
            }
            Expr::const_(name.clone(), Vec::new())
        }
        _ => {
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "natural literal or constant identifier",
            });
        }
    };

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
    Ok(Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_: Expr::const_(nat, Vec::new()),
        },
        value: expression,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![name],
    }))
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
        for malformed in ["", "_1", "1_", "0x", "0x1_", "0b2"] {
            assert_eq!(
                decode_natural(malformed),
                Err(NatDefinitionElabError::InvalidNaturalLiteral)
            );
        }
    }
}
