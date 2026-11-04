//! Quoted parentheses retain hygiene identities; only matching cdots bind.
//! Actual imported quotation execution is covered by source_imported_atomic_macros.
#![forbid(unsafe_code)]

use fln_core::{name::Name, outcome::Outcome};
use fln_elab::{
    NatDefinitionElabError, elaborate_definition_in_scope_with_budget,
    source::{SourceInferenceError, scope::SourceScope},
};
use fln_env::{
    constants::DefinitionVal,
    environment::{DeclarationBudget, DeclarationCommitted, Environment},
    pmap::CollisionBudget,
};
use fln_kernel::{
    Declaration,
    capability::{Published, admit},
    council::{Council, CouncilOutcome, convene},
    verdict::{Budget, Verdict},
};
use fln_syntax::{hygiene::add_macro_scope, source::SourceInfo, tree::Syntax};

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn environment() -> Environment {
    let mut environment = Environment::new();
    for declaration in fln_elab::seed::source_seed_declarations_iter() {
        let Outcome::Complete(admitted) = admit(&environment, declaration, budget()) else {
            panic!("seed admission did not complete")
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("seed declaration was refused")
        };
        environment = match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
                result.environment
            }
            Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
            other => panic!("seed publication: {other:?}"),
        };
    }
    environment
}

fn parsed(source: &str) -> Syntax {
    fln_parse::parse_definition(source.as_bytes())
        .unwrap()
        .syntax()
        .clone()
}

fn scope(serial: u64) -> Name {
    add_macro_scope(
        &Name::from_components(["ImportedQuotation"]),
        &Name::anonymous(),
        serial,
    )
    .unwrap()
}

fn map_hygiene(syntax: &mut Syntax, f: &mut impl FnMut(&mut Syntax)) -> usize {
    let Syntax::Node { kind, args, .. } = syntax else {
        return 0;
    };
    if *kind == Name::from_components(["hygieneInfo"]) {
        let [identifier] = args.as_mut_slice() else {
            panic!("parsed hygiene information")
        };
        f(identifier);
        1
    } else {
        args.iter_mut().map(|arg| map_hygiene(arg, f)).sum()
    }
}

fn quoted(source: &str) -> Syntax {
    let mut syntax = parsed(source);
    assert!(
        map_hygiene(&mut syntax, &mut |identifier| {
            let Syntax::Ident { val, .. } = identifier else {
                panic!("parsed hygiene identifier")
            };
            *val = scope(7);
        }) > 0
    );
    syntax
}

fn elaborate(
    syntax: &Syntax,
    environment: &Environment,
) -> Result<Declaration, NatDefinitionElabError> {
    elaborate_definition_in_scope_with_budget(
        syntax,
        environment,
        budget(),
        &SourceScope::default(),
    )
}

fn checked(syntax: &Syntax, environment: &Environment) -> DefinitionVal {
    let declaration = elaborate(syntax, environment).unwrap();
    assert!(matches!(
        fln_kernel::check(environment, &declaration, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    let Declaration::Defn(value) = declaration else {
        panic!("expected a definition")
    };
    value
}

#[test]
fn quoted_parentheses_keep_scoped_hygiene_identifiers() {
    let environment = environment();
    for source in [
        "def nested (n : Nat) : Nat := Nat.succ ((n))",
        "def expected : (Nat) := ((Nat.zero))",
    ] {
        let plain = checked(&parsed(source), &environment);
        let quoted = checked(&quoted(source), &environment);
        assert_eq!(quoted.base.type_, plain.base.type_);
        assert_eq!(quoted.value, plain.value);
    }
}

#[test]
fn quoted_cdots_match_parenthesis_and_ascription_hygiene() {
    let environment = environment();
    for source in [
        "def scopedFunction : Nat → Nat := (Nat.succ ·)",
        "def scopedFunction := (Nat.succ · : Nat → Nat)",
        "def scopedFunction : Nat → Nat := ((Nat.succ ·))",
    ] {
        let plain = checked(&parsed(source), &environment);
        let quoted = checked(&quoted(source), &environment);
        assert_eq!(quoted.base.type_, plain.base.type_);
        assert_eq!(quoted.value, plain.value);
    }
}

#[test]
fn cdots_from_other_quotation_scopes_are_not_captured() {
    let environment = environment();
    assert_eq!(scope(7).erase_macro_scopes(), scope(8).erase_macro_scopes());
    for (source, scopes) in [
        ("def bad : Nat → Nat := (Nat.succ ·)", vec![7, 8]),
        ("def bad := (Nat.succ · : Nat → Nat)", vec![7, 8]),
        // An outer scope cannot reach through a different inner parenthesis.
        ("def bad : Nat → Nat := ((Nat.succ ·))", vec![7, 8, 7]),
    ] {
        let mut syntax = parsed(source);
        let mut scopes = scopes.into_iter();
        map_hygiene(&mut syntax, &mut |identifier| {
            let Syntax::Ident { val, .. } = identifier else {
                panic!("parsed hygiene identifier")
            };
            *val = scope(scopes.next().unwrap());
        });
        assert!(scopes.next().is_none());
        assert!(matches!(
            elaborate(&syntax, &environment),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::CdotOutsideParentheses
            ))
        ));
    }
}

#[test]
fn malformed_hygiene_and_invalid_witnesses_remain_refused() {
    let environment = environment();
    for source in ["def malformed : Nat := (0)", "def malformed : Nat := ((0))"] {
        let mut syntax = parsed(source);
        map_hygiene(&mut syntax, &mut |identifier| {
            *identifier = Syntax::atom(SourceInfo::None, "not an identifier");
        });
        assert!(matches!(
            elaborate(&syntax, &environment),
            Err(NatDefinitionElabError::UnexpectedSyntax { .. })
        ));
    }
    for source in [
        "def wrongType : Bool := (Nat.zero)",
        "theorem falseProof : Eq (Nat.succ Nat.zero) Nat.zero := Eq.refl Nat.zero",
    ] {
        assert!(
            elaborate(&quoted(source), &environment).is_err(),
            "{source}"
        );
    }
}

#[test]
fn native_ascriptions_without_cdots_do_not_require_a_hygienic_opener() {
    fn bare_openers(syntax: &mut Syntax) -> usize {
        let Syntax::Node { kind, args, .. } = syntax else {
            return 0;
        };
        let own = if *kind == Name::from_components(["Lean", "Parser", "Term", "typeAscription"]) {
            args[0] = Syntax::atom(SourceInfo::None, "(");
            1
        } else {
            0
        };
        own + args.iter_mut().map(bare_openers).sum::<usize>()
    }

    let environment = environment();
    for source in [
        "def generatedAscription : Nat := (Nat.zero : Nat)",
        "def generatedAscription : Nat → Nat := ((Nat.succ ·) : Nat → Nat)",
    ] {
        let plain = checked(&parsed(source), &environment);
        let mut native = parsed(source);
        assert!(bare_openers(&mut native) > 0);
        let native = checked(&native, &environment);
        assert_eq!(native.base.type_, plain.base.type_);
        assert_eq!(native.value, plain.value);
    }
}
