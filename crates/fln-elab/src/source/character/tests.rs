use super::*;
use fln_core::expr::NatLit;
use fln_env::constants::AxiomVal;
use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_syntax::source::SourceInfo;

fn n(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn c(label: &str) -> Expr {
    Expr::const_(n(label), vec![])
}

fn number(value: u32) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(u64::from(value))))
}

fn arrow(domain: Expr, codomain: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, codomain, BinderInfo::Default)
}

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn publish(environment: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(environment, declaration, budget()) else {
        panic!("the typechecking fixture must have an admission answer");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("the typechecking fixture must pass the kernel");
    };
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
            result.environment
        }
        Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
        other => panic!("typechecking fixture publication: {other:?}"),
    }
}

fn signature(environment: &Environment, name: Name, type_: Expr) -> Environment {
    publish(
        environment,
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name,
                level_params: vec![],
                type_,
            },
            is_unsafe: false,
        }),
    )
}

fn fixture(with_function: bool) -> Environment {
    // These signatures isolate frontend typing and name resolution. They are
    // not runtime Char models or a claim of imported Prelude admission.
    let environment = crate::seed::bootstrap_nat_environment(budget()).unwrap();
    let environment = signature(&environment, n("Char"), Expr::sort(Level::one()));
    if with_function {
        signature(&environment, n("Char.ofNat"), arrow(c("Nat"), c("Char")))
    } else {
        environment
    }
}

fn literal(spelling: &str) -> Syntax {
    Syntax::node(n("char"), vec![Syntax::atom(SourceInfo::None, spelling)])
}

fn expected(character: char) -> Expr {
    Expr::app(c("Char.ofNat"), number(u32::from(character)))
}

#[test]
fn character_decoding_preserves_unicode_and_the_pins_escape_rules() {
    for (spelling, character) in [
        ("'a'", 'a'),
        ("'λ'", 'λ'),
        ("'🙂'", '🙂'),
        ("'\u{10ffff}'", '\u{10ffff}'),
        ("'\\n'", '\n'),
        ("'\\r'", '\r'),
        ("'\\t'", '\t'),
        ("'\\\\'", '\\'),
        ("'\\\''", '\''),
        ("'\\\"'", '"'),
        ("'\"'", '"'),
        ("'\\x00'", '\0'),
        ("'\\xFF'", '\u{ff}'),
        ("'\\u2665'", '♥'),
        ("'\\uD7FF'", '\u{d7ff}'),
        ("'\\uD800'", '\0'),
        ("'\\uDFFF'", '\0'),
        ("'\\uE000'", '\u{e000}'),
    ] {
        assert_eq!(decode_character(spelling).unwrap(), character, "{spelling}");
    }
    for spelling in [
        "",
        "a",
        "''",
        "'''",
        "'ab'",
        "'❤️'",
        "'a",
        "'a' trailing",
        "'\\0'",
        "'\\b'",
        "'\\f'",
        "'\\a'",
        "'\\U0001F642'",
        "'\\u{1F642}'",
        "'\\x0'",
        "'\\xGG'",
        "'\\u123'",
        "'\\u12GG'",
        "'\\uD800\\uDC00'",
        "'\\\n  a'",
        "\"a\"",
        "r\"a\"",
    ] {
        assert_eq!(decode_character(spelling), Err(invalid()), "{spelling}");
    }
}

#[test]
fn character_source_builds_a_checked_global_application_to_a_raw_natural() {
    let environment = fixture(true);
    let before = environment.len();
    for (spelling, character) in [
        ("'a'", 'a'),
        ("'λ'", 'λ'),
        ("'🙂'", '🙂'),
        ("'\\n'", '\n'),
        ("'\\x00'", '\0'),
        ("'\\uD800'", '\0'),
        ("'\\uDFFF'", '\0'),
    ] {
        for source in [
            format!("def value := {spelling}"),
            format!("def value : Char := ((({spelling})))"),
        ] {
            let checked = crate::check_definition_source(source.as_bytes(), &environment, budget())
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            assert!(matches!(
                checked.outcome,
                Outcome::Complete(Verdict::Accepted { .. })
            ));
            let Declaration::Defn(value) = checked.declaration else {
                panic!("a checked character definition");
            };
            assert_eq!(value.base.type_, c("Char"));
            assert_eq!(value.value, expected(character), "{source}");
            assert!(!value.value.has_expr_mvar());
            assert!(!value.value.has_fvar());
        }
    }
    assert!(matches!(
        crate::check_definition_source(b"def wrong : Nat := 'a'", &environment, budget()),
        Err(crate::DefinitionFrontendError::Elaborate(
            NatDefinitionElabError::Inference(SourceInferenceError::TypeMismatch { .. })
        ))
    ));
    assert_eq!(environment.len(), before);
}

fn with_zero_numerals(mut environment: Environment) -> Environment {
    for declaration in crate::instances::numeric::declarations()
        .unwrap()
        .declarations
    {
        match declaration {
            Declaration::Inductive(block) if block.types[0].base.name == n("OfNat") => {
                environment = publish(&environment, Declaration::Inductive(block));
            }
            Declaration::Defn(value) if value.base.name == n("OfNat.ofNat") => {
                environment = publish(&environment, Declaration::Defn(value));
            }
            Declaration::Defn(mut value) if value.base.name == n("instOfNatNat") => {
                let body = [c("Nat"), Expr::bvar(0).unwrap(), number(0)]
                    .into_iter()
                    .fold(Expr::const_(n("OfNat.mk"), vec![Level::zero()]), Expr::app);
                value.value = Expr::lam(n("n"), c("Nat"), body, BinderInfo::Default);
                environment = publish(&environment, Declaration::Defn(value));
            }
            _ => {}
        }
    }
    let environment = crate::instances::register_class(&environment, &n("OfNat")).unwrap();
    crate::instances::register_instance(&environment, &n("instOfNatNat"), 1000).unwrap()
}

#[test]
fn character_hygiene_and_raw_payload_survive_shadowing_and_changed_of_nat() {
    let environment = with_zero_numerals(fixture(true));
    let environment = signature(
        &environment,
        n("Shadow.Char.ofNat"),
        arrow(c("Nat"), c("Nat")),
    );
    let environment = signature(
        &environment,
        Name::from_components(["Char.ofNat"]),
        arrow(c("Nat"), c("Nat")),
    );
    let mut context = Context::new(&environment, budget());
    context.source_scope.namespace = n("Shadow");
    context.source_scope.opened.push(n("Shadow"));
    context.txn.lctx.add_param(
        FVarId(n("localCharOfNat")),
        n("Char.ofNat"),
        arrow(c("Nat"), c("Nat")),
        BinderInfo::Default,
    );
    let numeral = Syntax::node(n("num"), vec![Syntax::atom(SourceInfo::None, "97")]);
    let numeral = context.term(&numeral, Some(c("Nat"))).unwrap();
    let numeral = context.finish(numeral).unwrap();
    assert_eq!(
        context.whnf(&numeral.value).unwrap(),
        number(0),
        "the control actually selects the changed OfNat instance"
    );
    let character = context.term(&literal("'a'"), Some(c("Char"))).unwrap();
    let character = context.finish(character).unwrap();
    assert_eq!(character.value, expected('a'));
    assert_eq!(character.type_, c("Char"));

    let parsed =
        crate::parse_definition("def value (Char : Type) : _root_.Char := 'λ'".as_bytes()).unwrap();
    let scope = SourceScope {
        namespace: n("Shadow"),
        ..SourceScope::default()
    };
    let declaration = crate::elaborate_definition_in_scope_with_budget(
        parsed.syntax(),
        &environment,
        budget(),
        &scope,
    )
    .unwrap();
    assert!(matches!(
        check(&environment, &declaration, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    let Declaration::Defn(value) = declaration else {
        panic!("scoped character definition");
    };
    let ExprNode::Lam { body, .. } = value.value.node() else {
        panic!("the local Char binder remains in the declaration");
    };
    assert_eq!(body, &expected('λ'));
}

#[test]
fn malformed_character_trees_missing_globals_and_resource_stops_are_refused() {
    let environment = fixture(true);
    for syntax in [
        Syntax::node(n("char"), vec![]),
        Syntax::node(n("char"), vec![literal("'a'")]),
        Syntax::node(
            n("char"),
            vec![Syntax::atom(SourceInfo::None, "'a'"), literal("'b'")],
        ),
        literal("'a' extra"),
        literal("'ab'"),
    ] {
        assert!(matches!(
            Context::new(&environment, budget()).character_literal(&syntax),
            Err(NatDefinitionElabError::UnexpectedSyntax { .. })
        ));
    }
    let missing = signature(
        &fixture(false),
        Name::from_components(["Char.ofNat"]),
        arrow(c("Nat"), c("Char")),
    );
    assert!(matches!(
        Context::new(&missing, budget()).character_literal(&literal("'a'")),
        Err(NatDefinitionElabError::Inference(SourceInferenceError::UnknownConstant(name)))
            if name == n("Char.ofNat")
    ));
    let wrong_domain = signature(
        &fixture(false),
        n("Char.ofNat"),
        arrow(c("Char"), c("Char")),
    );
    assert!(
        Context::new(&wrong_domain, budget())
            .character_literal(&literal("'a'"))
            .is_err()
    );
    let mut limited = Context::new(&environment, budget());
    // Zero disables this transaction limit; one heartbeat cannot scan even
    // the complete quoted token, so the second byte must stop elaboration.
    limited.txn.budget.max_heartbeats = 1;
    assert!(matches!(
        limited.character_literal(&literal("'🙂'")),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::ResourceLimit
        ))
    ));
}
