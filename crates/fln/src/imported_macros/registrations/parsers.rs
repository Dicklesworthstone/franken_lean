//! Parser ownership and resource regressions on the production registry.
//! Codec envelopes and import markers here are synthetic boundary inputs;
//! installed source tests separately supply real council and Reference evidence.
use super::*;

fn token_journal(token: &str) -> Vec<OpaqueExtensionBlock> {
    let row = Obj::mk_ctor(wire::PARSER_ENTRY_TOKEN, vec![Obj::mk_string(token)], &[]);
    vec![OpaqueExtensionBlock {
        name: parsers::extension_name(),
        entries: vec![compact(&Obj::mk_ctor(wire::SCOPE_GLOBAL, vec![row], &[]), 0).unwrap()],
    }]
}

#[test]
fn token_only_journals_follow_import_order_and_require_their_module_world() {
    let a = checked("A", &[], &[]);
    let b = checked("B", &[], &["A"]);
    let c = checked("C", &[], &[]);
    let a_rows = token_journal("a%");
    let b_rows = token_journal("b%");
    let c_rows = token_journal("c%");
    let admitted = environment(&[&a, &b, &c]);
    let registry = RegisteredParsers::prepare(
        &[
            ParserRegistrationModule {
                checked: &a,
                extensions: &a_rows,
            },
            ParserRegistrationModule {
                checked: &b,
                extensions: &b_rows,
            },
            ParserRegistrationModule {
                checked: &c,
                extensions: &c_rows,
            },
        ],
        &admitted,
        ParserRegistryLimits::default(),
    )
    .unwrap();
    let order = [name("C"), name("A"), name("B")];
    let engine = projected_engine(admitted.clone(), &order);
    let syntax = registry.project_imports(&order, &engine).unwrap();
    let tokens: Vec<_> = syntax
        .entries
        .iter()
        .map(|entry| {
            let ImportedSyntaxEntry::Token { scope, token } = entry else {
                panic!("{entry:?}")
            };
            assert!(scope.is_none());
            token.as_str()
        })
        .collect();
    assert_eq!(tokens, ["c%", "a%", "b%"]);
    let sibling = registry.project_imports(&[name("C")], &engine).unwrap();
    assert_eq!(sibling.entries.len(), 1);
    assert!(matches!(
        registry.project_imports(&[name("B")], &engine),
        Err(ParserRegistrationError::MissingImport { .. })
    ));
    assert!(matches!(
        registry.project_imports(&[name("B"), name("A")], &engine),
        Err(ParserRegistrationError::MissingImport { .. })
    ));
    let absent = projected_engine(admitted, &[]);
    assert!(matches!(
        registry.project_imports(&[name("C")], &absent),
        Err(ParserRegistrationError::Owner { .. })
    ));
}

fn rule(value: Expr) -> CheckedOleanModule {
    checked(
        "Library",
        &[definition("Library.rule", "Lean.ParserDescr", value)],
        &[],
    )
}

fn literal_rule(flag: bool) -> Expr {
    node(
        "Library.syntax",
        app(
            "Lean.ParserDescr.nonReservedSymbol",
            [text("@@"), c(if flag { "Bool.true" } else { "Bool.false" })],
        ),
    )
}

#[test]
fn literal_booleans_and_resource_stops_use_the_authoritative_data_reader() {
    for flag in [false, true] {
        let module = rule(literal_rule(flag));
        let rows = journal("Library.rule", "Library.syntax");
        let inputs = [ParserRegistrationModule {
            checked: &module,
            extensions: &rows,
        }];
        let admitted = environment(&[&module]);
        let registry =
            RegisteredParsers::prepare(&inputs, &admitted, ParserRegistryLimits::default())
                .unwrap();
        let order = [name("Library")];
        let syntax = registry
            .project_imports(&order, &projected_engine(admitted.clone(), &order))
            .unwrap();
        let descr = syntax
            .entries
            .iter()
            .find_map(|entry| match entry {
                ImportedSyntaxEntry::Parser(declaration) => Some(&declaration.descr),
                _ => None,
            })
            .unwrap();
        assert_eq!(
            *descr,
            Descr::Node {
                kind: name("Library.syntax"),
                prec: 1022,
                body: Box::new(Descr::NonReservedSymbol("@@".into(), flag)),
            }
        );
        for limits in [
            ParserRegistryLimits {
                max_steps: 0,
                ..ParserRegistryLimits::default()
            },
            ParserRegistryLimits {
                max_bytes: 0,
                ..ParserRegistryLimits::default()
            },
        ] {
            let error = RegisteredParsers::prepare(&inputs, &admitted, limits).unwrap_err();
            assert!(error.is_resource(), "{error:?}");
        }
    }
}

#[test]
fn surplus_constructor_fields_and_changed_projected_owners_are_refused() {
    let value = literal_rule(true);
    let valid = rule(value.clone());
    let rows = journal("Library.rule", "Library.syntax");
    let admitted = environment(&[&valid]);
    let registry = RegisteredParsers::prepare(
        &[ParserRegistrationModule {
            checked: &valid,
            extensions: &rows,
        }],
        &admitted,
        ParserRegistryLimits::default(),
    )
    .unwrap();
    let order = [name("Library")];
    registry
        .project_imports(&order, &projected_engine(admitted, &order))
        .unwrap();
    let changed = rule(literal_rule(false));
    assert!(matches!(
        registry.project_imports(&order, &projected_engine(environment(&[&changed]), &order)),
        Err(ParserRegistrationError::Owner { .. })
    ));
    let surplus = rule(Expr::app(value, number(99)));
    let error = RegisteredParsers::prepare(
        &[ParserRegistrationModule {
            checked: &surplus,
            extensions: &rows,
        }],
        &environment(&[&surplus]),
        ParserRegistryLimits::default(),
    )
    .unwrap_err();
    assert!(
        matches!(error, ParserRegistrationError::Description { .. }),
        "{error:?}"
    );
}
