use super::*;

fn variable() -> Name {
    macro_variable(&Name::from_components(["xs"]))
}

fn variables() -> Vec<(Vec<usize>, Name)> {
    vec![(vec![0], variable())]
}

fn template(family: &str, suffix: &str) -> Syntax {
    null_node(vec![Syntax::node(
        Name::from_components([family, "antiquot_scope"]),
        vec![
            null_node(vec![Syntax::node(
                Name::from_components(["body"]),
                vec![synthetic_ident(variable())],
            )]),
            Syntax::atom(SourceInfo::None, suffix),
        ],
    )])
}

fn capture(family: &str, suffix: &str) -> Syntax {
    null_node(vec![Syntax::node(
        Name::from_components([family, "antiquot_suffix_splice"]),
        vec![
            Syntax::node(
                Name::from_components(["term", "antiquot"]),
                vec![
                    Syntax::atom(SourceInfo::None, "$"),
                    null_node(vec![]),
                    synthetic_ident(Name::from_components(["xs"])),
                    null_node(vec![]),
                ],
            ),
            Syntax::atom(SourceInfo::None, suffix),
        ],
    )])
}

fn rule(rhs: Syntax, pattern: Option<Syntax>) -> NotationRule {
    NotationRule {
        variables: variables(),
        rhs,
        prechecked: false,
        pattern,
        source: None,
        starts_registration: true,
        fallbacks: Vec::new(),
    }
}

#[test]
fn direct_macro_types_distinguish_options_arrays_and_scalars() {
    let term = StxItem::Cat(Name::from_components(["term"]), None);
    let cases = [
        (
            StxItem::Postfix("?".to_owned(), Box::new(term.clone())),
            "optional",
            "?",
        ),
        (
            StxItem::Postfix("*".to_owned(), Box::new(term.clone())),
            "many",
            "*",
        ),
        (
            StxItem::Postfix(",*".to_owned(), Box::new(term.clone())),
            "sepBy",
            ",*",
        ),
    ];
    for (index, (item, family, suffix)) in cases.iter().enumerate() {
        let rhs = template(family, suffix);
        assert_eq!(
            direct(&rhs, &variables(), std::slice::from_ref(item)),
            Ok(())
        );
        let positioned =
            StxItem::Unary(Name::from_components(["withPosition"]), vec![item.clone()]);
        assert_eq!(direct(&rhs, &variables(), &[positioned]), Ok(()));
        for (other, (item, _, _)) in cases.iter().enumerate() {
            if index != other {
                assert_eq!(
                    direct(&rhs, &variables(), std::slice::from_ref(item)),
                    Err(INCOMPATIBLE_CAPTURE)
                );
            }
        }
        assert_eq!(
            direct(&rhs, &variables(), std::slice::from_ref(&term)),
            Err(INCOMPATIBLE_CAPTURE)
        );
    }
}

#[test]
fn pattern_types_reject_empty_and_singleton_array_as_an_option() {
    let pattern = Syntax::node(
        Name::from_components(["captureKindSyntax"]),
        vec![capture("many", "*")],
    );
    let rule = rule(template("optional", "?"), Some(pattern));
    for count in 0..=1 {
        let args = [null_node(vec![Syntax::Missing; count])];
        assert!(super::super::matches(&rule, &args).unwrap());
        assert_eq!(imported(&rule, None), Err(INCOMPATIBLE_CAPTURE));
    }
    let pattern = Syntax::node(
        Name::from_components(["captureKindSyntax"]),
        vec![capture("optional", "?")],
    );
    assert_eq!(
        imported(&rule_with_pattern(template("many", "*"), pattern), None),
        Err(INCOMPATIBLE_CAPTURE)
    );
}

fn rule_with_pattern(rhs: Syntax, pattern: Syntax) -> NotationRule {
    rule(rhs, Some(pattern))
}

#[test]
fn separated_arrays_require_the_same_framing_before_execution() {
    let children = [capture("sepBy", ";*")];
    assert_eq!(
        pattern(&template("sepBy", ";*"), &variables(), &children),
        Ok(())
    );
    assert_eq!(
        pattern(&template("sepBy", ",*"), &variables(), &children),
        Err(INCOMPATIBLE_CAPTURE)
    );
    assert_eq!(
        pattern(&template("many", "*"), &variables(), &children),
        Err(INCOMPATIBLE_CAPTURE)
    );
}

#[test]
fn malformed_native_capture_types_refuse_before_installing_anything() {
    let kind = Name::from_components(["captureKindSyntax"]);
    let mut module = NativeSyntaxModule::default();
    module
        .categories
        .insert(Name::from_components(["Fresh"]), IdentBehavior::Default);
    module.declarations.push(Arc::new(SyntaxDecl {
        module: Name::from_components(["Producer"]),
        decl: kind.clone(),
        category: Some(Name::from_components(["term"])),
        leading: true,
        priority: DEFAULT_PRIORITY,
        scope: None,
        descr: Descr::Node {
            kind: kind.clone(),
            prec: MAX_PREC,
            body: Box::new(Descr::Unary(
                Name::from_components(["many"]),
                Box::new(Descr::Cat(Name::from_components(["term"]), 0)),
            )),
        },
    }));
    let pattern = Syntax::node(kind.clone(), vec![capture("many", "*")]);
    module.rules.insert(
        kind.clone(),
        Arc::new(rule(template("optional", "?"), Some(pattern))),
    );
    let mut file = FileGrammar::new(false, &[], Some(Name::from_components(["Consumer"]))).unwrap();
    assert_eq!(file.import_native(&module), Err(INCOMPATIBLE_CAPTURE));
    assert!(!file.constants.contains(&kind));
    assert!(
        !file
            .categories
            .contains_key(&Name::from_components(["Fresh"]))
    );
    assert!(file.native_rule_counts.is_empty());

    // Direct macro journals have no quoted pattern. Their retained parser
    // description still proves that the input is an array, not an Option.
    Arc::make_mut(module.rules.get_mut(&kind).unwrap()).pattern = None;
    assert_eq!(file.import_native(&module), Err(INCOMPATIBLE_CAPTURE));
    Arc::make_mut(module.rules.get_mut(&kind).unwrap()).rhs = template("many", "*");
    file.import_native(&module).unwrap();
    assert!(file.constants.contains(&kind));
}

#[test]
fn validation_bounds_nested_descriptions_and_template_bodies() {
    let mut item = StxItem::Postfix(
        "?".to_owned(),
        Box::new(StxItem::Cat(Name::from_components(["term"]), None)),
    );
    for _ in 0..=MAX_DESCR_DEPTH {
        item = StxItem::Unary(Name::from_components(["withPosition"]), vec![item]);
    }
    let reason = direct(&template("optional", "?"), &variables(), &[item]).unwrap_err();
    assert_eq!(
        reason,
        "a quoted macro pattern past the node or depth budget"
    );
    assert!(registration_error(reason));
    let huge = null_node(vec![Syntax::Missing; MAX_TEMPLATE_NODES]);
    let reason = direct(&huge, &variables(), &[]).unwrap_err();
    assert_eq!(reason, "a macro template past the node budget");
    assert!(registration_error(reason));
}

#[test]
fn nested_splices_refuse_even_if_a_later_macro_would_discard_them() {
    for inner in [template("many", "*"), capture("many", "*")] {
        let rhs = null_node(vec![Syntax::node(
            Name::from_components(["optional", "antiquot_scope"]),
            vec![
                null_node(vec![Syntax::node(
                    Name::from_components(["discarded"]),
                    vec![inner],
                )]),
                Syntax::atom(SourceInfo::None, "?"),
            ],
        )]);
        assert_eq!(
            pattern(&rhs, &variables(), &[capture("optional", "?")]),
            Err(INCOMPATIBLE_CAPTURE)
        );
    }
}

#[test]
fn alternative_parser_arity_does_not_shift_later_optional_captures() {
    let alternative = Descr::Binary(
        Name::from_components(["orelse"]),
        Box::new(Descr::Symbol("left".to_owned())),
        Box::new(Descr::Symbol("right".to_owned())),
    );
    let descr = Descr::Node {
        kind: Name::from_components(["captureKindSyntax"]),
        prec: MAX_PREC,
        body: Box::new(Descr::Binary(
            Name::from_components(["andthen"]),
            Box::new(alternative),
            Box::new(Descr::Unary(
                Name::from_components(["optional"]),
                Box::new(Descr::Cat(Name::from_components(["term"]), 0)),
            )),
        )),
    };
    let mut rule = rule(template("optional", "?"), None);
    rule.variables[0].0 = vec![1];
    assert_eq!(imported(&rule, Some(&descr)), Ok(()));
    let incompatible = Descr::Binary(
        Name::from_components(["orelse"]),
        Box::new(Descr::Symbol("left".to_owned())),
        Box::new(Descr::Binary(
            Name::from_components(["andthen"]),
            Box::new(Descr::Symbol("right".to_owned())),
            Box::new(Descr::Symbol("extra".to_owned())),
        )),
    );
    assert_eq!(
        descriptor_slots(&incompatible, &mut Vec::new(), &mut 0, 0),
        Err(INCOMPATIBLE_CAPTURE)
    );
}
