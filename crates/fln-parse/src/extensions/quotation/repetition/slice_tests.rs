use super::*;

fn capture(name: &str) -> Syntax {
    Syntax::node(
        Name::from_components(["term", "pseudo", "antiquot"]),
        vec![
            Syntax::atom(SourceInfo::None, "$"),
            null_node(vec![]),
            synthetic_ident(Name::from_components([name])),
            null_node(vec![]),
        ],
    )
}
fn splice(name: &str) -> Syntax {
    Syntax::node(
        Name::from_components(["many", "antiquot_suffix_splice"]),
        vec![capture(name), Syntax::atom(SourceInfo::None, "*")],
    )
}
fn root(sequence: Syntax) -> Syntax {
    Syntax::node(Name::from_components(["testRoot"]), vec![sequence])
}

#[test]
fn suffix_bindings_remain_structural_for_every_middle_length() {
    let wrapper = |v| Syntax::node(Name::from_components(["wrapper"]), vec![v]);
    let sequence = null_node(vec![
        capture("first"),
        splice("xs"),
        wrapper(capture("last")),
    ]);
    let variables = variables(std::slice::from_ref(&sequence)).unwrap();
    assert_eq!(
        variables,
        vec![
            (vec![0], macro_variable(&Name::from_components(["xs"]))),
            (
                vec![0, 0],
                macro_variable(&Name::from_components(["first"]))
            ),
            (
                vec![0, 2, 0],
                macro_variable(&Name::from_components(["last"]))
            ),
        ]
    );
    let pattern = root(sequence);
    for length in 0..12 {
        let first = synthetic_ident(Name::from_components(["firstValue"]));
        let last = synthetic_ident(Name::from_components(["lastValue"]));
        let middle = vec![Syntax::Missing; length];
        let mut items = vec![first.clone()];
        items.extend(middle.clone());
        items.push(wrapper(last.clone()));
        let values = [null_node(items)];
        assert_eq!(
            resolve(Some(&pattern), &values, &[0], &mut 0)
                .unwrap()
                .as_ref(),
            &null_node(middle)
        );
        assert_eq!(
            resolve(Some(&pattern), &values, &[0, 0], &mut 0)
                .unwrap()
                .as_ref(),
            &first
        );
        assert_eq!(
            resolve(Some(&pattern), &values, &[0, 2, 0], &mut 0)
                .unwrap()
                .as_ref(),
            &last
        );
    }
}

#[test]
fn nested_slices_translate_each_suffix_at_its_own_level() {
    let pattern = root(null_node(vec![
        splice("xs"),
        null_node(vec![splice("ys"), capture("last")]),
    ]));
    let last = synthetic_ident(Name::from_components(["chosen"]));
    let inner = null_node(vec![Syntax::Missing, Syntax::Missing, last.clone()]);
    let values = [null_node(vec![
        Syntax::Missing,
        Syntax::Missing,
        Syntax::Missing,
        inner,
    ])];
    let outer = resolve(Some(&pattern), &values, &[0], &mut 0).unwrap();
    assert_eq!(outer.as_ref(), &null_node(vec![Syntax::Missing; 3]));
    let inner = resolve(Some(&pattern), &values, &[0, 1], &mut 0).unwrap();
    assert_eq!(inner.as_ref(), &null_node(vec![Syntax::Missing; 2]));
    assert_eq!(
        resolve(Some(&pattern), &values, &[0, 1, 1], &mut 0)
            .unwrap()
            .as_ref(),
        &last
    );
}

#[test]
fn malformed_paths_and_budget_stops_cannot_alias_another_capture() {
    let pattern = root(null_node(vec![
        capture("first"),
        splice("xs"),
        capture("last"),
    ]));
    let values = [null_node(vec![Syntax::Missing; 8])];
    for path in [
        vec![],
        vec![1],
        vec![0, 1],
        vec![0, 3],
        vec![0; MAX_DESCR_DEPTH + 1],
    ] {
        assert!(
            resolve(Some(&pattern), &values, &path, &mut 0).is_err(),
            "{path:?}"
        );
    }
    assert!(resolve(Some(&pattern), &[null_node(vec![])], &[0], &mut 0).is_err());
    let mut remaining = MAX_TEMPLATE_NODES - 1;
    assert!(resolve(Some(&pattern), &values, &[0, 2], &mut remaining).is_err());
    for _ in 0..2 {
        assert_eq!(
            resolve(Some(&pattern), &values, &[0, 2], &mut 0)
                .unwrap()
                .as_ref(),
            &Syntax::Missing
        );
    }
    let large = [null_node(vec![
        Syntax::Missing,
        Syntax::node(
            Name::from_components(["large"]),
            vec![Syntax::Missing; MAX_TEMPLATE_NODES],
        ),
        Syntax::Missing,
    ])];
    assert!(resolve(Some(&pattern), &large, &[0], &mut 0).is_err());
}

#[test]
fn separated_suffix_framing_is_checked_before_any_capture_is_registered() {
    let sep = Syntax::node(
        Name::from_components(["sepBy", "antiquot_suffix_splice"]),
        vec![capture("xs"), Syntax::atom(SourceInfo::None, ",*")],
    );
    for sequence in [
        null_node(vec![sep.clone(), capture("last")]),
        null_node(vec![
            sep.clone(),
            Syntax::atom(SourceInfo::None, ";"),
            capture("last"),
        ]),
        null_node(vec![sep.clone(), Syntax::atom(SourceInfo::None, ","), sep]),
    ] {
        assert!(slice(&sequence).is_err());
        assert!(variables(&[sequence]).is_err());
    }
}
