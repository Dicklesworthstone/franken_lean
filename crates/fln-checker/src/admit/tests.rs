use super::*;
use crate::environment::ReducibilityHint;

fn name(text: &str) -> WireName {
    WireName::from_parts(vec![NamePart::Text(text.to_owned())])
}

fn sort(level: usize) -> WireExpr {
    WireExpr::from_parts(
        vec![ExprNode::Sort {
            level: LevelId::from_index(level).expect("fixture level index"),
        }],
        vec![
            LevelNode::Zero,
            LevelNode::Succ(LevelId::from_index(0).unwrap()),
        ],
        ExprId::from_index(0).unwrap(),
    )
}

fn definition(text: &str) -> ConstantEntry {
    ConstantEntry::new(
        name(text),
        ConstantDeclaration::definition(
            vec![name("u")],
            sort(1),
            ConstantSafety::Unsafe,
            DefinitionBody::new(
                sort(0),
                ReducibilityHint::Regular(1),
                DefinitionSafety::Unsafe,
                Vec::new(),
            ),
        ),
    )
}

fn base() -> ConstantEnvironment {
    let outcome =
        ConstantEnvironment::build(vec![definition("retained")], EnvironmentBudget::unlimited());
    let EnvironmentOutcome::Complete { environment, .. } = outcome else {
        panic!("valid independent-checker fixture: {outcome:?}");
    };
    environment
}

#[test]
fn peer_headers_retain_shared_base_and_exclude_self_and_peer_bodies() {
    let base = base();
    let block = [definition("current"), definition("peer")];
    let scoped = predeclare_peers(&base, &block, 0).expect("valid peer headers");
    assert!(std::ptr::eq(
        base.find(&name("retained")).unwrap(),
        scoped.find(&name("retained")).unwrap(),
    ));
    assert_eq!(scoped.len(), 2);
    assert!(scoped.find(&name("current")).is_none());
    let peer = scoped.find(&name("peer")).unwrap();
    let original = block[1].declaration();
    assert_eq!(peer.type_(), original.type_());
    assert_eq!(peer.level_parameters(), original.level_parameters());
    assert_eq!(peer.kind(), original.kind());
    assert_eq!(peer.safety(), original.safety());
    assert!(peer.body_value().is_none());
    assert!(peer.delta_body().is_none());
    assert!(base.find(&name("peer")).is_none());

    let singleton = predeclare_peers(&base, &block[..1], 0).unwrap();
    assert_eq!(singleton, base);
    assert!(std::ptr::eq(
        singleton.find(&name("retained")).unwrap(),
        base.find(&name("retained")).unwrap(),
    ));
}

#[test]
fn invalid_peer_headers_refuse_without_changing_the_validated_base() {
    let base = base();
    let before = base.clone();
    let malformed = ConstantEntry::new(
        name("malformed"),
        ConstantDeclaration::header(
            Vec::new(),
            WireExpr::from_parts(Vec::new(), Vec::new(), ExprId::from_index(0).unwrap()),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    for invalid in [malformed, definition("retained"), definition("peer")] {
        let block = [definition("current"), definition("peer"), invalid];
        assert!(predeclare_peers(&base, &block, 0).is_err());
        assert_eq!(base, before);
        assert_eq!(base.len(), 1);
        assert!(std::ptr::eq(
            base.find(&name("retained")).unwrap(),
            before.find(&name("retained")).unwrap(),
        ));
        assert!(base.find(&name("peer")).is_none());
    }
}
