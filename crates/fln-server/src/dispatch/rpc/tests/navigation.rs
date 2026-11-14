use super::*;

fn navigate(
    sessions: &mut Sessions,
    id: u64,
    kind: &str,
    reference: &str,
    docs: &DocumentSession,
    provider: &mut Provider,
) -> Result<String> {
    let call = format!(
        r#"{{"textDocument":{{"uri":"{URI}"}},"position":{{"line":0,"character":0}},"sessionId":"{id}","method":"Lean.Widget.getGoToLocation","params":{{"kind":"{kind}","info":{reference}}}}}"#
    );
    sessions.execute("$/lean/rpc/call", RawField::Value(&call), docs, provider)
}

fn info_reference(sessions: &Sessions, session: u64, subexpression: Option<usize>) -> u64 {
    sessions.sessions[&session]
        .references
        .iter()
        .find_map(|(id, reference)| {
            (reference.kind
                == ReferenceKind::Info(InfoAddress {
                    code: CodeAddress {
                        goal: 0,
                        field: CodeField::Target,
                    },
                    subexpression,
                }))
            .then_some(*id)
        })
        .unwrap()
}

#[test]
fn navigation_uses_retained_native_origins_and_distinguishes_type_from_definition() {
    let source = "-- 😀\r\ndef value : Token := Token.mk\r\n";
    let start = source.find("def").unwrap();
    let definition = semantic::NavigationLocation::new(
        "file:///Library.lean".into(),
        source,
        start..source.len() - 2,
        start + 4..start + 9,
    )
    .unwrap();
    let type_definition = semantic::NavigationLocation::new(
        "file:///Types.lean".into(),
        "inductive Token where | mk",
        0..26,
        10..15,
    )
    .unwrap();
    for format in [WireFormat::V0, WireFormat::V1] {
        let mut result = annotated_answer();
        let Answer::InteractiveGoals { goals } = &mut result else {
            unreachable!()
        };
        let info = goals[0].target.info.as_mut().unwrap();
        info.definition = Some(vec![definition.clone()]);
        info.type_definition = Some(vec![type_definition.clone()]);
        goals[0].target.subexpressions[1].info.definition = Some(Vec::new());
        let mut provider = Provider {
            result: Some(result),
            ..Provider::new()
        };
        let mut sessions = Sessions {
            format,
            ..Sessions::default()
        };
        let id = sessions.create(URI.into(), Instant::now()).unwrap();
        let mut docs = documents();
        execute(&mut sessions, id, &docs, &mut provider).unwrap();
        let root = info_reference(&sessions, id, None);
        let local = info_reference(&sessions, id, Some(1));
        let retained = (
            sessions.sessions[&id].references.len(),
            sessions.sessions[&id].bytes,
        );
        for kind in ["declaration", "definition", "type"] {
            let result = navigate(
                &mut sessions,
                id,
                kind,
                &format.reference(root),
                &docs,
                &mut provider,
            )
            .unwrap();
            let expected = if kind == "type" {
                &type_definition
            } else {
                &definition
            };
            assert_eq!(result, format!("[{}]", expected.wire()));
            assert!(!result.contains("originSelectionRange"));
        }
        assert_eq!(
            navigate(
                &mut sessions,
                id,
                "definition",
                &format.reference(local),
                &docs,
                &mut provider
            )
            .unwrap(),
            "[]"
        );
        assert!(matches!(
            navigate(
                &mut sessions,
                id,
                "type",
                &format.reference(local),
                &docs,
                &mut provider
            ),
            Err((-32803, _))
        ));
        docs.save_with_text(URI, "changed source".into()).unwrap();
        let old = navigate(
            &mut sessions,
            id,
            "definition",
            &format.reference(root),
            &docs,
            &mut provider,
        )
        .unwrap();
        assert!(old.contains(r#""start":{"line":1,"character":0}"#), "{old}");
        assert!(old.contains(r#""targetSelectionRange":{"start":{"line":1,"character":4},"end":{"line":1,"character":9}}"#), "{old}");
        assert_eq!(provider.calls, 1, "navigation must not re-elaborate");
        assert_eq!(
            (
                sessions.sessions[&id].references.len(),
                sessions.sessions[&id].bytes
            ),
            retained
        );
        sessions.sessions.get_mut(&id).unwrap().release(root);
        assert!(matches!(
            navigate(
                &mut sessions,
                id,
                "definition",
                &format.reference(root),
                &docs,
                &mut provider
            ),
            Err((-32602, _))
        ));
    }
}

#[test]
fn navigation_rejects_malformed_and_foreign_references_and_dead_sessions() {
    for format in [WireFormat::V0, WireFormat::V1] {
        let mut sessions = Sessions {
            format,
            ..Sessions::default()
        };
        let id = sessions.create(URI.into(), Instant::now()).unwrap();
        let docs = documents();
        let mut provider = Provider {
            result: Some(annotated_answer()),
            ..Provider::new()
        };
        execute(&mut sessions, id, &docs, &mut provider).unwrap();
        let root = info_reference(&sessions, id, None);
        let other_format = match format {
            WireFormat::V0 => WireFormat::V1,
            WireFormat::V1 => WireFormat::V0,
        };
        for reference in [
            format.reference(0),
            format.reference(u64::MAX),
            other_format.reference(root),
            format!(r#"{{"{}":{root}}}"#, format.key()),
            format!(
                r#"{{"{}":"{root}","{}":"{root}"}}"#,
                format.key(),
                format.key()
            ),
            r#"{"p":"1","__rpcref":"1"}"#.into(),
            "null".into(),
        ] {
            assert!(
                matches!(
                    navigate(
                        &mut sessions,
                        id,
                        "definition",
                        &reference,
                        &docs,
                        &mut provider
                    ),
                    Err((-32602, _))
                ),
                "{reference}"
            );
        }
        assert!(matches!(
            navigate(
                &mut sessions,
                id,
                "implementation",
                &format.reference(root),
                &docs,
                &mut provider
            ),
            Err((-32602, _))
        ));
        let foreign = sessions.create(URI.into(), Instant::now()).unwrap();
        assert!(matches!(
            navigate(
                &mut sessions,
                foreign,
                "definition",
                &format.reference(root),
                &docs,
                &mut provider
            ),
            Err((-32602, _))
        ));
        sessions.sessions.get_mut(&id).unwrap().expires = Instant::now();
        assert!(matches!(
            navigate(
                &mut sessions,
                id,
                "definition",
                &format.reference(root),
                &docs,
                &mut provider
            ),
            Err((RECONNECT, _))
        ));
        assert_eq!(provider.calls, 1);
    }
}

#[test]
fn navigation_metadata_cannot_evade_snapshot_payload_bounds() {
    let location =
        semantic::NavigationLocation::new("file:///T.lean".into(), "abc", 0..3, 0..1).unwrap();
    let mut result = annotated_answer();
    let Answer::InteractiveGoals { goals } = &mut result else {
        unreachable!()
    };
    goals[0].target.info.as_mut().unwrap().definition = Some(vec![location; 257]);
    let mut provider = Provider {
        result: Some(result),
        ..Provider::new()
    };
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    assert!(matches!(
        execute(&mut sessions, id, &documents(), &mut provider),
        Err((-32803, _))
    ));
    assert!(sessions.sessions[&id].references.is_empty());
    assert_eq!(sessions.sessions[&id].bytes, 0);
}
