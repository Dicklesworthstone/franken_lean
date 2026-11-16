//! Deterministic state tests; installed-binary tests exercise native elaboration.
use super::*;
use semantic::{Goal, Hypothesis, TermGoal};
mod navigation;
const URI: &str = "file:///Rpc.lean";
fn answer(target: &str) -> Answer {
    Answer::InteractiveGoals {
        goals: vec![Goal {
            mvar_id: "_uniq.2".into(),
            user_name: Some("left".into()),
            hypotheses: vec![Hypothesis {
                name: "h".into(),
                fvar_id: "_uniq.1".into(),
                type_: "P".into(),
                value: None,
            }],
            target: target.into(),
        }],
    }
}
fn snapshot(target: &str) -> Arc<Snapshot> {
    let answer = answer(target);
    let bytes = semantic::interactive::payload_bytes(&answer).unwrap();
    Arc::new(Snapshot {
        version: 1,
        offset: 0,
        answer,
        bytes,
    })
}

fn annotated_answer() -> Answer {
    let mut result = answer("(f β)");
    let Answer::InteractiveGoals { goals } = &mut result else {
        unreachable!()
    };
    goals[0].target.info = Some(ExpressionInfo {
        type_: Some("P".into()),
        ..ExpressionInfo::default()
    });
    goals[0].target.subexpressions = vec![
        semantic::SubexpressionInfo {
            range: 1..2,
            position: 4,
            info: ExpressionInfo {
                type_: Some("P → P".into()),
                ..ExpressionInfo::default()
            },
        },
        semantic::SubexpressionInfo {
            range: 3..5,
            position: 5,
            info: ExpressionInfo {
                type_: Some("P".into()),
                ..ExpressionInfo::default()
            },
        },
    ];
    result
}

fn info_call(session: u64, reference: &str) -> String {
    format!(
        r#"{{"textDocument":{{"uri":"{URI}"}},"position":{{"line":0,"character":0}},"sessionId":"{session}","method":"Lean.Widget.InteractiveDiagnostics.infoToInteractive","params":{reference}}}"#
    )
}

fn popup(
    sessions: &mut Sessions,
    id: u64,
    reference: &str,
    docs: &DocumentSession,
    provider: &mut Provider,
) -> Result<String> {
    sessions.execute(
        "$/lean/rpc/call",
        RawField::Value(&info_call(id, reference)),
        docs,
        provider,
    )
}

#[test]
fn expression_popups_retain_native_metadata_across_edits_until_release() {
    for format in [WireFormat::V0, WireFormat::V1] {
        let mut sessions = Sessions {
            format,
            ..Sessions::default()
        };
        let id = sessions.create(URI.into(), Instant::now()).unwrap();
        let mut docs = documents();
        let mut provider = Provider {
            result: Some(annotated_answer()),
            ..Provider::new()
        };
        let result = execute(&mut sessions, id, &docs, &mut provider).unwrap();
        assert!(result.contains(r#""subexprPos":"/0""#), "{result}");
        assert!(result.contains(r#""subexprPos":"/1""#), "{result}");
        assert!(result.contains(r#""subexprPos":"/""#), "{result}");
        let find = |address| {
            sessions.sessions[&id]
                .references
                .iter()
                .find_map(|(id, reference)| {
                    (reference.kind == ReferenceKind::Info(address)).then_some(*id)
                })
                .unwrap()
        };
        let root = find(InfoAddress {
            code: CodeAddress {
                goal: 0,
                field: CodeField::Target,
            },
            subexpression: None,
        });
        let beta = find(InfoAddress {
            code: CodeAddress {
                goal: 0,
                field: CodeField::Target,
            },
            subexpression: Some(1),
        });
        assert_eq!(
            popup(
                &mut sessions,
                id,
                &format.reference(root),
                &docs,
                &mut provider
            )
            .unwrap(),
            r#"{"exprExplicit":{"text":"(f β)"},"type":{"text":"P"},"doc":null}"#,
        );
        assert_eq!(
            popup(
                &mut sessions,
                id,
                &format.reference(beta),
                &docs,
                &mut provider
            )
            .unwrap(),
            r#"{"exprExplicit":{"text":"β"},"type":{"text":"P"},"doc":null}"#,
        );
        assert_eq!(provider.calls, 1, "hover must not re-elaborate a snapshot");
        let session = &sessions.sessions[&id];
        let bytes = session.references[&root].snapshot.bytes;
        assert_eq!(session.bytes, bytes + 128 * session.references.len());
        docs.save_with_text(URI, "changed source".into()).unwrap();
        assert_eq!(
            popup(
                &mut sessions,
                id,
                &format.reference(beta),
                &docs,
                &mut provider
            )
            .unwrap(),
            r#"{"exprExplicit":{"text":"β"},"type":{"text":"P"},"doc":null}"#,
        );
        assert_eq!(provider.calls, 1);

        // Dropping the first/context reference cannot uncharge a snapshot held
        // by its expression references. The payload is released exactly once.
        sessions.sessions.get_mut(&id).unwrap().release(0);
        let session = &sessions.sessions[&id];
        assert_eq!(session.bytes, bytes + 128 * session.references.len());
        sessions.sessions.get_mut(&id).unwrap().release(beta);
        assert!(matches!(
            popup(
                &mut sessions,
                id,
                &format.reference(beta),
                &docs,
                &mut provider
            ),
            Err((-32602, _))
        ));
        let refs: Vec<_> = sessions.sessions[&id].references.keys().copied().collect();
        for reference in refs {
            sessions.sessions.get_mut(&id).unwrap().release(reference);
        }
        assert!(sessions.sessions[&id].references.is_empty());
        assert_eq!(sessions.sessions[&id].bytes, 0);
    }
}

#[test]
fn expression_popup_rejects_wrong_types_formats_and_dead_sessions() {
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
        let other = match format {
            WireFormat::V0 => WireFormat::V1,
            WireFormat::V1 => WireFormat::V0,
        };
        for bad in [
            format.reference(0), // ContextInfo cannot be used as InfoWithCtx.
            format.reference(u64::MAX),
            other.reference(1),
            format!(r#"{{"{}":1}}"#, format.key()),
            format!(r#"{{"{}":"1","{}":"2"}}"#, format.key(), format.key()),
            r#"{"p":"1","__rpcref":"1"}"#.to_owned(),
            "null".to_owned(),
        ] {
            assert!(
                matches!(
                    popup(&mut sessions, id, &bad, &docs, &mut provider),
                    Err((-32602, _))
                ),
                "{bad}"
            );
        }
        let second = sessions.create(URI.into(), Instant::now()).unwrap();
        assert!(matches!(
            popup(
                &mut sessions,
                second,
                &format.reference(1),
                &docs,
                &mut provider
            ),
            Err((-32602, _))
        ));
        sessions.sessions.get_mut(&id).unwrap().expires = Instant::now();
        assert!(matches!(
            popup(
                &mut sessions,
                id,
                &format.reference(1),
                &docs,
                &mut provider
            ),
            Err((RECONNECT, _))
        ));
        assert_eq!(provider.calls, 1);
    }
}

#[test]
fn malformed_expression_annotations_and_late_exhaustion_publish_no_references() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let docs = documents();
    let mut provider = Provider::new();
    for mutation in 0..4 {
        let mut bad = annotated_answer();
        let Answer::InteractiveGoals { goals } = &mut bad else {
            unreachable!()
        };
        let code = &mut goals[0].target;
        match mutation {
            0 => code.subexpressions[1].range = 4..5, // Split UTF-8 β.
            1 => code.subexpressions[1].range = 1..5, // Overlap another leaf.
            2 => code.subexpressions[1].position = 4, // Duplicate identity.
            _ => code.info.as_mut().unwrap().type_ = Some("x".repeat(65537)),
        }
        provider.result = Some(bad);
        assert!(execute(&mut sessions, id, &docs, &mut provider).is_err());
        assert!(sessions.sessions[&id].references.is_empty());
        assert_eq!(sessions.sessions[&id].bytes, 0);
    }
    provider.result = Some(annotated_answer());
    sessions.sessions.get_mut(&id).unwrap().next_reference = u64::MAX - 2;
    assert!(execute(&mut sessions, id, &docs, &mut provider).is_err());
    assert!(sessions.sessions[&id].references.is_empty());
    assert_eq!(sessions.sessions[&id].bytes, 0);
    assert_eq!(sessions.sessions[&id].next_reference, u64::MAX - 2);
}
fn documents() -> DocumentSession {
    let mut docs = DocumentSession::new();
    docs.open(URI.into(), 1, "β".into()).unwrap();
    docs
}
fn call(session: u64, method: &str) -> String {
    format!(
        r#"{{"textDocument":{{"uri":"{URI}"}},"position":{{"line":0,"character":0}},"sessionId":"{session}","method":"{method}","params":{{"textDocument":{{"uri":"{URI}"}},"position":{{"line":0,"character":0}}}}}}"#
    )
}
struct Provider {
    result: Option<Answer>,
    calls: usize,
    current: bool,
}
impl Provider {
    fn new() -> Self {
        Self {
            result: Some(answer("P")),
            calls: 0,
            current: false,
        }
    }
}
impl CheckSource for Provider {
    fn semantic_queries(&self) -> bool {
        true
    }
    fn check(&mut self, _: &str, _: &str, _: &[OpenDocumentSource<'_>]) -> Vec<String> {
        Vec::new()
    }
    fn query(
        &mut self,
        query: Query<'_>,
        docs: &[OpenDocumentSource<'_>],
    ) -> std::result::Result<Option<Answer>, String> {
        self.calls += 1;
        assert!(docs.iter().any(|doc| doc.uri == query.uri
            && doc.version == query.version
            && doc.text == Some(query.text)));
        Ok(if self.current {
            Some(answer(query.text))
        } else {
            self.result.clone()
        })
    }
}
fn execute(
    sessions: &mut Sessions,
    id: u64,
    docs: &DocumentSession,
    provider: &mut Provider,
) -> Result<String> {
    sessions.execute(
        "$/lean/rpc/call",
        RawField::Value(&call(id, "Lean.Widget.getInteractiveGoals")),
        docs,
        provider,
    )
}

#[test]
fn expiry_is_exact_and_session_numbers_never_repeat_after_close() {
    let mut sessions = Sessions::default();
    let now = Instant::now();
    let id = sessions.create(URI.into(), now).unwrap();
    assert!(
        sessions
            .session(id, URI, now + KEEP_ALIVE - Duration::from_nanos(1))
            .is_ok()
    );
    assert!(matches!(
        sessions.session(id, URI, now + KEEP_ALIVE),
        Err((RECONNECT, _))
    ));
    let next = sessions.create(URI.into(), now + KEEP_ALIVE).unwrap();
    assert_ne!(id, next);
    sessions.close(URI);
    assert!(sessions.sessions.is_empty());
    assert_ne!(sessions.create(URI.into(), now + KEEP_ALIVE).unwrap(), next);
}
#[test]
fn capacity_and_uri_binding_refuse_instead_of_reusing_another_session() {
    let mut sessions = Sessions::default();
    let now = Instant::now();
    let id = sessions.create(URI.into(), now).unwrap();
    assert!(matches!(
        sessions.session(id, "other", now),
        Err((RECONNECT, _))
    ));
    for _ in 1..MAX_SESSIONS {
        sessions.create("other".into(), now).unwrap();
    }
    assert!(sessions.create(URI.into(), now).is_err());
    sessions.close(URI);
    assert!(sessions.create(URI.into(), now).is_ok());
    sessions.clear();
    assert!(sessions.sessions.is_empty());
}
#[test]
fn repeated_context_refs_release_exactly_and_freed_numbers_never_alias() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let session = sessions.sessions.get_mut(&id).unwrap();
    let snapshot = snapshot("P");
    let a = session.retain(&snapshot, ReferenceKind::Context).unwrap();
    assert_eq!(
        session.retain(&snapshot, ReferenceKind::Context).unwrap(),
        a
    );
    assert_eq!(session.references[&a].count, 2);
    session.release(a);
    assert_eq!(session.references[&a].count, 1);
    session.release(a);
    assert!(session.references.is_empty());
    assert_eq!(session.bytes, 0);
    let b = session.retain(&snapshot, ReferenceKind::Context).unwrap();
    assert_ne!(a, b);
    session.release(a);
    assert!(session.references.contains_key(&b));
}
#[test]
fn both_formats_encode_structured_contexts_and_share_counted_goal_references() {
    for format in [WireFormat::V0, WireFormat::V1] {
        let mut sessions = Sessions {
            format,
            ..Sessions::default()
        };
        let id = sessions.create(URI.into(), Instant::now()).unwrap();
        let mut provider = Provider::new();
        let Some(Answer::InteractiveGoals { goals }) = &mut provider.result else {
            unreachable!()
        };
        let mut other = goals[0].clone();
        other.mvar_id = "_uniq.3".into();
        goals.push(other);
        let result = execute(&mut sessions, id, &documents(), &mut provider).unwrap();
        assert!(result.contains("\"fvarIds\":[\"_uniq.1\"]"));
        assert!(result.contains("\"mvarId\":\"_uniq.2\""));
        assert!(result.contains("\"userName\":\"left\""));
        assert_eq!(result.matches(&format.reference(0)).count(), 2);
        assert_eq!(sessions.sessions[&id].references[&0].count, 2);
        let framed = format!(r#"{{"jsonrpc":"2.0","id":1,"result":{result}}}"#);
        assert!(parse_envelope(&framed).is_ok());
    }
}
#[test]
fn term_references_are_distinct_and_range_uses_exact_utf16_coordinates() {
    let mut sessions = Sessions {
        format: WireFormat::V1,
        ..Sessions::default()
    };
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let mut provider = Provider::new();
    provider.result = Some(Answer::InteractiveTermGoal(TermGoal {
        hypotheses: vec![],
        target: "P".into(),
        range: 0..2,
    }));
    let input = call(id, "Lean.Widget.getInteractiveTermGoal");
    let result = sessions
        .execute(
            "$/lean/rpc/call",
            RawField::Value(&input),
            &documents(),
            &mut provider,
        )
        .unwrap();
    assert!(result.contains("\"ctx\":{\"__rpcref\":\"0\"}"));
    assert!(result.contains("\"term\":{\"__rpcref\":\"1\"}"));
    assert!(result.contains("\"end\":{\"line\":0,\"character\":1}"));
    assert_eq!(sessions.sessions[&id].references.len(), 2);
}
#[test]
fn late_reference_exhaustion_rolls_back_the_entire_response() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    sessions.sessions.get_mut(&id).unwrap().next_reference = u64::MAX - 1;
    let mut provider = Provider::new();
    provider.result = Some(Answer::InteractiveTermGoal(TermGoal {
        hypotheses: vec![],
        target: "P".into(),
        range: 0..2,
    }));
    let input = call(id, "Lean.Widget.getInteractiveTermGoal");
    assert!(
        sessions
            .execute(
                "$/lean/rpc/call",
                RawField::Value(&input),
                &documents(),
                &mut provider
            )
            .is_err()
    );
    assert!(sessions.sessions[&id].references.is_empty());
    assert_eq!(sessions.sessions[&id].bytes, 0);
    assert_eq!(sessions.sessions[&id].next_reference, u64::MAX - 1);
}
#[test]
fn unavailable_results_and_empty_goals_remain_distinct_and_hold_no_refs() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let mut provider = Provider::new();
    provider.result = None;
    assert_eq!(
        execute(&mut sessions, id, &documents(), &mut provider).unwrap(),
        "null"
    );
    provider.result = Some(Answer::InteractiveGoals { goals: vec![] });
    assert_eq!(
        execute(&mut sessions, id, &documents(), &mut provider).unwrap(),
        "{\"goals\":[]}"
    );
    assert!(sessions.sessions[&id].references.is_empty());
}
#[test]
fn malformed_provider_answers_cannot_install_refs() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let mut provider = Provider::new();
    for bad in [
        Answer::Goals { goals: vec![] },
        answer(&"x".repeat(65537)),
        Answer::InteractiveGoals {
            goals: vec![Goal {
                mvar_id: String::new(),
                user_name: None,
                hypotheses: vec![],
                target: "P".into(),
            }],
        },
    ] {
        provider.result = Some(bad);
        assert!(execute(&mut sessions, id, &documents(), &mut provider).is_err());
        assert!(sessions.sessions[&id].references.is_empty());
    }
}
#[test]
fn current_queries_do_not_read_retained_snapshots_and_invalid_edits_refuse() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let mut docs = documents();
    let mut provider = Provider {
        current: true,
        ..Provider::new()
    };
    assert!(
        execute(&mut sessions, id, &docs, &mut provider)
            .unwrap()
            .contains("β")
    );
    docs.save_with_text(URI, "new".into()).unwrap();
    assert!(
        execute(&mut sessions, id, &docs, &mut provider)
            .unwrap()
            .contains("new")
    );
    assert!(
        matches!(&sessions.sessions[&id].references[&0].snapshot.answer,
        Answer::InteractiveGoals { goals } if goals[0].target.text == "β")
    );
    docs.reject_change(URI, 2).unwrap();
    let before = provider.calls;
    assert!(execute(&mut sessions, id, &docs, &mut provider).is_err());
    assert_eq!(provider.calls, before);
    docs.change(URI, 3, "recovered".into()).unwrap();
    assert!(
        execute(&mut sessions, id, &docs, &mut provider)
            .unwrap()
            .contains("recovered")
    );
}
#[test]
fn wrong_session_or_cross_document_calls_never_reach_the_provider() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let mut provider = Provider::new();
    assert!(matches!(
        execute(
            &mut sessions,
            id.wrapping_add(1),
            &documents(),
            &mut provider
        ),
        Err((RECONNECT, _))
    ));
    let input = call(id, "Unknown.procedure");
    assert!(matches!(
        sessions.execute(
            "$/lean/rpc/call",
            RawField::Value(&input),
            &documents(),
            &mut provider
        ),
        Err((-32601, _))
    ));
    let input = call(id, "Lean.Widget.getInteractiveGoals").replacen(
        "\"params\":{\"textDocument\":{\"uri\":\"file:///Rpc.lean\"}",
        "\"params\":{\"textDocument\":{\"uri\":\"other\"}",
        1,
    );
    assert!(matches!(
        sessions.execute(
            "$/lean/rpc/call",
            RawField::Value(&input),
            &documents(),
            &mut provider
        ),
        Err((-32602, _))
    ));
    assert_eq!(provider.calls, 0);
}
#[test]
fn invalid_release_is_atomic_and_keepalive_does_not_revive_expired_sessions() {
    let mut sessions = Sessions::default();
    let now = Instant::now();
    let id = sessions.create(URI.into(), now).unwrap();
    sessions
        .sessions
        .get_mut(&id)
        .unwrap()
        .retain(&snapshot("P"), ReferenceKind::Context)
        .unwrap();
    let bad = format!(r#"{{"uri":"{URI}","sessionId":"{id}","refs":[{{"p":"0"}},{{"p":1}}]}}"#);
    assert!(
        sessions
            .notify("$/lean/rpc/release", RawField::Value(&bad))
            .is_err()
    );
    assert_eq!(sessions.sessions[&id].references.len(), 1);
    let keep = format!(r#"{{"uri":"{URI}","sessionId":"{id}"}}"#);
    sessions
        .notify("$/lean/rpc/keepAlive", RawField::Value(&keep))
        .unwrap();
    assert!(sessions.sessions[&id].expires >= now + KEEP_ALIVE);
    sessions.sessions.get_mut(&id).unwrap().expires = now;
    assert!(matches!(
        sessions.notify("$/lean/rpc/keepAlive", RawField::Value(&keep)),
        Err((RECONNECT, _))
    ));
    assert!(sessions.sessions.is_empty());
}

fn highlight_call(session: u64, uri: &str, params: &str) -> String {
    format!(
        r#"{{"textDocument":{{"uri":{}}},"position":{{"line":0,"character":0}},"sessionId":"{session}","method":"Lean.Widget.highlightMatches","params":{params}}}"#,
        crate::json_string(uri)
    )
}

fn search_message(
    sessions: &mut Sessions,
    id: u64,
    params: &str,
    docs: &DocumentSession,
    provider: &mut Provider,
) -> Result<String> {
    sessions.execute(
        "$/lean/rpc/call",
        RawField::Value(&highlight_call(id, URI, params)),
        docs,
        provider,
    )
}

fn root_info_reference(sessions: &Sessions, id: u64) -> u64 {
    sessions.sessions[&id]
        .references
        .iter()
        .find_map(|(id, reference)| {
            (reference.kind
                == ReferenceKind::Info(InfoAddress {
                    code: CodeAddress {
                        goal: 0,
                        field: CodeField::Target,
                    },
                    subexpression: None,
                }))
            .then_some(*id)
        })
        .unwrap()
}

#[test]
fn message_search_retains_each_expression_occurrence_until_its_own_release() {
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
        let root = root_info_reference(&sessions, id);
        let reference = format.reference(root);
        let expression = tagged(&reference, 1, &code("(f β)"));
        let embed = format!(r#"{{"tag":[{{"expr":{expression}}},{{"text":""}}]}}"#);
        let message = format!(r#"{{"append":[{embed},{embed}]}}"#);
        let session = &sessions.sessions[&id];
        let retained = (
            session.references.len(),
            session.bytes,
            session.next_reference,
        );
        for (index, query) in ["β", ""].into_iter().enumerate() {
            let params = format!(
                r#"{{"query":{},"msg":{message}}}"#,
                crate::json_string(query)
            );
            let result = search_message(&mut sessions, id, &params, &docs, &mut provider).unwrap();
            assert_eq!(result.matches(&format!(r#""info":{reference}"#)).count(), 2);
            if query.is_empty() {
                assert_eq!(result, message);
            } else {
                assert_eq!(
                    result
                        .matches(r#""tag":["highlighted",{"text":"β"}]"#)
                        .count(),
                    2
                );
            }
            assert_eq!(
                sessions.sessions[&id].references[&root].count,
                1 + 2 * (index + 1)
            );
            let session = &sessions.sessions[&id];
            assert_eq!(
                (
                    session.references.len(),
                    session.bytes,
                    session.next_reference
                ),
                retained
            );
        }
        assert_eq!(
            provider.calls, 1,
            "highlighting must reuse retained native metadata"
        );
        // Release the original presentation, then each highlighted occurrence.
        // A reference is invalidated only when the final copy is released.
        for _ in 0..4 {
            sessions.sessions.get_mut(&id).unwrap().release(root);
            assert_eq!(
                popup(&mut sessions, id, &reference, &docs, &mut provider).unwrap(),
                r#"{"exprExplicit":{"text":"(f β)"},"type":{"text":"P"},"doc":null}"#
            );
        }
        sessions.sessions.get_mut(&id).unwrap().release(root);
        assert!(matches!(
            popup(&mut sessions, id, &reference, &docs, &mut provider),
            Err((-32602, _))
        ));
        let refs: Vec<_> = sessions.sessions[&id].references.keys().copied().collect();
        for reference in refs {
            sessions.sessions.get_mut(&id).unwrap().release(reference);
        }
        assert!(sessions.sessions[&id].references.is_empty());
        assert_eq!(sessions.sessions[&id].bytes, 0);
    }
}

#[test]
fn message_search_uses_client_presentations_without_querying_or_retaining_objects() {
    for format in [WireFormat::V0, WireFormat::V1] {
        let mut sessions = Sessions {
            format,
            ..Sessions::default()
        };
        let id = sessions.create(URI.into(), Instant::now()).unwrap();
        let docs = documents();
        let mut provider = Provider::new();
        execute(&mut sessions, id, &docs, &mut provider).unwrap();
        let before = &sessions.sessions[&id];
        let retained = (before.references.len(), before.bytes, before.next_reference);
        let input = highlight_call(id, URI, r#"{"query":"β","msg":{"text":"aβb"}}"#);
        let result = sessions
            .execute(
                "$/lean/rpc/call",
                RawField::Value(&input),
                &docs,
                &mut provider,
            )
            .unwrap();
        assert_eq!(
            result,
            r#"{"append":[{"text":"a"},{"tag":["highlighted",{"text":"β"}]},{"text":"b"}]}"#
        );
        assert_eq!(
            provider.calls, 1,
            "search must not trigger another native elaboration"
        );
        let after = &sessions.sessions[&id];
        assert_eq!(
            (after.references.len(), after.bytes, after.next_reference),
            retained
        );
        assert_eq!(after.references[&0].count, 1);
    }
}

#[test]
fn message_search_rejects_dead_or_wrong_refs_and_rolls_back_late_failures() {
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
        let root = root_info_reference(&sessions, id);
        let dead = sessions.sessions[&id]
            .references
            .iter()
            .find_map(|(id, reference)| {
                matches!(reference.kind, ReferenceKind::Info(address) if address.subexpression.is_some())
                    .then_some(*id)
            })
            .unwrap();
        sessions.sessions.get_mut(&id).unwrap().release(dead);
        let embed = |reference: &str| {
            let expression = tagged(reference, 1, &code("(f β)"));
            format!(r#"{{"tag":[{{"expr":{expression}}},{{"text":""}}]}}"#)
        };
        let valid = embed(&format.reference(root));
        let other = if format == WireFormat::V0 {
            WireFormat::V1
        } else {
            WireFormat::V0
        };
        let session = &sessions.sessions[&id];
        let retained = (
            session.references.len(),
            session.bytes,
            session.next_reference,
        );
        for reference in [
            format.reference(0),
            format.reference(dead),
            format.reference(u64::MAX),
            other.reference(root),
        ] {
            let bad = embed(&reference);
            let params = format!(r#"{{"query":"","msg":{{"append":[{valid},{bad}]}}}}"#);
            assert!(
                matches!(
                    search_message(&mut sessions, id, &params, &docs, &mut provider),
                    Err((-32602, _))
                ),
                "{reference}"
            );
            let session = &sessions.sessions[&id];
            assert_eq!(
                (
                    session.references.len(),
                    session.bytes,
                    session.next_reference
                ),
                retained
            );
            assert_eq!(session.references[&root].count, 1);
        }
        let foreign = sessions.create(URI.into(), Instant::now()).unwrap();
        let params = format!(r#"{{"query":"","msg":{valid}}}"#);
        assert!(matches!(
            search_message(&mut sessions, foreign, &params, &docs, &mut provider),
            Err((-32602, _))
        ));
        assert!(sessions.sessions[&foreign].references.is_empty());

        let exhausted = format!(
            r#"{{"query":"x","msg":{{"append":[{valid},{{"text":"{}"}}]}}}}"#,
            "x".repeat(30000)
        );
        let error =
            search_message(&mut sessions, id, &exhausted, &docs, &mut provider).unwrap_err();
        assert_eq!(error.0, REQUEST_FAILED_CODE);
        assert!(error.1.contains("wire budget"));
        assert_eq!(sessions.sessions[&id].references[&root].count, 1);

        sessions
            .sessions
            .get_mut(&id)
            .unwrap()
            .references
            .get_mut(&root)
            .unwrap()
            .count = usize::MAX - 1;
        let exhausted = format!(r#"{{"query":"","msg":{{"append":[{valid},{valid}]}}}}"#);
        let error =
            search_message(&mut sessions, id, &exhausted, &docs, &mut provider).unwrap_err();
        assert_eq!(error.0, REQUEST_FAILED_CODE);
        assert!(error.1.contains("reference count"));
        assert_eq!(
            sessions.sessions[&id].references[&root].count,
            usize::MAX - 1
        );
        sessions
            .sessions
            .get_mut(&id)
            .unwrap()
            .references
            .get_mut(&root)
            .unwrap()
            .count = 1;
        assert_eq!(
            search_message(&mut sessions, id, &params, &docs, &mut provider).unwrap(),
            valid
        );
        assert_eq!(sessions.sessions[&id].references[&root].count, 2);
        let session = &sessions.sessions[&id];
        assert_eq!(
            (
                session.references.len(),
                session.bytes,
                session.next_reference
            ),
            retained
        );
        assert_eq!(provider.calls, 1);
    }
}

#[test]
fn message_search_reports_invalid_params_separately_from_unsupported_embeddings() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let mut provider = Provider::new();
    let docs = documents();
    for (params, expected) in [
        (r#"{"query":false,"msg":{"text":"x"}}"#, -32602),
        (r#"{"query":"x","msg":{"text":"x","text":"y"}}"#, -32602),
        (
            r#"{"query":"x","msg":{"tag":[{"goal":{}},{"text":""}]}}"#,
            REQUEST_FAILED_CODE,
        ),
    ] {
        let input = highlight_call(id, URI, params);
        let error = sessions
            .execute(
                "$/lean/rpc/call",
                RawField::Value(&input),
                &docs,
                &mut provider,
            )
            .unwrap_err();
        assert_eq!(error.0, expected);
        assert!(sessions.sessions[&id].references.is_empty());
    }
    assert_eq!(provider.calls, 0);
}

#[test]
fn message_search_output_exhaustion_is_atomic_and_does_not_poison_a_later_request() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let mut provider = Provider::new();
    let docs = documents();
    let params = format!(
        r#"{{"query":"x","msg":{{"text":"{}"}}}}"#,
        "x".repeat(30000)
    );
    let input = highlight_call(id, URI, &params);
    let error = sessions
        .execute(
            "$/lean/rpc/call",
            RawField::Value(&input),
            &docs,
            &mut provider,
        )
        .unwrap_err();
    assert_eq!(error.0, REQUEST_FAILED_CODE);
    assert!(error.1.contains("wire budget"));
    assert!(sessions.sessions[&id].references.is_empty());
    assert_eq!(sessions.sessions[&id].bytes, 0);
    let input = highlight_call(id, URI, r#"{"query":"x","msg":{"text":"x"}}"#);
    let expected = r#"{"tag":["highlighted",{"text":"x"}]}"#;
    for _ in 0..2 {
        assert_eq!(
            sessions
                .execute(
                    "$/lean/rpc/call",
                    RawField::Value(&input),
                    &docs,
                    &mut provider
                )
                .unwrap(),
            expected
        );
    }
    assert_eq!(provider.calls, 0);
}

#[test]
fn message_search_keeps_session_uri_expiry_and_current_document_guards() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let mut provider = Provider::new();
    let mut docs = documents();
    let params = r#"{"query":"x","msg":{"text":"x"}}"#;
    let cross_document = highlight_call(id, "file:///Other.lean", params);
    assert!(matches!(
        sessions.execute(
            "$/lean/rpc/call",
            RawField::Value(&cross_document),
            &docs,
            &mut provider
        ),
        Err((RECONNECT, _))
    ));
    let input = highlight_call(id, URI, params);
    docs.reject_change(URI, 2).unwrap();
    assert!(matches!(
        sessions.execute(
            "$/lean/rpc/call",
            RawField::Value(&input),
            &docs,
            &mut provider
        ),
        Err((REQUEST_FAILED_CODE, _))
    ));
    docs.change(URI, 3, "recovered".into()).unwrap();
    assert!(
        sessions
            .execute(
                "$/lean/rpc/call",
                RawField::Value(&input),
                &docs,
                &mut provider
            )
            .is_ok()
    );
    sessions.sessions.get_mut(&id).unwrap().expires = Instant::now();
    assert!(matches!(
        sessions.execute(
            "$/lean/rpc/call",
            RawField::Value(&input),
            &docs,
            &mut provider
        ),
        Err((RECONNECT, _))
    ));
    assert_eq!(provider.calls, 0);
}

#[test]
fn message_search_cannot_hide_invalid_outer_utf16_positions() {
    let mut sessions = Sessions::default();
    let id = sessions.create(URI.into(), Instant::now()).unwrap();
    let mut provider = Provider::new();
    let mut docs = DocumentSession::new();
    docs.open(URI.into(), 1, "😀".into()).unwrap();
    let input = highlight_call(id, URI, r#"{"query":"x","msg":{"text":"x"}}"#)
        .replace("\"character\":0", "\"character\":1");
    assert!(matches!(
        sessions.execute(
            "$/lean/rpc/call",
            RawField::Value(&input),
            &docs,
            &mut provider
        ),
        Err((-32602, _))
    ));
    assert_eq!(provider.calls, 0);
    assert!(sessions.sessions[&id].references.is_empty());
}

fn widgets_call(session: u64, uri: &str, outer_char: usize, params: &str) -> String {
    format!(
        r#"{{"textDocument":{{"uri":{}}},"position":{{"line":0,"character":{outer_char}}},"sessionId":"{session}","method":"Lean.Widget.getWidgets","params":{params}}}"#,
        crate::json_string(uri)
    )
}

#[test]
fn widgets_query_validates_bare_positions_and_preserves_session_guards() {
    for format in [WireFormat::V0, WireFormat::V1] {
        let mut sessions = Sessions {
            format,
            ..Sessions::default()
        };
        let id = sessions.create(URI.into(), Instant::now()).unwrap();
        let mut docs = DocumentSession::new();
        docs.open(URI.into(), 1, "😀\ndef x := 1\n".into()).unwrap();
        let mut provider = Provider::new();
        execute(&mut sessions, id, &docs, &mut provider).unwrap();
        let before = &sessions.sessions[&id];
        let retained = (before.references.len(), before.bytes, before.next_reference);

        for params in [
            r#"{"line":0,"character":0}"#,
            r#"{"line":1,"character":4}"#,
            r#"{"line":99,"character":99}"#,
        ] {
            let input = widgets_call(id, URI, 0, params);
            assert_eq!(
                sessions
                    .execute(
                        "$/lean/rpc/call",
                        RawField::Value(&input),
                        &docs,
                        &mut provider,
                    )
                    .unwrap(),
                r#"{"widgets":[]}"#,
                "{params}"
            );
        }
        assert_eq!(
            provider.calls, 1,
            "getWidgets must not re-elaborate or invoke semantic query"
        );
        let after = &sessions.sessions[&id];
        assert_eq!(
            (after.references.len(), after.bytes, after.next_reference),
            retained
        );

        for bad_params in [
            "null",
            "[]",
            "1",
            "{}",
            r#"{"line":-1,"character":0}"#,
            r#"{"line":"0","character":0}"#,
            r#"{"line":0,"character":1}"#,
            r#"{"line":0,"l\u0069ne":0,"character":0}"#,
            r#"{"textDocument":{"uri":"file:///Rpc.lean"},"position":{"line":0,"character":0}}"#,
        ] {
            let input = widgets_call(id, URI, 0, bad_params);
            assert!(
                matches!(
                    sessions.execute(
                        "$/lean/rpc/call",
                        RawField::Value(&input),
                        &docs,
                        &mut provider,
                    ),
                    Err((-32602, _))
                ),
                "{bad_params}"
            );
        }

        let bad_outer_surrogate = widgets_call(id, URI, 1, r#"{"line":1,"character":0}"#);
        assert!(matches!(
            sessions.execute(
                "$/lean/rpc/call",
                RawField::Value(&bad_outer_surrogate),
                &docs,
                &mut provider,
            ),
            Err((-32602, _))
        ));

        let wrong_uri = widgets_call(id, "file:///Other.lean", 0, r#"{"line":0,"character":0}"#);
        assert!(matches!(
            sessions.execute(
                "$/lean/rpc/call",
                RawField::Value(&wrong_uri),
                &docs,
                &mut provider,
            ),
            Err((RECONNECT, _))
        ));

        docs.reject_change(URI, 2).unwrap();
        let valid = widgets_call(id, URI, 0, r#"{"line":0,"character":0}"#);
        assert!(matches!(
            sessions.execute(
                "$/lean/rpc/call",
                RawField::Value(&valid),
                &docs,
                &mut provider,
            ),
            Err((REQUEST_FAILED_CODE, _))
        ));
        docs.change(URI, 3, "recovered".into()).unwrap();
        assert_eq!(
            sessions
                .execute(
                    "$/lean/rpc/call",
                    RawField::Value(&valid),
                    &docs,
                    &mut provider,
                )
                .unwrap(),
            r#"{"widgets":[]}"#
        );

        sessions.sessions.get_mut(&id).unwrap().expires = Instant::now();
        assert!(matches!(
            sessions.execute(
                "$/lean/rpc/call",
                RawField::Value(&valid),
                &docs,
                &mut provider,
            ),
            Err((RECONNECT, _))
        ));
    }
}

#[test]
fn widget_source_msg_to_interactive_and_lazy_trace_children_obey_pinned_contracts() {
    let call_with = |session: u64, method: &str, params: &str| {
        format!(
            r#"{{"textDocument":{{"uri":"{URI}"}},"position":{{"line":0,"character":0}},"sessionId":"{session}","method":"{method}","params":{params}}}"#
        )
    };
    for format in [WireFormat::V0, WireFormat::V1] {
        let mut sessions = Sessions {
            format,
            ..Sessions::default()
        };
        let id = sessions.create(URI.into(), Instant::now()).unwrap();
        let mut docs = DocumentSession::new();
        docs.open(URI.into(), 1, "😀\ndef x := 1\n".into()).unwrap();
        let mut provider = Provider {
            result: Some(annotated_answer()),
            ..Provider::new()
        };
        execute(&mut sessions, id, &docs, &mut provider).unwrap();

        // 1. getWidgetSource: valid pos + string hash -> -32602 "No widget module with hash ... registered"
        let ws = call_with(
            id,
            "Lean.Widget.getWidgetSource",
            r#"{"hash":"12345","pos":{"line":1,"character":2}}"#,
        );
        assert_eq!(
            sessions.execute(
                "$/lean/rpc/call",
                RawField::Value(&ws),
                &docs,
                &mut provider
            ),
            Err((
                -32602,
                "No widget module with hash 12345 registered".to_owned()
            ))
        );
        // Invalid UTF-16 surrogate position or numeric hash -> -32602
        for bad_ws in [
            r#"{"hash":12345,"pos":{"line":0,"character":0}}"#,
            r#"{"hash":"12345","pos":{"line":0,"character":1}}"#,
        ] {
            let input = call_with(id, "Lean.Widget.getWidgetSource", bad_ws);
            assert!(
                matches!(
                    sessions.execute(
                        "$/lean/rpc/call",
                        RawField::Value(&input),
                        &docs,
                        &mut provider
                    ),
                    Err((-32602, _))
                ),
                "{bad_ws}"
            );
        }

        // 2. msgToInteractive & lazyTraceChildrenToInteractive:
        // Unknown reference or wrong ReferenceKind (`InfoWithCtx` ref 0) -> -32602
        let wrong_msg = call_with(
            id,
            "Lean.Widget.InteractiveDiagnostics.msgToInteractive",
            &format!(r#"{{"msg":{},"indent":2}}"#, format.reference(0)),
        );
        let (_, detail) = sessions
            .execute(
                "$/lean/rpc/call",
                RawField::Value(&wrong_msg),
                &docs,
                &mut provider,
            )
            .unwrap_err();
        assert!(detail.contains("expected 'Lean.MessageData'"), "{detail}");

        let unknown_msg = call_with(
            id,
            "Lean.Widget.InteractiveDiagnostics.msgToInteractive",
            &format!(r#"{{"msg":{},"indent":0}}"#, format.reference(999_999)),
        );
        assert!(matches!(
            sessions.execute(
                "$/lean/rpc/call",
                RawField::Value(&unknown_msg),
                &docs,
                &mut provider
            ),
            Err((-32602, _))
        ));

        let wrong_lazy = call_with(
            id,
            "Lean.Widget.lazyTraceChildrenToInteractive",
            &format.reference(0),
        );
        let (_, detail) = sessions
            .execute(
                "$/lean/rpc/call",
                RawField::Value(&wrong_lazy),
                &docs,
                &mut provider,
            )
            .unwrap_err();
        assert!(
            detail.contains("expected 'Lean.Widget.LazyTraceChildren'"),
            "{detail}"
        );

        let unknown_lazy = call_with(
            id,
            "Lean.Widget.lazyTraceChildrenToInteractive",
            &format.reference(999_999),
        );
        let (code, detail) = sessions
            .execute(
                "$/lean/rpc/call",
                RawField::Value(&unknown_lazy),
                &docs,
                &mut provider,
            )
            .unwrap_err();
        assert_eq!(code, -32602);
        assert!(
            detail.contains("RPC reference '999999' is not valid"),
            "{detail}"
        );

        // Unnegotiated wire format key (`v0` vs `v1`) is refused as -32602.
        let other = match format {
            WireFormat::V0 => WireFormat::V1,
            WireFormat::V1 => WireFormat::V0,
        };
        let wrong_format_lazy = call_with(
            id,
            "Lean.Widget.lazyTraceChildrenToInteractive",
            &other.reference(0),
        );
        assert!(matches!(
            sessions.execute(
                "$/lean/rpc/call",
                RawField::Value(&wrong_format_lazy),
                &docs,
                &mut provider
            ),
            Err((-32602, _))
        ));
    }
}
