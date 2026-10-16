use super::super::CompletionItem;
use super::*;

fn query(text: &str, offset: usize, kind: QueryKind) -> Query<'_> {
    Query {
        kind,
        uri: "file:///Main.lean",
        version: 1,
        text,
        offset,
    }
}
fn hover(range: Range<usize>, contents: &str) -> Annotation {
    Annotation {
        selection: range.clone(),
        answer: Answer::Hover {
            contents: contents.to_owned(),
            range,
        },
    }
}
fn contents(answer: Option<Answer>) -> String {
    match answer {
        Some(Answer::Hover { contents, .. }) => contents,
        _ => panic!("expected hover"),
    }
}

#[test]
fn revisions_are_identity_based_and_clones_preserve_identity() {
    let revision = Revision::new();
    assert_eq!(revision, revision.clone());
    assert_ne!(revision, Revision::new());
}

#[test]
fn narrowest_annotation_wins_with_stable_later_ties() {
    let q = query("abcdef", 3, QueryKind::Hover);
    let revision = Revision::new();
    let index = SemanticIndex::new(
        q,
        &revision,
        vec![
            hover(2..4, "first"),
            hover(0..6, "outer"),
            hover(2..4, "later"),
        ],
    )
    .unwrap();
    assert_eq!(contents(index.query(q, &revision, &[]).unwrap()), "later");
    assert_eq!(
        contents(
            index
                .query(Query { offset: 5, ..q }, &revision, &[])
                .unwrap()
        ),
        "outer"
    );
}

#[test]
fn disjoint_short_ranges_do_not_hide_an_earlier_enclosing_interval() {
    let q = query("abcdefghij", 8, QueryKind::Hover);
    let revision = Revision::new();
    let index = SemanticIndex::new(
        q,
        &revision,
        vec![
            hover(6..7, "ended"),
            hover(0..10, "outer"),
            hover(2..3, "also ended"),
        ],
    )
    .unwrap();
    assert_eq!(contents(index.query(q, &revision, &[]).unwrap()), "outer");
}

#[test]
fn absent_information_is_not_a_solved_goal_or_another_query_kind() {
    let q = query("abcd", 1, QueryKind::Goals);
    let revision = Revision::new();
    let index = SemanticIndex::new(
        q,
        &revision,
        vec![Annotation {
            selection: 1..1,
            answer: Answer::Goals { goals: Vec::new() },
        }],
    )
    .unwrap();
    assert_eq!(
        index.query(q, &revision, &[]).unwrap(),
        Some(Answer::Goals { goals: Vec::new() })
    );
    assert_eq!(
        index
            .query(Query { offset: 2, ..q }, &revision, &[])
            .unwrap(),
        None
    );
    assert_eq!(
        index
            .query(
                Query {
                    kind: QueryKind::Hover,
                    ..q
                },
                &revision,
                &[]
            )
            .unwrap(),
        None
    );
}

#[test]
fn same_version_same_length_source_is_stale_under_a_new_revision() {
    let q = query("old", 1, QueryKind::Hover);
    let revision = Revision::new();
    let index = SemanticIndex::new(q, &revision, vec![hover(0..3, "old native result")]).unwrap();
    assert_eq!(
        index.query(Query { text: "new", ..q }, &Revision::new(), &[]),
        Err(IndexRefusal::ContentModified)
    );
    assert!(index.query(q, &revision.clone(), &[]).is_ok());
}

#[test]
fn wrong_document_version_length_and_invalid_cursor_are_refused() {
    let q = query("abc", 1, QueryKind::Hover);
    let revision = Revision::new();
    let index = SemanticIndex::new(q, &revision, vec![hover(0..3, "native")]).unwrap();
    for other in [
        Query {
            uri: "file:///Other.lean",
            ..q
        },
        Query { version: 2, ..q },
        Query { text: "abcd", ..q },
    ] {
        assert_eq!(
            index.query(other, &revision, &[]),
            Err(IndexRefusal::ContentModified)
        );
    }
    assert_eq!(
        index.query(Query { offset: 4, ..q }, &revision, &[]),
        Err(IndexRefusal::InvalidAnnotation)
    );
}

#[test]
fn malformed_later_annotation_refuses_the_whole_index() {
    let q = query("abc", 0, QueryKind::Hover);
    assert!(matches!(
        SemanticIndex::new(
            q,
            &Revision::new(),
            vec![hover(0..3, "valid"), hover(0..4, "invalid"),]
        ),
        Err(IndexRefusal::InvalidAnnotation)
    ));
}

#[test]
fn selection_and_answer_ranges_require_exact_unicode_and_crlf_boundaries() {
    let q = query("😀\r\nx", 0, QueryKind::Hover);
    for range in [0..1, 1..4, 4..5, 5..6, 0..99, Range { start: 6, end: 4 }] {
        assert!(matches!(
            SemanticIndex::new(q, &Revision::new(), vec![hover(range, "bad")]),
            Err(IndexRefusal::InvalidAnnotation)
        ));
    }
    assert!(SemanticIndex::new(q, &Revision::new(), vec![hover(0..4, "good")]).is_ok());
    let bad_answer = Annotation {
        selection: 0..4,
        answer: Answer::Hover {
            contents: "bad".into(),
            range: 0..5,
        },
    };
    assert!(matches!(
        SemanticIndex::new(q, &Revision::new(), vec![bad_answer]),
        Err(IndexRefusal::InvalidAnnotation)
    ));
}

#[test]
fn annotation_count_payload_and_build_work_are_separately_bounded() {
    let q = query("x", 0, QueryKind::Hover);
    assert!(matches!(
        SemanticIndex::new(
            q,
            &Revision::new(),
            vec![hover(0..1, "x"); MAX_ANNOTATIONS + 1]
        ),
        Err(IndexRefusal::ResourceLimit)
    ));
    assert!(matches!(
        SemanticIndex::new(
            q,
            &Revision::new(),
            vec![hover(0..1, &"x".repeat(MAX_PAYLOAD_BYTES + 1))]
        ),
        Err(IndexRefusal::ResourceLimit)
    ));
    let text = "x".repeat(1024 * 1024);
    let q = query(&text, 0, QueryKind::Hover);
    assert!(matches!(
        SemanticIndex::new(q, &Revision::new(), vec![hover(0..1, "x"); 5]),
        Err(IndexRefusal::ResourceLimit)
    ));
    let mut count = usize::MAX;
    assert_eq!(
        add(&mut count, 1, usize::MAX),
        Err(IndexRefusal::ResourceLimit)
    );
}

#[test]
fn completion_preserves_native_order_and_requires_a_covering_edit_range() {
    let q = query("abc", 2, QueryKind::Completion);
    let revision = Revision::new();
    let items = ["z", "a"]
        .map(|name| CompletionItem {
            label: name.into(),
            replacement: name.into(),
        })
        .to_vec();
    let answer = Answer::Completion {
        items,
        range: 0..3,
        is_incomplete: true,
    };
    let index = SemanticIndex::new(
        q,
        &revision,
        vec![Annotation {
            selection: 1..3,
            answer: answer.clone(),
        }],
    )
    .unwrap();
    assert_eq!(
        index.query(q, &revision, &[]).unwrap(),
        Some(answer.clone())
    );
    let bad = Annotation {
        selection: 0..3,
        answer: Answer::Completion {
            items: Vec::new(),
            range: 1..3,
            is_incomplete: false,
        },
    };
    assert!(matches!(
        SemanticIndex::new(q, &revision, vec![bad]),
        Err(IndexRefusal::InvalidAnnotation)
    ));
}

#[test]
fn definition_targets_are_resolved_native_facts_and_open_overlays_are_revalidated() {
    let q = query("name", 2, QueryKind::Definition);
    let revision = Revision::new();
    let answer = Answer::Definition {
        uri: "file:///Dep.lean".into(),
        source: "😀name".into(),
        range: 4..8,
    };
    let index = SemanticIndex::new(
        q,
        &revision,
        vec![Annotation {
            selection: 0..4,
            answer: answer.clone(),
        }],
    )
    .unwrap();
    let good = [OpenDocumentSource {
        uri: "file:///Dep.lean",
        version: 1,
        text: Some("😀name"),
    }];
    assert_eq!(index.query(q, &revision, &good).unwrap(), Some(answer));
    for text in [None, Some("😀else")] {
        let changed = [OpenDocumentSource { text, ..good[0] }];
        assert_eq!(
            index.query(q, &revision, &changed),
            Err(IndexRefusal::ContentModified)
        );
    }
}

#[test]
fn point_annotations_at_end_of_document_are_supported() {
    let q = query("x", 1, QueryKind::Goals);
    let revision = Revision::new();
    let answer = Answer::Goals {
        goals: vec!["⊢ True".into()],
    };
    let index = SemanticIndex::new(
        q,
        &revision,
        vec![Annotation {
            selection: 1..1,
            answer: answer.clone(),
        }],
    )
    .unwrap();
    assert_eq!(index.query(q, &revision, &[]).unwrap(), Some(answer));
}

fn term_goal(selection: Range<usize>, range: Range<usize>, goal: &str) -> Annotation {
    Annotation {
        selection,
        answer: Answer::TermGoal {
            goal: goal.to_owned(),
            range,
        },
    }
}

#[test]
fn term_goals_are_indexed_separately_with_native_interval_precedence() {
    let q = query("abcdef", 3, QueryKind::TermGoal);
    let revision = Revision::new();
    let later = term_goal(2..3, 2..4, "x : A\n⊢ A");
    let index = SemanticIndex::new(
        q,
        &revision,
        vec![
            term_goal(0..5, 0..6, "⊢ Outer"),
            term_goal(2..3, 2..4, "⊢ Earlier"),
            later.clone(),
            hover(3..3, "native hover"),
        ],
    )
    .unwrap();
    assert_eq!(index.query(q, &revision, &[]).unwrap(), Some(later.answer));
    assert_eq!(
        index
            .query(Query { offset: 5, ..q }, &revision, &[])
            .unwrap(),
        Some(Answer::TermGoal {
            goal: "⊢ Outer".into(),
            range: 0..6,
        })
    );
    assert_eq!(
        contents(
            index
                .query(Query { kind: QueryKind::Hover, ..q }, &revision, &[])
                .unwrap()
        ),
        "native hover"
    );
    assert_eq!(
        index
            .query(Query { kind: QueryKind::Goals, ..q }, &revision, &[])
            .unwrap(),
        None
    );
    assert_eq!(
        index
            .query(Query { offset: 6, ..q }, &revision, &[])
            .unwrap(),
        None
    );
}

#[test]
fn term_goal_selection_cannot_include_the_exclusive_answer_endpoint() {
    let q = query("abc", 0, QueryKind::TermGoal);
    let revision = Revision::new();
    for (selection, range) in [(0..3, 0..3), (3..3, 0..3), (0..1, 1..3), (0..0, 0..0)] {
        assert!(matches!(
            SemanticIndex::new(q, &revision, vec![term_goal(selection, range, "⊢ A")]),
            Err(IndexRefusal::InvalidAnnotation)
        ));
    }
    // An exact cursor at a token's start is valid; a cursor immediately after
    // the token has no term information, rather than failing wire validation.
    let answer = term_goal(1..1, 1..2, "⊢ A");
    let index = SemanticIndex::new(q, &revision, vec![answer.clone()]).unwrap();
    assert_eq!(
        index.query(Query { offset: 1, ..q }, &revision, &[]).unwrap(),
        Some(answer.answer)
    );
    assert_eq!(
        index.query(Query { offset: 2, ..q }, &revision, &[]).unwrap(),
        None
    );
}

#[test]
fn term_goal_index_revalidates_unicode_ranges_and_editor_revisions() {
    let text = "😀\r\n_";
    let q = query(text, 6, QueryKind::TermGoal);
    let revision = Revision::new();
    let answer = term_goal(6..6, 6..7, "x : A\n⊢ A");
    let index = SemanticIndex::new(q, &revision, vec![answer.clone()]).unwrap();
    assert_eq!(index.query(q, &revision, &[]).unwrap(), Some(answer.answer));
    assert_eq!(
        index.query(Query { text: "😀\r\nx", ..q }, &Revision::new(), &[]),
        Err(IndexRefusal::ContentModified)
    );
    for (selection, range) in [(0..0, 0..1), (0..0, 0..5), (5..5, 4..6), (6..6, 6..8)] {
        assert!(matches!(
            SemanticIndex::new(q, &revision, vec![term_goal(selection, range, "⊢ A")]),
            Err(IndexRefusal::InvalidAnnotation)
        ));
    }
}

#[test]
fn term_goal_payload_and_build_work_are_charged_before_publication() {
    let q = query("_", 0, QueryKind::TermGoal);
    let revision = Revision::new();
    let goal = "x : A\n⊢ A";
    assert_eq!(payload_bytes(&term_goal(0..0, 0..1, goal).answer), Ok(goal.len()));
    for goal in [String::new(), "x".repeat(super::super::MAX_RESULT_BYTES / 16 + 1)] {
        assert!(matches!(
            SemanticIndex::new(q, &revision, vec![term_goal(0..0, 0..1, &goal)]),
            Err(IndexRefusal::InvalidAnnotation)
        ));
    }
    assert!(matches!(
        payload_bytes(&term_goal(0..0, 0..1, &"x".repeat(MAX_PAYLOAD_BYTES + 1)).answer),
        Err(IndexRefusal::ResourceLimit)
    ));
    let text = "x".repeat(1024 * 1024);
    let q = query(&text, 0, QueryKind::TermGoal);
    assert!(matches!(
        SemanticIndex::new(q, &revision, vec![term_goal(0..0, 0..1, "⊢ A"); 5]),
        Err(IndexRefusal::ResourceLimit)
    ));
}
