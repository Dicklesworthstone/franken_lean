//! Typed wire-boundary checks for provisional term goals.
use super::{Answer, MAX_RESULT_BYTES, Query, QueryKind, result_json};
use std::ops::Range;

fn query(text: &str, offset: usize) -> Query<'_> {
    Query {
        kind: QueryKind::TermGoal,
        uri: "file:///term-goals.lean",
        version: 3,
        text,
        offset,
    }
}

fn answer(range: Range<usize>) -> Answer {
    Answer::TermGoal {
        goal: "A : Type\nx : A\n⊢ A".to_owned(),
        range,
    }
}

#[test]
fn term_goal_uses_the_plain_term_goal_shape_not_the_tactic_goal_shape() {
    let text = "def pending : Nat := _";
    let start = text.find('_').unwrap();
    let result = result_json(answer(start..start + 1), query(text, start)).unwrap();
    assert_eq!(
        result,
        format!(
            "{{\"goal\":\"A : Type\\nx : A\\n⊢ A\",\"range\":{{\"start\":{{\"line\":0,\"character\":{start}}},\"end\":{{\"line\":0,\"character\":{}}}}}}}",
            start + 1,
        ),
    );
    assert!(!result.contains("\"goals\""));
    assert!(!result.contains("\"rendered\""));
}

#[test]
fn term_goal_ranges_count_utf16_units_and_treat_crlf_as_one_newline() {
    let text = "-- heading\r\n😀 _\r\n";
    let start = text.find('_').unwrap();
    let result = result_json(answer(start..start + 1), query(text, start)).unwrap();
    assert!(result.contains("\"start\":{\"line\":1,\"character\":3}"));
    assert!(result.contains("\"end\":{\"line\":1,\"character\":4}"));
}

#[test]
fn term_goal_text_is_json_escaped_without_changing_its_plaintext_meaning() {
    let goal = "x : String := \"a\\b\"\n⊢ String\t\r";
    let result = result_json(
        Answer::TermGoal {
            goal: goal.to_owned(),
            range: 0..1,
        },
        query("_", 0),
    )
    .unwrap();
    assert!(result.contains(&format!("\"goal\":{}", crate::json_string(goal))));
    assert!(!result.contains('\n'));
    assert!(!result.contains('\r'));
    assert!(!result.contains('\t'));
}

#[test]
fn term_goal_refuses_empty_reversed_out_of_source_and_unrelated_ranges() {
    let text = "_ abc";
    for range in [0..0, Range { start: 3, end: 2 }, 0..6, 2..5] {
        assert!(result_json(answer(range), query(text, 0)).is_err());
    }
}

#[test]
fn term_goal_refuses_utf8_scalar_splits() {
    let text = "é_";
    assert!(result_json(answer(1..3), query(text, 2)).is_err());
    assert!(result_json(answer(0..1), query(text, 0)).is_err());
}

#[test]
fn term_goal_refuses_an_end_inside_crlf() {
    let text = "_\r\n";
    assert!(result_json(answer(0..2), query(text, 0)).is_err());
    assert!(result_json(answer(0..1), query(text, 0)).is_ok());
}

#[test]
fn term_goal_enforces_the_provider_output_budget_at_its_exact_boundary() {
    for size in [MAX_RESULT_BYTES / 16, MAX_RESULT_BYTES / 16 + 1] {
        let result = result_json(
            Answer::TermGoal {
                goal: "x".repeat(size),
                range: 0..1,
            },
            query("_", 0),
        );
        assert_eq!(result.is_ok(), size == MAX_RESULT_BYTES / 16);
    }
}

#[test]
fn term_goal_rejects_empty_provider_text() {
    assert!(
        result_json(
            Answer::TermGoal {
                goal: String::new(),
                range: 0..1,
            },
            query("_", 0),
        )
        .is_err()
    );
}

#[test]
fn term_goal_and_tactic_goal_answers_cannot_be_interchanged() {
    assert!(result_json(Answer::Goals { goals: vec![] }, query("_", 0)).is_err());
    let mut tactic_query = query("_", 0);
    tactic_query.kind = QueryKind::Goals;
    assert!(result_json(answer(0..1), tactic_query).is_err());
}
