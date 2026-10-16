//! Term-goal payloads use the same correlation and cancellation passes as other
//! semantic queries. These fixtures prove wire contracts, not source elaboration.
use super::*;

const RANGE: &str = r#"{"start":{"line":1,"character":2},"end":{"line":1,"character":3}}"#;

fn result(goal: &str, range: &str) -> String {
    format!("{{\"goal\":{},\"range\":{range}}}", crate::json_string(goal))
}

fn frames(messages: &[&str]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for message in messages {
        crate::transport::write_message(&mut bytes, message.as_bytes()).unwrap();
    }
    bytes
}

fn pair(response: &str, cancel: bool) -> (Vec<u8>, Vec<u8>) {
    let mut requests = vec![
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A","version":1,"text":"x"}}}"#,
        r#"{"jsonrpc":"2.0","id":1.25e2,"method":"$/lean/plainTermGoal","params":{"textDocument":{"uri":"file:///A"},"position":{"line":0,"character":0}}}"#,
    ];
    if cancel {
        requests.push(r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":1.25e2}}"#);
    }
    requests.extend([
        r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///A"}}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    ]);
    let responses = frames(&[
        r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
        response,
        r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
    ]);
    (frames(&requests), responses)
}

fn reply(value: &str) -> String {
    format!("{{\"jsonrpc\":\"2.0\",\"id\":1.25e2,\"result\":{value}}}")
}

#[test]
fn accepts_bounded_term_goal_payloads_without_confusing_them_with_tactic_goals() {
    let value = result("α : Type\nx : α\n⊢ α", RANGE);
    assert!(crate::json::plain_term_goal_result(&value));
    assert!(!crate::json::plain_goal_result(&value));
    assert!(!crate::json::plain_term_goal_result(r#"{"rendered":"no goals","goals":[]}"#));
    assert!(crate::json::plain_term_goal_result(&result(
        "⊢ \"quoted\" \\ 😀",
        r#"{"start":{"line":1,"character":99},"end":{"line":2,"character":0}}"#,
    )));
}

#[test]
fn rejects_missing_duplicated_mistyped_and_inverted_term_goal_fields() {
    let good = result("⊢ A", RANGE);
    let invalid = [
        "null".to_owned(),
        "[]".to_owned(),
        "{}".to_owned(),
        result("", RANGE),
        format!("{{\"goal\":1,\"range\":{RANGE}}}"),
        format!("{{\"range\":{RANGE}}}"),
        r#"{"goal":"A"}"#.to_owned(),
        format!("{{\"goal\":\"A\",\"g\\u006fal\":\"B\",\"range\":{RANGE}}}"),
        format!("{{\"goal\":\"A\",\"range\":{RANGE},\"range\":{RANGE}}}"),
        good.replace("\"line\":1", "\"line\":-1"),
        good.replace("\"line\":1", "\"line\":2147483648"),
        good.replace("\"line\":1", "\"line\":1.0"),
        good.replace("\"line\":1", "\"line\":\"1\""),
        good.replace("\"line\":1", "\"line\":1,\"line\":1"),
        good.replace("\"character\":2", "\"character\":4"),
        good.replace("\"character\":2", "\"character\":3"),
        result("A", r#"{"start":{"line":0,"character":0}}"#),
        result("A", r#"{"start":null,"end":{"line":1,"character":0}}"#),
        result("A", r#"{"start":{"line":1,"character":0},"end":{"line":0,"character":99}}"#),
    ];
    for value in invalid {
        assert!(!crate::json::plain_term_goal_result(&value), "accepted {value}");
    }
}

#[test]
fn decoded_text_and_total_wire_have_independent_ceilings() {
    assert!(crate::json::plain_term_goal_result(&result(&"a".repeat(64 * 1024), RANGE)));
    assert!(!crate::json::plain_term_goal_result(&result(&"a".repeat(64 * 1024 + 1), RANGE)));
    // Escaped ASCII occupies six wire bytes but one decoded byte. Unicode
    // occupies its UTF-8 byte count, not merely its scalar count.
    let escaped = format!("{{\"goal\":\"{}\",\"range\":{RANGE}}}", "\\u0061".repeat(64 * 1024));
    assert!(crate::json::plain_term_goal_result(&escaped));
    assert!(!crate::json::plain_term_goal_result(&result(&"😀".repeat(16 * 1024 + 1), RANGE)));
    let oversized = format!("{{\"goal\":\"A\",\"range\":{RANGE},\"extra\":\"{}\"}}", "x".repeat(1024 * 1024));
    assert!(!crate::json::plain_term_goal_result(&oversized));
}

#[test]
fn correlates_real_term_goal_shapes_and_retains_null_as_no_information() {
    let response = reply(&result("x : A\n⊢ A", RANGE));
    let (client, server) = pair(&response, false);
    let stats = correlate_transcripts(&client, &server).unwrap();
    assert_eq!(stats.matched_responses, 3);
    assert_eq!(stats.method_contract_responses, 3);
    assert_eq!(stats.semantic_query_results, 1);
    assert_eq!(stats.no_information_query_results, 0);
    assert_eq!(stats.semantic_query_errors, 0);
    assert!(render_correlation(stats).contains("\"methodResponseSchema\":\"fln.lsp-method-response/4\""));

    let (client, server) = pair(&reply("null"), false);
    let stats = correlate_transcripts(&client, &server).unwrap();
    assert_eq!(stats.semantic_query_results, 0);
    assert_eq!(stats.no_information_query_results, 1);
}

#[test]
fn preserves_semantic_errors_and_cancelled_target_accounting() {
    for code in [-32602, -32803, -32800] {
        let response = format!("{{\"jsonrpc\":\"2.0\",\"id\":1.25e2,\"error\":{{\"code\":{code},\"message\":\"query did not complete\"}}}}");
        let (client, server) = pair(&response, true);
        let stats = correlate_transcripts(&client, &server).unwrap();
        assert_eq!(stats.semantic_query_errors, 1);
        assert_eq!(stats.semantic_query_results, 0);
        assert_eq!(stats.no_information_query_results, 0);
        assert_eq!(stats.server.error_responses, 1);
        assert_eq!(stats.client.other_request_cancellation_targets, 1);
        assert_eq!(stats.cancelled_target_request_cancelled_responses, u64::from(code == -32800));
        assert_eq!(stats.cancelled_target_other_error_responses, u64::from(code != -32800));
    }
    let response = reply(&result("⊢ A", RANGE));
    let (client, server) = pair(&response, true);
    let stats = correlate_transcripts(&client, &server).unwrap();
    assert_eq!(stats.cancelled_target_result_responses, 1);
    assert_eq!(stats.semantic_query_results, 1);
}

#[test]
fn refuses_other_response_shapes_errors_and_normalized_numeric_ids() {
    for value in ["0", "{}", "[]", r#"{"rendered":"no goals","goals":[]}"#] {
        let (client, server) = pair(&reply(value), false);
        let error = correlate_transcripts(&client, &server).unwrap_err();
        assert!(error.contains("plain-term-goal method contract"), "{error}");
    }
    for code in [-32601, -32603, 0] {
        let response = format!("{{\"jsonrpc\":\"2.0\",\"id\":1.25e2,\"error\":{{\"code\":{code},\"message\":\"wrong error\"}}}}");
        let (client, server) = pair(&response, false);
        let error = correlate_transcripts(&client, &server).unwrap_err();
        assert!(error.contains("plain-term-goal method contract"), "{error}");
    }
    let response = reply(&result("⊢ A", RANGE)).replace("1.25e2", "125");
    let (client, server) = pair(&response, false);
    assert!(correlate_transcripts(&client, &server).unwrap_err().contains("unknown canonical request ID 125"));
}
