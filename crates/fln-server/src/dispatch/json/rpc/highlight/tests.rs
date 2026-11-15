use super::*;

fn response(value: RawField<'_>, limit: usize) -> Result<String> {
    Request::decode(value, WireFormat::V0)?.response(limit)
}

fn request(query: &str, message: &str) -> String {
    format!(
        r#"{{"query":{},"msg":{message}}}"#,
        crate::json_string(query)
    )
}
fn highlight(query: &str, message: &str) -> String {
    response(RawField::Value(&request(query, message)), MAX_INPUT_BYTES).unwrap()
}

#[test]
fn text_results_use_the_pinned_tagged_text_wire_shape() {
    assert_eq!(
        highlight("goal", r#"{"text":"one goal remains"}"#),
        r#"{"append":[{"text":"one "},{"tag":["highlighted",{"text":"goal"}]},{"text":" remains"}]}"#
    );
    assert_eq!(
        highlight("P", r#"{"text":"P"}"#),
        r#"{"tag":["highlighted",{"text":"P"}]}"#
    );
    for query in ["", "missing", "p"] {
        assert_eq!(highlight(query, r#"{"text":"P"}"#), r#"{"text":"P"}"#);
    }
    assert_eq!(highlight("x", r#"{"text":""}"#), r#"{"text":""}"#);
}

#[test]
fn searches_cross_unicode_text_nodes_without_flattening_the_append_tree() {
    assert_eq!(
        highlight(
            "βγ😀",
            r#"{"append":[{"text":"alphaβ"},{"text":"γ😀tail"}]}"#
        ),
        r#"{"append":[{"append":[{"text":"alpha"},{"tag":["highlighted",{"text":"β"}]}]},{"append":[{"tag":["highlighted",{"text":"γ😀"}]},{"text":"tail"}]}]}"#
    );
    assert_eq!(
        highlight(
            "abc",
            r#"{"append":[{"text":"a"},{"append":[]},{"append":[{"text":""},{"text":"b"}]},{"text":"c"}]}"#
        ),
        r#"{"append":[{"tag":["highlighted",{"text":"a"}]},{"append":[]},{"append":[{"text":""},{"tag":["highlighted",{"text":"b"}]}]},{"tag":["highlighted",{"text":"c"}]}]}"#
    );
    assert_eq!(highlight("", r#"{"append":[]}"#), r#"{"append":[]}"#);
}

#[test]
fn overlapping_matches_follow_the_pins_leaf_sensitive_emission_order() {
    // WidgetRequests.highlightStringMatches? does not merge overlaps. Its
    // per-leaf cursor stops after a match reaches that leaf's end.
    assert_eq!(
        highlight("ana", r#"{"text":"banana"}"#),
        r#"{"append":[{"text":"b"},{"tag":["highlighted",{"text":"ana"}]},{"tag":["highlighted",{"text":"ana"}]}]}"#
    );
    assert_eq!(
        highlight("aaa", r#"{"append":[{"text":"aaa"},{"text":"a"}]}"#),
        r#"{"append":[{"tag":["highlighted",{"text":"aaa"}]},{"tag":["highlighted",{"text":"a"}]}]}"#
    );
    assert_eq!(
        highlight("aaa", r#"{"text":"aaaa"}"#),
        r#"{"append":[{"tag":["highlighted",{"text":"aaa"}]},{"tag":["highlighted",{"text":"aaa"}]}]}"#
    );
}

fn words(maximum: usize) -> Vec<String> {
    let mut all = vec![String::new()];
    let mut layer = vec![String::new()];
    for _ in 0..maximum {
        let mut next = Vec::new();
        for word in &layer {
            for suffix in ["a", "β", "😀"] {
                next.push(format!("{word}{suffix}"));
            }
        }
        all.extend(next.iter().cloned());
        layer = next;
    }
    all
}

#[test]
fn kmp_agrees_with_independent_byte_windows_for_all_small_unicode_words() {
    for query in words(3) {
        for text in words(5) {
            let expected: Vec<_> = if query.is_empty() {
                Vec::new()
            } else {
                text.as_bytes()
                    .windows(query.len())
                    .enumerate()
                    .filter_map(|(index, window)| (window == query.as_bytes()).then_some(index))
                    .collect()
            };
            let actual = match_positions(&query, &text).unwrap();
            assert_eq!(actual, expected, "query={query:?}, text={text:?}");
            for index in actual {
                assert!(text.is_char_boundary(index));
                assert!(text.is_char_boundary(index + query.len()));
            }
        }
    }
}

#[test]
fn json_escapes_round_trip_and_response_limits_count_encoded_utf8_bytes() {
    let original = "é😀\n\"\\\0\u{0008}\u{000c}\u{001f}";
    let message = format!(r#"{{"text":{}}}"#, crate::json_string(original));
    let plain = highlight("", &message);
    assert_eq!(
        decoded_string_field(RawField::Value(&plain), "text"),
        DecodedField::Valid(original.into())
    );
    let input = request("😀", &message);
    let result = response(RawField::Value(&input), MAX_INPUT_BYTES).unwrap();
    assert_eq!(
        response(RawField::Value(&input), result.len()).unwrap(),
        result
    );
    assert!(matches!(
        response(RawField::Value(&input), result.len() - 1),
        Err(Error::Limit(_))
    ));
    assert_eq!(parse_value_end(&result, 0, 0), Some(result.len()));
    assert_eq!(
        response(RawField::Value(&input), MAX_INPUT_BYTES).unwrap(),
        result
    );
}

#[test]
fn malformed_or_ambiguous_inputs_are_not_successful_empty_searches() {
    for input in [
        "null",
        "[]",
        "{}",
        r#"{"query":0,"msg":{"text":"x"}}"#,
        r#"{"query":"x","qu\u0065ry":"y","msg":{"text":"x"}}"#,
        r#"{"query":"x","msg":{"text":"x"},"m\u0073g":{"text":"y"}}"#,
        r#"{"query":"x","msg":{"text":"x","te\u0078t":"y"}}"#,
        r#"{"query":"x","msg":{"text":"x","append":[]}}"#,
        r#"{"query":"x","msg":{"text":false}}"#,
        r#"{"query":"x","msg":{"text":"\ud800"}}"#,
        r#"{"query":"x","msg":{"append":{}}}"#,
        r#"{"query":"x","msg":{"append":[{"text":"x"},]}}"#,
        r#"{"query":"x","msg":{"append":[null]}}"#,
        r#"{"query":"x","msg":{"unknown":"x"}}"#,
    ] {
        assert!(
            matches!(
                response(RawField::Value(input), MAX_INPUT_BYTES),
                Err(Error::Invalid(_))
            ),
            "{input}"
        );
    }
    assert!(matches!(
        response(RawField::Missing, MAX_INPUT_BYTES),
        Err(Error::Invalid(_))
    ));
}

#[test]
fn unsupported_objects_refuse_instead_of_being_copied_as_trusted_refs() {
    for tag in [
        r#"{"goal":{}}"#,
        r#"{"widget":[{}, {"text":"x"}]}"#,
        r#"{"trace":[0,"class",{"text":"x"},true,{"lazy":{"p":"0"}}]}"#,
    ] {
        let message = format!(r#"{{"append":[{{"text":"x"}},{{"tag":[{tag},{{"text":""}}]}}]}}"#);
        assert!(matches!(
            response(RawField::Value(&request("x", &message)), MAX_INPUT_BYTES),
            Err(Error::Unsupported(_))
        ));
    }
}

#[test]
fn expression_search_crosses_code_and_message_nodes_and_preserves_info_tags() {
    for format in [WireFormat::V0, WireFormat::V1] {
        let outer = format!(
            r#"{{"info":{},"subexprPos":"/0","diffStatus":"willChange"}}"#,
            format.reference(17)
        );
        let inner = format!(r#"{{"info":{},"subexprPos":"/0/1"}}"#, format.reference(19));
        let message = format!(
            r#"{{"append":[{{"text":"before α"}},{{"tag":[{{"expr":{{"tag":[{outer},{{"append":[{{"text":"β"}},{{"tag":[{inner},{{"text":"γ"}}]}}]}}]}}}},{{"text":""}}]}},{{"text":"δ after"}}]}}"#
        );
        let input = request("αβγδ", &message);
        let decoded = Request::decode(RawField::Value(&input), format).unwrap();
        let mut references: Vec<_> = decoded.references().collect();
        references.sort_unstable();
        assert_eq!(references, [17, 19]);
        let expected = format!(
            r#"{{"append":[{{"append":[{{"text":"before "}},{{"tag":["highlighted",{{"text":"α"}}]}}]}},{{"tag":[{{"expr":{{"tag":[{outer},{{"append":[{{"tag":["highlighted",{{"text":"β"}}]}},{{"tag":[{inner},{{"tag":["highlighted",{{"text":"γ"}}]}}]}}]}}]}}}},{{"text":""}}]}},{{"append":[{{"tag":["highlighted",{{"text":"δ"}}]}},{{"text":" after"}}]}}]}}"#
        );
        assert_eq!(decoded.response(MAX_INPUT_BYTES).unwrap(), expected);
        assert_eq!(parse_value_end(&expected, 0, 0), Some(expected.len()));
        for query in ["", "missing"] {
            let input = request(query, &message);
            let decoded = Request::decode(RawField::Value(&input), format).unwrap();
            assert_eq!(decoded.response(MAX_INPUT_BYTES).unwrap(), message);
            assert_eq!(decoded.references().count(), 2);
        }
    }
}

#[test]
fn expression_tags_preserve_the_pins_fallback_search_and_render_order() {
    let message = r#"{"append":[{"tag":[{"expr":{"text":"ab"}},{"text":"XX"}]},{"text":"cd"}]}"#;
    // rewrite replaces the entire message tag for discovery ("abcd"), but
    // rendering advances through its fallback too ("abXXcd").
    assert_eq!(
        highlight("bc", message),
        r#"{"append":[{"tag":[{"expr":{"append":[{"text":"a"},{"tag":["highlighted",{"text":"b"}]}]}},{"append":[{"tag":["highlighted",{"text":"X"}]},{"text":"X"}]}]},{"text":"cd"}]}"#
    );
    assert_eq!(highlight("XX", message), message);

    // The pin leaves invalid raw UTF-8 positions unspecified. A client-created
    // fallback can cause one; reject it without slicing at a non-boundary.
    let input = request(
        "cd",
        r#"{"append":[{"tag":[{"expr":{"text":"a"}},{"text":"😀"}]},{"text":"bcd"}]}"#,
    );
    assert!(matches!(
        response(RawField::Value(&input), MAX_INPUT_BYTES),
        Err(Error::Invalid(_))
    ));
}

#[test]
fn expression_metadata_is_validated_and_reencoded_without_trusting_raw_fields() {
    let position = format!("/{}", vec!["3"; 40].join("/"));
    let message = format!(
        r#"{{"tag":[{{"expr":{{"tag":[{{"info":{{"p":"00017"}},"subexprPos":"{position}","diffStatus":null,"ignored":{{"p":"999"}}}},{{"text":"x"}}]}}}},{{"text":""}}]}}"#
    );
    let input = request("x", &message);
    let decoded = Request::decode(RawField::Value(&input), WireFormat::V0).unwrap();
    assert_eq!(decoded.references().collect::<Vec<_>>(), [17]);
    assert_eq!(
        decoded.response(MAX_INPUT_BYTES).unwrap(),
        format!(
            r#"{{"tag":[{{"expr":{{"tag":[{{"info":{{"p":"17"}},"subexprPos":"{position}"}},{{"tag":["highlighted",{{"text":"x"}}]}}]}}}},{{"text":""}}]}}"#
        )
    );
    for metadata in [
        r#""highlighted""#,
        r#"{}"#,
        r#"{"info":{"p":"17"}}"#,
        r#"{"info":{"p":"17"},"subexprPos":""}"#,
        r#"{"info":{"p":"17"},"subexprPos":"0"}"#,
        r#"{"info":{"p":"17"},"subexprPos":"/4"}"#,
        r#"{"info":{"p":"17"},"subexprPos":"/0/"}"#,
        r#"{"info":{"p":"17"},"subexprPos":"/00"}"#,
        r#"{"info":{"p":"17"},"subexprPos":"/","subexprPo\u0073":"/1"}"#,
        r#"{"info":{"p":"17"},"in\u0066o":{"p":"18"},"subexprPos":"/"}"#,
        r#"{"info":{"p":"17"},"subexprPos":"/","diffStatus":"unknown"}"#,
        r#"{"info":{"p":"17"},"subexprPos":"/","diffStatus":false}"#,
        r#"{"info":{"p":"17"},"subexprPos":"/","diffStatus":null,"diffStatus":null}"#,
        r#"{"info":{"p":17},"subexprPos":"/"}"#,
        r#"{"info":{"p":"17","p":"18"},"subexprPos":"/"}"#,
        r#"{"info":{"__rpcref":"17"},"subexprPos":"/"}"#,
        r#"{"info":{"p":"17","__rpcref":"17"},"subexprPos":"/"}"#,
    ] {
        let message = format!(
            r#"{{"tag":[{{"expr":{{"tag":[{metadata},{{"text":"x"}}]}}}},{{"text":""}}]}}"#
        );
        assert!(
            matches!(
                response(RawField::Value(&request("", &message)), MAX_INPUT_BYTES),
                Err(Error::Invalid(_))
            ),
            "{metadata}"
        );
    }
}

#[test]
fn malformed_expression_tags_do_not_become_valid_empty_matches() {
    for message in [
        r#"{"tag":{}}"#,
        r#"{"tag":[]}"#,
        r#"{"tag":[{"expr":{"text":"x"}}]}"#,
        r#"{"tag":[{"expr":{"text":"x"}},{"text":""},{"text":""}]}"#,
        r#"{"tag":["highlighted",{"text":"x"}]}"#,
        r#"{"tag":[{"unknown":{}},{"text":"x"}]}"#,
        r#"{"tag":[{"expr":{"text":"x"},"expr":{"text":"y"}},{"text":""}]}"#,
        r#"{"tag":[{"expr":null},{"text":""}]}"#,
        r#"{"tag":[{"expr":{"text":"x"}},null]}"#,
    ] {
        assert!(
            matches!(
                response(RawField::Value(&request("", message)), MAX_INPUT_BYTES),
                Err(Error::Invalid(_))
            ),
            "{message}"
        );
    }
}

fn nested(depth: usize, text: &str) -> String {
    let mut message = format!(r#"{{"text":{}}}"#, crate::json_string(text));
    for _ in 0..depth {
        message = format!(r#"{{"append":[{message}]}}"#);
    }
    message
}

#[test]
fn tree_and_match_limits_have_positive_boundaries_and_do_not_poison_retries() {
    let at_limit = request("", &nested(MAX_DEPTH, "ok"));
    assert!(response(RawField::Value(&at_limit), MAX_INPUT_BYTES).is_ok());
    let over = request("", &nested(MAX_DEPTH + 1, "ok"));
    assert!(matches!(
        response(RawField::Value(&over), MAX_INPUT_BYTES),
        Err(Error::Limit(_))
    ));
    let leaves = std::iter::repeat_n(r#"{"text":""}"#, MAX_NODES)
        .collect::<Vec<_>>()
        .join(",");
    let over = request("", &format!(r#"{{"append":[{leaves}]}}"#));
    assert!(matches!(
        response(RawField::Value(&over), MAX_INPUT_BYTES),
        Err(Error::Limit(_))
    ));
    assert_eq!(
        match_positions("a", &"a".repeat(MAX_MATCHES))
            .unwrap()
            .len(),
        MAX_MATCHES
    );
    assert!(matches!(
        match_positions("a", &"a".repeat(MAX_MATCHES + 1)),
        Err(Error::Limit(_))
    ));
    assert!(response(RawField::Value(&at_limit), MAX_INPUT_BYTES).is_ok());
}

#[test]
fn input_query_and_nested_scan_work_are_bounded_separately() {
    let huge = " ".repeat(MAX_INPUT_BYTES + 1);
    assert!(matches!(
        response(RawField::Value(&huge), MAX_INPUT_BYTES),
        Err(Error::Limit(_))
    ));
    let huge_query = request(&"a".repeat(MAX_QUERY_BYTES + 1), r#"{"text":""}"#);
    assert!(matches!(
        response(RawField::Value(&huge_query), MAX_INPUT_BYTES),
        Err(Error::Limit(_))
    ));
    let expensive = request("", &nested(MAX_DEPTH, &"a".repeat(300000)));
    assert!(expensive.len() < MAX_INPUT_BYTES);
    assert_eq!(
        response(RawField::Value(&expensive), MAX_INPUT_BYTES),
        Err(Error::Limit("RPC highlight parsing exceeds its work limit"))
    );
    assert_eq!(
        highlight("x", r#"{"text":"x"}"#),
        r#"{"tag":["highlighted",{"text":"x"}]}"#
    );
}
