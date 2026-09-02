#![forbid(unsafe_code)]

pub use fln_server::json_string;
pub const LSP_POSITION_ENCODING: &str = fln_server::LSP_POSITION_ENCODING;

// The strict-JSON façade is the one protocol foundation that compiles as an
// isolated external-crate boundary: it names no `super::`/`crate::` items, which
// is exactly why the transcript binaries include it the same way. Compiling it
// here keeps that boundary honest — if it grows a dependency on private dispatch
// state it stops being includable and this test fails to build. The deterministic
// wire and document-session modules are `pub(super)` members of `dispatch` that
// name `super::`/`crate::` items by design, so they compile as part of the
// library rather than as isolated units.
#[path = "../src/json.rs"]
mod json;

#[test]
fn modular_foundations_share_the_published_position_contract() {
    assert_eq!(LSP_POSITION_ENCODING, "utf-16");
    assert!(json_string("FrankenLean").starts_with('"'));
}

#[test]
fn strict_json_facade_parses_isolated_from_the_library() {
    // A well-formed request decodes its method and canonical request id.
    let envelope =
        json::parse_envelope(r#"{"jsonrpc":"2.0","id":7,"method":"initialize","params":{}}"#)
            .expect("a well-formed JSON-RPC request must parse");
    match envelope.method {
        json::DecodedField::Valid(ref method) => assert_eq!(method.as_str(), "initialize"),
        _ => panic!("method must decode to a valid string"),
    }
    match envelope.id {
        json::RequestIdField::Valid(json::RequestId::Number(ref digits)) => {
            assert_eq!(digits.as_str(), "7")
        }
        _ => panic!("numeric request id must decode as a number lexeme"),
    }

    // A structurally malformed request is rejected, never silently accepted.
    assert!(json::parse_envelope("{").is_err());

    // The response-facing surface extracts a present result object.
    assert!(matches!(
        json::response_result(r#"{"jsonrpc":"2.0","id":1,"result":{"ok":true}}"#),
        json::RawField::Value(_)
    ));
}
