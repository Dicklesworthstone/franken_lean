//! Borrowed document authority for import-aware checking callbacks.
use super::*;

#[derive(Debug, Clone, Copy)]
pub struct OpenDocumentSource<'a> {
    pub uri: &'a str,
    pub version: i64,
    /// None means open but unavailable/invalid, NOT permission to read disk.
    pub text: Option<&'a str>,
}

pub type OnDocumentCheck<'a> =
    dyn FnMut(&str, &str, &[OpenDocumentSource<'_>]) -> Vec<String> + 'a;

pub(super) trait CheckSource {
    fn check(&mut self, uri: &str, text: &str, documents: &[OpenDocumentSource<'_>]) -> Vec<String>;
}
impl<F: FnMut(&str, &str) -> Vec<String>> CheckSource for F {
    fn check(&mut self, uri: &str, text: &str, _: &[OpenDocumentSource<'_>]) -> Vec<String> {
        self(uri, text)
    }
}
struct Contextual<'a, 'b>(&'a mut OnDocumentCheck<'b>);
impl CheckSource for Contextual<'_, '_> {
    fn check(&mut self, uri: &str, text: &str, documents: &[OpenDocumentSource<'_>]) -> Vec<String> {
        self.0(uri, text, documents)
    }
}

/// Compatibility callback: existing embedders keep their two-argument interface.
pub fn serve(
    input: &mut dyn BufRead,
    output: &mut dyn Write,
    on_did_open: &mut OnDidOpen<'_>,
) -> io::Result<ServerOutcome> {
    let mut callback = |uri: &str, text: &str| on_did_open(uri, text);
    super::serve_inner(input, output, &mut callback)
}

/// Every check sees a bounded borrowed snapshot of all accepted open documents.
/// Rejected/stale edits, retention refusal and closes use the same session state
/// as diagnostics and waits; this API does not introduce a second text store.
pub fn serve_with_documents(
    input: &mut dyn BufRead,
    output: &mut dyn Write,
    on_check: &mut OnDocumentCheck<'_>,
) -> io::Result<ServerOutcome> {
    super::serve_inner(input, output, &mut Contextual(on_check))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn callbacks_observe_accepted_versions_invalidations_and_closes() {
        let mut input = Vec::new();
        for body in [
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A.lean","version":1,"text":"first"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///B.lean","version":1,"text":"other"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///A.lean","version":2},"contentChanges":[{"text":"new"}]}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///A.lean","version":1},"contentChanges":false}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///B.lean"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///A.lean","version":3},"contentChanges":false}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///B.lean"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///A.lean"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///B.lean"}}}"#,
            r#"{"jsonrpc":"2.0","id":9,"method":"shutdown"}"#,
            r#"{"jsonrpc":"2.0","method":"exit"}"#,
        ] { transport::write_message(&mut input, body.as_bytes()).unwrap(); }
        let mut observed = Vec::new();
        let mut callback = |uri: &str, text: &str, documents: &[OpenDocumentSource<'_>]| {
            observed.push((uri.to_owned(), text.to_owned(), documents.iter().map(|d| {
                (d.uri.to_owned(), d.version, d.text.map(str::to_owned))
            }).collect::<Vec<_>>()));
            vec![wire::clear_diagnostics_notification(uri)]
        };
        let result = serve_with_documents(&mut Cursor::new(input), &mut Vec::new(), &mut callback).unwrap();
        assert!(result.clean);
        assert_eq!(observed.len(), 6);
        assert_eq!(observed[2].2[0], ("file:///A.lean".to_owned(), 2, Some("new".to_owned())));
        assert_eq!(observed[3].2[0], observed[2].2[0]);
        assert_eq!(observed[4].2[0], ("file:///A.lean".to_owned(), 3, None));
        assert_eq!(observed[5].2.len(), 1);
        assert_eq!(observed[5].2[0].0, "file:///B.lean");
    }

    #[test]
    fn unretained_documents_remain_explicitly_open_without_source() {
        let mut session = DocumentSession::with_limits(2, 3);
        session.open("file:///large".to_owned(), 7, "oversized".to_owned()).unwrap();
        session.open("file:///small".to_owned(), 2, "ok".to_owned()).unwrap();
        let sources = session.sources();
        assert_eq!(sources.len(), 2);
        assert_eq!(sources[0].version, 7);
        assert_eq!(sources[0].text, None);
        assert_eq!(sources[1].text, Some("ok"));
    }
}
