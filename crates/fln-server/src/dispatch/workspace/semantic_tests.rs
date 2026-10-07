use super::*;
use crate::dispatch::semantic::{Answer, Query};
use crate::dispatch::semantic::index::{Annotation, Revision, SemanticIndex};
use std::io::Cursor;

#[derive(Default)]
struct CachedProvider {
    index: Option<SemanticIndex>,
    hits: usize,
    refusals: usize,
}
impl WorkspaceChecker for CachedProvider {
    fn semantic_queries(&self) -> bool { true }
    fn query_with_revision(
        &mut self, query: Query<'_>, revision: &Revision, documents: &[OpenDocumentSource<'_>],
    ) -> Result<Option<Answer>, String> {
        if self.index.is_none() {
            self.index = Some(SemanticIndex::new(query, revision, vec![Annotation {
                selection: 0..query.text.len(),
                answer: Answer::Hover { contents: "native cached answer".into(), range: 0..query.text.len() },
            }]).map_err(|error| error.to_string())?);
        }
        let result = self.index.as_ref().unwrap().query(query, revision, documents);
        if result.is_err() { self.refusals += 1; } else { self.hits += 1; }
        result.map_err(|error| error.to_string())
    }
    fn check(&mut self, uri: &str, _: &str, _: &[OpenDocumentSource<'_>]) -> Vec<String> {
        vec![clear_diagnostics_notification(uri)]
    }
    fn affected(&mut self, _: &[String], _: &[OpenDocumentSource<'_>]) -> Vec<String> { Vec::new() }
}
fn run(provider: &mut dyn WorkspaceChecker, events: &[&str]) -> String {
    let mut input = Vec::new();
    for message in [
        r#"{"jsonrpc":"2.0","id":0,"method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
    ].into_iter().chain(events.iter().copied()).chain([
        r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]) { transport::write_message(&mut input, message.as_bytes()).unwrap(); }
    let mut output = Vec::new();
    assert!(serve_workspace(&mut Cursor::new(input), &mut output, provider).unwrap().clean);
    String::from_utf8(output).unwrap()
}
const OPEN: &str = r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Main.lean","version":1,"text":"old"}}}"#;
const FIRST: &str = r#"{"jsonrpc":"2.0","id":1,"method":"textDocument/hover","params":{"textDocument":{"uri":"file:///Main.lean"},"position":{"line":0,"character":1}}}"#;
const SECOND: &str = r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/hover","params":{"textDocument":{"uri":"file:///Main.lean"},"position":{"line":0,"character":1}}}"#;

#[test]
fn unchanged_workspace_queries_reuse_one_revision() {
    let mut provider = CachedProvider::default();
    let output = run(&mut provider, &[OPEN, FIRST, SECOND]);
    assert_eq!((provider.hits, provider.refusals), (2, 0));
    assert!(output.contains(r#""id":2,"result":{"contents"#), "{output}");
}

#[test]
fn same_version_save_edits_and_dependency_events_cannot_reuse_old_answers() {
    for mutation in [
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///Main.lean"},"text":"new"}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Main.lean","version":2},"contentChanges":[{"text":"new"}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Dep.lean","version":1,"text":"dep"}}}"#,
        r#"{"jsonrpc":"2.0","method":"workspace/didChangeWatchedFiles","params":{"changes":[{"uri":"file:///Dep.lean","type":2}]}}"#,
    ] {
        let mut provider = CachedProvider::default();
        let output = run(&mut provider, &[OPEN, FIRST, mutation, SECOND]);
        assert_eq!((provider.hits, provider.refusals), (1, 1), "{mutation}: {output}");
        assert!(output.contains(r#""id":2,"error":{"code":-32803"#), "{output}");
        assert!(!output.contains(r#""id":2,"result"#), "{output}");
    }
}

#[test]
fn close_reopen_and_a_new_session_never_revive_identical_source() {
    let mut provider = CachedProvider::default();
    let close = r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///Main.lean"}}}"#;
    run(&mut provider, &[OPEN, FIRST, close, OPEN, SECOND]);
    assert_eq!((provider.hits, provider.refusals), (1, 1));
    run(&mut provider, &[OPEN, FIRST]);
    assert_eq!((provider.hits, provider.refusals), (1, 2));
}

#[test]
fn invalidated_source_is_unavailable_then_recovery_still_refuses_old_index() {
    let mut provider = CachedProvider::default();
    let invalid = r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Main.lean","version":2},"contentChanges":false}}"#;
    let save = r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///Main.lean"},"text":"old"}}"#;
    let output = run(&mut provider, &[OPEN, FIRST, invalid, SECOND, save, FIRST]);
    assert!(output.contains("accepted editor source is unavailable"), "{output}");
    assert_eq!((provider.hits, provider.refusals), (1, 1));
}

#[test]
fn existing_query_implementations_keep_their_native_results() {
    struct Legacy;
    impl WorkspaceChecker for Legacy {
        fn semantic_queries(&self) -> bool { true }
        fn query(&mut self, _: Query<'_>, _: &[OpenDocumentSource<'_>]) -> Result<Option<Answer>, String> {
            Ok(Some(Answer::Hover { contents: "existing native producer".into(), range: 0..3 }))
        }
        fn check(&mut self, uri: &str, _: &str, _: &[OpenDocumentSource<'_>]) -> Vec<String> {
            vec![clear_diagnostics_notification(uri)]
        }
        fn affected(&mut self, _: &[String], _: &[OpenDocumentSource<'_>]) -> Vec<String> { Vec::new() }
    }
    let output = run(&mut Legacy, &[OPEN, FIRST]);
    assert!(output.contains("existing native producer"), "{output}");
    assert!(output.contains(r#""id":1,"result":{"contents"#), "{output}");
}
