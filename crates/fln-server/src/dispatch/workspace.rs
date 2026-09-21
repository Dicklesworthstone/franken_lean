//! Reactive document checking. Dependency selection is typed, not inferred from JSON.
use super::*;
use std::collections::BTreeSet;

/// An import-aware checker that can identify the open documents affected by a
/// source event. `affected` must include transitive consumers, or conservatively
/// include every possible consumer when dependency discovery was incomplete.
/// Returned URIs are requests to recheck, never diagnostic or source authority.
/// The dispatcher intersects them with its current session and checks each once.
pub trait WorkspaceChecker {
    fn semantic_queries(&self) -> bool {
        false
    }
    fn query(
        &mut self,
        _: semantic::Query<'_>,
        _: &[OpenDocumentSource<'_>],
    ) -> Result<Option<semantic::Answer>, String> {
        Ok(None)
    }

    fn check(&mut self, uri: &str, text: &str, documents: &[OpenDocumentSource<'_>])
    -> Vec<String>;
    fn affected(&mut self, changed: &[String], documents: &[OpenDocumentSource<'_>])
    -> Vec<String>;
}

struct Adapter<'a>(&'a mut dyn WorkspaceChecker);
impl CheckSource for Adapter<'_> {
    fn semantic_queries(&self) -> bool {
        self.0.semantic_queries()
    }
    fn query(
        &mut self,
        query: semantic::Query<'_>,
        documents: &[OpenDocumentSource<'_>],
    ) -> Result<Option<semantic::Answer>, String> {
        self.0.query(query, documents)
    }

    fn check(
        &mut self,
        uri: &str,
        text: &str,
        documents: &[OpenDocumentSource<'_>],
    ) -> Vec<String> {
        self.0.check(uri, text, documents)
    }
    fn tracks_dependencies(&self) -> bool {
        true
    }
    fn affected(
        &mut self,
        changed: &[String],
        documents: &[OpenDocumentSource<'_>],
    ) -> Vec<String> {
        self.0.affected(changed, documents)
    }
}

/// Process each document event and its reverse-dependent checks before reading
/// the next request. Every check uses the same accepted session snapshot. The
/// legacy `serve` and `serve_with_documents` callbacks retain their old behavior.
pub fn serve_workspace(
    input: &mut dyn BufRead,
    output: &mut dyn Write,
    checker: &mut dyn WorkspaceChecker,
) -> io::Result<ServerOutcome> {
    super::serve_inner(input, output, &mut Adapter(checker))
}

/// Only bounded URI/version/availability metadata is copied, never source text.
/// Comparing all entries also catches multi-document accounting recovery. A
/// successful check explicitly marks saves whose text changed without a version
/// change; stale, duplicate, malformed-envelope and out-of-lifecycle events do not.
pub(super) struct BeforeChange(BTreeMap<String, (i64, bool)>);
impl BeforeChange {
    pub(super) fn capture(session: &DocumentSession) -> Self {
        Self(
            session
                .sources()
                .iter()
                .map(|d| (d.uri.to_owned(), (d.version, d.text.is_some())))
                .collect(),
        )
    }
    pub(super) fn changed(self, session: &DocumentSession, checked: Option<&str>) -> Vec<String> {
        let after = Self::capture(session).0;
        let mut changed = BTreeSet::new();
        for (uri, before) in &self.0 {
            if after.get(uri) != Some(before) {
                changed.insert(uri.clone());
            }
        }
        for (uri, current) in &after {
            if self.0.get(uri) != Some(current) {
                changed.insert(uri.clone());
            }
        }
        if let Some(uri) = checked {
            changed.insert(uri.to_owned());
        }
        changed.into_iter().collect()
    }
}

pub(super) fn refresh(
    output: &mut dyn Write,
    session: &DocumentSession,
    waits: &mut PendingDiagnosticWaits,
    frontiers: &mut BTreeMap<String, DiagnosticFrontier>,
    checker: &mut dyn CheckSource,
    changed: &[String],
    already_checked: Option<&str>,
) -> io::Result<()> {
    let sources = session.sources();
    let requested: BTreeSet<_> = checker.affected(changed, &sources).into_iter().collect();
    // Session ordering is deterministic. Unknown, closed, duplicate and already
    // checked targets cannot invent checks, text, versions or additional work.
    let targets: Vec<_> = sources
        .iter()
        .filter(|d| Some(d.uri) != already_checked && requested.contains(d.uri))
        .copied()
        .collect();
    // Invalidate every affected frontier first, including unchanged importer
    // versions. A dependent's previous success belongs to a different world.
    for target in &targets {
        frontiers.remove(target.uri);
    }
    for target in targets {
        let completion = match target.text {
            Some(text) => check_document(output, target.uri, text, checker, session)?,
            None => {
                write_protocol_message(output, clear_diagnostics_notification(target.uri))?;
                write_protocol_message(
                    output,
                    diagnostic_callback_failure_notification(target.uri),
                )?;
                DiagnosticCompletion::Failed
            }
        };
        let checked = CheckedVersion {
            uri: target.uri.to_owned(),
            version: target.version,
            completion,
        };
        record_frontier(frontiers, &checked);
        settle_waits(
            output,
            waits.complete_ready(target.uri, target.version),
            completion,
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[derive(Default)]
    struct Checker {
        calls: Vec<(String, String)>,
        changes: Vec<Vec<String>>,
    }
    impl WorkspaceChecker for Checker {
        fn check(
            &mut self,
            uri: &str,
            text: &str,
            documents: &[OpenDocumentSource<'_>],
        ) -> Vec<String> {
            self.calls.push((uri.to_owned(), text.to_owned()));
            if text == "consumer"
                && documents
                    .iter()
                    .any(|d| d.uri == "file:///Dep.lean" && d.text.is_none())
            {
                vec![diagnostic_callback_failure_notification(uri)]
            } else {
                vec![clear_diagnostics_notification(uri)]
            }
        }
        fn affected(
            &mut self,
            changed: &[String],
            documents: &[OpenDocumentSource<'_>],
        ) -> Vec<String> {
            self.changes.push(changed.to_vec());
            if !changed.iter().any(|uri| uri == "file:///Dep.lean") {
                return Vec::new();
            }
            let mut targets: Vec<_> = documents
                .iter()
                .filter(|d| d.text == Some("consumer"))
                .map(|d| d.uri.to_owned())
                .collect();
            targets.extend([
                "file:///Dep.lean".to_owned(),
                "file:///closed.lean".to_owned(),
                "file:///Main.lean".to_owned(),
            ]);
            targets.reverse();
            targets
        }
    }
    fn run(events: &[String], checker: &mut Checker) -> String {
        let mut input = Vec::new();
        let mut messages = vec![
            r#"{"jsonrpc":"2.0","id":0,"method":"initialize","params":{}}"#.to_owned(),
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_owned(),
        ];
        messages.extend_from_slice(events);
        messages.extend([
            r#"{"jsonrpc":"2.0","id":999,"method":"shutdown"}"#.to_owned(),
            r#"{"jsonrpc":"2.0","method":"exit"}"#.to_owned(),
        ]);
        for message in messages {
            transport::write_message(&mut input, message.as_bytes()).unwrap();
        }
        let mut output = Vec::new();
        assert!(
            serve_workspace(&mut Cursor::new(input), &mut output, checker)
                .unwrap()
                .clean
        );
        String::from_utf8(output).unwrap()
    }
    fn open(name: &str, text: &str) -> String {
        format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":{{"uri":"file:///{name}.lean","version":1,"text":"{text}"}}}}}}"#
        )
    }
    fn event(method: &str, extra: &str) -> String {
        format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/{method}","params":{{"textDocument":{{"uri":"file:///Dep.lean"{extra}}}}}}}"#
        )
    }
    fn wait(id: usize) -> String {
        format!(
            r#"{{"jsonrpc":"2.0","id":{id},"method":"textDocument/waitForDiagnostics","params":{{"uri":"file:///Main.lean","version":1}}}}"#
        )
    }
    #[test]
    fn dependent_checks_are_unique_sorted_and_do_not_replay_stale_events() {
        let mut checker = Checker::default();
        run(&[
            open("Z", "consumer"), open("Main", "consumer"), open("Other", "unrelated"),
            open("Dep", "first"),
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Dep.lean","version":2},"contentChanges":[{"text":"new"}]}}"#.to_owned(),
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Dep.lean","version":1},"contentChanges":false}}"#.to_owned(),
            open("Dep", "duplicate"),
            event("didSave", ""), event("didClose", ""), event("didClose", ""),
        ], &mut checker);
        let names: Vec<_> = checker.calls.iter().map(|(uri, _)| uri.as_str()).collect();
        assert_eq!(
            names,
            [
                "file:///Z.lean",
                "file:///Main.lean",
                "file:///Other.lean",
                "file:///Dep.lean",
                "file:///Main.lean",
                "file:///Z.lean",
                "file:///Dep.lean",
                "file:///Main.lean",
                "file:///Z.lean",
                "file:///Dep.lean",
                "file:///Main.lean",
                "file:///Z.lean",
                "file:///Main.lean",
                "file:///Z.lean",
            ]
        );
        assert_eq!(checker.changes.len(), 7);
        assert_eq!(checker.calls[9].1, "new");
    }
    #[test]
    fn dependency_invalidation_changes_the_frontier_without_changing_importer_version() {
        let mut checker = Checker::default();
        let output = run(&[
            open("Dep", "ok"), open("Main", "consumer"), wait(10),
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Dep.lean","version":2},"contentChanges":false}}"#.to_owned(),
            wait(11),
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///Dep.lean"},"text":"fixed"}}"#.to_owned(),
            wait(12),
        ], &mut checker);
        assert!(output.contains(r#""id":10,"result":{}"#), "{output}");
        assert!(
            output.contains(r#""id":11,"error":{"code":-32803"#),
            "{output}"
        );
        assert!(output.contains(r#""id":12,"result":{}"#), "{output}");
        assert_eq!(
            checker
                .calls
                .iter()
                .filter(|(u, _)| u == "file:///Main.lean")
                .count(),
            3
        );
    }
    #[test]
    fn metadata_change_detection_includes_closes_invalidations_and_same_version_saves() {
        let mut session = DocumentSession::with_limits(4, 8);
        session.open("a".to_owned(), 1, "ok".to_owned()).unwrap();
        let before = BeforeChange::capture(&session);
        session.invalidate_text("a").unwrap();
        assert_eq!(before.changed(&session, None), ["a"]);
        let before = BeforeChange::capture(&session);
        session.reject_change("a", 2).unwrap();
        assert_eq!(before.changed(&session, None), ["a"]);
        let before = BeforeChange::capture(&session);
        session.close("a").unwrap();
        assert_eq!(before.changed(&session, None), ["a"]);
        assert_eq!(
            BeforeChange::capture(&session).changed(&session, Some("saved")),
            ["saved"]
        );
    }
}
