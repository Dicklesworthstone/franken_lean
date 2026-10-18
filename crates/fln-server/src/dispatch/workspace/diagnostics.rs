//! Bounded, current-version diagnostic presentations populated by real checks.
//! A missing or refused snapshot is not evidence that the document is clean.
use super::*;
use json::rpc::diagnostics::Batch;

const MAX_CACHE_BYTES: usize = 16 * 1024 * 1024;

struct Entry {
    version: i64,
    result: Result<Batch, &'static str>,
    bytes: usize,
}

pub(super) struct Cache {
    entries: BTreeMap<String, Entry>,
    bytes: usize,
    max_entries: usize,
    max_bytes: usize,
}

impl Default for Cache {
    fn default() -> Self {
        Self {
            entries: BTreeMap::new(),
            bytes: 0,
            max_entries: session::MAX_OPEN_DOCUMENTS,
            max_bytes: MAX_CACHE_BYTES,
        }
    }
}

impl Cache {
    fn remove(&mut self, uri: &str) {
        if let Some(entry) = self.entries.remove(uri) {
            self.bytes -= entry.bytes;
        }
    }

    pub(super) fn record(
        &mut self,
        uri: &str,
        text: &str,
        sources: &[OpenDocumentSource<'_>],
        notifications: &[String],
    ) {
        // Retire the old result first, including same-version saves and native
        // failures. A replacement which exceeds a budget cannot revive it.
        self.remove(uri);
        self.prune(sources);
        let Some(source) = sources.iter().find(|source| {
            source.uri == uri && source.text == Some(text)
        }) else {
            return;
        };
        let mut result = Batch::from_notifications(notifications, uri, source.version);
        let overhead = uri.len().checked_add(std::mem::size_of::<Entry>());
        let Some(overhead) = overhead else {
            return;
        };
        let mut bytes = match &result {
            Ok(batch) => batch.retained_bytes().and_then(|size| size.checked_add(overhead)),
            Err(_) => Some(overhead),
        };
        if bytes.is_none_or(|size| {
            self.bytes.checked_add(size).is_none_or(|total| total > self.max_bytes)
        }) {
            result = Err("current diagnostic snapshot exceeds its retention budget");
            bytes = Some(overhead);
        }
        let Some(bytes) = bytes else {
            return;
        };
        let Some(total) = self.bytes.checked_add(bytes).filter(|total| *total <= self.max_bytes)
        else {
            return;
        };
        if self.entries.len() >= self.max_entries {
            return;
        }
        self.entries.insert(uri.to_owned(), Entry {
            version: source.version,
            result,
            bytes,
        });
        self.bytes = total;
    }

    pub(super) fn prune(&mut self, sources: &[OpenDocumentSource<'_>]) {
        let bytes = &mut self.bytes;
        self.entries.retain(|uri, entry| {
            let keep = sources.iter().any(|source| {
                source.uri == uri && source.version == entry.version && source.text.is_some()
            });
            if !keep {
                *bytes -= entry.bytes;
            }
            keep
        });
    }

    pub(super) fn get(&self, uri: &str, version: i64) -> Result<&Batch, &'static str> {
        let entry = self.entries.get(uri)
            .filter(|entry| entry.version == version)
            .ok_or("current native diagnostics are unavailable")?;
        entry.result.as_ref().map_err(|error| *error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    const URI: &str = "file:///Diagnostics.lean";
    const DEP: &str = "file:///Dep.lean";
    struct Provider {
        checks: usize,
    }
    impl WorkspaceChecker for Provider {
        fn semantic_queries(&self) -> bool {
            true
        }
        fn check(&mut self, uri: &str, text: &str, documents: &[OpenDocumentSource<'_>]) -> Vec<String> {
            self.checks += 1;
            if text == "failure" {
                return vec![diagnostic_callback_failure_notification(uri)];
            }
            if text == "clean" {
                return vec![clear_diagnostics_notification(uri)];
            }
            let dependency = documents.iter().find(|doc| doc.uri == DEP)
                .and_then(|doc| doc.text).unwrap_or("absent");
            let version = documents.iter().find(|doc| doc.uri == uri).unwrap().version;
            vec![format!(
                r#"{{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{{"uri":{},"version":{version},"diagnostics":[{{"range":{{"start":{{"line":0,"character":0}},"end":{{"line":0,"character":0}}}},"message":{},"severity":1}}]}}}}"#,
                crate::json_string(uri), crate::json_string(&format!("{text}: {dependency}"))
            )]
        }
        fn affected(&mut self, changed: &[String], _: &[OpenDocumentSource<'_>]) -> Vec<String> {
            if changed.iter().any(|uri| uri == DEP) {
                vec![URI.to_owned()]
            } else {
                Vec::new()
            }
        }
    }
    fn check(adapter: &mut Adapter<'_>, docs: &DocumentSession) {
        assert_eq!(
            check_document(&mut Vec::new(), URI, docs.text(URI).unwrap(), adapter, docs).unwrap(),
            DiagnosticCompletion::Complete
        );
    }
    fn connect(sessions: &mut rpc::Sessions, docs: &DocumentSession, adapter: &mut Adapter<'_>) -> String {
        let input = format!(r#"{{"uri":"{URI}"}}"#);
        let response = sessions.request("$/lean/rpc/connect", RawField::Value(&input),
            &RequestId::Number("1".into()), docs, adapter);
        response.split("\"sessionId\":\"").nth(1).unwrap().split('"').next().unwrap().to_owned()
    }
    fn request(sessions: &mut rpc::Sessions, id: &str, docs: &DocumentSession, adapter: &mut Adapter<'_>, params: &str) -> String {
        let input = format!(
            r#"{{"textDocument":{{"uri":"{URI}"}},"position":{{"line":0,"character":0}},"sessionId":"{id}","method":"Lean.Widget.getInteractiveDiagnostics","params":{params}}}"#
        );
        sessions.request("$/lean/rpc/call", RawField::Value(&input),
            &RequestId::Number("2".into()), docs, adapter)
    }
    #[test]
    fn repeated_rpc_reads_use_checked_diagnostics_without_rechecking_source() {
        let mut provider = Provider { checks: 0 };
        let mut adapter = Adapter(&mut provider, semantic::index::Revision::new(), Cache::default());
        let mut docs = DocumentSession::new();
        docs.open(URI.into(), 1, "first".into()).unwrap();
        check(&mut adapter, &docs);
        let mut sessions = rpc::Sessions::default();
        let id = connect(&mut sessions, &docs, &mut adapter);
        for _ in 0..3 {
            let result = request(&mut sessions, &id, &docs, &mut adapter, "{}");
            assert!(result.contains(r#""message":{"text":"first: absent"}"#), "{result}");
        }
        let excluded = request(&mut sessions, &id, &docs, &mut adapter, r#"{"lineRange":{"start":2,"end":3}}"#);
        assert!(excluded.contains(r#""result":[]"#), "{excluded}");
        let invalid = request(&mut sessions, &id, &docs, &mut adapter, r#"{"lineRange":false}"#);
        assert!(invalid.contains(r#""code":-32602"#), "{invalid}");
        drop(adapter);
        assert_eq!(provider.checks, 1);
    }
    #[test]
    fn same_version_saves_and_failures_replace_old_results() {
        let mut provider = Provider { checks: 0 };
        let mut adapter = Adapter(&mut provider, semantic::index::Revision::new(), Cache::default());
        let mut docs = DocumentSession::new();
        docs.open(URI.into(), 1, "first".into()).unwrap();
        check(&mut adapter, &docs);
        let mut sessions = rpc::Sessions::default();
        let id = connect(&mut sessions, &docs, &mut adapter);
        docs.save_with_text(URI, "second".into()).unwrap();
        check(&mut adapter, &docs);
        let result = request(&mut sessions, &id, &docs, &mut adapter, "{}");
        assert!(result.contains("second: absent") && !result.contains("first: absent"));
        docs.change(URI, 2, "failure".into()).unwrap();
        assert_eq!(check_document(&mut Vec::new(), URI, "failure", &mut adapter, &docs).unwrap(), DiagnosticCompletion::Failed);
        let result = request(&mut sessions, &id, &docs, &mut adapter, "{}");
        assert!(result.contains(r#""code":-32803"#) && !result.contains(r#""result":[]"#));
        docs.save_with_text(URI, "clean".into()).unwrap();
        check(&mut adapter, &docs);
        assert!(request(&mut sessions, &id, &docs, &mut adapter, "{}").contains(r#""result":[]"#));
    }
    #[test]
    fn dependency_refresh_updates_diagnostics_at_an_unchanged_importer_version() {
        let mut provider = Provider { checks: 0 };
        let mut adapter = Adapter(&mut provider, semantic::index::Revision::new(), Cache::default());
        let mut docs = DocumentSession::new();
        docs.open(URI.into(), 1, "consumer".into()).unwrap();
        docs.open(DEP.into(), 1, "old".into()).unwrap();
        check(&mut adapter, &docs);
        docs.change(DEP, 2, "new".into()).unwrap();
        refresh(&mut Vec::new(), &docs, &mut PendingDiagnosticWaits::new(),
            &mut BTreeMap::new(), &mut adapter, &[DEP.into()], Some(DEP)).unwrap();
        let result = adapter.diagnostics(URI, 1).unwrap().response(None, 4096).unwrap();
        assert!(result.contains("consumer: new") && !result.contains("consumer: old"));
    }
    #[test]
    fn close_invalidation_and_expiry_cannot_reuse_a_previous_snapshot() {
        let mut provider = Provider { checks: 0 };
        let mut adapter = Adapter(&mut provider, semantic::index::Revision::new(), Cache::default());
        let mut docs = DocumentSession::new();
        docs.open(URI.into(), 1, "first".into()).unwrap();
        check(&mut adapter, &docs);
        assert!(adapter.diagnostics(URI, 2).is_err());
        let mut sessions = rpc::Sessions::default();
        let id = connect(&mut sessions, &docs, &mut adapter);
        docs.reject_change(URI, 2).unwrap();
        adapter.affected(&[URI.into()], &docs.sources());
        assert!(adapter.diagnostics(URI, 1).is_err());
        assert!(request(&mut sessions, &id, &docs, &mut adapter, "{}").contains(r#""code":-32803"#));
        docs.close(URI).unwrap();
        adapter.affected(&[URI.into()], &docs.sources());
        assert_eq!(adapter.2.bytes, 0);
        sessions.sweep(Instant::now() + std::time::Duration::from_secs(31));
        docs.open(URI.into(), 1, "new document".into()).unwrap();
        check(&mut adapter, &docs);
        assert!(request(&mut sessions, &id, &docs, &mut adapter, "{}").contains(r#""code":-32900"#));
    }
    #[test]
    fn capacity_refusal_retires_the_old_result_and_releases_all_bytes_on_close() {
        let mut cache = Cache::default();
        let sources = [OpenDocumentSource { uri: URI, version: 1, text: Some("source") }];
        cache.record(URI, "source", &sources, &[clear_diagnostics_notification(URI)]);
        assert_eq!(cache.get(URI, 1).unwrap().response(None, 2).unwrap(), "[]");
        cache.max_bytes = 0;
        cache.record(URI, "source", &sources, &[clear_diagnostics_notification(URI)]);
        assert!(cache.get(URI, 1).is_err());
        assert_eq!(cache.bytes, 0);
        cache.max_bytes = MAX_CACHE_BYTES;
        cache.max_entries = 0;
        cache.record(URI, "source", &sources, &[clear_diagnostics_notification(URI)]);
        assert!(cache.get(URI, 1).is_err());
        cache.max_entries = 1;
        cache.record(URI, "source", &sources, &[clear_diagnostics_notification(URI)]);
        assert!(cache.bytes > 0);
        cache.prune(&[]);
        assert_eq!(cache.bytes, 0);
        assert!(cache.entries.is_empty());
    }
}
