use std::collections::BTreeMap;

pub(super) const MAX_OPEN_DOCUMENTS: usize = 1024;
pub(super) const MAX_RETAINED_SOURCE_BYTES: usize = 256 * 1024 * 1024;
pub(super) const MAX_RETAINED_URI_BYTES: usize = 4 * 1024 * 1024;

#[derive(Debug)]
struct OpenDocument {
    version: i64,
    text: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RetentionRefusal {
    ByteLimit,
    AccountingOverflow,
}

impl RetentionRefusal {
    pub(super) const fn message(self) -> &'static str {
        match self {
            Self::ByteLimit => {
                "FrankenLean retained-source byte budget is exhausted; current source was checked but not retained"
            }
            Self::AccountingOverflow => {
                "FrankenLean retained-source accounting overflowed; current source was checked but not retained"
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RetentionOutcome {
    Retained,
    NotRetained(RetentionRefusal),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SessionRefusal {
    DuplicateOpen,
    DocumentLimit,
    DocumentMetadataLimit,
    NotOpen,
    NonMonotone,
    AccountingInvariant,
}

impl SessionRefusal {
    pub(super) const fn message(self) -> &'static str {
        match self {
            Self::DuplicateOpen => {
                "FrankenLean refused duplicate didOpen; the existing open document remains authoritative"
            }
            Self::DocumentLimit => {
                "FrankenLean refused didOpen because the bounded open-document limit was reached"
            }
            Self::DocumentMetadataLimit => {
                "FrankenLean refused didOpen because the bounded open-document URI budget was reached"
            }
            Self::NotOpen => {
                "FrankenLean refused the document event because the document is not open"
            }
            Self::NonMonotone => {
                "FrankenLean refused non-monotone didChange version; the latest accepted version remains authoritative"
            }
            Self::AccountingInvariant => {
                "FrankenLean document-session accounting invariant failed; affected text was invalidated and accounting was rebuilt"
            }
        }
    }
}

#[derive(Debug)]
pub(super) struct DocumentSession {
    documents: BTreeMap<String, OpenDocument>,
    retained_bytes: usize,
    retained_uri_bytes: usize,
    max_documents: usize,
    max_retained_bytes: usize,
    max_retained_uri_bytes: usize,
}

impl DocumentSession {
    pub(super) fn new() -> Self {
        Self::with_resource_limits(
            MAX_OPEN_DOCUMENTS,
            MAX_RETAINED_SOURCE_BYTES,
            MAX_RETAINED_URI_BYTES,
        )
    }

    #[cfg(test)]
    pub(super) fn with_limits(max_documents: usize, max_retained_bytes: usize) -> Self {
        Self::with_resource_limits(max_documents, max_retained_bytes, MAX_RETAINED_URI_BYTES)
    }

    fn with_resource_limits(
        max_documents: usize,
        max_retained_bytes: usize,
        max_retained_uri_bytes: usize,
    ) -> Self {
        Self {
            documents: BTreeMap::new(),
            retained_bytes: 0,
            retained_uri_bytes: 0,
            max_documents,
            max_retained_bytes,
            max_retained_uri_bytes,
        }
    }

    pub(super) fn is_open(&self, uri: &str) -> bool {
        self.documents.contains_key(uri)
    }

    pub(super) fn version(&self, uri: &str) -> Option<i64> {
        self.documents.get(uri).map(|document| document.version)
    }

    pub(super) fn text(&self, uri: &str) -> Option<&str> {
        self.documents
            .get(uri)
            .and_then(|document| document.text.as_deref())
    }

    fn retain_text(
        retained_bytes: &mut usize,
        max_retained_bytes: usize,
        text: String,
    ) -> (Option<String>, RetentionOutcome) {
        let Some(next_total) = retained_bytes.checked_add(text.len()) else {
            return (
                None,
                RetentionOutcome::NotRetained(RetentionRefusal::AccountingOverflow),
            );
        };
        if next_total > max_retained_bytes {
            return (
                None,
                RetentionOutcome::NotRetained(RetentionRefusal::ByteLimit),
            );
        }
        *retained_bytes = next_total;
        (Some(text), RetentionOutcome::Retained)
    }

    fn discard_all_text(&mut self) {
        for document in self.documents.values_mut() {
            document.text = None;
        }
        self.retained_bytes = 0;
    }

    fn rebuild_retained_bytes(&mut self) {
        let rebuilt = self.documents.values().try_fold(0usize, |total, document| {
            let len = document.text.as_ref().map_or(0, String::len);
            total.checked_add(len)
        });
        match rebuilt {
            Some(total) if total <= self.max_retained_bytes => self.retained_bytes = total,
            Some(_) | None => self.discard_all_text(),
        }
    }

    fn rebuild_retained_uri_bytes(&mut self) {
        self.retained_uri_bytes = self
            .documents
            .keys()
            .try_fold(0usize, |total, uri| total.checked_add(uri.len()))
            .unwrap_or(usize::MAX);
    }

    fn rebuild_accounting(&mut self) {
        self.rebuild_retained_bytes();
        self.rebuild_retained_uri_bytes();
    }

    pub(super) fn open(
        &mut self,
        uri: String,
        version: i64,
        text: String,
    ) -> Result<RetentionOutcome, SessionRefusal> {
        if self.documents.contains_key(&uri) {
            return Err(SessionRefusal::DuplicateOpen);
        }
        if self.documents.len() >= self.max_documents {
            return Err(SessionRefusal::DocumentLimit);
        }
        let next_uri_bytes = self
            .retained_uri_bytes
            .checked_add(uri.len())
            .ok_or(SessionRefusal::DocumentMetadataLimit)?;
        if next_uri_bytes > self.max_retained_uri_bytes {
            return Err(SessionRefusal::DocumentMetadataLimit);
        }
        let (text, retention) =
            Self::retain_text(&mut self.retained_bytes, self.max_retained_bytes, text);
        self.retained_uri_bytes = next_uri_bytes;
        self.documents.insert(uri, OpenDocument { version, text });
        Ok(retention)
    }

    fn replace_text(
        &mut self,
        uri: &str,
        version: Option<i64>,
        text: String,
    ) -> Result<RetentionOutcome, SessionRefusal> {
        let Some(mut document) = self.documents.remove(uri) else {
            return Err(SessionRefusal::NotOpen);
        };
        let old_len = document.text.as_ref().map_or(0, String::len);
        let Some(retained_bytes) = self.retained_bytes.checked_sub(old_len) else {
            document.text = None;
            self.documents.insert(uri.to_string(), document);
            self.rebuild_accounting();
            return Err(SessionRefusal::AccountingInvariant);
        };
        self.retained_bytes = retained_bytes;
        if let Some(version) = version {
            document.version = version;
        }
        let (text, retention) =
            Self::retain_text(&mut self.retained_bytes, self.max_retained_bytes, text);
        document.text = text;
        self.documents.insert(uri.to_string(), document);
        Ok(retention)
    }

    pub(super) fn change(
        &mut self,
        uri: &str,
        version: i64,
        text: String,
    ) -> Result<RetentionOutcome, SessionRefusal> {
        let Some(current) = self.version(uri) else {
            return Err(SessionRefusal::NotOpen);
        };
        if version <= current {
            return Err(SessionRefusal::NonMonotone);
        }
        self.replace_text(uri, Some(version), text)
    }

    pub(super) fn save_with_text(
        &mut self,
        uri: &str,
        text: String,
    ) -> Result<RetentionOutcome, SessionRefusal> {
        self.replace_text(uri, None, text)
    }

    pub(super) fn invalidate_text(&mut self, uri: &str) -> Result<(), SessionRefusal> {
        let Some(mut document) = self.documents.remove(uri) else {
            return Err(SessionRefusal::NotOpen);
        };
        let old_len = document.text.take().as_ref().map_or(0, String::len);
        let Some(retained_bytes) = self.retained_bytes.checked_sub(old_len) else {
            self.documents.insert(uri.to_string(), document);
            self.rebuild_accounting();
            return Err(SessionRefusal::AccountingInvariant);
        };
        self.retained_bytes = retained_bytes;
        self.documents.insert(uri.to_string(), document);
        Ok(())
    }

    pub(super) fn close(&mut self, uri: &str) -> Result<bool, SessionRefusal> {
        let Some(document) = self.documents.remove(uri) else {
            return Ok(false);
        };
        let old_len = document.text.as_ref().map_or(0, String::len);
        let Some(retained_bytes) = self.retained_bytes.checked_sub(old_len) else {
            self.rebuild_accounting();
            return Err(SessionRefusal::AccountingInvariant);
        };
        let Some(retained_uri_bytes) = self.retained_uri_bytes.checked_sub(uri.len()) else {
            self.rebuild_accounting();
            return Err(SessionRefusal::AccountingInvariant);
        };
        self.retained_bytes = retained_bytes;
        self.retained_uri_bytes = retained_uri_bytes;
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retention_pressure_never_erases_open_or_version_authority() {
        let mut session = DocumentSession::with_limits(1, 3);
        assert_eq!(
            session.open("file:///x".to_string(), 1, "oversized".to_string()),
            Ok(RetentionOutcome::NotRetained(RetentionRefusal::ByteLimit))
        );
        assert!(session.is_open("file:///x"));
        assert_eq!(session.version("file:///x"), Some(1));
        assert_eq!(session.text("file:///x"), None);

        assert_eq!(
            session.change("file:///x", 2, "still-too-large".to_string()),
            Ok(RetentionOutcome::NotRetained(RetentionRefusal::ByteLimit))
        );
        assert_eq!(session.version("file:///x"), Some(2));
        assert!(matches!(
            session.change("file:///x", 2, "x".to_string()),
            Err(SessionRefusal::NonMonotone)
        ));
    }

    #[test]
    fn uri_pressure_is_bounded_before_source_budget_changes() {
        let mut session = DocumentSession::with_resource_limits(2, 4, 10);
        assert_eq!(
            session.open("1234567890".to_string(), 1, "x".to_string()),
            Ok(RetentionOutcome::Retained)
        );
        assert_eq!(session.retained_uri_bytes, 10);
        assert_eq!(session.retained_bytes, 1);

        assert_eq!(
            session.open("z".to_string(), 1, "yyy".to_string()),
            Err(SessionRefusal::DocumentMetadataLimit)
        );
        assert!(!session.is_open("z"));
        assert_eq!(session.retained_uri_bytes, 10);
        assert_eq!(session.retained_bytes, 1);

        assert_eq!(session.close("1234567890"), Ok(true));
        assert_eq!(session.retained_uri_bytes, 0);
        assert_eq!(session.retained_bytes, 0);
        assert_eq!(
            session.open("z".to_string(), 1, "yyy".to_string()),
            Ok(RetentionOutcome::Retained)
        );
    }

    #[test]
    fn invalidating_text_preserves_lifecycle_state() {
        let mut session = DocumentSession::new();
        session
            .open("file:///x".to_string(), 7, "source".to_string())
            .unwrap();
        session.invalidate_text("file:///x").unwrap();
        assert!(session.is_open("file:///x"));
        assert_eq!(session.version("file:///x"), Some(7));
        assert_eq!(session.text("file:///x"), None);
        assert_eq!(session.retained_uri_bytes, "file:///x".len());
    }

    #[test]
    fn duplicate_open_and_unopened_change_are_typed_refusals() {
        let mut session = DocumentSession::new();
        session
            .open("file:///x".to_string(), 1, "x".to_string())
            .unwrap();
        assert_eq!(
            session.open("file:///x".to_string(), 2, "y".to_string()),
            Err(SessionRefusal::DuplicateOpen)
        );
        assert_eq!(
            session.change("file:///missing", 1, "x".to_string()),
            Err(SessionRefusal::NotOpen)
        );
    }

    #[test]
    fn close_releases_retained_bytes_and_membership() {
        let mut session = DocumentSession::with_limits(2, 4);
        session
            .open("file:///x".to_string(), 1, "1234".to_string())
            .unwrap();
        assert_eq!(session.close("file:///x"), Ok(true));
        assert!(!session.is_open("file:///x"));
        assert_eq!(session.retained_bytes, 0);
        assert_eq!(session.retained_uri_bytes, 0);
        assert_eq!(session.close("file:///x"), Ok(false));
    }

    #[test]
    fn accounting_recovery_invalidates_only_affected_text_when_rebuild_is_safe() {
        let mut session = DocumentSession::with_limits(3, 64);
        session
            .open("file:///a".to_string(), 1, "alpha".to_string())
            .unwrap();
        session
            .open("file:///b".to_string(), 4, "beta".to_string())
            .unwrap();

        session.retained_bytes = 0;
        session.retained_uri_bytes = 0;
        assert_eq!(
            session.change("file:///a", 2, "new".to_string()),
            Err(SessionRefusal::AccountingInvariant)
        );
        assert!(session.is_open("file:///a"));
        assert!(session.is_open("file:///b"));
        assert_eq!(session.version("file:///a"), Some(1));
        assert_eq!(session.version("file:///b"), Some(4));
        assert_eq!(session.text("file:///a"), None);
        assert_eq!(session.text("file:///b"), Some("beta"));
        assert_eq!(session.retained_bytes, 4);
        assert_eq!(
            session.retained_uri_bytes,
            "file:///a".len() + "file:///b".len()
        );

        assert_eq!(
            session.change("file:///a", 2, "new".to_string()),
            Ok(RetentionOutcome::Retained)
        );
        assert_eq!(session.version("file:///a"), Some(2));
        assert_eq!(session.text("file:///a"), Some("new"));
        assert_eq!(session.retained_bytes, 7);
    }

    #[test]
    fn impossible_source_rebuild_discards_text_but_preserves_uri_authority() {
        let mut session = DocumentSession::with_limits(3, 8);
        session.documents.insert(
            "file:///a".to_string(),
            OpenDocument {
                version: 1,
                text: Some("oversized".to_string()),
            },
        );
        session.documents.insert(
            "file:///b".to_string(),
            OpenDocument {
                version: 2,
                text: Some("also-oversized".to_string()),
            },
        );
        session.retained_bytes = 0;
        session.retained_uri_bytes = 0;
        session.rebuild_accounting();
        assert_eq!(session.retained_bytes, 0);
        assert_eq!(session.text("file:///a"), None);
        assert_eq!(session.text("file:///b"), None);
        assert_eq!(session.version("file:///a"), Some(1));
        assert_eq!(session.version("file:///b"), Some(2));
        assert_eq!(
            session.retained_uri_bytes,
            "file:///a".len() + "file:///b".len()
        );
    }
}
