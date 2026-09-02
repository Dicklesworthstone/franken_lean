use std::collections::BTreeMap;

use super::json::RequestId;

pub(super) const MAX_PENDING_DIAGNOSTIC_WAITS: usize = 4096;

#[derive(Debug, Clone, PartialEq, Eq)]
struct PendingWait {
    id: RequestId,
    version: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RegisterOutcome {
    Ready,
    Pending,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum WaitRefusal {
    Capacity,
    DuplicateRequestId,
}

impl WaitRefusal {
    pub(super) const fn message(self) -> &'static str {
        match self {
            Self::Capacity => {
                "FrankenLean refused waitForDiagnostics because the bounded pending-wait limit was reached"
            }
            Self::DuplicateRequestId => {
                "FrankenLean refused waitForDiagnostics because its request id is already pending"
            }
        }
    }
}

#[derive(Debug)]
pub(super) struct DiagnosticWaitRegistry {
    completed_versions: BTreeMap<String, i64>,
    pending: BTreeMap<String, Vec<PendingWait>>,
    pending_count: usize,
    max_pending: usize,
}

impl DiagnosticWaitRegistry {
    pub(super) fn new() -> Self {
        Self::with_limit(MAX_PENDING_DIAGNOSTIC_WAITS)
    }

    pub(super) fn with_limit(max_pending: usize) -> Self {
        Self {
            completed_versions: BTreeMap::new(),
            pending: BTreeMap::new(),
            pending_count: 0,
            max_pending,
        }
    }

    pub(super) fn completed_version(&self, uri: &str) -> Option<i64> {
        self.completed_versions.get(uri).copied()
    }

    fn request_id_is_pending(&self, id: &RequestId) -> bool {
        self.pending
            .values()
            .flatten()
            .any(|pending| pending.id == *id)
    }

    pub(super) fn register(
        &mut self,
        uri: String,
        version: i64,
        id: RequestId,
    ) -> Result<RegisterOutcome, WaitRefusal> {
        if self
            .completed_version(&uri)
            .is_some_and(|completed| completed >= version)
        {
            return Ok(RegisterOutcome::Ready);
        }
        if self.request_id_is_pending(&id) {
            return Err(WaitRefusal::DuplicateRequestId);
        }
        if self.pending_count >= self.max_pending {
            return Err(WaitRefusal::Capacity);
        }
        self.pending
            .entry(uri)
            .or_default()
            .push(PendingWait { id, version });
        self.pending_count += 1;
        Ok(RegisterOutcome::Pending)
    }

    pub(super) fn mark_completed(&mut self, uri: &str, version: i64) -> Vec<RequestId> {
        self.completed_versions
            .entry(uri.to_string())
            .and_modify(|completed| *completed = (*completed).max(version))
            .or_insert(version);

        let Some(waiters) = self.pending.remove(uri) else {
            return Vec::new();
        };
        let mut ready = Vec::new();
        let mut remaining = Vec::new();
        for waiter in waiters {
            if waiter.version <= version {
                ready.push(waiter.id);
            } else {
                remaining.push(waiter);
            }
        }
        self.pending_count = self.pending_count.saturating_sub(ready.len());
        if !remaining.is_empty() {
            self.pending.insert(uri.to_string(), remaining);
        }
        ready
    }

    pub(super) fn cancel(&mut self, id: &RequestId) -> Option<RequestId> {
        let mut empty_uri = None;
        let mut cancelled = None;
        for (uri, waiters) in &mut self.pending {
            if let Some(index) = waiters.iter().position(|waiter| waiter.id == *id) {
                cancelled = Some(waiters.remove(index).id);
                if waiters.is_empty() {
                    empty_uri = Some(uri.clone());
                }
                break;
            }
        }
        if let Some(uri) = empty_uri {
            self.pending.remove(&uri);
        }
        if cancelled.is_some() {
            self.pending_count = self.pending_count.saturating_sub(1);
        }
        cancelled
    }

    pub(super) fn close(&mut self, uri: &str) -> Vec<RequestId> {
        self.completed_versions.remove(uri);
        let cancelled = self.pending.remove(uri).unwrap_or_default();
        self.pending_count = self.pending_count.saturating_sub(cancelled.len());
        cancelled.into_iter().map(|waiter| waiter.id).collect()
    }

    pub(super) fn drain(&mut self) -> Vec<RequestId> {
        self.completed_versions.clear();
        self.pending_count = 0;
        std::mem::take(&mut self.pending)
            .into_values()
            .flatten()
            .map(|waiter| waiter.id)
            .collect()
    }

    #[cfg(test)]
    fn pending_count(&self) -> usize {
        self.pending_count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(value: &str) -> RequestId {
        RequestId::Text(value.to_string())
    }

    #[test]
    fn completed_versions_reply_immediately_and_future_versions_queue() {
        let mut waits = DiagnosticWaitRegistry::new();
        assert_eq!(waits.mark_completed("file:///x", 3), Vec::new());
        assert_eq!(
            waits.register("file:///x".to_string(), 2, id("ready")),
            Ok(RegisterOutcome::Ready)
        );
        assert_eq!(
            waits.register("file:///x".to_string(), 4, id("future")),
            Ok(RegisterOutcome::Pending)
        );
        assert_eq!(waits.pending_count(), 1);
        assert_eq!(waits.mark_completed("file:///x", 3), Vec::new());
        assert_eq!(waits.mark_completed("file:///x", 4), vec![id("future")]);
        assert_eq!(waits.pending_count(), 0);
    }

    #[test]
    fn completion_releases_only_satisfied_waiters_in_registration_order() {
        let mut waits = DiagnosticWaitRegistry::new();
        for (version, request) in [(5, "five-a"), (7, "seven"), (5, "five-b")] {
            assert_eq!(
                waits.register("file:///x".to_string(), version, id(request)),
                Ok(RegisterOutcome::Pending)
            );
        }
        assert_eq!(
            waits.mark_completed("file:///x", 5),
            vec![id("five-a"), id("five-b")]
        );
        assert_eq!(waits.pending_count(), 1);
        assert_eq!(waits.mark_completed("file:///x", 7), vec![id("seven")]);
    }

    #[test]
    fn duplicate_ids_and_capacity_are_typed_refusals() {
        let mut waits = DiagnosticWaitRegistry::with_limit(1);
        assert_eq!(
            waits.register("file:///x".to_string(), 1, id("same")),
            Ok(RegisterOutcome::Pending)
        );
        assert_eq!(
            waits.register("file:///y".to_string(), 1, id("same")),
            Err(WaitRefusal::DuplicateRequestId)
        );
        assert_eq!(
            waits.register("file:///y".to_string(), 1, id("other")),
            Err(WaitRefusal::Capacity)
        );
    }

    #[test]
    fn cancel_close_and_drain_release_exact_request_ids() {
        let mut waits = DiagnosticWaitRegistry::new();
        waits
            .register("file:///x".to_string(), 2, id("x-a"))
            .unwrap();
        waits
            .register("file:///x".to_string(), 3, id("x-b"))
            .unwrap();
        waits
            .register("file:///y".to_string(), 1, id("y"))
            .unwrap();

        assert_eq!(waits.cancel(&id("x-a")), Some(id("x-a")));
        assert_eq!(waits.cancel(&id("missing")), None);
        assert_eq!(waits.close("file:///x"), vec![id("x-b")]);
        assert_eq!(waits.completed_version("file:///x"), None);
        assert_eq!(waits.drain(), vec![id("y")]);
        assert_eq!(waits.pending_count(), 0);
    }
}
