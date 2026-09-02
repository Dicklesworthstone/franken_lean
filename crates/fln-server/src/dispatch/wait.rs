use super::json::RequestId;

pub(super) const MAX_PENDING_DIAGNOSTIC_WAITS: usize = 4096;
pub(super) const MAX_PENDING_DIAGNOSTIC_WAIT_BYTES: usize = 4 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
struct PendingWait {
    id: RequestId,
    uri: String,
    version: i64,
}

impl PendingWait {
    fn retained_bytes(&self) -> Option<usize> {
        request_id_bytes(&self.id).checked_add(self.uri.len())
    }
}

fn request_id_bytes(id: &RequestId) -> usize {
    match id {
        RequestId::Number(value) | RequestId::Text(value) => value.len(),
        RequestId::Null => 0,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum WaitRefusal {
    DuplicateId,
    Capacity,
}

impl WaitRefusal {
    pub(super) const fn message(self) -> &'static str {
        match self {
            Self::DuplicateId => "FrankenLean refused a duplicate outstanding JSON-RPC request id",
            Self::Capacity => "FrankenLean pending diagnostic-wait capacity is exhausted",
        }
    }
}

#[derive(Debug)]
pub(super) struct PendingDiagnosticWaits {
    waits: Vec<PendingWait>,
    max_waits: usize,
    max_bytes: usize,
}

impl PendingDiagnosticWaits {
    pub(super) fn new() -> Self {
        Self::with_limits(
            MAX_PENDING_DIAGNOSTIC_WAITS,
            MAX_PENDING_DIAGNOSTIC_WAIT_BYTES,
        )
    }

    pub(super) fn with_limits(max_waits: usize, max_bytes: usize) -> Self {
        Self {
            waits: Vec::new(),
            max_waits,
            max_bytes,
        }
    }

    pub(super) fn contains(&self, id: &RequestId) -> bool {
        self.waits.iter().any(|wait| &wait.id == id)
    }

    fn retained_bytes(&self) -> Option<usize> {
        self.waits.iter().try_fold(0usize, |total, wait| {
            total.checked_add(wait.retained_bytes()?)
        })
    }

    pub(super) fn register(
        &mut self,
        id: RequestId,
        uri: String,
        version: i64,
    ) -> Result<(), WaitRefusal> {
        if self.contains(&id) {
            return Err(WaitRefusal::DuplicateId);
        }
        if self.waits.len() >= self.max_waits {
            return Err(WaitRefusal::Capacity);
        }
        let new_bytes = request_id_bytes(&id)
            .checked_add(uri.len())
            .ok_or(WaitRefusal::Capacity)?;
        let retained_bytes = self.retained_bytes().ok_or(WaitRefusal::Capacity)?;
        let next_bytes = retained_bytes
            .checked_add(new_bytes)
            .ok_or(WaitRefusal::Capacity)?;
        if next_bytes > self.max_bytes {
            return Err(WaitRefusal::Capacity);
        }
        self.waits.push(PendingWait { id, uri, version });
        Ok(())
    }

    pub(super) fn complete_ready(&mut self, uri: &str, version: i64) -> Vec<RequestId> {
        let mut ready = Vec::new();
        let mut pending = Vec::with_capacity(self.waits.len());
        for wait in self.waits.drain(..) {
            if wait.uri == uri && wait.version <= version {
                ready.push(wait.id);
            } else {
                pending.push(wait);
            }
        }
        self.waits = pending;
        ready
    }

    pub(super) fn cancel(&mut self, id: &RequestId) -> Option<RequestId> {
        let position = self.waits.iter().position(|wait| &wait.id == id)?;
        Some(self.waits.remove(position).id)
    }

    pub(super) fn drain_uri(&mut self, uri: &str) -> Vec<RequestId> {
        let mut drained = Vec::new();
        let mut pending = Vec::with_capacity(self.waits.len());
        for wait in self.waits.drain(..) {
            if wait.uri == uri {
                drained.push(wait.id);
            } else {
                pending.push(wait);
            }
        }
        self.waits = pending;
        drained
    }

    pub(super) fn drain_all(&mut self) -> Vec<RequestId> {
        self.waits.drain(..).map(|wait| wait.id).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(value: &str) -> RequestId {
        RequestId::Text(value.to_string())
    }

    #[test]
    fn ready_waits_complete_in_registration_order() {
        let mut waits = PendingDiagnosticWaits::new();
        waits.register(id("a"), "file:///x".to_string(), 2).unwrap();
        waits.register(id("b"), "file:///y".to_string(), 1).unwrap();
        waits.register(id("c"), "file:///x".to_string(), 3).unwrap();

        assert_eq!(waits.complete_ready("file:///x", 2), vec![id("a")]);
        assert_eq!(waits.complete_ready("file:///x", 3), vec![id("c")]);
        assert_eq!(waits.complete_ready("file:///y", 1), vec![id("b")]);
    }

    #[test]
    fn duplicate_ids_and_count_capacity_are_typed_refusals() {
        let mut waits = PendingDiagnosticWaits::with_limits(1, 100);
        waits.register(id("a"), "file:///x".to_string(), 2).unwrap();
        assert!(waits.contains(&id("a")));
        assert_eq!(
            waits.register(id("a"), "file:///y".to_string(), 3),
            Err(WaitRefusal::DuplicateId)
        );
        assert_eq!(
            waits.register(id("b"), "file:///y".to_string(), 3),
            Err(WaitRefusal::Capacity)
        );
    }

    #[test]
    fn aggregate_retained_bytes_are_bounded_without_mutable_accounting() {
        let mut waits = PendingDiagnosticWaits::with_limits(4, 12);
        waits.register(id("a"), "file:///x".to_string(), 2).unwrap();
        // Accounting is request-id bytes + uri bytes: id "a" (1) + "file:///x" (9) = 10.
        assert_eq!(waits.retained_bytes(), Some(10));
        assert_eq!(
            waits.register(id("bbbb"), "file:///y".to_string(), 3),
            Err(WaitRefusal::Capacity)
        );
        assert_eq!(waits.retained_bytes(), Some(10));
    }

    #[test]
    fn cancellation_and_drains_remove_exact_waits() {
        let mut waits = PendingDiagnosticWaits::new();
        waits.register(id("a"), "file:///x".to_string(), 2).unwrap();
        waits.register(id("b"), "file:///x".to_string(), 3).unwrap();
        waits.register(id("c"), "file:///y".to_string(), 4).unwrap();

        assert_eq!(waits.cancel(&id("b")), Some(id("b")));
        assert_eq!(waits.cancel(&id("missing")), None);
        assert_eq!(waits.drain_uri("file:///x"), vec![id("a")]);
        assert_eq!(waits.drain_all(), vec![id("c")]);
        assert!(waits.drain_all().is_empty());
    }
}
