//! Debug ownership shadows (plan §6.2, bead fln-lld): double-release and
//! foreign-pointer misuse detection with provenance tags, quarantine instead
//! of corruption, and deterministic replay events for ownership faults.
//!
//! Design:
//! * A global registry maps live CompatHeap addresses to `(alloc_seq, size)`.
//!   `alloc_seq` is a deterministic per-enable counter — replay events carry
//!   sequence tags, never raw addresses, so two runs of the same operation
//!   script produce identical event streams.
//! * While shadows are enabled, **every** free is quarantined: the memory is
//!   retained and the header tag poisoned, so addresses are never reused and
//!   use-after-release is deterministically detectable. Faulty operations
//!   (double release, RC traffic on a pointer the membrane never minted) are
//!   recorded and **skipped** — quarantine, never corruption.
//! * Disabled (the default and the release posture), every hook is a single
//!   relaxed atomic load; behavior is exactly the Reference's blind-trust
//!   discipline.
//!
//! This module is pure safe Rust: it manipulates bookkeeping keyed by
//! addresses, never the objects themselves.

use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventKind {
    Alloc,
    Release,
    DoubleRelease,
    ForeignPointer,
    TraversalSkip,
}

/// One deterministic replay event. `tag` is the allocation sequence number of
/// the object involved (`None` when the pointer was never registered).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShadowEvent {
    pub seq: u64,
    pub kind: EventKind,
    pub tag: Option<u64>,
    pub category: Option<u8>,
    pub op: &'static str,
}

#[derive(Default)]
struct ShadowState {
    live: HashMap<usize, (u64, usize)>,
    quarantined: HashMap<usize, u64>,
    events: Vec<ShadowEvent>,
    next_alloc: u64,
    next_event: u64,
}

static ENABLED: AtomicBool = AtomicBool::new(false);
static STATE: Mutex<Option<ShadowState>> = Mutex::new(None);

#[inline(always)]
pub fn enabled() -> bool {
    ENABLED.load(Ordering::Relaxed)
}

/// Enable shadow tracking with a fresh deterministic state. Tests serialize
/// enable/drain around their operation scripts.
pub fn enable() {
    let mut guard = STATE.lock().expect("shadow state poisoned");
    *guard = Some(ShadowState::default());
    ENABLED.store(true, Ordering::SeqCst);
}

/// Disable tracking and return the replay event stream plus the count of
/// still-live (leaked) registrations.
pub fn disable_and_drain() -> (Vec<ShadowEvent>, usize) {
    ENABLED.store(false, Ordering::SeqCst);
    let mut guard = STATE.lock().expect("shadow state poisoned");
    match guard.take() {
        Some(st) => (st.events, st.live.len()),
        None => (Vec::new(), 0),
    }
}

fn with_state<R>(f: impl FnOnce(&mut ShadowState) -> R) -> Option<R> {
    let mut guard = STATE.lock().expect("shadow state poisoned");
    guard.as_mut().map(f)
}

fn push_event(
    st: &mut ShadowState,
    kind: EventKind,
    tag: Option<u64>,
    category: Option<u8>,
    op: &'static str,
) {
    let seq = st.next_event;
    st.next_event += 1;
    st.events.push(ShadowEvent {
        seq,
        kind,
        tag,
        category,
        op,
    });
}

/// Record a freshly minted CompatHeap object. Returns its provenance tag.
pub(crate) fn on_alloc(addr: usize, size: usize, category: u8) -> Option<u64> {
    if !enabled() {
        return None;
    }
    with_state(|st| {
        let tag = st.next_alloc;
        st.next_alloc += 1;
        st.live.insert(addr, (tag, size));
        push_event(st, EventKind::Alloc, Some(tag), Some(category), "alloc");
        tag
    })
}

/// Verdict the membrane consults before releasing memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FreeVerdict {
    /// Shadows disabled: release normally.
    Release,
    /// Shadows enabled and the free is legitimate: retain (quarantine) the
    /// memory, poison the header, and record the release.
    Quarantine,
    /// Fault detected (double release or foreign pointer): do not touch the
    /// memory at all.
    Fault,
}

/// Consult the registry about a free of `addr` (category read from the live
/// header by the caller before the verdict is applied).
pub(crate) fn on_free(addr: usize, category: u8, op: &'static str) -> FreeVerdict {
    if !enabled() {
        return FreeVerdict::Release;
    }
    with_state(|st| {
        if let Some((tag, _sz)) = st.live.remove(&addr) {
            st.quarantined.insert(addr, tag);
            push_event(st, EventKind::Release, Some(tag), Some(category), op);
            FreeVerdict::Quarantine
        } else if let Some(&tag) = st.quarantined.get(&addr) {
            push_event(st, EventKind::DoubleRelease, Some(tag), Some(category), op);
            FreeVerdict::Fault
        } else {
            push_event(st, EventKind::ForeignPointer, None, Some(category), op);
            FreeVerdict::Fault
        }
    })
    .unwrap_or(FreeVerdict::Release)
}

/// Check an RC operation's target. Returns `false` when the operation must be
/// skipped (foreign or quarantined pointer — quarantine, never corruption).
pub(crate) fn check_rc_target(addr: usize, op: &'static str) -> bool {
    if !enabled() {
        return true;
    }
    with_state(|st| {
        if st.live.contains_key(&addr) {
            true
        } else if let Some(&tag) = st.quarantined.get(&addr) {
            push_event(st, EventKind::DoubleRelease, Some(tag), None, op);
            false
        } else {
            push_event(st, EventKind::ForeignPointer, None, None, op);
            false
        }
    })
    .unwrap_or(true)
}

/// Record a traversal the slice cannot perform yet (external-object
/// `m_foreach` requires the apply machinery — beads franken_lean-7xe/fln-3gv).
pub(crate) fn on_traversal_skip(category: u8, op: &'static str) {
    if !enabled() {
        return;
    }
    with_state(|st| push_event(st, EventKind::TraversalSkip, None, Some(category), op));
}
