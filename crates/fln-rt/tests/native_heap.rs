//! `native_heap` — the named suite for fln-lld's NativeHeap
//! (`fln_rt::native_heap`).
//!
//! # The laws proven here
//!
//! Handle authenticity (a handle resolves only to its own live, same-generation,
//! same-type allocation), ABA retirement (a freed slot's generation advances; at
//! the maximum the slot retires rather than re-issue a stale generation), the
//! persistent arm of the tri-state law (immutable, never freed individually),
//! total interning (structural dedup with full-value comparison on a hit, and a
//! freed interned slot leaving the index), and close-reclaims (every handle
//! refuses afterwards, with the refusal typed). Every misuse is a typed
//! `HeapError`, never UB and never a wrong value.

#![forbid(unsafe_code)]

use fln_rt::native_heap::{HeapError, NativeHeap};

// ---------------------------------------------------------------------------
// Handle authenticity
// ---------------------------------------------------------------------------

#[test]
fn a_handle_resolves_to_its_own_allocation_only() {
    let mut heap = NativeHeap::new();
    let first = heap.alloc(String::from("first"));
    let second = heap.alloc(String::from("second"));
    assert_eq!(heap.get(first).unwrap(), "first");
    assert_eq!(heap.get(second).unwrap(), "second");
    heap.get_mut(first).unwrap().push_str("-edited");
    assert_eq!(heap.get(first).unwrap(), "first-edited");
    assert_eq!(
        heap.get(second).unwrap(),
        "second",
        "the neighbour is untouched"
    );
    assert_eq!(heap.live(), 2);
}

#[test]
fn a_type_mismatch_is_typed_not_a_panic() {
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(42u64);
    // The same slot addressed as a different type, planted through the public
    // parts constructor: the heap says so, typed, never a panic and never UB.
    let as_string =
        fln_rt::native_heap::NativeHandle::<String>::from_parts(handle.slot(), handle.generation());
    assert_eq!(heap.get(as_string), Err(HeapError::TypeMismatch));
    assert_eq!(*heap.get(handle).unwrap(), 42u64);
}

// ---------------------------------------------------------------------------
// The free law and ABA retirement
// ---------------------------------------------------------------------------

#[test]
fn a_stale_handle_refuses_after_free_and_a_reused_slot_carries_a_new_generation() {
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(1u64);
    let slot = handle.slot();
    let generation = handle.generation();
    heap.free(handle).unwrap();
    assert_eq!(heap.get(handle), Err(HeapError::StaleHandle));
    assert_eq!(
        heap.free(handle),
        Err(HeapError::StaleHandle),
        "double free is typed"
    );
    assert_eq!(heap.live(), 0);

    // The slot is reused — with a NEW generation, so the stale handle still refuses.
    let fresh = heap.alloc(2u64);
    assert_eq!(fresh.slot(), slot, "the freed slot is recycled");
    assert_ne!(
        fresh.generation(),
        generation,
        "the generation advances (ABA law)"
    );
    assert_eq!(heap.get(handle), Err(HeapError::StaleHandle));
    assert_eq!(*heap.get(fresh).unwrap(), 2u64);
}

#[test]
fn a_slot_retires_at_the_generation_maximum() {
    // The retirement rule at its boundary, exercised directly rather than
    // through four billion alloc/free cycles.
    use fln_rt::native_heap::next_slot_generation;
    assert_eq!(next_slot_generation(0), Some(1));
    assert_eq!(next_slot_generation(u32::MAX - 1), Some(u32::MAX));
    assert_eq!(
        next_slot_generation(u32::MAX),
        None,
        "at the maximum the slot retires rather than re-issuing generation 0 to a stale handle"
    );

    // And the reuse law on the heap itself: a freed slot is recycled with an
    // advanced generation, so the stale handle still refuses.
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(1u64);
    heap.free(handle).unwrap();
    let fresh = heap.alloc(2u64);
    assert_eq!(fresh.slot(), handle.slot());
    assert!(fresh.generation() > handle.generation());
    assert_eq!(heap.get(handle), Err(HeapError::StaleHandle));
}

// ---------------------------------------------------------------------------
// The persistent arm
// ---------------------------------------------------------------------------

#[test]
fn persistent_allocations_are_immutable_and_never_freed() {
    let mut heap = NativeHeap::new();
    let persistent = heap.alloc_persistent(String::from("permanent"));
    assert_eq!(heap.get(persistent).unwrap(), "permanent");
    assert_eq!(
        heap.get_mut(persistent),
        Err(HeapError::PersistentMutation),
        "persistent is immutable"
    );
    assert_eq!(
        heap.free(persistent),
        Err(HeapError::PersistentMutation),
        "persistent is never counted (the m_rc == 0 arm)"
    );
    assert_eq!(heap.live(), 1, "the refusal changed nothing");
}

// ---------------------------------------------------------------------------
// Total interning
// ---------------------------------------------------------------------------

#[test]
fn interning_dedups_structurally_and_a_freed_slot_leaves_the_index() {
    let mut heap = NativeHeap::new();
    let key = |s: &String| s.clone();
    let first = heap.intern("shared".to_string(), key);
    let second = heap.intern("shared".to_string(), key);
    assert_eq!(
        first, second,
        "the same value interns to the same live handle"
    );
    assert_eq!(heap.live(), 1, "dedup is real, not nominal");

    let third = heap.intern("different".to_string(), key);
    assert_ne!(first, third);
    assert_eq!(heap.live(), 2);

    // Free the interned handle: the index must not resolve a future re-used slot
    // to a different value.
    heap.free(first).unwrap();
    let fourth = heap.intern("shared".to_string(), key);
    assert_eq!(heap.get(fourth).unwrap(), "shared");
    assert_eq!(heap.live(), 2, "one freed, one re-interned fresh");
}

// ---------------------------------------------------------------------------
// Close reclaims
// ---------------------------------------------------------------------------

#[test]
fn close_reclaims_everything_and_every_handle_refuses_typed() {
    let mut heap = NativeHeap::new();
    let ordinary = heap.alloc(1u64);
    let persistent = heap.alloc_persistent(2u64);
    heap.close();
    assert!(heap.is_closed());
    assert_eq!(heap.live(), 0);
    assert_eq!(heap.get(ordinary), Err(HeapError::Closed));
    assert_eq!(heap.get(persistent), Err(HeapError::Closed));
    assert_eq!(heap.free(ordinary), Err(HeapError::Closed));
}

#[test]
#[should_panic(expected = "caller bug")]
fn allocating_on_a_closed_heap_is_the_programmer_invariant() {
    let mut heap = NativeHeap::new();
    heap.close();
    let _ = heap.alloc(1u64);
}

// ---------------------------------------------------------------------------
// The two-heap separation law
// ---------------------------------------------------------------------------

#[test]
fn the_native_heap_carries_no_abi_obligation() {
    // The module's own law, asserted at its source: native_heap.rs may not name
    // the Compat side's types (the membrane is the converters, not the heap).
    let source = include_str!("../src/native_heap.rs");
    // Code lines only: the module doc legitimately explains the two-heap
    // architecture (it NAMES the Compat side to say what it is not) — the law
    // is about type usage, and a needle that cannot tell prose from code
    // reddens its own documentation.
    let code: String = source
        .lines()
        .filter(|line| {
            let trimmed = line.trim_start();
            !trimmed.starts_with("//")
        })
        .collect::<Vec<_>>()
        .join("\n");
    for forbidden in ["LeanObject", "CompatHeap", "lean_object", "m_rc"] {
        assert!(
            !code.contains(forbidden),
            "native_heap.rs names the Compat side's `{forbidden}` in code — the type \
             separation the acceptance text requires is compile-time, and this is the tripwire"
        );
    }
    for forbidden in ["unsafe fn", "unsafe impl", "unsafe {"] {
        assert!(
            !code.contains(forbidden),
            "native_heap.rs carries `{forbidden}` — the module is forbid(unsafe_code) \
             and stays that way"
        );
    }
}
