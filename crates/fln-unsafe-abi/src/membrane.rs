//! CompatHeap membrane allocation (plan §6.1b, beads fln-lld / franken_lean-83r).
//!
//! Every CompatHeap object is minted and released ONLY through this module.
//! The size/`m_cs_sz` discipline mirrors the pin's distributed build exactly
//! (`LEAN_MIMALLOC` defined in the toolchain's `include/lean/config.h`):
//!
//! * small path (`lean_alloc_small_object`, `lean.h:409-432`): size is
//!   aligned up to `OBJECT_SIZE_DELTA` and the aligned size is stored in
//!   `m_cs_sz` at allocation time; header init leaves it in place.
//! * big path (`lean_alloc_object`, `object.cpp:355-376` — arrays, scalar
//!   arrays, strings, closures): exact requested size, `m_cs_sz = 0`.
//! * ctor memory (`lean_alloc_ctor_memory`, `lean.h:434-465`): small path
//!   plus zero-initialization of the final word when alignment padded the
//!   request, preserving the sharing-maximizer determinism upstream relies
//!   on (`maxsharing.cpp`/`compact.cpp` comment at `lean.h:441-449`).
//!
//! **The small heap is size-prefixed** (bead franken_lean-83r): under the
//! pin's `LEAN_MIMALLOC` config the C inlines free small objects *sizelessly*
//! (`lean_free_small_object` → `mi_free(o)`, `lean.h:490-497` — and the
//! header comment at `lean.h:125-131` warns `m_cs_sz` may be repurposed by
//! free time, so the allocator must not read it). We adopt upstream's OWN
//! fallback discipline for exactly this problem — the non-mimalloc path at
//! `lean.h:425-429` stores the size in one word before the object
//! (`*(size_t*)mem = sz; return (size_t*)mem + 1`). Every small block, Rust-
//! or C-minted, carries that hidden prefix, so `mi_free`-shaped sizeless
//! release and Rust sized release resolve to one free path. The prefix is
//! invisible at the ABI: object pointers, layouts, and header facts are
//! unchanged (C4 rig).
//!
//! Internal allocation failure aborts the process
//! (`std::alloc::handle_alloc_error`) — an abort, never a Rust panic
//! unwinding toward an ABI boundary (§6.5 panic law). The *exported* C
//! surface instead mirrors the pin's observable OOM behavior
//! (`lean_internal_panic_out_of_memory`); see `export.rs`. The owned
//! calibrated heartbeat hook is installed at the small-allocation seam; the
//! size-classed backend that replaces `std::alloc` underneath this interface
//! remains bead fln-8w8 work. The membrane discipline and observable header
//! facts are already final here.

use crate::contract::{MAX_SMALL_OBJECT_SIZE, OBJECT_SIZE_DELTA, TAG_RESERVED};
use crate::layout::LeanObject;
use crate::shadow;
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::cell::Cell;

/// `lean_align` (`lean.h:390-392`) at `OBJECT_SIZE_DELTA` granularity.
#[inline(always)]
pub(crate) fn align_obj_size(sz: usize) -> usize {
    (sz / OBJECT_SIZE_DELTA) * OBJECT_SIZE_DELTA
        + OBJECT_SIZE_DELTA * usize::from(!sz.is_multiple_of(OBJECT_SIZE_DELTA))
}

/// All CompatHeap blocks are 8-aligned: `lean_object` demands 4, every
/// object-model struct field demands at most 8, and the small path's size
/// quantum is `OBJECT_SIZE_DELTA = 8`.
const OBJ_ALIGN: usize = 8;

/// Hidden size prefix on every small-heap block (`lean.h:425-429` shape):
/// one word, so the returned object pointer stays 8-aligned.
const SMALL_PREFIX: usize = size_of::<usize>();

thread_local! {
    /// `g_heartbeat` / `heap::m_heartbeat` at the pin: one counter per
    /// runtime thread, shared by small allocations and explicit bumps.
    static HEARTBEAT: Cell<u64> = const { Cell::new(0) };
}

/// Add explicit heartbeat ticks with the pin's wrapping unsigned arithmetic.
pub(crate) fn add_heartbeats(ticks: u64) {
    HEARTBEAT.with(|heartbeat| heartbeat.set(heartbeat.get().wrapping_add(ticks)));
}

/// The counting hook used by both supported small-allocator entry paths.
pub(crate) fn charge_small_allocation() {
    add_heartbeats(1);
}

/// Test-only observation of the current runtime thread's counter.
#[cfg(test)]
pub(crate) fn heartbeat_value() -> u64 {
    HEARTBEAT.with(Cell::get)
}

fn obj_layout(size: usize) -> Layout {
    debug_assert!(size > 0);
    Layout::from_size_align(size, OBJ_ALIGN).expect("object size overflows Layout")
}

fn small_layout(user_size: usize) -> Layout {
    let total = user_size
        .checked_add(SMALL_PREFIX)
        .expect("small object size overflows Layout");
    Layout::from_size_align(total, OBJ_ALIGN).expect("small object size overflows Layout")
}

/// Raw small-heap allocation: `user_size` bytes behind a hidden size prefix.
/// Returns null on exhaustion (the caller chooses the failure policy:
/// internal paths abort, the C export surface panics like the pin).
///
/// # Safety
/// `user_size > 0`. The returned pointer must be released with
/// [`small_free_raw`] and only through it.
// UNSAFE-LEDGER: FLN-UL-0064
#[allow(unsafe_code)]
pub(crate) unsafe fn small_alloc_raw(user_size: usize) -> *mut u8 {
    debug_assert!(user_size > 0);
    let layout = small_layout(user_size);
    // SAFETY: layout has non-zero size; the prefix word is in-bounds of the
    // fresh exclusively-owned block.
    unsafe {
        let base = alloc(layout);
        if base.is_null() {
            return core::ptr::null_mut();
        }
        base.cast::<usize>().write(user_size);
        base.add(SMALL_PREFIX)
    }
}

/// Raw small-heap release: the `mi_free` shape — no size argument, the
/// prefix word is the size authority (never `m_cs_sz`, which the pin
/// documents as repurposable by free time, `lean.h:125-131`).
///
/// # Safety
/// `p` was returned by [`small_alloc_raw`] and is released exactly once.
// UNSAFE-LEDGER: FLN-UL-0065
#[allow(unsafe_code)]
pub(crate) unsafe fn small_free_raw(p: *mut u8) {
    // SAFETY: the prefix word sits immediately below the user pointer and
    // still holds the exact size passed to small_alloc_raw.
    unsafe {
        let base = p.sub(SMALL_PREFIX);
        let user_size = base.cast::<usize>().read();
        dealloc(base, small_layout(user_size));
    }
}

/// Raw small-heap size query (`lean_small_mem_size` shape): the prefix word.
///
/// # Safety
/// `p` was returned by [`small_alloc_raw`] and is still live.
// UNSAFE-LEDGER: FLN-UL-0066
#[allow(unsafe_code)]
pub(crate) unsafe fn small_mem_size_raw(p: *mut u8) -> usize {
    // SAFETY: as small_free_raw; read-only.
    unsafe { p.sub(SMALL_PREFIX).cast::<usize>().read() }
}

/// Small-path allocation: `lean_alloc_small_object` under `LEAN_MIMALLOC`
/// (`lean.h:417-424`). Returns uninitialized memory except `m_cs_sz`, which
/// holds the aligned size exactly as the pin's build leaves it in live
/// objects.
///
/// # Safety
/// Caller must initialize the header (and every salient field) before the
/// object is shared, and must release through this module.
// UNSAFE-LEDGER: FLN-UL-0001
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_small(sz: usize) -> *mut LeanObject {
    let aligned = align_obj_size(sz);
    debug_assert!(aligned <= MAX_SMALL_OBJECT_SIZE);
    charge_small_allocation();
    // SAFETY: aligned > 0; block minted by the small heap; m_cs_sz is
    // in-bounds of the fresh exclusively-owned block.
    unsafe {
        let p = small_alloc_raw(aligned);
        if p.is_null() {
            handle_alloc_error(small_layout(aligned));
        }
        let o = p.cast::<LeanObject>();
        (&raw mut (*o).m_cs_sz).write(aligned as u16);
        o
    }
}

/// Nullable big-path core: exact requested size, `m_cs_sz = 0` marks the big
/// path in live headers (`object.cpp:364-370`). Returns null on exhaustion.
///
/// # Safety
/// As [`alloc_big`]; null must be handled by the caller.
// UNSAFE-LEDGER: FLN-UL-0067
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_big_nullable(sz: usize) -> *mut LeanObject {
    // SAFETY: freshly allocated, exclusively owned, at least 8 bytes.
    unsafe {
        let p = alloc(obj_layout(sz));
        if p.is_null() {
            return core::ptr::null_mut();
        }
        let o = p.cast::<LeanObject>();
        (&raw mut (*o).m_cs_sz).write(0);
        o
    }
}

/// Big-path allocation: `lean_alloc_object` under `LEAN_MIMALLOC`
/// (`object.cpp:355-376`). `m_cs_sz = 0` marks the big path in live headers.
///
/// # Safety
/// As [`alloc_small`]; additionally the caller must retain `sz` knowledge
/// (big-object byte size is recomputed from salient fields at release).
// UNSAFE-LEDGER: FLN-UL-0002
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_big(sz: usize) -> *mut LeanObject {
    // SAFETY: delegated; null handled by aborting exactly like alloc_small.
    unsafe {
        let o = alloc_big_nullable(sz);
        if o.is_null() {
            handle_alloc_error(obj_layout(sz));
        }
        o
    }
}

/// `lean_alloc_ctor_memory` under `LEAN_MIMALLOC` (`lean.h:454-461`): small
/// allocation plus deterministic zeroing of the final padded word.
///
/// # Safety
/// As [`alloc_small`].
// UNSAFE-LEDGER: FLN-UL-0003
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_ctor_memory(sz: usize) -> *mut LeanObject {
    let aligned = align_obj_size(sz);
    // SAFETY: delegated, exactly as this function's own `# Safety` clause says
    // ("As `alloc_small`"): the caller has already discharged `alloc_small`'s
    // obligation, so calling it here adds none.
    let o = unsafe { alloc_small(sz) };
    if aligned > sz {
        // SAFETY: the block is `aligned` bytes; the final word is in-bounds.
        unsafe {
            o.cast::<u8>()
                .add(aligned - size_of::<usize>())
                .cast::<usize>()
                .write(0);
        }
    }
    o
}

/// Release a CompatHeap block of known byte size (small callers pass the
/// header's `m_cs_sz`; big callers pass the recomputed category byte size,
/// mirroring `lean_free_object`, `object.cpp:271-280`). The header's
/// `m_cs_sz` discriminates the paths exactly as the pin's live headers do:
/// non-zero = small heap (prefix-sized release), zero = big heap (sized
/// release).
///
/// Shadow discipline: with shadows enabled the memory is quarantined (header
/// tag poisoned to `TAG_RESERVED`, block retained) and faulty releases are
/// skipped entirely — quarantine, never corruption.
///
/// # Safety
/// `o` must have been minted by this module with byte size `size` and must
/// not be used after this call (shadow mode detects violations; release mode
/// trusts the caller exactly as the Reference does).
// UNSAFE-LEDGER: FLN-UL-0004
#[allow(unsafe_code)]
pub(crate) unsafe fn release_with_size(o: *mut LeanObject, size: usize, op: &'static str) {
    // SAFETY: caller guarantees `o` is a live membrane object; the tag and
    // cs_sz reads precede any state change.
    let (category, cs_sz) = unsafe {
        (
            (&raw const (*o).m_tag).read(),
            (&raw const (*o).m_cs_sz).read(),
        )
    };
    match shadow::on_free(o as usize, category, op) {
        shadow::FreeVerdict::Release => {
            if cs_sz != 0 {
                debug_assert!(usize::from(cs_sz) == size, "small release size drift");
                // SAFETY: non-zero cs_sz marks a small-heap block, which was
                // minted by small_alloc_raw and carries the size prefix.
                unsafe { small_free_raw(o.cast::<u8>()) };
            } else {
                // SAFETY: big blocks are minted by alloc_big{,_nullable} with
                // exactly this size/alignment pair.
                unsafe { dealloc(o.cast::<u8>(), obj_layout(size)) };
            }
        }
        shadow::FreeVerdict::Quarantine => {
            // SAFETY: block retained; poisoning the tag keeps later misuse
            // deterministically detectable.
            unsafe { (&raw mut (*o).m_tag).write(TAG_RESERVED) };
        }
        shadow::FreeVerdict::Fault => {}
    }
}

/// Record a freshly initialized object with the shadow registry (no-op when
/// shadows are disabled). Called by every constructor after header init.
pub(crate) fn note_alloc(o: *mut LeanObject, size: usize, category: u8) {
    shadow::on_alloc(o as usize, size, category);
}
