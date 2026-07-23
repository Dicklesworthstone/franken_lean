//! Tri-state reference counting (plan §6.2, bead fln-lld) — the exact
//! Reference discipline (`lean.h:535-583`, `object.cpp:335-457`):
//!
//! * `m_rc > 0`: single-threaded plain count (fast path).
//! * `m_rc < 0`: multi-threaded negative count; increment is atomic
//!   `fetch_sub`, decrement is atomic `fetch_add`, and the object dies when
//!   a decrement observes `-1` (`object.cpp:443-457`).
//! * `m_rc == 0`: persistent — never counted (compact-region residents and
//!   `lean_mark_persistent` graphs).
//!
//! Deletion is an explicit iterative worklist exactly like upstream's todo
//! list (`object.cpp:431-441`) — never recursion, so teardown depth is
//! bounded on any stack (the dev-box "unlimited stack" trap is covered by a
//! bounded-stack test). Upstream threads the todo list through dead object
//! headers; we use a `Vec`, which is observationally identical (the header
//! repurposing is only ever visible to the allocator's own dead objects) and
//! keeps headers intact for the shadow quarantine.

use crate::contract::{
    TAG_ARRAY, TAG_CLOSURE, TAG_EXTERNAL, TAG_MAX_CTOR_TAG, TAG_MPZ, TAG_PROMISE, TAG_REF,
    TAG_RESERVED, TAG_SCALAR_ARRAY, TAG_STRING, TAG_TASK, TAG_THUNK,
};
use crate::layout::{
    LeanArrayObject, LeanClosureObject, LeanObject, LeanPromiseObject, LeanSarrayObject,
    LeanStringObject,
};
use crate::membrane;
use crate::object;
use crate::shadow;
use crate::tagged::is_scalar;
use core::sync::atomic::{AtomicI32, Ordering};

/// A loaded object header (plain reads, mirroring the C fast paths' direct
/// field access).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Header {
    pub rc: i32,
    pub cs_sz: u16,
    pub other: u8,
    pub tag: u8,
}

/// Load the header of a live object.
///
/// # Safety
/// `o` must point at a live (or quarantined) membrane object; must not be a
/// boxed scalar.
// UNSAFE-LEDGER: FLN-UL-0035
#[allow(unsafe_code)]
pub(crate) unsafe fn read_header(o: *mut LeanObject) -> Header {
    debug_assert!(!is_scalar(o));
    // SAFETY: live object per caller contract; plain reads mirror the C
    // fast-path access discipline.
    unsafe {
        Header {
            rc: (&raw const (*o).m_rc).read(),
            cs_sz: (&raw const (*o).m_cs_sz).read(),
            other: (&raw const (*o).m_other).read(),
            tag: (&raw const (*o).m_tag).read(),
        }
    }
}

/// `lean_set_st_header` under `LEAN_MIMALLOC` (`lean.h:635-643`): `m_rc = 1`,
/// tag and `m_other` set, `m_cs_sz` left exactly as allocation wrote it.
///
/// # Safety
/// `o` freshly minted by the membrane and not yet shared.
// UNSAFE-LEDGER: FLN-UL-0036
#[allow(unsafe_code)]
pub(crate) unsafe fn init_st_header(o: *mut LeanObject, tag: u8, other: u8) {
    // SAFETY: exclusive access to a fresh allocation.
    unsafe {
        (&raw mut (*o).m_rc).write(1);
        (&raw mut (*o).m_other).write(other);
        (&raw mut (*o).m_tag).write(tag);
    }
}

/// `lean_get_rc_mt_addr` (`lean.h:552-554`): the MT branches address `m_rc`
/// atomically while ST/persistent branches read it plainly — the exact mixed
/// discipline the Reference compiles to.
///
/// # Safety
/// `o` live object; `m_rc` is 4-aligned by the header layout.
// UNSAFE-LEDGER: FLN-UL-0037
#[allow(unsafe_code)]
unsafe fn atomic_rc<'a>(o: *mut LeanObject) -> &'a AtomicI32 {
    // SAFETY: m_rc is a valid, 4-aligned i32 within a live object; AtomicI32
    // has the same layout as i32.
    unsafe { AtomicI32::from_ptr(&raw mut (*o).m_rc) }
}

/// `lean_inc_ref_n` (`lean.h:556-566`). ST: plain add. MT: atomic
/// `fetch_sub` (the count is negative). Persistent: no-op.
///
/// # Safety
/// `o` live non-scalar object.
// UNSAFE-LEDGER: FLN-UL-0038
#[allow(unsafe_code)]
pub(crate) unsafe fn inc_ref_n(o: *mut LeanObject, n: usize) {
    if !shadow::check_rc_target(o as usize, "inc_ref_n") {
        return;
    }
    // SAFETY: live object; ST branch has single-thread exclusivity by the
    // tri-state invariant, MT branch is atomic.
    unsafe {
        let rc = (&raw const (*o).m_rc).read();
        if rc > 0 {
            let n = i32::try_from(n).expect("rc increment overflows i32");
            debug_assert!(rc.checked_add(n).is_some(), "single-threaded RC overflow");
            (&raw mut (*o).m_rc).write(rc.wrapping_add(n));
        } else if rc != 0 {
            atomic_rc(o).fetch_sub(
                i32::try_from(n).expect("rc increment overflows i32"),
                Ordering::Relaxed,
            );
        }
    }
}

/// `lean_dec_ref` (`lean.h:574-580`): fast decrement, cold path at 1/MT.
///
/// # Safety
/// `o` live non-scalar object; the caller gives up one owned reference.
// UNSAFE-LEDGER: FLN-UL-0039
#[allow(unsafe_code)]
pub(crate) unsafe fn dec_ref(o: *mut LeanObject) {
    if !shadow::check_rc_target(o as usize, "dec_ref") {
        return;
    }
    // SAFETY: live object; branches mirror the upstream inline exactly.
    unsafe {
        let rc = (&raw const (*o).m_rc).read();
        if rc > 1 {
            (&raw mut (*o).m_rc).write(rc - 1);
        } else if rc != 0 {
            dec_ref_cold(o);
        }
    }
}

/// The worklist child-decrement — `dec(o, todo)` in `object.cpp:335-347`.
///
/// # Safety
/// `o` valid object pointer or boxed scalar; one owned reference given up.
// UNSAFE-LEDGER: FLN-UL-0040
#[allow(unsafe_code)]
unsafe fn dec_child(o: *mut LeanObject, todo: &mut Vec<*mut LeanObject>) {
    if is_scalar(o) {
        return;
    }
    if !shadow::check_rc_target(o as usize, "dec_child") {
        return;
    }
    // SAFETY: live object; mirrors object.cpp's dec() including the MT
    // acquire-release handshake on the last release.
    unsafe {
        let rc = (&raw const (*o).m_rc).read();
        if rc > 1 {
            (&raw mut (*o).m_rc).write(rc - 1);
        } else if rc == 1 {
            todo.push(o);
        } else if rc == 0 {
        } else if atomic_rc(o).fetch_add(1, Ordering::AcqRel) == -1 {
            todo.push(o);
        }
    }
}

/// `lean_object_byte_size` (`object.cpp:242-259` under `LEAN_MIMALLOC`):
/// big-path categories compute from salient fields; small-path categories
/// report the header's `m_cs_sz`.
///
/// # Safety
/// `o` live non-scalar object.
// UNSAFE-LEDGER: FLN-UL-0041
#[allow(unsafe_code)]
pub(crate) unsafe fn object_byte_size(o: *mut LeanObject) -> usize {
    // SAFETY: live object; each arm reads only that category's salient
    // fields, per the size formulas in lean.h (array:857, sarray:1048,
    // string:1209, closure:818).
    unsafe {
        let h = read_header(o);
        match h.tag {
            t if t == TAG_ARRAY => {
                size_of::<LeanArrayObject>()
                    + size_of::<*mut LeanObject>() * object::array_fields(o).1
            }
            t if t == TAG_SCALAR_ARRAY => {
                let (elem, _, cap, _) = object::sarray_fields(o);
                size_of::<LeanSarrayObject>() + usize::from(elem) * cap
            }
            t if t == TAG_STRING => {
                let s = o.cast::<LeanStringObject>();
                size_of::<LeanStringObject>() + (&raw const (*s).m_capacity).read()
            }
            t if t == TAG_CLOSURE => {
                let c = o.cast::<LeanClosureObject>();
                size_of::<LeanClosureObject>()
                    + size_of::<*mut LeanObject>()
                        * usize::from((&raw const (*c).m_num_fixed).read())
            }
            _ => usize::from(h.cs_sz),
        }
    }
}

/// `lean_del_core` + `lean_del_core_other` (`object.cpp:381-441`): release
/// one dead object, pushing its owned children on the worklist.
///
/// Slice-1 restrictions (typed, not silent): tasks must be Finished
/// (`m_imp == NULL`; scheduled tasks arrive with bead fln-3gv) and external
/// finalizers run but `m_foreach` is never needed on the death path.
///
/// # Safety
/// `o` dead (this call owns the last reference) non-scalar membrane object.
// UNSAFE-LEDGER: FLN-UL-0042
#[allow(unsafe_code)]
unsafe fn del_core(o: *mut LeanObject, todo: &mut Vec<*mut LeanObject>) {
    // SAFETY: last-reference ownership; every read precedes the release of
    // the block it reads from; children ownership transfers to the worklist.
    unsafe {
        let h = read_header(o);
        let sz = object_byte_size(o);
        if h.tag <= TAG_MAX_CTOR_TAG {
            for i in 0..usize::from(h.other) {
                dec_child(object::ctor_get(o, i), todo);
            }
            membrane::release_with_size(o, sz, "del.ctor");
            return;
        }
        match h.tag {
            t if t == TAG_CLOSURE => {
                let (_, _, num_fixed, args) = object::closure_fields(o);
                for i in 0..usize::from(num_fixed) {
                    dec_child(args.add(i).read(), todo);
                }
                membrane::release_with_size(o, sz, "del.closure");
            }
            t if t == TAG_ARRAY => {
                let (size, _) = object::array_fields(o);
                for i in 0..size {
                    dec_child(object::array_get(o, i), todo);
                }
                membrane::release_with_size(o, sz, "del.array");
            }
            t if t == TAG_SCALAR_ARRAY => membrane::release_with_size(o, sz, "del.sarray"),
            t if t == TAG_STRING => membrane::release_with_size(o, sz, "del.string"),
            t if t == TAG_MPZ => {
                object::mpz_drop_limbs(o);
                membrane::release_with_size(o, sz, "del.mpz");
            }
            t if t == TAG_THUNK => {
                let (v, c) = object::thunk_fields(o);
                if !c.is_null() {
                    dec_child(c, todo);
                }
                if !v.is_null() {
                    dec_child(v, todo);
                }
                membrane::release_with_size(o, sz, "del.thunk");
            }
            t if t == TAG_REF => {
                let v = object::ref_value(o);
                if !v.is_null() {
                    dec_child(v, todo);
                }
                membrane::release_with_size(o, sz, "del.ref");
            }
            t if t == TAG_TASK => {
                let (v, imp) = object::task_fields(o);
                debug_assert!(
                    imp.is_null(),
                    "scheduled tasks require fln-3gv (deactivate_task)"
                );
                if !imp.is_null() {
                    shadow::on_traversal_skip(TAG_TASK, "del.task.imp");
                }
                if !v.is_null() {
                    dec_child(v, todo);
                }
                membrane::release_with_size(o, sz, "del.task");
            }
            t if t == TAG_PROMISE => {
                let r = (&raw const (*o.cast::<LeanPromiseObject>()).m_result).read();
                if !r.is_null() {
                    dec_child(r.cast::<LeanObject>(), todo);
                }
                membrane::release_with_size(o, sz, "del.promise");
            }
            t if t == TAG_EXTERNAL => {
                let (class, data) = object::external_fields(o);
                ((*class).m_finalize)(data);
                membrane::release_with_size(o, sz, "del.external");
            }
            t if t == TAG_RESERVED => {
                debug_assert!(false, "del on reserved/poisoned tag");
                shadow::on_traversal_skip(TAG_RESERVED, "del.reserved");
            }
            _ => unreachable!("del_core: unknown tag {}", h.tag),
        }
    }
}

/// `lean_dec_ref_cold` (`object.cpp:443-457`): the death test plus the
/// iterative deletion loop.
///
/// # Safety
/// `o` live non-scalar object whose caller gives up one owned reference and
/// has already observed `m_rc == 1 || m_rc < 0`.
// UNSAFE-LEDGER: FLN-UL-0043
#[allow(unsafe_code)]
unsafe fn dec_ref_cold(o: *mut LeanObject) {
    // SAFETY: mirrors the upstream cold path exactly; the AcqRel fetch_add
    // pairs MT decrements so exactly one thread observes -1 and frees.
    unsafe {
        let rc = (&raw const (*o).m_rc).read();
        if rc == 1 || atomic_rc(o).fetch_add(1, Ordering::AcqRel) == -1 {
            let mut todo: Vec<*mut LeanObject> = Vec::new();
            del_core(o, &mut todo);
            while let Some(next) = todo.pop() {
                del_core(next, &mut todo);
            }
        }
    }
}

/// `lean_mark_persistent` (`object.cpp:553-620`): iteratively zero `m_rc`
/// over the reachable graph. Slice-1 restriction: external objects cannot be
/// traversed (their `m_foreach` takes a Lean closure — bead franken_lean-7xe);
/// encountering one is a typed skip, asserted in debug.
///
/// # Safety
/// `o` valid object pointer or boxed scalar; the graph must not be mutated
/// concurrently (upstream requires the same).
// UNSAFE-LEDGER: FLN-UL-0044
#[allow(unsafe_code)]
pub(crate) unsafe fn mark_persistent(o: *mut LeanObject) {
    let mut todo = vec![o];
    // SAFETY: every pointer pushed is a child slot read from a live object;
    // traversal matches object.cpp's category switch.
    unsafe {
        while let Some(o) = todo.pop() {
            if is_scalar(o) {
                continue;
            }
            let h = read_header(o);
            if h.rc == 0 {
                continue;
            }
            (&raw mut (*o).m_rc).write(0);
            push_children(o, h, &mut todo, "mark_persistent");
        }
    }
}

/// `lean_mark_mt` (`object.cpp:633-681`): negate ST counts over the graph.
///
/// # Safety
/// As [`mark_persistent`].
// UNSAFE-LEDGER: FLN-UL-0045
#[allow(unsafe_code)]
pub(crate) unsafe fn mark_mt(o: *mut LeanObject) {
    if is_scalar(o) {
        return;
    }
    // SAFETY: as mark_persistent; only ST objects are flipped, exactly as
    // upstream (`if (lean_is_scalar(o) || !lean_is_st(o)) return`).
    unsafe {
        if (&raw const (*o).m_rc).read() <= 0 {
            return;
        }
        let mut todo = vec![o];
        while let Some(o) = todo.pop() {
            if is_scalar(o) {
                continue;
            }
            let h = read_header(o);
            if h.rc <= 0 {
                continue;
            }
            (&raw mut (*o).m_rc).write(-h.rc);
            push_children(o, h, &mut todo, "mark_mt");
        }
    }
}

/// Shared child-traversal for the mark walks (the category switches of
/// `object.cpp:571-617` / `646-681` minus the external/task arms the slice
/// cannot run).
///
/// # Safety
/// `o` live object with header `h`; `todo` receives borrowed child pointers.
// UNSAFE-LEDGER: FLN-UL-0046
#[allow(unsafe_code)]
unsafe fn push_children(
    o: *mut LeanObject,
    h: Header,
    todo: &mut Vec<*mut LeanObject>,
    op: &'static str,
) {
    // SAFETY: bounds come from the same header the caller loaded; each read
    // is within the category's salient area.
    unsafe {
        if h.tag <= TAG_MAX_CTOR_TAG {
            for i in 0..usize::from(h.other) {
                todo.push(object::ctor_get(o, i));
            }
            return;
        }
        match h.tag {
            t if t == TAG_SCALAR_ARRAY || t == TAG_STRING || t == TAG_MPZ => {}
            t if t == TAG_EXTERNAL => {
                debug_assert!(
                    false,
                    "external traversal requires apply machinery (franken_lean-7xe)"
                );
                shadow::on_traversal_skip(TAG_EXTERNAL, op);
            }
            t if t == TAG_TASK => {
                let (v, imp) = object::task_fields(o);
                debug_assert!(imp.is_null(), "scheduled tasks require fln-3gv");
                if !v.is_null() {
                    todo.push(v);
                }
            }
            t if t == TAG_PROMISE => {
                let r = (&raw const (*o.cast::<LeanPromiseObject>()).m_result).read();
                if !r.is_null() {
                    todo.push(r.cast::<LeanObject>());
                }
            }
            t if t == TAG_CLOSURE => {
                let (_, _, num_fixed, args) = object::closure_fields(o);
                for i in 0..usize::from(num_fixed) {
                    todo.push(args.add(i).read());
                }
            }
            t if t == TAG_ARRAY => {
                let (size, _) = object::array_fields(o);
                for i in 0..size {
                    todo.push(object::array_get(o, i));
                }
            }
            t if t == TAG_THUNK => {
                let (v, c) = object::thunk_fields(o);
                if !c.is_null() {
                    todo.push(c);
                }
                if !v.is_null() {
                    todo.push(v);
                }
            }
            t if t == TAG_REF => {
                let v = object::ref_value(o);
                if !v.is_null() {
                    todo.push(v);
                }
            }
            _ => unreachable!("push_children: unknown tag {}", h.tag),
        }
    }
}

/// Deterministic MT stress harness for the atomic RC lanes: after
/// `mark_mt`, `threads` scoped threads each perform `iters` balanced
/// inc/dec pairs; count conservation is exact regardless of interleaving.
/// Lives here so tests stay safe code.
///
/// # Safety
/// `o` live MT (or persistent) object that outlives the call.
// UNSAFE-LEDGER: FLN-UL-0047
#[allow(unsafe_code)]
pub(crate) unsafe fn mt_stress(o: *mut LeanObject, threads: usize, iters: usize) {
    struct SendPtr(*mut LeanObject);
    // SAFETY: MT objects are exactly the ones whose RC traffic is atomic;
    // the pointer outlives the scope per caller contract.
    // UNSAFE-LEDGER: FLN-UL-0048
    #[allow(unsafe_code)]
    unsafe impl Send for SendPtr {}
    std::thread::scope(|s| {
        for _ in 0..threads {
            let p = SendPtr(o);
            s.spawn(move || {
                let p = p;
                for _ in 0..iters {
                    // SAFETY: caller keeps `o` alive across the scope; all
                    // traffic on an MT object is atomic.
                    unsafe {
                        inc_ref_n(p.0, 1);
                        dec_ref(p.0);
                    }
                }
            });
        }
    });
}
