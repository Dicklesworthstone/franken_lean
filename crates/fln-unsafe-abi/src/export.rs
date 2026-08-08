//! The exported `lean_*` C symbol surface (plan §6.5/§6.6, bead
//! franken_lean-83r; the per-symbol census join fln-lld deferred here).
//!
//! Every function in this module is one exported symbol of the pinned ABI:
//! `#[unsafe(export_name = "…")]` under an `extern "C"` signature copied
//! from the generated census (`fln-rt::abi::FUNCTION_CENSUS`, itself
//! extracted from the pinned `lean.h` — Rule D5: derived, never remembered).
//! The reviewed status of every census export symbol lives in
//! `ci/ABI_EXPORT_STATUS.txt`; `tools/structure-guard` enforces the join in
//! both directions (an export without an implemented status row, and an
//! implemented row without an export site, both fail CI) — there is no
//! unclassified symbol (§6.5).
//!
//! **Panic law (§6.5):** no Rust panic crosses these boundaries. Every
//! function is `extern "C"`, so any internal panic aborts the process at
//! the boundary (Rust 2024 abort-on-unwind shim) — termination per policy,
//! never a fabricated Lean result. Where the pin *defines* an observable
//! failure behavior (`lean_internal_panic`'s message + exit path), the
//! wrapper reproduces that behavior exactly.
//!
//! **Membrane support symbols:** under the pin's `LEAN_MIMALLOC` config the
//! `lean.h` inlines call `mi_malloc_small`/`mi_free` directly
//! (`lean.h:436-441`, `490-497`), so generated C — stage0 translation units
//! included — link-demands those two symbols alongside the `lean_*` census.
//! They are exported here as the membrane's raw small heap (status
//! `RawPlatform` in the export-status ledger).
//!
//! Slice-1 typed restrictions (tracked in `ci/ABI_EXPORT_STATUS.txt`, never
//! silent): closure application (`lean_apply_*`) — franken_lean-7xe; the
//! task plane is LIVE (fln-3gv slices 2-3: the state family, the promise
//! family, and the manager — `task_manager.rs`), with the `io.cpp` wrapper
//! family (as_task/map_task/bind_task/wait/wait_any + the cancel wrappers)
//! and `wait_any_core` still fln-3gv's next slice; general IO
//! (`lean_io_*` beyond those) — fln-3gv; bignum arithmetic
//! (`lean_nat_big_*`, `lean_int_big_*`) — the fln-bignum shim; panic-path
//! Lean-buffered stderr and backtrace printing — fln-3gv (messages go to the
//! process stderr until the IO plane exists).

use crate::contract::TAG_MPZ;
use crate::layout::{LeanObject, LeanStringObject};
use crate::membrane;
use crate::object;
use crate::rc;
use crate::tagged::is_scalar;
use core::ffi::{c_char, c_uint, c_void};
use core::sync::atomic::{AtomicBool, Ordering};
use std::io::Write;

// ---------------------------------------------------------------- panic core

/// `g_exit_on_panic` (`object.cpp:113`).
static EXIT_ON_PANIC: AtomicBool = AtomicBool::new(false);
/// `g_panic_messages` (`object.cpp:114`).
static PANIC_MESSAGES: AtomicBool = AtomicBool::new(true);

/// `should_abort_on_panic` (`object.cpp`): the `LEAN_ABORT_ON_PANIC`
/// environment probe, checked at panic time exactly as upstream.
fn should_abort_on_panic() -> bool {
    std::env::var_os("LEAN_ABORT_ON_PANIC").is_some()
}

/// `lean_internal_panic`'s body (`object.cpp:91-95`): message to the process
/// stderr, then abort (env) or `exit(1)`.
pub(crate) fn internal_panic_impl(msg: &str) -> ! {
    let mut err = std::io::stderr().lock();
    let _ = writeln!(err, "INTERNAL PANIC: {msg}");
    let _ = err.flush();
    if should_abort_on_panic() {
        std::process::abort();
    }
    std::process::exit(1);
}

/// `lean_panic_impl` (`object.cpp:175-191`): the two-arm message router
/// then the abort/exit policy, in the pin's order (abort BEFORE exit,
/// object.cpp:187-190). The arm chooser is `panic_eprintln`'s exactly
/// (object.cpp:131): fatal-bound — `force_stderr`, exit-on-panic, or the
/// abort env — writes the process stderr, because the Lean buffer would
/// die with the process; the NON-FATAL arm routes through the
/// thread-current stderr STREAM (fln-3gv slice 8d over the seam measured
/// in bead comment 2111), falling back to the process stderr only for a
/// foreign-closure stream — the disclosed 7xe boundary. The backtrace
/// block (object.cpp:178-184) remains open with fln-3gv.
pub(crate) fn panic_impl(msg: &[u8], force_stderr: bool) {
    if PANIC_MESSAGES.load(Ordering::Relaxed) {
        let fatal_bound =
            force_stderr || EXIT_ON_PANIC.load(Ordering::Relaxed) || should_abort_on_panic();
        if fatal_bound || !crate::stdio::panic_message_via_stream(msg) {
            let mut err = std::io::stderr().lock();
            let _ = err.write_all(msg);
            let _ = err.write_all(b"\n");
            let _ = err.flush();
        }
    }
    if should_abort_on_panic() {
        std::process::abort();
    }
    if EXIT_ON_PANIC.load(Ordering::Relaxed) {
        std::process::exit(1);
    }
}

// ---------------------------------------------------------------- UTF-8 core
// Safe ports of `utf8.cpp` — bit-for-bit the pin's semantics, including its
// deliberate quirks (`get_utf8_size` treats every invalid lead byte as one
// char, so `lean_utf8_strlen` over garbage counts garbage bytes — that IS
// the contract).

/// `get_utf8_size` (`utf8.cpp:16-33`).
fn get_utf8_size(c: u8) -> usize {
    if c & 0x80 == 0 {
        1
    } else if c & 0xE0 == 0xC0 {
        2
    } else if c & 0xF0 == 0xE0 {
        3
    } else if c & 0xF8 == 0xF0 {
        4
    } else if c & 0xFC == 0xF8 {
        5
    } else if c & 0xFE == 0xFC {
        6
    } else {
        1 // 0xFF and stray continuations: 1, exactly as upstream
    }
}

/// `validate_utf8_one` (`utf8.cpp:223-268`).
fn validate_utf8_one(s: &[u8], pos: &mut usize) -> bool {
    let size = s.len();
    let c = u32::from(s[*pos]);
    if c & 0x80 == 0 {
        *pos += 1;
    } else if c & 0xE0 == 0xC0 {
        if *pos + 1 >= size {
            return false;
        }
        let c1 = u32::from(s[*pos + 1]);
        if c1 & 0xC0 != 0x80 {
            return false;
        }
        let r = ((c & 0x1F) << 6) | (c1 & 0x3F);
        if r < 0x80 {
            return false;
        }
        *pos += 2;
    } else if c & 0xF0 == 0xE0 {
        if *pos + 2 >= size {
            return false;
        }
        let c1 = u32::from(s[*pos + 1]);
        let c2 = u32::from(s[*pos + 2]);
        if c1 & 0xC0 != 0x80 || c2 & 0xC0 != 0x80 {
            return false;
        }
        let r = ((c & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
        if r < 0x800 || (0xD800..=0xDFFF).contains(&r) {
            return false;
        }
        *pos += 3;
    } else if c & 0xF8 == 0xF0 {
        if *pos + 3 >= size {
            return false;
        }
        let c1 = u32::from(s[*pos + 1]);
        let c2 = u32::from(s[*pos + 2]);
        let c3 = u32::from(s[*pos + 3]);
        if c1 & 0xC0 != 0x80 || c2 & 0xC0 != 0x80 || c3 & 0xC0 != 0x80 {
            return false;
        }
        let r = ((c & 0x07) << 18) | ((c1 & 0x3F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
        if !(0x10000..=0x10FFFF).contains(&r) {
            return false;
        }
        *pos += 4;
    } else {
        return false;
    }
    true
}

/// `validate_utf8` (`utf8.cpp:270-276`): on failure `pos` is the end of the
/// valid prefix and `i` the codepoints seen so far.
fn validate_utf8(s: &[u8], pos: &mut usize, i: &mut usize) -> bool {
    while *pos < s.len() {
        if !validate_utf8_one(s, pos) {
            return false;
        }
        *i += 1;
    }
    true
}

/// `utf8_strlen(str, sz)` = `lean_utf8_n_strlen` (`utf8.cpp:49-58`).
fn utf8_n_strlen_impl(s: &[u8]) -> usize {
    let mut r = 0usize;
    let mut i = 0usize;
    while i < s.len() {
        i += get_utf8_size(s[i]);
        r += 1;
    }
    r
}

/// `lean_mk_string_lossy_recover` (`object.cpp:1989-2002`): the pin's exact
/// U+FFFD replacement walk, `i` counting replacements as codepoints.
///
/// # Safety
/// Only the constructor call is unsafe; the recovered bytes are an owned
/// copy, so the caller owes nothing beyond the slice being readable.
// UNSAFE-LEDGER: FLN-UL-0068
#[allow(unsafe_code)]
unsafe fn mk_string_lossy_recover(s: &[u8], mut pos: usize, mut i: usize) -> *mut LeanObject {
    let mut out: Vec<u8> = s[..pos].to_vec();
    let mut start = pos;
    while pos < s.len() {
        if !validate_utf8_one(s, &mut pos) {
            out.extend_from_slice(&s[start..pos]);
            out.extend_from_slice("\u{FFFD}".as_bytes());
            pos += 1;
            while pos < s.len() && s[pos] & 0xC0 == 0x80 {
                pos += 1;
            }
            start = pos;
        }
        i += 1;
    }
    out.extend_from_slice(&s[start..pos]);
    // SAFETY: constructor over an owned byte copy with the recomputed count.
    unsafe { object::mk_string_unchecked(&out, i) }
}

/// Shared body of `lean_mk_string_from_bytes` (`object.cpp:2005-2012`).
///
/// # Safety
/// `s`/`sz` must describe `sz` readable bytes (or `sz == 0`).
// UNSAFE-LEDGER: FLN-UL-0069
#[allow(unsafe_code)]
pub(crate) unsafe fn mk_string_from_bytes_impl(s: *const c_char, sz: usize) -> *mut LeanObject {
    // SAFETY: caller (C contract) vouches for sz readable bytes.
    let bytes = if sz == 0 {
        &[][..]
    } else {
        // SAFETY: the note above, stated where a mechanical reader looks for
        // it. `sz > 0` in this arm and the caller's C contract vouches for `sz`
        // readable bytes at `s`; the slice only borrows them for this call.
        unsafe { core::slice::from_raw_parts(s.cast::<u8>(), sz) }
    };
    let mut pos = 0usize;
    let mut i = 0usize;
    if validate_utf8(bytes, &mut pos, &mut i) {
        // SAFETY: constructor over an owned byte copy.
        unsafe { object::mk_string_unchecked(&bytes[..pos], i) }
    } else {
        // SAFETY: bytes readable per this function's own contract.
        unsafe { mk_string_lossy_recover(bytes, pos, i) }
    }
}

/// `strlen` over a NUL-terminated C string.
///
/// # Safety
/// `s` must be a valid NUL-terminated string.
// UNSAFE-LEDGER: FLN-UL-0070
#[allow(unsafe_code)]
unsafe fn c_strlen(s: *const c_char) -> usize {
    // SAFETY: caller vouches for NUL termination; CStr walks to the NUL.
    unsafe { core::ffi::CStr::from_ptr(s).to_bytes().len() }
}

/// String salient reads without copying: `(m_size, data ptr)`.
///
/// # Safety
/// `o` live string object.
// UNSAFE-LEDGER: FLN-UL-0071
#[allow(unsafe_code)]
unsafe fn string_size_and_data(o: *mut LeanObject) -> (usize, *const u8) {
    // SAFETY: live string per caller contract; m_size bytes are salient.
    unsafe {
        let s = o.cast::<LeanStringObject>();
        (
            (&raw const (*s).m_size).read(),
            (&raw const (*s).m_data).cast::<u8>(),
        )
    }
}

// ================================================================ exports
// One `#[unsafe(export_name)]` site per census symbol; signatures are the
// census signatures. Rust-side callers (tests) use the `export_*` names.

// ---- membrane: the small heap ------------------------------------------------

/// `lean_alloc_small` (`lean.h:400`, SMALL_ALLOCATOR surface): raw
/// small-heap block of `sz` bytes; OOM panics like the pin's allocator.
// UNSAFE-LEDGER: FLN-UL-0072
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_alloc_small")]
pub(crate) extern "C" fn export_lean_alloc_small(sz: c_uint, slot_idx: c_uint) -> *mut c_void {
    debug_assert!(sz > 0 && sz.is_multiple_of(8));
    debug_assert!(slot_idx == sz / 8 - 1, "lean_get_slot_idx law (lean.h:394)");
    let _ = slot_idx;
    membrane::charge_small_allocation();
    // SAFETY: sz > 0 per the inline callers' contract (asserted upstream).
    let p = unsafe { membrane::small_alloc_raw(sz as usize) };
    if p.is_null() {
        internal_panic_impl("out of memory");
    }
    p.cast::<c_void>()
}

/// `lean_free_small` (`lean.h:401`): sizeless small-heap release.
// UNSAFE-LEDGER: FLN-UL-0073
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_free_small")]
pub(crate) extern "C" fn export_lean_free_small(p: *mut c_void) {
    // SAFETY: p was minted by the small heap per the ABI contract.
    unsafe { membrane::small_free_raw(p.cast::<u8>()) };
}

/// `lean_small_mem_size` (`lean.h:402`): usable size of a small-heap block.
// UNSAFE-LEDGER: FLN-UL-0074
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_small_mem_size")]
pub(crate) extern "C" fn export_lean_small_mem_size(p: *mut c_void) -> c_uint {
    // SAFETY: p live small-heap block per the ABI contract.
    let sz = unsafe { membrane::small_mem_size_raw(p.cast::<u8>()) };
    sz as c_uint
}

/// `mi_malloc_small` (mimalloc.h:126; membrane support): the pin's
/// `LEAN_MIMALLOC` inlines call this directly (`lean.h:436-441`). Null on
/// exhaustion — the C inline performs the OOM panic itself.
// UNSAFE-LEDGER: FLN-UL-0075
#[allow(unsafe_code)]
#[unsafe(export_name = "mi_malloc_small")]
pub(crate) extern "C" fn export_mi_malloc_small(size: usize) -> *mut c_void {
    if size == 0 {
        // malloc(0) contract: a unique releasable pointer.
        // SAFETY: 8-byte block stands in for the zero-size allocation.
        return unsafe { membrane::small_alloc_raw(8) }.cast::<c_void>();
    }
    // SAFETY: size > 0.
    unsafe { membrane::small_alloc_raw(size) }.cast::<c_void>()
}

/// `mi_free` (mimalloc.h:115; membrane support): sizeless release,
/// null-safe like `free`.
// UNSAFE-LEDGER: FLN-UL-0076
#[allow(unsafe_code)]
#[unsafe(export_name = "mi_free")]
pub(crate) extern "C" fn export_mi_free(p: *mut c_void) {
    if p.is_null() {
        return;
    }
    // SAFETY: non-null p was minted by the small heap per the ABI contract.
    unsafe { membrane::small_free_raw(p.cast::<u8>()) };
}

// ---- membrane: the big heap --------------------------------------------------

/// `lean_alloc_object` (`object.cpp:355-376` under `LEAN_MIMALLOC`): exact
/// `sz` bytes, `m_cs_sz = 0`; OOM = `lean_internal_panic_out_of_memory`.
// UNSAFE-LEDGER: FLN-UL-0077
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_alloc_object")]
pub(crate) extern "C" fn export_lean_alloc_object(sz: usize) -> *mut LeanObject {
    // SAFETY: fresh exclusive block; cs_sz written by the callee.
    let o = unsafe { membrane::alloc_big_nullable(sz) };
    if o.is_null() {
        internal_panic_impl("out of memory");
    }
    o
}

/// `lean_free_object` (`object.cpp:271-280`): category-dispatched release —
/// big categories by recomputed byte size, `LeanMPZ` drops its limbs first,
/// everything else through the small heap.
// UNSAFE-LEDGER: FLN-UL-0078
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_free_object")]
pub(crate) extern "C" fn export_lean_free_object(o: *mut LeanObject) {
    // SAFETY: o is a live membrane object whose storage the caller releases;
    // the byte size is recomputed from salient fields exactly as upstream,
    // and release_with_size discriminates small/big on the header's cs_sz.
    unsafe {
        let h = rc::read_header(o);
        if h.tag == TAG_MPZ {
            object::mpz_drop_limbs(o);
        }
        let sz = rc::object_byte_size(o);
        membrane::release_with_size(o, sz, "export.free_object");
    }
}

// ---- heartbeat ---------------------------------------------------------------

/// `lean_inc_heartbeat` (`alloc.cpp:493-496`): allocation-linked thread-local
/// counter, distinct from `interrupt.cpp`'s `check_system` poll counter.
// UNSAFE-LEDGER: FLN-UL-0079
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_inc_heartbeat")]
pub(crate) extern "C" fn export_lean_inc_heartbeat() {
    membrane::add_heartbeats(1);
}

/// `IO.getNumHeartbeats` (`io.cpp:952-955`): snapshot the allocation-linked
/// counter and return it as an owned Lean `Nat`.
// UNSAFE-LEDGER: FLN-UL-0200
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_get_num_heartbeats")]
pub(crate) extern "C" fn export_lean_io_get_num_heartbeats() -> *mut LeanObject {
    let count = membrane::get_num_heartbeats();
    if count <= crate::tagged::MAX_SMALL_NAT as u64 {
        crate::tagged::boxi(count as usize)
    } else {
        export_lean_big_uint64_to_nat(count)
    }
}

/// `IO.setNumHeartbeats` (`io.cpp:957-962`): consume a Lean `Nat`, install its
/// low 64 bits as this runtime thread's allocation-linked counter, and return
/// `Unit`.
// UNSAFE-LEDGER: FLN-UL-0201
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_set_heartbeats")]
pub(crate) extern "C" fn export_lean_io_set_heartbeats(count: *mut LeanObject) -> *mut LeanObject {
    let value = if is_scalar(count) {
        crate::tagged::unbox(count) as u64
    } else {
        export_lean_uint64_of_big_nat(count)
    };
    membrane::set_heartbeats(value);
    // SAFETY: `count` is an owned `Nat` by the generated extern contract;
    // conversion above only borrowed it, so the wrapper now consumes it.
    unsafe { dec(count) };
    crate::tagged::boxi(0)
}

// ---- reference counting ------------------------------------------------------

/// `lean_dec_ref_cold` (`object.cpp:443-457`): the death test plus the
/// iterative deletion loop.
// UNSAFE-LEDGER: FLN-UL-0080
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_dec_ref_cold")]
pub(crate) extern "C" fn export_lean_dec_ref_cold(o: *mut LeanObject) {
    // SAFETY: caller observed rc == 1 || rc < 0 and gives up one reference
    // (the lean_dec_ref inline's contract, lean.h:574-580).
    unsafe { rc::dec_ref_cold(o) };
}

/// `lean_mark_persistent` (`object.cpp:553-620`).
// UNSAFE-LEDGER: FLN-UL-0081
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mark_persistent")]
pub(crate) extern "C" fn export_lean_mark_persistent(o: *mut LeanObject) {
    // SAFETY: o valid object or boxed scalar; graph not concurrently mutated
    // (upstream's own requirement).
    unsafe { rc::mark_persistent(o) };
}

/// `lean_mark_mt` (`object.cpp:633-681`).
// UNSAFE-LEDGER: FLN-UL-0082
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mark_mt")]
pub(crate) extern "C" fn export_lean_mark_mt(o: *mut LeanObject) {
    // SAFETY: as lean_mark_persistent.
    unsafe { rc::mark_mt(o) };
}

// ---- byte sizes --------------------------------------------------------------

/// `lean_object_byte_size` (`object.cpp:242-259`).
// UNSAFE-LEDGER: FLN-UL-0083
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_object_byte_size")]
pub(crate) extern "C" fn export_lean_object_byte_size(o: *mut LeanObject) -> usize {
    // SAFETY: o live non-scalar object per the ABI contract.
    unsafe { rc::object_byte_size(o) }
}

/// `lean_object_data_byte_size` (`object.cpp:237-259`): salient bytes only —
/// big categories from `m_size` (not capacity), small categories from
/// `m_cs_sz`; the upstream branch structure is kept literally.
// UNSAFE-LEDGER: FLN-UL-0084
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_object_data_byte_size")]
pub(crate) extern "C" fn export_lean_object_data_byte_size(o: *mut LeanObject) -> usize {
    use crate::contract::{TAG_ARRAY, TAG_CLOSURE, TAG_SCALAR_ARRAY, TAG_STRING};
    use crate::layout::{LeanArrayObject, LeanClosureObject, LeanSarrayObject};
    // SAFETY: o live non-scalar object; each arm reads only that category's
    // salient fields, mirroring object.cpp:237-259.
    unsafe {
        let h = rc::read_header(o);
        match h.tag {
            t if t == TAG_ARRAY => {
                size_of::<LeanArrayObject>()
                    + size_of::<*mut LeanObject>() * object::array_fields(o).0
            }
            t if t == TAG_SCALAR_ARRAY => {
                let (elem, size, _, _) = object::sarray_fields(o);
                size_of::<LeanSarrayObject>() + usize::from(elem) * size
            }
            t if t == TAG_STRING => {
                let (size, _) = string_size_and_data(o);
                size_of::<LeanStringObject>() + size
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

// ---- panics ------------------------------------------------------------------

/// `lean_internal_panic` (`object.cpp:91-95`).
// UNSAFE-LEDGER: FLN-UL-0085
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_internal_panic")]
pub(crate) extern "C" fn export_lean_internal_panic(msg: *const c_char) -> ! {
    // SAFETY: msg is a NUL-terminated C string per the contract.
    let text = unsafe { core::ffi::CStr::from_ptr(msg) }.to_string_lossy();
    internal_panic_impl(&text)
}

/// `lean_internal_panic_out_of_memory` (`object.cpp:97-99`).
// UNSAFE-LEDGER: FLN-UL-0086
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_internal_panic_out_of_memory")]
pub(crate) extern "C" fn export_lean_internal_panic_out_of_memory() -> ! {
    internal_panic_impl("out of memory")
}

/// `lean_internal_panic_overflow` (`object.cpp:109-111`).
// UNSAFE-LEDGER: FLN-UL-0087
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_internal_panic_overflow")]
pub(crate) extern "C" fn export_lean_internal_panic_overflow() -> ! {
    internal_panic_impl("integer overflow")
}

/// `lean_internal_panic_rc_overflow` (`object.cpp:105-107`).
// UNSAFE-LEDGER: FLN-UL-0088
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_internal_panic_rc_overflow")]
pub(crate) extern "C" fn export_lean_internal_panic_rc_overflow() -> ! {
    internal_panic_impl("reference counter overflowed")
}

/// `lean_internal_panic_unreachable` (`object.cpp:101-103`).
// UNSAFE-LEDGER: FLN-UL-0089
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_internal_panic_unreachable")]
pub(crate) extern "C" fn export_lean_internal_panic_unreachable() -> ! {
    internal_panic_impl("unreachable code has been reached")
}

/// `lean_panic` (`object.cpp` panic surface).
// UNSAFE-LEDGER: FLN-UL-0090
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_panic")]
pub(crate) extern "C" fn export_lean_panic(msg: *const c_char, force_stderr: bool) {
    // SAFETY: msg NUL-terminated per the contract.
    let bytes = unsafe { core::ffi::CStr::from_ptr(msg) }.to_bytes();
    panic_impl(bytes, force_stderr);
}

/// `lean_panic_fn` (`object.cpp`): print the Lean string `msg` (consumed),
/// return `default_val` (ownership passes through).
// UNSAFE-LEDGER: FLN-UL-0091
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_panic_fn")]
pub(crate) extern "C" fn export_lean_panic_fn(
    default_val: *mut LeanObject,
    msg: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: msg is a live string object; m_size-1 strips the NUL exactly
    // as upstream; the dec gives up the consumed reference.
    unsafe {
        let (size, data) = string_size_and_data(msg);
        let bytes = core::slice::from_raw_parts(data, size.saturating_sub(1));
        panic_impl(bytes, false);
        if !is_scalar(msg) {
            rc::dec_ref(msg);
        }
    }
    default_val
}

/// `lean_panic_fn_borrowed` (`object.cpp`): borrowed default is retained
/// before delegating.
// UNSAFE-LEDGER: FLN-UL-0092
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_panic_fn_borrowed")]
pub(crate) extern "C" fn export_lean_panic_fn_borrowed(
    default_val: *mut LeanObject,
    msg: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: default_val live (borrowed) — retaining it mirrors lean_inc.
    unsafe {
        if !is_scalar(default_val) {
            rc::inc_ref_n(default_val, 1);
        }
    }
    export_lean_panic_fn(default_val, msg)
}

/// `lean_set_exit_on_panic` (`object.cpp:116-118`).
// UNSAFE-LEDGER: FLN-UL-0093
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_set_exit_on_panic")]
pub(crate) extern "C" fn export_lean_set_exit_on_panic(flag: bool) {
    EXIT_ON_PANIC.store(flag, Ordering::Relaxed);
}

/// `lean_set_panic_messages` (`object.cpp:125-127`).
// UNSAFE-LEDGER: FLN-UL-0094
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_set_panic_messages")]
pub(crate) extern "C" fn export_lean_set_panic_messages(flag: bool) {
    PANIC_MESSAGES.store(flag, Ordering::Relaxed);
}

// ---- strings -----------------------------------------------------------------

/// `lean_mk_string_unchecked` (`object.cpp:1981-1987`).
// UNSAFE-LEDGER: FLN-UL-0095
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_string_unchecked")]
pub(crate) extern "C" fn export_lean_mk_string_unchecked(
    s: *const c_char,
    sz: usize,
    len: usize,
) -> *mut LeanObject {
    // SAFETY: sz readable bytes per the contract; constructor copies them.
    unsafe {
        let bytes = if sz == 0 {
            &[][..]
        } else {
            core::slice::from_raw_parts(s.cast::<u8>(), sz)
        };
        object::mk_string_unchecked(bytes, len)
    }
}

/// `lean_mk_string_from_bytes` (`object.cpp:2005-2012`): validate, else
/// lossy-recover with U+FFFD.
// UNSAFE-LEDGER: FLN-UL-0096
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_string_from_bytes")]
pub(crate) extern "C" fn export_lean_mk_string_from_bytes(
    s: *const c_char,
    sz: usize,
) -> *mut LeanObject {
    // SAFETY: sz readable bytes per the contract.
    unsafe { mk_string_from_bytes_impl(s, sz) }
}

/// `lean_mk_string_from_bytes_unchecked` (`object.cpp:2014-2016`).
// UNSAFE-LEDGER: FLN-UL-0097
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_string_from_bytes_unchecked")]
pub(crate) extern "C" fn export_lean_mk_string_from_bytes_unchecked(
    s: *const c_char,
    sz: usize,
) -> *mut LeanObject {
    // SAFETY: sz readable bytes per the contract.
    unsafe {
        let bytes = if sz == 0 {
            &[][..]
        } else {
            core::slice::from_raw_parts(s.cast::<u8>(), sz)
        };
        object::mk_string_unchecked(bytes, utf8_n_strlen_impl(bytes))
    }
}

/// `lean_mk_string` (`object.cpp:2018-2020`).
// UNSAFE-LEDGER: FLN-UL-0098
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_string")]
pub(crate) extern "C" fn export_lean_mk_string(s: *const c_char) -> *mut LeanObject {
    // SAFETY: NUL-terminated string per the contract.
    unsafe {
        let len = c_strlen(s);
        mk_string_from_bytes_impl(s, len)
    }
}

/// `lean_mk_ascii_string_unchecked` (`object.cpp:2022-2025`).
// UNSAFE-LEDGER: FLN-UL-0099
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_ascii_string_unchecked")]
pub(crate) extern "C" fn export_lean_mk_ascii_string_unchecked(
    s: *const c_char,
) -> *mut LeanObject {
    // SAFETY: NUL-terminated ASCII string per the contract.
    unsafe {
        let len = c_strlen(s);
        let bytes = core::slice::from_raw_parts(s.cast::<u8>(), len);
        object::mk_string_unchecked(bytes, len)
    }
}

/// `lean_utf8_strlen` (`utf8.cpp:35-43`): NUL-terminated walk with the
/// pin's `get_utf8_size` stepping (garbage bytes count — bug-compatible).
// UNSAFE-LEDGER: FLN-UL-0100
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_utf8_strlen")]
pub(crate) extern "C" fn export_lean_utf8_strlen(s: *const c_char) -> usize {
    // SAFETY: NUL-terminated string; the walk can step past the NUL exactly
    // as upstream's pointer walk does when a lead byte overstates its size —
    // the byte range up to (and semantically past) the NUL is readable per
    // the C string contract this symbol inherits from the pin.
    unsafe {
        let mut p = s.cast::<u8>();
        let mut r = 0usize;
        while p.read() != 0 {
            p = p.add(get_utf8_size(p.read()));
            r += 1;
        }
        r
    }
}

/// `lean_utf8_n_strlen` (`utf8.cpp:49-58`).
// UNSAFE-LEDGER: FLN-UL-0101
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_utf8_n_strlen")]
pub(crate) extern "C" fn export_lean_utf8_n_strlen(s: *const c_char, n: usize) -> usize {
    // SAFETY: n readable bytes per the contract.
    unsafe {
        let bytes = if n == 0 {
            &[][..]
        } else {
            core::slice::from_raw_parts(s.cast::<u8>(), n)
        };
        utf8_n_strlen_impl(bytes)
    }
}

/// `lean_string_eq_cold` (`object.cpp`): byte compare over `m_size` bytes
/// (the sizes are already known equal — the inline's fast path checked).
// UNSAFE-LEDGER: FLN-UL-0102
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_eq_cold")]
pub(crate) extern "C" fn export_lean_string_eq_cold(
    s1: *mut LeanObject,
    s2: *mut LeanObject,
) -> bool {
    // SAFETY: both live strings; m_size bytes are salient per the string law.
    unsafe {
        let (n1, d1) = string_size_and_data(s1);
        let (_, d2) = string_size_and_data(s2);
        core::slice::from_raw_parts(d1, n1) == core::slice::from_raw_parts(d2, n1)
    }
}

// ---- slice 2: array / byte-array / string-conversion families ----------------
// Demand-driven growth (stage0 demand audit): exact ports of the upstream
// bodies. Where upstream delegates to Lean-compiled helpers
// (`lean_list_to_array` / `lean_array_to_list_impl`), the twin walks the
// List cells natively — same observable result, proven by the gauntlet
// differential against libleanshared.

/// `lean_inc` shape for raw children.
///
/// # Safety
/// `o` valid object pointer or boxed scalar.
// UNSAFE-LEDGER: FLN-UL-0113
#[allow(unsafe_code)]
unsafe fn inc(o: *mut LeanObject) {
    if !is_scalar(o) {
        // SAFETY: live non-scalar object per caller contract.
        unsafe { rc::inc_ref_n(o, 1) };
    }
}

/// `lean_dec` shape for raw children.
///
/// # Safety
/// `o` valid object pointer or boxed scalar; one owned reference yielded.
// UNSAFE-LEDGER: FLN-UL-0114
#[allow(unsafe_code)]
unsafe fn dec(o: *mut LeanObject) {
    if !is_scalar(o) {
        // SAFETY: live non-scalar object; caller yields one reference.
        unsafe { rc::dec_ref(o) };
    }
}

/// `lean_is_exclusive` (`lean.h:612-618`): single-threaded and rc == 1.
///
/// # Safety
/// `o` live non-scalar object.
// UNSAFE-LEDGER: FLN-UL-0115
#[allow(unsafe_code)]
unsafe fn is_exclusive(o: *mut LeanObject) -> bool {
    // SAFETY: header read on a live object.
    let h = unsafe { rc::read_header(o) };
    h.rc == 1
}

/// Array object-slot base (`lean_array_cptr`, `lean.h:863`).
///
/// # Safety
/// `o` live array object.
// UNSAFE-LEDGER: FLN-UL-0116
#[allow(unsafe_code)]
unsafe fn array_data(o: *mut LeanObject) -> *mut *mut LeanObject {
    use crate::layout::LeanArrayObject;
    // SAFETY: repr(C) mirror; m_data follows the fixed fields.
    unsafe { (&raw mut (*o.cast::<LeanArrayObject>()).m_data).cast::<*mut LeanObject>() }
}

/// `lean_copy_expand_array` (`object.cpp:2674-2697`): copy with optional
/// `(cap+1)*2` growth; an exclusive source transfers element ownership and
/// its block is released without touching the children.
///
/// # Safety
/// `a` live array whose reference the caller yields.
// UNSAFE-LEDGER: FLN-UL-0117
#[allow(unsafe_code)]
unsafe fn copy_expand_array(a: *mut LeanObject, expand: bool) -> *mut LeanObject {
    // SAFETY: salient reads/writes within both arrays' allocations; the
    // exclusive arm releases only the source BLOCK (children transferred),
    // the shared arm retains each child before yielding the source ref.
    unsafe {
        let (sz, mut cap) = object::array_fields(a);
        if expand {
            cap = (cap + 1) * 2;
        }
        let r = object::alloc_array(sz, cap);
        let src = array_data(a);
        let dst = array_data(r);
        if is_exclusive(a) {
            core::ptr::copy_nonoverlapping(src, dst, sz);
            let bytes = rc::object_byte_size(a);
            membrane::release_with_size(a, bytes, "export.copy_expand_array");
        } else {
            for i in 0..sz {
                let child = src.add(i).read();
                dst.add(i).write(child);
                inc(child);
            }
            rc::dec_ref(a);
        }
        r
    }
}

/// `lean_copy_sarray` (`object.cpp:2514-2524`).
///
/// # Safety
/// `a` live scalar array whose reference the caller yields.
// UNSAFE-LEDGER: FLN-UL-0118
#[allow(unsafe_code)]
unsafe fn copy_sarray(a: *mut LeanObject, cap: usize) -> *mut LeanObject {
    // SAFETY: byte copy of the salient prefix; the new array's fields are
    // set by the constructor; the source reference is yielded via dec.
    unsafe {
        let (esz, sz, _, src) = object::sarray_fields(a);
        let r = object::alloc_sarray(esz, sz, cap);
        let (_, _, _, dst) = object::sarray_fields(r);
        core::ptr::copy_nonoverlapping(src, dst, usize::from(esz) * sz);
        rc::dec_ref(a);
        r
    }
}

/// `lean_sarray_ensure_capacity` + `lean_sarray_ensure_exclusive`
/// (`object.cpp:2526-2544`), composed in the push order.
///
/// # Safety
/// `a` live scalar array whose reference the caller yields.
// UNSAFE-LEDGER: FLN-UL-0119
#[allow(unsafe_code)]
unsafe fn sarray_ensure_pushable(a: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: delegated salient reads and copies.
    unsafe {
        let (_, sz, cap, _) = object::sarray_fields(a);
        let min_cap = sz + 1;
        let a = if min_cap <= cap {
            a
        } else {
            copy_sarray(a, min_cap * 2)
        };
        if is_exclusive(a) {
            a
        } else {
            let (_, _, cap, _) = object::sarray_fields(a);
            copy_sarray(a, cap)
        }
    }
}

/// `MurmurHash64A` (`hash.cpp:15-56`) — the pin's `hash_str` core, exact
/// wrapping arithmetic.
fn murmur64a(data: &[u8], seed: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let len = data.len();
    let mut h = seed ^ (len as u64).wrapping_mul(M);
    let (chunks, tail) = data.as_chunks::<8>();
    for chunk in chunks {
        let mut k = u64::from_le_bytes(*chunk);
        k = k.wrapping_mul(M);
        k ^= k >> R;
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
    }
    if !tail.is_empty() {
        for (i, byte) in tail.iter().enumerate() {
            h ^= u64::from(*byte) << (8 * i);
        }
        h = h.wrapping_mul(M);
    }
    h ^= h >> R;
    h = h.wrapping_mul(M);
    h ^= h >> R;
    h
}

/// `push_unicode_scalar` (`utf8.cpp:300-320`): UTF-8 encode, no validation
/// (Char scalars are valid by construction upstream and here).
fn push_unicode_scalar(out: &mut Vec<u8>, code: u32) {
    if code < 0x80 {
        out.push(code as u8);
    } else if code < 0x800 {
        out.push(((code >> 6) & 0x1F) as u8 | 0xC0);
        out.push((code & 0x3F) as u8 | 0x80);
    } else if code < 0x10000 {
        out.push(((code >> 12) & 0x0F) as u8 | 0xE0);
        out.push(((code >> 6) & 0x3F) as u8 | 0x80);
        out.push((code & 0x3F) as u8 | 0x80);
    } else {
        out.push(((code >> 18) & 0x07) as u8 | 0xF0);
        out.push(((code >> 12) & 0x3F) as u8 | 0x80);
        out.push(((code >> 6) & 0x3F) as u8 | 0x80);
        out.push((code & 0x3F) as u8 | 0x80);
    }
}

/// `next_utf8` (`utf8.cpp:167-208`) including the invalid-byte fallback
/// (advance one, return the raw byte — bug-compatible).
fn next_utf8(s: &[u8], i: &mut usize) -> u32 {
    let size = s.len();
    let c = u32::from(s[*i]);
    if c & 0x80 == 0 {
        *i += 1;
        return c;
    }
    if c & 0xE0 == 0xC0 && *i + 1 < size {
        let c1 = u32::from(s[*i + 1]);
        let r = ((c & 0x1F) << 6) | (c1 & 0x3F);
        if r >= 0x80 {
            *i += 2;
            return r;
        }
    }
    if c & 0xF0 == 0xE0 && *i + 2 < size {
        let c1 = u32::from(s[*i + 1]);
        let c2 = u32::from(s[*i + 2]);
        let r = ((c & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
        if r >= 0x800 && !(0xD800..=0xDFFF).contains(&r) {
            *i += 3;
            return r;
        }
    }
    if c & 0xF8 == 0xF0 && *i + 3 < size {
        let c1 = u32::from(s[*i + 1]);
        let c2 = u32::from(s[*i + 2]);
        let c3 = u32::from(s[*i + 3]);
        let r = ((c & 0x07) << 18) | ((c1 & 0x3F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
        if (0x10000..=0x10FFFF).contains(&r) {
            *i += 4;
            return r;
        }
    }
    *i += 1;
    c
}

/// `lean_array_push` (`object.cpp:2703-2715`): exclusivity fast path, the
/// exact growth policy otherwise.
// UNSAFE-LEDGER: FLN-UL-0120
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_array_push")]
pub(crate) extern "C" fn export_lean_array_push(
    a: *mut LeanObject,
    v: *mut LeanObject,
) -> *mut LeanObject {
    use crate::layout::LeanArrayObject;
    // SAFETY: live array; the chosen target always has cap > size by the
    // upstream law; the slot write is an initialization write.
    unsafe {
        let r = if is_exclusive(a) {
            let (sz, cap) = object::array_fields(a);
            if cap > sz {
                a
            } else {
                copy_expand_array(a, true)
            }
        } else {
            let (sz, cap) = object::array_fields(a);
            copy_expand_array(a, cap < 2 * sz + 1)
        };
        let (sz, _) = object::array_fields(r);
        array_data(r).add(sz).write(v);
        (&raw mut (*r.cast::<LeanArrayObject>()).m_size).write(sz + 1);
        r
    }
}

/// `lean_array_mk` (`object.cpp:490-492`): List → Array. Upstream calls the
/// Lean-compiled `lean_list_to_array`; the twin walks the cons cells
/// natively (nil = boxed 0, cons = ctor tag 1 of (head, tail)) with the
/// same ownership balance: the array takes one retained reference per
/// element, then the list is released.
// UNSAFE-LEDGER: FLN-UL-0121
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_array_mk")]
pub(crate) extern "C" fn export_lean_array_mk(lst: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: cons cells are live ctors; children are borrowed during the
    // walk and retained before the list yields its references.
    unsafe {
        let mut n = 0usize;
        let mut cur = lst;
        while !is_scalar(cur) {
            n += 1;
            cur = object::ctor_get(cur, 1);
        }
        let r = object::alloc_array(n, n);
        let dst = array_data(r);
        let mut cur = lst;
        let mut i = 0usize;
        while !is_scalar(cur) {
            let head = object::ctor_get(cur, 0);
            inc(head);
            dst.add(i).write(head);
            i += 1;
            cur = object::ctor_get(cur, 1);
        }
        dec(lst);
        r
    }
}

/// `lean_array_to_list` (`object.cpp:494-496`): Array → List, built from the
/// end exactly like `string_to_list_core` builds cons chains; each element
/// is retained before the array yields its references.
// UNSAFE-LEDGER: FLN-UL-0122
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_array_to_list")]
pub(crate) extern "C" fn export_lean_array_to_list(a: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: salient reads within the array; each fresh cons cell's slots
    // are fully initialized before the next iteration.
    unsafe {
        let (sz, _) = object::array_fields(a);
        let src = array_data(a);
        let mut r = crate::tagged::boxi(0);
        for i in (0..sz).rev() {
            let head = src.add(i).read();
            inc(head);
            let cell = object::alloc_ctor(1, 2, 0);
            object::ctor_set(cell, 0, head);
            object::ctor_set(cell, 1, r);
            r = cell;
        }
        dec(a);
        r
    }
}

/// `lean_array_get_panic` (`object.cpp:499-501`).
// UNSAFE-LEDGER: FLN-UL-0123
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_array_get_panic")]
pub(crate) extern "C" fn export_lean_array_get_panic(
    default_val: *mut LeanObject,
) -> *mut LeanObject {
    let msg = export_lean_mk_ascii_string_unchecked(c"Error: index out of bounds".as_ptr());
    export_lean_panic_fn(default_val, msg)
}

/// `lean_array_set_panic` (`object.cpp:503-506`).
// UNSAFE-LEDGER: FLN-UL-0124
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_array_set_panic")]
pub(crate) extern "C" fn export_lean_array_set_panic(
    a: *mut LeanObject,
    v: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: v's reference is yielded exactly as upstream's lean_dec.
    unsafe { dec(v) };
    let msg = export_lean_mk_ascii_string_unchecked(c"Error: index out of bounds".as_ptr());
    export_lean_panic_fn(a, msg)
}

/// `lean_byte_array_mk` (`object.cpp:2549-2560`): Array of boxed UInt8 →
/// ByteArray.
// UNSAFE-LEDGER: FLN-UL-0125
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_byte_array_mk")]
pub(crate) extern "C" fn export_lean_byte_array_mk(a: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: elements are boxed scalars (unbox is address arithmetic); the
    // array reference is yielded after the copy.
    unsafe {
        let (sz, _) = object::array_fields(a);
        let src = array_data(a);
        let r = object::alloc_sarray(1, sz, sz);
        let (_, _, _, dst) = object::sarray_fields(r);
        for i in 0..sz {
            dst.add(i)
                .write(crate::tagged::unbox(src.add(i).read()) as u8);
        }
        dec(a);
        r
    }
}

/// `lean_byte_array_data` (`object.cpp:2562-2573`): ByteArray → Array of
/// boxed UInt8.
// UNSAFE-LEDGER: FLN-UL-0126
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_byte_array_data")]
pub(crate) extern "C" fn export_lean_byte_array_data(a: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: salient byte reads; every array slot initialized with a boxed
    // scalar before the source yields its reference.
    unsafe {
        let (_, sz, _, src) = object::sarray_fields(a);
        let r = object::alloc_array(sz, sz);
        let dst = array_data(r);
        for i in 0..sz {
            dst.add(i)
                .write(crate::tagged::boxi(usize::from(src.add(i).read())));
        }
        dec(a);
        r
    }
}

/// `lean_byte_array_push` (`object.cpp:2575-2582`): ensure capacity (×2
/// growth), ensure exclusivity, append.
// UNSAFE-LEDGER: FLN-UL-0127
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_byte_array_push")]
pub(crate) extern "C" fn export_lean_byte_array_push(a: *mut LeanObject, b: u8) -> *mut LeanObject {
    use crate::layout::LeanSarrayObject;
    // SAFETY: the pushable target has cap > size by construction; the byte
    // write is an initialization write.
    unsafe {
        let r = sarray_ensure_pushable(a);
        let (_, sz, _, dst) = object::sarray_fields(r);
        dst.add(sz).write(b);
        (&raw mut (*r.cast::<LeanSarrayObject>()).m_size).write(sz + 1);
        r
    }
}

/// `lean_string_mk` (`object.cpp`): List Char → String (UTF-8 encode with
/// the pin's exact byte emitter).
// UNSAFE-LEDGER: FLN-UL-0128
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_mk")]
pub(crate) extern "C" fn export_lean_string_mk(cs: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: cons cells are live ctors with boxed-scalar Char heads.
    unsafe {
        let mut bytes = Vec::new();
        let mut len = 0usize;
        let mut cur = cs;
        while !is_scalar(cur) {
            let code = crate::tagged::unbox(object::ctor_get(cur, 0)) as u32;
            push_unicode_scalar(&mut bytes, code);
            cur = object::ctor_get(cur, 1);
            len += 1;
        }
        dec(cs);
        object::mk_string_unchecked(&bytes, len)
    }
}

/// `lean_string_data` (`object.cpp`): String → List Char, decoded with the
/// pin's `next_utf8` (including its invalid-byte fallback), consuming the
/// string via `lean_dec_ref` exactly as upstream.
// UNSAFE-LEDGER: FLN-UL-0129
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_data")]
pub(crate) extern "C" fn export_lean_string_data(s: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: salient string bytes copied before the reference is yielded;
    // fresh cons cells fully initialized.
    unsafe {
        let (size, data) = string_size_and_data(s);
        let content = core::slice::from_raw_parts(data, size.saturating_sub(1)).to_vec();
        rc::dec_ref(s);
        let mut codes = Vec::new();
        let mut i = 0usize;
        while i < content.len() {
            codes.push(next_utf8(&content, &mut i));
        }
        let mut r = crate::tagged::boxi(0);
        for code in codes.iter().rev() {
            let cell = object::alloc_ctor(1, 2, 0);
            object::ctor_set(cell, 0, crate::tagged::boxi(*code as usize));
            object::ctor_set(cell, 1, r);
            r = cell;
        }
        r
    }
}

/// `lean_string_hash` (`object.cpp:2450-2454`): MurmurHash64A over the
/// content bytes with seed 11.
// UNSAFE-LEDGER: FLN-UL-0130
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_hash")]
pub(crate) extern "C" fn export_lean_string_hash(s: *mut LeanObject) -> u64 {
    // SAFETY: salient string bytes, borrowed.
    unsafe {
        let (size, data) = string_size_and_data(s);
        let bytes = core::slice::from_raw_parts(data, size.saturating_sub(1));
        murmur64a(bytes, 11)
    }
}

// ---- slice 3: the bignum-backed Nat families ---------------------------------
// Exact ports of object.cpp:1347-1600 / 1805-1830 over the owned bignum
// (fln-bignum, D1 — Lean Nat semantics: truncated sub, x/0=0, x%0=x). The
// pin's conventions, kept literally: operands are BORROWED (`@& Nat`), the
// result is owned; `mpz_to_nat` arms normalize small results back to boxed
// scalars while `mpz_to_nat_core` arms stay mpz (the value cannot be small
// there — mpz objects hold only values > MAX_SMALL_NAT by invariant);
// truncations read low bits exactly as the pin's `mpz_fdiv_r_2exp` /
// lowest-limb accessors do for non-negative values.

use fln_bignum::nat::{BigNat, BigNatView};

/// Run `f` with a zero-copy view of a borrowed Nat operand.
///
/// Scalars use one stack limb for the callback invocation. Heap Nats borrow
/// the mpz object's immutable ABI limb buffer directly. Because the callback's
/// result type is independent of that borrow, the view cannot escape.
///
/// # Safety
/// `o` is a live boxed scalar or mpz Nat object.
// UNSAFE-LEDGER: FLN-UL-0134
#[allow(unsafe_code)]
unsafe fn with_nat_view<R>(o: *mut LeanObject, f: impl FnOnce(BigNatView<'_>) -> R) -> R {
    if is_scalar(o) {
        let word = [crate::tagged::unbox(o) as u64];
        let limbs = if word[0] == 0 { &[] } else { &word[..] };
        f(BigNatView::from_limbs_le(limbs))
    } else {
        // SAFETY: live mpz object; |m_size| limbs are salient (Nat: >= 0).
        let (alloc, size, pointer, live) = unsafe { object::mpz_fields(o) };
        assert!(size >= 0, "Nat mpz objects are non-negative");
        assert!(alloc >= 0, "mpz allocation count is negative");
        assert!(
            live <= alloc as usize,
            "mpz live limb count exceeds its allocation"
        );
        let limbs = if live == 0 {
            &[]
        } else {
            assert!(!pointer.is_null(), "nonempty mpz has a null limb buffer");
            // SAFETY: live <= allocation was checked above; the borrowed Nat
            // remains live for the duration of this non-escaping callback.
            unsafe { core::slice::from_raw_parts(pointer, live) }
        };
        f(BigNatView::from_limbs_le(limbs))
    }
}

/// `mpz_to_nat` (`object.cpp:1352-1357`): box when the value fits
/// `MAX_SMALL_NAT`, else a fresh mpz object.
///
/// # Safety
/// None beyond allocation; the constructor copies the limbs.
// UNSAFE-LEDGER: FLN-UL-0135
#[allow(unsafe_code)]
unsafe fn nat_obj_from_bignat(n: &BigNat) -> *mut LeanObject {
    match n.to_u64() {
        Some(v) if (v as usize) <= crate::tagged::MAX_SMALL_NAT => crate::tagged::boxi(v as usize),
        // SAFETY: fresh mpz object over an owned limb copy.
        _ => unsafe { object::alloc_mpz(n.limbs_le(), false) },
    }
}

/// `mpz_to_nat_core` (`object.cpp:1347-1350`): always an mpz object; the
/// caller's arm guarantees the value cannot be small.
///
/// # Safety
/// As [`nat_obj_from_bignat`].
// UNSAFE-LEDGER: FLN-UL-0136
#[allow(unsafe_code)]
unsafe fn nat_obj_from_bignat_core(n: &BigNat) -> *mut LeanObject {
    debug_assert!(
        n.to_u64()
            .is_none_or(|v| (v as usize) > crate::tagged::MAX_SMALL_NAT),
        "mpz_to_nat_core on a small value (upstream lean_assert)"
    );
    // SAFETY: fresh mpz object over an owned limb copy.
    unsafe { object::alloc_mpz(n.limbs_le(), false) }
}

/// Low-64 truncation of a borrowed mpz Nat (`mpz::mod64`/`get_size_t` on
/// non-negative values = the lowest limb; zero-limb objects cannot occur
/// for Nats but degrade to 0 exactly like `mpz_getlimbn`).
///
/// # Safety
/// `a` live mpz object.
// UNSAFE-LEDGER: FLN-UL-0137
#[allow(unsafe_code)]
unsafe fn big_nat_limb0(a: *mut LeanObject) -> u64 {
    // SAFETY: live mpz per the contract.
    unsafe { with_nat_view(a, |value| value.limbs_le().first().copied().unwrap_or(0)) }
}

/// `lean_nat_big_add` (`object.cpp:1383-1391`): every arm is `_core` — a
/// big plus anything non-negative stays big.
// UNSAFE-LEDGER: FLN-UL-0138
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_nat_big_add")]
pub(crate) extern "C" fn export_lean_nat_big_add(
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: borrowed live Nat operands.
    unsafe {
        let r = with_nat_view(a1, |n1| with_nat_view(a2, |n2| n1.add(n2)));
        nat_obj_from_bignat_core(&r)
    }
}

/// `lean_nat_big_sub` (`object.cpp:1393-1408`): scalar-minus-big is 0 by
/// the caller's guarantee; big arms normalize (the difference can shrink).
// UNSAFE-LEDGER: FLN-UL-0139
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_nat_big_sub")]
pub(crate) extern "C" fn export_lean_nat_big_sub(
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: borrowed live Nat operands.
    unsafe {
        if is_scalar(a1) {
            return crate::tagged::boxi(0);
        }
        let r = with_nat_view(a1, |n1| {
            with_nat_view(a2, |n2| {
                if !is_scalar(a2) && n1.ble(n2) && !n2.ble(n1) {
                    None
                } else {
                    Some(n1.sub(n2))
                }
            })
        });
        let Some(r) = r else {
            return crate::tagged::boxi(0);
        };
        nat_obj_from_bignat(&r)
    }
}

/// `lean_nat_big_mul` (`object.cpp:1409-1417`): scalar arms normalize (the
/// scalar can be 0), big·big stays `_core`.
// UNSAFE-LEDGER: FLN-UL-0140
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_nat_big_mul")]
pub(crate) extern "C" fn export_lean_nat_big_mul(
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: borrowed live Nat operands.
    unsafe {
        let r = with_nat_view(a1, |n1| with_nat_view(a2, |n2| n1.mul(n2)));
        if is_scalar(a1) || is_scalar(a2) {
            nat_obj_from_bignat(&r)
        } else {
            nat_obj_from_bignat_core(&r)
        }
    }
}

/// `lean_nat_overflow_mul` (`object.cpp:1419-1421`): the scalar·scalar
/// overflow path, normalized.
// UNSAFE-LEDGER: FLN-UL-0141
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_nat_overflow_mul")]
pub(crate) extern "C" fn export_lean_nat_overflow_mul(a1: usize, a2: usize) -> *mut LeanObject {
    let r = BigNat::from_u64(a1 as u64).mul(&BigNat::from_u64(a2 as u64));
    // SAFETY: fresh result object only.
    unsafe { nat_obj_from_bignat(&r) }
}

/// `lean_nat_big_div` (`object.cpp:1423-1434`): scalar/big is 0 (caller
/// law); n/0 returns the boxed-zero divisor exactly as upstream returns
/// `a2`; big arms normalize.
// UNSAFE-LEDGER: FLN-UL-0142
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_nat_big_div")]
pub(crate) extern "C" fn export_lean_nat_big_div(
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: borrowed live Nat operands.
    unsafe {
        if is_scalar(a1) {
            return crate::tagged::boxi(0);
        }
        if is_scalar(a2) && crate::tagged::unbox(a2) == 0 {
            return a2;
        }
        let r = with_nat_view(a1, |n1| with_nat_view(a2, |n2| n1.div(n2)));
        nat_obj_from_bignat(&r)
    }
}

/// `lean_nat_big_mod` (`object.cpp:1455-1472` shape): scalar%big is the
/// scalar itself (borrowed scalar returns as-is — no rc); n%0 returns `a1`
/// RETAINED exactly as upstream's `lean_inc(a1)`; big arms normalize.
// UNSAFE-LEDGER: FLN-UL-0143
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_nat_big_mod")]
pub(crate) extern "C" fn export_lean_nat_big_mod(
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: borrowed live Nat operands; the x%0 arm returns the retained
    // input exactly as upstream.
    unsafe {
        if is_scalar(a1) {
            return a1;
        }
        if is_scalar(a2) && crate::tagged::unbox(a2) == 0 {
            inc(a1);
            return a1;
        }
        let r = with_nat_view(a1, |n1| with_nat_view(a2, |n2| n1.rem(n2)));
        nat_obj_from_bignat(&r)
    }
}

/// `lean_nat_big_eq` (`object.cpp:1470-1481`): a scalar can never equal an
/// mpz object (representation invariant), the caller guarantees it.
// UNSAFE-LEDGER: FLN-UL-0144
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_nat_big_eq")]
pub(crate) extern "C" fn export_lean_nat_big_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
    // SAFETY: borrowed live Nat operands.
    unsafe {
        if is_scalar(a1) || is_scalar(a2) {
            return false;
        }
        with_nat_view(a1, |n1| with_nat_view(a2, |n2| n1.beq(n2)))
    }
}

/// `lean_nat_big_le` (`object.cpp:1483-1494`): scalar <= big always, big <=
/// scalar never (representation invariant).
// UNSAFE-LEDGER: FLN-UL-0145
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_nat_big_le")]
pub(crate) extern "C" fn export_lean_nat_big_le(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
    // SAFETY: borrowed live Nat operands.
    unsafe {
        if is_scalar(a1) {
            return true;
        }
        if is_scalar(a2) {
            return false;
        }
        with_nat_view(a1, |n1| with_nat_view(a2, |n2| n1.ble(n2)))
    }
}

/// `lean_nat_big_lt` (`object.cpp:1496-1507`): same invariant shape.
// UNSAFE-LEDGER: FLN-UL-0146
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_nat_big_lt")]
pub(crate) extern "C" fn export_lean_nat_big_lt(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
    // SAFETY: borrowed live Nat operands.
    unsafe {
        if is_scalar(a1) {
            return true;
        }
        if is_scalar(a2) {
            return false;
        }
        with_nat_view(a1, |n1| with_nat_view(a2, |n2| n1.ble(n2) && !n1.beq(n2)))
    }
}

/// `lean_nat_pow` (`object.cpp:1577-1586`): the exponent must be a scalar
/// `<= UINT_MAX` or the pin's INTERNAL PANIC fires; result normalized.
// UNSAFE-LEDGER: FLN-UL-0147
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_nat_pow")]
pub(crate) extern "C" fn export_lean_nat_pow(
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: borrowed live Nat operands.
    unsafe {
        if !is_scalar(a2) || crate::tagged::unbox(a2) > u32::MAX as usize {
            internal_panic_impl("Nat.pow exponent is too big");
        }
        let r = with_nat_view(a1, |n| n.pow(crate::tagged::unbox(a2) as u32));
        nat_obj_from_bignat(&r)
    }
}

/// `lean_cstr_to_nat` (`object.cpp:1359-1361`): decimal literal (generated
/// code emits digits only) → normalized Nat.
// UNSAFE-LEDGER: FLN-UL-0148
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_cstr_to_nat")]
pub(crate) extern "C" fn export_lean_cstr_to_nat(n: *const c_char) -> *mut LeanObject {
    // SAFETY: NUL-terminated digit string per the generated-code contract;
    // a malformed literal is an internal fault, terminated per policy —
    // never a fabricated Nat.
    unsafe {
        let text = core::ffi::CStr::from_ptr(n).to_string_lossy();
        let Some(v) = BigNat::from_decimal(&text) else {
            internal_panic_impl("lean_cstr_to_nat: malformed numeral");
        };
        nat_obj_from_bignat(&v)
    }
}

/// `lean_big_usize_to_nat` (`object.cpp:1363-1369`).
// UNSAFE-LEDGER: FLN-UL-0149
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_big_usize_to_nat")]
pub(crate) extern "C" fn export_lean_big_usize_to_nat(n: usize) -> *mut LeanObject {
    if n <= crate::tagged::MAX_SMALL_NAT {
        crate::tagged::boxi(n)
    } else {
        // SAFETY: fresh mpz over one limb.
        unsafe { nat_obj_from_bignat_core(&BigNat::from_u64(n as u64)) }
    }
}

/// `lean_big_uint64_to_nat` (`object.cpp:1371-1377`).
// UNSAFE-LEDGER: FLN-UL-0150
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_big_uint64_to_nat")]
pub(crate) extern "C" fn export_lean_big_uint64_to_nat(n: u64) -> *mut LeanObject {
    if (n as usize) <= crate::tagged::MAX_SMALL_NAT {
        crate::tagged::boxi(n as usize)
    } else {
        // SAFETY: fresh mpz over one limb.
        unsafe { nat_obj_from_bignat_core(&BigNat::from_u64(n)) }
    }
}

/// `lean_uint8_of_big_nat` (`object.cpp:1805-1807`; `mpz::mod8`).
// UNSAFE-LEDGER: FLN-UL-0151
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_uint8_of_big_nat")]
pub(crate) extern "C" fn export_lean_uint8_of_big_nat(a: *mut LeanObject) -> u8 {
    // SAFETY: borrowed live mpz.
    unsafe { big_nat_limb0(a) as u8 }
}

/// `lean_uint16_of_big_nat` (`object.cpp:1809-1811`; `mpz::mod16`).
// UNSAFE-LEDGER: FLN-UL-0152
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_uint16_of_big_nat")]
pub(crate) extern "C" fn export_lean_uint16_of_big_nat(a: *mut LeanObject) -> u16 {
    // SAFETY: borrowed live mpz.
    unsafe { big_nat_limb0(a) as u16 }
}

/// `lean_uint32_of_big_nat` (`object.cpp:1813-1815`; `mpz::mod32`).
// UNSAFE-LEDGER: FLN-UL-0153
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_uint32_of_big_nat")]
pub(crate) extern "C" fn export_lean_uint32_of_big_nat(a: *mut LeanObject) -> u32 {
    // SAFETY: borrowed live mpz.
    unsafe { big_nat_limb0(a) as u32 }
}

/// `lean_uint64_of_big_nat` (`object.cpp:1817-1819`; `mpz::mod64`).
// UNSAFE-LEDGER: FLN-UL-0154
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_uint64_of_big_nat")]
pub(crate) extern "C" fn export_lean_uint64_of_big_nat(a: *mut LeanObject) -> u64 {
    // SAFETY: borrowed live mpz.
    unsafe { big_nat_limb0(a) }
}

/// `lean_usize_of_big_nat` (`object.cpp:1825-1827`; `mpz::get_size_t` =
/// lowest limb).
// UNSAFE-LEDGER: FLN-UL-0155
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_usize_of_big_nat")]
pub(crate) extern "C" fn export_lean_usize_of_big_nat(a: *mut LeanObject) -> usize {
    // SAFETY: borrowed live mpz.
    unsafe { big_nat_limb0(a) as usize }
}

/// `lean_string_of_usize` (`object.cpp:2456-2458`).
// UNSAFE-LEDGER: FLN-UL-0156
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_of_usize")]
pub(crate) extern "C" fn export_lean_string_of_usize(n: usize) -> *mut LeanObject {
    let text = n.to_string();
    // SAFETY: ASCII digits; byte count = codepoint count.
    unsafe { object::mk_string_unchecked(text.as_bytes(), text.len()) }
}

/// `lean_nat_eq` inline shape (`lean.h:1499`), needed by the Name walk.
///
/// # Safety
/// Both live Nat operands, borrowed.
// UNSAFE-LEDGER: FLN-UL-0157
#[allow(unsafe_code)]
unsafe fn nat_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
    if is_scalar(a1) && is_scalar(a2) {
        return a1 == a2;
    }
    export_lean_nat_big_eq(a1, a2)
}

/// `lean_string_eq` inline shape (`lean.h:1262-1264`).
///
/// # Safety
/// Both live string objects, borrowed.
// UNSAFE-LEDGER: FLN-UL-0158
#[allow(unsafe_code)]
unsafe fn string_eq(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
    if s1 == s2 {
        return true;
    }
    // SAFETY: live strings; sizes read before the cold byte compare.
    unsafe {
        let (n1, _) = string_size_and_data(s1);
        let (n2, _) = string_size_and_data(s2);
        n1 == n2 && export_lean_string_eq_cold(s1, s2)
    }
}

/// `lean_name_eq` (`object.cpp:2720-2750`): pointer/hash fast paths, then
/// the prefix walk — the cached hash lives at scalar offset 16
/// (`lean_name_hash_ptr`, `lean.h:3003-3006`); `str` components (tag 1)
/// compare as strings, `num` components as Nats.
// UNSAFE-LEDGER: FLN-UL-0159
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_name_eq")]
pub(crate) extern "C" fn export_lean_name_eq(
    mut n1: *mut LeanObject,
    mut n2: *mut LeanObject,
) -> u8 {
    // SAFETY: borrowed live Name objects; the only scalar Name is anonymous,
    // so the hash reads below are reached with ctor objects only.
    unsafe {
        if n1 == n2 {
            return 1;
        }
        if is_scalar(n1) != is_scalar(n2)
            || object::ctor_get_scalar::<u64>(n1, 16) != object::ctor_get_scalar::<u64>(n2, 16)
        {
            return 0;
        }
        loop {
            let t1 = rc::read_header(n1).tag;
            if t1 != rc::read_header(n2).tag {
                return 0;
            }
            if t1 == 1 {
                if !string_eq(object::ctor_get(n1, 1), object::ctor_get(n2, 1)) {
                    return 0;
                }
            } else if !nat_eq(object::ctor_get(n1, 1), object::ctor_get(n2, 1)) {
                return 0;
            }
            n1 = object::ctor_get(n1, 0);
            n2 = object::ctor_get(n2, 0);
            if n1 == n2 {
                return 1;
            }
            if is_scalar(n1) != is_scalar(n2) {
                return 0;
            }
        }
    }
}

// ---- slice 4: closure application + once cells --------------------------------
// The apply membrane (`apply.cpp`, generated by gen/apply.lean): closure
// values ARE ABI values, so applying one is transmuting `m_fun` to the
// arity-shaped C function pointer and calling it — the single calling
// convention of §11.1. The exclusive/shared ownership split, the
// over-application curry+reapply, and the under-application fix_args are
// ported arm-for-arm. Only the demanded lean_apply_1..4 are exported; the
// generic core serves them all (over-application re-enters it exactly
// where upstream calls lean_apply_n).

/// The `fnn` shape (`apply.cpp:76`): arities > 16 pass an argument array.
type FnN = unsafe extern "C" fn(*mut *mut LeanObject) -> *mut LeanObject;

/// `curry` (`apply.cpp:77-98`): dispatch `m_fun` at the exact arity.
///
/// # Safety
/// `fun` is the closure's `m_fun` for a closure of arity `args.len()`
/// (foreign code vouches for the signature exactly as upstream's
/// reinterpret_cast does); every argument reference is owned by the callee.
// UNSAFE-LEDGER: FLN-UL-0162
#[allow(unsafe_code)]
unsafe fn closure_call(fun: *mut c_void, a: &[*mut LeanObject]) -> *mut LeanObject {
    type O = *mut LeanObject;
    use core::mem::transmute as t;
    // SAFETY: the transmute IS the ABI contract (apply.cpp FN1..FN16/FNN);
    // the callee owns every argument reference.
    unsafe {
        match a.len() {
            1 => t::<*mut c_void, unsafe extern "C" fn(O) -> O>(fun)(a[0]),
            2 => t::<*mut c_void, unsafe extern "C" fn(O, O) -> O>(fun)(a[0], a[1]),
            3 => t::<*mut c_void, unsafe extern "C" fn(O, O, O) -> O>(fun)(a[0], a[1], a[2]),
            4 => {
                t::<*mut c_void, unsafe extern "C" fn(O, O, O, O) -> O>(fun)(a[0], a[1], a[2], a[3])
            }
            5 => t::<*mut c_void, unsafe extern "C" fn(O, O, O, O, O) -> O>(fun)(
                a[0], a[1], a[2], a[3], a[4],
            ),
            6 => t::<*mut c_void, unsafe extern "C" fn(O, O, O, O, O, O) -> O>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5],
            ),
            7 => t::<*mut c_void, unsafe extern "C" fn(O, O, O, O, O, O, O) -> O>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6],
            ),
            8 => t::<*mut c_void, unsafe extern "C" fn(O, O, O, O, O, O, O, O) -> O>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7],
            ),
            9 => t::<*mut c_void, unsafe extern "C" fn(O, O, O, O, O, O, O, O, O) -> O>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8],
            ),
            10 => t::<*mut c_void, unsafe extern "C" fn(O, O, O, O, O, O, O, O, O, O) -> O>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9],
            ),
            11 => {
                t::<*mut c_void, unsafe extern "C" fn(O, O, O, O, O, O, O, O, O, O, O) -> O>(fun)(
                    a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10],
                )
            }
            12 => {
                t::<*mut c_void, unsafe extern "C" fn(O, O, O, O, O, O, O, O, O, O, O, O) -> O>(fun)(
                    a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11],
                )
            }
            13 => {
                t::<*mut c_void, unsafe extern "C" fn(O, O, O, O, O, O, O, O, O, O, O, O, O) -> O>(
                    fun,
                )(
                    a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12],
                )
            }
            14 => t::<
                *mut c_void,
                unsafe extern "C" fn(O, O, O, O, O, O, O, O, O, O, O, O, O, O) -> O,
            >(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12],
                a[13],
            ),
            15 => t::<
                *mut c_void,
                unsafe extern "C" fn(O, O, O, O, O, O, O, O, O, O, O, O, O, O, O) -> O,
            >(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12],
                a[13], a[14],
            ),
            16 => t::<
                *mut c_void,
                unsafe extern "C" fn(O, O, O, O, O, O, O, O, O, O, O, O, O, O, O, O) -> O,
            >(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12],
                a[13], a[14], a[15],
            ),
            0 => unreachable!("curry at arity 0 (apply.cpp lean_unreachable)"),
            _ => t::<*mut c_void, FnN>(fun)(a.as_ptr().cast_mut()),
        }
    }
}

/// `fix_args` (`apply.cpp:12-38`): under-application extends the closure —
/// exclusive sources transfer their fixed args and release only the block,
/// shared sources retain each and yield the closure reference.
///
/// # Safety
/// `f` live closure whose reference the caller yields; `an` references are
/// owned by the new closure.
// UNSAFE-LEDGER: FLN-UL-0163
#[allow(unsafe_code)]
unsafe fn fix_args(f: *mut LeanObject, an: &[*mut LeanObject]) -> *mut LeanObject {
    // SAFETY: salient closure reads; every new-closure slot initialized.
    unsafe {
        let (fun, arity, fixed, src) = object::closure_fields(f);
        let fixed = usize::from(fixed);
        let new_fixed = fixed + an.len();
        debug_assert!(
            new_fixed < usize::from(arity),
            "fix_args law (apply.cpp:16)"
        );
        let r = object::alloc_closure(fun, arity, new_fixed as u16);
        let (_, _, _, dst) = object::closure_fields(r);
        if !is_exclusive(f) {
            for i in 0..fixed {
                let c = src.add(i).read();
                inc(c);
                dst.add(i).write(c);
            }
            rc::dec_ref(f);
        } else {
            for i in 0..fixed {
                dst.add(i).write(src.add(i).read());
            }
            let bytes = rc::object_byte_size(f);
            membrane::release_with_size(f, bytes, "export.apply.fix_args");
        }
        for (i, a) in an.iter().enumerate() {
            dst.add(fixed + i).write(*a);
        }
        r
    }
}

/// The `lean_apply_N` core (`apply.cpp:101-460` arm structure): scalar f is
/// an erased proof (args dropped); exact application calls through the
/// membrane — an exclusive closure of arity ≤ 16 transfers its fixed args
/// and frees only its block, otherwise fixed args are retained and the
/// closure reference yielded; over-application curries `arity` args and
/// re-enters with the rest; under-application extends via [`fix_args`].
///
/// # Safety
/// `f` valid closure or scalar whose reference the caller yields; argument
/// references are yielded to the application.
// UNSAFE-LEDGER: FLN-UL-0164
#[allow(unsafe_code)]
pub(crate) unsafe fn apply_core(f: *mut LeanObject, an: &[*mut LeanObject]) -> *mut LeanObject {
    // SAFETY: mirrors the generated arms; every branch settles ownership
    // exactly as annotated inline.
    unsafe {
        if is_scalar(f) {
            for a in an {
                dec(*a);
            }
            return f;
        }
        let n = an.len();
        let (fun, arity16, fixed16, src) = object::closure_fields(f);
        let arity = usize::from(arity16);
        let fixed = usize::from(fixed16);
        if arity == fixed + n {
            let mut args: Vec<*mut LeanObject> = Vec::with_capacity(arity);
            if is_exclusive(f) && arity <= 16 {
                for i in 0..fixed {
                    args.push(src.add(i).read()); // ownership transfers
                }
                args.extend_from_slice(an);
                let r = closure_call(fun, &args);
                let bytes = rc::object_byte_size(f);
                membrane::release_with_size(f, bytes, "export.apply.free");
                r
            } else {
                for i in 0..fixed {
                    let c = src.add(i).read();
                    inc(c);
                    args.push(c);
                }
                args.extend_from_slice(an);
                let r = closure_call(fun, &args);
                rc::dec_ref(f);
                r
            }
        } else if arity < fixed + n {
            let take = arity - fixed;
            let mut args: Vec<*mut LeanObject> = Vec::with_capacity(arity);
            for i in 0..fixed {
                let c = src.add(i).read();
                inc(c);
                args.push(c);
            }
            args.extend_from_slice(&an[..take]);
            let new_f = closure_call(fun, &args);
            rc::dec_ref(f);
            apply_core(new_f, &an[take..])
        } else {
            fix_args(f, an)
        }
    }
}

/// The exact 4-line violation block `notify_assertion_violation` prints
/// (`debug.cpp:48-55`), factored pure so the byte layout is testable without
/// crossing the crash path.
pub(crate) fn format_assert_violation(file: &str, line: i32, condition: &str) -> String {
    format!("LEAN ASSERTION VIOLATION\nFile: {file}\nLine: {line}\n{condition}\n")
}

/// `lean_notify_assert` (`debug.cpp:144-147`; declared at `lean.h:66` WITHOUT
/// the `LEAN_EXPORT` token — the census-hole symbol the G0-3 plugin demand
/// list surfaced). Prints upstream's exact violation block to stderr, then
/// ABORTS. Documented divergence, crash-path only: upstream follows the print
/// with `invoke_debugger()`, which by default throws a C++ exception
/// reachable only by a C++ host; a Rust wrapper cannot throw one, and an
/// assert violation is an invariant failure either way (FL-INV-07: never a
/// user diagnostic, never a silent continue).
// UNSAFE-LEDGER: FLN-UL-0186
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_notify_assert")]
pub(crate) extern "C" fn export_lean_notify_assert(
    file_name: *const core::ffi::c_char,
    line: core::ffi::c_int,
    condition: *const core::ffi::c_char,
) -> ! {
    // SAFETY: census-signatured entry; callers hand NUL-terminated C strings
    // per the assert macro's expansion (`lean.h:67`). A null pointer is
    // rendered as a placeholder rather than dereferenced.
    let render = |p: *const core::ffi::c_char| -> String {
        if p.is_null() {
            "<null>".to_string()
        } else {
            // SAFETY: non-null per the branch; NUL-terminated per the assert
            // macro's expansion (`lean.h:67` hands string literals).
            unsafe { core::ffi::CStr::from_ptr(p) }
                .to_string_lossy()
                .into_owned()
        }
    };
    eprint!(
        "{}",
        format_assert_violation(&render(file_name), line, &render(condition))
    );
    std::process::abort()
}

/// `lean_string_append` (`object.cpp:2084-2105`): `s1` owned, `s2` borrowed
/// (`lean.h:1225`); arms ported in [`object::string_append_core`], with the
/// exclusivity verdict taken here exactly as upstream takes it.
// UNSAFE-LEDGER: FLN-UL-0184
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_append")]
pub(crate) extern "C" fn export_lean_string_append(
    s1: *mut LeanObject,
    s2: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: census-signatured entry — callers hand live string objects under
    // the lean.h ownership convention; the exclusivity read and the core's
    // arms settle s1 in every path, s2 is never consumed.
    unsafe {
        let exclusive = is_exclusive(s1);
        object::string_append_core(s1, s2, exclusive)
    }
}

/// `lean_apply_1` (`apply.cpp:101-158`).
// UNSAFE-LEDGER: FLN-UL-0165
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_apply_1")]
pub(crate) extern "C" fn export_lean_apply_1(
    f: *mut LeanObject,
    a1: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: the exported apply contract; references yielded.
    unsafe { apply_core(f, &[a1]) }
}

/// `lean_apply_2` (`apply.cpp:160-...`).
// UNSAFE-LEDGER: FLN-UL-0166
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_apply_2")]
pub(crate) extern "C" fn export_lean_apply_2(
    f: *mut LeanObject,
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: as lean_apply_1.
    unsafe { apply_core(f, &[a1, a2]) }
}

/// `lean_apply_3`.
// UNSAFE-LEDGER: FLN-UL-0167
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_apply_3")]
pub(crate) extern "C" fn export_lean_apply_3(
    f: *mut LeanObject,
    a1: *mut LeanObject,
    a2: *mut LeanObject,
    a3: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: as lean_apply_1.
    unsafe { apply_core(f, &[a1, a2, a3]) }
}

/// `lean_apply_4`.
// UNSAFE-LEDGER: FLN-UL-0168
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_apply_4")]
pub(crate) extern "C" fn export_lean_apply_4(
    f: *mut LeanObject,
    a1: *mut LeanObject,
    a2: *mut LeanObject,
    a3: *mut LeanObject,
    a4: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: as lean_apply_1.
    unsafe { apply_core(f, &[a1, a2, a3, a4]) }
}

// The once cells (`lean.h:3268-3300`, `object.cpp:2827-2900`): generated C
// owns the static storage — `{_Atomic int state; _Atomic int lock}` — and
// the cold path runs the initializer exactly once under the simple atomic
// lock. The C++20 wait/notify pair is a blocking optimization; the twin
// spins with a scheduler yield, which is observably the same lock.

use core::sync::atomic::AtomicI32;

/// `lock_simple_atomic`/`unlock` (`object.cpp:2827-2840`), SeqCst like the
/// C++ defaults.
///
/// # Safety
/// `tok` points at a live `lean_once_cell_t` (C static storage).
// UNSAFE-LEDGER: FLN-UL-0169
#[allow(unsafe_code)]
unsafe fn once_cell_run<T>(
    tok: *mut c_void,
    loc: *mut T,
    init: unsafe extern "C" fn() -> T,
    persist: bool,
) -> T
where
    T: Copy,
{
    // SAFETY: the cell is two i32 atomics per the C layout; loc is the
    // C-side storage slot the initializer fills exactly once.
    unsafe {
        let state = AtomicI32::from_ptr(tok.cast::<i32>());
        let lock = AtomicI32::from_ptr(tok.cast::<i32>().add(1));
        loop {
            while lock.load(Ordering::SeqCst) == 1 {
                std::thread::yield_now();
            }
            if lock
                .compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
            {
                break;
            }
        }
        if state.load(Ordering::SeqCst) != 1 {
            let v = init();
            loc.write(v);
            if persist {
                // lean_obj_once_cold additionally persists the object graph.
                rc::mark_persistent(loc.cast::<*mut LeanObject>().read());
            }
            state.store(1, Ordering::SeqCst);
        }
        let out = loc.read();
        lock.store(0, Ordering::SeqCst);
        out
    }
}

/// `lean_obj_once_cold` (`object.cpp:2842-2851`).
// UNSAFE-LEDGER: FLN-UL-0170
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_obj_once_cold")]
pub(crate) extern "C" fn export_lean_obj_once_cold(
    loc: *mut *mut LeanObject,
    tok: *mut c_void,
    init: unsafe extern "C" fn() -> *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: C-owned cell + slot per the once contract.
    unsafe { once_cell_run(tok, loc, init, true) }
}

/// `lean_uint8_once_cold` (`object.cpp:2853-2861`).
// UNSAFE-LEDGER: FLN-UL-0171
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_uint8_once_cold")]
pub(crate) extern "C" fn export_lean_uint8_once_cold(
    loc: *mut u8,
    tok: *mut c_void,
    init: unsafe extern "C" fn() -> u8,
) -> u8 {
    // SAFETY: as lean_obj_once_cold, scalar slot.
    unsafe { once_cell_run(tok, loc, init, false) }
}

/// `lean_uint16_once_cold`.
// UNSAFE-LEDGER: FLN-UL-0172
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_uint16_once_cold")]
pub(crate) extern "C" fn export_lean_uint16_once_cold(
    loc: *mut u16,
    tok: *mut c_void,
    init: unsafe extern "C" fn() -> u16,
) -> u16 {
    // SAFETY: as lean_uint8_once_cold.
    unsafe { once_cell_run(tok, loc, init, false) }
}

/// `lean_uint32_once_cold`.
// UNSAFE-LEDGER: FLN-UL-0173
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_uint32_once_cold")]
pub(crate) extern "C" fn export_lean_uint32_once_cold(
    loc: *mut u32,
    tok: *mut c_void,
    init: unsafe extern "C" fn() -> u32,
) -> u32 {
    // SAFETY: as lean_uint8_once_cold.
    unsafe { once_cell_run(tok, loc, init, false) }
}

/// `lean_uint64_once_cold`.
// UNSAFE-LEDGER: FLN-UL-0174
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_uint64_once_cold")]
pub(crate) extern "C" fn export_lean_uint64_once_cold(
    loc: *mut u64,
    tok: *mut c_void,
    init: unsafe extern "C" fn() -> u64,
) -> u64 {
    // SAFETY: as lean_uint8_once_cold.
    unsafe { once_cell_run(tok, loc, init, false) }
}

/// `lean_float32_once_cold` (`object.cpp:2903-2911`): the scalar once cell
/// at `f32` — the generated code's cached `Float32` constants
/// (fln-3gv slice 8e).
// UNSAFE-LEDGER: FLN-UL-0425
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_float32_once_cold")]
pub(crate) extern "C" fn export_lean_float32_once_cold(
    loc: *mut f32,
    tok: *mut c_void,
    init: unsafe extern "C" fn() -> f32,
) -> f32 {
    // SAFETY: as lean_uint8_once_cold, float slot.
    unsafe { once_cell_run(tok, loc, init, false) }
}

/// `lean_float_once_cold` (`object.cpp:2913-2921`): the `f64` twin.
// UNSAFE-LEDGER: FLN-UL-0426
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_float_once_cold")]
pub(crate) extern "C" fn export_lean_float_once_cold(
    loc: *mut f64,
    tok: *mut c_void,
    init: unsafe extern "C" fn() -> f64,
) -> f64 {
    // SAFETY: as lean_uint8_once_cold, float slot.
    unsafe { once_cell_run(tok, loc, init, false) }
}

/// `lean_usize_once_cold`.
// UNSAFE-LEDGER: FLN-UL-0175
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_usize_once_cold")]
pub(crate) extern "C" fn export_lean_usize_once_cold(
    loc: *mut usize,
    tok: *mut c_void,
    init: unsafe extern "C" fn() -> usize,
) -> usize {
    // SAFETY: as lean_uint8_once_cold.
    unsafe { once_cell_run(tok, loc, init, false) }
}

// ---- extern-census symbols (declared by generated C itself, not lean.h) ------
// The stage0 demand audit surfaced these: generated C emits its own extern
// declarations for @[extern] runtime symbols (contracts/extern_census.tsv
// universe). Status rows use the `extern` kind.

/// `lean_sorry` (`object.cpp:208-211`; extern census `sorryAx`): executing a
/// sorry is an internal panic.
// UNSAFE-LEDGER: FLN-UL-0108
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_sorry")]
pub(crate) extern "C" fn export_lean_sorry(_synthetic: u8) -> *mut LeanObject {
    internal_panic_impl("executed 'sorry'")
}

/// `lean_system_platform_nbits` (`platform.cpp:12-18`; extern census
/// `System.Platform.getNumBits`): boxed 64 on the certified targets (the
/// crate refuses to compile elsewhere). The argument is the opaque unit
/// thunk token — a scalar, never dec'd, exactly as upstream ignores it.
// UNSAFE-LEDGER: FLN-UL-0109
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_system_platform_nbits")]
pub(crate) extern "C" fn export_lean_system_platform_nbits(
    _unit: *mut LeanObject,
) -> *mut LeanObject {
    crate::tagged::boxi(64)
}

/// `lean_string_from_utf8_unchecked` (`object.cpp`; extern census
/// `String.ofByteArray`): consume a byte array, produce a string with the
/// bug-compatible codepoint count.
// UNSAFE-LEDGER: FLN-UL-0110
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_from_utf8_unchecked")]
pub(crate) extern "C" fn export_lean_string_from_utf8_unchecked(
    a: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: a is a live byte array whose m_size bytes are salient; the
    // consumed reference is released through the internal rc twin.
    unsafe {
        let (_, size, _, data) = object::sarray_fields(a);
        let bytes = if size == 0 {
            &[][..]
        } else {
            core::slice::from_raw_parts(data.cast_const(), size)
        };
        let r = object::mk_string_unchecked(bytes, utf8_n_strlen_impl(bytes));
        rc::dec_ref(a);
        r
    }
}

/// `lean_string_to_utf8` (`object.cpp`; extern census `String.toByteArray` /
/// `String.toUTF8`): borrowed string to a fresh byte array of its `m_size-1`
/// content bytes.
// UNSAFE-LEDGER: FLN-UL-0111
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_to_utf8")]
pub(crate) extern "C" fn export_lean_string_to_utf8(s: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: s is a live (borrowed) string; the new sarray's data bytes are
    // fully initialized by the copy before return.
    unsafe {
        let (size, data) = string_size_and_data(s);
        let sz = size.saturating_sub(1);
        let r = object::alloc_sarray(1, sz, sz);
        let (_, _, _, dst) = object::sarray_fields(r);
        core::ptr::copy_nonoverlapping(data, dst, sz);
        r
    }
}

// ===================================================================
// fln-3gv slice 1: the ST ref-cell plane + platform/error-string leaves.
//
// The effect plane's pure substrate — no threads, no event loop. The ST ref
// family is `IO.Ref`'s carrier: the pin serves every access through a
// single-threaded plain path unless the cell is multi-threaded or persistent
// (`ref_maybe_mt`, io.cpp:1445), in which case the value slot is an atomic
// with exchange discipline and stored values are marked multi-threaded.
// Deviation disclosed in mechanism, not observables: the ST branches below go
// through the same `AtomicPtr` slot with `Relaxed` ordering instead of plain
// loads/stores — indistinguishable single-threaded, and it keeps one access
// path per slot (`AtomicPtr<T>` is layout-identical to `*mut T`, the same
// fact the thunk/task layouts already rely on).
// ===================================================================

/// `ref_maybe_mt` (`io.cpp:1445`): the cell is multi-threaded (`m_rc < 0`) or
/// persistent (`m_rc == 0`); mirrors `lean_is_mt` / `lean_is_persistent`'s
/// own plain header reads (`lean.h`).
// UNSAFE-LEDGER: FLN-UL-0203
#[allow(unsafe_code)]
unsafe fn ref_maybe_mt(r: *mut LeanObject) -> bool {
    // SAFETY: r is a live object per every caller's contract; the rc word is
    // read plainly exactly as the pin's own inline predicates read it.
    unsafe { (&raw const (*r).m_rc).read() <= 0 }
}

/// The ref value slot viewed atomically (`mt_ref_val_addr`, io.cpp:1430-1432).
// UNSAFE-LEDGER: FLN-UL-0204
#[allow(unsafe_code)]
unsafe fn ref_val_slot<'a>(r: *mut LeanObject) -> &'a core::sync::atomic::AtomicPtr<LeanObject> {
    // SAFETY: r is a live ref object; `AtomicPtr<LeanObject>` is
    // layout-identical to the `*mut LeanObject` slot it overlays.
    unsafe {
        &*(&raw mut (*r.cast::<crate::layout::LeanRefObject>()).m_value)
            .cast::<core::sync::atomic::AtomicPtr<LeanObject>>()
    }
}

/// `lean_st_mk_ref` (`io.cpp:1423-1428`): a fresh single-threaded ref cell
/// owning `a`.
// UNSAFE-LEDGER: FLN-UL-0205
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_st_mk_ref")]
pub(crate) extern "C" fn export_lean_st_mk_ref(a: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: `a` is consumed into the cell; alloc_ref owns header init.
    unsafe { object::alloc_ref(a) }
}

/// `lean_st_ref_get` (`io.cpp:1447-1472`): borrowed cell, owned value out.
/// The MT arm takes the RC token by exchange, duplicates it, and puts one
/// token back, decrementing any value another thread wrote in the window.
// UNSAFE-LEDGER: FLN-UL-0206
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_st_ref_get")]
pub(crate) extern "C" fn export_lean_st_ref_get(r: *mut LeanObject) -> *mut LeanObject {
    use core::sync::atomic::Ordering;
    // SAFETY: r is a live ref (borrowed); values leaving the slot follow the
    // pin's exchange discipline exactly, so ownership is balanced on every
    // path including the racing-writer arm.
    unsafe {
        let slot = ref_val_slot(r);
        if ref_maybe_mt(r) {
            loop {
                let val = slot.swap(core::ptr::null_mut(), Ordering::SeqCst);
                if !val.is_null() {
                    if !crate::tagged::is_scalar(val) {
                        rc::inc_ref_n(val, 1);
                    }
                    let tmp = slot.swap(val, Ordering::SeqCst);
                    if !tmp.is_null() && !crate::tagged::is_scalar(tmp) {
                        rc::dec_ref(tmp);
                    }
                    return val;
                }
            }
        } else {
            let val = slot.load(Ordering::Relaxed);
            if !crate::tagged::is_scalar(val) {
                rc::inc_ref_n(val, 1);
            }
            val
        }
    }
}

/// `lean_st_ref_take` (`io.cpp:1474-1488`): borrowed cell, the value moves
/// out and the slot is left null until the paired `set`.
// UNSAFE-LEDGER: FLN-UL-0207
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_st_ref_take")]
pub(crate) extern "C" fn export_lean_st_ref_take(r: *mut LeanObject) -> *mut LeanObject {
    use core::sync::atomic::Ordering;
    // SAFETY: r live ref; ownership of the slot's token transfers to the
    // caller on both arms.
    unsafe {
        let slot = ref_val_slot(r);
        if ref_maybe_mt(r) {
            loop {
                let val = slot.swap(core::ptr::null_mut(), Ordering::SeqCst);
                if !val.is_null() {
                    return val;
                }
            }
        } else {
            let val = slot.load(Ordering::Relaxed);
            slot.store(core::ptr::null_mut(), Ordering::Relaxed);
            val
        }
    }
}

/// `lean_st_ref_set` (`io.cpp:1492-1510`): consumes `a`; the MT arm marks the
/// stored value multi-threaded first (an ST graph must never be reachable
/// from an MT object); returns the unit `box(0)`.
// UNSAFE-LEDGER: FLN-UL-0208
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_st_ref_set")]
pub(crate) extern "C" fn export_lean_st_ref_set(
    r: *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    use core::sync::atomic::Ordering;
    // SAFETY: r live ref (borrowed), a consumed; the displaced value's token
    // is released on both arms exactly as the pin does.
    unsafe {
        let slot = ref_val_slot(r);
        if ref_maybe_mt(r) {
            if !crate::tagged::is_scalar(a) {
                rc::mark_mt(a);
            }
            let old = slot.swap(a, Ordering::SeqCst);
            if !old.is_null() && !crate::tagged::is_scalar(old) {
                rc::dec_ref(old);
            }
        } else {
            let old = slot.load(Ordering::Relaxed);
            if !old.is_null() && !crate::tagged::is_scalar(old) {
                rc::dec_ref(old);
            }
            slot.store(a, Ordering::Relaxed);
        }
    }
    crate::tagged::boxi(0)
}

/// `lean_st_ref_swap` (`io.cpp:1512-1527`): consumes `a`, returns the old
/// value; a null ST slot is the pin's `lean_internal_panic("null reference
/// read")`, reproduced verbatim.
// UNSAFE-LEDGER: FLN-UL-0209
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_st_ref_swap")]
pub(crate) extern "C" fn export_lean_st_ref_swap(
    r: *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    use core::sync::atomic::Ordering;
    // SAFETY: r live ref (borrowed), a consumed, old token returned owned.
    unsafe {
        let slot = ref_val_slot(r);
        if ref_maybe_mt(r) {
            if !crate::tagged::is_scalar(a) {
                rc::mark_mt(a);
            }
            loop {
                let old = slot.swap(a, Ordering::SeqCst);
                if !old.is_null() {
                    return old;
                }
            }
        } else {
            let old = slot.load(Ordering::Relaxed);
            if old.is_null() {
                internal_panic_impl("null reference read");
            }
            slot.store(a, Ordering::Relaxed);
            old
        }
    }
}

/// `lean_st_ref_ptr_eq` (`io.cpp:1530-1532`): cell identity, not value
/// equality.
// UNSAFE-LEDGER: FLN-UL-0212
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_st_ref_ptr_eq")]
pub(crate) extern "C" fn export_lean_st_ref_ptr_eq(r1: *mut LeanObject, r2: *mut LeanObject) -> u8 {
    u8::from(core::ptr::eq(r1, r2))
}

/// `lean_string_utf8_get` (`object.cpp:2219-2245` + `_fast_cold`): decode the
/// scalar at byte position `i`; every out-of-range, non-scalar-index or
/// invalid-encoding case is the pin's `lean_char_default_value()` = `'A'`.
// UNSAFE-LEDGER: FLN-UL-0210
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_utf8_get")]
pub(crate) extern "C" fn export_lean_string_utf8_get(
    s: *mut LeanObject,
    i0: *mut LeanObject,
) -> u32 {
    const DEFAULT: u32 = 'A' as u32;
    if !crate::tagged::is_scalar(i0) {
        return DEFAULT;
    }
    let i = crate::tagged::unbox(i0);
    // SAFETY: s is a live (borrowed) string; reads below stay inside the
    // m_size-bounded content prefix.
    unsafe {
        let (size, data) = string_size_and_data(s);
        let size = size.saturating_sub(1);
        if i >= size {
            return DEFAULT;
        }
        let bytes = core::slice::from_raw_parts(data, size);
        let c = u32::from(bytes[i]);
        if c < 0x80 {
            return c;
        }
        if (c & 0xe0) == 0xc0 && i + 1 < size {
            let c1 = u32::from(bytes[i + 1]);
            let r = ((c & 0x1f) << 6) | (c1 & 0x3f);
            if r >= 0x80 {
                return r;
            }
        }
        if (c & 0xf0) == 0xe0 && i + 2 < size {
            let c1 = u32::from(bytes[i + 1]);
            let c2 = u32::from(bytes[i + 2]);
            let r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
            if r >= 0x800 && !(0xD800..=0xDFFF).contains(&r) {
                return r;
            }
        }
        if (c & 0xf8) == 0xf0 && i + 3 < size {
            let c1 = u32::from(bytes[i + 1]);
            let c2 = u32::from(bytes[i + 2]);
            let c3 = u32::from(bytes[i + 3]);
            let r = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
            if (0x10000..=0x10FFFF).contains(&r) {
                return r;
            }
        }
        DEFAULT
    }
}

/// `lean_string_utf8_set` (`object.cpp:2423-2448`): out-of-range or
/// non-scalar index returns `s` unchanged; exclusive ASCII-over-ASCII writes
/// in place; a non-first-byte position returns `s`; otherwise rebuild with
/// the replacement scalar, codepoint length unchanged.
// UNSAFE-LEDGER: FLN-UL-0211
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_utf8_set")]
pub(crate) extern "C" fn export_lean_string_utf8_set(
    s: *mut LeanObject,
    i0: *mut LeanObject,
    c: u32,
) -> *mut LeanObject {
    if !crate::tagged::is_scalar(i0) {
        return s;
    }
    let i = crate::tagged::unbox(i0);
    // SAFETY: s owned by this call; all reads/writes stay inside its content
    // bytes; the rebuild path releases s exactly once.
    unsafe {
        let (size, data) = string_size_and_data(s);
        let sz = size.saturating_sub(1);
        if i >= sz {
            return s;
        }
        let first = *data.add(i);
        if is_exclusive(s) && first < 128 && c < 128 {
            let w = data as *mut u8;
            w.add(i).write(c as u8);
            return s;
        }
        if (first & 0xC0) == 0x80 {
            return s;
        }
        let bytes = core::slice::from_raw_parts(data, sz);
        let old_char_size = match bytes[i] {
            b if b < 0x80 => 1,
            b if (b & 0xe0) == 0xc0 => 2,
            b if (b & 0xf0) == 0xe0 => 3,
            b if (b & 0xf8) == 0xf0 => 4,
            _ => 1,
        };
        let mut rebuilt = Vec::with_capacity(sz + 4);
        rebuilt.extend_from_slice(&bytes[..i]);
        push_unicode_scalar(&mut rebuilt, c);
        rebuilt.extend_from_slice(&bytes[(i + old_char_size).min(sz)..]);
        let (_, _, len, _) = object::string_fields(s);
        rc::dec_ref(s);
        object::mk_string_unchecked(&rebuilt, len)
    }
}

/// `lean_system_platform_windows` (`platform.cpp:20-26`).
// UNSAFE-LEDGER: FLN-UL-0213
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_system_platform_windows")]
pub(crate) extern "C" fn export_lean_system_platform_windows(_w: *mut LeanObject) -> u8 {
    u8::from(cfg!(target_os = "windows"))
}

/// `lean_system_platform_osx` (`platform.cpp:28-34`).
// UNSAFE-LEDGER: FLN-UL-0214
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_system_platform_osx")]
pub(crate) extern "C" fn export_lean_system_platform_osx(_w: *mut LeanObject) -> u8 {
    u8::from(cfg!(target_os = "macos"))
}

/// `lean_system_platform_emscripten` (`platform.cpp:36-42`).
// UNSAFE-LEDGER: FLN-UL-0215
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_system_platform_emscripten")]
pub(crate) extern "C" fn export_lean_system_platform_emscripten(_w: *mut LeanObject) -> u8 {
    u8::from(cfg!(target_os = "emscripten"))
}

// ===================================================================
// fln-3gv slice 2: the promise/task-state family — the pin's managerless
// envelope, ported arm-for-arm.
//
// The pin DEFINES `g_task_manager == NULL` behavior rather than leaving it
// undefined: spawn/map/bind take an explicit eager arm (object.cpp:
// 1153/1176/1237), `task_pure`/`task_get` are pure data over Finished
// tasks, `io_get_task_state_core` answers 2 before consulting the manager
// (object.cpp:1260-1265), `option_get_or_block` is Option-unwrap with the
// pin's own panic (io.cpp:1627-1639), and `io_promise_new` REFUSES with a
// named internal panic (object.cpp:1272-1278) — the mode every compiled
// Lean binary runs its `initialize` blocks in (EmitC.lean:1112-1128).
// Marrow serves exactly that envelope — and, as of slice 3, the manager
// arms beside it (`task_manager.rs`): each function below branches on the
// live manager exactly where the pin branches on `g_task_manager`.
// Deviation disclosed: where the pin's managerless arm is a null-deref on
// `g_task_manager` (`task_get` on an unfinished task, `get_task_state`
// with `m_imp != NULL`, promise resolve / result_opt), Marrow refuses
// typed per the §6.5 panic law instead of reproducing UB — unreachable
// through conforming managerless code, since no unfinished task and no
// promise is constructible without the manager.
// ===================================================================

/// Typed refusal for the arms the pin serves through `g_task_manager` —
/// and null-derefs when it is absent (`object.cpp:1191/1265/1294`).
/// Managerless Marrow constructs no unfinished task and no promise, so
/// these arms are unreachable through conforming code; refusing typed is
/// the §6.5 panic law, never a fabricated result.
fn task_manager_refusal(what: &str) -> ! {
    let text = format!(
        "task plane: {what} requires the task manager, which is not running \
         (managerless membrane, bead fln-3gv; the manager plane is the next slice)"
    );
    internal_panic_impl(&text)
}

/// `lean_task_pure` (`object.cpp:1162-1164`): a Finished task owning `a`,
/// born single-threaded (`alloc_task(obj_arg v)` uses `lean_set_st_header`,
/// object.cpp:1136-1142) — and the pin deliberately does NOT mark the value
/// multi-threaded on this path.
// UNSAFE-LEDGER: FLN-UL-0218
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_task_pure")]
pub(crate) extern "C" fn export_lean_task_pure(a: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: `a` is consumed into the task; alloc_task_pure owns header init.
    unsafe { object::alloc_task_pure(a) }
}

/// `lean_task_get` (`object.cpp:1187-1203`): borrowed task in, BORROWED
/// value out (`b_lean_obj_res`, census). The unfinished arm blocks through
/// the manager's `wait_for` (slice 3); without a manager — where the pin
/// null-derefs — it refuses typed (see the banner).
// UNSAFE-LEDGER: FLN-UL-0219
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_task_get")]
pub(crate) extern "C" fn export_lean_task_get(t: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: t is a live (borrowed) task; the Acquire value load mirrors
    // the pin's `_Atomic` read, and the returned reference stays borrowed.
    unsafe {
        let (v, _) = object::task_fields(t);
        if !v.is_null() {
            return v;
        }
        if let Some(mgr) = crate::task_manager::manager() {
            mgr.wait_for(crate::task_manager::TaskPtr(t.cast()));
            let (v, _) = object::task_fields(t);
            debug_assert!(!v.is_null());
            return v;
        }
        task_manager_refusal("`Task.get` on an unfinished task");
    }
}

/// `lean_task_map_core` (`object.cpp:1166-1185`): eager when there is no
/// manager OR when `sync` finds the input already finished — the pin's
/// exact condition — with `prio`/`keep_alive` silently ignored on that arm;
/// otherwise a Waiting task carrying `task_map_fn` joins the dependency
/// graph via `add_dep`. `lean_task_get_own` is the lean.h inline
/// (get, then inc, then dec; lean.h:1328-1334), expanded here with the
/// pin's scalar-checked inc/dec.
// UNSAFE-LEDGER: FLN-UL-0220
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_task_map_core")]
pub(crate) extern "C" fn export_lean_task_map_core(
    f: *mut LeanObject,
    t: *mut LeanObject,
    prio: c_uint,
    sync: bool,
    keep_alive: bool,
) -> *mut LeanObject {
    use crate::task_manager::{self, LEAN_SYNC_PRIO, TaskPtr};
    // SAFETY: f and t are consumed on both arms; the eager arm follows the
    // pin's scalar-checked get_own discipline, the manager arm hands both
    // references to the mark_mt'd map closure.
    unsafe {
        let (v, _) = object::task_fields(t);
        let mgr = task_manager::manager();
        if mgr.is_none() || (sync && !v.is_null()) {
            if v.is_null() {
                task_manager_refusal("`Task.map` on an unfinished task");
            }
            if !is_scalar(v) {
                rc::inc_ref_n(v, 1);
            }
            if !is_scalar(t) {
                rc::dec_ref(t); // 3gv-M2 anchor: map_core releases its consumed task
            }
            let r = apply_core(f, &[v]);
            return object::alloc_task_pure(r);
        }
        let mgr = mgr.expect("manager arm");
        let c = object::alloc_closure(task_manager::task_map_fn as *mut c_void, 3, 2);
        object::closure_set(c, 0, f);
        object::closure_set(c, 1, t);
        let new_task =
            object::alloc_task_scheduled(c, if sync { LEAN_SYNC_PRIO } else { prio }, keep_alive);
        mgr.add_dep(TaskPtr(t.cast()), TaskPtr(new_task.cast()));
        new_task
    }
}

/// `lean_io_get_task_state` (`io.cpp:1579-1581` over `_core`,
/// `object.cpp:1260-1265`; extern census `IO.getTaskState`): Finished
/// (`m_imp == NULL`) answers 2 before the manager is ever consulted; the
/// `m_imp != NULL` arm takes the manager's locked read (0 waiting/queued,
/// 1 running/promised), and without a manager — where the pin null-derefs —
/// refuses typed. The `_core` census symbol is served below since slice 8e.
// UNSAFE-LEDGER: FLN-UL-0221
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_get_task_state")]
pub(crate) extern "C" fn export_lean_io_get_task_state(t: *mut LeanObject) -> u8 {
    // SAFETY: t is a live (borrowed) task; only its header-adjacent fields
    // are read.
    unsafe {
        let (_, imp) = object::task_fields(t);
        if imp.is_null() {
            return 2; // finished — the pin's pre-manager fast path
        }
    }
    if let Some(mgr) = crate::task_manager::manager() {
        return mgr.get_task_state(crate::task_manager::TaskPtr(t.cast()));
    }
    task_manager_refusal("`IO.getTaskState` on an unfinished task")
}

/// `lean_io_get_task_state_core` (`object.cpp:1260-1265`): the runtime-layer
/// symbol the pin's `lean_io_get_task_state` wrapper calls. Ours inverts the
/// delegation direction — the core delegates to the wrapper above, whose
/// body IS the core's (null `m_imp` fast path, then the manager's locked
/// read) — observably identical, one copy of the logic (fln-3gv slice 8e).
// UNSAFE-LEDGER: FLN-UL-0427
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_get_task_state_core")]
pub(crate) extern "C" fn export_lean_io_get_task_state_core(t: *mut LeanObject) -> u8 {
    export_lean_io_get_task_state(t)
}

/// `lean_io_promise_new` (`object.cpp:1271-1292, 1298-1301`; extern census
/// `IO.Promise.new`): with the manager running, an ST promise object owning
/// one Promised task; before it runs, the pin REFUSES with this exact
/// internal panic — reproduced verbatim, message and exit path.
// UNSAFE-LEDGER: FLN-UL-0222
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_promise_new")]
pub(crate) extern "C" fn export_lean_io_promise_new() -> *mut LeanObject {
    if crate::task_manager::manager().is_some() {
        // SAFETY: the allocator owns header/field init for both objects.
        return unsafe { object::alloc_promise() };
    }
    internal_panic_impl(concat!(
        "`IO.Promise.new` called before the task manager is running; this typically ",
        "happens when called (directly or transitively, e.g. via `IO.CancelToken.new`) ",
        "from an `initialize` block. Construct lazily on first use instead."
    ))
}

/// `lean_io_promise_resolve` (`object.cpp:1294-1296, 1303-1306`; extern
/// census `IO.Promise.resolve`): resolve the promise's task to
/// `some value` — first call wins, the second value is silently dropped —
/// returning unit. Without a manager — where the pin null-derefs — a typed
/// refusal (no promise is constructible there anyway).
// UNSAFE-LEDGER: FLN-UL-0223
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_promise_resolve")]
pub(crate) extern "C" fn export_lean_io_promise_resolve(
    value: *mut LeanObject,
    promise: *mut LeanObject,
) -> *mut LeanObject {
    if let Some(mgr) = crate::task_manager::manager() {
        // SAFETY: promise is a live (borrowed) promise object; the value is
        // consumed into the `some` cell exactly as mk_option_some does.
        unsafe {
            let some = object::alloc_ctor(1, 1, 0);
            object::ctor_set(some, 0, value);
            let r =
                (&raw const (*promise.cast::<crate::layout::LeanPromiseObject>()).m_result).read();
            mgr.resolve(crate::task_manager::TaskPtr(r), some);
        }
        return crate::tagged::boxi(0);
    }
    task_manager_refusal("`IO.Promise.resolve`")
}

/// `lean_io_promise_result_opt` (`object.cpp:1308-1312`; extern census
/// `IO.Promise.result?`): one `inc_ref` of the promise's result task —
/// pure, exactly the pin's body. Without a manager — where no promise can
/// exist — a typed refusal rather than a read of a nonexistent object.
// UNSAFE-LEDGER: FLN-UL-0224
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_promise_result_opt")]
pub(crate) extern "C" fn export_lean_io_promise_result_opt(
    promise: *mut LeanObject,
) -> *mut LeanObject {
    if crate::task_manager::manager().is_some() {
        // SAFETY: promise is a live (borrowed) promise; the task's MT rc
        // takes one more token.
        unsafe {
            let r =
                (&raw const (*promise.cast::<crate::layout::LeanPromiseObject>()).m_result).read();
            let t = r.cast::<LeanObject>();
            rc::inc_ref_n(t, 1);
            return t;
        }
    }
    task_manager_refusal("`IO.Promise.result?`")
}

/// `lean_option_get_or_block` (`io.cpp:1627-1639`; extern census
/// `Option.getOrBlock!`): despite the name it never blocks on a task — it
/// unwraps an already-materialized `Option`. `some v` steals the value out
/// of the consumed option cell; `none` is the pin's
/// `lean_panic(..., force_stderr)` followed by the non-fatal-panic arm's
/// deliberate sleep-forever loop (io.cpp:1633-1638), arm-for-arm.
// UNSAFE-LEDGER: FLN-UL-0225
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_option_get_or_block")]
pub(crate) extern "C" fn export_lean_option_get_or_block(o: *mut LeanObject) -> *mut LeanObject {
    if is_scalar(o) {
        // `none` (`box(0)`): the pin's panic; then, when panics are
        // non-fatal, its forever-sleep rather than a fabricated value.
        panic_impl(
            b"PANIC: Promise.result!: promise has been dropped without ever being resolved",
            false,
        );
        loop {
            std::thread::sleep(std::time::Duration::from_secs(86_400));
        }
    }
    // SAFETY: o is a live owned `some` cell; the value is duplicated before
    // the cell's release, so the steal is ownership-balanced
    // (`option_ref::steal`'s discipline).
    unsafe {
        let v = object::ctor_get(o, 0);
        if !is_scalar(v) {
            rc::inc_ref_n(v, 1);
        }
        rc::dec_ref(o);
        v
    }
}

// ===================================================================
// fln-3gv slice 3: the task manager goes live — init/finalize, spawn and
// bind cores, cancellation. The manager itself is `task_manager.rs` (the
// literal object.cpp:727-1113 port; design + asupersync pricing in
// bead-comments fln-3gv:1847/:1852). The slice-2 state family above gained
// its manager arms in place; the pre-manager else-arms are unchanged and
// remain the pin's own managerless behavior.
// ===================================================================

/// `lean_init_task_manager` (`object.cpp:1083-1085`): `LEAN_NUM_THREADS`
/// else hardware concurrency.
// UNSAFE-LEDGER: FLN-UL-0244
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_init_task_manager")]
pub(crate) extern "C" fn export_lean_init_task_manager() {
    crate::task_manager::init_using(crate::task_manager::default_num_workers());
}

/// `lean_init_task_manager_using` (`object.cpp:1065-1072`): zero workers
/// installs NO manager, exactly as upstream.
// UNSAFE-LEDGER: FLN-UL-0245
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_init_task_manager_using")]
pub(crate) extern "C" fn export_lean_init_task_manager_using(num_workers: c_uint) {
    crate::task_manager::init_using(num_workers);
}

/// `lean_finalize_task_manager` (`object.cpp:1092-1097`): drain, join, drop.
// UNSAFE-LEDGER: FLN-UL-0246
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_finalize_task_manager")]
pub(crate) extern "C" fn export_lean_finalize_task_manager() {
    crate::task_manager::finalize();
}

/// `lean_task_spawn_core` (`object.cpp:1152-1160`): enqueue a Queued task
/// through the manager; without one, the pin's eager arm verbatim.
// UNSAFE-LEDGER: FLN-UL-0247
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_task_spawn_core")]
pub(crate) extern "C" fn export_lean_task_spawn_core(
    c: *mut LeanObject,
    prio: c_uint,
    keep_alive: bool,
) -> *mut LeanObject {
    use crate::task_manager::{self, TaskPtr};
    // SAFETY: c is consumed on both arms — into the scheduled task, or by
    // the eager apply.
    unsafe {
        if let Some(mgr) = task_manager::manager() {
            let t = object::alloc_task_scheduled(c, prio, keep_alive);
            mgr.enqueue(TaskPtr(t.cast()));
            t
        } else {
            let r = apply_core(c, &[crate::tagged::boxi(0)]);
            object::alloc_task_pure(r)
        }
    }
}

/// `lean_task_bind_core` (`object.cpp:1234-1244`): a Waiting task carrying
/// `task_bind_fn1` joins the graph; the eager arm — no manager, or `sync`
/// with a finished input — is `apply_1(f, get_own(x))` returning whatever
/// task `f` made, exactly as the pin (no re-wrap).
// UNSAFE-LEDGER: FLN-UL-0248
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_task_bind_core")]
pub(crate) extern "C" fn export_lean_task_bind_core(
    x: *mut LeanObject,
    f: *mut LeanObject,
    prio: c_uint,
    sync: bool,
    keep_alive: bool,
) -> *mut LeanObject {
    use crate::task_manager::{self, LEAN_SYNC_PRIO, TaskPtr};
    // SAFETY: x and f are consumed on both arms; the manager arm hands both
    // to the mark_mt'd bind closure.
    unsafe {
        let (v, _) = object::task_fields(x);
        let mgr = task_manager::manager();
        if mgr.is_none() || (sync && !v.is_null()) {
            if v.is_null() {
                task_manager_refusal("`Task.bind` on an unfinished task");
            }
            if !is_scalar(v) {
                rc::inc_ref_n(v, 1);
            }
            if !is_scalar(x) {
                rc::dec_ref(x);
            }
            return apply_core(f, &[v]);
        }
        let mgr = mgr.expect("manager arm");
        let c = object::alloc_closure(task_manager::task_bind_fn1 as *mut c_void, 3, 2);
        object::closure_set(c, 0, x);
        object::closure_set(c, 1, f);
        let new_task =
            object::alloc_task_scheduled(c, if sync { LEAN_SYNC_PRIO } else { prio }, keep_alive);
        mgr.add_dep(TaskPtr(x.cast()), TaskPtr(new_task.cast()));
        new_task
    }
}

/// `lean_io_check_canceled_core` (`object.cpp:1246-1252`): the current
/// task's cancellation flag, or the manager's shutdown; `false` off-worker
/// and managerless — the pin's own answers.
// UNSAFE-LEDGER: FLN-UL-0249
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_check_canceled_core")]
pub(crate) extern "C" fn export_lean_io_check_canceled_core() -> bool {
    crate::task_manager::manager().is_some_and(crate::task_manager::Manager::check_canceled_current)
}

/// `lean_io_cancel_core` (`object.cpp:1254-1258`): finished tasks are a
/// no-op before the manager is consulted; unfinished ones set the flag
/// under the lock. Managerless — where the pin null-derefs — the finished
/// arm still answers and the unreachable arm refuses typed.
// UNSAFE-LEDGER: FLN-UL-0250
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_cancel_core")]
pub(crate) extern "C" fn export_lean_io_cancel_core(t: *mut LeanObject) {
    // SAFETY: t is a live (borrowed) task.
    unsafe {
        let (v, _) = object::task_fields(t);
        if !v.is_null() {
            return;
        }
    }
    if let Some(mgr) = crate::task_manager::manager() {
        mgr.cancel(crate::task_manager::TaskPtr(t.cast()));
        return;
    }
    task_manager_refusal("`IO.cancel` on an unfinished task")
}

// ===================================================================
// fln-3gv slice 3b: the io.cpp wrapper family over the live cores
// (io.cpp:1534-1592). At this pin a compiled BaseIO result IS the bare
// value (the world is erased and the error arm is impossible), so the
// task-body closures apply the action/function to the world token and
// return the result unchanged — exactly what the pin's object_ref dance
// nets to. All three task builders pass keep_alive = true, the pin's own
// IO-vs-Task distinction.
// ===================================================================

/// `lean_io_as_task_fn` (`io.cpp:1535-1538`): apply the BaseIO action to
/// the world token; the bare result is the task's value.
// UNSAFE-LEDGER: FLN-UL-0254
#[allow(unsafe_code)]
pub(crate) extern "C" fn io_as_task_fn(
    act: *mut LeanObject,
    _w: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: act is the owned BaseIO action; apply consumes it and yields
    // the owned bare result.
    unsafe { apply_core(act, &[crate::tagged::boxi(0)]) }
}

/// `lean_io_bind_task_fn` (`io.cpp:1548-1551`): apply `f` to the task's
/// value and the world token; serves both mapTask (bare β out) and
/// bindTask (a Task β out), exactly as the pin reuses it.
// UNSAFE-LEDGER: FLN-UL-0255
#[allow(unsafe_code)]
pub(crate) extern "C" fn io_bind_task_fn(
    f: *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: f and a are owned; apply consumes both and yields the owned
    // result.
    unsafe { apply_core(f, &[a, crate::tagged::boxi(0)]) }
}

/// `lean_io_as_task` (`io.cpp:1541-1546`; extern census `BaseIO.asTask`):
/// spawn the action's closure with `keep_alive = true` — an IO task runs
/// even if its last reference is dropped.
// UNSAFE-LEDGER: FLN-UL-0256
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_as_task")]
pub(crate) extern "C" fn export_lean_io_as_task(
    act: *mut LeanObject,
    prio: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: act is consumed into the closure; the boxed prio is unboxed
    // exactly as the pin does.
    unsafe {
        let c = object::alloc_closure(io_as_task_fn as *mut c_void, 2, 1);
        object::closure_set(c, 0, act);
        export_lean_task_spawn_core(c, crate::tagged::unbox(prio) as c_uint, true)
    }
}

/// `lean_io_map_task` (`io.cpp:1554-1559`; extern census `BaseIO.mapTask`).
// UNSAFE-LEDGER: FLN-UL-0257
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_map_task")]
pub(crate) extern "C" fn export_lean_io_map_task(
    f: *mut LeanObject,
    t: *mut LeanObject,
    prio: *mut LeanObject,
    sync: u8,
) -> *mut LeanObject {
    // SAFETY: f is consumed into the closure, t into map_core.
    unsafe {
        let c = object::alloc_closure(io_bind_task_fn as *mut c_void, 2, 1);
        object::closure_set(c, 0, f);
        export_lean_task_map_core(c, t, crate::tagged::unbox(prio) as c_uint, sync != 0, true)
    }
}

/// `lean_io_bind_task` (`io.cpp:1562-1567`; extern census
/// `BaseIO.bindTask`).
// UNSAFE-LEDGER: FLN-UL-0258
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_bind_task")]
pub(crate) extern "C" fn export_lean_io_bind_task(
    t: *mut LeanObject,
    f: *mut LeanObject,
    prio: *mut LeanObject,
    sync: u8,
) -> *mut LeanObject {
    // SAFETY: f is consumed into the closure, t into bind_core.
    unsafe {
        let c = object::alloc_closure(io_bind_task_fn as *mut c_void, 2, 1);
        object::closure_set(c, 0, f);
        export_lean_task_bind_core(t, c, crate::tagged::unbox(prio) as c_uint, sync != 0, true)
    }
}

/// `lean_io_check_canceled` (`io.cpp:1570-1572`; extern census
/// `IO.checkCanceled`).
// UNSAFE-LEDGER: FLN-UL-0259
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_check_canceled")]
pub(crate) extern "C" fn export_lean_io_check_canceled() -> u8 {
    u8::from(export_lean_io_check_canceled_core())
}

/// `lean_io_cancel` (`io.cpp:1574-1577`; extern census `IO.cancel`).
// UNSAFE-LEDGER: FLN-UL-0260
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_cancel")]
pub(crate) extern "C" fn export_lean_io_cancel(t: *mut LeanObject) -> *mut LeanObject {
    export_lean_io_cancel_core(t);
    crate::tagged::boxi(0)
}

/// `lean_io_wait` (`io.cpp:1583-1585`; extern census `IO.wait`):
/// `lean_task_get_own` — get (blocking through the manager where needed),
/// then the scalar-checked inc/dec of the lean.h inline.
// UNSAFE-LEDGER: FLN-UL-0261
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_wait")]
pub(crate) extern "C" fn export_lean_io_wait(t: *mut LeanObject) -> *mut LeanObject {
    let v = export_lean_task_get(t);
    // SAFETY: v is the borrowed published value; t is the consumed task.
    unsafe {
        if !is_scalar(v) {
            rc::inc_ref_n(v, 1);
        }
        if !is_scalar(t) {
            rc::dec_ref(t);
        }
    }
    v
}

/// `lean_io_wait_any_core` (`object.cpp:1267-1269` over `wait_any`,
/// `object.cpp:919-929, 1014-1023`): the first FINISHED member in list
/// order, borrowed; block-and-rescan through the manager until one
/// appears. Managerless — where the pin null-derefs unconditionally — the
/// finished-scan still answers and the empty-handed arm refuses typed.
// UNSAFE-LEDGER: FLN-UL-0262
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_wait_any_core")]
pub(crate) extern "C" fn export_lean_io_wait_any_core(
    task_list: *mut LeanObject,
) -> *mut LeanObject {
    if let Some(mgr) = crate::task_manager::manager() {
        return mgr
            .wait_any(task_list)
            .expect("wait_any blocks until a member finishes");
    }
    if let Some(t) = crate::task_manager::wait_any_check(task_list) {
        return t;
    }
    task_manager_refusal("`IO.waitAny` with no finished member")
}

/// `lean_io_wait_any` (`io.cpp:1587-1592`; extern census `IO.waitAny`):
/// wait_any_core, then the winner's value duplicated out.
// UNSAFE-LEDGER: FLN-UL-0263
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_wait_any")]
pub(crate) extern "C" fn export_lean_io_wait_any(task_list: *mut LeanObject) -> *mut LeanObject {
    let t = export_lean_io_wait_any_core(task_list);
    let v = export_lean_task_get(t);
    // SAFETY: v is the borrowed published value of a finished task; one
    // token is minted for the caller (the pin's lean_inc).
    unsafe {
        if !is_scalar(v) {
            rc::inc_ref_n(v, 1);
        }
    }
    v
}

// ================================================================ stdio
// fln-3gv slice 5a (design comment 1856): the stdio plane — the
// thread-current stream trio, the Handle prims the println path drives,
// and the native Stream.ofHandle. Signatures match io.cpp exactly; the
// mechanism deviations are disclosed in stdio.rs's module doc.

/// `lean_get_stdin` (`io.cpp:119-121`; extern census `IO.getStdin`).
// UNSAFE-LEDGER: FLN-UL-0304
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_get_stdin")]
pub(crate) extern "C" fn export_lean_get_stdin() -> *mut LeanObject {
    crate::stdio::get_stdin()
}

/// `lean_get_stdout` (`io.cpp:124-126`; extern census `IO.getStdout`).
// UNSAFE-LEDGER: FLN-UL-0305
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_get_stdout")]
pub(crate) extern "C" fn export_lean_get_stdout() -> *mut LeanObject {
    crate::stdio::get_stdout()
}

/// `lean_get_stderr` (`io.cpp:129-131`; extern census `IO.getStderr`).
// UNSAFE-LEDGER: FLN-UL-0306
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_get_stderr")]
pub(crate) extern "C" fn export_lean_get_stderr() -> *mut LeanObject {
    crate::stdio::get_stderr()
}

/// `lean_get_set_stdin` (`io.cpp:134-139`; extern census `IO.setStdin`).
// UNSAFE-LEDGER: FLN-UL-0307
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_get_set_stdin")]
pub(crate) extern "C" fn export_lean_get_set_stdin(h: *mut LeanObject) -> *mut LeanObject {
    crate::stdio::get_set_stdin(h)
}

/// `lean_get_set_stdout` (`io.cpp:142-147`; extern census `IO.setStdout`).
// UNSAFE-LEDGER: FLN-UL-0308
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_get_set_stdout")]
pub(crate) extern "C" fn export_lean_get_set_stdout(h: *mut LeanObject) -> *mut LeanObject {
    crate::stdio::get_set_stdout(h)
}

/// `lean_get_set_stderr` (`io.cpp:150-155`; extern census `IO.setStderr`).
// UNSAFE-LEDGER: FLN-UL-0309
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_get_set_stderr")]
pub(crate) extern "C" fn export_lean_get_set_stderr(h: *mut LeanObject) -> *mut LeanObject {
    crate::stdio::get_set_stderr(h)
}

/// `lean_io_prim_handle_mk` (`io.cpp:385-418`; extern census
/// `IO.FS.Handle.mk`): borrowed filename + mode byte to an io_result
/// Handle.
// UNSAFE-LEDGER: FLN-UL-0299
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_mk")]
pub(crate) extern "C" fn export_lean_io_prim_handle_mk(
    filename: *mut LeanObject,
    mode: u8,
) -> *mut LeanObject {
    // SAFETY: filename is borrowed and live per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_mk(filename, mode) }
}

/// `lean_io_prim_handle_put_str` (`io.cpp:661-670`; extern census
/// `IO.FS.Handle.putStr`).
// UNSAFE-LEDGER: FLN-UL-0300
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_put_str")]
pub(crate) extern "C" fn export_lean_io_prim_handle_put_str(
    h: *mut LeanObject,
    s: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: both borrowed and live per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_put_str(h, s) }
}

/// `lean_io_prim_handle_flush` (`io.cpp:550-556`; extern census
/// `IO.FS.Handle.flush`).
// UNSAFE-LEDGER: FLN-UL-0301
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_flush")]
pub(crate) extern "C" fn export_lean_io_prim_handle_flush(h: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: borrowed live handle per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_flush(h) }
}

/// `lean_io_prim_handle_read` (`io.cpp:584-607`; extern census
/// `IO.FS.Handle.read`): borrowed handle + byte count to an io_result
/// ByteArray, with the pin's EOF and zero-read arms.
// UNSAFE-LEDGER: FLN-UL-0318
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_read")]
pub(crate) extern "C" fn export_lean_io_prim_handle_read(
    h: *mut LeanObject,
    nbytes: usize,
) -> *mut LeanObject {
    // SAFETY: borrowed live handle per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_read(h, nbytes) }
}

/// `lean_io_prim_handle_write` (`io.cpp:609-618`; extern census
/// `IO.FS.Handle.write`).
// UNSAFE-LEDGER: FLN-UL-0319
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_write")]
pub(crate) extern "C" fn export_lean_io_prim_handle_write(
    h: *mut LeanObject,
    buf: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: both borrowed and live per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_write(h, buf) }
}

/// `lean_io_prim_handle_get_line` (`io.cpp:635-659`; extern census
/// `IO.FS.Handle.getLine`): borrowed handle to an io_result String — the
/// locked byte loop, the retained newline, the EOF partial-line arm, and
/// the lossy-U+FFFD string constructor, exactly the pin's arms.
// UNSAFE-LEDGER: FLN-UL-0331
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_get_line")]
pub(crate) extern "C" fn export_lean_io_prim_handle_get_line(
    h: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: borrowed live handle per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_get_line(h) }
}

/// `lean_io_prim_handle_rewind` (`io.cpp:560-568`; extern census
/// `IO.FS.Handle.rewind`).
// UNSAFE-LEDGER: FLN-UL-0338
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_rewind")]
pub(crate) extern "C" fn export_lean_io_prim_handle_rewind(h: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: borrowed live handle per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_rewind(h) }
}

/// `lean_io_prim_handle_truncate` (`io.cpp:570-582`; extern census
/// `IO.FS.Handle.truncate`): ftruncate at the current offset.
// UNSAFE-LEDGER: FLN-UL-0339
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_truncate")]
pub(crate) extern "C" fn export_lean_io_prim_handle_truncate(
    h: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: borrowed live handle per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_truncate(h) }
}

/// `lean_io_prim_handle_lock` (`io.cpp:480-488`; extern census
/// `IO.FS.Handle.lock`): blocking flock, exclusive or shared.
// UNSAFE-LEDGER: FLN-UL-0340
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_lock")]
pub(crate) extern "C" fn export_lean_io_prim_handle_lock(
    h: *mut LeanObject,
    exclusive: u8,
) -> *mut LeanObject {
    // SAFETY: borrowed live handle per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_lock(h, exclusive) }
}

/// `lean_io_prim_handle_try_lock` (`io.cpp:490-502`; extern census
/// `IO.FS.Handle.tryLock`): held elsewhere is `ok false`, never an error.
// UNSAFE-LEDGER: FLN-UL-0341
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_try_lock")]
pub(crate) extern "C" fn export_lean_io_prim_handle_try_lock(
    h: *mut LeanObject,
    exclusive: u8,
) -> *mut LeanObject {
    // SAFETY: borrowed live handle per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_try_lock(h, exclusive) }
}

/// `lean_io_prim_handle_unlock` (`io.cpp:504-512`; extern census
/// `IO.FS.Handle.unlock`).
// UNSAFE-LEDGER: FLN-UL-0342
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_unlock")]
pub(crate) extern "C" fn export_lean_io_prim_handle_unlock(h: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: borrowed live handle per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_unlock(h) }
}

/// `lean_chmod` (`io.cpp:372-382`; extern census `IO.setAccessRights`).
// UNSAFE-LEDGER: FLN-UL-0353
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_chmod")]
pub(crate) extern "C" fn export_lean_chmod(
    filename: *mut LeanObject,
    mode: u32,
) -> *mut LeanObject {
    // SAFETY: borrowed live string per the b_obj_arg contract.
    unsafe { crate::fs::prim_chmod(filename, mode) }
}

/// `lean_io_create_dir` (`io.cpp:1169-1183`; extern census
/// `IO.FS.createDir`).
// UNSAFE-LEDGER: FLN-UL-0354
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_create_dir")]
pub(crate) extern "C" fn export_lean_io_create_dir(p: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: borrowed live string per the b_obj_arg contract.
    unsafe { crate::fs::prim_create_dir(p) }
}

/// `lean_io_remove_dir` (`io.cpp:1185-1195`; extern census
/// `IO.FS.removeDir`).
// UNSAFE-LEDGER: FLN-UL-0355
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_remove_dir")]
pub(crate) extern "C" fn export_lean_io_remove_dir(p: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: borrowed live string per the b_obj_arg contract.
    unsafe { crate::fs::prim_remove_dir(p) }
}

/// `lean_io_rename` (`io.cpp:1197-1227`; extern census `IO.FS.rename`).
// UNSAFE-LEDGER: FLN-UL-0356
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_rename")]
pub(crate) extern "C" fn export_lean_io_rename(
    from: *mut LeanObject,
    to: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: both borrowed and live per the b_obj_arg contract.
    unsafe { crate::fs::prim_rename(from, to) }
}

/// `lean_io_current_dir` (`io.cpp:1409-1417`; extern census
/// `IO.currentDir`).
// UNSAFE-LEDGER: FLN-UL-0357
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_current_dir")]
pub(crate) extern "C" fn export_lean_io_current_dir() -> *mut LeanObject {
    // SAFETY: no arguments; the prim owns every object it builds.
    unsafe { crate::fs::prim_current_dir() }
}

/// `lean_io_realpath` (`io.cpp:1002-1055`; extern census
/// `IO.FS.realPath`). The pin's own signature takes `filename` OWNED
/// (`obj_arg`), unlike every sibling.
// UNSAFE-LEDGER: FLN-UL-0358
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_realpath")]
pub(crate) extern "C" fn export_lean_io_realpath(filename: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: owned live string per the pin's obj_arg contract.
    unsafe { crate::fs::prim_realpath(filename) }
}

/// `lean_io_read_dir` (`io.cpp:1064-1086`; extern census
/// `IO.FS.readDir`): an Array of two-field DirEntry ctors.
// UNSAFE-LEDGER: FLN-UL-0359
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_read_dir")]
pub(crate) extern "C" fn export_lean_io_read_dir(dirname: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: borrowed live string per the b_obj_arg contract.
    unsafe { crate::fs::prim_read_dir(dirname) }
}

/// `lean_io_remove_file` (`io.cpp:1339-1350`; extern census
/// `IO.FS.removeFile`): unlink through the uv-error decoder — the pin
/// routes this member through libuv, so its failure carries libuv's
/// NEGATED code and uv_strerror details, measured in
/// `tribunal/fixtures/c4/uv_error_contract.txt`.
// UNSAFE-LEDGER: FLN-UL-0364
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_remove_file")]
pub(crate) extern "C" fn export_lean_io_remove_file(filename: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: borrowed live string per the b_obj_arg contract.
    unsafe { crate::fs::prim_remove_file(filename) }
}

/// `lean_io_hard_link` (`io.cpp:1229-1245`; extern census
/// `IO.FS.Handle`-adjacent `hardLink`): link(2) through the uv-error
/// decoder, failure attributed to the ORIG path as the pin's.
// UNSAFE-LEDGER: FLN-UL-0365
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_hard_link")]
pub(crate) extern "C" fn export_lean_io_hard_link(
    orig: *mut LeanObject,
    link_path: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: both borrowed and live per the b_obj_arg contract.
    unsafe { crate::fs::prim_hard_link(orig, link_path) }
}

/// `lean_io_create_tempfile` (`io.cpp:1248-1291`; extern census
/// `IO.FS.createTempFile`): the `(Handle × FilePath)` pair over mkostemp
/// with O_CLOEXEC (libuv's own call), failure through the uv decoder.
// UNSAFE-LEDGER: FLN-UL-0369
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_create_tempfile")]
pub(crate) extern "C" fn export_lean_io_create_tempfile(_w: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: the world token is unused exactly as the pin's signature.
    unsafe { crate::fs::prim_create_tempfile() }
}

/// `lean_io_create_tempdir` (`io.cpp:1294-1337`; extern census
/// `IO.FS.createTempDir`): the created path over mkdtemp.
// UNSAFE-LEDGER: FLN-UL-0370
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_create_tempdir")]
pub(crate) extern "C" fn export_lean_io_create_tempdir(_w: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: the world token is unused exactly as the pin's signature.
    unsafe { crate::fs::prim_create_tempdir() }
}

/// `lean_io_metadata` (`io.cpp:1131-1146`; extern census
/// `IO.FS.metadata`): stat into the pin's Metadata ctor, failure through
/// the measured uv decoder.
// UNSAFE-LEDGER: FLN-UL-0376
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_metadata")]
pub(crate) extern "C" fn export_lean_io_metadata(filename: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: borrowed live string per the b_obj_arg contract.
    unsafe { crate::fs::prim_metadata(filename) }
}

/// `lean_io_symlink_metadata` (`io.cpp:1148-1165`; extern census
/// `IO.FS.symlinkMetadata`): lstat, otherwise as metadata.
// UNSAFE-LEDGER: FLN-UL-0377
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_symlink_metadata")]
pub(crate) extern "C" fn export_lean_io_symlink_metadata(
    filename: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: borrowed live string per the b_obj_arg contract.
    unsafe { crate::fs::prim_symlink_metadata(filename) }
}

/// `lean_io_getenv` (`io.cpp:964-1000`; extern census `IO.getEnv`): the
/// bare Option, exactly the pin's BaseIO shape — an embedded NUL answers
/// `none`, never an error.
// UNSAFE-LEDGER: FLN-UL-0389
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_getenv")]
pub(crate) extern "C" fn export_lean_io_getenv(env_var: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: borrowed live string per the b_obj_arg contract.
    unsafe { crate::fs::prim_getenv(env_var) }
}

/// `lean_io_mono_ms_now` (`io.cpp:843-849`; extern census
/// `IO.monoMsNow`): the bare Nat, the pin's BaseIO shape.
// UNSAFE-LEDGER: FLN-UL-0390
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_mono_ms_now")]
pub(crate) extern "C" fn export_lean_io_mono_ms_now() -> *mut LeanObject {
    // SAFETY: no arguments; the prim owns every object it builds.
    unsafe { crate::fs::prim_mono_ms_now() }
}

/// `lean_io_mono_nanos_now` (`io.cpp:851-857`; extern census
/// `IO.monoNanosNow`).
// UNSAFE-LEDGER: FLN-UL-0391
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_mono_nanos_now")]
pub(crate) extern "C" fn export_lean_io_mono_nanos_now() -> *mut LeanObject {
    // SAFETY: no arguments; the prim owns every object it builds.
    unsafe { crate::fs::prim_mono_nanos_now() }
}

/// `lean_io_get_tid` (`process.cpp:340-352`; extern census `IO.getTID`).
// UNSAFE-LEDGER: FLN-UL-0392
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_get_tid")]
pub(crate) extern "C" fn export_lean_io_get_tid() -> u64 {
    // SAFETY: trivially safe syscall wrapper.
    unsafe { crate::fs::prim_get_tid() }
}

/// `lean_io_process_get_pid` (`process.cpp:330-333`; extern census
/// `IO.Process.getPID`).
// UNSAFE-LEDGER: FLN-UL-0393
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_process_get_pid")]
pub(crate) extern "C" fn export_lean_io_process_get_pid() -> u32 {
    // SAFETY: trivially safe syscall wrapper.
    unsafe { crate::fs::prim_get_pid() }
}

/// `lean_io_app_path` (`io.cpp:1354-1407`, the Linux arm; extern census
/// `IO.appPath`): readlink of `/proc/<pid>/exe`; failure the pin's bare
/// userError.
// UNSAFE-LEDGER: FLN-UL-0394
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_app_path")]
pub(crate) extern "C" fn export_lean_io_app_path() -> *mut LeanObject {
    // SAFETY: no arguments; the prim owns every object it builds.
    unsafe { crate::fs::prim_app_path() }
}

/// `lean_io_initializing` (`io.cpp:81-83`; extern census
/// `IO.initializing`) and its census-rowed setter twin below.
// UNSAFE-LEDGER: FLN-UL-0396
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_initializing")]
pub(crate) extern "C" fn export_lean_io_initializing() -> u8 {
    crate::fs::initializing()
}

/// `lean_io_mark_end_initialization` (`io.cpp:77-79`; lean.h census row):
/// the flag flip generated main performs after module initializers.
// UNSAFE-LEDGER: FLN-UL-0397
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_mark_end_initialization")]
pub(crate) extern "C" fn export_lean_io_mark_end_initialization() {
    crate::fs::mark_end_initialization();
}

/// `lean_io_get_random_bytes` (`io.cpp:865-925`, the POSIX arm; extern
/// census `IO.getRandomBytes`): `/dev/urandom` with the pin's zero-byte,
/// overflow and EINTR arms.
// UNSAFE-LEDGER: FLN-UL-0395
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_get_random_bytes")]
pub(crate) extern "C" fn export_lean_io_get_random_bytes(nbytes: usize) -> *mut LeanObject {
    // SAFETY: the prim owns every object it builds.
    unsafe { crate::fs::prim_get_random_bytes(nbytes) }
}

/// `lean_io_prim_handle_is_tty` (`io.cpp:516-531`; extern census
/// `IO.FS.Handle.isTty`): the raw bool, exactly the pin's C signature.
// UNSAFE-LEDGER: FLN-UL-0302
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_prim_handle_is_tty")]
pub(crate) extern "C" fn export_lean_io_prim_handle_is_tty(h: *mut LeanObject) -> u8 {
    // SAFETY: borrowed live handle per the b_obj_arg contract.
    unsafe { crate::stdio::prim_handle_is_tty(h) }
}

/// `lean_stream_of_handle` (`Init/System/IO.lean:1683`,
/// `@[export lean_stream_of_handle]`; consumed by the pin's own
/// `initialize_io`, io.cpp:109/1647-1652): the six-field `FS.Stream` over a
/// consumed Handle — served NATIVELY here because the pin's definition is
/// compiled Lean the staticlib does not carry (the B2 Native-Mirror arm at
/// spike depth, disclosed in stdio.rs).
// UNSAFE-LEDGER: FLN-UL-0303
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_stream_of_handle")]
pub(crate) extern "C" fn export_lean_stream_of_handle(h: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: h is consumed into the stream's closures.
    unsafe { crate::stdio::stream_of_handle(h) }
}

/// `lean_initialize_runtime_module` (`init_module.cpp:19-29`; the entry
/// every generated main stub calls before module initializers): the pin
/// initializes alloc/debug/object/io/thread/mutex/process/stack/libuv; in
/// Marrow every one of those planes is static or lazily seeded, so the
/// twin's eager half is exactly the io stream trio — the one plane whose
/// pin-side init has an observable (the SIGPIPE disposition and the
/// process-initial streams).
// UNSAFE-LEDGER: FLN-UL-0310
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_initialize_runtime_module")]
pub(crate) extern "C" fn export_lean_initialize_runtime_module() {
    crate::stdio::initialize_streams();
}

/// `lean_nat_to_size_t` (`object.cpp:2496-2508`): a scalar unboxes; a big
/// Nat that fits `size_t` yields its value and releases the object; one
/// that does not is the pin's internal out-of-memory panic.
///
/// # Safety
/// `n` is a live Nat, consumed exactly as the pin's `obj_arg`.
// UNSAFE-LEDGER: FLN-UL-0401
#[allow(unsafe_code)]
unsafe fn nat_to_usize(n: *mut LeanObject) -> usize {
    if is_scalar(n) {
        return crate::tagged::unbox(n);
    }
    // SAFETY: live mpz Nat per contract; the view does not escape.
    let value = unsafe {
        with_nat_view(n, |v| {
            let limbs = v.limbs_le();
            match limbs.len() {
                0 => Some(0usize),
                1 => usize::try_from(limbs[0]).ok(),
                _ => None,
            }
        })
    };
    let Some(value) = value else {
        internal_panic_impl("out of memory");
    };
    // SAFETY: the pin releases the consumed big Nat after reading it.
    unsafe {
        rc::dec_ref(n);
    }
    value
}

/// `lean_sarray_ensure_capacity` (`object.cpp:2534-2542`): at least
/// `min_cap`, doubling on copy unless `exact`.
///
/// # Safety
/// `a` live scalar array whose reference the caller yields.
// UNSAFE-LEDGER: FLN-UL-0402
#[allow(unsafe_code)]
unsafe fn sarray_ensure_capacity(
    a: *mut LeanObject,
    min_cap: usize,
    exact: bool,
) -> *mut LeanObject {
    // SAFETY: delegated salient reads and copies.
    unsafe {
        let (_, _, cap, _) = object::sarray_fields(a);
        if min_cap <= cap {
            a
        } else {
            copy_sarray(a, if exact { min_cap } else { min_cap * 2 })
        }
    }
}

/// `lean_sarray_ensure_exclusive` (`object.cpp:2525-2531`).
///
/// # Safety
/// `a` live scalar array whose reference the caller yields.
// UNSAFE-LEDGER: FLN-UL-0408
#[allow(unsafe_code)]
unsafe fn sarray_ensure_exclusive(a: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: delegated salient reads and copies.
    unsafe {
        if is_exclusive(a) {
            a
        } else {
            let (_, _, cap, _) = object::sarray_fields(a);
            copy_sarray(a, cap)
        }
    }
}

/// `lean_runtime_mark_multi_threaded` (`io.cpp:1602-1605`; extern census
/// `Runtime.markMultiThreaded`): the live mark_mt core's Runtime.* skin.
// UNSAFE-LEDGER: FLN-UL-0403
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_runtime_mark_multi_threaded")]
pub(crate) extern "C" fn export_lean_runtime_mark_multi_threaded(
    a: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: owned live object; marking never frees.
    unsafe {
        rc::mark_mt(a);
    }
    a
}

/// `lean_runtime_mark_persistent` (`io.cpp:1607-1610`; extern census
/// `Runtime.markPersistent`).
// UNSAFE-LEDGER: FLN-UL-0404
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_runtime_mark_persistent")]
pub(crate) extern "C" fn export_lean_runtime_mark_persistent(
    a: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: owned live object; marking never frees.
    unsafe {
        rc::mark_persistent(a);
    }
    a
}

/// `lean_runtime_forget` (`io.cpp:1618-1626`; extern census
/// `Runtime.forget`): the owned argument is DELIBERATELY leaked — that is
/// the operation — and unit is answered. The pin's ASAN ignore is a
/// sanitizer-build detail with no observable.
// UNSAFE-LEDGER: FLN-UL-0405
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_runtime_forget")]
pub(crate) extern "C" fn export_lean_runtime_forget(_o: *mut LeanObject) -> *mut LeanObject {
    crate::tagged::boxi(0)
}

/// `lean_string_validate_utf8` (`object.cpp:2037-2040`; extern census
/// `String.validateUTF8`): the validator over a borrowed ByteArray.
// UNSAFE-LEDGER: FLN-UL-0406
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_validate_utf8")]
pub(crate) extern "C" fn export_lean_string_validate_utf8(a: *mut LeanObject) -> u8 {
    // SAFETY: borrowed live sarray per the b_obj_arg contract.
    unsafe {
        let (_, sz, _, data) = object::sarray_fields(a);
        let bytes = if sz == 0 {
            &[][..]
        } else {
            core::slice::from_raw_parts(data, sz)
        };
        let mut pos = 0usize;
        let mut i = 0usize;
        u8::from(validate_utf8(bytes, &mut pos, &mut i))
    }
}

/// `lean_byte_array_copy_slice` (`object.cpp:2584-2603`), arm-for-arm:
/// the src-offset early return, the length clamp, the dest-offset clamp,
/// the grow-to-max sizing, ensure-capacity(exact)/ensure-exclusive, and
/// the non-overlapping copy the exclusivity guarantees.
// UNSAFE-LEDGER: FLN-UL-0407
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_byte_array_copy_slice")]
pub(crate) extern "C" fn export_lean_byte_array_copy_slice(
    src: *mut LeanObject,
    o_src_off: *mut LeanObject,
    dest: *mut LeanObject,
    o_dest_off: *mut LeanObject,
    o_len: *mut LeanObject,
    exact: bool,
) -> *mut LeanObject {
    // SAFETY: src borrowed, dest and the three Nats consumed per the pin's
    // signature; the copy targets an exclusive array sized to hold it.
    unsafe {
        let (_, ssz, _, sdata) = object::sarray_fields(src);
        let (_, dsz, _, _) = object::sarray_fields(dest);
        let src_off = nat_to_usize(o_src_off);
        if src_off > ssz {
            return dest;
        }
        let len = nat_to_usize(o_len).min(ssz - src_off);
        let mut dest_off = nat_to_usize(o_dest_off);
        if dest_off > dsz {
            dest_off = dsz;
        }
        let new_dsz = dsz.max(dest_off + len);
        let r = sarray_ensure_exclusive(sarray_ensure_capacity(dest, new_dsz, exact));
        (&raw mut (*r.cast::<crate::layout::LeanSarrayObject>()).m_size).write(new_dsz);
        let (_, _, _, rdata) = object::sarray_fields(r);
        core::ptr::copy_nonoverlapping(sdata.add(src_off), rdata.add(dest_off), len);
        r
    }
}

/// `lean_io_error_to_string` (`Init/System/IOError.lean:271`; extern census
/// `IO.Error.toString`): the pin's Lean-compiled pretty-printer, ported
/// arm-for-arm in `stdio::error_to_string`.
// UNSAFE-LEDGER: FLN-UL-0414
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_error_to_string")]
pub(crate) extern "C" fn export_lean_io_error_to_string(err: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: owned live IO.Error per the obj_arg contract.
    unsafe { crate::stdio::error_to_string(err) }
}

/// `lean_io_exit` (`io.cpp:1594-1596`; extern census `IO.Process.exit`'s
/// prim): `exit(code)`. Process-fatal, so its evidence is the gauntlet's
/// exit-parity mode (rc + the flushed-buffer split vs the Reference), never
/// an in-process cell.
// UNSAFE-LEDGER: FLN-UL-0419
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_exit")]
pub(crate) extern "C" fn export_lean_io_exit(code: u8) -> *mut LeanObject {
    crate::stdio::io_exit(code)
}

/// `lean_io_force_exit` (`io.cpp:1598-1600`): `std::_Exit(code)` — the
/// no-flush twin, split from `exit` by the same gauntlet mode pair.
// UNSAFE-LEDGER: FLN-UL-0420
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_force_exit")]
pub(crate) extern "C" fn export_lean_io_force_exit(code: u8) -> *mut LeanObject {
    crate::stdio::io_force_exit(code)
}

/// `lean_io_result_show_error` (`io.cpp:61-67`): "uncaught exception: " plus
/// the pretty-printed error and a newline on the process stderr, flushed —
/// `std::cerr << ... << std::endl`'s exact bytes on fd 2.
// UNSAFE-LEDGER: FLN-UL-0415
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_io_result_show_error")]
pub(crate) extern "C" fn export_lean_io_result_show_error(r: *mut LeanObject) {
    // SAFETY: borrowed live error-arm result per the b_obj_arg contract.
    unsafe {
        crate::stdio::io_result_show_error_core(r, &mut std::io::stderr().lock());
    }
}

/// `lean_decode_io_error` (`io.cpp:161-260`; census row `franken_lean-83r`):
/// the errno decoder every fs/handle prim shares, exported under the pin's
/// name — errnum plus a BORROWED, possibly-null filename to the exact
/// `IO.Error` arm. The EINTR/ENOENT arms require a filename exactly as the
/// pin's `lean_inc(fname)` does.
// UNSAFE-LEDGER: FLN-UL-0428
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_decode_io_error")]
pub(crate) extern "C" fn export_lean_decode_io_error(
    errnum: core::ffi::c_int,
    fname: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: fname borrowed (nullable) per the b_obj_arg contract.
    unsafe { crate::stdio::decode_io_error(errnum, fname) }
}

/// `lean_decode_uv_error` (`io.cpp:258` onward): the uv decoder over the
/// MEASURED 71-row contract table (`tribunal/fixtures/c4/uv_error_contract.txt`,
/// fln-3gv slice 6b), exported under the pin's name — the NEGATIVE uv code
/// plus a borrowed, possibly-null filename.
// UNSAFE-LEDGER: FLN-UL-0429
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_decode_uv_error")]
pub(crate) extern "C" fn export_lean_decode_uv_error(
    errnum: core::ffi::c_int,
    fname: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: fname borrowed (nullable) per the b_obj_arg contract.
    unsafe { crate::fs::decode_uv_error(errnum, fname) }
}

/// `lean_mk_io_user_error` (IOError.c:71 + its generated body; `IO.userError`):
/// the owned msg wrapped in the tag-18 `userError` ctor.
// UNSAFE-LEDGER: FLN-UL-0430
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_io_user_error")]
pub(crate) extern "C" fn export_lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: fresh 1-field ctor; the owned msg settles into its slot.
    unsafe {
        let r = object::alloc_ctor(18, 1, 0);
        object::ctor_set(r, 0, msg);
        r
    }
}
