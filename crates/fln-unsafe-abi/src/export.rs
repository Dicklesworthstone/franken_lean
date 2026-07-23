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
//! silent): closure application (`lean_apply_*`) — franken_lean-7xe; tasks /
//! IO (`lean_io_*`, `lean_task_*`) — fln-3gv; bignum arithmetic
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
use std::cell::Cell;
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
fn internal_panic_impl(msg: &str) -> ! {
    let mut err = std::io::stderr().lock();
    let _ = writeln!(err, "INTERNAL PANIC: {msg}");
    let _ = err.flush();
    if should_abort_on_panic() {
        std::process::abort();
    }
    std::process::exit(1);
}

/// `lean_panic_impl` (`object.cpp:139-146` shape): optional message, then
/// the exit/abort policy. Slice-1 restriction (status ledger): upstream
/// routes non-fatal messages through the Lean IO stderr buffer
/// (`io_eprintln`) and can print a backtrace; both need the fln-3gv IO
/// plane, so every message goes to the process stderr here.
fn panic_impl(msg: &[u8]) {
    if PANIC_MESSAGES.load(Ordering::Relaxed) {
        let mut err = std::io::stderr().lock();
        let _ = err.write_all(msg);
        let _ = err.write_all(b"\n");
        let _ = err.flush();
    }
    if EXIT_ON_PANIC.load(Ordering::Relaxed) {
        std::process::exit(1);
    }
    if should_abort_on_panic() {
        std::process::abort();
    }
}

thread_local! {
    /// `g_heartbeat` (`interrupt.cpp:18`): thread-local allocation/progress
    /// counter. The calibrated heartbeat *law* (fuel parity) is bead
    /// fln-8w8/G0-6; the counting twin lives here so the exported symbol has
    /// the pin's exact storage discipline from day one.
    static HEARTBEAT: Cell<usize> = const { Cell::new(0) };
}

/// Test hook: current thread's heartbeat count.
#[cfg(test)]
pub(crate) fn heartbeat_value() -> usize {
    HEARTBEAT.with(Cell::get)
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
unsafe fn mk_string_from_bytes_impl(s: *const c_char, sz: usize) -> *mut LeanObject {
    // SAFETY: caller (C contract) vouches for sz readable bytes.
    let bytes = if sz == 0 {
        &[][..]
    } else {
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

/// `lean_inc_heartbeat` (`interrupt.cpp:28`): thread-local counter.
// UNSAFE-LEDGER: FLN-UL-0079
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_inc_heartbeat")]
pub(crate) extern "C" fn export_lean_inc_heartbeat() {
    HEARTBEAT.with(|h| h.set(h.get().wrapping_add(1)));
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
    let _ = force_stderr; // both routes are the process stderr pre-fln-3gv
    // SAFETY: msg NUL-terminated per the contract.
    let bytes = unsafe { core::ffi::CStr::from_ptr(msg) }.to_bytes();
    panic_impl(bytes);
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
        panic_impl(bytes);
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

use fln_bignum::nat::BigNat;

/// Borrowed Nat operand → owned `BigNat` value copy.
///
/// # Safety
/// `o` is a live boxed scalar or mpz Nat object.
// UNSAFE-LEDGER: FLN-UL-0134
#[allow(unsafe_code)]
unsafe fn nat_as_bignat(o: *mut LeanObject) -> BigNat {
    if is_scalar(o) {
        BigNat::from_u64(crate::tagged::unbox(o) as u64)
    } else {
        // SAFETY: live mpz object; |m_size| limbs are salient (Nat: >= 0).
        let (_, size, limbs) = unsafe { object::mpz_fields(o) };
        debug_assert!(size >= 0, "Nat mpz objects are non-negative");
        BigNat::from_limbs_le(limbs)
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
    let (_, _, limbs) = unsafe { object::mpz_fields(a) };
    limbs.first().copied().unwrap_or(0)
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
        let r = nat_as_bignat(a1).add(&nat_as_bignat(a2));
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
        let n1 = nat_as_bignat(a1);
        let n2 = nat_as_bignat(a2);
        if !is_scalar(a2) && n1.ble(&n2) && !n2.ble(&n1) {
            return crate::tagged::boxi(0);
        }
        nat_obj_from_bignat(&n1.sub(&n2))
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
        let r = nat_as_bignat(a1).mul(&nat_as_bignat(a2));
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
        let r = nat_as_bignat(a1).div(&nat_as_bignat(a2));
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
        let r = nat_as_bignat(a1).rem(&nat_as_bignat(a2));
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
        nat_as_bignat(a1).beq(&nat_as_bignat(a2))
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
        nat_as_bignat(a1).ble(&nat_as_bignat(a2))
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
        let n1 = nat_as_bignat(a1);
        let n2 = nat_as_bignat(a2);
        n1.ble(&n2) && !n1.beq(&n2)
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
        let r = nat_as_bignat(a1).pow(crate::tagged::unbox(a2) as u32);
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
unsafe fn apply_core(f: *mut LeanObject, an: &[*mut LeanObject]) -> *mut LeanObject {
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
