//! CompatHeap object layouts — `repr(C)` mirrors of the pinned `lean_object`
//! ABI (plan §6.1, bead fln-lld).
//!
//! Every struct here mirrors a row of the generated contract tables in
//! [`crate::contract`]; the layout suite asserts field-by-field agreement
//! between these mirrors and offsets computed from the contract's C field
//! specs, and the C4 probe rig (`tribunal/fixtures/c4/`) asserts agreement
//! with `offsetof`/`sizeof` facts emitted by the real pinned toolchain.
//!
//! Bitfield law (G0-1 finding, `tribunal/fixtures/c3/FINDINGS.md` item 3):
//! the C header packs `m_cs_sz:16 | m_other:8 | m_tag:8` into one 4-byte
//! `unsigned` unit, allocated low-to-high on the certified little-endian
//! targets — so discrete `u16`/`u8`/`u8` fields at the same offsets are
//! byte-identical. The crate root refuses to compile on big-endian or
//! non-64-bit targets, which is what makes this mirror exact rather than
//! approximate.
//!
//! Flexible C arrays (`lean_object * m_objs[]`) are mirrored as zero-length
//! arrays: same trailing offset, zero size contribution.

use core::ffi::c_void;
use core::sync::atomic::AtomicPtr;

/// `lean_object` — the 8-byte object header (`lean.h:143-148`).
///
/// `m_rc` tri-state (`lean.h:121-141`): `> 0` single-threaded count,
/// `< 0` multi-threaded (atomic) count, `== 0` persistent (never counted).
/// Under the pin's `LEAN_MIMALLOC` build (`include/lean/config.h:10` in the
/// distributed toolchain), `m_cs_sz` of a live small-path object holds its
/// aligned allocation size and big-path objects store `0`.
#[repr(C)]
pub(crate) struct LeanObject {
    pub(crate) m_rc: i32,
    pub(crate) m_cs_sz: u16,
    pub(crate) m_other: u8,
    pub(crate) m_tag: u8,
}

/// `lean_ctor_object` — constructor objects (`lean.h:182-185`).
///
/// Field order law (G0-1 item 5): pointer fields first in declaration order,
/// then the scalar area starting at `m_objs + m_other`.
#[repr(C)]
pub(crate) struct LeanCtorObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_objs: [*mut LeanObject; 0],
}

/// `lean_array_object` (`lean.h:188-193`).
#[repr(C)]
pub(crate) struct LeanArrayObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_size: usize,
    pub(crate) m_capacity: usize,
    pub(crate) m_data: [*mut LeanObject; 0],
}

/// `lean_sarray_object` — scalar arrays (`lean.h:196-201`); element size
/// lives in the header's `m_other`.
#[repr(C)]
pub(crate) struct LeanSarrayObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_size: usize,
    pub(crate) m_capacity: usize,
    pub(crate) m_data: [u8; 0],
}

/// `lean_string_object` (`lean.h:203-209`): `m_size` = byte length INCLUDING
/// the `'\0'` terminator; `m_length` = UTF-8 codepoint count (G0-1 item 8).
#[repr(C)]
pub(crate) struct LeanStringObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_size: usize,
    pub(crate) m_capacity: usize,
    pub(crate) m_length: usize,
    pub(crate) m_data: [u8; 0],
}

/// `lean_closure_object` (`lean.h:211-217`).
#[repr(C)]
pub(crate) struct LeanClosureObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_fun: *mut c_void,
    pub(crate) m_arity: u16,
    pub(crate) m_num_fixed: u16,
    pub(crate) m_objs: [*mut LeanObject; 0],
}

/// `lean_ref_object` — `IO.Ref` cells (`lean.h:219-222`).
#[repr(C)]
pub(crate) struct LeanRefObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_value: *mut LeanObject,
}

/// `lean_thunk_object` (`lean.h:224-228`). Both fields are `_Atomic` in C;
/// `AtomicPtr<T>` has the same layout as `*mut T`. Either field may be
/// legally NULL (G0-1 item 10).
#[repr(C)]
pub(crate) struct LeanThunkObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_value: AtomicPtr<LeanObject>,
    pub(crate) m_closure: AtomicPtr<LeanObject>,
}

/// `lean_task_imp` — per-task execution data (`lean.h:234-243`), released
/// when the task terminates. Marrow never allocates one: only Finished
/// tasks (`m_imp == NULL`, `m_value != NULL`) are constructible — the
/// fln-3gv slice-2 state family answers for them and refuses typed on
/// `m_imp != NULL`; scheduled tasks arrive with the manager plane
/// (fln-3gv, next slice).
#[repr(C)]
pub(crate) struct LeanTaskImp {
    pub(crate) m_closure: *mut LeanObject,
    pub(crate) m_head_dep: *mut LeanTaskObject,
    pub(crate) m_next_dep: *mut LeanTaskObject,
    pub(crate) m_prio: u32,
    pub(crate) m_canceled: u8,
    pub(crate) m_keep_alive: u8,
    pub(crate) m_deleted: u8,
}

/// `lean_task_object` (`lean.h:296-300`).
#[repr(C)]
pub(crate) struct LeanTaskObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_value: AtomicPtr<LeanObject>,
    pub(crate) m_imp: *mut LeanTaskImp,
}

/// `lean_promise_object` (`lean.h:302-305`).
#[repr(C)]
pub(crate) struct LeanPromiseObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_result: *mut LeanTaskObject,
}

/// `lean_external_class` — finalize/foreach vtable (`lean.h:310-313`).
///
/// `m_foreach` receives a Lean *closure* to apply to each owned child; running
/// it requires the apply machinery (bead franken_lean-7xe), so slice-1 RC
/// traversals over external objects are restricted (see `rc.rs`).
#[repr(C)]
pub(crate) struct LeanExternalClass {
    pub(crate) m_finalize: unsafe extern "C" fn(*mut c_void),
    pub(crate) m_foreach: unsafe extern "C" fn(*mut c_void, *mut LeanObject),
}

/// `lean_external_object` (`lean.h:318-322`).
#[repr(C)]
pub(crate) struct LeanExternalObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_class: *mut LeanExternalClass,
    pub(crate) m_data: *mut c_void,
}

/// The pin's `mpz_object` view (`vendor/lean4-src/src/runtime/object.h:21-26`
/// via the GMP `mpz` it embeds; byte layout confirmed at Corpus scale by G0-1,
/// `tribunal/fixtures/c3/FINDINGS.md` item 9): `{ m_alloc: i32, m_size: i32,
/// m_limbs: *mut u64 }` after the header. Sign of the value is the sign of
/// `m_size`; `|m_size|` is the live limb count. Slice-1 Marrow owns the limb
/// buffer structurally (alloc/copy/free); arithmetic arrives with the
/// fln-bignum shim (Crucible workstream).
///
/// NOT part of the `lean.h` contract tables — `mpz_object` is private to the
/// upstream runtime — so this mirror is validated by the G0-1 resurrection
/// evidence rather than the generated `contract.rs` tables.
#[repr(C)]
pub(crate) struct LeanMpzObject {
    pub(crate) m_header: LeanObject,
    pub(crate) m_alloc: i32,
    pub(crate) m_size: i32,
    pub(crate) m_limbs: *mut u64,
}

// Static shape guards for the header itself; every other mirror is checked
// against the generated contract tables by the layout suite and against the
// real compiler by the C4 probes.
const _: () = assert!(size_of::<LeanObject>() == 8);
const _: () = assert!(align_of::<LeanObject>() == 4);
const _: () = assert!(size_of::<*mut LeanObject>() == 8);
const _: () = assert!(size_of::<AtomicPtr<LeanObject>>() == 8);
