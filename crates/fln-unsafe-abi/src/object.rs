//! Per-category CompatHeap constructors and accessors — the `lean.h` inline
//! twins (plan §6.1, bead fln-lld). Every function mirrors one upstream
//! `static inline` (cited per function); layout constants come from the
//! generated contract, never from memory.
//!
//! Ownership conventions follow the contract's `Ownership` classes: `alloc_*`
//! return an owned reference (`lean_obj_res`); getters return borrowed
//! pointers (`b_lean_obj_res`); setters consume the stored value
//! (`lean_obj_arg`) exactly as upstream.

use crate::contract::{
    MAX_CTOR_FIELDS, MAX_CTOR_SCALARS_SIZE, TAG_ARRAY, TAG_CLOSURE, TAG_EXTERNAL, TAG_MAX_CTOR_TAG,
    TAG_MPZ, TAG_REF, TAG_SCALAR_ARRAY, TAG_STRING, TAG_TASK, TAG_THUNK,
};
use crate::layout::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanMpzObject, LeanObject, LeanRefObject, LeanSarrayObject, LeanStringObject, LeanTaskObject,
    LeanThunkObject,
};
use crate::membrane;
use crate::rc::{self, init_st_header};
use core::ffi::c_void;
use core::sync::atomic::{AtomicPtr, Ordering};
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

// ---------------------------------------------------------------- ctor

/// `lean_alloc_ctor` (`lean.h:679-684`).
///
/// # Safety
/// Caller owns the result and must initialize all `num_objs` object slots
/// (and any scalar bytes it reads later) before sharing or releasing it.
// UNSAFE-LEDGER: FLN-UL-0005
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_ctor(tag: u8, num_objs: usize, scalar_sz: usize) -> *mut LeanObject {
    assert!(
        tag <= TAG_MAX_CTOR_TAG && num_objs < MAX_CTOR_FIELDS && scalar_sz < MAX_CTOR_SCALARS_SIZE
    );
    let sz = size_of::<LeanCtorObject>() + size_of::<*mut LeanObject>() * num_objs + scalar_sz;
    // SAFETY: sz is bounded by the contract maxima (< 8 + 256*8 + 1024), well
    // inside the small-object range; header initialized before return.
    let o = unsafe { membrane::alloc_ctor_memory(sz) };
    // SAFETY: this is the "header initialized before return" the note above
    // promises. `alloc_ctor_memory` diverges through `handle_alloc_error` on
    // exhaustion rather than returning null, so `o` is a live, exclusively
    // owned block of at least `sz` bytes and the header write is in bounds.
    unsafe { init_st_header(o, tag, num_objs as u8) };
    membrane::note_alloc(o, membrane::align_obj_size(sz), tag);
    o
}

/// `lean_ctor_obj_cptr` (`lean.h:669-672`): base of the object-slot area.
///
/// # Safety
/// `o` must be a live ctor object minted by the membrane.
// UNSAFE-LEDGER: FLN-UL-0006
#[allow(unsafe_code)]
pub(crate) unsafe fn ctor_obj_cptr(o: *mut LeanObject) -> *mut *mut LeanObject {
    // SAFETY: repr(C) mirror places m_objs immediately after the header,
    // matching the contract's flexible-array offset.
    unsafe { (&raw mut (*o.cast::<LeanCtorObject>()).m_objs).cast::<*mut LeanObject>() }
}

/// `lean_ctor_get` (`lean.h:686-689`); borrowed result.
///
/// # Safety
/// `o` live ctor object; `i < m_other` (asserted in debug like upstream).
// UNSAFE-LEDGER: FLN-UL-0007
#[allow(unsafe_code)]
pub(crate) unsafe fn ctor_get(o: *mut LeanObject, i: usize) -> *mut LeanObject {
    // SAFETY: bound asserted against the header's field count exactly as the
    // upstream assert; slot i is within the allocation.
    unsafe {
        debug_assert!(i < usize::from((&raw const (*o).m_other).read()));
        ctor_obj_cptr(o).add(i).read()
    }
}

/// `lean_ctor_set` (`lean.h:703-706`); consumes `v`.
///
/// # Safety
/// As [`ctor_get`]; `v` must be a valid object pointer or boxed scalar whose
/// reference the slot now owns.
// UNSAFE-LEDGER: FLN-UL-0008
#[allow(unsafe_code)]
pub(crate) unsafe fn ctor_set(o: *mut LeanObject, i: usize, v: *mut LeanObject) {
    // SAFETY: as ctor_get; plain slot write mirrors the upstream inline.
    unsafe {
        debug_assert!(i < usize::from((&raw const (*o).m_other).read()));
        ctor_obj_cptr(o).add(i).write(v);
    }
}

/// `lean_ctor_set_tag` (`lean.h:708-711`).
///
/// # Safety
/// `o` live ctor object; `new_tag <= TAG_MAX_CTOR_TAG` (asserted).
// UNSAFE-LEDGER: FLN-UL-0009
#[allow(unsafe_code)]
pub(crate) unsafe fn ctor_set_tag(o: *mut LeanObject, new_tag: u8) {
    assert!(new_tag <= TAG_MAX_CTOR_TAG);
    // SAFETY: header write on a live object; tag stays in the ctor range.
    unsafe { (&raw mut (*o).m_tag).write(new_tag) };
}

/// Scalar-area byte pointer: `lean_ctor_scalar_cptr` (`lean.h:674-677`).
/// The G0-1 packing law: scalars live after all `m_other` object slots.
///
/// # Safety
/// `o` live ctor object.
// UNSAFE-LEDGER: FLN-UL-0010
#[allow(unsafe_code)]
pub(crate) unsafe fn ctor_scalar_cptr(o: *mut LeanObject) -> *mut u8 {
    // SAFETY: scalar area begins exactly after the object slots, per the
    // contract layout and the upstream inline.
    unsafe {
        let n = usize::from((&raw const (*o).m_other).read());
        ctor_obj_cptr(o).add(n).cast::<u8>()
    }
}

/// `lean_ctor_get_uint8/16/32/64/usize/float/float32` family
/// (`lean.h:724-757`): read a scalar at `offset` bytes from the object-slot
/// base (usize variants index in words upstream; callers pass byte offsets
/// here and the handle layer preserves upstream's indexing conventions).
///
/// # Safety
/// `o` live ctor object; `offset >= m_other * 8` (upstream's assert) and
/// `offset + size_of::<T>()` within the allocated scalar area; the scalar
/// bytes must have been initialized.
// UNSAFE-LEDGER: FLN-UL-0011
#[allow(unsafe_code)]
pub(crate) unsafe fn ctor_get_scalar<T: Copy>(o: *mut LeanObject, offset: usize) -> T {
    // SAFETY: caller upholds the upstream bound; unaligned read because the
    // scalar area is byte-packed by the compiler's packing rules.
    unsafe {
        debug_assert!(
            offset >= usize::from((&raw const (*o).m_other).read()) * size_of::<*mut LeanObject>()
        );
        ctor_obj_cptr(o)
            .cast::<u8>()
            .add(offset)
            .cast::<T>()
            .read_unaligned()
    }
}

/// `lean_ctor_set_uint8/…` family (`lean.h:759-792`); see [`ctor_get_scalar`].
///
/// # Safety
/// As [`ctor_get_scalar`].
// UNSAFE-LEDGER: FLN-UL-0012
#[allow(unsafe_code)]
pub(crate) unsafe fn ctor_set_scalar<T: Copy>(o: *mut LeanObject, offset: usize, v: T) {
    // SAFETY: as ctor_get_scalar.
    unsafe {
        debug_assert!(
            offset >= usize::from((&raw const (*o).m_other).read()) * size_of::<*mut LeanObject>()
        );
        ctor_obj_cptr(o)
            .cast::<u8>()
            .add(offset)
            .cast::<T>()
            .write_unaligned(v);
    }
}

// ---------------------------------------------------------------- array

/// `lean_alloc_array` (`lean.h:848-854`): big path, `m_cs_sz = 0`.
///
/// # Safety
/// Caller owns the result and must initialize slots `0..size` before they
/// are read or the object is released.
// UNSAFE-LEDGER: FLN-UL-0013
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_array(size: usize, capacity: usize) -> *mut LeanObject {
    let bytes = size_of::<LeanArrayObject>()
        .checked_add(
            size_of::<*mut LeanObject>()
                .checked_mul(capacity)
                .expect("array capacity overflow"),
        )
        .expect("array size overflow");
    // SAFETY: overflow-checked size; header + salient fields initialized
    // before return.
    let o = unsafe { membrane::alloc_big(bytes) };
    // SAFETY: the "header + salient fields initialized before return" the note
    // above defers to. `alloc_big` diverges through `handle_alloc_error` on
    // exhaustion rather than returning null, so `o` is a live, exclusively
    // owned block of `bytes`, and every write below lies inside it.
    unsafe {
        init_st_header(o, TAG_ARRAY, 0);
        let a = o.cast::<LeanArrayObject>();
        (&raw mut (*a).m_size).write(size);
        (&raw mut (*a).m_capacity).write(capacity);
    }
    membrane::note_alloc(o, bytes, TAG_ARRAY);
    o
}

/// Array salient fields `(m_size, m_capacity)` (`lean.h:855-856`).
///
/// # Safety
/// `o` live array object.
// UNSAFE-LEDGER: FLN-UL-0014
#[allow(unsafe_code)]
pub(crate) unsafe fn array_fields(o: *mut LeanObject) -> (usize, usize) {
    // SAFETY: live array object per caller contract.
    unsafe {
        let a = o.cast::<LeanArrayObject>();
        (
            (&raw const (*a).m_size).read(),
            (&raw const (*a).m_capacity).read(),
        )
    }
}

/// `lean_array_cptr` + indexed read (`lean.h:863`, `870-872`); borrowed.
///
/// # Safety
/// `o` live array; `i < m_size`; slot initialized.
// UNSAFE-LEDGER: FLN-UL-0015
#[allow(unsafe_code)]
pub(crate) unsafe fn array_get(o: *mut LeanObject, i: usize) -> *mut LeanObject {
    // SAFETY: bound asserted like upstream; data follows the fixed fields.
    unsafe {
        debug_assert!(i < array_fields(o).0);
        (&raw mut (*o.cast::<LeanArrayObject>()).m_data)
            .cast::<*mut LeanObject>()
            .add(i)
            .read()
    }
}

/// Slot initialization write (the `lean_array_set_core` shape); consumes `v`.
///
/// # Safety
/// `o` live array; `i < m_capacity`; overwritten slot must not own a
/// reference (initialization discipline, as upstream's uses).
// UNSAFE-LEDGER: FLN-UL-0016
#[allow(unsafe_code)]
pub(crate) unsafe fn array_set_core(o: *mut LeanObject, i: usize, v: *mut LeanObject) {
    // SAFETY: bound asserted against capacity; plain slot write.
    unsafe {
        debug_assert!(i < array_fields(o).1);
        (&raw mut (*o.cast::<LeanArrayObject>()).m_data)
            .cast::<*mut LeanObject>()
            .add(i)
            .write(v);
    }
}

// ---------------------------------------------------------------- sarray

/// `lean_alloc_sarray` (`lean.h:1036-1042`): big path; element size in
/// `m_other`.
///
/// # Safety
/// Caller owns the result; data bytes `0..elem_size*size` must be
/// initialized before they are read.
// UNSAFE-LEDGER: FLN-UL-0017
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_sarray(elem_size: u8, size: usize, capacity: usize) -> *mut LeanObject {
    let bytes = size_of::<LeanSarrayObject>()
        .checked_add(
            usize::from(elem_size)
                .checked_mul(capacity)
                .expect("sarray capacity overflow"),
        )
        .expect("sarray size overflow");
    // SAFETY: overflow-checked; header + salient fields initialized here.
    let o = unsafe { membrane::alloc_big(bytes) };
    // SAFETY: the "header + salient fields initialized here" the note above
    // defers to. `alloc_big` diverges through `handle_alloc_error` rather than
    // returning null, so `o` is a live, exclusively owned block of `bytes`,
    // and every write below lies inside it.
    unsafe {
        init_st_header(o, TAG_SCALAR_ARRAY, elem_size);
        let a = o.cast::<LeanSarrayObject>();
        (&raw mut (*a).m_size).write(size);
        (&raw mut (*a).m_capacity).write(capacity);
    }
    membrane::note_alloc(o, bytes, TAG_SCALAR_ARRAY);
    o
}

/// Sarray salient fields `(elem_size, m_size, m_capacity)` and data base
/// (`lean.h:1043-1060`).
///
/// # Safety
/// `o` live scalar array.
// UNSAFE-LEDGER: FLN-UL-0018
#[allow(unsafe_code)]
pub(crate) unsafe fn sarray_fields(o: *mut LeanObject) -> (u8, usize, usize, *mut u8) {
    // SAFETY: live sarray per caller contract.
    unsafe {
        let a = o.cast::<LeanSarrayObject>();
        (
            (&raw const (*o).m_other).read(),
            (&raw const (*a).m_size).read(),
            (&raw const (*a).m_capacity).read(),
            (&raw mut (*a).m_data).cast::<u8>(),
        )
    }
}

// ---------------------------------------------------------------- string

/// `lean_mk_string_unchecked` (`object.cpp` at the pin): allocates
/// `size = capacity = bytes + 1`, copies, NUL-terminates. `len` is the UTF-8
/// codepoint count the caller vouches for.
///
/// # Safety
/// Caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0019
#[allow(unsafe_code)]
pub(crate) unsafe fn mk_string_unchecked(bytes: &[u8], len: usize) -> *mut LeanObject {
    let rsz = bytes.len().checked_add(1).expect("string size overflow");
    let total = size_of::<LeanStringObject>()
        .checked_add(rsz)
        .expect("string size overflow");
    // SAFETY: overflow-checked; all salient bytes (data + NUL) written below.
    let o = unsafe { membrane::alloc_big(total) };
    // SAFETY: the "all salient bytes (data + NUL) written below" the note above
    // defers to. `alloc_big` diverges through `handle_alloc_error` rather than
    // returning null, so `o` is a live, exclusively owned block of `total`
    // bytes, and every write below lies inside it.
    unsafe {
        init_st_header(o, TAG_STRING, 0);
        let s = o.cast::<LeanStringObject>();
        (&raw mut (*s).m_size).write(rsz);
        (&raw mut (*s).m_capacity).write(rsz);
        (&raw mut (*s).m_length).write(len);
        let data = (&raw mut (*s).m_data).cast::<u8>();
        core::ptr::copy_nonoverlapping(bytes.as_ptr(), data, bytes.len());
        data.add(bytes.len()).write(0);
    }
    membrane::note_alloc(o, total, TAG_STRING);
    o
}

/// `alloc_string` with an explicit capacity (`object.cpp` at the pin): the
/// data area beyond the fields is salient only up to what the caller writes;
/// header/size/capacity/length are set here.
///
/// # Safety
/// Caller owns the result and must write `size` data bytes (including the
/// terminating NUL) before the object is read as a string.
// UNSAFE-LEDGER: FLN-UL-0182
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_string_cap(size: usize, capacity: usize, len: usize) -> *mut LeanObject {
    let total = size_of::<LeanStringObject>()
        .checked_add(capacity)
        .expect("string capacity overflow");
    // SAFETY: overflow-checked; fields written below; data bytes are the
    // caller's declared obligation per the doc contract.
    let o = unsafe { membrane::alloc_big(total) };
    // SAFETY: `alloc_big` diverges rather than returning null, so `o` is a
    // live exclusively owned block of `total` bytes; every field write below
    // lies inside it.
    unsafe {
        init_st_header(o, TAG_STRING, 0);
        let s = o.cast::<LeanStringObject>();
        (&raw mut (*s).m_size).write(size);
        (&raw mut (*s).m_capacity).write(capacity);
        (&raw mut (*s).m_length).write(len);
    }
    membrane::note_alloc(o, total, TAG_STRING);
    o
}

/// `lean_string_append`'s object-model core (`object.cpp:2084-2105`), ported
/// arm-for-arm. `exclusive` is the caller's `lean_is_exclusive(s1)` verdict:
/// the SHARED arm allocates fresh at `mk_capacity(new_sz) == 2 * new_sz` and
/// `dec_ref`s `s1`; the EXCLUSIVE arm reuses `s1` in place when capacity
/// suffices and otherwise reallocates at `cap + sz1 + (sz2 - 1)` with a raw
/// dealloc of the old block (`string_ensure_capacity`, `object.cpp:1966`).
/// `s2` is borrowed and never consumed, exactly as the `b_lean_obj_arg`
/// signature states.
///
/// # Safety
/// `s1` and `s2` live string objects; `s1` owned by the caller (consumed in
/// every arm), `s2` borrowed; `exclusive` truthful for `s1`.
// UNSAFE-LEDGER: FLN-UL-0183
#[allow(unsafe_code)]
pub(crate) unsafe fn string_append_core(
    s1: *mut LeanObject,
    s2: *mut LeanObject,
    exclusive: bool,
) -> *mut LeanObject {
    // SAFETY: live strings per the contract; every read/write below is within
    // the objects' declared salient bytes, and each arm settles s1's
    // ownership exactly as annotated.
    unsafe {
        let a = s1.cast::<LeanStringObject>();
        let b = s2.cast::<LeanStringObject>();
        let sz1 = (&raw const (*a).m_size).read();
        let sz2 = (&raw const (*b).m_size).read();
        let len1 = (&raw const (*a).m_length).read();
        let len2 = (&raw const (*b).m_length).read();
        let new_len = len1.checked_add(len2).expect("string length overflow");
        let new_sz = sz1
            .checked_add(sz2)
            .and_then(|s| s.checked_sub(1))
            .expect("string size overflow");
        let r = if !exclusive {
            let cap = new_sz.checked_mul(2).expect("capacity overflow");
            let r = alloc_string_cap(new_sz, cap, new_len);
            let dst = (&raw mut (*r.cast::<LeanStringObject>()).m_data).cast::<u8>();
            let src = (&raw const (*a).m_data).cast::<u8>();
            core::ptr::copy_nonoverlapping(src, dst, sz1 - 1);
            crate::rc::dec_ref(s1);
            r
        } else {
            let cap = (&raw const (*a).m_capacity).read();
            let extra = sz2 - 1;
            if sz1 + extra > cap {
                let grown_cap = cap
                    .checked_add(sz1)
                    .and_then(|c| c.checked_add(extra))
                    .expect("capacity overflow");
                let r = alloc_string_cap(sz1, grown_cap, len1);
                let dst = (&raw mut (*r.cast::<LeanStringObject>()).m_data).cast::<u8>();
                let src = (&raw const (*a).m_data).cast::<u8>();
                core::ptr::copy_nonoverlapping(src, dst, sz1);
                let old_bytes = size_of::<LeanStringObject>() + cap;
                membrane::release_with_size(s1, old_bytes, "object.string_append.grow");
                r
            } else {
                s1
            }
        };
        let rs = r.cast::<LeanStringObject>();
        let dst = (&raw mut (*rs).m_data).cast::<u8>();
        let src2 = (&raw const (*b).m_data).cast::<u8>();
        core::ptr::copy_nonoverlapping(src2, dst.add(sz1 - 1), sz2 - 1);
        (&raw mut (*rs).m_size).write(new_sz);
        (&raw mut (*rs).m_length).write(new_len);
        dst.add(new_sz - 1).write(0);
        r
    }
}

/// String salient fields `(m_size, m_capacity, m_length)` plus a copy of the
/// data bytes including the NUL (`lean.h:1208-1223` accessor family).
///
/// # Safety
/// `o` live string object.
// UNSAFE-LEDGER: FLN-UL-0020
#[allow(unsafe_code)]
pub(crate) unsafe fn string_fields(o: *mut LeanObject) -> (usize, usize, usize, Vec<u8>) {
    // SAFETY: live string; m_size bytes of data are salient by the string law.
    unsafe {
        let s = o.cast::<LeanStringObject>();
        let size = (&raw const (*s).m_size).read();
        let cap = (&raw const (*s).m_capacity).read();
        let len = (&raw const (*s).m_length).read();
        let data = (&raw const (*s).m_data).cast::<u8>();
        let copy = core::slice::from_raw_parts(data, size).to_vec();
        (size, cap, len, copy)
    }
}

// ---------------------------------------------------------------- closure

/// `lean_alloc_closure` (`lean.h:800-809`): big path.
///
/// # Safety
/// Caller owns the result and must initialize all `num_fixed` slots.
/// `arity > 0 && num_fixed < arity` asserted as upstream.
// UNSAFE-LEDGER: FLN-UL-0021
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_closure(
    fun: *mut c_void,
    arity: u16,
    num_fixed: u16,
) -> *mut LeanObject {
    assert!(arity > 0 && num_fixed < arity);
    let bytes =
        size_of::<LeanClosureObject>() + size_of::<*mut LeanObject>() * usize::from(num_fixed);
    // SAFETY: bounded by CLOSURE_MAX_ARGS * 8 + fixed part; fields set below.
    let o = unsafe { membrane::alloc_big(bytes) };
    // SAFETY: the "fields set below" the note above defers to. `alloc_big`
    // diverges through `handle_alloc_error` rather than returning null, so `o`
    // is a live, exclusively owned block of `bytes`, and every write below lies
    // inside it.
    unsafe {
        init_st_header(o, TAG_CLOSURE, 0);
        let c = o.cast::<LeanClosureObject>();
        (&raw mut (*c).m_fun).write(fun);
        (&raw mut (*c).m_arity).write(arity);
        (&raw mut (*c).m_num_fixed).write(num_fixed);
    }
    membrane::note_alloc(o, bytes, TAG_CLOSURE);
    o
}

/// Closure salient fields `(m_fun, m_arity, m_num_fixed, args base)`
/// (`lean.h:796-799`).
///
/// # Safety
/// `o` live closure object.
// UNSAFE-LEDGER: FLN-UL-0022
#[allow(unsafe_code)]
pub(crate) unsafe fn closure_fields(
    o: *mut LeanObject,
) -> (*mut c_void, u16, u16, *mut *mut LeanObject) {
    // SAFETY: live closure per caller contract.
    unsafe {
        let c = o.cast::<LeanClosureObject>();
        (
            (&raw const (*c).m_fun).read(),
            (&raw const (*c).m_arity).read(),
            (&raw const (*c).m_num_fixed).read(),
            (&raw mut (*c).m_objs).cast::<*mut LeanObject>(),
        )
    }
}

/// `lean_closure_set` (`lean.h:814-817`); consumes `a`.
///
/// # Safety
/// `o` live closure; `i < m_num_fixed`; initialization write.
// UNSAFE-LEDGER: FLN-UL-0023
#[allow(unsafe_code)]
pub(crate) unsafe fn closure_set(o: *mut LeanObject, i: usize, a: *mut LeanObject) {
    // SAFETY: bound asserted like upstream.
    unsafe {
        let (_, _, num_fixed, args) = closure_fields(o);
        debug_assert!(i < usize::from(num_fixed));
        args.add(i).write(a);
    }
}

// ---------------------------------------------------------------- ref / thunk / task

/// `lean_alloc_ref`-shape (`lean_st_mk_ref` runtime path): small object
/// holding one owned value (nullable during teardown only).
///
/// # Safety
/// Caller owns the result; `value` reference is consumed.
// UNSAFE-LEDGER: FLN-UL-0024
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_ref(value: *mut LeanObject) -> *mut LeanObject {
    let sz = size_of::<LeanRefObject>();
    // SAFETY: fixed small size; fields set below.
    let o = unsafe { membrane::alloc_small(sz) };
    // SAFETY: the "fields set below" the note above defers to. `alloc_small`
    // diverges through `handle_alloc_error` rather than returning null, so `o`
    // is a live, exclusively owned block of `sz` bytes, and every write below
    // lies inside it.
    unsafe {
        init_st_header(o, TAG_REF, 0);
        (&raw mut (*o.cast::<LeanRefObject>()).m_value).write(value);
    }
    membrane::note_alloc(o, membrane::align_obj_size(sz), TAG_REF);
    o
}

/// Ref value slot (borrowed read).
///
/// # Safety
/// `o` live ref object.
// UNSAFE-LEDGER: FLN-UL-0025
#[allow(unsafe_code)]
pub(crate) unsafe fn ref_value(o: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live ref per caller contract.
    unsafe { (&raw const (*o.cast::<LeanRefObject>()).m_value).read() }
}

/// Owned `lean_st_ref_get` result. The MT/persistent arm temporarily claims
/// the cell's RC token before retaining it, exactly as the pinned runtime.
///
/// # Safety
/// `o` live ref object whose cell is non-null.
// UNSAFE-LEDGER: FLN-UL-0193
#[allow(unsafe_code)]
pub(crate) unsafe fn ref_get_owned(o: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live ref per caller contract. A non-positive header count selects
    // the atomic cell protocol; a positive count carries ST exclusivity.
    unsafe {
        if rc::read_header(o).rc <= 0 {
            let slot = AtomicPtr::from_ptr(&raw mut (*o.cast::<LeanRefObject>()).m_value);
            loop {
                let value = slot.swap(core::ptr::null_mut(), Ordering::SeqCst);
                if value.is_null() {
                    continue;
                }
                if !crate::tagged::is_scalar(value) {
                    rc::inc_ref_n(value, 1);
                }
                let displaced = slot.swap(value, Ordering::SeqCst);
                if !displaced.is_null() && !crate::tagged::is_scalar(displaced) {
                    rc::dec_ref(displaced);
                }
                return value;
            }
        }

        let value = (&raw const (*o.cast::<LeanRefObject>()).m_value).read();
        assert!(!value.is_null(), "null reference read");
        if !crate::tagged::is_scalar(value) {
            rc::inc_ref_n(value, 1);
        }
        value
    }
}

/// `lean_st_ref_take`: transfer the cell's owned value to the caller and
/// leave the slot null until a later set. The MT/persistent arm retries a
/// transient null exactly as the pinned runtime.
///
/// # Safety
/// `o` live ref object whose cell is non-null.
// UNSAFE-LEDGER: FLN-UL-0199
#[allow(unsafe_code)]
pub(crate) unsafe fn ref_take(o: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live ref per caller contract. A shared ref uses the pinned
    // atomic exchange loop; an ST-exclusive ref transfers its slot directly.
    unsafe {
        if rc::read_header(o).rc <= 0 {
            let slot = AtomicPtr::from_ptr(&raw mut (*o.cast::<LeanRefObject>()).m_value);
            loop {
                let value = slot.swap(core::ptr::null_mut(), Ordering::SeqCst);
                if !value.is_null() {
                    return value;
                }
            }
        }

        let slot = &raw mut (*o.cast::<LeanRefObject>()).m_value;
        let value = slot.read();
        assert!(!value.is_null(), "null reference take");
        slot.write(core::ptr::null_mut());
        value
    }
}

/// `lean_st_ref_set`: consume `value`, replace the cell, release any old
/// occupant, and preserve the Reference's MT reachability invariant.
///
/// # Safety
/// `o` live ref object; `value` is one owned ABI reference.
// UNSAFE-LEDGER: FLN-UL-0194
#[allow(unsafe_code)]
pub(crate) unsafe fn ref_set(o: *mut LeanObject, value: *mut LeanObject) {
    // SAFETY: live ref and owned value per caller contract. A shared ref uses
    // the atomic slot and requires every reachable heap object to be MT.
    unsafe {
        let old = if rc::read_header(o).rc <= 0 {
            if !crate::tagged::is_scalar(value) {
                rc::mark_mt(value);
            }
            AtomicPtr::from_ptr(&raw mut (*o.cast::<LeanRefObject>()).m_value)
                .swap(value, Ordering::SeqCst)
        } else {
            let slot = &raw mut (*o.cast::<LeanRefObject>()).m_value;
            let old = slot.read();
            slot.write(value);
            old
        };
        if !old.is_null() && !crate::tagged::is_scalar(old) {
            rc::dec_ref(old);
        }
    }
}

/// `lean_st_ref_swap`: consume `value` and return the previous owned cell
/// value. The transient-null retry matches the pinned MT protocol.
///
/// # Safety
/// `o` live ref object; `value` is one owned ABI reference.
// UNSAFE-LEDGER: FLN-UL-0195
#[allow(unsafe_code)]
pub(crate) unsafe fn ref_swap(o: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live ref and owned value per caller contract. Shared cells use
    // the same exchange loop as runtime/io.cpp.
    unsafe {
        if rc::read_header(o).rc <= 0 {
            if !crate::tagged::is_scalar(value) {
                rc::mark_mt(value);
            }
            let slot = AtomicPtr::from_ptr(&raw mut (*o.cast::<LeanRefObject>()).m_value);
            loop {
                let old = slot.swap(value, Ordering::SeqCst);
                if !old.is_null() {
                    return old;
                }
            }
        }

        let slot = &raw mut (*o.cast::<LeanRefObject>()).m_value;
        let old = slot.read();
        assert!(!old.is_null(), "null reference read");
        slot.write(value);
        old
    }
}

/// Evaluated-thunk constructor (`lean_thunk_pure` shape, `lean.h` thunk
/// family): `m_value = v`, `m_closure = NULL`. Both fields legally nullable
/// (G0-1 item 10); forcing unevaluated thunks needs the apply machinery
/// (bead franken_lean-7xe).
///
/// # Safety
/// Caller owns the result; `v` reference is consumed.
// UNSAFE-LEDGER: FLN-UL-0026
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_thunk_value(v: *mut LeanObject) -> *mut LeanObject {
    let sz = size_of::<LeanThunkObject>();
    // SAFETY: fixed small size; fields set below.
    let o = unsafe { membrane::alloc_small(sz) };
    // SAFETY: the "fields set below" the note above defers to. `alloc_small`
    // diverges through `handle_alloc_error` rather than returning null, so `o`
    // is a live, exclusively owned block of `sz` bytes, and every write below
    // lies inside it.
    unsafe {
        init_st_header(o, TAG_THUNK, 0);
        let t = o.cast::<LeanThunkObject>();
        (&raw mut (*t).m_value).write(AtomicPtr::new(v));
        (&raw mut (*t).m_closure).write(AtomicPtr::new(core::ptr::null_mut()));
    }
    membrane::note_alloc(o, membrane::align_obj_size(sz), TAG_THUNK);
    o
}

/// Delayed-thunk constructor (`lean_mk_thunk`): `m_value = NULL` and
/// `m_closure = closure`.
///
/// # Safety
/// Caller owns the result; `closure` reference is consumed.
// UNSAFE-LEDGER: FLN-UL-0196
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_thunk_closure(closure: *mut LeanObject) -> *mut LeanObject {
    let sz = size_of::<LeanThunkObject>();
    // SAFETY: fixed small size; every field is initialized before publication.
    let o = unsafe { membrane::alloc_small(sz) };
    // SAFETY: fresh exclusively owned block of at least sz bytes.
    unsafe {
        init_st_header(o, TAG_THUNK, 0);
        let thunk = o.cast::<LeanThunkObject>();
        (&raw mut (*thunk).m_value).write(AtomicPtr::new(core::ptr::null_mut()));
        (&raw mut (*thunk).m_closure).write(AtomicPtr::new(closure));
    }
    membrane::note_alloc(o, membrane::align_obj_size(sz), TAG_THUNK);
    o
}

/// Finished-task constructor (`Task.pure` state machine entry,
/// `lean.h:250-295`): `m_value = v`, `m_imp = NULL`. Live scheduled tasks
/// arrive with the asupersync effects bead (fln-3gv).
///
/// # Safety
/// Caller owns the result; `v` reference is consumed.
// UNSAFE-LEDGER: FLN-UL-0027
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_task_pure(v: *mut LeanObject) -> *mut LeanObject {
    let sz = size_of::<LeanTaskObject>();
    // SAFETY: fixed small size; fields set below.
    let o = unsafe { membrane::alloc_small(sz) };
    // SAFETY: the "fields set below" the note above defers to. `alloc_small`
    // diverges through `handle_alloc_error` rather than returning null, so `o`
    // is a live, exclusively owned block of `sz` bytes, and every write below
    // lies inside it.
    unsafe {
        init_st_header(o, TAG_TASK, 0);
        let t = o.cast::<LeanTaskObject>();
        (&raw mut (*t).m_value).write(AtomicPtr::new(v));
        (&raw mut (*t).m_imp).write(core::ptr::null_mut());
    }
    membrane::note_alloc(o, membrane::align_obj_size(sz), TAG_TASK);
    o
}

/// Task salient fields `(m_value, m_imp)`.
///
/// # Safety
/// `o` live task object.
// UNSAFE-LEDGER: FLN-UL-0028
#[allow(unsafe_code)]
pub(crate) unsafe fn task_fields(
    o: *mut LeanObject,
) -> (*mut LeanObject, *mut crate::layout::LeanTaskImp) {
    // SAFETY: live task per caller contract; relaxed load mirrors the
    // C `_Atomic` default read for our single-owner teardown uses.
    unsafe {
        let t = o.cast::<LeanTaskObject>();
        (
            (*t).m_value.load(core::sync::atomic::Ordering::Acquire),
            (&raw const (*t).m_imp).read(),
        )
    }
}

/// Thunk salient fields `(m_value, m_closure)`.
///
/// # Safety
/// `o` live thunk object.
// UNSAFE-LEDGER: FLN-UL-0029
#[allow(unsafe_code)]
pub(crate) unsafe fn thunk_fields(o: *mut LeanObject) -> (*mut LeanObject, *mut LeanObject) {
    // SAFETY: live thunk per caller contract.
    unsafe {
        let t = o.cast::<LeanThunkObject>();
        (
            (*t).m_value.load(core::sync::atomic::Ordering::Acquire),
            (*t).m_closure.load(core::sync::atomic::Ordering::Acquire),
        )
    }
}

/// Claim an unevaluated thunk's owned closure exactly once.
///
/// # Safety
/// `o` live thunk object.
// UNSAFE-LEDGER: FLN-UL-0197
#[allow(unsafe_code)]
pub(crate) unsafe fn thunk_take_closure(o: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live thunk per caller contract; AcqRel transfers the stored
    // closure's ownership token to the successful claimant.
    unsafe {
        (*o.cast::<LeanThunkObject>())
            .m_closure
            .swap(core::ptr::null_mut(), Ordering::AcqRel)
    }
}

/// Complete a claimed thunk by installing one owned value if its value slot is
/// still empty. Returns false without consuming `value` if another value won.
///
/// # Safety
/// `o` live thunk object; `value` is one owned ABI reference.
// UNSAFE-LEDGER: FLN-UL-0198
#[allow(unsafe_code)]
pub(crate) unsafe fn thunk_try_set_value(o: *mut LeanObject, value: *mut LeanObject) -> bool {
    // SAFETY: live thunk per caller contract. A non-null closure means no
    // claimant owns the computation yet, so completion must refuse.
    unsafe {
        let thunk = o.cast::<LeanThunkObject>();
        if !(*thunk).m_closure.load(Ordering::Acquire).is_null() {
            return false;
        }
        (*thunk)
            .m_value
            .compare_exchange(
                core::ptr::null_mut(),
                value,
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_ok()
    }
}

// ---------------------------------------------------------------- external

/// `lean_register_external_class` (`lean.h:315`): classes are immortal
/// registrations, exactly as upstream (which heap-allocates and never frees).
pub(crate) fn register_external_class(
    finalize: unsafe extern "C" fn(*mut c_void),
    foreach: unsafe extern "C" fn(*mut c_void, *mut LeanObject),
) -> *mut LeanExternalClass {
    Box::into_raw(Box::new(LeanExternalClass {
        m_finalize: finalize,
        m_foreach: foreach,
    }))
}

/// `lean_alloc_external` (`lean.h` external family): small object.
///
/// # Safety
/// Caller owns the result; `class` must be a registered class pointer that
/// outlives every object of it; `data`'s ownership transfers to the object
/// (released via `m_finalize`).
// UNSAFE-LEDGER: FLN-UL-0030
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    let sz = size_of::<LeanExternalObject>();
    // SAFETY: fixed small size; fields set below.
    let o = unsafe { membrane::alloc_small(sz) };
    // SAFETY: the "fields set below" the note above defers to. `alloc_small`
    // diverges through `handle_alloc_error` rather than returning null, so `o`
    // is a live, exclusively owned block of `sz` bytes, and every write below
    // lies inside it. `class` and `data` are stored verbatim; their validity is
    // the caller's obligation, recorded in this function's `# Safety` clause.
    unsafe {
        init_st_header(o, TAG_EXTERNAL, 0);
        let e = o.cast::<LeanExternalObject>();
        (&raw mut (*e).m_class).write(class);
        (&raw mut (*e).m_data).write(data);
    }
    membrane::note_alloc(o, membrane::align_obj_size(sz), TAG_EXTERNAL);
    o
}

/// External salient fields `(m_class, m_data)`.
///
/// # Safety
/// `o` live external object.
// UNSAFE-LEDGER: FLN-UL-0031
#[allow(unsafe_code)]
pub(crate) unsafe fn external_fields(o: *mut LeanObject) -> (*mut LeanExternalClass, *mut c_void) {
    // SAFETY: live external per caller contract.
    unsafe {
        let e = o.cast::<LeanExternalObject>();
        (
            (&raw const (*e).m_class).read(),
            (&raw const (*e).m_data).read(),
        )
    }
}

// ---------------------------------------------------------------- mpz

fn limb_layout(count: usize) -> Layout {
    Layout::array::<u64>(count).expect("mpz limb buffer overflows Layout")
}

/// Structural bignum constructor: the pin's `mpz_object` byte layout
/// (G0-1 item 9) with a Marrow-owned limb buffer. `m_alloc` = allocated limb
/// count, `m_size` = signed live limb count. Arithmetic arrives with the
/// fln-bignum shim; this slice owns allocation, view, and teardown.
///
/// # Safety
/// Caller owns the result. Redundant high zero limbs are trimmed before
/// allocation, and a zero magnitude cannot retain a negative sign.
// UNSAFE-LEDGER: FLN-UL-0032
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_mpz(limbs: &[u64], negative: bool) -> *mut LeanObject {
    let live = limbs
        .iter()
        .rposition(|limb| *limb != 0)
        .map_or(0, |index| index + 1);
    let limbs = &limbs[..live];
    let n = limbs.len();
    assert!(i32::try_from(n).is_ok(), "mpz limb count exceeds i32");
    let buf = if n == 0 {
        core::ptr::null_mut()
    } else {
        // SAFETY: n > 0 checked; buffer fully initialized by the copy.
        let p = unsafe { alloc(limb_layout(n)) }.cast::<u64>();
        if p.is_null() {
            handle_alloc_error(limb_layout(n));
        }
        // SAFETY: the "buffer fully initialized by the copy" the note above
        // promises. `p` is non-null (null aborts two lines up) and was laid out
        // for exactly `n` u64s, `limbs` holds `n` initialized u64s, and a fresh
        // allocation cannot overlap the caller's slice.
        unsafe { core::ptr::copy_nonoverlapping(limbs.as_ptr(), p, n) };
        p
    };
    let sz = size_of::<LeanMpzObject>();
    // SAFETY: fixed small size; fields set below.
    let o = unsafe { membrane::alloc_small(sz) };
    // SAFETY: the "fields set below" the note above defers to. `alloc_small`
    // diverges through `handle_alloc_error` rather than returning null, so `o`
    // is a live, exclusively owned block of `sz` bytes, and every write below
    // lies inside it. `buf` is either null (n == 0) or the limb buffer this
    // function allocated and fully initialized above; the object owns it now.
    unsafe {
        init_st_header(o, TAG_MPZ, 0);
        let m = o.cast::<LeanMpzObject>();
        (&raw mut (*m).m_alloc).write(n as i32);
        (&raw mut (*m).m_size).write(if negative { -(n as i32) } else { n as i32 });
        (&raw mut (*m).m_limbs).write(buf);
    }
    membrane::note_alloc(o, membrane::align_obj_size(sz), TAG_MPZ);
    o
}

/// Raw mpz salient fields `(m_alloc, m_size, limb pointer, live count)`.
///
/// This function deliberately does not turn the pointer into either an owned
/// allocation or a reference with an unconstrained lifetime. The safe
/// [`crate::handle::Obj`] observer binds the immutable slice to `&self`; the C
/// export bridge binds it to a non-escaping callback invocation.
///
/// # Safety
/// `o` live mpz object.
// UNSAFE-LEDGER: FLN-UL-0033
#[allow(unsafe_code)]
pub(crate) unsafe fn mpz_fields(o: *mut LeanObject) -> (i32, i32, *const u64, usize) {
    // SAFETY: live mpz; these are fixed-size field reads. The pointer is not
    // dereferenced here.
    unsafe {
        let m = o.cast::<LeanMpzObject>();
        let alloc_ct = (&raw const (*m).m_alloc).read();
        let size = (&raw const (*m).m_size).read();
        let p = (&raw const (*m).m_limbs).read();
        let live = usize::try_from(size.unsigned_abs()).expect("mpz size");
        (alloc_ct, size, p.cast_const(), live)
    }
}

/// Free an mpz object's limb buffer (the `~mpz()` destructor half of
/// `lean_free_object`'s `LeanMPZ` arm). The small object itself goes through
/// the membrane afterwards.
///
/// # Safety
/// `o` live mpz object whose limb buffer was minted by [`alloc_mpz`]; must
/// be called exactly once, before the object's release.
// UNSAFE-LEDGER: FLN-UL-0034
#[allow(unsafe_code)]
pub(crate) unsafe fn mpz_drop_limbs(o: *mut LeanObject) {
    // SAFETY: buffer minted with limb_layout(m_alloc) by alloc_mpz.
    unsafe {
        let m = o.cast::<LeanMpzObject>();
        let alloc_ct = (&raw const (*m).m_alloc).read();
        let p = (&raw const (*m).m_limbs).read();
        if !p.is_null() && alloc_ct > 0 {
            dealloc(p.cast::<u8>(), limb_layout(alloc_ct as usize));
        }
    }
}
