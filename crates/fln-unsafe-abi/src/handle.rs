//! Safe RAII object handles over the CompatHeap (bead fln-lld).
//!
//! `Obj` is the exported safe surface (re-exported by `fln-rt::obj` behind
//! `forbid(unsafe_code)`): a linear owned reference. Every public item here
//! carries a reviewed `ci/BOUNDARY_API.txt` row (D3 law b). Invariant (the
//! safety argument for every method below):
//!
//! > An `Obj` holds either a boxed scalar or a pointer to a live membrane
//! > object on which this `Obj` owns exactly one RC reference. Constructors
//! > establish the invariant; `clone_ref` adds a reference before copying
//! > the pointer; `Drop` surrenders the reference. Borrowed reads never
//! > escape raw pointers to callers.
//!
//! Handles are deliberately `!Send`/`!Sync` (raw-pointer field): the ST fast
//! path's exclusivity is structural. Cross-thread traffic goes through
//! `mark_mt` + the atomic lanes (`stress_mt`), mirroring upstream's
//! discipline exactly.

use crate::contract::TAG_MAX_CTOR_TAG;
use crate::layout::LeanObject;
use crate::object;
use crate::rc::{self, Header};
use crate::shadow;
use crate::tagged;
use core::ffi::c_void;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Count of canned-class external finalizer runs (test observability).
pub static EXTERNAL_FINALIZED: AtomicUsize = AtomicUsize::new(0);

// UNSAFE-LEDGER: FLN-UL-0051
#[allow(unsafe_code)]
unsafe extern "C" fn counting_finalize(_data: *mut c_void) {
    EXTERNAL_FINALIZED.fetch_add(1, Ordering::SeqCst);
}

// UNSAFE-LEDGER: FLN-UL-0052
#[allow(unsafe_code)]
unsafe extern "C" fn counting_foreach(_data: *mut c_void, _fn: *mut LeanObject) {}

/// An owned CompatHeap reference (or boxed scalar). See the module invariant.
pub struct Obj(*mut LeanObject);

// The single allowance for this module: every method body below manipulates
// raw membrane objects under the documented linear-ownership invariant.
// UNSAFE-LEDGER: FLN-UL-0049
#[allow(unsafe_code)]
impl Obj {
    /// Box a small `Nat` as an odd tagged pointer (`(n << 1) | 1`).
    pub fn mk_nat(n: usize) -> Obj {
        assert!(n <= tagged::MAX_SMALL_NAT);
        Obj(tagged::boxi(n))
    }

    /// Constructor object; consumes the children, copies the scalar bytes.
    pub fn mk_ctor(tag: u8, children: Vec<Obj>, scalar_bytes: &[u8]) -> Obj {
        assert!(tag <= TAG_MAX_CTOR_TAG);
        // SAFETY: fresh allocation; every slot is initialized with an owned
        // reference surrendered by its `Obj`; scalar bytes stay within the
        // declared scalar area.
        unsafe {
            let o = object::alloc_ctor(tag, children.len(), scalar_bytes.len());
            for (i, c) in children.into_iter().enumerate() {
                object::ctor_set(o, i, c.into_raw());
            }
            core::ptr::copy_nonoverlapping(
                scalar_bytes.as_ptr(),
                object::ctor_scalar_cptr(o),
                scalar_bytes.len(),
            );
            Obj(o)
        }
    }

    /// String object (`m_size = bytes + 1` incl. NUL; `m_length` = chars).
    pub fn mk_string(s: &str) -> Obj {
        // SAFETY: fresh, fully initialized by mk_string_unchecked.
        unsafe { Obj(object::mk_string_unchecked(s.as_bytes(), s.chars().count())) }
    }

    /// Array of objects; consumes the elements; capacity == size.
    pub fn mk_array(items: Vec<Obj>) -> Obj {
        // SAFETY: fresh allocation; slots 0..len initialized with owned refs.
        unsafe {
            let o = object::alloc_array(items.len(), items.len());
            for (i, it) in items.into_iter().enumerate() {
                object::array_set_core(o, i, it.into_raw());
            }
            Obj(o)
        }
    }

    /// Scalar array over raw bytes (`elem_size` recorded in `m_other`).
    pub fn mk_sarray(elem_size: u8, data: &[u8]) -> Obj {
        assert!(elem_size > 0 && data.len().is_multiple_of(usize::from(elem_size)));
        let n = data.len() / usize::from(elem_size);
        // SAFETY: fresh allocation; all n*elem_size salient bytes written.
        unsafe {
            let o = object::alloc_sarray(elem_size, n, n);
            let (_, _, _, dst) = object::sarray_fields(o);
            core::ptr::copy_nonoverlapping(data.as_ptr(), dst, data.len());
            Obj(o)
        }
    }

    /// Closure shell (function never invoked in slice 1); consumes `fixed`.
    pub fn mk_closure(arity: u16, fixed: Vec<Obj>) -> Obj {
        // SAFETY: fresh allocation; fixed slots initialized with owned refs;
        // the dangling fun pointer is data until the apply machinery exists.
        unsafe {
            let o = object::alloc_closure(
                core::ptr::dangling_mut::<c_void>(),
                arity,
                u16::try_from(fixed.len()).expect("num_fixed"),
            );
            for (i, f) in fixed.into_iter().enumerate() {
                object::closure_set(o, i, f.into_raw());
            }
            Obj(o)
        }
    }

    /// `IO.Ref` cell; consumes the value.
    pub fn mk_ref(value: Obj) -> Obj {
        // SAFETY: fresh allocation initialized with the owned value.
        unsafe { Obj(object::alloc_ref(value.into_raw())) }
    }

    /// Evaluated thunk; consumes the value.
    pub fn mk_thunk_value(value: Obj) -> Obj {
        // SAFETY: fresh allocation initialized with the owned value.
        unsafe { Obj(object::alloc_thunk_value(value.into_raw())) }
    }

    /// Finished task (`Task.pure`); consumes the value.
    pub fn mk_task_pure(value: Obj) -> Obj {
        // SAFETY: fresh allocation initialized with the owned value.
        unsafe { Obj(object::alloc_task_pure(value.into_raw())) }
    }

    /// Structural bignum from sign + little-endian limbs.
    pub fn mk_mpz(limbs: &[u64], negative: bool) -> Obj {
        // SAFETY: fresh allocation; limb buffer copied and owned.
        unsafe { Obj(object::alloc_mpz(limbs, negative)) }
    }

    /// External object of the canned counting class (finalizer increments
    /// [`EXTERNAL_FINALIZED`]). Real foreign classes arrive with the plugin
    /// door (bead franken_lean-sno).
    pub fn mk_external_counting() -> Obj {
        use std::sync::OnceLock;
        static CLASS: OnceLock<usize> = OnceLock::new();
        let class = *CLASS.get_or_init(|| {
            object::register_external_class(counting_finalize, counting_foreach) as usize
        });
        // SAFETY: the class registration is immortal; data is null and the
        // canned finalizer ignores it.
        unsafe {
            Obj(object::alloc_external(
                class as *mut _,
                core::ptr::null_mut(),
            ))
        }
    }

    // ---- observers -----------------------------------------------------

    pub fn is_scalar(&self) -> bool {
        tagged::is_scalar(self.0)
    }

    pub fn unbox(&self) -> usize {
        assert!(self.is_scalar());
        tagged::unbox(self.0)
    }

    /// Loaded header of a heap object.
    pub fn header(&self) -> Header {
        assert!(!self.is_scalar());
        // SAFETY: invariant — live membrane object.
        unsafe { rc::read_header(self.0) }
    }

    /// `lean_obj_tag` (`lean.h:597-599`).
    pub fn obj_tag(&self) -> usize {
        if self.is_scalar() {
            self.unbox()
        } else {
            usize::from(self.header().tag)
        }
    }

    pub fn byte_size(&self) -> usize {
        assert!(!self.is_scalar());
        // SAFETY: invariant — live membrane object.
        unsafe { rc::object_byte_size(self.0) }
    }

    /// Borrow a ctor child as a fresh owned reference.
    pub fn ctor_child(&self, i: usize) -> Obj {
        let h = self.header();
        assert!(h.tag <= TAG_MAX_CTOR_TAG && i < usize::from(h.other));
        // SAFETY: bounds asserted; the borrowed child is inc'd before it
        // escapes, so the result owns its own reference.
        unsafe {
            let c = object::ctor_get(self.0, i);
            if !tagged::is_scalar(c) {
                rc::inc_ref_n(c, 1);
            }
            Obj(c)
        }
    }

    /// `lean_ctor_set_tag` (compiler reuse discipline): retag in place.
    pub fn ctor_retag(&self, new_tag: u8) {
        assert!(self.header().tag <= TAG_MAX_CTOR_TAG);
        // SAFETY: invariant + ctor assertion; tag range asserted in the raw
        // layer.
        unsafe { object::ctor_set_tag(self.0, new_tag) };
    }

    /// Write a scalar into the ctor scalar area at `byte_off` past the
    /// object slots (upstream offset convention: bytes from the slot base).
    pub fn ctor_scalar_set_u64(&self, byte_off: usize, v: u64) {
        let h = self.header();
        assert!(h.tag <= TAG_MAX_CTOR_TAG);
        // SAFETY: offset discipline as in ctor_scalar_u64.
        unsafe { object::ctor_set_scalar::<u64>(self.0, byte_off, v) };
    }

    /// Read a scalar from the ctor scalar area at `byte_off` past the object
    /// slots (upstream offset convention: bytes from the slot base).
    pub fn ctor_scalar_u64(&self, byte_off: usize) -> u64 {
        let h = self.header();
        assert!(h.tag <= TAG_MAX_CTOR_TAG);
        // SAFETY: offset discipline asserted in the raw layer (debug) and by
        // construction here: callers pass offsets within the area they built.
        unsafe { object::ctor_get_scalar::<u64>(self.0, byte_off) }
    }

    /// String salient facts `(size, capacity, length, bytes-with-NUL)`.
    pub fn string_view(&self) -> (usize, usize, usize, Vec<u8>) {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_STRING));
        // SAFETY: invariant + tag assertion.
        unsafe { object::string_fields(self.0) }
    }

    /// Array `(size, capacity)`.
    pub fn array_view(&self) -> (usize, usize) {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_ARRAY));
        // SAFETY: invariant + tag assertion.
        unsafe { object::array_fields(self.0) }
    }

    /// Array element as a fresh owned reference.
    pub fn array_child(&self, i: usize) -> Obj {
        let (size, _) = self.array_view();
        assert!(i < size);
        // SAFETY: bounds asserted; inc before escape as in ctor_child.
        unsafe {
            let c = object::array_get(self.0, i);
            if !tagged::is_scalar(c) {
                rc::inc_ref_n(c, 1);
            }
            Obj(c)
        }
    }

    /// Mpz salient view `(alloc, size, limbs)`.
    pub fn mpz_view(&self) -> (i32, i32, Vec<u64>) {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_MPZ));
        // SAFETY: invariant + tag assertion.
        unsafe { object::mpz_fields(self.0) }
    }

    /// Closure `(arity, num_fixed)`.
    pub fn closure_view(&self) -> (u16, u16) {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_CLOSURE));
        // SAFETY: invariant + tag assertion.
        unsafe {
            let (_, arity, num_fixed, _) = object::closure_fields(self.0);
            (arity, num_fixed)
        }
    }

    // ---- reference discipline ------------------------------------------

    /// Opaque object identity for sharing tables (the compactor's dedup key,
    /// mirroring upstream's pointer-keyed `m_obj_table`). Distinct live
    /// objects yield distinct tokens; scalars yield their tagged word.
    /// NON-DETERMINISTIC across runs (address-derived) — a token must never
    /// enter an artifact, digest, or ordering decision (CGSE law).
    pub fn identity_token(&self) -> usize {
        self.0 as usize
    }

    /// Add one reference and return a second owned handle.
    pub fn clone_ref(&self) -> Obj {
        if !self.is_scalar() {
            // SAFETY: invariant — live object; adds the reference the new
            // handle will own.
            unsafe { rc::inc_ref_n(self.0, 1) };
        }
        Obj(self.0)
    }

    /// `lean_mark_persistent` over this handle's graph.
    pub fn make_persistent(&self) {
        if !self.is_scalar() {
            // SAFETY: invariant; single-threaded call, graph unshared.
            unsafe { rc::mark_persistent(self.0) };
        }
    }

    /// `lean_mark_mt` over this handle's graph.
    pub fn make_mt(&self) {
        if !self.is_scalar() {
            // SAFETY: invariant; single-threaded call point.
            unsafe { rc::mark_mt(self.0) };
        }
    }

    /// Balanced multi-threaded inc/dec storm on an MT object; conservation
    /// is asserted by the caller via `header()`.
    pub fn stress_mt(&self, threads: usize, iters: usize) {
        assert!(!self.is_scalar());
        // SAFETY: the handle keeps the object alive across the scoped storm.
        unsafe { rc::mt_stress(self.0, threads, iters) };
    }

    fn into_raw(self) -> *mut LeanObject {
        let p = self.0;
        core::mem::forget(self);
        p
    }

    // ---- scripted misuse probes (shadow mutation tests) ----------------

    /// Deliberately release the same object twice. With shadows enabled the
    /// second release must be detected and skipped (quarantine law).
    pub fn probe_double_release() {
        assert!(shadow::enabled(), "misuse probes require shadows");
        // SAFETY: shadows are enabled, so the faulty second dec is
        // intercepted by the registry before any dereference of freed state
        // (quarantined memory is retained and poisoned, never reused).
        unsafe {
            let o = object::alloc_ref(tagged::boxi(7));
            rc::dec_ref(o); // legitimate release -> quarantine
            rc::dec_ref(o); // fault: double release, must be skipped
        }
    }

    /// Deliberately run RC traffic on a pointer the membrane never minted.
    /// With shadows enabled the operation must be detected and skipped
    /// before any dereference.
    pub fn probe_foreign_pointer() {
        assert!(shadow::enabled(), "misuse probes require shadows");
        let foreign = Box::into_raw(Box::new(0u64)).cast::<LeanObject>();
        // SAFETY: shadows are enabled and check the registry BEFORE any
        // header access, so the foreign block is never read or written.
        unsafe { rc::dec_ref(foreign) };
        // SAFETY: reclaim the probe allocation we just leaked into a raw
        // pointer; it was never touched by the membrane.
        unsafe { drop(Box::from_raw(foreign.cast::<u64>())) };
    }

    /// Header facts of a quarantined (released-under-shadows) object: the
    /// poison law says its tag reads `TAG_RESERVED`.
    pub fn probe_quarantine_poison() -> u8 {
        assert!(shadow::enabled(), "misuse probes require shadows");
        // SAFETY: under shadows, released memory is retained (quarantined),
        // so reading its header is defined; that is exactly what this probe
        // verifies.
        unsafe {
            let o = object::alloc_ref(tagged::boxi(9));
            rc::dec_ref(o);
            rc::read_header(o).tag
        }
    }
}

// UNSAFE-LEDGER: FLN-UL-0050
#[allow(unsafe_code)]
impl Drop for Obj {
    fn drop(&mut self) {
        if !tagged::is_scalar(self.0) {
            // SAFETY: invariant — this handle owns exactly one reference and
            // surrenders it here.
            unsafe { rc::dec_ref(self.0) };
        }
    }
}
