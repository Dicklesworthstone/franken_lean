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
//! > expose raw pointers. Immutable variable-size payloads may escape only as
//! > slices whose lifetime is tied to the owning `&Obj`.
//!
//! Handles are deliberately `!Send`/`!Sync` (raw-pointer field): the ST fast
//! path's exclusivity is structural. Cross-thread traffic goes through
//! `mark_mt` + the atomic lanes (`stress_mt`), mirroring upstream's
//! discipline exactly.

use crate::contract::TAG_MAX_CTOR_TAG;
use crate::export;
use crate::layout::LeanObject;
use crate::object;
use crate::rc::{self, Header};
use crate::shadow;
use crate::tagged;

/// Boxed-convention function types for the callable-closure constructors: every
/// parameter and the result are `lean_object*`, per the pin's `m_fun` contract
/// (`lean.h:211-217`; apply arms `apply.cpp:101-460`).
///
/// Reachable today from the apply cells only (hence the scoped dead_code
/// allowance, contract.rs precedent): the production consumer is Golem's
/// dispatch (bead franken_lean-7xe increments 5+), which widens these to the
/// reviewed public surface through fln-rt when it lands — a deliberate act
/// with BOUNDARY_API rows, never a default.
#[allow(dead_code)]
pub(crate) type BoxedFn1 = extern "C" fn(*mut LeanObject) -> *mut LeanObject;
/// Binary boxed-convention target ([`BoxedFn1`]).
#[allow(dead_code)]
pub(crate) type BoxedFn2 = extern "C" fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject;
/// Ternary boxed-convention target ([`BoxedFn1`]).
#[allow(dead_code)]
pub(crate) type BoxedFn3 =
    extern "C" fn(*mut LeanObject, *mut LeanObject, *mut LeanObject) -> *mut LeanObject;
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

/// The one law the raw layer's lower-bound `debug_assert` cannot state alone:
/// a scalar access at `byte_off` of `size` bytes must land inside the ctor's
/// scalar area, which spans `[other * 8, cs_sz - 8)` measured from `obj_cptr`.
/// A safe method may never permit an out-of-bounds read or write for any input
/// (review finding: the tag-only assert left the upper bound open entirely).
fn assert_scalar_bounds(h: &crate::rc::Header, byte_off: usize, size: usize) {
    assert!(
        h.tag <= TAG_MAX_CTOR_TAG,
        "scalar access on non-ctor tag {}",
        h.tag
    );
    let floor = usize::from(h.other) * 8;
    let extent = usize::from(h.cs_sz).saturating_sub(8);
    assert!(
        byte_off >= floor && byte_off + size <= extent,
        "scalar access at byte offset {byte_off} with size {size} escapes the \
         ctor scalar area [{floor}, {extent})"
    );
}

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

    /// Closure shell (function pointer dangling; layout/RC suites only). A
    /// shell must never reach [`Obj::apply`] — the callable constructors are
    /// the `mk_closure_fn*` family, where the arity comes from the TYPE.
    pub fn mk_closure(arity: u16, fixed: Vec<Obj>) -> Obj {
        // SAFETY: fresh allocation; fixed slots initialized with owned refs;
        // the dangling fun pointer is inert layout data — the apply machinery
        // (export.rs `apply_core`, 83r slice 4) is only reachable through the
        // typed `mk_closure_fn*` constructors below.
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

    /// Callable unary closure. The arity is derived from the function TYPE, so
    /// the closure/target contract cannot lie — the soundness condition the
    /// boxed convention needs is carried by the signature itself.
    #[allow(dead_code)]
    pub(crate) fn mk_closure_fn1(fun: BoxedFn1, fixed: Vec<Obj>) -> Obj {
        Self::mk_closure_native(fun as *mut c_void, 1, fixed)
    }

    /// Callable binary closure (arity from the type, as [`Obj::mk_closure_fn1`]).
    #[allow(dead_code)]
    pub(crate) fn mk_closure_fn2(fun: BoxedFn2, fixed: Vec<Obj>) -> Obj {
        Self::mk_closure_native(fun as *mut c_void, 2, fixed)
    }

    /// Callable ternary closure (arity from the type, as [`Obj::mk_closure_fn1`]).
    #[allow(dead_code)]
    pub(crate) fn mk_closure_fn3(fun: BoxedFn3, fixed: Vec<Obj>) -> Obj {
        Self::mk_closure_native(fun as *mut c_void, 3, fixed)
    }

    fn mk_closure_native(fun: *mut c_void, arity: u16, fixed: Vec<Obj>) -> Obj {
        assert!(
            usize::from(arity) > fixed.len(),
            "fixed args must leave at least one open slot"
        );
        // SAFETY: fresh allocation; fixed slots initialized with owned refs;
        // `fun` is a real extern "C" function pointer whose boxed-convention
        // arity equals `arity` BY TYPE at every public call site (the
        // `mk_closure_fn{1,2,3}` wrappers), which is exactly the precondition
        // `apply_core`'s saturated call relies on.
        // UNSAFE-LEDGER: FLN-UL-0181
        #[allow(unsafe_code)]
        unsafe {
            let o =
                object::alloc_closure(fun, arity, u16::try_from(fixed.len()).expect("num_fixed"));
            for (i, f) in fixed.into_iter().enumerate() {
                object::closure_set(o, i, f.into_raw());
            }
            Obj(o)
        }
    }

    /// Apply this value to `args` under the pin's boxed convention
    /// (`apply.cpp` semantics via export.rs `apply_core`): saturation calls
    /// the target, under-application curries a new closure, over-application
    /// re-enters with the remainder, and a scalar callee absorbs its
    /// arguments (the erased-proof arm). Consumes `self` and every argument;
    /// panics on an empty argument list (an application of nothing is a
    /// caller bug, not a runtime state).
    #[allow(dead_code)]
    pub(crate) fn apply(self, args: Vec<Obj>) -> Obj {
        assert!(!args.is_empty(), "apply needs at least one argument");
        let mut f = self.into_raw();
        let mut raw: Vec<*mut LeanObject> = args.into_iter().map(Obj::into_raw).collect();
        let mut i = 0usize;
        while i < raw.len() {
            let left = raw.len() - i;
            // The exported arms are safe fns over owned raw pointers; chunking
            // through arity 4 reproduces over-application re-entry exactly
            // (apply_core's own third arm does the same).
            f = match left {
                1 => export::export_lean_apply_1(f, raw[i]),
                2 => export::export_lean_apply_2(f, raw[i], raw[i + 1]),
                3 => export::export_lean_apply_3(f, raw[i], raw[i + 1], raw[i + 2]),
                _ => export::export_lean_apply_4(f, raw[i], raw[i + 1], raw[i + 2], raw[i + 3]),
            };
            i += left.min(4);
        }
        raw.clear();
        Obj(f)
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

    /// Unevaluated thunk carrying one owned closure.
    pub fn mk_thunk_closure(closure: Obj) -> Obj {
        assert!(closure.obj_tag() == usize::from(crate::contract::TAG_CLOSURE));
        // SAFETY: fresh allocation initialized with the consumed closure.
        unsafe { Obj(object::alloc_thunk_closure(closure.into_raw())) }
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

    /// Write a scalar into the ctor scalar area at `byte_off`, measured from
    /// `obj_cptr` (so the area spans `[other * 8, cs_sz - 8)` — the same
    /// convention the raw layer asserts from below).
    pub fn ctor_scalar_set_u64(&self, byte_off: usize, v: u64) {
        let h = self.header();
        assert_scalar_bounds(&h, byte_off, size_of::<u64>());
        // SAFETY: bounds asserted above; the write lands inside the object's
        // own scalar area.
        unsafe { object::ctor_set_scalar::<u64>(self.0, byte_off, v) };
    }

    /// Read a scalar from the ctor scalar area at `byte_off`, measured from
    /// `obj_cptr` (same convention as [`Self::ctor_scalar_set_u64`]).
    pub fn ctor_scalar_u64(&self, byte_off: usize) -> u64 {
        let h = self.header();
        assert_scalar_bounds(&h, byte_off, size_of::<u64>());
        // SAFETY: bounds asserted above; the read lands inside the object's
        // own scalar area.
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

    /// Mpz salient borrowed view `(alloc, size, limbs)`.
    ///
    /// The returned slice aliases the object's immutable ABI limb buffer and
    /// is valid only while this handle remains borrowed. No limb allocation,
    /// copy, radix conversion, or ownership transfer occurs.
    pub fn mpz_view(&self) -> (i32, i32, &[u64]) {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_MPZ));
        // SAFETY: invariant + tag assertion.
        unsafe {
            let (alloc, size, pointer, live) = object::mpz_fields(self.0);
            assert!(alloc >= 0, "mpz allocation count is negative");
            assert!(
                live <= alloc as usize,
                "mpz live limb count exceeds its allocation"
            );
            let limbs = if live == 0 {
                &[]
            } else {
                assert!(!pointer.is_null(), "nonempty mpz has a null limb buffer");
                core::slice::from_raw_parts(pointer, live)
            };
            (alloc, size, limbs)
        }
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

    /// Inspect a non-callable closure shell and retain each fixed argument.
    ///
    /// `None` distinguishes a native closure carrying a real function pointer
    /// from the shells created by [`Obj::mk_closure`]. The returned children
    /// are fresh owned references; no raw function or object pointer escapes.
    pub fn closure_shell_parts(&self) -> Option<(u16, Vec<Obj>)> {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_CLOSURE));
        // SAFETY: invariant + tag assertion. The function pointer is compared
        // only with the shell sentinel and never dereferenced. Every child is
        // retained before an owned handle escapes.
        unsafe {
            let (fun, arity, num_fixed, args) = object::closure_fields(self.0);
            if fun != core::ptr::dangling_mut::<c_void>() {
                return None;
            }
            let mut fixed = Vec::with_capacity(usize::from(num_fixed));
            for i in 0..usize::from(num_fixed) {
                let child = args.add(i).read();
                if !tagged::is_scalar(child) {
                    rc::inc_ref_n(child, 1);
                }
                fixed.push(Obj(child));
            }
            Some((arity, fixed))
        }
    }

    /// Read an `ST.Ref` cell as a fresh owned reference.
    pub fn ref_get(&self) -> Obj {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_REF));
        // SAFETY: invariant + tag assertion; the raw operation retains the
        // borrowed cell value before it escapes.
        unsafe { Obj(object::ref_get_owned(self.0)) }
    }

    /// Transfer the current `ST.Ref` value and leave the cell empty.
    ///
    /// The caller must refill the cell with [`Obj::ref_set`] before any
    /// operation that requires a live occupant.
    pub fn ref_take(&self) -> Obj {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_REF));
        // SAFETY: invariant + tag assertion; the raw operation transfers the
        // cell's owned token without retaining or releasing it.
        unsafe { Obj(object::ref_take(self.0)) }
    }

    /// Replace an `ST.Ref` cell, consuming the new value.
    pub fn ref_set(&self, value: Obj) {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_REF));
        // SAFETY: invariant + tag assertion; into_raw transfers exactly the
        // owned reference consumed by the cell.
        unsafe { object::ref_set(self.0, value.into_raw()) };
    }

    /// Replace an `ST.Ref` cell and return its previous owned value.
    pub fn ref_swap(&self, value: Obj) -> Obj {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_REF));
        // SAFETY: invariant + tag assertion; into_raw transfers the new cell
        // token and the raw operation transfers the old token back.
        unsafe { Obj(object::ref_swap(self.0, value.into_raw())) }
    }

    /// Reference identity equality without exposing either address.
    pub fn ref_ptr_eq(&self, other: &Obj) -> bool {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_REF));
        assert!(other.obj_tag() == usize::from(crate::contract::TAG_REF));
        self.0 == other.0
    }

    /// Retain the value of an already evaluated thunk.
    ///
    /// `None` denotes an unevaluated or in-flight thunk; forcing it requires
    /// the closure-application state machine rather than this observer.
    pub fn evaluated_thunk_value(&self) -> Option<Obj> {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_THUNK));
        // SAFETY: invariant + tag assertion. Evaluated thunks have a non-null
        // value and null closure; the value is retained before escape.
        unsafe {
            let (value, closure) = object::thunk_fields(self.0);
            if value.is_null() || !closure.is_null() {
                return None;
            }
            if !tagged::is_scalar(value) {
                rc::inc_ref_n(value, 1);
            }
            Some(Obj(value))
        }
    }

    /// Atomically claim an unevaluated thunk's closure.
    ///
    /// At most one caller receives `Some`; a later `None` means the thunk is
    /// already evaluated or another force is in flight.
    pub fn claim_thunk_closure(&self) -> Option<Obj> {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_THUNK));
        // SAFETY: invariant + tag assertion; the atomic exchange transfers the
        // stored ownership token to this handle.
        unsafe {
            let closure = object::thunk_take_closure(self.0);
            if closure.is_null() {
                None
            } else {
                Some(Obj(closure))
            }
        }
    }

    /// Install the value produced by a claimed thunk computation.
    ///
    /// The value is consumed on success. On a lost or invalid completion race
    /// it is released here and `false` is returned.
    pub fn complete_claimed_thunk(&self, value: Obj) -> bool {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_THUNK));
        let value = value.into_raw();
        // SAFETY: invariant + tag assertion; value is one owned reference and
        // the raw operation consumes it only when the compare-exchange wins.
        let installed = unsafe { object::thunk_try_set_value(self.0, value) };
        if !installed {
            drop(Obj(value));
        }
        installed
    }

    /// Retain the value of a finished task.
    ///
    /// `None` denotes a scheduled, waiting, or malformed task state; the
    /// scheduler owns those transitions.
    pub fn finished_task_value(&self) -> Option<Obj> {
        assert!(self.obj_tag() == usize::from(crate::contract::TAG_TASK));
        // SAFETY: invariant + tag assertion. A finished task has a non-null
        // value and no task implementation; retain before escape.
        unsafe {
            let (value, implementation) = object::task_fields(self.0);
            if value.is_null() || !implementation.is_null() {
                return None;
            }
            if !tagged::is_scalar(value) {
                rc::inc_ref_n(value, 1);
            }
            Some(Obj(value))
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

    /// Balanced multi-threaded inc/dec storm on an MT or persistent object;
    /// conservation is asserted by the caller via `header()`. Racing the RC of
    /// a single-threaded (`rc > 0`) object is upstream's UB, mirrored or not,
    /// so the precondition is asserted rather than assumed (review finding).
    pub fn stress_mt(&self, threads: usize, iters: usize) {
        assert!(!self.is_scalar());
        let header_rc = self.header().rc;
        assert!(
            header_rc <= 0,
            "stress_mt requires an MT or persistent object (rc <= 0), got rc = {header_rc}"
        );
        // SAFETY: the handle keeps the object alive across the scoped storm,
        // and the precondition above is exactly the one the atomic RC traffic
        // requires.
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

    /// Deliberately release the same object twice through the COLD path
    /// directly — the one RC entry that used to skip the shadow entirely.
    pub fn probe_cold_double_release() {
        assert!(shadow::enabled(), "misuse probes require shadows");
        // SAFETY: as probe_double_release; the cold path now checks first, so
        // the faulty second cold release is intercepted before `del_core`.
        unsafe {
            let o = object::alloc_ref(tagged::boxi(7));
            rc::dec_ref_cold(o); // legitimate release -> quarantine
            rc::dec_ref_cold(o); // fault: cold double release, must be skipped
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
