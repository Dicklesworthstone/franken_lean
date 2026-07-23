//! fln-lld slice 2: the safe Marrow surface consumed at fln-rt level.
//!
//! Everything here is `forbid(unsafe_code)` (crate-wide): the object model is
//! exercised exclusively through the BOUNDARY_API-governed surface, and every
//! expectation comes from `fln_rt::abi` — the generated contract — never from
//! remembered constants. This is the covenant working end-to-end: rank-3 safe
//! code driving the rank-2 membrane with the kernel unnameable from below.

#![forbid(unsafe_code)]

use fln_rt::abi;
use fln_rt::obj::{Obj, shadow};
use std::sync::{Mutex, MutexGuard};

static TEST_LOCK: Mutex<()> = Mutex::new(());

fn lock() -> MutexGuard<'static, ()> {
    TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

fn align_delta(sz: usize) -> usize {
    sz.div_ceil(abi::OBJECT_SIZE_DELTA) * abi::OBJECT_SIZE_DELTA
}

/// Header facts of surface-built objects agree with the generated contract:
/// tags come from the contract tag table, small-path `m_cs_sz` obeys the
/// `OBJECT_SIZE_DELTA` alignment law, big-path categories store zero.
#[test]
fn surface_headers_agree_with_contract() {
    let _g = lock();

    let s = Obj::mk_string("via-fln-rt");
    assert_eq!(s.obj_tag(), usize::from(abi::TAG_STRING));
    assert_eq!(s.header().cs_sz, 0, "strings ride the big path");

    let a = Obj::mk_array(vec![Obj::mk_nat(1), Obj::mk_nat(2)]);
    assert_eq!(a.obj_tag(), usize::from(abi::TAG_ARRAY));
    assert_eq!(a.header().cs_sz, 0);

    let sa = Obj::mk_sarray(8, &[0u8; 16]);
    assert_eq!(sa.obj_tag(), usize::from(abi::TAG_SCALAR_ARRAY));
    assert_eq!(sa.header().other, 8, "element size lives in m_other");

    let c = Obj::mk_ctor(3, vec![Obj::mk_nat(7)], &[1, 2, 3]);
    assert!(usize::from(c.header().tag) <= usize::from(abi::TAG_MAX_CTOR_TAG));
    // Small path: m_cs_sz is the DELTA-aligned allocation size of
    // header + slots + scalars.
    let raw = 8 + 8 + 3;
    assert_eq!(usize::from(c.header().cs_sz), align_delta(raw));
    assert_eq!(c.byte_size(), align_delta(raw));

    let r = Obj::mk_ref(Obj::mk_string("cell"));
    assert_eq!(r.obj_tag(), usize::from(abi::TAG_REF));
    let t = Obj::mk_thunk_value(Obj::mk_nat(4));
    assert_eq!(t.obj_tag(), usize::from(abi::TAG_THUNK));
    let task = Obj::mk_task_pure(Obj::mk_nat(5));
    assert_eq!(task.obj_tag(), usize::from(abi::TAG_TASK));
    let m = Obj::mk_mpz(&[42], false);
    assert_eq!(m.obj_tag(), usize::from(abi::TAG_MPZ));
    let cl = Obj::mk_closure(2, vec![]);
    assert_eq!(cl.obj_tag(), usize::from(abi::TAG_CLOSURE));
    let e = Obj::mk_external_counting();
    assert_eq!(e.obj_tag(), usize::from(abi::TAG_EXTERNAL));
}

/// The RC discipline observed through the safe surface: balance, persistence,
/// MT negation and conservation — with the shadow registry proving the whole
/// scenario tears down without a single ownership fault.
#[test]
fn surface_rc_discipline_is_clean_under_shadows() {
    let _g = lock();
    shadow::enable();
    {
        let s = Obj::mk_string("shared-through-the-surface");
        let a = s.clone_ref();
        let b = s.clone_ref();
        assert_eq!(s.header().rc, 3);
        drop(a);
        drop(b);
        assert_eq!(s.header().rc, 1);

        let mt = Obj::mk_string("mt-through-the-surface");
        mt.make_mt();
        assert_eq!(mt.header().rc, -1, "mark_mt negates in place");
        mt.stress_mt(4, 500);
        assert_eq!(mt.header().rc, -1, "balanced storm conserves the count");

        let graph = Obj::mk_ctor(0, vec![Obj::mk_array(vec![Obj::mk_string("leaf")])], &[]);
        drop(graph);
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "everything released exactly once");
    assert!(
        events
            .iter()
            .all(|e| e.kind != shadow::EventKind::DoubleRelease
                && e.kind != shadow::EventKind::ForeignPointer)
    );
}

/// Negative lane: the surface exposes the misuse probes, and the shadows
/// kill both seeded faults when driven from safe rank-3 code.
#[test]
fn surface_shadow_probes_detect_seeded_faults() {
    let _g = lock();
    shadow::enable();
    Obj::probe_double_release();
    Obj::probe_foreign_pointer();
    let (events, _) = shadow::disable_and_drain();
    assert!(
        events
            .iter()
            .any(|e| e.kind == shadow::EventKind::DoubleRelease)
    );
    assert!(
        events
            .iter()
            .any(|e| e.kind == shadow::EventKind::ForeignPointer)
    );
}

/// The persistent law through the surface (never counted, immortal).
#[test]
fn surface_persistent_objects_never_count() {
    let _g = lock();
    let p = Obj::mk_string("immortal-through-the-surface");
    p.make_persistent();
    assert_eq!(p.header().rc, 0);
    let c = p.clone_ref();
    drop(c);
    assert_eq!(p.header().rc, 0);
}
