//! fln-lld slice-1 verification: layout tests GENERATED from the contract
//! tables (never hand-written offsets), RC balance property tests, ownership
//! shadow mutation kills, tri-state transitions, bounded-stack teardown, and
//! the Marrow half of the C4 native-ABI probe rig.
//!
//! Every test takes the crate-wide lock: the shadow registry is global state
//! and the membrane consults it on every release.

use crate::contract::{self, FieldSpec};
use crate::handle::{EXTERNAL_FINALIZED, Obj};
use crate::layout::*;
use crate::membrane::align_obj_size;
use crate::shadow::{self, EventKind};
use crate::tagged;
use std::mem::offset_of;
use std::sync::atomic::Ordering;
use std::sync::{Mutex, MutexGuard};

static TEST_LOCK: Mutex<()> = Mutex::new(());

fn lock() -> MutexGuard<'static, ()> {
    TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

// ================================================================ layout law

/// (size, align) of a contract C type on the certified 64-bit LE targets.
fn c_type_info(c_type: &str) -> (usize, usize) {
    if c_type.contains('*') || c_type.ends_with("_proc") {
        return (8, 8);
    }
    match c_type {
        "int" | "unsigned" | "uint32_t" => (4, 4),
        "size_t" => (8, 8),
        "uint16_t" => (2, 2),
        "uint8_t" | "char" => (1, 1),
        "lean_object" => (8, 4),
        other => panic!("layout computer: unmapped C type {other:?}"),
    }
}

fn align_up(v: usize, a: usize) -> usize {
    v.div_ceil(a) * a
}

/// Compute field byte offsets and struct size from the generated contract
/// field specs, per the C layout rules (natural alignment; bitfield runs
/// packed LSB-first into their declared unit — G0-1 item 3).
fn c_struct_layout(fields: &[FieldSpec]) -> (Vec<(&'static str, usize)>, usize) {
    let mut offsets = Vec::new();
    let mut cur = 0usize;
    let mut max_align = 1usize;
    let mut i = 0;
    while i < fields.len() {
        let f = &fields[i];
        if let Some(_bits) = f.bits {
            // A run of bitfields sharing one unit of the declared type.
            let (unit_sz, unit_align) = c_type_info(f.c_type);
            let unit_off = align_up(cur, unit_align);
            max_align = max_align.max(unit_align);
            let mut bit_cursor = 0usize;
            while i < fields.len() {
                let Some(b) = fields[i].bits else { break };
                let b = usize::from(b);
                assert!(
                    b.is_multiple_of(8),
                    "contract bitfield {} not byte-aligned",
                    fields[i].name
                );
                assert!(bit_cursor + b <= unit_sz * 8, "bitfield unit overflow");
                offsets.push((fields[i].name, unit_off + bit_cursor / 8));
                bit_cursor += b;
                i += 1;
            }
            cur = unit_off + unit_sz;
            continue;
        }
        let (sz, al) = c_type_info(f.c_type);
        let off = align_up(cur, al);
        offsets.push((f.name, off));
        max_align = max_align.max(al);
        if f.array == Some("[]") {
            // Flexible array member: contributes offset and alignment only.
            cur = off;
        } else {
            cur = off + sz;
        }
        i += 1;
    }
    (offsets, align_up(cur, max_align))
}

/// The mirror registry: contract struct name -> (Rust size, field offsets).
/// The OFFSETS come from the compiler; the EXPECTATIONS come from the
/// contract tables — nothing here is a remembered constant.
fn mirror_layout(name: &str) -> (usize, Vec<(&'static str, usize)>) {
    match name {
        "lean_object" => (
            size_of::<LeanObject>(),
            vec![
                ("m_rc", offset_of!(LeanObject, m_rc)),
                ("m_cs_sz", offset_of!(LeanObject, m_cs_sz)),
                ("m_other", offset_of!(LeanObject, m_other)),
                ("m_tag", offset_of!(LeanObject, m_tag)),
            ],
        ),
        "lean_ctor_object" => (
            size_of::<LeanCtorObject>(),
            vec![
                ("m_header", offset_of!(LeanCtorObject, m_header)),
                ("m_objs", offset_of!(LeanCtorObject, m_objs)),
            ],
        ),
        "lean_array_object" => (
            size_of::<LeanArrayObject>(),
            vec![
                ("m_header", offset_of!(LeanArrayObject, m_header)),
                ("m_size", offset_of!(LeanArrayObject, m_size)),
                ("m_capacity", offset_of!(LeanArrayObject, m_capacity)),
                ("m_data", offset_of!(LeanArrayObject, m_data)),
            ],
        ),
        "lean_sarray_object" => (
            size_of::<LeanSarrayObject>(),
            vec![
                ("m_header", offset_of!(LeanSarrayObject, m_header)),
                ("m_size", offset_of!(LeanSarrayObject, m_size)),
                ("m_capacity", offset_of!(LeanSarrayObject, m_capacity)),
                ("m_data", offset_of!(LeanSarrayObject, m_data)),
            ],
        ),
        "lean_string_object" => (
            size_of::<LeanStringObject>(),
            vec![
                ("m_header", offset_of!(LeanStringObject, m_header)),
                ("m_size", offset_of!(LeanStringObject, m_size)),
                ("m_capacity", offset_of!(LeanStringObject, m_capacity)),
                ("m_length", offset_of!(LeanStringObject, m_length)),
                ("m_data", offset_of!(LeanStringObject, m_data)),
            ],
        ),
        "lean_closure_object" => (
            size_of::<LeanClosureObject>(),
            vec![
                ("m_header", offset_of!(LeanClosureObject, m_header)),
                ("m_fun", offset_of!(LeanClosureObject, m_fun)),
                ("m_arity", offset_of!(LeanClosureObject, m_arity)),
                ("m_num_fixed", offset_of!(LeanClosureObject, m_num_fixed)),
                ("m_objs", offset_of!(LeanClosureObject, m_objs)),
            ],
        ),
        "lean_ref_object" => (
            size_of::<LeanRefObject>(),
            vec![
                ("m_header", offset_of!(LeanRefObject, m_header)),
                ("m_value", offset_of!(LeanRefObject, m_value)),
            ],
        ),
        "lean_thunk_object" => (
            size_of::<LeanThunkObject>(),
            vec![
                ("m_header", offset_of!(LeanThunkObject, m_header)),
                ("m_value", offset_of!(LeanThunkObject, m_value)),
                ("m_closure", offset_of!(LeanThunkObject, m_closure)),
            ],
        ),
        "lean_task_imp" => (
            size_of::<LeanTaskImp>(),
            vec![
                ("m_closure", offset_of!(LeanTaskImp, m_closure)),
                ("m_head_dep", offset_of!(LeanTaskImp, m_head_dep)),
                ("m_next_dep", offset_of!(LeanTaskImp, m_next_dep)),
                ("m_prio", offset_of!(LeanTaskImp, m_prio)),
                ("m_canceled", offset_of!(LeanTaskImp, m_canceled)),
                ("m_keep_alive", offset_of!(LeanTaskImp, m_keep_alive)),
                ("m_deleted", offset_of!(LeanTaskImp, m_deleted)),
            ],
        ),
        "lean_task_object" => (
            size_of::<LeanTaskObject>(),
            vec![
                ("m_header", offset_of!(LeanTaskObject, m_header)),
                ("m_value", offset_of!(LeanTaskObject, m_value)),
                ("m_imp", offset_of!(LeanTaskObject, m_imp)),
            ],
        ),
        "lean_promise_object" => (
            size_of::<LeanPromiseObject>(),
            vec![
                ("m_header", offset_of!(LeanPromiseObject, m_header)),
                ("m_result", offset_of!(LeanPromiseObject, m_result)),
            ],
        ),
        "lean_external_class" => (
            size_of::<LeanExternalClass>(),
            vec![
                ("m_finalize", offset_of!(LeanExternalClass, m_finalize)),
                ("m_foreach", offset_of!(LeanExternalClass, m_foreach)),
            ],
        ),
        "lean_external_object" => (
            size_of::<LeanExternalObject>(),
            vec![
                ("m_header", offset_of!(LeanExternalObject, m_header)),
                ("m_class", offset_of!(LeanExternalObject, m_class)),
                ("m_data", offset_of!(LeanExternalObject, m_data)),
            ],
        ),
        other => panic!("no mirror registered for contract struct {other:?}"),
    }
}

/// Layout tests generated FROM the contract module: every struct, every
/// field, offsets and sizes computed from the generated field specs and
/// compared against the compiler's view of the repr(C) mirrors.
#[test]
fn layout_mirrors_match_contract_tables() {
    let _g = lock();
    for spec in contract::OBJECT_STRUCTS {
        let (expected_fields, expected_size) = c_struct_layout(spec.fields);
        let (mirror_size, mirror_fields) = mirror_layout(spec.name);
        assert_eq!(
            mirror_size, expected_size,
            "sizeof({}) mirror vs contract-computed",
            spec.name
        );
        assert_eq!(
            mirror_fields.len(),
            expected_fields.len(),
            "field count of {} (contract line {})",
            spec.name,
            spec.line
        );
        for ((mf, moff), (cf, coff)) in mirror_fields.iter().zip(expected_fields.iter()) {
            assert_eq!(mf, cf, "field order in {}", spec.name);
            assert_eq!(moff, coff, "offsetof({}, {})", spec.name, mf);
        }
    }
}

/// The header packing law (G0-1 item 3): `m_rc` low word, then
/// `m_cs_sz:16 | m_other:8 | m_tag:8` low-to-high in the second word.
#[test]
fn header_bitfield_packing() {
    let _g = lock();
    assert_eq!(size_of::<LeanObject>(), 8);
    assert_eq!(offset_of!(LeanObject, m_rc), 0);
    assert_eq!(offset_of!(LeanObject, m_cs_sz), 4);
    assert_eq!(offset_of!(LeanObject, m_other), 6);
    assert_eq!(offset_of!(LeanObject, m_tag), 7);
}

// ================================================================ tagged

#[test]
fn tagged_pointer_law() {
    let _g = lock();
    for n in [0usize, 1, 2, 41, 1 << 20, tagged::MAX_SMALL_NAT] {
        let b = Obj::mk_nat(n);
        assert!(b.is_scalar());
        assert_eq!(b.unbox(), n);
        assert_eq!(b.obj_tag(), n); // lean_obj_tag on scalars is the value
    }
}

// ================================================================ objects

#[test]
fn ctor_header_and_scalar_facts() {
    let _g = lock();
    let c = Obj::mk_ctor(
        5,
        vec![Obj::mk_nat(1), Obj::mk_nat(2)],
        &[0xAB, 0xCD, 3, 4, 5, 6, 7, 8, 9],
    );
    let h = c.header();
    assert_eq!(h.tag, 5);
    assert_eq!(h.other, 2, "m_other = pointer-field count");
    assert_eq!(h.rc, 1);
    // Small path under the pin's LEAN_MIMALLOC config: m_cs_sz = aligned size.
    let raw = 8 + 2 * 8 + 9;
    assert_eq!(usize::from(h.cs_sz), align_obj_size(raw));
    assert_eq!(c.byte_size(), align_obj_size(raw));
    assert_eq!(c.ctor_child(0).unbox(), 1);
    assert_eq!(c.ctor_child(1).unbox(), 2);
    // Scalar area begins after the object slots (G0-1 packing law).
    let first = c.ctor_scalar_u64(2 * 8);
    assert_eq!(first & 0xFF, 0xAB);
    assert_eq!((first >> 8) & 0xFF, 0xCD);
}

#[test]
fn ctor_retag_and_scalar_write() {
    let _g = lock();
    let c = Obj::mk_ctor(1, vec![Obj::mk_nat(0)], &[0u8; 8]);
    assert_eq!(c.header().tag, 1);
    c.ctor_retag(9);
    assert_eq!(c.header().tag, 9, "lean_ctor_set_tag semantics");
    c.ctor_scalar_set_u64(8, 0x0123_4567_89AB_CDEF);
    assert_eq!(c.ctor_scalar_u64(8), 0x0123_4567_89AB_CDEF);
}

/// The sharing-maximizer zero law: alignment padding of ctor memory is
/// deterministically zeroed (`lean.h:441-451`).
#[test]
fn ctor_padded_word_is_zeroed() {
    let _g = lock();
    // 8 (header) + 8 (one slot) + 1 (scalar) = 17 -> aligned 24; the final
    // word (bytes 16..24 of the block, i.e. scalar offset 8) must read as the
    // written byte with all padding bytes zero.
    let c = Obj::mk_ctor(0, vec![Obj::mk_nat(3)], &[0x7F]);
    assert_eq!(c.ctor_scalar_u64(8), 0x7F);
}

#[test]
fn string_facts_utf8() {
    let _g = lock();
    let s = Obj::mk_string("héllo∀");
    let bytes = "héllo∀".as_bytes();
    let (size, cap, len, data) = s.string_view();
    assert_eq!(size, bytes.len() + 1, "m_size includes the NUL");
    assert_eq!(cap, bytes.len() + 1);
    assert_eq!(len, 6, "m_length is the codepoint count");
    assert_eq!(&data[..bytes.len()], bytes);
    assert_eq!(data[bytes.len()], 0);
    // Strings ride the big path: m_cs_sz = 0.
    assert_eq!(s.header().cs_sz, 0);

    let empty = Obj::mk_string("");
    let (size, _, len, data) = empty.string_view();
    assert_eq!(
        (size, len),
        (1, 0),
        "empty string stores its NUL (G0-1 item 8)"
    );
    assert_eq!(data, vec![0]);
}

#[test]
fn array_and_sarray_facts() {
    let _g = lock();
    let a = Obj::mk_array(vec![Obj::mk_nat(10), Obj::mk_string("x"), Obj::mk_nat(30)]);
    assert_eq!(a.array_view(), (3, 3));
    assert_eq!(a.header().cs_sz, 0, "arrays ride the big path");
    assert_eq!(a.array_child(0).unbox(), 10);
    assert_eq!(a.array_child(2).unbox(), 30);
    assert_eq!(a.byte_size(), size_of::<LeanArrayObject>() + 3 * 8);

    let sa = Obj::mk_sarray(4, &[1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]);
    let h = sa.header();
    assert_eq!(h.other, 4, "element size lives in m_other");
    assert_eq!(h.cs_sz, 0);
    assert_eq!(sa.byte_size(), size_of::<LeanSarrayObject>() + 12);
}

#[test]
fn closure_ref_thunk_task_mpz_facts() {
    let _g = lock();
    let cl = Obj::mk_closure(3, vec![Obj::mk_nat(9), Obj::mk_string("fixed")]);
    assert_eq!(cl.closure_view(), (3, 2));
    let (arity, fixed) = cl
        .closure_shell_parts()
        .expect("mk_closure produces an inspectable shell");
    assert_eq!(arity, 3);
    assert_eq!(fixed.len(), 2);
    assert_eq!(fixed[0].unbox(), 9);
    assert_eq!(cl.header().cs_sz, 0, "closures ride the big path");
    drop(cl);
    let (size, _, _, bytes) = fixed[1].string_view();
    assert_eq!(
        &bytes[..size],
        b"fixed\0",
        "retained shell children outlive the original closure handle"
    );

    let r = Obj::mk_ref(Obj::mk_string("cell"));
    assert_eq!(
        usize::from(r.header().cs_sz),
        align_obj_size(size_of::<LeanRefObject>())
    );
    let alias = r.clone_ref();
    assert!(r.ref_ptr_eq(&alias));
    let distinct = Obj::mk_ref(Obj::mk_string("cell"));
    assert!(
        !r.ref_ptr_eq(&distinct),
        "equal contents do not collapse reference identity"
    );
    let before = r.ref_get();
    let old = r.ref_swap(Obj::mk_string("swapped"));
    let after = alias.ref_get();
    let (_, _, _, before_bytes) = before.string_view();
    let (_, _, _, old_bytes) = old.string_view();
    let (_, _, _, after_bytes) = after.string_view();
    assert_eq!(before_bytes, b"cell\0");
    assert_eq!(old_bytes, b"cell\0");
    assert_eq!(after_bytes, b"swapped\0");
    alias.ref_set(Obj::mk_string("set"));
    let set = r.ref_get();
    let (_, _, _, set_bytes) = set.string_view();
    assert_eq!(set_bytes, b"set\0");

    let t = Obj::mk_thunk_value(Obj::mk_string("thunk"));
    assert_eq!(t.obj_tag(), usize::from(contract::TAG_THUNK));
    let thunk_value = t
        .evaluated_thunk_value()
        .expect("Thunk.pure is already evaluated");
    drop(t);
    let (_, _, _, thunk_bytes) = thunk_value.string_view();
    assert_eq!(
        thunk_bytes, b"thunk\0",
        "retained thunk payload outlives its container"
    );

    let delayed = Obj::mk_thunk_closure(Obj::mk_closure(1, Vec::new()));
    assert!(delayed.evaluated_thunk_value().is_none());
    let claimed = delayed
        .claim_thunk_closure()
        .expect("the delayed closure is claimed exactly once");
    assert_eq!(claimed.closure_view(), (1, 0));
    assert!(
        delayed.claim_thunk_closure().is_none(),
        "a second force sees the in-flight state"
    );
    drop(claimed);
    assert!(delayed.complete_claimed_thunk(Obj::mk_string("forced")));
    assert!(
        !delayed.complete_claimed_thunk(Obj::mk_string("discarded")),
        "a completed thunk cannot be overwritten"
    );
    let delayed_value = delayed
        .evaluated_thunk_value()
        .expect("the completed payload is retained");
    let (_, _, _, delayed_bytes) = delayed_value.string_view();
    assert_eq!(delayed_bytes, b"forced\0");

    let task = Obj::mk_task_pure(Obj::mk_string("task"));
    assert_eq!(task.obj_tag(), usize::from(contract::TAG_TASK));
    let task_value = task
        .finished_task_value()
        .expect("Task.pure is already finished");
    drop(task);
    let (_, _, _, task_bytes) = task_value.string_view();
    assert_eq!(
        task_bytes, b"task\0",
        "retained task payload outlives its container"
    );

    let m = Obj::mk_mpz(&[0xDEAD_BEEF, 0x1], true);
    let (alloc, size, limbs) = m.mpz_view();
    assert_eq!(alloc, 2);
    assert_eq!(size, -2, "sign of the value is the sign of m_size");
    assert_eq!(limbs, &[0xDEAD_BEEF, 0x1]);
}

#[test]
fn ref_take_transfers_the_exact_cell_token_and_refill_restores_ownership() {
    let _g = lock();
    shadow::enable();
    {
        let payload = Obj::mk_string("single-threaded");
        let payload_identity = payload.identity_token();
        let cell = Obj::mk_ref(payload);
        let taken = cell.ref_take();
        assert_eq!(
            taken.identity_token(),
            payload_identity,
            "take transfers the cell token without retaining or replacing it"
        );
        cell.ref_set(Obj::mk_string("refilled"));
        let refilled = cell.ref_get();
        let (_, _, _, refilled_bytes) = refilled.string_view();
        assert_eq!(refilled_bytes, b"refilled\0");

        let shared_payload = Obj::mk_string("shared");
        let shared_identity = shared_payload.identity_token();
        let shared_cell = Obj::mk_ref(shared_payload);
        let shared_alias = shared_cell.clone_ref();
        shared_cell.make_mt();
        let shared_taken = shared_alias.ref_take();
        assert_eq!(
            shared_taken.identity_token(),
            shared_identity,
            "the atomic lane transfers the same owned cell token"
        );
        shared_cell.ref_set(Obj::mk_string("shared-refill"));
        let shared_refilled = shared_alias.ref_get();
        let (_, _, _, shared_bytes) = shared_refilled.string_view();
        assert_eq!(shared_bytes, b"shared-refill\0");

        let drop_payload = Obj::mk_string("outlives-empty-cell");
        let drop_identity = drop_payload.identity_token();
        let empty_cell = Obj::mk_ref(drop_payload);
        let survivor = empty_cell.ref_take();
        drop(empty_cell);
        assert_eq!(
            survivor.identity_token(),
            drop_identity,
            "dropping an empty cell does not release the transferred token"
        );
        let (_, _, _, survivor_bytes) = survivor.string_view();
        assert_eq!(survivor_bytes, b"outlives-empty-cell\0");
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "take and refill leave no live ABI allocation");
    assert!(
        events.iter().all(|event| {
            event.kind != EventKind::DoubleRelease && event.kind != EventKind::ForeignPointer
        }),
        "take and refill preserve exact cell ownership"
    );
}

#[test]
fn mt_ref_cell_operations_preserve_owned_values_on_the_atomic_lane() {
    let _g = lock();
    shadow::enable();
    {
        let cell = Obj::mk_ref(Obj::mk_string("old"));
        let alias = cell.clone_ref();
        cell.make_mt();
        assert_eq!(cell.header().rc, -2);

        cell.ref_set(Obj::mk_string("new"));
        let retained = alias.ref_get();
        assert!(
            retained.header().rc <= -2,
            "the cell and owned read retain distinct MT references"
        );
        let previous = cell.ref_swap(Obj::mk_string("final"));
        assert_eq!(
            retained.identity_token(),
            previous.identity_token(),
            "swap transfers the exact previous ABI object"
        );
        let (_, _, _, previous_bytes) = previous.string_view();
        assert_eq!(previous_bytes, b"new\0");
        let current = alias.ref_get();
        let (_, _, _, current_bytes) = current.string_view();
        assert_eq!(current_bytes, b"final\0");
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0);
    assert!(
        events.iter().all(|event| {
            event.kind != EventKind::DoubleRelease && event.kind != EventKind::ForeignPointer
        }),
        "the atomic ref lane preserves exact ownership"
    );
}

#[test]
fn mpz_view_is_zero_copy_normalized_and_excludes_negative_zero() {
    let _g = lock();
    let m = Obj::mk_mpz(&[0xDEAD_BEEF, 0x1], false);
    let (alloc, size, first) = m.mpz_view();
    let (_, _, second) = m.mpz_view();
    assert_eq!((alloc, size), (2, 2));
    assert_eq!(first.as_ptr(), second.as_ptr(), "the view must not copy");
    let magnitude = fln_bignum::nat::BigNatView::from_limbs_le(first);
    assert_eq!(
        magnitude.limbs_le().as_ptr(),
        first.as_ptr(),
        "the bignum view must alias the ABI limb buffer"
    );

    let normalized = Obj::mk_mpz(&[7, 0, 0], true);
    let (alloc, size, limbs) = normalized.mpz_view();
    assert_eq!((alloc, size, limbs), (1, -1, &[7][..]));

    let zero = Obj::mk_mpz(&[0, 0], true);
    let (alloc, size, limbs) = zero.mpz_view();
    assert_eq!((alloc, size), (0, 0), "negative zero is impossible");
    assert!(limbs.is_empty());
}

#[test]
fn external_finalizer_runs_exactly_once() {
    let _g = lock();
    let before = EXTERNAL_FINALIZED.load(Ordering::SeqCst);
    let e = Obj::mk_external_counting();
    assert_eq!(e.obj_tag(), usize::from(contract::TAG_EXTERNAL));
    drop(e);
    assert_eq!(EXTERNAL_FINALIZED.load(Ordering::SeqCst), before + 1);
}

// ================================================================ tri-state RC

#[test]
fn rc_clone_and_drop_balance() {
    let _g = lock();
    let s = Obj::mk_string("shared");
    assert_eq!(s.header().rc, 1);
    let a = s.clone_ref();
    let b = s.clone_ref();
    assert_eq!(s.header().rc, 3);
    drop(a);
    assert_eq!(s.header().rc, 2);
    drop(b);
    assert_eq!(s.header().rc, 1);
}

#[test]
fn persistent_objects_are_never_counted() {
    let _g = lock();
    let s = Obj::mk_string("immortal");
    s.make_persistent();
    assert_eq!(s.header().rc, 0);
    let c = s.clone_ref();
    assert_eq!(s.header().rc, 0, "inc on persistent is a no-op");
    drop(c);
    assert_eq!(s.header().rc, 0, "dec on persistent is a no-op");
    // The object is deliberately immortal from here on (upstream semantics);
    // Obj's final drop is also a no-op.
}

#[test]
fn mark_persistent_traverses_the_graph() {
    let _g = lock();
    let inner = Obj::mk_string("leaf");
    let keep = inner.clone_ref();
    let c = Obj::mk_ctor(1, vec![inner, Obj::mk_nat(2)], &[]);
    c.make_persistent();
    assert_eq!(c.header().rc, 0);
    assert_eq!(
        keep.header().rc,
        0,
        "children are zeroed too (object.cpp:553)"
    );
}

#[test]
fn mark_mt_negates_and_atomics_conserve() {
    let _g = lock();
    let s = Obj::mk_string("concurrent");
    let extra = s.clone_ref();
    assert_eq!(s.header().rc, 2);
    s.make_mt();
    assert_eq!(s.header().rc, -2, "mark_mt negates the ST count in place");
    s.stress_mt(8, 2000);
    assert_eq!(s.header().rc, -2, "balanced MT traffic conserves the count");
    drop(extra);
    assert_eq!(s.header().rc, -1, "MT dec via atomic fetch_add");
}

/// An ST refcount that overflows must FAULT, not wrap (D3; FL-INV-07).
///
/// A wrapped positive count does not become "a very large count" — it becomes a
/// NEGATIVE one, and `m_rc < 0` *is* the multi-threaded encoding in this ABI.
/// `mark_mt_negates_and_atomics_conserve` above asserts exactly that negation,
/// so an overflow silently reclassifies an object's threading discipline: every
/// later dec takes the atomic MT path on an object nothing is synchronizing,
/// and the tri-state invariant the whole RC surface rests on is gone.
///
/// The site's only guard was a `debug_assert!` sitting next to a
/// `wrapping_add`, which is to say there was no guard in a release build at
/// all — the shape this test exists to keep out.
///
/// Reachability: `lean_inc_ref_n` takes a caller-supplied `size_t n` at the pin
/// (`lean.h:556`, and it is already specified in `fln_rt::abi::FUNCTION_CENSUS`),
/// so once that export is wired this is one hostile call from C. Today it is
/// only reachable internally, where `n` is always 1.
#[test]
#[should_panic(expected = "single-threaded RC overflow")]
fn st_refcount_overflow_faults_rather_than_wrapping_into_the_mt_encoding() {
    let _g = lock();
    let s = Obj::mk_string("overflow");
    assert_eq!(s.header().rc, 1);
    // rc is 1, so one increment of i32::MAX carries it past i32::MAX.
    // UNSAFE-LEDGER: FLN-UL-0180
    #[allow(unsafe_code)]
    unsafe {
        // SAFETY: `s` keeps the object alive for the call; the pointer is this
        // handle's own address. The call is expected to fault before it writes,
        // leaving rc at 1 so the handle still drops cleanly.
        crate::rc::inc_ref_n(s.identity_token() as *mut LeanObject, i32::MAX as usize);
    }
}

#[test]
fn mt_object_dies_on_last_dec() {
    let _g = lock();
    shadow::enable();
    {
        let s = Obj::mk_string("mt-death");
        s.make_mt();
        let c = s.clone_ref();
        drop(s);
        drop(c);
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "the MT object was released exactly once");
    let releases = events
        .iter()
        .filter(|e| e.kind == EventKind::Release)
        .count();
    assert_eq!(releases, 1);
    assert!(
        events
            .iter()
            .all(|e| e.kind != EventKind::DoubleRelease && e.kind != EventKind::ForeignPointer)
    );
}

/// RC balance property: a seeded random object soup — builds, shares, and
/// drops — must tear down completely with zero ownership faults.
///
/// MANDATED MUTANT (AGENTS testing policy: "dropped retain"): neutering
/// `rc::inc_ref_n` fails this test at `rc.rs`'s ownership-fault check. Verified
/// by planting it on 2026-07-26 (bead
/// `fln-mandated-mutant-join-unwatched-uagk`), not by inspection —
/// `mt_object_dies_on_last_dec` and `rc_clone_and_drop_balance` also die, the
/// latter by SIGABRT rather than a clean assertion. The marker is what joins
/// this test to §18's list; without it the kill was real but nothing recorded
/// which obligation it discharged.
#[test]
fn rc_balance_property_random_graphs() {
    let _g = lock();
    // xorshift64* — deterministic, dependency-free.
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = move || {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        state = state.wrapping_mul(0x2545_F491_4F6C_DD1D);
        state
    };
    shadow::enable();
    {
        let mut pool: Vec<Obj> = Vec::new();
        for step in 0..400u64 {
            match next() % 6 {
                0 => pool.push(Obj::mk_nat((next() % 1000) as usize)),
                1 => pool.push(Obj::mk_string("prop")),
                2 if !pool.is_empty() => {
                    let i = (next() as usize) % pool.len();
                    pool.push(pool[i].clone_ref());
                }
                3 if pool.len() >= 2 => {
                    let a = pool.remove((next() as usize) % pool.len());
                    let b = pool.remove((next() as usize) % pool.len());
                    let tag = (next() % 4) as u8;
                    pool.push(Obj::mk_ctor(tag, vec![a, b], &[(step & 0xFF) as u8]));
                }
                4 if pool.len() >= 3 => {
                    let a = pool.remove((next() as usize) % pool.len());
                    let b = pool.remove((next() as usize) % pool.len());
                    let c = pool.remove((next() as usize) % pool.len());
                    pool.push(Obj::mk_array(vec![a, b, c]));
                }
                _ if !pool.is_empty() => {
                    let i = (next() as usize) % pool.len();
                    drop(pool.remove(i));
                }
                _ => {}
            }
        }
        drop(pool);
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "every allocation released exactly once");
    assert!(
        events
            .iter()
            .all(|e| e.kind != EventKind::DoubleRelease && e.kind != EventKind::ForeignPointer),
        "no ownership faults in a balanced script"
    );
}

/// Teardown of a deep chain must not recurse: run on a deliberately small
/// stack (the dev-box `ulimit -s unlimited` masks overflow bugs otherwise).
#[test]
fn deep_chain_teardown_bounded_stack() {
    let _g = lock();
    std::thread::Builder::new()
        .name("bounded-teardown".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut o = Obj::mk_nat(0);
            for _ in 0..100_000 {
                o = Obj::mk_ctor(0, vec![o], &[]);
            }
            drop(o); // iterative worklist, or this overflows 256 KiB
        })
        .expect("spawn")
        .join()
        .expect("deep teardown must not overflow the bounded stack");
}

// ================================================================ shadows

#[test]
fn shadow_kills_double_release() {
    let _g = lock();
    shadow::enable();
    Obj::probe_double_release();
    let (events, _) = shadow::disable_and_drain();
    assert!(
        events.iter().any(|e| e.kind == EventKind::DoubleRelease),
        "seeded double release must be detected"
    );
}

#[test]
fn shadow_kills_cold_double_release() {
    let _g = lock();
    shadow::enable();
    Obj::probe_cold_double_release();
    let (events, _) = shadow::disable_and_drain();
    assert!(
        events.iter().any(|e| e.kind == EventKind::DoubleRelease),
        "the cold path must detect a double release like every sibling"
    );
}

#[test]
fn ctor_scalar_bounds_refuse_every_escape() {
    let _g = lock();
    // One child slot and a 16-byte scalar area: the object extent is
    // header(8) + slot(8) + 16, so scalar bytes span [8, 24) from obj_cptr.
    let obj = Obj::mk_ctor(1, vec![Obj::mk_nat(1)], &[0xAB; 16]);
    // Control first: the valid ends of the area read and write cleanly.
    obj.ctor_scalar_set_u64(8, 0x1122_3344_5566_7788);
    obj.ctor_scalar_set_u64(16, 0x8877_6655_4433_2211);
    assert_eq!(obj.ctor_scalar_u64(8), 0x1122_3344_5566_7788);
    assert_eq!(obj.ctor_scalar_u64(16), 0x8877_6655_4433_2211);

    for bad in [0usize, 24, 128, usize::MAX - 8] {
        let read =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| obj.ctor_scalar_u64(bad)));
        assert!(
            read.is_err(),
            "an out-of-area read at {bad} must refuse, not escape"
        );
        let write = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            obj.ctor_scalar_set_u64(bad, 0)
        }));
        assert!(
            write.is_err(),
            "an out-of-area write at {bad} must refuse, not escape"
        );
    }
}

#[test]
fn stress_mt_refuses_a_single_threaded_object() {
    let _g = lock();
    let st = Obj::mk_ctor(0, vec![], &[]);
    assert!(st.header().rc > 0, "the fixture is single-threaded");
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| st.stress_mt(2, 8)));
    let payload = unwound.expect_err("an ST object must refuse the MT storm");
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or("<non-string payload>");
    assert!(
        message.contains("MT or persistent"),
        "the refusal must name the precondition, got: {message}"
    );
}

#[test]
fn shadow_kills_foreign_pointer() {
    let _g = lock();
    shadow::enable();
    Obj::probe_foreign_pointer();
    let (events, _) = shadow::disable_and_drain();
    assert!(
        events.iter().any(|e| e.kind == EventKind::ForeignPointer),
        "seeded foreign-pointer misuse must be detected"
    );
}

#[test]
fn shadow_quarantine_poisons_headers() {
    let _g = lock();
    shadow::enable();
    let tag = Obj::probe_quarantine_poison();
    let (_, _) = shadow::disable_and_drain();
    assert_eq!(
        tag,
        contract::TAG_RESERVED,
        "quarantined objects read as poisoned"
    );
}

/// Replay determinism: the same operation script yields the same event
/// stream (kinds and provenance tags), independent of addresses.
#[test]
fn shadow_replay_is_deterministic() {
    let _g = lock();
    let script = || {
        shadow::enable();
        let a = Obj::mk_string("replay");
        let b = a.clone_ref();
        let c = Obj::mk_ctor(2, vec![Obj::mk_nat(1)], &[]);
        drop(b);
        drop(c);
        drop(a);
        shadow::disable_and_drain()
    };
    let (run1, live1) = script();
    let (run2, live2) = script();
    assert_eq!(live1, live2);
    assert_eq!(
        run1, run2,
        "event streams must be bit-identical across runs"
    );
}

// ================================================================ C4 probe

/// The Marrow half of the C4 native-ABI probe rig (corpus family C4,
/// plan §18): emits layout and behavior facts as NDJSON when
/// `FLN_C4_EMIT` names an output file. The e2e scenario
/// (`scripts/e2e/marrow_abi_probes.sh`) diffs this against the same facts
/// emitted by a C program compiled against the pinned toolchain's `lean.h`
/// and linked to the real Reference runtime.
#[test]
fn c4_probe_emit_facts() {
    let _g = lock();
    let facts = collect_c4_facts();
    // Internal coherence regardless of emission.
    assert!(!facts.is_empty());
    if let Ok(path) = std::env::var("FLN_C4_EMIT") {
        let mut out = String::new();
        for (k, v) in &facts {
            out.push_str(&format!(
                "{{\"schema\":\"fln-c4-abi-probe/1\",\"probe\":\"{k}\",\"value\":{v}}}\n"
            ));
        }
        std::fs::write(&path, out).expect("write C4 facts");
    }
}

fn collect_c4_facts() -> Vec<(String, i64)> {
    let mut f: Vec<(String, i64)> = Vec::new();
    let mut fact = |k: &str, v: usize| f.push((k.to_string(), i64::try_from(v).expect("fact")));

    // Layout facts: every contract struct, every field, plus sizeof.
    for spec in contract::OBJECT_STRUCTS {
        let (size, fields) = mirror_layout(spec.name);
        fact(&format!("sizeof.{}", spec.name), size);
        for (name, off) in fields {
            fact(&format!("offsetof.{}.{}", spec.name, name), off);
        }
    }

    // Tagged scalars.
    for n in [0usize, 1, 41, 1 << 20] {
        let b = Obj::mk_nat(n);
        fact(&format!("box.{n}.bits"), b.unbox() * 2 + 1);
        fact(&format!("box.{n}.tag"), b.obj_tag());
    }

    // Ctor: header facts + scalar packing + the padded-zero law.
    let c = Obj::mk_ctor(
        7,
        vec![Obj::mk_nat(1), Obj::mk_nat(2)],
        &[0xAB, 0xCD, 0, 0, 0, 0, 0, 0],
    );
    let h = c.header();
    fact("ctor.7_2_8.rc", usize::try_from(h.rc).expect("rc"));
    fact("ctor.7_2_8.cs_sz", usize::from(h.cs_sz));
    fact("ctor.7_2_8.other", usize::from(h.other));
    fact("ctor.7_2_8.tag", usize::from(h.tag));
    fact(
        "ctor.7_2_8.scalar_u64",
        usize::try_from(c.ctor_scalar_u64(16)).expect("scalar"),
    );

    // Padded word: 1 slot + 1 scalar byte -> aligned block, upper bytes zero.
    let p = Obj::mk_ctor(0, vec![Obj::mk_nat(3)], &[0x7F]);
    fact(
        "ctor.padzero.scalar_u64",
        usize::try_from(p.ctor_scalar_u64(8)).expect("pad"),
    );

    // String semantics.
    let s = Obj::mk_string("héllo∀");
    let (size, cap, len, data) = s.string_view();
    fact("string.hello.size", size);
    fact("string.hello.capacity", cap);
    fact("string.hello.length", len);
    fact("string.hello.cs_sz", usize::from(s.header().cs_sz));
    fact("string.hello.byte0", usize::from(data[0]));
    fact("string.hello.nul", usize::from(*data.last().expect("nul")));
    let e = Obj::mk_string("");
    let (size, _, len, _) = e.string_view();
    fact("string.empty.size", size);
    fact("string.empty.length", len);

    // Array / sarray.
    let a = Obj::mk_array(vec![Obj::mk_nat(1), Obj::mk_nat(2), Obj::mk_nat(3)]);
    fact("array.3.size", a.array_view().0);
    fact("array.3.capacity", a.array_view().1);
    fact("array.3.cs_sz", usize::from(a.header().cs_sz));
    let sa = Obj::mk_sarray(4, &[9, 0, 0, 0, 8, 0, 0, 0]);
    fact("sarray.4_2.elem_size", usize::from(sa.header().other));
    fact("sarray.4_2.cs_sz", usize::from(sa.header().cs_sz));

    // Closure.
    let cl = Obj::mk_closure(3, vec![Obj::mk_nat(1)]);
    fact("closure.3_1.arity", usize::from(cl.closure_view().0));
    fact("closure.3_1.num_fixed", usize::from(cl.closure_view().1));
    fact("closure.3_1.cs_sz", usize::from(cl.header().cs_sz));

    // Tri-state RC transitions.
    let r = Obj::mk_string("rc-probe");
    let r2 = r.clone_ref();
    let r3 = r.clone_ref();
    fact(
        "rc.st.after_2inc",
        usize::try_from(r.header().rc).expect("rc"),
    );
    drop(r3);
    fact(
        "rc.st.after_dec",
        usize::try_from(r.header().rc).expect("rc"),
    );
    drop(r2);
    let pers = Obj::mk_string("persist-probe");
    pers.make_persistent();
    fact(
        "rc.persistent.value",
        usize::try_from(pers.header().rc).expect("rc"),
    );
    let keep = pers.clone_ref();
    drop(keep);
    fact(
        "rc.persistent.after_incdec",
        usize::try_from(pers.header().rc).expect("rc"),
    );
    let mt = Obj::mk_string("mt-probe");
    mt.make_mt();
    fact(
        "rc.mt.after_mark",
        usize::try_from(-mt.header().rc).expect("rc"),
    );
    let mtc = mt.clone_ref();
    fact(
        "rc.mt.after_inc",
        usize::try_from(-mt.header().rc).expect("rc"),
    );
    drop(mtc);
    fact(
        "rc.mt.after_dec",
        usize::try_from(-mt.header().rc).expect("rc"),
    );

    f
}

// ================================================================ the C export surface (bead franken_lean-83r)
// Parity of the exported census-signatured wrappers against the internal
// twins, the size-prefixed small heap, and the pin's UTF-8 quirk vectors.
// Panic-message printing is disabled around the panic_fn cases so the suite
// output stays clean; the process-exit behaviors live in the gauntlet lane
// (scripts/e2e/marrow_stage0_gauntlet.sh), not here.

#[test]
fn export_small_heap_prefix_roundtrip() {
    let _g = lock();
    use crate::export::{
        export_lean_alloc_small, export_lean_free_small, export_lean_inc_heartbeat,
        export_lean_small_mem_size, export_mi_free, export_mi_malloc_small,
    };
    let before = crate::membrane::get_num_heartbeats();
    // mi twin: size preserved through the prefix, pointer 8-aligned.
    let p = export_mi_malloc_small(24);
    assert!(!p.is_null());
    assert_eq!(p.addr() % 8, 0, "objects are 8-aligned");
    assert_eq!(export_lean_small_mem_size(p), 24);
    export_mi_free(p);
    // free(NULL) is a no-op, exactly like free.
    export_mi_free(core::ptr::null_mut());
    // malloc(0): unique releasable block.
    let z = export_mi_malloc_small(0);
    assert!(!z.is_null());
    export_mi_free(z);
    assert_eq!(
        crate::membrane::get_num_heartbeats(),
        before,
        "the raw mimalloc shim is downstream of lean.h's explicit bump"
    );
    // The distributed lean.h path performs this exact composition:
    // lean_inc_heartbeat(), then mi_malloc_small(). It must charge once.
    export_lean_inc_heartbeat();
    let composed = export_mi_malloc_small(16);
    assert!(!composed.is_null());
    export_mi_free(composed);
    assert_eq!(
        crate::membrane::get_num_heartbeats(),
        before + 1,
        "the distributed lean.h small-allocation path must not double-charge"
    );
    // SMALL_ALLOCATOR surface: aligned size + slot-idx law.
    let q = export_lean_alloc_small(32, 3);
    assert!(!q.is_null());
    assert_eq!(export_lean_small_mem_size(q), 32);
    export_lean_free_small(q);
    assert_eq!(
        crate::membrane::get_num_heartbeats(),
        before + 2,
        "the small-allocator entry point owns exactly one bump"
    );
}

#[test]
fn small_heap_bins_are_bounded_lifo_and_cross_thread_adoptable() {
    let _g = lock();
    use crate::export::{export_lean_small_mem_size, export_mi_free, export_mi_malloc_small};

    assert_eq!(crate::membrane::small_class_for_test(1), Some((0, 8)));
    assert_eq!(crate::membrane::small_class_for_test(8), Some((0, 8)));
    assert_eq!(crate::membrane::small_class_for_test(9), Some((1, 16)));
    assert_eq!(
        crate::membrane::small_class_for_test(4096),
        Some((511, 4096))
    );
    assert_eq!(crate::membrane::small_class_for_test(4097), None);
    assert!(
        crate::membrane::small_bin_metadata_bytes_for_test() <= 5 * 1024,
        "intrusive heads keep per-thread allocator metadata bounded"
    );

    for size in [1usize, 8, 9, 4095, 4096, 4097] {
        let block = export_mi_malloc_small(size);
        assert!(!block.is_null());
        assert_eq!(
            export_lean_small_mem_size(block),
            u32::try_from(size).expect("test size fits c_uint"),
            "the hidden prefix preserves logical size across every class edge"
        );
        export_mi_free(block);
    }

    let capacity = crate::membrane::small_bin_capacity_for_test();
    let mut held = Vec::new();
    for _ in 0..capacity + 3 {
        let block = export_mi_malloc_small(9);
        assert!(!block.is_null());
        held.push(block);
    }
    assert_eq!(
        crate::membrane::small_bin_depth_for_test(9),
        0,
        "holding more than one full bin drains every prior cached block"
    );

    let recycled = held.pop().expect("one held class-16 block");
    let recycled_address = recycled.addr();
    export_mi_free(recycled);
    assert_eq!(crate::membrane::small_bin_depth_for_test(9), 1);

    let reused = export_mi_malloc_small(15);
    assert_eq!(
        reused.addr(),
        recycled_address,
        "same-class allocation reuses the most recently deferred block"
    );
    assert_eq!(
        export_lean_small_mem_size(reused),
        15,
        "reuse rewrites the logical-size prefix"
    );
    export_mi_free(reused);
    for block in held {
        export_mi_free(block);
    }
    assert_eq!(
        crate::membrane::small_bin_depth_for_test(9),
        capacity,
        "each thread-local class is bounded exactly"
    );

    let cross_thread = export_mi_malloc_small(24);
    assert!(!cross_thread.is_null());
    let cross_thread_address = cross_thread.expose_provenance();
    std::thread::spawn(move || {
        let block =
            core::ptr::with_exposed_provenance_mut::<core::ffi::c_void>(cross_thread_address);
        export_mi_free(block);
        assert_eq!(
            crate::membrane::small_bin_depth_for_test(24),
            1,
            "a foreign-thread release is adopted by the freeing thread"
        );
        let reused = export_mi_malloc_small(17);
        assert_eq!(
            reused.addr(),
            cross_thread_address,
            "the adopting thread owns the next same-class reuse"
        );
        assert_eq!(export_lean_small_mem_size(reused), 17);
        export_mi_free(reused);
    })
    .join()
    .expect("cross-thread small-bin reuse");
}

#[test]
fn export_alloc_object_marks_big_path_and_frees() {
    let _g = lock();
    use crate::export::{export_lean_alloc_object, export_lean_free_object};
    let o = export_lean_alloc_object(64);
    assert!(!o.is_null());
    // Header init through the internal twin, then release through the
    // exported category dispatch.
    // SAFETY: `o` was minted by this crate's own exported allocator and
    // asserted non-null above; the test owns it exclusively until it frees it
    // below, and `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0103
    #[allow(unsafe_code)]
    unsafe {
        assert_eq!(
            (&raw const (*o).m_cs_sz).read(),
            0,
            "big path marks cs_sz=0"
        );
        crate::rc::init_st_header(o, contract::TAG_SCALAR_ARRAY, 1);
        let a = o.cast::<LeanSarrayObject>();
        (&raw mut (*a).m_size).write(0);
        (&raw mut (*a).m_capacity).write(64 - size_of::<LeanSarrayObject>());
    }
    export_lean_free_object(o);
}

#[test]
fn export_string_constructors_match_pin_semantics() {
    let _g = lock();
    use crate::export::{
        export_lean_dec_ref_cold, export_lean_mk_ascii_string_unchecked, export_lean_mk_string,
        export_lean_mk_string_from_bytes, export_lean_object_byte_size,
        export_lean_object_data_byte_size, export_lean_string_eq_cold,
    };
    // SAFETY: every object here is minted by this crate's own constructors from
    // literals that satisfy their contracts, is owned exclusively by this test,
    // and is released through the exported cold path before the block ends;
    // `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0104
    #[allow(unsafe_code)]
    unsafe {
        // Valid UTF-8: codepoints counted, NUL appended, size = bytes + 1.
        let s = export_lean_mk_string(c"h\u{e9}llo".as_ptr());
        let (size, cap, len, bytes) = crate::object::string_fields(s);
        assert_eq!((size, cap, len), (7, 7, 5), "é is two bytes, five chars");
        assert_eq!(&bytes[..6], "héllo".as_bytes());
        assert_eq!(bytes[6], 0);
        assert_eq!(
            export_lean_object_byte_size(s),
            size_of::<LeanStringObject>() + 7
        );
        assert_eq!(
            export_lean_object_data_byte_size(s),
            size_of::<LeanStringObject>() + 7
        );
        // eq_cold: equal bytes true, same-size different bytes false.
        let t = export_lean_mk_string(c"h\u{e9}llo".as_ptr());
        let u = export_lean_mk_string(c"h\u{e9}llp".as_ptr());
        assert!(export_lean_string_eq_cold(s, t));
        assert!(!export_lean_string_eq_cold(s, u));
        // ASCII unchecked: byte count is the codepoint count by fiat.
        let a = export_lean_mk_ascii_string_unchecked(c"abc".as_ptr());
        let (asize, _, alen, _) = crate::object::string_fields(a);
        assert_eq!((asize, alen), (4, 3));
        for o in [s, t, u, a] {
            export_lean_dec_ref_cold(o);
        }
        // Lossy recovery vectors (object.cpp:1989-2012 semantics):
        // one invalid byte mid-string -> U+FFFD, count includes it.
        let v1 = b"ab\xFFcd";
        let r1 = export_lean_mk_string_from_bytes(v1.as_ptr().cast(), v1.len());
        let (_, _, l1, b1) = crate::object::string_fields(r1);
        assert_eq!(&b1[..b1.len() - 1], "ab\u{FFFD}cd".as_bytes());
        assert_eq!(l1, 5);
        // stray continuation at the start.
        let v2 = b"\x80abc";
        let r2 = export_lean_mk_string_from_bytes(v2.as_ptr().cast(), v2.len());
        let (_, _, l2, b2) = crate::object::string_fields(r2);
        assert_eq!(&b2[..b2.len() - 1], "\u{FFFD}abc".as_bytes());
        assert_eq!(l2, 4);
        // truncated 4-byte sequence: continuations are skipped as one char.
        let v3 = b"\xF0\x9F\x92";
        let r3 = export_lean_mk_string_from_bytes(v3.as_ptr().cast(), v3.len());
        let (_, _, l3, b3) = crate::object::string_fields(r3);
        assert_eq!(&b3[..b3.len() - 1], "\u{FFFD}".as_bytes());
        assert_eq!(l3, 1);
        for o in [r1, r2, r3] {
            export_lean_dec_ref_cold(o);
        }
    }
}

#[test]
fn export_utf8_strlen_quirks_are_bug_compatible() {
    let _g = lock();
    use crate::export::{export_lean_utf8_n_strlen, export_lean_utf8_strlen};
    // Valid text: codepoints.
    assert_eq!(export_lean_utf8_strlen(c"h\u{e9}llo".as_ptr()), 5);
    assert_eq!(export_lean_utf8_strlen(c"".as_ptr()), 0);
    // The pin's quirk (utf8.cpp:29-32): 0xFF is size 1, so garbage counts.
    let g1 = b"\xFFabc";
    assert_eq!(export_lean_utf8_n_strlen(g1.as_ptr().cast(), g1.len()), 4);
    // A lead byte overstating its size jumps the cursor PAST the buffer end
    // and the walk still terminates with the partial count (bounded variant).
    let g2 = b"a\xC3";
    assert_eq!(export_lean_utf8_n_strlen(g2.as_ptr().cast(), g2.len()), 2);
    let g3 = b"ab\xE2\x82";
    assert_eq!(export_lean_utf8_n_strlen(g3.as_ptr().cast(), g3.len()), 3);
}

#[test]
fn export_panic_fn_balances_ownership_and_returns_default() {
    let _g = lock();
    use crate::export::{
        export_lean_dec_ref_cold, export_lean_mk_string, export_lean_panic_fn,
        export_lean_panic_fn_borrowed, export_lean_set_panic_messages,
    };
    // Quiet: the message plane is exercised by the gauntlet lane with real
    // process boundaries; here we assert the ownership contract only.
    export_lean_set_panic_messages(false);
    // SAFETY: both objects are minted by this crate's own constructors and owned
    // exclusively by this test; the ownership contract under assertion is
    // exactly which of them the exported panic path consumes, and each is
    // released once. `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0105
    #[allow(unsafe_code)]
    unsafe {
        let default_val = crate::object::alloc_ctor(0, 0, 0);
        let msg = export_lean_mk_string(c"boom".as_ptr());
        // Consuming form: msg is freed, default passes through untouched.
        let out = export_lean_panic_fn(default_val, msg);
        assert_eq!(out, default_val);
        assert_eq!(crate::rc::read_header(default_val).rc, 1);
        // Borrowed form: default retained before delegation.
        let msg2 = export_lean_mk_string(c"boom2".as_ptr());
        let out2 = export_lean_panic_fn_borrowed(default_val, msg2);
        assert_eq!(out2, default_val);
        assert_eq!(crate::rc::read_header(default_val).rc, 2);
        crate::rc::dec_ref(default_val);
        export_lean_dec_ref_cold(default_val);
    }
    export_lean_set_panic_messages(true);
}

#[test]
fn export_heartbeat_is_thread_local_counting() {
    let _g = lock();
    use crate::export::{
        export_lean_big_uint64_to_nat, export_lean_dec_ref_cold, export_lean_inc_heartbeat,
        export_lean_io_get_num_heartbeats, export_lean_io_set_heartbeats,
        export_lean_uint64_of_big_nat,
    };

    let unit = export_lean_io_set_heartbeats(tagged::boxi(0));
    assert_eq!(tagged::unbox(unit), 0);
    for _ in 0..5 {
        export_lean_inc_heartbeat();
    }
    assert_eq!(crate::membrane::get_num_heartbeats(), 5);
    assert_eq!(tagged::unbox(export_lean_io_get_num_heartbeats()), 5);

    // A fresh thread starts its own counter (LEAN_THREAD_VALUE semantics).
    std::thread::spawn(|| {
        assert_eq!(tagged::unbox(export_lean_io_get_num_heartbeats()), 0);
        export_lean_inc_heartbeat();
        assert_eq!(tagged::unbox(export_lean_io_get_num_heartbeats()), 1);
        let unit = export_lean_io_set_heartbeats(tagged::boxi(9));
        assert_eq!(tagged::unbox(unit), 0);
        assert_eq!(tagged::unbox(export_lean_io_get_num_heartbeats()), 9);
    })
    .join()
    .expect("heartbeat thread");
    assert_eq!(crate::membrane::get_num_heartbeats(), 5);

    // The u64 boundary takes the heap-Nat arm. The getter snapshots first,
    // then its returned big Nat is itself one small allocation: MAX wraps to
    // zero in the live counter while the returned value remains MAX.
    let maximum = export_lean_big_uint64_to_nat(u64::MAX);
    let unit = export_lean_io_set_heartbeats(maximum);
    assert_eq!(tagged::unbox(unit), 0);
    let snapshot = export_lean_io_get_num_heartbeats();
    assert!(!tagged::is_scalar(snapshot));
    assert_eq!(export_lean_uint64_of_big_nat(snapshot), u64::MAX);
    assert_eq!(crate::membrane::get_num_heartbeats(), 0);
    export_lean_dec_ref_cold(snapshot);

    let unit = export_lean_io_set_heartbeats(tagged::boxi(0));
    assert_eq!(tagged::unbox(unit), 0);
}

#[test]
fn marrow_small_objects_charge_and_big_objects_do_not() {
    let _g = lock();
    let before = crate::membrane::get_num_heartbeats();

    let small = Obj::mk_ref(Obj::mk_nat(7));
    assert_eq!(
        crate::membrane::get_num_heartbeats(),
        before + 1,
        "a Marrow small-object constructor charges one allocation tick"
    );
    drop(small);

    let big = Obj::mk_array(Vec::new());
    assert_eq!(
        crate::membrane::get_num_heartbeats(),
        before + 1,
        "the Reference heartbeat law does not charge a big allocation"
    );
    drop(big);
}

#[test]
fn export_dec_ref_cold_tears_down_graphs() {
    let _g = lock();
    use crate::export::export_lean_dec_ref_cold;
    // SAFETY: the whole object graph is built here by this crate's own
    // constructors and is owned exclusively by this test; the single
    // `dec_ref_cold` at the root is the only release, which is the property
    // under test. `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0106
    #[allow(unsafe_code)]
    unsafe {
        // ctor(ctor(string), string) torn down through the exported cold path.
        let inner_s = crate::object::mk_string_unchecked(b"leaf", 4);
        let inner = crate::object::alloc_ctor(1, 1, 0);
        crate::object::ctor_set(inner, 0, inner_s);
        let outer_s = crate::object::mk_string_unchecked(b"leaf2", 5);
        let outer = crate::object::alloc_ctor(0, 2, 0);
        crate::object::ctor_set(outer, 0, inner);
        crate::object::ctor_set(outer, 1, outer_s);
        export_lean_dec_ref_cold(outer);
    }
}

#[test]
fn export_mark_persistent_via_c_surface() {
    let _g = lock();
    use crate::export::export_lean_mark_persistent;
    // SAFETY: the string and ctor are minted by this crate's own constructors
    // and owned exclusively by this test; marking them persistent is the
    // operation under test and is applied to objects this block created.
    // `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0107
    #[allow(unsafe_code)]
    unsafe {
        let s = crate::object::mk_string_unchecked(b"p", 1);
        let o = crate::object::alloc_ctor(0, 1, 0);
        crate::object::ctor_set(o, 0, s);
        export_lean_mark_persistent(o);
        assert_eq!(crate::rc::read_header(o).rc, 0);
        assert_eq!(crate::rc::read_header(s).rc, 0);
        // Persistent objects are never freed; the blocks leak by design here
        // exactly as compact-region residents would.
    }
}

#[test]
fn export_platform_and_byte_array_roundtrip() {
    let _g = lock();
    use crate::export::{
        export_lean_dec_ref_cold, export_lean_mk_string, export_lean_string_from_utf8_unchecked,
        export_lean_string_to_utf8, export_lean_system_platform_nbits,
    };
    assert_eq!(
        tagged::unbox(export_lean_system_platform_nbits(tagged::boxi(0))),
        64
    );
    // SAFETY: the string is minted from a NUL-terminated literal through this
    // crate's own exported constructor and is owned exclusively by this test;
    // each conversion in the roundtrip consumes or borrows exactly as its
    // contract states. `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0112
    #[allow(unsafe_code)]
    unsafe {
        // String -> ByteArray (borrowed) -> String (consuming) roundtrip.
        let s = export_lean_mk_string(c"h\u{e9}llo".as_ptr());
        let ba = export_lean_string_to_utf8(s);
        let (elem, size, _cap, _) = crate::object::sarray_fields(ba);
        assert_eq!((elem, size), (1, 6), "content bytes only, no NUL");
        let s2 = export_lean_string_from_utf8_unchecked(ba);
        let (sz2, _, len2, bytes2) = crate::object::string_fields(s2);
        assert_eq!((sz2, len2), (7, 5));
        assert_eq!(&bytes2[..6], "héllo".as_bytes());
        export_lean_dec_ref_cold(s);
        export_lean_dec_ref_cold(s2);
    }
}

// ================================================================ slice 2: array/byte-array/string-conversion exports

#[test]
fn export_array_list_roundtrip_and_push_laws() {
    let _g = lock();
    use crate::export::{
        export_lean_array_mk, export_lean_array_push, export_lean_array_to_list,
        export_lean_dec_ref_cold,
    };
    // SAFETY: the list is built here from boxed scalars, so every node is this
    // test's own and exclusively owned; the Array/List conversions consume and
    // produce objects of the shapes their contracts require, and the result is
    // released once. `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0131
    #[allow(unsafe_code)]
    unsafe {
        // List [10, 20, 30] (boxed) -> Array -> List roundtrip.
        let mut lst = tagged::boxi(0);
        for v in [30usize, 20, 10] {
            let cell = crate::object::alloc_ctor(1, 2, 0);
            crate::object::ctor_set(cell, 0, tagged::boxi(v));
            crate::object::ctor_set(cell, 1, lst);
            lst = cell;
        }
        let a = export_lean_array_mk(lst);
        let (sz, cap) = crate::object::array_fields(a);
        assert_eq!((sz, cap), (3, 3));
        assert_eq!(tagged::unbox(crate::object::array_get(a, 0)), 10);
        assert_eq!(tagged::unbox(crate::object::array_get(a, 2)), 30);
        let back = export_lean_array_to_list(a);
        let mut cur = back;
        let mut seen = Vec::new();
        while !tagged::is_scalar(cur) {
            seen.push(tagged::unbox(crate::object::ctor_get(cur, 0)));
            cur = crate::object::ctor_get(cur, 1);
        }
        assert_eq!(seen, vec![10, 20, 30]);
        export_lean_dec_ref_cold(back);

        // Push growth law from (0,0): (cap+1)*2 exactly when full (exclusive).
        let mut arr = crate::object::alloc_array(0, 0);
        for (i, expect_cap) in [(0usize, 2usize), (1, 2), (2, 6)] {
            arr = export_lean_array_push(arr, tagged::boxi(i));
            let (s, c) = crate::object::array_fields(arr);
            assert_eq!((s, c), (i + 1, expect_cap), "push {i}");
        }
        // Shared push: retain, push -> nonlinear copy, original untouched.
        crate::rc::inc_ref_n(arr, 1);
        let pushed = export_lean_array_push(arr, tagged::boxi(9));
        assert_ne!(pushed, arr, "shared push copies");
        assert_eq!(crate::object::array_fields(arr).0, 3);
        let (psz, pcap) = crate::object::array_fields(pushed);
        assert_eq!((psz, pcap), (4, 14), "nonlinear expand law (6+1)*2");
        export_lean_dec_ref_cold(pushed);
        export_lean_dec_ref_cold(arr);
    }
}

#[test]
fn export_byte_array_families_match_pin_laws() {
    let _g = lock();
    use crate::export::{
        export_lean_byte_array_data, export_lean_byte_array_mk, export_lean_byte_array_push,
        export_lean_dec_ref_cold,
    };
    // SAFETY: the array is allocated here with matching size and capacity and
    // every slot is written before it is read; the ByteArray conversions
    // consume and produce objects of the shapes their contracts require.
    // `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0132
    #[allow(unsafe_code)]
    unsafe {
        // Array of boxed bytes -> ByteArray -> Array roundtrip.
        let a = crate::object::alloc_array(3, 3);
        for (i, b) in [7usize, 8, 9].into_iter().enumerate() {
            crate::object::array_set_core(a, i, tagged::boxi(b));
        }
        let ba = export_lean_byte_array_mk(a);
        let (elem, sz, _, data) = crate::object::sarray_fields(ba);
        assert_eq!((elem, sz), (1, 3));
        assert_eq!(
            core::slice::from_raw_parts(data, 3),
            &[7, 8, 9],
            "byte content"
        );
        let arr2 = export_lean_byte_array_data(ba);
        assert_eq!(tagged::unbox(crate::object::array_get(arr2, 1)), 8);
        export_lean_dec_ref_cold(arr2);

        // Push growth: (size+1)*2 capacity when full.
        let mut b = crate::object::alloc_sarray(1, 0, 0);
        b = export_lean_byte_array_push(b, 0xAB);
        let (_, s1, c1, _) = crate::object::sarray_fields(b);
        assert_eq!((s1, c1), (1, 2), "min_cap*2 growth");
        b = export_lean_byte_array_push(b, 0xCD);
        let (_, s2, c2, d2) = crate::object::sarray_fields(b);
        assert_eq!((s2, c2), (2, 2));
        assert_eq!(core::slice::from_raw_parts(d2, 2), &[0xAB, 0xCD]);
        export_lean_dec_ref_cold(b);
    }
}

#[test]
fn export_string_list_roundtrip_and_hash() {
    let _g = lock();
    use crate::export::{
        export_lean_dec_ref_cold, export_lean_mk_string, export_lean_string_data,
        export_lean_string_eq_cold, export_lean_string_hash, export_lean_string_mk,
    };
    // SAFETY: the string is minted from a NUL-terminated literal through this
    // crate's own exported constructor; the extra reference this test takes is
    // matched by the releases below, so every borrow is live for its use.
    // `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0133
    #[allow(unsafe_code)]
    unsafe {
        let s = export_lean_mk_string(c"h\u{e9}llo".as_ptr());
        crate::rc::inc_ref_n(s, 1);
        let lst = export_lean_string_data(s); // consumes one ref
        let mut codes = Vec::new();
        let mut cur = lst;
        while !tagged::is_scalar(cur) {
            codes.push(tagged::unbox(crate::object::ctor_get(cur, 0)) as u32);
            cur = crate::object::ctor_get(cur, 1);
        }
        assert_eq!(codes, vec![0x68, 0xE9, 0x6C, 0x6C, 0x6F]);
        let s2 = export_lean_string_mk(lst); // consumes the list
        assert!(export_lean_string_eq_cold(s, s2));
        // Hash: deterministic, content-sensitive (exact parity vs the
        // Reference is pinned by the gauntlet differential).
        let t = export_lean_mk_string(c"h\u{e9}llp".as_ptr());
        assert_eq!(export_lean_string_hash(s), export_lean_string_hash(s2));
        assert_ne!(export_lean_string_hash(s), export_lean_string_hash(t));
        for o in [s, s2, t] {
            export_lean_dec_ref_cold(o);
        }
    }
}

// ================================================================ slice 3: bignum-backed Nat families

#[test]
fn export_nat_big_arithmetic_normalization_and_truncation() {
    let _g = lock();
    use crate::export::{
        export_lean_big_uint64_to_nat, export_lean_big_usize_to_nat, export_lean_cstr_to_nat,
        export_lean_dec_ref_cold, export_lean_nat_big_add, export_lean_nat_big_div,
        export_lean_nat_big_eq, export_lean_nat_big_le, export_lean_nat_big_lt,
        export_lean_nat_big_mod, export_lean_nat_big_mul, export_lean_nat_big_sub,
        export_lean_nat_overflow_mul, export_lean_string_of_usize, export_lean_uint8_of_big_nat,
        export_lean_uint64_of_big_nat, export_lean_usize_of_big_nat,
    };
    // SAFETY: every value here is either a boxed scalar, which carries no
    // pointer, or an mpz minted by this crate's own constructor and owned
    // exclusively by this test; each arithmetic entry point is handed operands
    // of the shape it documents. `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0160
    #[allow(unsafe_code)]
    unsafe {
        let mpz_copy = |object| {
            let (alloc, size, pointer, live) = crate::object::mpz_fields(object);
            assert!(alloc >= 0 && live <= alloc as usize);
            let limbs = if live == 0 {
                Vec::new()
            } else {
                assert!(!pointer.is_null());
                core::slice::from_raw_parts(pointer, live).to_vec()
            };
            (size, limbs)
        };

        // Boundary law: MAX_SMALL_NAT boxes, MAX_SMALL_NAT+1 mints mpz.
        let max_small = tagged::MAX_SMALL_NAT;
        assert!(tagged::is_scalar(export_lean_big_usize_to_nat(max_small)));
        let big = export_lean_big_uint64_to_nat(u64::MAX);
        assert!(!tagged::is_scalar(big), "2^64-1 exceeds MAX_SMALL_NAT");
        let (sz, limbs) = mpz_copy(big);
        assert_eq!((sz, limbs.as_slice()), (1, &[u64::MAX][..]));

        // add: big + 1 = 2^64 (stays mpz, _core arm).
        let big2 = export_lean_nat_big_add(big, tagged::boxi(1));
        let (sz2, limbs2) = mpz_copy(big2);
        assert_eq!((sz2, limbs2.as_slice()), (2, &[0, 1][..]));

        // sub: 2^64 - (2^64-1) = 1 -> NORMALIZED to a boxed scalar.
        let one = export_lean_nat_big_sub(big2, big);
        assert!(tagged::is_scalar(one));
        assert_eq!(tagged::unbox(one), 1);
        // scalar - big = 0 (caller-guaranteed arm).
        assert_eq!(
            tagged::unbox(export_lean_nat_big_sub(tagged::boxi(5), big)),
            0
        );

        // mul: 0 * big normalizes to 0; big * big stays mpz.
        assert_eq!(
            tagged::unbox(export_lean_nat_big_mul(tagged::boxi(0), big)),
            0
        );
        let sq = export_lean_nat_big_mul(big, big);
        assert!(!tagged::is_scalar(sq));

        // div: scalar/big = 0; x/0 returns the boxed-zero divisor; big/big.
        assert_eq!(
            tagged::unbox(export_lean_nat_big_div(tagged::boxi(7), big)),
            0
        );
        assert_eq!(
            tagged::unbox(export_lean_nat_big_div(big, tagged::boxi(0))),
            0
        );
        assert_eq!(tagged::unbox(export_lean_nat_big_div(big2, big)), 1);

        // mod: scalar%big = the scalar; x%0 returns the RETAINED input.
        assert_eq!(
            tagged::unbox(export_lean_nat_big_mod(tagged::boxi(9), big)),
            9
        );
        let before = crate::rc::read_header(big).rc;
        let same = export_lean_nat_big_mod(big, tagged::boxi(0));
        assert_eq!(same, big);
        assert_eq!(crate::rc::read_header(big).rc, before + 1, "x%0 retains");
        crate::rc::dec_ref(big);
        assert_eq!(tagged::unbox(export_lean_nat_big_mod(big2, big)), 1);

        // comparisons: representation-invariant arms + real big compares.
        assert!(!export_lean_nat_big_eq(tagged::boxi(3), big));
        assert!(export_lean_nat_big_eq(big, big));
        assert!(export_lean_nat_big_le(tagged::boxi(3), big));
        assert!(!export_lean_nat_big_le(big, tagged::boxi(3)));
        assert!(export_lean_nat_big_lt(big, big2) && !export_lean_nat_big_lt(big2, big));

        // overflow_mul: 2^40 * 2^40 = 2^80.
        let of = export_lean_nat_overflow_mul(1 << 40, 1 << 40);
        let (osz, olimbs) = mpz_copy(of);
        assert_eq!((osz, olimbs.as_slice()), (2, &[0, 1 << 16][..]));

        // cstr parse: small and 2^128 + 1.
        assert_eq!(tagged::unbox(export_lean_cstr_to_nat(c"123".as_ptr())), 123);
        let c128 = export_lean_cstr_to_nat(c"340282366920938463463374607431768211457".as_ptr());
        let (csz, climbs) = mpz_copy(c128);
        assert_eq!((csz, climbs.as_slice()), (3, &[1, 0, 1][..]));

        // truncations: lowest limb / low bits.
        assert_eq!(export_lean_uint64_of_big_nat(big), u64::MAX);
        assert_eq!(export_lean_uint8_of_big_nat(big2), 0);
        assert_eq!(export_lean_usize_of_big_nat(c128), 1);

        // string_of_usize.
        let s = export_lean_string_of_usize(9007199254740993);
        let (ssz, _, slen, sbytes) = crate::object::string_fields(s);
        assert_eq!((ssz, slen), (17, 16));
        assert_eq!(&sbytes[..16], b"9007199254740993");

        for o in [big, big2, sq, of, c128, s] {
            export_lean_dec_ref_cold(o);
        }
    }
}

#[test]
fn export_name_eq_walks_prefixes_exactly() {
    let _g = lock();
    use crate::export::{
        export_lean_big_uint64_to_nat, export_lean_dec_ref_cold, export_lean_name_eq,
    };
    // SAFETY: the Name node is built here with the field and scalar counts the
    // ctor layout requires, so the cached-hash slot this test reads is inside
    // the allocation, and the graph is owned exclusively by this test and
    // released once. `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0161
    #[allow(unsafe_code)]
    unsafe {
        // Name.str node: ctor tag 1, fields (parent, string), cached hash at
        // scalar offset 16 (lean_name_hash_ptr law).
        let mk_str_name = |parent: *mut LeanObject, text: &[u8], hash: u64| {
            let s = crate::object::mk_string_unchecked(text, text.len());
            let n = crate::object::alloc_ctor(1, 2, 8);
            crate::object::ctor_set(n, 0, parent);
            crate::object::ctor_set(n, 1, s);
            crate::object::ctor_set_scalar::<u64>(n, 16, hash);
            n
        };
        let anon = tagged::boxi(0);
        let n1 = mk_str_name(anon, b"foo", 0x1234);
        let n2 = mk_str_name(anon, b"foo", 0x1234);
        let n3 = mk_str_name(anon, b"bar", 0x1234); // same hash, different text
        let n4 = mk_str_name(anon, b"foo", 0x9999); // different hash: fast reject
        assert_eq!(export_lean_name_eq(n1, n1), 1, "pointer fast path");
        assert_eq!(export_lean_name_eq(n1, n2), 1, "structural equality");
        assert_eq!(export_lean_name_eq(n1, n3), 0, "text differs despite hash");
        assert_eq!(export_lean_name_eq(n1, n4), 0, "hash fast reject");
        assert_eq!(export_lean_name_eq(anon, n1), 0, "scalar vs node");

        // Name.num node (tag 2) with a BIG Nat component: the walk must use
        // the big-eq arm.
        let big_a = export_lean_big_uint64_to_nat(u64::MAX);
        let big_b = export_lean_big_uint64_to_nat(u64::MAX);
        let mk_num_name = |parent: *mut LeanObject, nat: *mut LeanObject, hash: u64| {
            let n = crate::object::alloc_ctor(2, 2, 8);
            crate::object::ctor_set(n, 0, parent);
            crate::object::ctor_set(n, 1, nat);
            crate::object::ctor_set_scalar::<u64>(n, 16, hash);
            n
        };
        let m1 = mk_num_name(n1, big_a, 0x77);
        let m2 = mk_num_name(n2, big_b, 0x77);
        assert_eq!(export_lean_name_eq(m1, m2), 1, "big-nat component + prefix");
        for o in [m1, m2] {
            export_lean_dec_ref_cold(o);
        }
    }
}

// ================================================================ slice 4: apply membrane + once cells

/// Closure targets for the apply tests: real extern "C" functions whose
/// pointers live in closure objects exactly as compiled Lean code's would.
mod apply_targets {
    use crate::layout::LeanObject;
    use crate::tagged;

    pub(crate) extern "C" fn add2(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
        tagged::boxi(tagged::unbox(a) + tagged::unbox(b))
    }
    pub(crate) extern "C" fn pair_sum3(
        a: *mut LeanObject,
        b: *mut LeanObject,
        c: *mut LeanObject,
    ) -> *mut LeanObject {
        tagged::boxi(tagged::unbox(a) * 100 + tagged::unbox(b) * 10 + tagged::unbox(c))
    }
    /// arity-1 returning a NEW closure (for the over-application arm).
    pub(crate) extern "C" fn make_adder(a: *mut LeanObject) -> *mut LeanObject {
        // SAFETY: reached only as a closure target invoked by the apply arms in
        // this module, which pass `a` as an owned argument. The closure is
        // allocated here with the arity and fixed-argument count `add2`
        // declares, and takes ownership of `a` in slot 0.
        // UNSAFE-LEDGER: FLN-UL-0176
        #[allow(unsafe_code)]
        unsafe {
            let c = crate::object::alloc_closure(add2 as *mut core::ffi::c_void, 2, 1);
            crate::object::closure_set(c, 0, a);
            c
        }
    }
}

#[test]
fn export_apply_arms_match_generated_semantics() {
    let _g = lock();
    use crate::export::{export_lean_apply_1, export_lean_apply_2, export_lean_apply_3};
    // SAFETY: each closure is allocated here with an arity and fixed-argument
    // count matching the `extern "C"` target it wraps, which is what makes the
    // apply arms well-formed; every closure and result is owned exclusively by
    // this test. `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0177
    #[allow(unsafe_code)]
    unsafe {
        // Exact application, no fixed args.
        let f = crate::object::alloc_closure(apply_targets::add2 as *mut core::ffi::c_void, 2, 0);
        let r = export_lean_apply_2(f, tagged::boxi(30), tagged::boxi(12));
        assert_eq!(tagged::unbox(r), 42);

        // Under-application: fix one arg, then exact application of the rest.
        let f =
            crate::object::alloc_closure(apply_targets::pair_sum3 as *mut core::ffi::c_void, 3, 0);
        let g = export_lean_apply_1(f, tagged::boxi(1)); // fixes a=1
        let h = crate::rc::read_header(g);
        assert_eq!(h.tag, contract::TAG_CLOSURE, "under-application curries");
        let r = export_lean_apply_2(g, tagged::boxi(2), tagged::boxi(3));
        assert_eq!(tagged::unbox(r), 123);

        // Exact application through fixed args on a SHARED closure: fixed
        // args are retained, the closure survives.
        let f =
            crate::object::alloc_closure(apply_targets::pair_sum3 as *mut core::ffi::c_void, 3, 1);
        let boxed = crate::object::mk_string_unchecked(b"witness", 7); // rc-carrying fixed arg
        crate::object::closure_set(f, 0, boxed);
        crate::rc::inc_ref_n(f, 1); // shared
        // pair_sum3 unboxes its first arg; use a boxed scalar instead:
        // rebuild with scalar fixed arg for the arithmetic, keep `boxed`
        // reachable via a second closure slot pattern instead.
        crate::rc::dec_ref(f); // undo share of the string-carrying probe
        crate::rc::dec_ref(f); // release it entirely (string freed too)
        let f =
            crate::object::alloc_closure(apply_targets::pair_sum3 as *mut core::ffi::c_void, 3, 1);
        crate::object::closure_set(f, 0, tagged::boxi(9));
        crate::rc::inc_ref_n(f, 1); // rc = 2: shared application path
        let r = export_lean_apply_2(f, tagged::boxi(8), tagged::boxi(7));
        assert_eq!(tagged::unbox(r), 987);
        assert_eq!(
            crate::rc::read_header(f).rc,
            1,
            "shared apply yields one ref"
        );
        crate::rc::dec_ref(f);

        // Over-application: arity-1 closure applied to two args — curry
        // then re-apply (apply.cpp else-if arm).
        let f =
            crate::object::alloc_closure(apply_targets::make_adder as *mut core::ffi::c_void, 1, 0);
        let r = export_lean_apply_2(f, tagged::boxi(40), tagged::boxi(2));
        assert_eq!(tagged::unbox(r), 42);

        // Erased proof: scalar f returns itself, args dropped.
        let s = crate::object::mk_string_unchecked(b"dropme", 6);
        let r = export_lean_apply_3(tagged::boxi(0), s, tagged::boxi(1), tagged::boxi(2));
        assert_eq!(tagged::unbox(r), 0);
    }
}

#[test]
fn export_once_cells_initialize_exactly_once() {
    let _g = lock();
    use crate::export::{export_lean_obj_once_cold, export_lean_uint64_once_cold};
    use std::sync::atomic::{AtomicU64, Ordering as O};
    static CALLS: AtomicU64 = AtomicU64::new(0);
    extern "C" fn init_u64() -> u64 {
        CALLS.fetch_add(1, O::SeqCst);
        0xFEED
    }
    extern "C" fn init_obj() -> *mut LeanObject {
        // SAFETY: reached only as the once-initialisation target invoked by the
        // test below. It takes no arguments and mints a fresh string from a
        // static literal whose length it states correctly, so the constructor's
        // contract is satisfied by construction.
        // UNSAFE-LEDGER: FLN-UL-0178
        #[allow(unsafe_code)]
        unsafe {
            crate::object::mk_string_unchecked(b"once", 4)
        }
    }
    // SAFETY: `cell` is a local array owned by this test, so the pointer handed
    // to the once-initialisation entry point is valid, aligned and exclusively
    // borrowed for the call; it stands in for the C-side static and outlives
    // every use here. `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0179
    #[allow(unsafe_code)]
    unsafe {
        // The C-side static cell: {state: i32, lock: i32} zeroed.
        let mut cell = [0i32; 2];
        let mut slot = 0u64;
        CALLS.store(0, O::SeqCst);
        let a = export_lean_uint64_once_cold(&raw mut slot, (&raw mut cell).cast(), init_u64);
        let b = export_lean_uint64_once_cold(&raw mut slot, (&raw mut cell).cast(), init_u64);
        assert_eq!((a, b, slot), (0xFEED, 0xFEED, 0xFEED));
        assert_eq!(CALLS.load(O::SeqCst), 1, "initializer ran exactly once");
        assert_eq!(cell, [1, 0], "state set, lock released");

        // Object cells persist their graph (rc = 0).
        let mut ocell = [0i32; 2];
        let mut oslot: *mut LeanObject = core::ptr::null_mut();
        let o = export_lean_obj_once_cold(&raw mut oslot, (&raw mut ocell).cast(), init_obj);
        assert_eq!(o, oslot);
        assert_eq!(
            crate::rc::read_header(o).rc,
            0,
            "once objects are persistent"
        );
    }
}

// ---------------------------------------------------------------------------
// G0-3: the closures-corpus semantics through the SAFE surface, with the RC
// shadow asserting balance per cell (bead franken_lean-7xe; the raw arms are
// 83r slice 4's, held by export_apply_arms_match_generated_semantics — these
// cells hold the covenant surface and acceptance (c) in the same breath).
// ---------------------------------------------------------------------------

mod corpus_targets {
    use crate::layout::LeanObject;
    use crate::tagged;

    /// `addN`'s body under the boxed convention: `fun n x => x + n` at
    /// saturation (fixed `n`, applied `x`).
    pub(crate) extern "C" fn add2(n: *mut LeanObject, x: *mut LeanObject) -> *mut LeanObject {
        tagged::boxi(tagged::unbox(n) + tagged::unbox(x))
    }

    /// `(· * 2)`.
    pub(crate) extern "C" fn double(x: *mut LeanObject) -> *mut LeanObject {
        tagged::boxi(tagged::unbox(x) * 2)
    }

    /// `fun x y z => x * y + z` — the corpus's ternary lambda.
    pub(crate) extern "C" fn mul_add3(
        x: *mut LeanObject,
        y: *mut LeanObject,
        z: *mut LeanObject,
    ) -> *mut LeanObject {
        tagged::boxi(tagged::unbox(x) * tagged::unbox(y) + tagged::unbox(z))
    }
}

#[test]
fn handle_apply_reproduces_the_closures_corpus_semantics_with_rc_balance() {
    let _g = lock();
    use crate::handle::Obj;
    shadow::enable();
    {
        // corpus closures.lean line 3: `compose (addN 5) (· * 2) 10` = 25.
        // compose = fun f g x => f (g x), evaluated by chaining the safe
        // surface exactly as the corpus's saturated call tree does.
        let add5 = Obj::mk_closure_fn2(corpus_targets::add2, vec![Obj::mk_nat(5)]);
        let doubled =
            Obj::mk_closure_fn1(corpus_targets::double, vec![]).apply(vec![Obj::mk_nat(10)]);
        let composed = add5.apply(vec![doubled]);
        assert_eq!(composed.unbox(), 25, "compose (addN 5) (.*2) 10");

        // corpus line 4 shape: under-application curries — `addN 100` alone is
        // a closure with one fixed slot, and applying it later completes.
        let add100 =
            Obj::mk_closure_fn2(corpus_targets::add2, vec![]).apply(vec![Obj::mk_nat(100)]);
        assert!(!add100.is_scalar(), "under-application yields a closure");
        assert_eq!(
            add100.header().tag,
            crate::contract::TAG_CLOSURE,
            "curried value is a closure object"
        );
        assert_eq!(
            add100.apply(vec![Obj::mk_nat(4)]).unbox(),
            104,
            "addN 100 applied to 4"
        );

        // corpus line 5: `(fun x y z => x * y + z) 2 3 4` = 10 — saturation in
        // one call, and the same result arg-by-arg (over-application re-entry
        // through the chunked safe path).
        let f3 = Obj::mk_closure_fn3(corpus_targets::mul_add3, vec![]);
        assert_eq!(
            f3.apply(vec![Obj::mk_nat(2), Obj::mk_nat(3), Obj::mk_nat(4)])
                .unbox(),
            10
        );
        let g3 = Obj::mk_closure_fn3(corpus_targets::mul_add3, vec![]);
        assert_eq!(
            g3.apply(vec![Obj::mk_nat(2)])
                .apply(vec![Obj::mk_nat(3)])
                .apply(vec![Obj::mk_nat(4)])
                .unbox(),
            10,
            "one-at-a-time currying agrees with saturation"
        );
    }
    // Acceptance (c)'s instrument: every closure allocated above was freed
    // exactly once — no leak, no double-free — under the debug ownership
    // shadow. Scalars are unboxed and never enter the shadow, so live=0 is
    // the whole balance claim.
    let (_events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "RC balance: every apply cell freed its objects");
}

#[test]
fn handle_apply_reproduces_the_arrays_and_strings_corpus_slices_with_rc_balance() {
    let _g = lock();
    use crate::handle::Obj;
    shadow::enable();
    {
        // arrays.lean line 3 shape: `#[1,2,3,4].map (· * 2) |>.foldl (· + ·) 0`
        // = 20 — map as apply-per-element through the safe surface, fold as a
        // chained binary apply, exactly Golem's dispatch shape.
        let arr = Obj::mk_array(vec![
            Obj::mk_nat(1),
            Obj::mk_nat(2),
            Obj::mk_nat(3),
            Obj::mk_nat(4),
        ]);
        let (size, capacity) = arr.array_view();
        assert_eq!((size, capacity), (4, 4), "capacity == size by construction");
        let mut mapped = Vec::new();
        for i in 0..size {
            let doubler = Obj::mk_closure_fn1(corpus_targets::double, vec![]);
            mapped.push(doubler.apply(vec![arr.array_child(i)]));
        }
        let mut acc = Obj::mk_nat(0);
        for m in mapped {
            let adder = Obj::mk_closure_fn2(corpus_targets::add2, vec![]);
            acc = adder.apply(vec![acc, m]);
        }
        assert_eq!(acc.unbox(), 20, "map-then-fold over the ABI array");

        // strings.lean semantics natively: the UTF-8 length law ("héllo" is 5
        // chars / 6 bytes, m_size includes NUL) and append reproducing the
        // corpus's byte-and-char accounting.
        let s = Obj::mk_string("héllo");
        let (m_size, m_capacity, m_length, bytes) = s.string_view();
        assert_eq!(m_length, 5, "char length (the corpus's .length observable)");
        assert_eq!(m_size, 7, "byte size includes the NUL");
        assert!(m_capacity >= m_size);
        assert_eq!(&bytes[..6], "héllo".as_bytes());
        let appended = Obj::mk_string(&format!("{}{}", "franken", "lean"));
        let (_, _, app_len, app_bytes) = appended.string_view();
        assert_eq!(app_len, 11);
        assert_eq!(&app_bytes[..11], b"frankenlean");

        // The ctor slice: Tree.node Tree.leaf Tree.leaf from the corpus's
        // inductive, traversed back out through ctor_child.
        let leaf = || Obj::mk_ctor(0, vec![], &[]);
        let node = Obj::mk_ctor(1, vec![leaf(), leaf()], &[]);
        assert_eq!(node.header().tag, 1);
        assert_eq!(node.ctor_child(0).header().tag, 0);
        assert_eq!(node.ctor_child(1).header().tag, 0);
    }
    let (_events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "RC balance across arrays, strings, and ctors");
}

#[test]
fn export_string_append_matches_upstream_arms() {
    let _g = lock();
    use crate::export::export_lean_string_append;
    shadow::enable();
    // SAFETY: every string below is allocated here and settled here: owned
    // references are yielded to the append exactly per lean.h:1225 (s1 owned,
    // s2 borrowed), borrowed ones dec'd at the end; field reads are within
    // live objects. `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0185
    #[allow(unsafe_code)]
    unsafe {
        // SHARED arm (object.cpp:2084-2096): a second reference forces the
        // fresh-alloc path — capacity EXACTLY mk_capacity(new_sz) = 2*new_sz,
        // and the shared original survives with its bytes intact.
        let s1 = crate::object::mk_string_unchecked(b"franken", 7);
        crate::rc::inc_ref_n(s1, 1); // the keeper reference
        let s2 = crate::object::mk_string_unchecked(b"lean", 4);
        let appended = export_lean_string_append(s1, s2);
        assert_ne!(appended, s1, "shared arm allocates fresh");
        let (a_size, a_cap, a_len, a_bytes) = crate::object::string_fields(appended);
        assert_eq!(&a_bytes[..11], b"frankenlean");
        assert_eq!(
            (a_size, a_len),
            (12, 11),
            "combined bytes + NUL / char count"
        );
        assert_eq!(a_cap, 24, "shared arm: capacity == 2 * new_sz exactly");
        let (_, _, _, kept) = crate::object::string_fields(s1);
        assert_eq!(&kept[..7], b"franken", "the shared original is untouched");
        crate::rc::dec_ref(s1); // drop the keeper

        // EXCLUSIVE arm, in-place: `appended` is exclusively owned with
        // capacity 24 and size 12 — room for the tail, so identity holds.
        let bang = crate::object::mk_string_unchecked(b"!", 1);
        let grown = export_lean_string_append(appended, bang);
        assert_eq!(grown, appended, "exclusive fit reuses the block in place");
        let (g_size, g_cap, g_len, g_bytes) = crate::object::string_fields(grown);
        assert_eq!(&g_bytes[..12], b"frankenlean!");
        assert_eq!((g_size, g_cap, g_len), (13, 24, 12));
        crate::rc::dec_ref(grown);
        crate::rc::dec_ref(bang);

        // EXCLUSIVE arm, grow (string_ensure_capacity, object.cpp:1966): a
        // fresh exact-capacity string must reallocate at cap + sz1 + extra,
        // and the old identity dies.
        let tight = crate::object::mk_string_unchecked(b"ab", 2); // size 3, cap 3
        let add = crate::object::mk_string_unchecked(b"cd", 2); // sz2 = 3, extra = 2
        let g2 = export_lean_string_append(tight, add);
        assert_ne!(g2, tight, "exclusive grow reallocates");
        let (z_size, z_cap, z_len, z_bytes) = crate::object::string_fields(g2);
        assert_eq!(&z_bytes[..4], b"abcd");
        assert_eq!((z_size, z_len), (5, 4));
        assert_eq!(z_cap, 3 + 3 + 2, "grow law: cap + sz1 + extra");
        crate::rc::dec_ref(g2);
        crate::rc::dec_ref(add);
        crate::rc::dec_ref(s2);
    }
    let (_events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "RC balance across all three append arms");
}

#[test]
fn export_assert_violation_format_matches_upstream() {
    // debug.cpp:48-55 byte-for-byte: four lines, each newline-terminated, the
    // condition bare on its own line. The abort half is the crash path and is
    // deliberately not crossed in-process; the format is the testable half.
    assert_eq!(
        crate::export::format_assert_violation("plug.c", 42, "x != NULL"),
        "LEAN ASSERTION VIOLATION\nFile: plug.c\nLine: 42\nx != NULL\n"
    );
}

#[test]
#[cfg(target_os = "linux")]
fn door_loads_a_reference_built_plugin_end_to_end() {
    let _g = lock();
    use crate::door::{LoadedPlugin, RTLD_GLOBAL, RTLD_NOW};
    use std::ffi::CString;
    use std::process::Command;

    // Env-gated on the pinned toolchain (the kernel_replay pattern): the
    // committed fixture is the SOURCE plus the build protocol; the .so is
    // regenerable platform-bound output, never committed.
    let home = std::env::var("HOME").unwrap_or_default();
    let bin =
        std::path::PathBuf::from(&home).join(".elan/toolchains/leanprover--lean4---v4.32.0/bin");
    if !bin.join("lean").is_file() {
        eprintln!("SKIP: pinned Reference toolchain not installed");
        return;
    }
    let plug_lean =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../fln-vm/fixtures/g03/plug.lean");
    let work = std::env::temp_dir().join(format!("fln-g03-door-{}", std::process::id()));
    std::fs::create_dir_all(&work).expect("workdir");
    std::fs::copy(&plug_lean, work.join("plug.lean")).expect("fixture copy");

    let run = |cmd: &mut Command| {
        let out = cmd.output().expect("spawn");
        assert!(
            out.status.success(),
            "{:?} failed:\n{}",
            cmd,
            String::from_utf8_lossy(&out.stderr)
        );
    };
    // The receipt protocol from the plugin import census, verbatim.
    run(Command::new(bin.join("lean"))
        .current_dir(&work)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SYSROOT")
        .env("LC_ALL", "C")
        .args(["plug.lean", "-c", "plug.c"]));
    run(Command::new(bin.join("leanc")).current_dir(&work).args([
        "-DLEAN_EXPORTING",
        "-shared",
        "-fPIC",
        "plug.c",
        "-o",
        "plug.so",
    ]));
    // The initializer shim: initialize_Init served as a leanc-compiled object
    // whose io-result construction resolves against THIS binary's exports.
    std::fs::write(
        work.join("shim.c"),
        "#include <lean/lean.h>\nLEAN_EXPORT lean_object * initialize_Init(uint8_t builtin) {\n  (void)builtin;\n  return lean_io_result_mk_ok(lean_box(0));\n}\n",
    )
    .expect("shim");
    run(Command::new(bin.join("leanc")).current_dir(&work).args([
        "-DLEAN_EXPORTING",
        "-shared",
        "-fPIC",
        "shim.c",
        "-o",
        "shim.so",
    ]));

    shadow::enable();
    {
        // RTLD_NOW on both loads: every undefined symbol — the census demand
        // list — must resolve at bind time against this test binary's
        // -rdynamic export surface, or the loader names the first miss.
        let cpath =
            |p: std::path::PathBuf| CString::new(p.into_os_string().into_encoded_bytes()).unwrap();
        let _shim = LoadedPlugin::open(&cpath(work.join("shim.so")), RTLD_NOW | RTLD_GLOBAL)
            .expect("the initializer shim binds against Marrow's exports");
        let plug = LoadedPlugin::open(&cpath(work.join("plug.so")), RTLD_NOW)
            .expect("the REAL Reference-built plugin binds against Marrow's exports");

        let init = plug
            .symbol(&CString::new("initialize_plug").unwrap())
            .expect("initializer");
        let add = plug
            .symbol(&CString::new("plug_add_five").unwrap())
            .expect("plug_add_five");
        let greet = plug
            .symbol(&CString::new("plug_greet").unwrap())
            .expect("plug_greet");
        // SAFETY: the census-declared signatures — initializer (uint8_t) ->
        // lean_object*, and the two boxed-convention exports; every returned
        // object is owned here and released here.
        // UNSAFE-LEDGER: FLN-UL-0189
        #[allow(unsafe_code)]
        unsafe {
            let f: extern "C" fn(u8) -> *mut LeanObject = core::mem::transmute(init);
            let res = f(1);
            assert!(!tagged::is_scalar(res), "io-result is a heap object");
            assert_eq!(crate::rc::read_header(res).tag, 0, "ok-branch ctor tag");
            crate::rc::dec_ref(res);

            // The exported functions are callable from the host over ABI
            // values: the corpus meaning holds through a REAL plugin.
            let fa: extern "C" fn(*mut LeanObject) -> *mut LeanObject = core::mem::transmute(add);
            assert_eq!(
                tagged::unbox(fa(tagged::boxi(37))),
                42,
                "addFive 37 through the membrane"
            );

            let fg: extern "C" fn(*mut LeanObject) -> *mut LeanObject = core::mem::transmute(greet);
            let s = crate::object::mk_string_unchecked(b"hello", 5);
            let out = fg(s);
            let (_, _, olen, obytes) = crate::object::string_fields(out);
            assert_eq!(&obytes[..21], b"hello from the plugin");
            assert_eq!(olen, 21, "the plugin's append ran on OUR wrapper");
            crate::rc::dec_ref(out);
        }
    }
    let (_events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "RC balance across the whole plugin round trip");
    // The per-pid workdir is scratch: reclaimed on the passing path (the census's
    // SELF_CLEANING class; a failed assert leaves it for forensics, which is the
    // class's own shape, not an accident).
    let _ = std::fs::remove_dir_all(&work);
}

#[test]
fn export_st_ref_family_matches_upstream_arms() {
    let _g = lock();
    use crate::export::{
        export_lean_st_mk_ref, export_lean_st_ref_get, export_lean_st_ref_ptr_eq,
        export_lean_st_ref_set, export_lean_st_ref_swap, export_lean_st_ref_take,
    };
    shadow::enable();
    // SAFETY: every object is allocated and settled here; the ref exports'
    // ownership contracts (io.cpp:1423-1532) are exercised token-for-token,
    // and `lock()` serialises the heap-observing tests.
    // UNSAFE-LEDGER: FLN-UL-0216
    #[allow(unsafe_code)]
    unsafe {
        // ST fast path: mk consumes, get duplicates, set displaces + releases.
        let v1 = crate::object::mk_string_unchecked(b"alpha", 5);
        let cell = export_lean_st_mk_ref(v1);
        let got = export_lean_st_ref_get(cell);
        assert_eq!(got, v1, "ST get returns the stored object identity");
        crate::rc::dec_ref(got);
        let v2 = crate::object::mk_string_unchecked(b"beta", 4);
        let unit = export_lean_st_ref_set(cell, v2);
        assert_eq!(crate::tagged::unbox(unit), 0, "set returns box(0)");
        // swap returns the old token and installs the new value.
        let v3 = crate::object::mk_string_unchecked(b"gamma", 5);
        let old = export_lean_st_ref_swap(cell, v3);
        let (_, _, _, old_bytes) = crate::object::string_fields(old);
        assert_eq!(&old_bytes[..4], b"beta", "swap yields the displaced value");
        crate::rc::dec_ref(old);
        // take moves the token out and leaves the slot null until re-set.
        let taken = export_lean_st_ref_take(cell);
        let (_, _, _, taken_bytes) = crate::object::string_fields(taken);
        assert_eq!(&taken_bytes[..5], b"gamma");
        let refill = crate::object::mk_string_unchecked(b"delta", 5);
        let unit2 = export_lean_st_ref_set(cell, refill);
        assert_eq!(crate::tagged::unbox(unit2), 0);
        crate::rc::dec_ref(taken);
        // identity, never value equality.
        let other_v = crate::object::mk_string_unchecked(b"delta", 5);
        let other = export_lean_st_mk_ref(other_v);
        assert_eq!(export_lean_st_ref_ptr_eq(cell, cell), 1);
        assert_eq!(
            export_lean_st_ref_ptr_eq(cell, other),
            0,
            "equal values in distinct cells are not ptr-equal"
        );
        // The maybe-mt arm: a PERSISTENT cell must take the atomic path and
        // mark stored values multi-threaded (io.cpp's global-Ref law). The
        // observable: the value stored into a persistent cell leaves the ST
        // rc regime (m_rc no longer positive after mark_mt).
        crate::rc::mark_persistent(other);
        let mt_v = crate::object::mk_string_unchecked(b"epsilon", 7);
        let unit3 = export_lean_st_ref_set(other, mt_v);
        assert_eq!(crate::tagged::unbox(unit3), 0);
        let back = export_lean_st_ref_get(other);
        let (_, _, _, back_bytes) = crate::object::string_fields(back);
        assert_eq!(
            &back_bytes[..7],
            b"epsilon",
            "persistent-cell get round-trips"
        );
        assert!(
            (&raw const (*back).m_rc).read() < 0,
            "a value stored into a persistent cell is marked multi-threaded"
        );
        crate::rc::dec_ref(back);
        crate::rc::dec_ref(cell);
        // `other` is persistent: never counted, deliberately not dec'd.
    }
    let _ = shadow::disable_and_drain();
}

#[test]
fn export_string_utf8_get_set_match_upstream_arms() {
    let _g = lock();
    use crate::export::{export_lean_string_utf8_get, export_lean_string_utf8_set};
    shadow::enable();
    // SAFETY: strings allocated and settled here; get borrows, set consumes,
    // per lean.h:1229/1255.
    // UNSAFE-LEDGER: FLN-UL-0217
    #[allow(unsafe_code)]
    unsafe {
        // h(0x68) é(0xC3 0xA9) l l o — the same vector family the hash and
        // lossy suites pin.
        let s = crate::object::mk_string_unchecked(b"h\xc3\xa9llo", 5);
        let get =
            |st: *mut LeanObject, i: usize| export_lean_string_utf8_get(st, crate::tagged::boxi(i));
        assert_eq!(get(s, 0), u32::from(b'h'));
        assert_eq!(get(s, 1), 0xE9, "two-byte scalar decodes at its first byte");
        assert_eq!(
            get(s, 2),
            u32::from('A'),
            "continuation byte is the default char"
        );
        assert_eq!(get(s, 3), u32::from(b'l'));
        assert_eq!(
            get(s, 99),
            u32::from('A'),
            "out of range is the default char"
        );
        // Exclusive ASCII-over-ASCII: in place, identity preserved.
        let s2 = export_lean_string_utf8_set(s, crate::tagged::boxi(0), u32::from(b'H'));
        assert_eq!(s2, s, "exclusive ASCII set writes in place");
        assert_eq!(get(s2, 0), u32::from(b'H'));
        // Multi-byte replacement rebuilds; codepoint length is preserved.
        let s3 = export_lean_string_utf8_set(s2, crate::tagged::boxi(1), 0x2603 /* SNOWMAN */);
        let (size3, _, len3, bytes3) = crate::object::string_fields(s3);
        assert_eq!(&bytes3[..size3 - 1], b"H\xe2\x98\x83llo");
        assert_eq!(len3, 5, "codepoint count survives the rebuild");
        assert_eq!(get(s3, 1), 0x2603);
        // Non-first-byte target returns the string unchanged.
        let s4 = export_lean_string_utf8_set(s3, crate::tagged::boxi(2), u32::from(b'x'));
        assert_eq!(s4, s3, "a continuation-byte index is a no-op");
        crate::rc::dec_ref(s4);
    }
    let _ = shadow::disable_and_drain();
}

/// fln-3gv slice 2 apply targets — safe bodies only; ownership passthrough
/// carries the non-scalar arm without touching rc.
mod task_state_targets {
    use crate::layout::LeanObject;

    /// `id` under the boxed convention: consumes `x` by returning it.
    pub(crate) extern "C" fn ident(x: *mut LeanObject) -> *mut LeanObject {
        x
    }

    /// Spawn target `fun _ => 42` under the boxed convention.
    pub(crate) extern "C" fn forty_two(_w: *mut LeanObject) -> *mut LeanObject {
        crate::tagged::boxi(42)
    }

    /// Bind target `fun v => t_captured`: releases the owned input value and
    /// returns the captured task, exercising the re-arm arm.
    // UNSAFE-LEDGER: FLN-UL-0251
    #[allow(unsafe_code)]
    pub(crate) extern "C" fn return_captured_task(
        t: *mut LeanObject,
        v: *mut LeanObject,
    ) -> *mut LeanObject {
        if !crate::tagged::is_scalar(v) {
            // SAFETY: v is the owned input value this closure consumes.
            unsafe { crate::rc::dec_ref(v) };
        }
        t
    }

    /// `fun a => pure (a * 2)` under the compiled BaseIO convention (bare
    /// result, world token ignored).
    pub(crate) extern "C" fn io_double(a: *mut LeanObject, _w: *mut LeanObject) -> *mut LeanObject {
        crate::tagged::boxi(crate::tagged::unbox(a) * 2)
    }

    /// `fun a => pure (Task.pure (a + 1))` — the bindTask target returning
    /// a task, through the safe export wrapper.
    pub(crate) extern "C" fn io_task_succ(
        a: *mut LeanObject,
        _w: *mut LeanObject,
    ) -> *mut LeanObject {
        crate::export::export_lean_task_pure(crate::tagged::boxi(crate::tagged::unbox(a) + 1))
    }
}

#[test]
fn export_task_promise_state_family_matches_upstream_arms() {
    let _g = lock();
    use crate::export::{
        export_lean_io_get_task_state, export_lean_option_get_or_block, export_lean_task_get,
        export_lean_task_map_core, export_lean_task_pure,
    };
    shadow::enable();
    // SAFETY: every object is allocated and settled here; the family's live
    // (managerless) arms — object.cpp:1162/1176-eager/1187-finished,
    // io.cpp:1627-some — are exercised with the shadow oracle watching the
    // ownership balance. The refusal arms terminate the process by design
    // and belong to the gauntlet's panic-parity lane, not to in-process
    // cells.
    // UNSAFE-LEDGER: FLN-UL-0226
    #[allow(unsafe_code)]
    unsafe {
        // Task.pure over a scalar: Finished at birth, single-threaded header,
        // borrowed get, state 2 before any manager is consulted.
        let t = export_lean_task_pure(crate::tagged::boxi(21));
        assert_eq!(
            export_lean_io_get_task_state(t),
            2,
            "Task.pure is born Finished (m_imp == NULL answers 2, object.cpp:1260-1263)"
        );
        assert!(
            (&raw const (*t).m_rc).read() > 0,
            "Task.pure is born single-threaded (alloc_task's lean_set_st_header arm)"
        );
        let v = export_lean_task_get(t);
        assert_eq!(
            crate::tagged::unbox(v),
            21,
            "task_get returns m_value borrowed"
        );
        let v2 = export_lean_task_get(t);
        assert_eq!(v, v2, "task_get does not consume the task or the value");

        // map_core's managerless-eager arm over a scalar payload:
        // task_pure(apply_1(f, get_own(t))) with f = (· * 2).
        let double =
            crate::object::alloc_closure(corpus_targets::double as *mut core::ffi::c_void, 1, 0);
        let t2 = export_lean_task_map_core(double, t, 0, false, false);
        assert_eq!(
            export_lean_io_get_task_state(t2),
            2,
            "the eager arm funnels through task_pure, so the result is Finished"
        );
        assert_eq!(
            crate::tagged::unbox(export_lean_task_get(t2)),
            42,
            "map_core applied f eagerly on the calling thread (object.cpp:1176)"
        );
        crate::rc::dec_ref(t2);

        // map_core over a NON-scalar payload — the arm class whose scalar
        // guards the slice-1 differential had to teach us; here the value
        // rides through get_own's inc/dec with the shadow oracle watching.
        // sync and keep_alive are both silently ignored on this arm,
        // exactly as the pin ignores them (object.cpp:1175-1178).
        let s = crate::object::mk_string_unchecked(b"alpha", 5);
        let ts = export_lean_task_pure(s);
        let ident =
            crate::object::alloc_closure(task_state_targets::ident as *mut core::ffi::c_void, 1, 0);
        let t3 = export_lean_task_map_core(ident, ts, 0, true, true);
        let out = export_lean_task_get(t3);
        assert_eq!(
            out, s,
            "identity map hands the same object through the eager arm"
        );
        assert!(
            (&raw const (*out).m_rc).read() > 0,
            "the eager arm never marks the value multi-threaded (task_pure's deliberate exception)"
        );
        crate::rc::dec_ref(t3);

        // option_get_or_block's `some` arm: the value is stolen out of the
        // consumed cell (io.cpp:1627-1631's option_ref discipline).
        let s2 = crate::object::mk_string_unchecked(b"beta", 4);
        let some = crate::object::alloc_ctor(1, 1, 0);
        crate::object::ctor_set(some, 0, s2);
        let r = export_lean_option_get_or_block(some);
        assert_eq!(
            r, s2,
            "getOrBlock! steals the value out of the consumed some cell"
        );
        crate::rc::dec_ref(r);
    }
    let _ = shadow::disable_and_drain();
}

#[test]
fn export_task_manager_family_matches_upstream_arms() {
    let _g = lock();
    use crate::export::{
        export_lean_finalize_task_manager, export_lean_init_task_manager_using,
        export_lean_io_get_task_state, export_lean_io_promise_new, export_lean_io_promise_resolve,
        export_lean_io_promise_result_opt, export_lean_task_bind_core, export_lean_task_get,
        export_lean_task_map_core, export_lean_task_spawn_core,
    };
    shadow::enable();
    /// Finalize on every exit path, so a failing assertion cannot leak a
    /// live manager into the other cells (the manager is process-global and
    /// flips the rc teardown arms).
    struct Fin;
    impl Drop for Fin {
        fn drop(&mut self) {
            export_lean_finalize_task_manager();
        }
    }
    // SAFETY: every object is allocated and settled here; the manager arms
    // of object.cpp:727-1312 are exercised end to end with the shadow
    // oracle watching, and the sync-priority cells pin the pin's
    // inline-execution ordering guarantees.
    // UNSAFE-LEDGER: FLN-UL-0252
    #[allow(unsafe_code)]
    unsafe {
        export_lean_init_task_manager_using(2);
        let _fin = Fin;

        // spawn + get: Queued -> Running -> Finished on a pooled worker;
        // get blocks until the value is published (object.cpp:1152-1160,
        // 1187-1203).
        let c = crate::object::alloc_closure(
            task_state_targets::forty_two as *mut core::ffi::c_void,
            1,
            0,
        );
        let t = export_lean_task_spawn_core(c, 0, false);
        let v = export_lean_task_get(t);
        assert_eq!(
            crate::tagged::unbox(v),
            42,
            "spawned closure ran on a worker and get returned its value"
        );
        assert_eq!(export_lean_io_get_task_state(t), 2, "finished after get");
        crate::rc::dec_ref(t);

        // The promise lifecycle: Promised (state 1) -> resolve publishes
        // some(value), marked multi-threaded, first call wins
        // (object.cpp:960-972, 1271-1312).
        let p = export_lean_io_promise_new();
        let rt = export_lean_io_promise_result_opt(p);
        assert_eq!(
            export_lean_io_get_task_state(rt),
            1,
            "an unresolved promise's task reports running (closure-less imp)"
        );
        let s = crate::object::mk_string_unchecked(b"gamma", 5);
        let unit = export_lean_io_promise_resolve(s, p);
        assert!(crate::tagged::is_scalar(unit), "resolve returns unit");
        assert_eq!(export_lean_io_get_task_state(rt), 2, "resolved is finished");
        let some_v = export_lean_task_get(rt);
        assert_eq!(
            crate::object::ctor_get(some_v, 0),
            s,
            "the resolved payload is some(value) around the exact object"
        );
        assert!(
            (&raw const (*some_v).m_rc).read() < 0,
            "resolve_core marked the published value multi-threaded (object.cpp:893)"
        );
        let s2 = crate::object::mk_string_unchecked(b"delta", 5);
        export_lean_io_promise_resolve(s2, p);
        assert_eq!(
            export_lean_task_get(rt),
            some_v,
            "the second resolve is silently dropped — only the first has an effect"
        );
        crate::rc::dec_ref(rt);
        crate::rc::dec_ref(p);

        // sync := true on an UNFINISHED promise task: the dependent joins
        // the graph Waiting (state 0), and resolve runs it INLINE before
        // returning — the ordering CancelToken.onSet relies on
        // (enqueue_core's LEAN_SYNC_PRIO arm, object.cpp:758-763).
        let p2 = export_lean_io_promise_new();
        let rt2 = export_lean_io_promise_result_opt(p2);
        let fident =
            crate::object::alloc_closure(task_state_targets::ident as *mut core::ffi::c_void, 1, 0);
        let mapped = export_lean_task_map_core(fident, rt2, 0, true, false);
        assert_eq!(
            export_lean_io_get_task_state(mapped),
            0,
            "a sync dependent of an unresolved promise is Waiting (closure present)"
        );
        export_lean_io_promise_resolve(crate::tagged::boxi(9), p2);
        assert_eq!(
            export_lean_io_get_task_state(mapped),
            2,
            "the sync dependent ran inline during resolve, before it returned"
        );
        let got = export_lean_task_get(mapped);
        assert_eq!(
            crate::tagged::unbox(crate::object::ctor_get(got, 0)),
            9,
            "identity map over some(9)"
        );
        crate::rc::dec_ref(mapped);
        crate::rc::dec_ref(p2);

        // Dropping an unresolved promise resolves its task to none
        // (deactivate_promise, object.cpp:1314-1318).
        let p3 = export_lean_io_promise_new();
        let rt3 = export_lean_io_promise_result_opt(p3);
        crate::rc::dec_ref(p3);
        assert_eq!(export_lean_io_get_task_state(rt3), 2);
        assert!(
            crate::tagged::is_scalar(export_lean_task_get(rt3)),
            "a dropped unresolved promise publishes none"
        );
        crate::rc::dec_ref(rt3);

        // bind through the RE-ARM path, made deterministic with sync:
        // resolve(p4) runs bind_fn1 inline, f returns p5's still-unfinished
        // task, so the bound task re-arms on it (run_task's NULL-sentinel
        // arm, object.cpp:874-885); resolve(p5) then finishes it inline.
        let p4 = export_lean_io_promise_new();
        let rt4 = export_lean_io_promise_result_opt(p4);
        let p5 = export_lean_io_promise_new();
        let rt5 = export_lean_io_promise_result_opt(p5);
        let fbind = crate::object::alloc_closure(
            task_state_targets::return_captured_task as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::object::closure_set(fbind, 0, rt5);
        let bound = export_lean_task_bind_core(rt4, fbind, 0, true, false);
        export_lean_io_promise_resolve(crate::tagged::boxi(1), p4);
        assert_eq!(
            export_lean_io_get_task_state(bound),
            0,
            "after the outer resolve the bound task is re-armed Waiting on the nested one (its continuation closure is installed)"
        );
        export_lean_io_promise_resolve(crate::tagged::boxi(7), p5);
        let bv = export_lean_task_get(bound);
        assert_eq!(
            crate::tagged::unbox(crate::object::ctor_get(bv, 0)),
            7,
            "the re-armed bind carries the nested task's published value"
        );
        crate::rc::dec_ref(bound);
        crate::rc::dec_ref(p4);
        crate::rc::dec_ref(p5);

        drop(_fin); // join the workers before the shadow drain
    }
    let _ = shadow::disable_and_drain();
}

#[test]
fn export_io_task_wrapper_family_matches_upstream_arms() {
    let _g = lock();
    use crate::export::{
        export_lean_finalize_task_manager, export_lean_init_task_manager_using,
        export_lean_io_as_task, export_lean_io_bind_task, export_lean_io_cancel,
        export_lean_io_check_canceled, export_lean_io_get_task_state, export_lean_io_map_task,
        export_lean_io_promise_new, export_lean_io_promise_result_opt, export_lean_io_wait,
        export_lean_io_wait_any, export_lean_io_wait_any_core, export_lean_task_pure,
    };
    shadow::enable();
    struct Fin;
    impl Drop for Fin {
        fn drop(&mut self) {
            export_lean_finalize_task_manager();
        }
    }
    // SAFETY: every object is allocated and settled here; the io.cpp wrapper
    // family (io.cpp:1534-1592) is exercised over the live manager and the
    // managerless finished-scan arm, with the shadow oracle watching.
    // UNSAFE-LEDGER: FLN-UL-0264
    #[allow(unsafe_code)]
    unsafe {
        export_lean_init_task_manager_using(2);
        let _fin = Fin;

        // asTask: the BaseIO action's bare result becomes the task value;
        // keep_alive means the task runs even if its reference is dropped.
        let act = crate::object::alloc_closure(
            task_state_targets::forty_two as *mut core::ffi::c_void,
            1,
            0,
        );
        let t1 = export_lean_io_as_task(act, crate::tagged::boxi(0));
        assert_eq!(
            crate::tagged::unbox(export_lean_io_wait(t1)),
            42,
            "asTask ran the action on a worker; wait consumed the task"
        );

        // mapTask: f applied to the value and the world token, bare result.
        let f2 = crate::object::alloc_closure(
            task_state_targets::io_double as *mut core::ffi::c_void,
            2,
            0,
        );
        let t2 = export_lean_io_map_task(
            f2,
            export_lean_task_pure(crate::tagged::boxi(21)),
            crate::tagged::boxi(0),
            0,
        );
        assert_eq!(
            crate::tagged::unbox(export_lean_io_wait(t2)),
            42,
            "mapTask applied f through io_bind_task_fn"
        );

        // bindTask: f returns a Task; the bound task continues as it.
        let f3 = crate::object::alloc_closure(
            task_state_targets::io_task_succ as *mut core::ffi::c_void,
            2,
            0,
        );
        let t3 = export_lean_io_bind_task(
            export_lean_task_pure(crate::tagged::boxi(5)),
            f3,
            crate::tagged::boxi(0),
            0,
        );
        assert_eq!(
            crate::tagged::unbox(export_lean_io_wait(t3)),
            6,
            "bindTask continued as f's task"
        );

        // waitAny: the first FINISHED member in list order — the unresolved
        // promise task is skipped, the pure task answers.
        let pw = export_lean_io_promise_new();
        let pwt = export_lean_io_promise_result_opt(pw);
        let fin3 = export_lean_task_pure(crate::tagged::boxi(3));
        let nil = crate::tagged::boxi(0);
        let l2 = crate::object::alloc_ctor(1, 2, 0);
        crate::object::ctor_set(l2, 0, fin3);
        crate::object::ctor_set(l2, 1, nil);
        let l1 = crate::object::alloc_ctor(1, 2, 0);
        crate::object::ctor_set(l1, 0, pwt);
        crate::object::ctor_set(l1, 1, l2);
        assert_eq!(
            crate::tagged::unbox(export_lean_io_wait_any(l1)),
            3,
            "waitAny returns the first finished member's value in list order"
        );
        crate::rc::dec_ref(l1);
        crate::rc::dec_ref(pw);

        // cancel wrapper on a finished task is a unit no-op; the check
        // wrapper answers false off-task.
        let fc = export_lean_task_pure(crate::tagged::boxi(1));
        assert!(crate::tagged::is_scalar(export_lean_io_cancel(fc)));
        assert_eq!(
            export_lean_io_get_task_state(fc),
            2,
            "cancel of a finished task is the pin's pre-manager no-op"
        );
        crate::rc::dec_ref(fc);
        assert_eq!(export_lean_io_check_canceled(), 0, "false off-task");

        drop(_fin); // join the workers, then exercise the managerless arm
        let lone = export_lean_task_pure(crate::tagged::boxi(4));
        let nil2 = crate::tagged::boxi(0);
        let l3 = crate::object::alloc_ctor(1, 2, 0);
        crate::object::ctor_set(l3, 0, lone);
        crate::object::ctor_set(l3, 1, nil2);
        let w = export_lean_io_wait_any_core(l3);
        assert_eq!(
            crate::tagged::unbox(crate::object::task_fields(w).0),
            4,
            "managerless wait_any_core still answers from the finished scan"
        );
        crate::rc::dec_ref(l3);
    }
    let _ = shadow::disable_and_drain();
}
