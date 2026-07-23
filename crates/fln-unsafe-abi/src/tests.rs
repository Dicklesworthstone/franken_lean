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
    let cl = Obj::mk_closure(3, vec![Obj::mk_nat(9)]);
    assert_eq!(cl.closure_view(), (3, 1));
    assert_eq!(cl.header().cs_sz, 0, "closures ride the big path");

    let r = Obj::mk_ref(Obj::mk_string("cell"));
    assert_eq!(
        usize::from(r.header().cs_sz),
        align_obj_size(size_of::<LeanRefObject>())
    );

    let t = Obj::mk_thunk_value(Obj::mk_nat(4));
    assert_eq!(t.obj_tag(), usize::from(contract::TAG_THUNK));

    let task = Obj::mk_task_pure(Obj::mk_nat(5));
    assert_eq!(task.obj_tag(), usize::from(contract::TAG_TASK));

    let m = Obj::mk_mpz(&[0xDEAD_BEEF, 0x1], true);
    let (alloc, size, limbs) = m.mpz_view();
    assert_eq!(alloc, 2);
    assert_eq!(size, -2, "sign of the value is the sign of m_size");
    assert_eq!(limbs, vec![0xDEAD_BEEF, 0x1]);
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
        export_lean_alloc_small, export_lean_free_small, export_lean_small_mem_size,
        export_mi_free, export_mi_malloc_small,
    };
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
    // SMALL_ALLOCATOR surface: aligned size + slot-idx law.
    let q = export_lean_alloc_small(32, 3);
    assert!(!q.is_null());
    assert_eq!(export_lean_small_mem_size(q), 32);
    export_lean_free_small(q);
}

#[test]
fn export_alloc_object_marks_big_path_and_frees() {
    let _g = lock();
    use crate::export::{export_lean_alloc_object, export_lean_free_object};
    let o = export_lean_alloc_object(64);
    assert!(!o.is_null());
    // Header init through the internal twin, then release through the
    // exported category dispatch.
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
    use crate::export::{export_lean_inc_heartbeat, heartbeat_value};
    let before = heartbeat_value();
    for _ in 0..5 {
        export_lean_inc_heartbeat();
    }
    assert_eq!(heartbeat_value(), before + 5);
    // A fresh thread starts its own counter (LEAN_THREAD_VALUE semantics).
    std::thread::spawn(|| {
        assert_eq!(heartbeat_value(), 0);
        export_lean_inc_heartbeat();
        assert_eq!(heartbeat_value(), 1);
    })
    .join()
    .expect("heartbeat thread");
}

#[test]
fn export_dec_ref_cold_tears_down_graphs() {
    let _g = lock();
    use crate::export::export_lean_dec_ref_cold;
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
    // UNSAFE-LEDGER: FLN-UL-0160
    #[allow(unsafe_code)]
    unsafe {
        // Boundary law: MAX_SMALL_NAT boxes, MAX_SMALL_NAT+1 mints mpz.
        let max_small = tagged::MAX_SMALL_NAT;
        assert!(tagged::is_scalar(export_lean_big_usize_to_nat(max_small)));
        let big = export_lean_big_uint64_to_nat(u64::MAX);
        assert!(!tagged::is_scalar(big), "2^64-1 exceeds MAX_SMALL_NAT");
        let (_, sz, limbs) = crate::object::mpz_fields(big);
        assert_eq!((sz, limbs.as_slice()), (1, &[u64::MAX][..]));

        // add: big + 1 = 2^64 (stays mpz, _core arm).
        let big2 = export_lean_nat_big_add(big, tagged::boxi(1));
        let (_, sz2, limbs2) = crate::object::mpz_fields(big2);
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
        let (_, osz, olimbs) = crate::object::mpz_fields(of);
        assert_eq!((osz, olimbs.as_slice()), (2, &[0, 1 << 16][..]));

        // cstr parse: small and 2^128 + 1.
        assert_eq!(tagged::unbox(export_lean_cstr_to_nat(c"123".as_ptr())), 123);
        let c128 = export_lean_cstr_to_nat(c"340282366920938463463374607431768211457".as_ptr());
        let (_, csz, climbs) = crate::object::mpz_fields(c128);
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
        // UNSAFE-LEDGER: FLN-UL-0178
        #[allow(unsafe_code)]
        unsafe {
            crate::object::mk_string_unchecked(b"once", 4)
        }
    }
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
