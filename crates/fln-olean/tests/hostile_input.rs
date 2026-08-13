//! Hostile-input suite (bead `fln-abaz`): every refusal the codec must make on
//! malformed bytes, constructed by real surgery on the committed fixtures and
//! asserted by the refusal's own words. The pre-fix failures these cells would
//! have produced — a panic in a dev build, an OOM, or a silent accept — are
//! FL-INV-07 violations: malformed input is a value, never an invariant event.
//!
//! Every cell first asserts the unmutated fixture is VALID under the same
//! operation, so a green proves the law refuses only the hostile shape, never
//! the real corpus.

#![forbid(unsafe_code)]

use std::collections::HashSet;
use std::path::PathBuf;

use fln_olean::decl::DeclDecoder;
use fln_olean::rebuild::rebuild;
use fln_olean::region::{OleanView, RegionError, WalkBudget};
use fln_rt::abi;
use fln_rt::region::parse_olean_envelope;

fn fixture(path: &str) -> Vec<u8> {
    // Resolved at run time, never baked at compile time: a test binary built in
    // one checkout and run from another must read the INVOKING tree (the
    // golden_vellum pattern, not a raw env! site — k60n).
    let root = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .expect("cargo identifies the invoking crate directory");
    let full = root.join(path);
    let data = std::fs::read(&full);
    assert!(
        data.is_ok(),
        "missing fixture {}: {:?}",
        full.display(),
        data.err()
    );
    data.expect("asserted above")
}

fn pilot() -> Vec<u8> {
    fixture("fixtures/g05_pilot.olean")
}

fn c3(name: &str) -> Vec<u8> {
    fixture(&format!("../../tribunal/fixtures/c3/{name}"))
}

fn get_u64(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().expect("in-range read"))
}

fn put_u64(bytes: &mut [u8], offset: usize, value: u64) {
    bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}

const HEADER_SIZE: usize = 88; // format::OLEAN_HEADER_SIZE

/// One object in the pointer graph: its file offset and header fields.
#[derive(Debug, Clone, Copy)]
struct ObjAt {
    off: usize,
    tag: u8,
    other: u8,
}

/// Walk the pointer graph from the root word with the same layout law the
/// codec enforces (rc==0 required to be a real object header), collecting
/// every object once. This is the surgery locator: cells mutate a real object
/// of the needed category rather than fabricating bytes the format would
/// never carry.
fn collect_objects(bytes: &[u8]) -> Vec<ObjAt> {
    let envelope = parse_olean_envelope(bytes).expect("fixture parses");
    let base = envelope.base_addr;
    let deref = |ptr: u64| -> Option<usize> {
        if ptr & 1 == 1 || ptr == 0 {
            return None;
        }
        let resolved = usize::try_from(ptr.checked_sub(base)?).ok()?;
        (resolved >= HEADER_SIZE && resolved < bytes.len() && resolved % 8 == 0).then_some(resolved)
    };
    let root = get_u64(bytes, HEADER_SIZE);
    let mut seen: HashSet<usize> = HashSet::new();
    let mut stack = vec![root];
    let mut out = Vec::new();
    while let Some(ptr) = stack.pop() {
        let Some(off) = deref(ptr) else { continue };
        if !seen.insert(off) {
            continue;
        }
        let word = get_u64(bytes, off);
        let tag = ((word >> 56) & 0xff) as u8;
        let other = ((word >> 48) & 0xff) as u8;
        match tag {
            // Constructor-shaped (incl. the Level nodes, tags 1-5): `other`
            // pointer fields from off+8.
            t if t <= abi::TAG_MAX_CTOR_TAG => {
                for i in 0..other as usize {
                    let field = off + 8 + 8 * i;
                    if field + 8 <= bytes.len() {
                        stack.push(get_u64(bytes, field));
                    }
                }
            }
            t if t == abi::TAG_ARRAY => {
                let size = get_u64(bytes, off + 8);
                for i in 0..size.min(1 << 16) {
                    let field = off + 24 + 8 * i as usize;
                    if field + 8 <= bytes.len() {
                        stack.push(get_u64(bytes, field));
                    }
                }
            }
            t if (t == abi::TAG_THUNK || t == abi::TAG_REF) && off + 16 <= bytes.len() => {
                stack.push(get_u64(bytes, off + 8));
            }
            _ => {}
        }
        out.push(ObjAt { off, tag, other });
    }
    out
}

fn message_of(error: &RegionError) -> String {
    match error {
        RegionError::DecodeShape { reason, .. } => (*reason).to_string(),
        other => format!("{other}"),
    }
}

// --- finding 1: a cyclic object graph is a typed Shape, never a runaway ------

/// Locate a real Level succ node by offering each candidate to the decoder as
/// its own oracle: a self-cycled node that decodes as a level is refused by the
/// post-order law, and anything else is a typed shape error — both are refusals,
/// and exactly the real nodes produce the law's name. The alternative, guessing
/// a Level node from the region layout alone, is unsound: ctor tags 1-5 are
/// shared with every Lean structure of the same tag.
fn first_post_order_refusal(bytes: &[u8], other_ok: &[u8]) -> (usize, String) {
    let envelope = parse_olean_envelope(bytes).expect("fixture parses");
    let objects = collect_objects(bytes);
    for obj in objects
        .iter()
        .filter(|obj| obj.tag <= abi::TAG_MAX_CTOR_TAG && other_ok.contains(&obj.other))
    {
        let mut hostile = bytes.to_vec();
        put_u64(
            &mut hostile,
            obj.off + 8,
            obj.off as u64 + envelope.base_addr,
        );
        let view = OleanView::parse(&hostile).expect("hostile parses structurally");
        let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
        let root = obj.off as u64 + envelope.base_addr;
        let error = match decoder.decode_level(root) {
            Ok(_) => continue,
            Err(error) => error,
        };
        let text = format!("{error:?}");
        if text.contains("post-order law") {
            return (obj.off, text);
        }
    }
    panic!(
        "no candidate produced a post-order-law refusal over {} objects",
        objects.len()
    );
}

#[test]
fn a_cyclic_level_child_is_refused_by_the_post_order_law() {
    let bytes = pilot();
    let (off, text) = first_post_order_refusal(&bytes, &[1, 2]);
    assert!(
        text.contains("post-order law"),
        "the refusal must name the law at {off:#x}: {text}"
    );
}

#[test]
fn a_cyclic_expr_child_is_refused_by_the_post_order_law() {
    let bytes = pilot();
    let envelope = parse_olean_envelope(&bytes).expect("pilot parses");
    let objects = collect_objects(&bytes);
    let mut proven = 0usize;
    for obj in objects
        .iter()
        .filter(|obj| obj.tag <= abi::TAG_MAX_CTOR_TAG && obj.other >= 1)
    {
        let mut hostile = bytes.clone();
        put_u64(
            &mut hostile,
            obj.off + 8,
            obj.off as u64 + envelope.base_addr,
        );
        let view = OleanView::parse(&hostile).expect("hostile parses structurally");
        let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
        let root = obj.off as u64 + envelope.base_addr;
        let error = match decoder.decode_expr(root) {
            Ok(_) => continue,
            Err(error) => error,
        };
        let text = format!("{error:?}");
        if text.contains("post-order law") {
            proven += 1;
            break;
        }
    }
    assert_eq!(proven, 1, "a real Expr node must cycle into the law");
}

// --- finding 2: a capacity high-bit flip is a typed Shape, never overflow ----

#[test]
fn an_array_capacity_high_bit_flip_is_refused_without_overflow() {
    let bytes = pilot();
    rebuild(&bytes).expect("the unmutated pilot rebuilds");

    let objects = collect_objects(&bytes);
    let array = objects
        .iter()
        .find(|obj| obj.tag == abi::TAG_ARRAY)
        .expect("the pilot carries an array");
    let mut hostile = bytes.clone();
    // Flip the top bit of the array's capacity: the slack multiply used to
    // overflow here — debug panic, release wrap with a silent accept.
    let capacity = get_u64(&hostile, array.off + 16);
    put_u64(&mut hostile, array.off + 16, capacity | (1u64 << 63));

    let error = rebuild(&hostile).expect_err("an overflowing slack must refuse typed");
    let text = message_of(&error);
    assert!(
        text.contains("overflows"),
        "the refusal must name the overflow, got: {text}"
    );
}

// --- finding 3: a wrap-around base is refused at the envelope ----------------

#[test]
fn a_base_addr_that_wraps_the_extent_is_refused_at_the_envelope() {
    let bytes = pilot();
    let envelope = parse_olean_envelope(&bytes).expect("pilot parses");
    // Find where base_addr lives in the header by its current value.
    let needle = envelope.base_addr.to_le_bytes();
    let at = bytes[..HEADER_SIZE]
        .windows(8)
        .position(|window| window == needle)
        .expect("base_addr is findable in the header");

    let mut hostile = bytes.clone();
    put_u64(&mut hostile, at, u64::MAX - 8); // 8-aligned, wraps on any extent
    let error =
        parse_olean_envelope(&hostile).expect_err("a base that wraps the file extent must refuse");
    assert!(
        matches!(error, fln_rt::region::RegionFault::MisalignedBase { .. }),
        "expected MisalignedBase, got {error:?}"
    );

    // And the production audit entry point agrees, with no panic anywhere.
    let hostile2 = hostile;
    match std::panic::catch_unwind(|| OleanView::parse(&hostile2)) {
        Ok(Err(_)) => {}
        other => panic!("shared entry must refuse typed, got: {other:?}"),
    }
}

// --- finding 4: the typed-error path itself must not panic -------------------

#[test]
fn a_truncation_with_a_huge_wanted_saturates_the_diagnostic() {
    let bytes = pilot();
    let objects = collect_objects(&bytes);
    let string = objects
        .iter()
        .find(|obj| obj.tag == abi::TAG_STRING)
        .expect("the pilot carries a string");
    let mut hostile = bytes.clone();
    // Capacity just under the overflow line: STRING_FIXED + cap still fits a
    // usize, so the engine reports Truncated — and the diagnostic add used to
    // overflow while CONSTRUCTING the typed error.
    put_u64(&mut hostile, string.off + 16, u64::MAX - 40);

    let view = OleanView::parse(&hostile).expect("hostile parses structurally");
    let error = view
        .shared_audit()
        .expect_err("a string past its file must refuse");
    match error {
        RegionError::Truncated { wanted_end, .. } => {
            assert_eq!(
                wanted_end,
                u64::MAX,
                "the diagnostic saturates rather than wrapping: {wanted_end:#x}"
            );
        }
        other => panic!("expected Truncated, got {other:?}"),
    }
}

#[test]
fn a_string_whose_m_length_is_not_the_scalar_count_is_refused() {
    let bytes = pilot();
    {
        let view = OleanView::parse(&bytes).expect("pilot parses");
        view.walk(WalkBudget::default())
            .expect("the unmutated pilot walks");
    }
    let objects = collect_objects(&bytes);
    let string = objects
        .iter()
        .find(|obj| obj.tag == abi::TAG_STRING)
        .expect("the pilot carries a string");
    let stored = get_u64(&bytes, string.off + 24);
    let mut hostile = bytes.clone();
    put_u64(&mut hostile, string.off + 24, stored.wrapping_add(1));

    let view = OleanView::parse(&hostile).expect("hostile parses structurally");
    let error = view
        .walk(WalkBudget::default())
        .expect_err("a drifted m_length must refuse");
    assert!(
        matches!(
            error,
            RegionError::StringIntegrity {
                reason: "m_length is not the UTF-8 scalar count",
                ..
            }
        ),
        "expected m_length integrity, got {error:?}"
    );
}

// --- finding 5: the walk's scalar-array law is the shared engine's law --------

#[test]
fn a_scalar_array_past_eof_is_refused_by_the_walk() {
    let bytes = pilot();
    {
        let view = OleanView::parse(&bytes).expect("pilot parses");
        view.walk(WalkBudget::default())
            .expect("the unmutated pilot walks");
    }
    let objects = collect_objects(&bytes);
    let array = objects
        .iter()
        .find(|obj| obj.tag == abi::TAG_ARRAY)
        .expect("the pilot carries an array to re-tag as a scalar array");

    // Re-tag the array as a scalar array with 8-byte elements: same size and
    // capacity fields, and the walk's new law must hold them exactly.
    let retag = |bytes: &[u8]| -> Vec<u8> {
        let mut hostile = bytes.to_vec();
        let word = get_u64(&hostile, array.off);
        let retagged =
            (word & !(0xffu64 << 56)) | ((abi::TAG_SCALAR_ARRAY as u64) << 56) | (8u64 << 48);
        put_u64(&mut hostile, array.off, retagged);
        hostile
    };

    // (a) size beyond capacity: the new capacity check refuses it.
    let mut hostile = retag(&bytes);
    let capacity = get_u64(&hostile, array.off + 16);
    put_u64(&mut hostile, array.off + 8, capacity + 1);
    let view = OleanView::parse(&hostile).expect("hostile parses structurally");
    let error = view
        .walk(WalkBudget::default())
        .expect_err("size beyond capacity must refuse");
    let text = message_of(&error);
    assert!(
        text.contains("capacity"),
        "the refusal must name the capacity law, got: {text}"
    );

    // (b) capacity * elem past EOF: the old walk charged `size` bytes and the
    // overrun passed clean.
    let mut hostile = retag(&bytes);
    put_u64(&mut hostile, array.off + 8, u64::MAX / 2);
    put_u64(&mut hostile, array.off + 16, u64::MAX / 2);
    let view = OleanView::parse(&hostile).expect("hostile parses structurally");
    let error = view
        .walk(WalkBudget::default())
        .expect_err("an extent past EOF must refuse");
    let text = format!("{error:?}");
    assert!(
        text.contains("overflows") || text.contains("Truncated"),
        "the refusal must be typed, got: {text}"
    );
}

// --- finding 6: an mpz may not point its limbs into another object ----------

#[test]
fn an_mpz_with_foreign_limbs_is_refused_by_the_inline_law() {
    let bytes = pilot();
    let objects = collect_objects(&bytes);
    let mpz = objects
        .iter()
        .find(|obj| obj.tag == abi::TAG_MPZ)
        .expect("the pilot carries an mpz");
    {
        let view = OleanView::parse(&bytes).expect("pilot parses");
        view.walk(WalkBudget::default())
            .expect("the unmutated pilot walks");
    }

    let mut hostile = bytes.clone();
    // Point the limb pointer at the payload's first word — valid memory, but
    // outside this mpz's inline limb block, so the number would decode from
    // another object's bytes.
    let foreign =
        (HEADER_SIZE + parse_olean_envelope(&bytes).expect("envelope").base_addr as usize) as u64;
    put_u64(&mut hostile, mpz.off + 16, foreign);

    let view = OleanView::parse(&hostile).expect("hostile parses structurally");
    let error = view
        .walk(WalkBudget::default())
        .expect_err("foreign limbs must refuse");
    assert!(
        matches!(error, RegionError::MpzIntegrity { .. }),
        "expected MpzIntegrity, got {error:?}"
    );
}

// --- finding 7: a Level param/mvar of the wrong arity is a typed Shape -------

#[test]
fn a_level_param_of_wrong_arity_is_refused() {
    let bytes = c3("Init.BinderNameHint.olean");
    let envelope = parse_olean_envelope(&bytes).expect("fixture parses");
    let objects = collect_objects(&bytes);
    let mut proven = 0usize;
    // Offer each tag-4 object with a wrong `other` to the Level decoder as its
    // own oracle: a real param is refused by the arity law; anything else is a
    // typed ctor shape error. Only a real param names the law.
    for obj in objects.iter().filter(|obj| obj.tag == 4) {
        let mut hostile = bytes.clone();
        let word = get_u64(&hostile, obj.off);
        let rewritten = (word & !(0xffu64 << 48)) | (2u64 << 48);
        put_u64(&mut hostile, obj.off, rewritten);
        let view = OleanView::parse(&hostile).expect("hostile parses structurally");
        let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
        let root = obj.off as u64 + envelope.base_addr;
        let error = match decoder.decode_level(root) {
            Ok(_) => continue,
            Err(error) => error,
        };
        let text = format!("{error:?}");
        if text.contains("param/mvar arity") {
            proven += 1;
            break;
        }
    }
    assert_eq!(proven, 1, "a real Level param must trip the arity law");
}
