//! Declaration-decoder suite (bead franken_lean-z6c seed): real pinned-Reference
//! declarations decoded from the C3 fixture corpus, with the identity-layer
//! cross-checks (Name.hash / Level.Data / Expr.Data) that make a layout misread
//! or a hash-law divergence a typed error rather than silent corruption.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::path::PathBuf;

use fln_core::expr::{Expr, ExprNode, Literal, NatLit};
use fln_env::constants::ConstantInfo;
use fln_olean::decl::{DeclDecoder, DeclError};
use fln_olean::region::{OleanView, WalkBudget};
use fln_rt::abi;
use fln_rt::region::parse_olean_envelope;

fn fixture(name: &str) -> Vec<u8> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tribunal/fixtures/c3")
        .join(name);
    let data = std::fs::read(&path);
    assert!(
        data.is_ok(),
        "missing C3 fixture {}: {:?}",
        path.display(),
        data.err()
    );
    data.expect("asserted above")
}

/// Locate real pinned `.olean` companion chains. A host without the pin cannot
/// run this corpus regression, but must not replace it with a synthetic graph:
/// the omission occurred only across the Reference module-system sidecars.
fn reference_lib() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var("FLN_REFERENCE_LIB") {
        let path = PathBuf::from(dir);
        return path.is_dir().then_some(path);
    }
    let home = std::env::var("HOME").ok()?;
    let path = PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
    path.is_dir().then_some(path)
}

/// The four modules named in the `franken_lean-timy` investigation contain the
/// equation-compiler families that public-only decoding had omitted.
fn companion_and_public_names() -> Option<(BTreeSet<String>, BTreeSet<String>)> {
    let reference_lib = reference_lib()?;
    let modules = [
        "Init/Prelude",
        "Init/Data/List/ToArrayImpl",
        "Init/Data/Array/Basic",
        "Init/Control/MonadAttach",
    ];
    let mut public_names = BTreeSet::new();
    let mut private_names = BTreeSet::new();

    for module in modules {
        let artifact = reference_lib.join(format!("{module}.olean"));
        let server = artifact.with_extension("olean.server");
        let private = artifact.with_extension("olean.private");
        let public_bytes = std::fs::read(&artifact)
            .unwrap_or_else(|error| panic!("read public {}: {error}", artifact.display()));
        let server_bytes = std::fs::read(&server)
            .unwrap_or_else(|error| panic!("read server {}: {error}", server.display()));
        let private_bytes = std::fs::read(&private)
            .unwrap_or_else(|error| panic!("read private {}: {error}", private.display()));

        let public_view = OleanView::parse(&public_bytes)
            .unwrap_or_else(|error| panic!("parse public {}: {error}", artifact.display()));
        public_names.extend(
            DeclDecoder::new(&public_view, WalkBudget::default())
                .decode_module_constants()
                .unwrap_or_else(|error| panic!("decode public {}: {error}", artifact.display()))
                .into_iter()
                .map(|info| info.name().to_display_string()),
        );

        let private_view = OleanView::parse_with_dependencies(
            &private_bytes,
            &[public_bytes.as_slice(), server_bytes.as_slice()],
        )
        .unwrap_or_else(|error| panic!("parse private {}: {error}", private.display()));
        private_names.extend(
            DeclDecoder::new(&private_view, WalkBudget::default())
                .decode_module_constants()
                .unwrap_or_else(|error| panic!("decode private {}: {error}", private.display()))
                .into_iter()
                .map(|info| info.name().to_display_string()),
        );
    }

    Some((public_names, private_names))
}

fn numbered_private_auxiliary(name: &str, prefix: &str) -> bool {
    name.rsplit('.').next().is_some_and(|segment| {
        segment.strip_prefix(prefix).is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
    })
}

fn has_component(name: &str, component: &str) -> bool {
    name.split('.').skip(1).any(|part| part == component)
}

fn assert_private_auxiliary_family(family: &str, belongs_to_family: impl Fn(&str) -> bool) {
    let Some((public_names, private_names)) = companion_and_public_names() else {
        return;
    };
    // `_private.` describes Lean's declaration-name mangling, not which part
    // of a module-system chain introduced the declaration. Derive origin from
    // the actual exported/private arrays so a public-overlap helper cannot
    // turn the family regression into a false RED.
    let restored: Vec<_> = private_names
        .iter()
        .filter(|name| !public_names.contains(*name) && belongs_to_family(name))
        .collect();
    assert!(
        !restored.is_empty(),
        "complete private companion decode omitted every {family} auxiliary"
    );
}

#[test]
fn private_companion_decodes_match_n_auxiliaries() {
    assert_private_auxiliary_family("match_N", |name| numbered_private_auxiliary(name, "match_"));
}

#[test]
fn private_companion_decodes_proof_n_auxiliaries() {
    assert_private_auxiliary_family("_proof_N", |name| {
        numbered_private_auxiliary(name, "_proof_")
    });
}

#[test]
fn private_companion_decodes_loop_auxiliaries() {
    assert_private_auxiliary_family(".loop", |name| has_component(name, "loop"));
}

#[test]
fn private_companion_decodes_eq_n_auxiliaries() {
    assert_private_auxiliary_family("eq_N", |name| numbered_private_auxiliary(name, "eq_"));
}

#[test]
fn binder_name_hint_declarations_decode_with_crosschecks() {
    let bytes = fixture("Init.BinderNameHint.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    // Cross-checks default ON: every Name.hash / Level.Data / Expr.Data word
    // in these declarations must equal our recomputation, or decode errors.
    let infos = decoder.decode_module_constants().expect("decode");
    assert_eq!(infos.len(), 2);

    let names: Vec<String> = infos.iter().map(|i| i.name().to_display_string()).collect();
    assert!(names.iter().any(|n| n == "binderNameHint"), "{names:?}");

    // binderNameHint is a def: `@[reducible] def binderNameHint ... := ...`.
    let def = infos
        .iter()
        .find(|i| i.name().to_display_string() == "binderNameHint");
    assert!(
        matches!(def, Some(ConstantInfo::Defn(_))),
        "expected a definition"
    );
}

#[test]
fn size_of_lemmas_theorems_and_defs_decode() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    let infos = decoder.decode_module_constants().expect("decode");
    assert_eq!(infos.len(), 16);
    let thms = infos
        .iter()
        .filter(|i| matches!(i, ConstantInfo::Thm(_)))
        .count();
    let defs = infos
        .iter()
        .filter(|i| matches!(i, ConstantInfo::Defn(_)))
        .count();
    let axioms = infos
        .iter()
        .filter(|i| matches!(i, ConstantInfo::Axiom(_)))
        .count();
    assert_eq!(
        (axioms, defs, thms),
        (9, 0, 7),
        "kind census for SizeOfLemmas"
    );

    // Every constant carries a well-formed type; theorems carry a value.
    for info in &infos {
        assert!(!info.name().to_display_string().is_empty());
        if let ConstantInfo::Thm(t) = info {
            // A theorem's type is a Prop-shaped statement; at minimum it and
            // its proof decoded without a cross-check failure (already proven
            // by reaching here). Spot-check the level-param arity is sane.
            assert!(t.base.level_params.len() <= 8);
        }
    }
}

#[test]
fn crosscheck_catches_a_corrupted_hash_word() {
    // Flip a bit somewhere in the data region and demand that decoding either
    // fails typed (a cross-check or shape error) or returns Ok — but NEVER
    // panics. Reaching the end of the loop is itself the no-panic proof
    // (FL-INV-07). The constant-decoder only traverses declarations reachable
    // from the `constants` array, so flips landing in extension payloads or
    // unreferenced objects legitimately leave the decoded set unchanged; the
    // detection floor below asserts the cross-checks are genuinely live without
    // demanding coverage of unreachable bytes. Deterministic sweep.
    let good = fixture("Init.BinderNameHint.olean");
    let mut seed: u64 = 0x7a_36_63_5f_69_6f_74_61;
    let mut flips = 0u32;
    let mut typed = 0u32;
    while flips < 200 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let pos = 88 + (seed as usize) % (good.len() - 88);
        let mut bad = good.clone();
        bad[pos] ^= 1 << ((seed >> 40) % 8);
        flips += 1;
        if let Ok(view) = OleanView::parse(&bad) {
            let mut decoder = DeclDecoder::new(
                &view,
                WalkBudget {
                    max_objects: 2_000_000,
                },
            );
            if decoder.decode_module_constants().is_err() {
                typed += 1;
            }
        } else {
            typed += 1;
        }
    }
    assert_eq!(flips, 200);
    assert!(
        typed > 25,
        "only {typed}/200 flips detected — cross-checks not live"
    );
}

#[test]
fn disabling_crosscheck_still_decodes_clean_fixtures() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    decoder.cross_check = false;
    let infos = decoder
        .decode_module_constants()
        .expect("decode without cross-check");
    assert_eq!(infos.len(), 16);
}

#[test]
fn budget_exhaustion_is_typed() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let mut decoder = DeclDecoder::new(&view, WalkBudget { max_objects: 5 });
    let r = decoder.decode_module_constants();
    assert!(matches!(r, Err(DeclError::Budget { .. })), "{r:?}");
}

/// A real pinned declaration decodes to a **DAG, not a tree** (bead `fln-sv7x`).
///
/// # The read half of "serialization preserving sharing exactly"
///
/// `fln-sv7x` asks for sharing to survive both codecs. Only half of that is even
/// coherent, and only half is reachable today:
///
/// * `fln-hash`'s `Canonical` must be sharing-**independent** — it is documented as
///   "a value with exactly one canonical encoding under a frozen schema", so a
///   sharing-sensitive encoder there would give one value many encodings and move
///   every content-addressed digest with construction history. Pinned separately by
///   `fln-env`'s `interning_rewrites_sharing_and_canonical_bytes_do_not_move`.
/// * The **olean** codec is where sharing preservation is a genuine requirement: the
///   artifact is storage, not an identity preimage, and expanding a shared DAG into a
///   tree is a real resource defect — `k` levels of two-way sharing become `2^k`
///   written nodes.
///
/// The olean **writer does not exist** (`decode_expr` has no encoder beside it), so the
/// round trip cannot be asserted yet. This pins the half that does exist and that the
/// future encoder must match: `DeclDecoder::decode_expr` memoises on the object offset,
/// so two slots pointing at one object become two references to one `Expr` node rather
/// than two equal nodes.
///
/// # Why the assertion is on node identity rather than on a count
///
/// Structural equality cannot see this: a tree and a DAG denoting the same term are
/// `==`. Neither can a round-trip check, which a sharing-losing decoder also passes. The
/// only thing that discriminates is pointer identity of the decoded nodes, which is what
/// this counts — and a failure here means either the decoder expanded, or the chosen
/// fixture genuinely has no shared subterm, so the message says which to check.
#[test]
fn real_declarations_decode_to_shared_dags_not_expanded_trees() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    let infos = decoder.decode_module_constants().expect("decode");

    // Walk one type expression, counting tree POSITIONS against DISTINCT nodes.
    // A tree has one node per position; a DAG has fewer.
    fn measure(expr: &fln_core::expr::Expr) -> (usize, std::collections::HashSet<usize>) {
        use fln_core::expr::ExprNode;
        let mut positions = 0usize;
        let mut distinct = std::collections::HashSet::new();
        let mut stack = vec![expr];
        while let Some(current) = stack.pop() {
            positions += 1;
            distinct.insert(std::ptr::from_ref(current.node()) as usize);
            match current.node() {
                ExprNode::App { f, a } => {
                    stack.push(f);
                    stack.push(a);
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    stack.push(binder_type);
                    stack.push(body);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    stack.push(type_);
                    stack.push(value);
                    stack.push(body);
                }
                // Both carry their single child under the same field name.
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    stack.push(expr);
                }
                _ => {}
            }
        }
        (positions, distinct)
    }

    let mut shared_declarations = 0usize;
    for info in &infos {
        let (positions, distinct) = measure(&info.constant_val().type_);
        if distinct.len() < positions {
            shared_declarations += 1;
        }
    }

    assert!(
        shared_declarations > 0,
        "no decoded declaration retained a shared subterm across {} constants: either \
         decode_expr stopped memoising on the object offset (the defect this pins), or \
         this fixture's declarations genuinely contain no shared subterm (pick another)",
        infos.len()
    );
}

/// One object in a fixture's pointer graph, with the size word the codec's
/// list walker discards.
#[derive(Debug, Clone, Copy)]
struct Obj {
    off: usize,
    tag: u8,
    other: u8,
    cs_sz: u16,
}

fn word_at(bytes: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(bytes[off..off + 8].try_into().expect("in-range read"))
}

/// Walk every reachable object, same layout law the codec enforces. This is a
/// local walker on purpose: `OleanView`'s `deref`/`obj_header` are
/// `pub(crate)`, and an integration test must not grow the crate's public
/// surface to see bytes it can read itself. `hostile_input.rs` does the same.
fn objects_of(bytes: &[u8]) -> (Vec<Obj>, u64) {
    const HEADER_SIZE: usize = 88; // format::OLEAN_HEADER_SIZE
    let envelope = parse_olean_envelope(bytes).expect("fixture parses");
    let base = envelope.base_addr;
    let deref = |ptr: u64| -> Option<usize> {
        if ptr & 1 == 1 || ptr == 0 {
            return None;
        }
        let resolved = usize::try_from(ptr.checked_sub(base)?).ok()?;
        (resolved >= HEADER_SIZE && resolved + 8 <= bytes.len() && resolved % 8 == 0)
            .then_some(resolved)
    };
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut stack = vec![word_at(bytes, HEADER_SIZE)];
    let mut out = Vec::new();
    while let Some(ptr) = stack.pop() {
        let Some(off) = deref(ptr) else { continue };
        if !seen.insert(off) {
            continue;
        }
        let word = word_at(bytes, off);
        let tag = ((word >> 56) & 0xff) as u8;
        let other = ((word >> 48) & 0xff) as u8;
        let cs_sz = ((word >> 32) & 0xffff) as u16;
        if tag <= abi::TAG_MAX_CTOR_TAG {
            for i in 0..other as usize {
                let field = off + 8 + 8 * i;
                if field + 8 <= bytes.len() {
                    stack.push(word_at(bytes, field));
                }
            }
        } else if tag == abi::TAG_ARRAY {
            let size = word_at(bytes, off + 8);
            for i in 0..size.min(1 << 16) {
                let field = off + 24 + 8 * i as usize;
                if field + 8 <= bytes.len() {
                    stack.push(word_at(bytes, field));
                }
            }
        }
        out.push(Obj {
            off,
            tag,
            other,
            cs_sz,
        });
    }
    (out, base)
}

/// A `Name.str` link and a `List.cons` cell are separated ONLY by their stored
/// size, and the decoder's list walker does not read it.
///
/// `list_ptrs` (`decl.rs`) accepts a cons cell on `tag == 1 && other == 2` and
/// discards `cs_sz`. `Name.str` is also tag 1 with two pointer fields. So the
/// rule cannot reject a name where a list belongs, and the confusion is
/// reachable: `levelParams` is slot 1 of a `ConstantVal` while `induct` - a
/// `Name` - is slot 1 of the `ConstructorVal` that contains it.
///
/// THE CLASSIFICATION HERE DOES NOT USE THE SIZE, which is the whole point. An
/// object is called a name link when its second field points at a STRING, and a
/// cons cell when its second field is boxed nil or another cell of the same
/// shape. That discriminator is independent of `cs_sz`, so the sizes it then
/// reports are a measurement rather than a restatement of the premise.
///
/// This is the corpus measurement `bad3bd20` recorded as missing before
/// `list_ptrs` could be repaired, made over real pinned declarations. It is not
/// the repair: nothing here changes `src`.
#[test]
fn a_name_link_and_a_cons_cell_collide_on_shape_and_differ_only_in_size() {
    let mut name_sizes: BTreeSet<u16> = BTreeSet::new();
    let mut cons_sizes: BTreeSet<u16> = BTreeSet::new();
    let mut names = 0usize;
    let mut cells = 0usize;

    for module in [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ] {
        let bytes = fixture(module);
        let (objects, base) = objects_of(&bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();

        for object in &objects {
            if (object.tag, object.other) != (1, 2) {
                continue;
            }
            let second = word_at(&bytes, object.off + 16);
            let target = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| at.get(&off));
            match target {
                // `Name.str prefix component` - the component is a string.
                Some(t) if t.tag == abi::TAG_STRING => {
                    names += 1;
                    name_sizes.insert(object.cs_sz);
                }
                // `List.cons head tail` - the tail is another cell...
                Some(t) if (t.tag, t.other) == (1, 2) => {
                    cells += 1;
                    cons_sizes.insert(object.cs_sz);
                }
                // ...or boxed `List.nil`.
                None if second & 1 == 1 && second >> 1 == 0 => {
                    cells += 1;
                    cons_sizes.insert(object.cs_sz);
                }
                _ => {}
            }
        }
    }

    // Anti-vacuity: the collision must be real in this corpus, not a shape
    // two populations could occupy. Both are reached, at the same tag and
    // arity, and no rule the list walker applies can tell them apart.
    assert!(
        names > 0 && cells > 0,
        "both shapes must occur, or the collision is hypothetical and the \
         sizes below describe one population: {names} name links, {cells} cons \
         cells"
    );
    assert_eq!(
        name_sizes.len(),
        1,
        "every name link must carry ONE size, or `cs_sz` cannot separate the \
         two shapes: {name_sizes:?}"
    );
    assert_eq!(
        cons_sizes.len(),
        1,
        "every cons cell must carry ONE size, for the same reason: \
         {cons_sizes:?}"
    );
    let name_size = *name_sizes.iter().next().expect("asserted non-empty");
    let cons_size = *cons_sizes.iter().next().expect("asserted non-empty");
    assert_ne!(
        name_size, cons_size,
        "the stored size is the ONLY field that separates a name link from a \
         cons cell; if these were equal, no size rule could repair `list_ptrs` \
         and the hole would need a different fix"
    );
    assert!(
        cons_size < name_size,
        "a name link is a cons cell's two pointers PLUS the stored hash word, \
         so it must be the larger of the two: cons {cons_size}, name \
         {name_size}"
    );
    // Already corpus-measured and enforced by `decode_name`'s own size rule,
    // so this cannot be wrong without that rule being wrong too.
    assert_eq!(name_size, 32, "Name.str/num link");
}

/// The decoder consumes a `Name.str` link as a cons cell, and refuses only at
/// the NEXT hop. A live witness for the hole measured above.
///
/// The plant repoints one `ConstantVal`'s `levelParams` - slot 1, the exact
/// slot a `ConstructorVal`'s `induct` occupies one level out - at a real name
/// link. If `list_ptrs` read the size, it would refuse AT that link. It does
/// not: it accepts the link as a cell, takes the name's PREFIX as a list
/// member, takes the name's STRING as the tail, and fails on the string.
///
/// The assertion is the OFFSET, not merely that decoding failed. A cell that
/// only required an error would pass just as well against a decoder that
/// refused at the name link for the right reason, and would therefore go on
/// passing after the repair while silently ceasing to witness anything.
#[test]
fn a_planted_name_link_is_consumed_as_a_cons_cell_before_anything_refuses() {
    let mut bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect("the unmodified fixture decodes");

    let (objects, base) = objects_of(&bytes);
    let at: std::collections::BTreeMap<usize, Obj> = objects.iter().map(|o| (o.off, *o)).collect();

    // A real `Name.str` link, and the string its second field points at.
    let (link, string_off) = objects
        .iter()
        .find_map(|object| {
            if (object.tag, object.other) != (1, 2) {
                return None;
            }
            let second = word_at(&bytes, object.off + 16);
            if second & 1 == 1 {
                return None;
            }
            let off = usize::try_from(second.checked_sub(base)?).ok()?;
            (at.get(&off)?.tag == abi::TAG_STRING).then_some((*object, off))
        })
        .expect("the fixture carries name links");

    // A `ConstantVal`: three pointer fields, no scalars. Its slot 1 is
    // `levelParams`.
    let constant_val = objects
        .iter()
        .find(|object| (object.tag, object.other) == (0, 3))
        .copied()
        .expect("the fixture carries ConstantVals");

    let planted = base + u64::try_from(link.off).expect("in-range");
    bytes[constant_val.off + 16..constant_val.off + 24].copy_from_slice(&planted.to_le_bytes());

    let view = OleanView::parse(&bytes).expect("the plant changes no header");
    let error = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect_err("a name where a list belongs must not decode");

    match error {
        DeclError::Shape { offset, what } => {
            assert_eq!(
                what, "List cons",
                "the refusal comes from the list walker, not from a name rule"
            );
            assert_eq!(
                offset,
                u64::try_from(string_off).expect("in-range"),
                "and it names the STRING, which is only reachable by having \
                 already accepted the name link as a cell and walked to its \
                 tail. Naming the link itself would mean the walker had \
                 rejected it on shape - the repair, not the hole."
            );
        }
        other => panic!("expected a List cons shape refusal, got {other}"),
    }
}

/// The SAME collision in the other direction is already closed, and by exactly
/// the rule `list_ptrs` is missing.
///
/// Its sibling above plants a `Name.str` link where a list belongs and shows
/// the list walker consuming it. This cell plants a real `List.cons` cell where
/// a NAME belongs. `decode_name` applies the identical shape test first -
/// `tag == 1 || tag == 2` and `other == 2` - and a cons cell passes it, so the
/// two are indistinguishable at that layer in both directions. What catches it
/// is the next line: `decode_name` also requires `cs_sz == 32`, and refuses.
///
/// So the repair for `list_ptrs` is not a new idea that needs designing. It is
/// the rule its neighbour in the same file already applies, ten functions away,
/// against a corpus measurement of 5,842,155 objects. The pair of witnesses is
/// what turns that from a claim into a demonstrated asymmetry: one direction
/// reads the size and refuses at the planted object, the other does not and
/// walks into it.
///
/// THE ANTI-VACUITY GUARD IS THE REFUSAL'S IDENTITY. If the planted cell were
/// caught by the `Name ctor` shape rule instead, this cell would pass while
/// proving the opposite of what it says - that the shapes are distinguishable
/// without the size. It therefore asserts the message is the SIZE rule's, and
/// separately that the planted cell really does carry the colliding tag and
/// arity and a size other than 32.
#[test]
fn a_planted_cons_cell_is_refused_by_the_name_size_rule_the_list_walker_lacks() {
    let mut bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("parse");
    let infos = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect("the unmodified fixture decodes");

    // The census this module is pinned to, two cells above. The plant's target
    // is taken FROM it rather than guessed: whichever declaration the chosen
    // `ConstantVal` belongs to must be one this module actually declares.
    assert_eq!(infos.len(), 16, "the pinned SizeOfLemmas constant census");
    let census: BTreeSet<String> = infos
        .iter()
        .map(|info| info.name().to_display_string())
        .collect();

    let (objects, base) = objects_of(&bytes);
    let at: std::collections::BTreeMap<usize, Obj> = objects.iter().map(|o| (o.off, *o)).collect();

    // A real cons cell, by the same size-independent discriminator the
    // measurement cell uses: its tail is another cell of the same shape, or
    // boxed `List.nil`.
    let cell = objects
        .iter()
        .find(|object| {
            if (object.tag, object.other) != (1, 2) {
                return false;
            }
            let tail = word_at(&bytes, object.off + 16);
            if tail & 1 == 1 {
                return tail >> 1 == 0;
            }
            usize::try_from(tail.wrapping_sub(base))
                .ok()
                .and_then(|off| at.get(&off))
                .is_some_and(|t| (t.tag, t.other) == (1, 2))
        })
        .copied()
        .expect("the fixture carries cons cells");

    // Without these the refusal below could be the shape rule firing, and the
    // cell would read as proof that the size is not needed.
    assert_eq!(
        (cell.tag, cell.other),
        (1, 2),
        "the planted object must collide with a name link on tag and arity, or \
         `decode_name`'s shape rule catches it and the size rule is never \
         reached"
    );
    assert_ne!(
        cell.cs_sz, 32,
        "and it must differ in size, or there is nothing for the size rule to \
         refuse"
    );

    // A `ConstantVal` - three pointer fields, no scalars - whose slot 0 is the
    // declaration's name. Confirm the declaration is one the census names.
    let (constant_val, declaration) = objects
        .iter()
        .find_map(|object| {
            if (object.tag, object.other) != (0, 3) {
                return None;
            }
            let name = DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(word_at(&bytes, object.off + 8))
                .ok()?
                .to_display_string();
            census.contains(&name).then_some((*object, name))
        })
        .expect("a ConstantVal naming a declaration this module declares");

    let planted = base + u64::try_from(cell.off).expect("in-range");
    bytes[constant_val.off + 8..constant_val.off + 16].copy_from_slice(&planted.to_le_bytes());

    let view = OleanView::parse(&bytes).expect("the plant changes no header");
    let error = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect_err("a cons cell where a name belongs must not decode");

    match error {
        DeclError::Shape { offset, what } => {
            assert_eq!(
                what, "Name object size disagrees with its two-pointer-plus-hash layout",
                "{declaration}: the refusal must come from the SIZE rule. The \
                 `Name ctor` shape rule ran first and let this object through, \
                 which is the whole point - a cons cell and a name link are the \
                 same tag and arity"
            );
            assert_eq!(
                offset,
                u64::try_from(cell.off).expect("in-range"),
                "{declaration}: and it names the planted cell itself, refusing \
                 AT the colliding object rather than one hop later - which is \
                 exactly what the sibling witness shows `list_ptrs` failing to \
                 do"
            );
        }
        other => panic!("expected a Name size refusal, got {other}"),
    }
}

/// RECORDS the cons cell's stored size, derived from the object's own header
/// rather than written down.
///
/// `c48c0813` established that a name link and a cons cell differ in `cs_sz`,
/// which is what makes the `list_ptrs` repair possible. It deliberately did not
/// write the cons cell's number: that was the one value I had reasoned to and
/// not measured, and comments 2285/2286 record what writing such a literal
/// costs. But a passing test prints nothing, so the measurement existed and the
/// number stayed unrecorded, and the src repair has been waiting on it.
///
/// THE WAY OUT IS NOT TO GUESS BETTER, IT IS TO DERIVE. Every Lean object's
/// size is its header, plus one word per declared pointer field, plus whatever
/// scalar area the constructor stores after them. `other` is on the wire. So
/// the SCALAR AREA WIDTH is measurable per object as
/// `cs_sz - (8 + 8 * other)`, and it is that width - not the total - that
/// actually separates the two shapes: a cons cell stores nothing after its two
/// pointers, a name link stores the `Name.hash` word. `decode_name`'s own
/// comment states the same arithmetic for its side, as `8 + 8*2 + 8`.
///
/// The literal below is therefore ENTAILED rather than asserted: the cell first
/// proves the scalar width is zero and the arity is two, both from the bytes,
/// and only then records what that makes the size. If the corpus disagrees the
/// derivation fails first and names the real number, which is the ordering
/// `f193516d` had to correct in `decode_level` - a literal checked before the
/// rule that explains it teaches the reader nothing when it fires.
///
/// This records a measurement. It is not the repair, and it does not make one:
/// `list_ptrs` still reads no size.
#[test]
fn the_cons_cell_scalar_area_is_empty_and_that_is_what_fixes_its_size() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();

    // Corpus scale where the pin is installed; the C3 fixtures alone still
    // carry enough cells to measure, so a host without it is not skipped.
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
        }
    }

    let mut cells = 0usize;
    let mut links = 0usize;
    let mut cons_widths: BTreeSet<i64> = BTreeSet::new();
    let mut name_widths: BTreeSet<i64> = BTreeSet::new();
    let mut cons_sizes: BTreeSet<u16> = BTreeSet::new();
    let mut cons_arities: BTreeSet<u8> = BTreeSet::new();

    for (_module, bytes) in &modules {
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();

        for object in &objects {
            if (object.tag, object.other) != (1, 2) {
                continue;
            }
            // The scalar area this object stores after its declared pointers.
            let width = i64::from(object.cs_sz) - (8 + 8 * i64::from(object.other));
            let second = word_at(bytes, object.off + 16);
            let target = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| at.get(&off));
            match target {
                Some(t) if t.tag == abi::TAG_STRING => {
                    links += 1;
                    name_widths.insert(width);
                }
                Some(t) if (t.tag, t.other) == (1, 2) => {
                    cells += 1;
                    cons_widths.insert(width);
                    cons_sizes.insert(object.cs_sz);
                    cons_arities.insert(object.other);
                }
                None if second & 1 == 1 && second >> 1 == 0 => {
                    cells += 1;
                    cons_widths.insert(width);
                    cons_sizes.insert(object.cs_sz);
                    cons_arities.insert(object.other);
                }
                _ => {}
            }
        }
    }

    // Anti-vacuity: a measurement over nothing reports whatever it likes.
    assert!(
        cells >= 100 && links >= 100,
        "too few objects to call this a measurement: {cells} cons cells, \
         {links} name links across {} modules",
        modules.len()
    );

    // The derivation, from the wire, before any literal.
    assert_eq!(
        cons_widths.len(),
        1,
        "a cons cell's scalar area must be one width across the corpus, or \
         there is no single rule to give `list_ptrs`: {cons_widths:?}"
    );
    assert_eq!(
        cons_widths.iter().next().copied(),
        Some(0),
        "a `List.cons` stores head and tail and NOTHING after them; a non-zero \
         width here would mean the layout is not what the repair assumes"
    );
    assert_eq!(
        name_widths.iter().next().copied(),
        Some(8),
        "a `Name.str` link stores the `Name.hash` word after its two pointers - \
         `decode_name`'s own comment derives this as 8 + 8*2 + 8 - and that \
         ONE word is the entire difference between the two shapes"
    );
    assert_eq!(
        cons_arities.iter().copied().collect::<Vec<_>>(),
        vec![2_u8],
        "and every cons cell declares exactly two pointer fields"
    );

    // Only now, entailed by the two facts above: header + two pointers + no
    // scalar area. THIS IS THE RECORDED MEASUREMENT the src repair was waiting
    // on, over the population counted above.
    assert_eq!(
        cons_sizes.iter().copied().collect::<Vec<_>>(),
        vec![24_u16],
        "measured `List.cons` stored size across {cells} cells in {} modules",
        modules.len()
    );
}

/// The measured cons cells are the ones the DECODER walked, not merely ones
/// reachable from the root.
///
/// CONFIRMED ABSENT BEFORE WRITING THIS. Every cell above - `c48c0813`'s
/// collision measurement, `35efc748`'s two witnesses, `ac97cb3a`'s derived
/// width - classifies objects by walking bytes from the root word. None of them
/// establishes that the objects so measured are the objects `list_ptrs`
/// traverses. That gap is invisible while the numbers agree and fatal if they
/// do not: a width measured over cells the decoder never visits would license a
/// size rule for a population the rule will not be applied to, and the repair
/// would be built on a measurement of the wrong set.
///
/// The binding is a COUNT, per declaration. For each `ConstantVal` on the wire
/// this walks its `levelParams` chain and counts the cells; for each decoded
/// constant it takes `level_params.len()`; and it requires the two to be equal
/// for that declaration by name. Equality in both directions is what makes the
/// populations the same one: no cell the decoder skipped, no name it invented.
/// Only then are the width and the size asserted, and they are asserted on the
/// cells that count bound.
///
/// THE FIRST VERSION OF THIS CELL WAS ITSELF THE DEFECT IT LOOKS FOR, and w113
/// caught it on `Init/Prelude.olean`. It treated `(tag, other, cs_sz) ==
/// (0, 3, 32)` as identifying a `ConstantVal` and asserted that every hop of
/// such an object's slot-1 chain was a cons cell. That header shape is
/// `ConstantVal`'s and ALSO other three-field structures'; on Prelude one of
/// them holds an array there, and the walk asserted `(246, 0) == (1, 2)`. The
/// C3 fixtures are too small to contain a collision, so the filter looked
/// injective for exactly as long as nobody ran it at scale - a projection keyed
/// as an identity without checking injectivity, which is the same defect this
/// file's other cells were written to catch.
///
/// The repair is not a looser assertion. A candidate must now also NAME a
/// declaration this module declares, and a candidate whose slot 1 is not a cons
/// chain is DROPPED rather than asserted against - a mismatch there is evidence
/// the object is something else, not evidence the corpus is malformed. The
/// binding then requires some candidate to carry a chain of exactly the decoded
/// length, and measures that chain. That is stronger than the version w113
/// killed, which accepted whatever chain the last same-named candidate happened
/// to leave behind.
///
/// The anti-vacuity guard is the total. Every assertion here is an equality
/// that a corpus of universe-monomorphic declarations satisfies as `0 == 0`,
/// so the cell would pass over an empty population and report a binding it
/// never made - the shape this campaign has been finding all week, arriving in
/// the denominator. It therefore requires the bound total to be positive and
/// prints it.
#[test]
fn the_measured_cons_cells_are_the_ones_the_decoder_walked() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
        }
    }

    let mut bound = 0usize;
    let mut declarations = 0usize;
    let mut widths: BTreeSet<i64> = BTreeSet::new();
    let mut sizes: BTreeSet<u16> = BTreeSet::new();

    for (module, bytes) in &modules {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let infos = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .unwrap_or_else(|e| panic!("{module}: decode: {e}"));

        let (objects, base) = objects_of(bytes);
        // Indexed once: Prelude carries enough objects that a linear scan per
        // chain hop would make this cell quadratic.
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let deref = |ptr: u64| -> Option<usize> {
            (ptr & 1 == 0)
                .then(|| usize::try_from(ptr.checked_sub(base)?).ok())
                .flatten()
        };

        // The names this module actually declares. A candidate that does not
        // name one of them is not a declaration's `ConstantVal`, whatever its
        // header says.
        let census: BTreeSet<String> = infos.iter().map(|i| i.name().to_display_string()).collect();

        // Candidate `ConstantVal`s by name, each with the cons chain its slot 1
        // carries. A candidate whose slot 1 is NOT a cons chain is dropped
        // rather than asserted against: the header shape is not a proof of
        // identity, so a mismatch there is evidence the object is something
        // else, not evidence the corpus is malformed.
        let mut candidates: std::collections::BTreeMap<String, Vec<Vec<Obj>>> =
            std::collections::BTreeMap::new();
        for object in &objects {
            // Necessary but NOT sufficient: three pointer fields and no scalar
            // area is `ConstantVal`'s shape and also other structures'.
            if (object.tag, object.other, object.cs_sz) != (0, 3, 32) {
                continue;
            }
            let Ok(name) = DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(word_at(bytes, object.off + 8))
            else {
                continue;
            };
            let name = name.to_display_string();
            if !census.contains(&name) {
                continue;
            }

            let mut cursor = word_at(bytes, object.off + 16);
            let mut chain: Vec<Obj> = Vec::new();
            let is_cons_chain = loop {
                if cursor & 1 == 1 {
                    break cursor >> 1 == 0; // boxed `List.nil` ends it
                }
                let Some(off) = deref(cursor) else {
                    break false;
                };
                let Some(cell) = at.get(&off) else {
                    break false;
                };
                if (cell.tag, cell.other) != (1, 2) {
                    break false;
                }
                if chain.len() == 4096 {
                    break false; // the post-order law forbids cycles; do not rely on it
                }
                chain.push(*cell);
                cursor = word_at(bytes, cell.off + 16);
            };
            if is_cons_chain {
                candidates.entry(name).or_default().push(chain);
            }
        }

        // The binding, per declaration: some `ConstantVal` on the wire must
        // carry a cons chain of exactly the length the decoder returned, and
        // the cells measured are that chain's.
        for info in &infos {
            let name = info.name().to_display_string();
            let decoded = info.constant_val().level_params.len();
            let chains = candidates.get(&name).map(Vec::as_slice).unwrap_or(&[]);
            let matching = chains
                .iter()
                .find(|chain| chain.len() == decoded)
                .unwrap_or_else(|| {
                    panic!(
                        "{module}: {name}: the decoder returned {decoded} universe \
                         parameters, and no ConstantVal on the wire carries a cons \
                         chain of that length. Candidate lengths: {:?}. Unequal \
                         means the cells measured by the cells above are not the \
                         cells `list_ptrs` walks, and the recorded width describes \
                         the wrong population",
                        chains.iter().map(Vec::len).collect::<Vec<_>>()
                    )
                });
            for cell in matching {
                widths.insert(i64::from(cell.cs_sz) - (8 + 8 * i64::from(cell.other)));
                sizes.insert(cell.cs_sz);
            }
            bound += decoded;
            declarations += 1;
        }
    }

    // Without this the equalities above are all `0 == 0` over a corpus with no
    // universe-polymorphic declarations, and the cell reports a binding it
    // never made.
    assert!(
        bound > 0,
        "no universe parameters were bound across {declarations} declarations \
         in {} modules; every equality above held vacuously",
        modules.len()
    );

    // Asserted on the bound cells only - the ones just proven to be the
    // decoder's - rather than on everything shaped like a cons cell.
    assert_eq!(
        widths.iter().copied().collect::<Vec<_>>(),
        vec![0_i64],
        "the cells the decoder walked store nothing after head and tail \
         ({bound} cells over {declarations} declarations)"
    );
    assert_eq!(
        sizes.iter().copied().collect::<Vec<_>>(),
        vec![24_u16],
        "and the size that follows from that width, on the same population"
    );
}

/// A THIRD SHAPE SHARES THE CONS CELL'S HEADER, and it bounds the repair.
///
/// This cell asserted the opposite until w115 measured it. The claim was that
/// `cs_sz` identifies the two shapes at `(tag, other) == (1, 2)`, so a size
/// rule in `list_ptrs` would be safe. Over 7,591 such objects, 99 are 24 bytes
/// with a tail that is neither a cons cell nor boxed nil - the first at
/// `Init/Prelude.olean` offset `0x32e7d0`.
///
/// SO THE ONE-LINE FIX I RECOMMENDED FOR FIVE COMMITS IS WRONG. A refusal keyed
/// on `cs_sz != 24` would accept those 99 as cons cells; a rule that instead
/// demanded 24 would reject nothing extra, but the size still does not say
/// "this is a list", which is what `list_ptrs` needs to know. Size separates a
/// name link from a cons cell - that much held, and the two planted witnesses
/// still stand - but separating two shapes is not identifying one.
///
/// NOTE WHICH ASSERTION SURVIVED, because it locates the defect. The partition
/// by size is still exhaustive: every `(1, 2)` object is 24 or 32, and no third
/// SIZE exists. The third shape hides INSIDE 24. A cell that had only counted
/// sizes would still be green and still be wrong, which is why this one looks
/// at what the tail points at.
///
/// WHAT THE 99 ARE IS NOT KNOWN, and this cell does not pretend otherwise. It
/// splits the 24-byte population into cons-shaped and this third tail, pins the
/// remainder at its measured count so the blocker cannot quietly disappear, and
/// carries a characterisation of the tails into the failure message for
/// whoever reads it next. Identifying them is the next piece of work, not a
/// guess to be recorded here.
///
/// The pinned count is asserted only where `Init/Prelude.olean` was actually
/// loaded, because that is the corpus it was measured over; the C3 fixtures
/// alone do not contain it.
#[test]
fn a_third_shape_shares_the_cons_cell_header_and_bounds_the_size_rule() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut population = 0usize;
    let mut cons_shaped = 0usize;
    let mut third_tail = 0usize;
    let mut name_shaped = 0usize;
    let mut name_misfits = 0usize;
    let mut unexpected_sizes: BTreeSet<u16> = BTreeSet::new();
    let mut tail_kinds: BTreeSet<String> = BTreeSet::new();
    let mut first_third: Option<String> = None;

    for (module, bytes) in &modules {
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();

        for object in &objects {
            if (object.tag, object.other) != (1, 2) {
                continue;
            }
            population += 1;

            let second = word_at(bytes, object.off + 16);
            let target = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| at.get(&off));
            let ends_the_list = second & 1 == 1 && second >> 1 == 0;
            let looks_like_cons =
                ends_the_list || target.is_some_and(|t| (t.tag, t.other) == (1, 2));
            let looks_like_name = target.is_some_and(|t| t.tag == abi::TAG_STRING);

            match object.cs_sz {
                24 if looks_like_cons => cons_shaped += 1,
                24 => {
                    third_tail += 1;
                    // What the tail actually is, so the remainder is described
                    // rather than merely counted.
                    tail_kinds.insert(match target {
                        Some(t) => format!("object tag {} arity {}", t.tag, t.other),
                        None if second & 1 == 1 => {
                            format!("boxed scalar {}", second >> 1)
                        }
                        None => "unresolvable pointer".to_owned(),
                    });
                    first_third.get_or_insert_with(|| format!("{module} {:#x}", object.off));
                }
                32 if looks_like_name => name_shaped += 1,
                32 => name_misfits += 1,
                other => {
                    unexpected_sizes.insert(other);
                }
            }
        }
    }

    // Anti-vacuity, unchanged: an exhaustive partition of nothing partitions
    // nothing, and both sizes must actually occur.
    assert!(
        population >= 100,
        "too few (1,2) objects to bound the population: {population}"
    );
    assert!(
        cons_shaped > 0 && name_shaped > 0,
        "both shapes must occur, or one size is unwitnessed: {cons_shaped} at \
         24, {name_shaped} at 32"
    );

    // The partition is still exhaustive by ARITHMETIC, and it still holds:
    // there is no third SIZE. That is what makes the third shape interesting.
    assert_eq!(
        cons_shaped + third_tail + name_shaped + name_misfits,
        population,
        "the partition must account for every object"
    );
    assert!(
        unexpected_sizes.is_empty(),
        "a third SIZE appeared at (1,2), which is a different finding from the \
         third shape below: {unexpected_sizes:?}"
    );

    // The remainder, pinned rather than asserted away. A change in either
    // direction is a finding: shrinking to zero would mean the blocker is gone
    // and the size rule is back on the table.
    if prelude_loaded {
        assert_eq!(
            third_tail, 99,
            "the 24-byte objects at (1,2) whose tail is neither a cell nor nil, \
             measured at w115 over {population} objects. This is the remainder \
             that BLOCKS a `list_ptrs` size rule: 24 does not identify a cons \
             cell. Tail kinds: {tail_kinds:?}. First: {first_third:?}"
        );
        assert_eq!(
            name_misfits, 0,
            "no 32-byte (1,2) object should fail to be a name link; that \
             direction was clean at w115"
        );
    }
}

/// The bound population covers more than ONE of `list_ptrs`'s callers.
///
/// `the_measured_cons_cells_are_the_ones_the_decoder_walked` binds the cells to
/// the decoder's traversal, and it is green - but it walks `levelParams` and
/// nothing else. `decode_name_list` has seven call sites: `levelParams`, `all`
/// on five different payloads, and `ctors`. So "the cells `list_ptrs` walks"
/// has meant "the cells ONE of its seven callers walks", and the size rule the
/// repair adds would apply to all of them. That is the denominator question one
/// level up: not which objects were measured, but which CALLERS produced the
/// objects that were measured.
///
/// MATCHED BY CONTENT, NOT BY SLOT INDEX, and that is forced rather than
/// stylistic. `all` lives at payload slot 3 for a definition, 2 for a theorem
/// and an opaque, 3 for an inductive, 1 for a recursor, and `ctors` at 4 - so a
/// cell keyed on slot numbers would encode six layout constants and mean
/// nothing when one moved. Instead this scans every pointer slot of the
/// payload, tries to read a cons chain of names from each, and accepts the slot
/// whose decoded members EQUAL the list the decoder returned. A layout change
/// moves which slot matches; it cannot make a wrong slot match.
///
/// IDENTIFIED BY REFERENCE, NOT BY HEADER, which is the w113 lesson applied
/// rather than restated. A `ConstantVal` is trusted only when its slot-0 name
/// is one the module declares; the payload is then whatever object POINTS AT
/// that `ConstantVal` in its own slot 0 - `base` is slot 0 in all eight
/// variants. No `(tag, other, cs_sz)` triple is treated as an identity
/// anywhere in this cell, because `(0, 3, 32)` already proved they are not.
///
/// A candidate slot that is not a cons chain is skipped, not asserted against.
/// The claim is carried by REQUIRING a matching chain to exist, not by
/// rejecting the ones that do not match.
#[test]
fn the_all_and_ctors_chains_are_bound_to_the_decoder_too() {
    fn shown(names: &[fln_core::name::Name]) -> Vec<String> {
        names.iter().map(|n| n.to_display_string()).collect()
    }
    fn name_lists(info: &ConstantInfo) -> Vec<(&'static str, Vec<String>)> {
        match info {
            ConstantInfo::Defn(v) => vec![("all", shown(&v.all))],
            ConstantInfo::Thm(v) => vec![("all", shown(&v.all))],
            ConstantInfo::Opaque(v) => vec![("all", shown(&v.all))],
            ConstantInfo::Rec(v) => vec![("all", shown(&v.all))],
            ConstantInfo::Induct(v) => vec![("all", shown(&v.all)), ("ctors", shown(&v.ctors))],
            ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) | ConstantInfo::Ctor(_) => Vec::new(),
        }
    }

    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
        }
    }

    let mut lists_bound = 0usize;
    let mut members_bound = 0usize;
    let mut fields_seen: BTreeSet<&'static str> = BTreeSet::new();
    let mut widths: BTreeSet<i64> = BTreeSet::new();
    let mut sizes: BTreeSet<u16> = BTreeSet::new();

    for (module, bytes) in &modules {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let infos = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .unwrap_or_else(|e| panic!("{module}: decode: {e}"));
        let census: BTreeSet<String> = infos.iter().map(|i| i.name().to_display_string()).collect();

        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let deref = |ptr: u64| -> Option<usize> {
            (ptr & 1 == 0)
                .then(|| usize::try_from(ptr.checked_sub(base)?).ok())
                .flatten()
        };

        // Trusted `ConstantVal`s: the header shape is a filter, the NAME is the
        // evidence.
        let mut trusted: std::collections::BTreeMap<String, Vec<usize>> =
            std::collections::BTreeMap::new();
        for object in &objects {
            if (object.tag, object.other) != (0, 3) {
                continue;
            }
            let Ok(name) = DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(word_at(bytes, object.off + 8))
            else {
                continue;
            };
            let name = name.to_display_string();
            if census.contains(&name) {
                trusted.entry(name).or_default().push(object.off);
            }
        }

        // Payloads, by the `ConstantVal` they carry in their own slot 0.
        let mut payloads: std::collections::BTreeMap<usize, Vec<Obj>> =
            std::collections::BTreeMap::new();
        for object in &objects {
            if object.other == 0 || object.tag > abi::TAG_MAX_CTOR_TAG {
                continue;
            }
            if let Some(off) = deref(word_at(bytes, object.off + 8)) {
                payloads.entry(off).or_default().push(*object);
            }
        }

        // Read a chain of names from one slot, tolerantly: `None` means this
        // slot is not a name list, which is the common case and not a fault.
        let chain_at = |slot_word: u64| -> Option<(Vec<String>, Vec<Obj>)> {
            let mut cursor = slot_word;
            let mut cells: Vec<Obj> = Vec::new();
            let mut names: Vec<String> = Vec::new();
            loop {
                if cursor & 1 == 1 {
                    return (cursor >> 1 == 0).then_some((names, cells));
                }
                let cell = *at.get(&deref(cursor)?)?;
                if (cell.tag, cell.other) != (1, 2) || cells.len() == 4096 {
                    return None;
                }
                let head = DeclDecoder::new(&view, WalkBudget::default())
                    .decode_name(word_at(bytes, cell.off + 8))
                    .ok()?;
                names.push(head.to_display_string());
                cells.push(cell);
                cursor = word_at(bytes, cell.off + 16);
            }
        };

        for info in &infos {
            let declaration = info.name().to_display_string();
            for (field, expected) in name_lists(info) {
                if expected.is_empty() {
                    continue; // boxed nil is not a cell; nothing to bind
                }
                let found = trusted
                    .get(&declaration)
                    .map(Vec::as_slice)
                    .unwrap_or(&[])
                    .iter()
                    .flat_map(|cv| payloads.get(cv).map(Vec::as_slice).unwrap_or(&[]))
                    .find_map(|payload| {
                        (0..usize::from(payload.other)).find_map(|slot| {
                            let word = word_at(bytes, payload.off + 8 + 8 * slot);
                            chain_at(word).filter(|(names, _)| *names == expected)
                        })
                    });
                let (_, cells) = found.unwrap_or_else(|| {
                    panic!(
                        "{module}: {declaration}.{field}: the decoder returned \
                         {expected:?}, and no slot of any payload carrying this \
                         declaration's ConstantVal holds a cons chain of those \
                         names. The cells measured elsewhere are then not the \
                         cells this caller of `list_ptrs` walks"
                    )
                });
                for cell in &cells {
                    widths.insert(i64::from(cell.cs_sz) - (8 + 8 * i64::from(cell.other)));
                    sizes.insert(cell.cs_sz);
                }
                members_bound += cells.len();
                lists_bound += 1;
                fields_seen.insert(field);
            }
        }
    }

    // Anti-vacuity: every empty list is skipped, so a corpus of singleton
    // blocks would bind nothing and pass.
    assert!(
        lists_bound > 0 && members_bound > 0,
        "nothing was bound: {lists_bound} lists, {members_bound} members"
    );
    assert!(
        fields_seen.contains("all"),
        "the `all` caller must be exercised, or this cell extends the bound \
         population by nothing: {fields_seen:?}"
    );

    // The same width and size, now on cells reached through callers the green
    // binding cell never touched.
    assert_eq!(
        widths.iter().copied().collect::<Vec<_>>(),
        vec![0_i64],
        "cells reached through {fields_seen:?} store nothing after head and \
         tail ({members_bound} cells over {lists_bound} lists)"
    );
    assert_eq!(
        sizes.iter().copied().collect::<Vec<_>>(),
        vec![24_u16],
        "and carry the size recorded for the `levelParams` cells"
    );
}

/// WHAT the 99 are, by a pinned histogram of what their tails point at.
///
/// `a_third_shape_shares_the_cons_cell_header_and_bounds_the_size_rule` pins
/// the count and deliberately records no hypothesis. It also cannot show its
/// own characterisation on a green run - that only reaches the failure message,
/// which is the channel defect `ac97cb3a` had to fix once already. This cell
/// puts the characterisation in an assertion, where a green run means it still
/// holds and a red one names what changed.
///
/// THE BOXED SCALARS SETTLE IT. A `List` tail is a pointer to another cell or
/// the boxed nil, which is boxed ZERO - there is no other nullary constructor
/// of `List`. Seventeen of the 99 carry a boxed tail of 1 through 6. An object
/// whose second field holds boxed 1..6 belongs to a type with SEVERAL nullary
/// constructors, so it is not a list, and no walk of it as a list can be
/// correct. The remaining 82 point at two-field structures - 71 at `tag 0`, 11
/// at `tag 4` - which is consistent with the same reading and does not on its
/// own establish it.
///
/// So the 99 are constructors of OTHER inductives that coincide with
/// `List.cons` on tag, arity and size. That is why `daaaabe2` blocks the size
/// rule: 24 bytes at `(1, 2)` is a shape several types share, not a signature
/// of `List.cons`, and no refinement of the SIZE can separate them because the
/// size is identical.
///
/// The histogram is measured, not guessed. It was computed over the same four
/// modules by an independent walker before being written here, and that walker
/// reproduced w115's two published numbers exactly - 7,591 objects at `(1, 2)`
/// and 99 third tails, first at `Init/Prelude.olean` `0x32e7d0`. Two
/// implementations agreeing on the population is the reason this pin is a
/// record rather than a hypothesis.
#[test]
fn the_third_shape_tails_are_not_list_tails() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut population = 0usize;
    let mut third_tails = 0usize;
    let mut histogram: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();

        for object in &objects {
            if (object.tag, object.other) != (1, 2) {
                continue;
            }
            population += 1;
            if object.cs_sz != 24 {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            let target = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| at.get(&off));
            let ends_the_list = second & 1 == 1 && second >> 1 == 0;
            if ends_the_list || target.is_some_and(|t| (t.tag, t.other) == (1, 2)) {
                continue; // cons-shaped, and not one of the 99
            }
            third_tails += 1;
            let kind = match target {
                Some(t) => format!("tag {} arity {}", t.tag, t.other),
                None if second & 1 == 1 => format!("boxed scalar {}", second >> 1),
                None => "unresolvable".to_owned(),
            };
            *histogram.entry(kind).or_default() += 1;
        }
    }

    // Kept from the pinned remainder cell, and checked here too so the two
    // cannot drift apart about which population they describe.
    assert!(
        population >= 100,
        "too few (1,2) objects to characterise: {population}"
    );
    assert_eq!(
        histogram.values().sum::<usize>(),
        third_tails,
        "every third tail must land in exactly one bucket"
    );

    if !prelude_loaded {
        // Nothing to pin: the third shape does not occur in the C3 fixtures
        // alone, which is why the count is Prelude-gated in the sibling cell
        // too. The arithmetic above still ran.
        assert_eq!(
            third_tails, 0,
            "the C3 fixtures were not expected to contain the third shape; \
             finding one here is a new fact: {histogram:?}"
        );
        return;
    }

    // The remainder, still pinned two-way.
    assert_eq!(
        third_tails, 99,
        "the same 99 the remainder cell pins: {histogram:?}"
    );

    // The measured histogram. A change either way names what moved.
    let measured: Vec<(String, usize)> = histogram.into_iter().collect();
    assert_eq!(
        measured,
        vec![
            ("boxed scalar 1".to_owned(), 6),
            ("boxed scalar 2".to_owned(), 4),
            ("boxed scalar 3".to_owned(), 2),
            ("boxed scalar 4".to_owned(), 2),
            ("boxed scalar 5".to_owned(), 2),
            ("boxed scalar 6".to_owned(), 1),
            ("tag 0 arity 2".to_owned(), 71),
            ("tag 4 arity 2".to_owned(), 11),
        ],
        "what the 99 third tails point at, measured over the pinned corpus"
    );

    // The load-bearing half, stated as its own assertion so it cannot be lost
    // in a histogram edit: a boxed tail other than nil is proof the object is
    // not a list.
    let not_nil_scalars: usize = measured
        .iter()
        .filter(|(kind, _)| kind.starts_with("boxed scalar "))
        .map(|(_, count)| *count)
        .sum();
    assert_eq!(
        not_nil_scalars, 17,
        "objects whose tail is a boxed value OTHER than nil. `List` has one \
         nullary constructor and it is boxed zero, so these cannot be list \
         cells however they are walked - which is why no size rule can rescue \
         `list_ptrs`"
    );
}

/// Objects reachable from ONE pointer, by the same layout law `objects_of` uses.
///
/// Separate from `objects_of` because the question is not what exists but what
/// a particular root reaches: `ModuleData` has five pointer fields, and the
/// declaration graph hangs off exactly one of them.
fn reachable_from(bytes: &[u8], base: u64, start: u64) -> BTreeSet<usize> {
    const HEADER_SIZE: usize = 88;
    let deref = |ptr: u64| -> Option<usize> {
        if ptr & 1 == 1 || ptr == 0 {
            return None;
        }
        let resolved = usize::try_from(ptr.checked_sub(base)?).ok()?;
        (resolved >= HEADER_SIZE && resolved + 8 <= bytes.len() && resolved % 8 == 0)
            .then_some(resolved)
    };
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut stack = vec![start];
    while let Some(ptr) = stack.pop() {
        let Some(off) = deref(ptr) else { continue };
        if !seen.insert(off) {
            continue;
        }
        let word = word_at(bytes, off);
        let tag = ((word >> 56) & 0xff) as u8;
        let other = ((word >> 48) & 0xff) as u8;
        if tag <= abi::TAG_MAX_CTOR_TAG {
            for i in 0..other as usize {
                let field = off + 8 + 8 * i;
                if field + 8 <= bytes.len() {
                    stack.push(word_at(bytes, field));
                }
            }
        } else if tag == abi::TAG_ARRAY {
            let size = word_at(bytes, off + 8);
            for i in 0..size.min(1 << 16) {
                let field = off + 24 + 8 * i as usize;
                if field + 8 <= bytes.len() {
                    stack.push(word_at(bytes, field));
                }
            }
        }
    }
    seen
}

/// WHICH root reaches the 99: none of them is in the declaration graph.
///
/// `2ea2447b` established what they are - constructors of other inductives
/// sharing `List.cons`'s tag, arity and size, seventeen of them provably not
/// lists because their tail is a boxed value other than nil. That says the size
/// can never identify a cons cell. It does not say whether `list_ptrs` can ever
/// be HANDED one, which is a different question and the one that decides how
/// much of the blocker is real.
///
/// `ModuleData` carries five pointers. `constants` at slot 2 is the declaration
/// graph `decode_module_constants` walks; `entries` at slot 4 is
/// `Array (Name x Array EnvExtensionEntry)`, arbitrary serialised payloads from
/// environment extensions, which the declaration decoder never enters. Measured
/// over the pinned corpus: all 99 are reachable from `entries` and NONE from
/// `constants`.
///
/// THE ANTI-VACUITY GUARD IS THE WHOLE CELL. A `constants` walk that reached
/// nothing - a wrong slot, a broken deref - would report zero third-shape
/// objects in the declaration graph and look like this same result. So the cell
/// pins how many CONS-SHAPED cells that walk reaches: 2,259 of the 2,465 in the
/// corpus, against 206 reachable only from `entries`. A walk that finds
/// thousands of cons cells and none of the third shape has excluded something;
/// a walk that finds nothing has merely failed.
///
/// WHAT THIS DOES NOT ESTABLISH, because the distinction is the point. It is
/// one corpus at one pin. "Not reachable here" is not "cannot be reached", and
/// `entries` decoding is itself open work under `franken_lean-0nz` - the moment
/// those payloads are walked, these objects are in scope for whatever walks
/// them. This narrows the blocker to a population the declaration decoder does
/// not currently touch; it does not retire it, and it does not make the size a
/// discriminator, which `2ea2447b` already settled it is not.
#[test]
fn the_third_shape_is_reached_only_through_module_entries() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut third_tails = 0usize;
    let mut third_in_declarations = 0usize;
    let mut third_in_entries = 0usize;
    let mut third_in_neither = 0usize;
    let mut cons_in_declarations = 0usize;
    let mut cons_in_entries = 0usize;
    let mut examples: Vec<String> = Vec::new();

    for (module, bytes) in &modules {
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();

        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root in range");
        assert_eq!(
            at.get(&root).map(|o| (o.tag, o.other)),
            Some((0, 5)),
            "{module}: ModuleData carries imports, constNames, constants, \
             extraConstNames and entries"
        );
        let declarations = reachable_from(bytes, base, word_at(bytes, root + 24));
        let entries = reachable_from(bytes, base, word_at(bytes, root + 40));

        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            let target = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| at.get(&off));
            let cons_shaped = (second & 1 == 1 && second >> 1 == 0)
                || target.is_some_and(|t| (t.tag, t.other) == (1, 2));

            if cons_shaped {
                if declarations.contains(&object.off) {
                    cons_in_declarations += 1;
                } else if entries.contains(&object.off) {
                    cons_in_entries += 1;
                }
                continue;
            }

            third_tails += 1;
            if declarations.contains(&object.off) {
                third_in_declarations += 1;
                if examples.len() < 5 {
                    examples.push(format!("{module} {:#x}", object.off));
                }
            } else if entries.contains(&object.off) {
                third_in_entries += 1;
            } else {
                third_in_neither += 1;
            }
        }
    }

    assert_eq!(
        third_in_declarations + third_in_entries + third_in_neither,
        third_tails,
        "every third-shape object must land in exactly one bucket"
    );

    if !prelude_loaded {
        assert_eq!(
            third_tails, 0,
            "the third shape was not expected in the C3 fixtures alone"
        );
        return;
    }

    // THE GUARD, asserted before the exclusion it makes meaningful: the
    // declaration walk must demonstrably reach cons cells, or its zero above
    // says nothing.
    assert!(
        cons_in_declarations > 0,
        "the `constants` walk reached no cons cells at all, so it has not \
         excluded anything - it has failed"
    );
    assert_eq!(
        (cons_in_declarations, cons_in_entries),
        (2259, 206),
        "cons-shaped (1,2,24) cells by root, measured over the pinned corpus"
    );

    // The remainder, still pinned two-way, and its split.
    assert_eq!(third_tails, 99, "the same 99 the remainder cell pins");
    assert_eq!(
        (third_in_declarations, third_in_entries, third_in_neither),
        (0, 99, 0),
        "all of the third shape is reached through `entries` and none through \
         `constants`. A non-zero first element means `list_ptrs` CAN be handed \
         one from the declaration graph: {examples:?}"
    );
}

/// A LOCATABLE witness per module, so the finding can be opened rather than
/// only counted.
///
/// `1dd7c288` pins the aggregate: 99 third-shape objects, all reached through
/// `entries`, none through `constants`. Aggregates are checkable and not
/// openable - nothing in the file tells a reader where to put a debugger. This
/// pins the per-module table and, for each module that has one, the address of
/// a real instance.
///
/// THE ADDRESS IS THE LOWEST, NOT THE FIRST, and the distinction is a
/// correction. w115 reported "first at `Init/Prelude.olean` `0x32e7d0`", and
/// two of my commits repeated it. That is the first object in TRAVERSAL order -
/// the order a stack-based walk happens to pop - which is reproducible only for
/// a walker that pushes exactly as this one does. Change the traversal to a
/// queue and the same corpus reports a different "first". The lowest address is
/// a property of the data, so that is what this pins: `0x25ba60`. `0x32e7d0` is
/// not wrong, it is just not an identifier.
///
/// THE GUARD IS AT THE PINNED ADDRESS. A pinned constant that nothing
/// re-derives is a number that rots quietly; a stale offset would still be a
/// valid `usize` and the test would still pass if all it did was compare
/// counts. So the cell goes TO the address it pins and re-establishes, from the
/// bytes, that the object there is `(1, 2)` at 24 bytes, that its tail is
/// neither a cell nor nil, and that it is reachable from `entries` and not from
/// `constants`. The pin and its meaning move together or the cell fails.
///
/// The three C3 modules are pinned at zero. That is not padding: it is what
/// makes the Prelude row a contrast rather than the only observation, and it is
/// why the sibling cells gate on the pin at all.
#[test]
fn the_third_shape_has_a_locatable_witness_per_module() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    // Per module: third-shape count, how many of those `entries` reaches, and
    // the LOWEST address among them.
    let mut table: Vec<(String, usize, usize, Option<usize>)> = Vec::new();
    let mut total_third = 0usize;
    let mut cons_reached_by_declarations = 0usize;

    for (module, bytes) in &modules {
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root in range");
        let declarations = reachable_from(bytes, base, word_at(bytes, root + 24));
        let entries = reachable_from(bytes, base, word_at(bytes, root + 40));

        let mut third: Vec<usize> = Vec::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            let target = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| at.get(&off));
            if (second & 1 == 1 && second >> 1 == 0)
                || target.is_some_and(|t| (t.tag, t.other) == (1, 2))
            {
                if declarations.contains(&object.off) {
                    cons_reached_by_declarations += 1;
                }
                continue;
            }
            third.push(object.off);
        }

        let via_entries: Vec<usize> = third
            .iter()
            .copied()
            .filter(|off| entries.contains(off))
            .collect();
        total_third += third.len();
        table.push((
            module.clone(),
            third.len(),
            via_entries.len(),
            via_entries.iter().copied().min(),
        ));

        // The guard, at the address this module contributes to the pin.
        if let Some(witness) = via_entries.iter().copied().min() {
            let object = at.get(&witness).expect("the witness is a walked object");
            assert_eq!(
                (object.tag, object.other, object.cs_sz),
                (1, 2, 24),
                "{module}: the pinned witness must still be a cons-cell-shaped \
                 object"
            );
            let second = word_at(bytes, witness + 16);
            let target = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| at.get(&off));
            assert!(
                !((second & 1 == 1 && second >> 1 == 0)
                    || target.is_some_and(|t| (t.tag, t.other) == (1, 2))),
                "{module}: the pinned witness must still have a tail that is \
                 neither a cell nor nil, or the address has drifted onto an \
                 ordinary cons cell"
            );
            assert!(
                entries.contains(&witness) && !declarations.contains(&witness),
                "{module}: the pinned witness must still be reachable from \
                 `entries` and not from `constants`"
            );
        }
    }

    // Anti-vacuity for every "not in constants" above: the declaration walk has
    // to reach cons cells, or its silence is failure rather than exclusion.
    assert!(
        cons_reached_by_declarations > 0,
        "the `constants` walk reached no cons cells, so it has excluded nothing"
    );

    // The remainder, pinned two-way here as well.
    let expected_total = if prelude_loaded { 99 } else { 0 };
    assert_eq!(
        total_third, expected_total,
        "the same third-shape population the remainder cell pins"
    );

    let mut expected: Vec<(String, usize, usize, Option<usize>)> = vec![
        ("Init.olean".to_owned(), 0, 0, None),
        ("Init.BinderNameHint.olean".to_owned(), 0, 0, None),
        ("Init.SizeOfLemmas.olean".to_owned(), 0, 0, None),
    ];
    if prelude_loaded {
        expected.push(("Init/Prelude.olean".to_owned(), 99, 99, Some(0x25ba60)));
    }
    assert_eq!(
        table, expected,
        "per-module third-shape count, how many `entries` reaches, and the \
         LOWEST such address - a witness a reader can open"
    );
}

/// The 71 `tag 0 arity 2` tails are WELL-FORMED CONSTRUCTOR OBJECTS.
///
/// SAY WHAT THIS DOES AND DOES NOT ADD, because the obvious reading is a
/// tautology. That these tails are "not cons" follows from the selection
/// itself: the third shape is defined as a `(1, 2, 24)` object whose tail is
/// neither boxed nil nor a `(1, 2)` object, so a `tag 0` tail is excluded from
/// being `List.cons` by the filter that found it, not by anything measured
/// here. Asserting the tag inequality proves nothing that selecting on it did
/// not already assume.
///
/// What is NOT given by the selection is that these tails are real objects at
/// all. The competing explanation for the whole third shape has always been
/// that the walker is wrong - landing mid-object, resolving a pointer into the
/// middle of a payload, or reading a field that is not a pointer. Under that
/// explanation the "tails" would be arbitrary words, and their headers would
/// look arbitrary: mixed sizes, tags outside the constructor range, fields that
/// do not resolve. This cell measures exactly those things.
///
/// All 71 carry tag 0 with two pointer fields and a stored size of 24 - which
/// is `8 + 8 * 2` with NO scalar area, derived here from the object's own arity
/// before the literal is written, the ordering `ac97cb3a` settled. All 71 are
/// reachable from `entries`. And all 142 of their fields resolve to objects
/// that the walk actually visited: not one is a boxed scalar, not one is
/// unresolvable. A misread would not produce 142 valid pointers.
///
/// The grandchild histogram is pinned for the same reason the tail histogram
/// was: it is the characterisation, and a green run must carry it somewhere a
/// reader can see. Seventy-one of the 142 point at a single `tag 0 arity 4`
/// shape - one per tail - which says these are records of a regular type rather
/// than debris, without naming the type. Naming it needs the extension's own
/// schema and is not guessed here.
#[test]
fn the_tag_zero_third_shape_tails_are_well_formed_constructors() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut third_tails = 0usize;
    let mut tail_shapes: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut tag_zero = 0usize;
    let mut tag_zero_in_entries = 0usize;
    let mut tag_zero_sizes: BTreeSet<u16> = BTreeSet::new();
    let mut tag_zero_widths: BTreeSet<i64> = BTreeSet::new();
    let mut fields = 0usize;
    let mut unresolved_fields = 0usize;
    let mut grandchildren: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root in range");
        let entries = reachable_from(bytes, base, word_at(bytes, root + 40));

        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            let target = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| {
                    at.get(&off)
                        .map(|o| (*o, second.wrapping_sub(base) as usize))
                });
            if (second & 1 == 1 && second >> 1 == 0)
                || target.is_some_and(|(t, _)| (t.tag, t.other) == (1, 2))
            {
                continue;
            }
            third_tails += 1;
            let Some((tail, tail_off)) = target else {
                tail_shapes
                    .entry("boxed or unresolvable".to_owned())
                    .and_modify(|c| *c += 1)
                    .or_insert(1);
                continue;
            };
            *tail_shapes
                .entry(format!("tag {} arity {}", tail.tag, tail.other))
                .or_default() += 1;
            if (tail.tag, tail.other) != (0, 2) {
                continue;
            }

            tag_zero += 1;
            if entries.contains(&tail_off) {
                tag_zero_in_entries += 1;
            }
            // A constructor object, not an array, string, thunk or reference.
            assert!(
                tail.tag <= abi::TAG_MAX_CTOR_TAG,
                "a tail outside the constructor tag range is not a constructor \
                 object at all: tag {}",
                tail.tag
            );
            tag_zero_sizes.insert(tail.cs_sz);
            tag_zero_widths.insert(i64::from(tail.cs_sz) - (8 + 8 * i64::from(tail.other)));

            for slot in 0..usize::from(tail.other) {
                fields += 1;
                let word = word_at(bytes, tail_off + 8 + 8 * slot);
                match (word & 1 == 0)
                    .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                    .flatten()
                    .and_then(|off| at.get(&off))
                {
                    Some(child) => {
                        *grandchildren
                            .entry(format!("tag {} arity {}", child.tag, child.other))
                            .or_default() += 1;
                    }
                    None => unresolved_fields += 1,
                }
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(third_tails, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    // Kept: the remainder, two-way, and the tail histogram this refines.
    assert_eq!(third_tails, 99, "the same 99 the remainder cell pins");
    assert_eq!(
        tail_shapes.into_iter().collect::<Vec<_>>(),
        vec![
            ("boxed or unresolvable".to_owned(), 17),
            ("tag 0 arity 2".to_owned(), 71),
            ("tag 4 arity 2".to_owned(), 11),
        ],
        "the tail histogram `2ea2447b` pins, grouped by shape"
    );
    assert_eq!(tag_zero, 71, "the population this cell characterises");

    // Well-formedness: the derivation before the literal.
    assert_eq!(
        tag_zero_widths.iter().copied().collect::<Vec<_>>(),
        vec![0_i64],
        "every one stores two pointers and NOTHING after them"
    );
    assert_eq!(
        tag_zero_sizes.iter().copied().collect::<Vec<_>>(),
        vec![24_u16],
        "which is the size that follows: 8 + 8 * 2"
    );
    assert_eq!(
        tag_zero_in_entries, 71,
        "all of them reached through `entries`, like their parents"
    );

    // The claim that actually rules out a misread.
    assert_eq!(
        (fields, unresolved_fields),
        (142, 0),
        "every field of every one resolves to an object the walk visited. A \
         walker landing mid-object would not produce 142 valid pointers"
    );
    assert_eq!(
        grandchildren.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 0 arity 2".to_owned(), 24),
            ("tag 0 arity 4".to_owned(), 71),
            ("tag 1 arity 2".to_owned(), 2),
            ("tag 5 arity 1".to_owned(), 45),
        ],
        "what those fields point at; the 71 at a single `tag 0 arity 4` shape - \
         one per tail - are records of a regular type, not debris"
    );
}

/// The 11 `tag 4 arity 2` tails are `Expr.const` nodes with EMPTY level lists.
///
/// This is the last third of `2ea2447b`'s histogram. The other two were settled
/// differently: the 17 boxed tails by an argument (`List` has one nullary
/// constructor and it is boxed zero, so a boxed 1..6 cannot be a list), the 71
/// `tag 0` tails by well-formedness (142 fields, none unresolvable, which is
/// not what a misreading walker produces). These 11 are settled by SHAPE, and
/// the shape is specific enough to name.
///
/// Thirty-two bytes at arity 2 is `8 + 8 * 2` plus an eight-byte scalar area -
/// one trailing word. That is an `Expr` node's `Data` field, and tag 4 with two
/// pointers and a `Data` word is `Expr.const declName us`. The cell does not
/// stop at the arithmetic: it checks the two fields are what that constructor
/// declares. Slot 0 is a `Name` link in all 11 and `decode_name` accepts it -
/// the production decoder, not a shape guess. Slot 1 is boxed nil in all 11.
///
/// SLOT 1 IS THE POINT, and it is a small irony worth stating. `Expr.const`'s
/// second field is `List Level` - these objects DO carry a list, walked by the
/// same `list_ptrs`. Every one of the 11 carries the EMPTY list, so they
/// contribute no cons cells at all, which is why they turn up as tails and
/// never as cells.
///
/// The names are `obj` (5) and `tobj` (6), all single-component. That the
/// prefix is the anonymous name is structural - a boxed zero in the link's
/// first slot - and is measured independently of any string decoding. The
/// spellings themselves come from reading the string payload, which is the
/// least robust thing in this cell; a red there names what they really are and
/// is a finding rather than a fault. `obj` and `tobj` are how Lean's compiler
/// IR spells its object types, which is consistent with these living in an
/// extension payload, but this cell does not establish which extension and
/// does not claim to.
#[test]
fn the_tag_four_third_shape_tails_are_expr_const_nodes() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut third_tails = 0usize;
    let mut tail_shapes: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut tag_four = 0usize;
    let mut in_entries = 0usize;
    let mut widths: BTreeSet<i64> = BTreeSet::new();
    let mut sizes: BTreeSet<u16> = BTreeSet::new();
    let mut single_component = 0usize;
    let mut empty_level_lists = 0usize;
    let mut names: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root in range");
        let entries = reachable_from(bytes, base, word_at(bytes, root + 40));

        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            let tail_off = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten();
            let tail = tail_off.and_then(|off| at.get(&off).map(|o| (*o, off)));
            if (second & 1 == 1 && second >> 1 == 0)
                || tail.is_some_and(|(t, _)| (t.tag, t.other) == (1, 2))
            {
                continue;
            }
            third_tails += 1;
            let Some((tail, tail_off)) = tail else {
                *tail_shapes
                    .entry("boxed or unresolvable".to_owned())
                    .or_default() += 1;
                continue;
            };
            *tail_shapes
                .entry(format!("tag {} arity {}", tail.tag, tail.other))
                .or_default() += 1;
            if (tail.tag, tail.other) != (4, 2) {
                continue;
            }

            tag_four += 1;
            if entries.contains(&tail_off) {
                in_entries += 1;
            }
            widths.insert(i64::from(tail.cs_sz) - (8 + 8 * i64::from(tail.other)));
            sizes.insert(tail.cs_sz);

            // Slot 0: `declName`. Decoded by the production decoder.
            let name_word = word_at(bytes, tail_off + 8);
            let decoded = DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(name_word)
                .unwrap_or_else(|e| panic!("{module}: an Expr.const declName must decode: {e}"));
            *names.entry(decoded.to_display_string()).or_default() += 1;
            // Single-component: the link's own prefix slot is the anonymous
            // name, which is a boxed zero. Structural, not string-derived.
            if let Some(link) = usize::try_from(name_word.wrapping_sub(base))
                .ok()
                .filter(|off| at.contains_key(off))
            {
                let prefix = word_at(bytes, link + 8);
                if prefix & 1 == 1 && prefix >> 1 == 0 {
                    single_component += 1;
                }
            }

            // Slot 1: `us : List Level`.
            let levels = word_at(bytes, tail_off + 16);
            if levels & 1 == 1 && levels >> 1 == 0 {
                empty_level_lists += 1;
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(third_tails, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    // Kept: the remainder two-way, and the histogram this refines.
    assert_eq!(third_tails, 99, "the same 99 the remainder cell pins");
    assert_eq!(
        tail_shapes.into_iter().collect::<Vec<_>>(),
        vec![
            ("boxed or unresolvable".to_owned(), 17),
            ("tag 0 arity 2".to_owned(), 71),
            ("tag 4 arity 2".to_owned(), 11),
        ],
        "the tail histogram `2ea2447b` pins, grouped by shape"
    );
    assert_eq!(tag_four, 11, "the population this cell characterises");

    // The shape, derivation before literal.
    assert_eq!(
        widths.iter().copied().collect::<Vec<_>>(),
        vec![8_i64],
        "two pointer fields and ONE trailing word - an `Expr` node's `Data`"
    );
    assert_eq!(
        sizes.iter().copied().collect::<Vec<_>>(),
        vec![32_u16],
        "which is the size that follows: 8 + 8 * 2 + 8"
    );
    assert_eq!(in_entries, 11, "all reached through `entries`");

    // The two fields `Expr.const` declares.
    assert_eq!(
        single_component, 11,
        "every `declName` is a single component: its link's prefix slot is the \
         boxed anonymous name"
    );
    assert_eq!(
        empty_level_lists, 11,
        "every `us` is the EMPTY level list. `Expr.const`'s second field is a \
         `List Level` walked by this same `list_ptrs`, and all 11 carry boxed \
         nil - which is why these appear as tails and never as cells"
    );
    assert_eq!(
        names.into_iter().collect::<Vec<_>>(),
        vec![("obj".to_owned(), 5), ("tobj".to_owned(), 6)],
        "the declNames, decoded by the production decoder"
    );
}

/// The remaining 17 hold NO POINTERS AT ALL - both fields are boxed scalars.
///
/// `2ea2447b` pins that 17 of the 99 have a boxed tail other than nil, and
/// argues from that alone that they cannot be list cells. `aec3efd1` and
/// `84951450` characterised the other 82 by their tails. Every cell in this
/// file has read a third-shape object's TAIL; not one has read its HEAD. So the
/// 99 have been described entirely through one of their two fields, and the
/// other has never been looked at.
///
/// It is not empty. All 17 carry a boxed HEAD as well - values 4 through 14 -
/// so between them the 17 objects contain thirty-four fields and not one
/// pointer.
///
/// THAT IS THE MIRROR OF THE 71, and the pair is the argument. There, 142
/// fields were ALL pointers into objects the walk had independently visited,
/// which is not what a misreading walker produces. Here, 34 fields are ALL
/// scalars, which is also not what a misreading walker produces - a walk that
/// had drifted off a real object boundary would find a mixture, because
/// arbitrary words are pointer-shaped about as often as they are not. Two
/// populations, each internally uniform in opposite ways, is a much harder
/// thing to fake than either alone.
///
/// A boxed head is legal for a real `List.cons` - `List Nat` stores small
/// naturals unboxed in the head slot - so the head says nothing on its own
/// about whether these are lists. The tail already settled that. What the head
/// adds is that these objects are LEAF constructors: they reference nothing, so
/// no walk of them can reach anything, and the question of what they contain is
/// answered completely by the two scalars pinned below.
#[test]
fn the_boxed_tail_third_shape_objects_hold_no_pointers() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut third_tails = 0usize;
    let mut remainder = 0usize;
    let mut in_entries = 0usize;
    let mut in_declarations = 0usize;
    let mut fields = 0usize;
    let mut pointer_fields = 0usize;
    let mut tails: std::collections::BTreeMap<u64, usize> = std::collections::BTreeMap::new();
    let mut heads: std::collections::BTreeMap<u64, usize> = std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root in range");
        let entries = reachable_from(bytes, base, word_at(bytes, root + 40));
        let declarations = reachable_from(bytes, base, word_at(bytes, root + 24));

        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            let tail = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| at.get(&off));
            if (second & 1 == 1 && second >> 1 == 0)
                || tail.is_some_and(|t| (t.tag, t.other) == (1, 2))
            {
                continue;
            }
            third_tails += 1;

            // The remainder: a BOXED tail that is not nil. The other 82 have
            // pointer tails and are characterised elsewhere.
            if second & 1 == 0 {
                continue;
            }
            remainder += 1;
            *tails.entry(second >> 1).or_default() += 1;
            if entries.contains(&object.off) {
                in_entries += 1;
            }
            if declarations.contains(&object.off) {
                in_declarations += 1;
            }

            // Both fields, which is what has never been read.
            for slot in 0..usize::from(object.other) {
                fields += 1;
                let word = word_at(bytes, object.off + 8 + 8 * slot);
                if word & 1 == 0 {
                    pointer_fields += 1;
                } else if slot == 0 {
                    *heads.entry(word >> 1).or_default() += 1;
                }
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(third_tails, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    // Kept two-way: the whole population, and this leftover of it.
    assert_eq!(third_tails, 99, "the same 99 the remainder cell pins");
    assert_eq!(
        remainder, 17,
        "99 less the 71 `tag 0` tails and the 11 `tag 4` tails"
    );
    assert_eq!(
        (in_entries, in_declarations),
        (17, 0),
        "reached through `entries`, never through `constants`"
    );

    // The claim: no pointers anywhere in them.
    assert_eq!(
        (fields, pointer_fields),
        (34, 0),
        "seventeen objects, two fields each, and not one pointer. A walk that \
         had drifted off a real object boundary would find a MIXTURE - \
         arbitrary words are pointer-shaped about as often as not - so uniform \
         scalars are evidence these are real objects, exactly as the 71's \
         uniform pointers were"
    );

    assert_eq!(
        tails.into_iter().collect::<Vec<_>>(),
        vec![(1, 6), (2, 4), (3, 2), (4, 2), (5, 2), (6, 1)],
        "the boxed tail values `2ea2447b` pins, here as numbers rather than \
         formatted strings"
    );
    assert_eq!(
        heads.into_iter().collect::<Vec<_>>(),
        vec![
            (4, 1),
            (5, 1),
            (6, 2),
            (7, 2),
            (8, 3),
            (9, 1),
            (10, 3),
            (11, 1),
            (12, 1),
            (13, 1),
            (14, 1),
        ],
        "the boxed HEAD values, which nothing had read before"
    );
}

/// The heads of the other 82, closing the gap `a7a7a9e0` named.
///
/// That cell found that six waves had described the 99 entirely through their
/// TAILS and had never read a HEAD, and it read the heads of the 17. This reads
/// the heads of the remaining 82 - the 71 whose tail is a `tag 0` constructor
/// and the 11 that are `Expr.const` - and the answer is a clean split:
///
///   the 71   every head a POINTER, all at one shape: `tag 0` arity 5
///   the 11   every head BOXED, values 0 through 5
///   the 17   every head BOXED, values 4 through 14   (`a7a7a9e0`)
///
/// EACH GROUP IS INTERNALLY UNIFORM AND NO GROUP IS MIXED, and that is the
/// third independent measurement against the misread hypothesis. The 71 gave
/// 142 tail-side fields, all pointers. The 17 gave 34 fields, all scalars. Now
/// the head side splits the same way and along the same group boundaries: 71
/// pointers with not one scalar among them, 11 scalars with not one pointer.
/// A walker drifting off real object boundaries produces mixtures, and it
/// certainly does not produce mixtures that align with a partition derived from
/// a different field.
///
/// The 71 heads all point at a SINGLE shape, one per parent. Combined with
/// `84951450` - where 71 of the tails' 142 fields pointed at one `tag 0` arity
/// 4 shape, again one per tail - this is a regular record laid out the same way
/// 71 times. That is a data structure, not debris.
///
/// Classified by CONSTRUCTOR TAG AND ARITY ONLY. No size is asserted anywhere
/// in this cell: sizes appear in the file already where they were the thing
/// being measured, and reaching for one here would be reintroducing the
/// discriminator `daaaabe2` disproved through the back door.
#[test]
fn the_pointer_tailed_third_shape_heads_are_uniform_within_each_group() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut third_tails = 0usize;
    let mut tag_zero = (0usize, 0usize); // (population, pointer heads)
    let mut tag_four = (0usize, 0usize);
    let mut tag_zero_heads: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut tag_four_heads: std::collections::BTreeMap<u64, usize> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();

        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            let tail = (second & 1 == 0)
                .then(|| usize::try_from(second.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| at.get(&off));
            if (second & 1 == 1 && second >> 1 == 0)
                || tail.is_some_and(|t| (t.tag, t.other) == (1, 2))
            {
                continue;
            }
            third_tails += 1;
            let Some(tail) = tail else { continue }; // the 17, done at a7a7a9e0

            let head = word_at(bytes, object.off + 8);
            let head_object = (head & 1 == 0)
                .then(|| usize::try_from(head.wrapping_sub(base)).ok())
                .flatten()
                .and_then(|off| at.get(&off));

            match (tail.tag, tail.other) {
                (0, 2) => {
                    tag_zero.0 += 1;
                    if head & 1 == 0 {
                        tag_zero.1 += 1;
                        *tag_zero_heads
                            .entry(match head_object {
                                Some(h) => format!("tag {} arity {}", h.tag, h.other),
                                None => "unresolvable".to_owned(),
                            })
                            .or_default() += 1;
                    }
                }
                (4, 2) => {
                    tag_four.0 += 1;
                    if head & 1 == 0 {
                        tag_four.1 += 1;
                    } else {
                        *tag_four_heads.entry(head >> 1).or_default() += 1;
                    }
                }
                _ => {}
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(third_tails, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    // Kept two-way, and the arithmetic that ties the three groups together.
    assert_eq!(third_tails, 99, "the same 99 the remainder cell pins");
    assert_eq!(
        (tag_zero.0, tag_four.0),
        (71, 11),
        "the two pointer-tailed groups; the remaining 17 are `a7a7a9e0`'s"
    );
    assert_eq!(
        tag_zero.0 + tag_four.0 + 17,
        third_tails,
        "the three groups must account for the whole population"
    );

    // The 71: every head a pointer, all at one constructor shape.
    assert_eq!(
        tag_zero.1, 71,
        "every one of the 71 has a POINTER head - not one scalar among them"
    );
    assert_eq!(
        tag_zero_heads.into_iter().collect::<Vec<_>>(),
        vec![("tag 0 arity 5".to_owned(), 71)],
        "and they all point at a single constructor shape, one per parent - a \
         regular record laid out the same way 71 times, not debris"
    );

    // The 11: every head boxed.
    assert_eq!(
        tag_four.1, 0,
        "not one of the 11 has a pointer head; `Expr.const`'s parents carry \
         scalars here"
    );
    assert_eq!(
        tag_four_heads.into_iter().collect::<Vec<_>>(),
        vec![(0, 2), (1, 2), (2, 2), (3, 2), (4, 2), (5, 1)],
        "the boxed head values. A boxed ZERO is unremarkable in a head - it is \
         only in a TAIL that it would mean `List.nil`"
    );
}

/// The records the 71 heads point at - and there are 69 of them, not 71.
///
/// BOTH THINGS THIS WAVE OFFERED ARE ALREADY HARD ASSERTIONS, which is why this
/// cell is about neither. The constructor-tag count map for the 71 heads is
/// pinned by `9d365d6a` as `[("tag 0 arity 5", 71)]`, and that `constants`
/// reaches none of the 99 is pinned by `1dd7c288` as `(0, 99, 0)` and again for
/// the 17 by `a7a7a9e0`. Re-pinning either would add a green and no fact. What
/// nothing has read is the records those heads point AT.
///
/// A CORRECTION FIRST. `9d365d6a` described them as "a regular record laid out
/// the same way 71 times". Seventy-one is the number of REFERENCES. The number
/// of distinct objects is 69: two records are each pointed at twice. Nothing in
/// that cell was wrong - it counted heads, and there are 71 heads - but the
/// sentence invited the reading that there are 71 records, and there are not.
/// Compaction shares structurally identical subterms, so counting references as
/// objects is a mistake this format makes easy and this file has now made once.
///
/// Over the 69 distinct records: 345 fields, every one a pointer, not a single
/// scalar. That is the fourth population in this investigation to come out
/// uniform in pointer-ness - the 71's tails all pointers, the 17's fields all
/// scalars, the 82's heads split cleanly by group, and now these. Four
/// independent uniformities is not what a walker reading misaligned words
/// produces.
///
/// Four of the five slots hold a single shape apiece across all 69. The fifth
/// holds three shapes. A slot that varies where its neighbours do not is the
/// signature of a field whose type has several constructors, and that is as far
/// as this cell goes: it pins the tags and arities and names no type, no
/// extension and no schema.
#[test]
fn the_head_records_are_shared_and_uniformly_shaped() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut references = 0usize;
    let mut distinct: BTreeSet<(usize, usize)> = BTreeSet::new(); // (module index, offset)
    let mut fields = 0usize;
    let mut pointer_fields = 0usize;
    let mut per_slot: Vec<std::collections::BTreeMap<String, usize>> =
        vec![std::collections::BTreeMap::new(); 5];

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        let mut here: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            // The 71: a third-shape object whose tail is a `tag 0` arity-2
            // constructor. Its head is the record this cell reads.
            let Some(tail) = resolve(word_at(bytes, object.off + 16)) else {
                continue;
            };
            if at.get(&tail).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(head) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&head).map(|h| (h.tag, h.other)) != Some((0, 5)) {
                continue;
            }
            references += 1;
            here.insert(head);
        }

        for head in here {
            distinct.insert((index, head));
            for slot in 0..5usize {
                fields += 1;
                let word = word_at(bytes, head + 8 + 8 * slot);
                match resolve(word) {
                    Some(off) => {
                        pointer_fields += 1;
                        let child = at.get(&off).expect("filtered above");
                        *per_slot[slot]
                            .entry(format!("tag {} arity {}", child.tag, child.other))
                            .or_default() += 1;
                    }
                    None => {
                        *per_slot[slot]
                            .entry("boxed or unresolvable".to_owned())
                            .or_default() += 1;
                    }
                }
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(references, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    // The sharing, which is the fact `9d365d6a`'s wording obscured.
    assert_eq!(
        (references, distinct.len()),
        (71, 69),
        "seventy-one heads point at sixty-nine distinct records: two are shared. \
         Counting references as objects is the mistake a compacted format makes \
         easy"
    );
    assert_eq!(
        fields,
        distinct.len() * 5,
        "five fields per distinct record, counted once each"
    );
    assert_eq!(
        (fields, pointer_fields),
        (345, 345),
        "every field of every record is a pointer - the fourth population here \
         to come out uniform, and not what a walker reading misaligned words \
         produces"
    );

    // Four slots of one shape each; the fifth varies.
    let shapes: Vec<Vec<(String, usize)>> = per_slot
        .into_iter()
        .map(|slot| slot.into_iter().collect())
        .collect();
    assert_eq!(
        shapes,
        vec![
            vec![("tag 2 arity 2".to_owned(), 69)],
            vec![("tag 2 arity 2".to_owned(), 69)],
            vec![("tag 246 arity 0".to_owned(), 69)],
            vec![("tag 7 arity 3".to_owned(), 69)],
            vec![
                ("tag 0 arity 2".to_owned(), 57),
                ("tag 1 arity 2".to_owned(), 8),
                ("tag 5 arity 1".to_owned(), 4),
            ],
        ],
        "per-slot constructor tags and arities. Slot 2 carries the ARRAY tag; \
         slot 4 is the only one that varies, which is what a field whose type \
         has several constructors looks like. No type is named here"
    );
}

/// The two shared head records - and they are not special.
///
/// The other option this wave offered is EMPTY BY AN ALREADY-PINNED FACT, which
/// is worth saying rather than silently not doing. Reading "the tag-4 head
/// records the same way" cannot be done: `9d365d6a` pins that not one of the 11
/// has a pointer head, so there are no tag-4 head records to read. An
/// instruction can be unsatisfiable because an earlier measurement already
/// closed it, and that is not the same as declining it.
///
/// `2475a62f` found 71 references to 69 distinct records. This reads the
/// difference. The refcounts are 67 records referenced once and two referenced
/// twice, and the four referring parents are four distinct objects, so the
/// sharing is at the RECORD level and not an artefact of a parent being counted
/// twice.
///
/// THE RESULT IS NEGATIVE AND THAT IS WHY IT IS WORTH A CELL. The obvious guess
/// is that a record shared by two parents is a distinguished one - a default, a
/// sentinel, an empty case. It is not. Both shared records carry exactly the
/// per-slot shapes `2475a62f` pins for the population: the same single shape in
/// each of slots 0 through 3, and a slot 4 drawn from the same three-element
/// set the other 67 draw from. Nothing about their shape marks them out.
///
/// So the sharing is what compaction does to structurally identical subterms,
/// and not a signal about the data. Recording that stops the next reader
/// spending a wave looking for the distinction, which is the only thing a
/// negative result can buy and the reason to pin it rather than mention it.
///
/// The addresses are pinned with a guard at the address, the pattern
/// `d7518917` established: a constant nothing re-derives rots quietly, so the
/// cell goes to each one and re-establishes that the object there is the
/// five-field shape with exactly two referring parents.
#[test]
fn the_two_shared_head_records_are_not_structurally_special() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut references = 0usize;
    let mut refcounts: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    let mut parents_of: std::collections::BTreeMap<usize, BTreeSet<usize>> =
        std::collections::BTreeMap::new();
    let mut shared: Vec<usize> = Vec::new();
    let mut shared_slots: Vec<Vec<String>> = Vec::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        let mut here: std::collections::BTreeMap<usize, BTreeSet<usize>> =
            std::collections::BTreeMap::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let Some(tail) = resolve(word_at(bytes, object.off + 16)) else {
                continue;
            };
            if at.get(&tail).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(head) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&head).map(|h| (h.tag, h.other)) != Some((0, 5)) {
                continue;
            }
            references += 1;
            here.entry(head).or_default().insert(object.off);
        }

        for (record, parents) in here {
            *refcounts.entry(parents.len()).or_default() += 1;
            if parents.len() > 1 {
                shared.push(record);
                shared_slots.push(
                    (0..5usize)
                        .map(
                            |slot| match resolve(word_at(bytes, record + 8 + 8 * slot)) {
                                Some(off) => {
                                    let child = at.get(&off).expect("filtered above");
                                    format!("tag {} arity {}", child.tag, child.other)
                                }
                                None => "boxed or unresolvable".to_owned(),
                            },
                        )
                        .collect(),
                );
                // The guard, at the address about to be pinned.
                assert_eq!(
                    at.get(&record).map(|r| (r.tag, r.other)),
                    Some((0, 5)),
                    "a pinned shared record must still be the five-field shape"
                );
            }
            parents_of.insert(record, parents);
        }
    }

    if !prelude_loaded {
        assert_eq!(references, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    // The arithmetic `2475a62f` left as a difference.
    assert_eq!(
        refcounts.into_iter().collect::<Vec<_>>(),
        vec![(1, 67), (2, 2)],
        "sixty-seven records referenced once and two referenced twice - which \
         is the 71 references over 69 objects `2475a62f` pins"
    );
    assert_eq!(references, 71, "and the reference count is unchanged");

    let sharing_parents: usize = shared
        .iter()
        .map(|record| parents_of.get(record).map_or(0, BTreeSet::len))
        .sum();
    assert_eq!(
        (shared.len(), sharing_parents),
        (2, 4),
        "two shared records between four DISTINCT parents: the sharing is at \
         the record level, not a parent counted twice"
    );

    shared.sort_unstable();
    assert_eq!(
        shared,
        vec![0x2aa2e0, 0x2b9490],
        "the shared records, locatable rather than only counted"
    );

    // The negative result: nothing about their shape marks them out.
    let single = "tag 2 arity 2".to_owned();
    for slots in &shared_slots {
        assert_eq!(
            &slots[..4],
            &[
                single.clone(),
                single.clone(),
                "tag 246 arity 0".to_owned(),
                "tag 7 arity 3".to_owned(),
            ],
            "a shared record's first four slots carry exactly the shapes \
             `2475a62f` pins for all 69"
        );
        assert!(
            ["tag 0 arity 2", "tag 1 arity 2", "tag 5 arity 1"].contains(&slots[4].as_str()),
            "and its slot 4 is drawn from the same three shapes the other 67 \
             draw from, so sharing is not a structural distinction: {}",
            slots[4]
        );
    }
    assert_eq!(
        shared_slots.len(),
        2,
        "both shared records must have been examined, or the claim that \
         neither is special is made about nothing"
    );
}

/// What the head records actually hold in slots 0, 1 and 2.
///
/// NEITHER THING THIS WAVE OFFERED IS AVAILABLE, and both reasons are worth
/// recording. "Pin that 69 unique targets come from 71 heads" is already a hard
/// assertion - `2475a62f` asserts `(references, distinct) == (71, 69)`. And
/// there is no set of "2 heads the 71 do not share": the refcounts are 67
/// records with one referrer and 2 with two, so the sharing involves FOUR
/// parents across TWO records, and `c726dec5` classified those. Seventy-one
/// minus sixty-nine is a difference of objects, not a subset of heads. Reading
/// it as a subset is the reference-versus-object confusion that produced the
/// original overstatement, arriving one layer along.
///
/// So this reads the slots. `2475a62f` pinned their tags and arities and
/// nothing about their contents.
///
/// Slots 0 and 1 carry `tag 2` with two pointer fields - the shape of a
/// `Name.num` link - in all 69, and the cell settles that by handing each to
/// the PRODUCTION `decode_name` rather than by matching a shape. A hundred and
/// thirty-eight decodes that all succeed is a fact about the decoder agreeing
/// with the bytes, which shape-matching alone never is.
///
/// Slot 2 is the array tag, and an array's length is the first thing a reader
/// wants and the last thing a tag tells you. The lengths run 1 to 5 across the
/// 69 records, 157 elements in total.
///
/// No size is asserted here. Sizes were the measured thing where this file
/// asserts them; reaching for one now would be smuggling back the
/// discriminator `daaaabe2` disproved. No type, extension or schema is named.
#[test]
fn the_head_record_slots_are_names_and_a_short_array() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut records = 0usize;
    let mut names_decoded = 0usize;
    let mut name_shapes: BTreeSet<(u8, u8)> = BTreeSet::new();
    let mut array_lengths: std::collections::BTreeMap<u64, usize> =
        std::collections::BTreeMap::new();
    let mut elements = 0u64;

    for (module, bytes) in &modules {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        let mut here: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let Some(tail) = resolve(word_at(bytes, object.off + 16)) else {
                continue;
            };
            if at.get(&tail).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(head) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&head).map(|h| (h.tag, h.other)) == Some((0, 5)) {
                here.insert(head);
            }
        }

        for record in here {
            records += 1;
            // Slots 0 and 1: handed to the production decoder, not shape-matched.
            for slot in 0..2usize {
                let word = word_at(bytes, record + 8 + 8 * slot);
                let off = resolve(word).expect("slots 0 and 1 are pointers");
                let object = at.get(&off).expect("resolved above");
                name_shapes.insert((object.tag, object.other));
                DeclDecoder::new(&view, WalkBudget::default())
                    .decode_name(word)
                    .unwrap_or_else(|e| {
                        panic!("{module}: head record slot {slot} must decode as a Name: {e}")
                    });
                names_decoded += 1;
            }
            // Slot 2: an array. Its length is what a tag cannot tell you.
            let array = resolve(word_at(bytes, record + 8 + 8 * 2)).expect("slot 2 is a pointer");
            assert_eq!(
                at.get(&array).map(|a| a.tag),
                Some(abi::TAG_ARRAY),
                "{module}: slot 2 carries the array tag"
            );
            let length = word_at(bytes, array + 8);
            *array_lengths.entry(length).or_default() += 1;
            elements += length;
        }
    }

    if !prelude_loaded {
        assert_eq!(records, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(records, 69, "the distinct head records `2475a62f` counts");
    assert_eq!(
        names_decoded, 138,
        "two names per record, every one accepted by the production decoder - \
         which is a fact about the decoder agreeing with the bytes, where \
         matching a shape would only be the bytes agreeing with themselves"
    );
    assert_eq!(
        name_shapes.into_iter().collect::<Vec<_>>(),
        vec![(2, 2)],
        "and all 138 are the same link shape"
    );
    assert_eq!(
        array_lengths.into_iter().collect::<Vec<_>>(),
        vec![(1, 18), (2, 34), (3, 5), (4, 4), (5, 8)],
        "slot 2's array lengths across the 69 records"
    );
    assert_eq!(elements, 157, "and the elements they hold between them");
}

/// Slot 3 of the head records is an EXPRESSION, and a telescope at that.
///
/// The other option is empty again, and for the reason recorded at `c726dec5`:
/// `9d365d6a` pins that not one of the 11 tag-4 objects has a pointer head, so
/// there are no tag-4 head records to classify. Two waves have now offered it.
///
/// Slot 3 has been "tag 7 arity 3" since `2475a62f` and nothing more. That
/// shape is one this project has already measured elsewhere: `49b72dcf` bound
/// `Expr.forallE` to `(7, 3, 48)` over 9,547 objects in this same Prelude,
/// after I had first written the wrong size and had to correct it. So the shape
/// is not a fresh guess - it is a match against a corpus measurement that
/// already exists.
///
/// A MATCH IS STILL ONLY A MATCH, so the cell hands every one to the production
/// `decode_expr`. Sixty-nine acceptances is the decoder agreeing with the
/// bytes; a shape comparison would only be my arithmetic agreeing with my
/// arithmetic, which is the circularity refused at `84951450` and again at
/// `3b510e62`.
///
/// What the sub-slots hold makes it a TELESCOPE rather than a lone binder. Slot
/// 0 is a name link in all 69 - both link constructors occur, 34 of one and 35
/// of the other - and slot 2, the body, is itself `(7, 3)` in 51 of the 69. A
/// binder whose body is another binder, fifty-one deep across the population,
/// is a dependent function type written out.
///
/// And they are shared: 69 references reach 52 distinct objects. That is the
/// same reference-versus-object gap as `2475a62f`'s 71-and-69, in a different
/// slot, and it is pinned here as both numbers for the same reason.
///
/// No size is asserted; classification is by constructor tag and arity, and by
/// what the decoder accepts. No type outside `Expr` is named, and no extension
/// or schema is speculated about.
#[test]
fn the_head_record_slot_three_is_a_pi_type() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut references = 0usize;
    let mut distinct: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut shapes: BTreeSet<(u8, u8)> = BTreeSet::new();
    let mut decoded = 0usize;
    let mut binder_names: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut names_decoded = 0usize;
    let mut nested_binders = 0usize;

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let Some(tail) = resolve(word_at(bytes, object.off + 16)) else {
                continue;
            };
            if at.get(&tail).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(head) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&head).map(|h| (h.tag, h.other)) == Some((0, 5)) {
                records.insert(head);
            }
        }

        for record in records {
            references += 1;
            let word = word_at(bytes, record + 8 + 8 * 3);
            let off = resolve(word).expect("slot 3 is a pointer");
            let object = at.get(&off).expect("resolved above");
            shapes.insert((object.tag, object.other));
            distinct.insert((index, off));

            // The production decoder, not a shape comparison.
            DeclDecoder::new(&view, WalkBudget::default())
                .decode_expr(word)
                .unwrap_or_else(|e| panic!("{module}: slot 3 must decode as an Expr: {e}"));
            decoded += 1;

            // Sub-slot 0: the binder name.
            let name_word = word_at(bytes, off + 8);
            let name_off = resolve(name_word).expect("a binder name is a pointer");
            let link = at.get(&name_off).expect("resolved above");
            *binder_names
                .entry(format!("tag {} arity {}", link.tag, link.other))
                .or_default() += 1;
            DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(name_word)
                .unwrap_or_else(|e| panic!("{module}: a binder name must decode: {e}"));
            names_decoded += 1;

            // Sub-slot 2: the body. Another binder makes it a telescope.
            if let Some(body) = resolve(word_at(bytes, off + 24))
                && at.get(&body).map(|o| (o.tag, o.other)) == Some((7, 3))
            {
                nested_binders += 1;
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(references, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(references, 69, "one slot 3 per distinct head record");
    assert_eq!(
        distinct.len(),
        52,
        "reaching 52 distinct objects - the same reference-versus-object gap as \
         `2475a62f`'s 71 and 69, in a different slot"
    );
    assert_eq!(
        shapes.into_iter().collect::<Vec<_>>(),
        vec![(7, 3)],
        "one shape across all 69"
    );
    assert_eq!(
        decoded, 69,
        "and every one accepted by the PRODUCTION `decode_expr`, which is the \
         decoder agreeing with the bytes rather than my arithmetic agreeing \
         with itself"
    );

    assert_eq!(
        binder_names.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 2".to_owned(), 34),
            ("tag 2 arity 2".to_owned(), 35)
        ],
        "sub-slot 0 is a name link in all 69, and BOTH link constructors occur"
    );
    assert_eq!(names_decoded, 69, "each accepted by `decode_name` as well");
    assert_eq!(
        nested_binders, 51,
        "and in 51 of the 69 the body is itself a binder - a dependent function \
         type written out, not a lone binder"
    );
}

/// Slot 4 links BACK into the third shape - the population is not 99 unrelated
/// oddities.
///
/// The tag-4 option is offered for the third time and the answer has not
/// changed: `9d365d6a` pins that not one of the 11 has a pointer head, so there
/// are no tag-4 head records to classify. Recorded at `c726dec5`, repeated at
/// `c7836115`, repeated here.
///
/// Slot 4 is the last of the five, so this finishes the record. `2475a62f`
/// pinned that it is the only slot whose shape varies - three shapes where its
/// neighbours have one - and said nothing about what those shapes are.
///
/// EIGHT OF THEM ARE `(1, 2)` OBJECTS THAT ARE THEMSELVES THIRD-SHAPE. Not
/// merely the same tag and arity: they satisfy the same tail test that defines
/// the 99, checked here rather than inferred from the header. So a third-shape
/// object's head record can hold, in its last slot, another third-shape object.
///
/// That changes what the population IS. Nine waves have counted, split,
/// located and characterised the 99 as if they were 99 independent objects that
/// happened to share a header. They are not independent - at least eight of
/// them are reachable from another one, through its head record. Whatever these
/// are, they form a linked structure, and no cell before this one could have
/// seen that, because every one of them stopped at the first object whose shape
/// it recognised.
///
/// The other two shapes are pinned as counts and nothing more. No type,
/// extension or schema is named, and no size is asserted anywhere.
#[test]
fn the_head_record_slot_four_links_back_into_the_third_shape() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut references = 0usize;
    let mut distinct: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut shapes: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut third_shape_again = 0usize;
    let mut reaches_a_record = 0usize;

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        // The same test that defines the 99, applied to any candidate rather
        // than only to the objects the outer scan is walking.
        let is_third_shape = |off: usize| -> bool {
            if at.get(&off).map(|o| (o.tag, o.other, o.cs_sz)) != Some((1, 2, 24)) {
                return false;
            }
            let second = word_at(bytes, off + 16);
            if second & 1 == 1 {
                return second >> 1 != 0;
            }
            !resolve(second).is_some_and(|t| at.get(&t).map(|o| (o.tag, o.other)) == Some((1, 2)))
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if !is_third_shape(object.off) {
                continue;
            }
            let Some(tail) = resolve(word_at(bytes, object.off + 16)) else {
                continue;
            };
            if at.get(&tail).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(head) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&head).map(|h| (h.tag, h.other)) == Some((0, 5)) {
                records.insert(head);
            }
        }

        for record in records {
            references += 1;
            let word = word_at(bytes, record + 8 + 8 * 4);
            let Some(off) = resolve(word) else {
                *shapes
                    .entry("boxed or unresolvable".to_owned())
                    .or_default() += 1;
                continue;
            };
            let object = at.get(&off).expect("resolved above");
            distinct.insert((index, off));
            *shapes
                .entry(format!("tag {} arity {}", object.tag, object.other))
                .or_default() += 1;

            if is_third_shape(off) {
                third_shape_again += 1;
            }
            for slot in 0..usize::from(object.other) {
                if let Some(child) = resolve(word_at(bytes, off + 8 + 8 * slot))
                    && at.get(&child).map(|c| (c.tag, c.other)) == Some((0, 5))
                {
                    reaches_a_record += 1;
                }
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(references, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(references, 69, "one slot 4 per distinct head record");
    assert_eq!(
        distinct.len(),
        68,
        "reaching 68 distinct objects: one is shared"
    );
    assert_eq!(
        shapes.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 0 arity 2".to_owned(), 57),
            ("tag 1 arity 2".to_owned(), 8),
            ("tag 5 arity 1".to_owned(), 4),
        ],
        "the three shapes `2475a62f` found varying, now counted"
    );

    // The finding: the population refers to itself.
    assert_eq!(
        third_shape_again, 8,
        "every `(1, 2)` object at slot 4 is ITSELF third-shape - it satisfies \
         the same tail test that defines the 99, checked rather than inferred \
         from the header. The population is linked, not 99 independent objects \
         that happen to share a header"
    );
    assert_eq!(
        reaches_a_record, 8,
        "and each reaches a five-field head record in one hop, which is what \
         being third-shape with a `tag 0` tail means"
    );
}

/// The links are PAIRS. They never compose, and my last commit said otherwise.
///
/// NEITHER OPTION THIS WAVE OFFERED EXISTS. "Slot 5+" is arithmetically
/// impossible: the head records are `tag 0` ARITY 5, pinned by `2475a62f` and
/// re-asserted in every cell since, so their slots are 0 through 4 and
/// `8ca067f9` read the last one. And the 11 tag-4 objects have no head records
/// - `9d365d6a` pins that not one of them has a pointer head - which is the
/// fourth wave to offer it.
///
/// So this takes the increment `8ca067f9` named: the shape of the structure
/// those links form. It also CORRECTS that commit. It said the 99 "form a
/// LINKED STRUCTURE - a chain or a tree - rather than a scattered population".
/// The first half is right and the parenthesis is wrong.
///
/// Measured over the 71 nodes: 8 edges, every target in the node set, no node
/// with more than one incoming edge, no cycles, and the longest path from any
/// root is ONE EDGE. The structure is 8 disjoint pairs and 55 isolated nodes.
/// Links exist; they never compose.
///
/// THE ERROR WAS REASONING FROM AN EDGE'S EXISTENCE TO A SHAPE. Eight edges
/// among 71 nodes is equally consistent with one chain of nine, a tree, or
/// eight unrelated pairs, and "chain or a tree" picked two of those and left
/// out the one that is true. Nothing was measured between finding the edges and
/// describing what they build - the distance between those two steps is exactly
/// one graph traversal, and I wrote the sentence instead of taking it.
///
/// The pairs are still the substantive part: 16 of the 71 are not independent.
/// That is a smaller claim than the one it replaces and it is the one the bytes
/// support.
#[test]
fn the_third_shape_links_are_pairs_and_never_chains() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut nodes = 0usize;
    let mut edges = 0usize;
    let mut targets_outside = 0usize;
    let mut in_degrees: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();
    let mut longest = 0usize;
    let mut cycles = 0usize;
    let mut isolated = 0usize;

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let is_third_shape = |off: usize| -> bool {
            if at.get(&off).map(|o| (o.tag, o.other, o.cs_sz)) != Some((1, 2, 24)) {
                return false;
            }
            let second = word_at(bytes, off + 16);
            if second & 1 == 1 {
                return second >> 1 != 0;
            }
            !resolve(second).is_some_and(|t| at.get(&t).map(|o| (o.tag, o.other)) == Some((1, 2)))
        };

        // Nodes: third-shape objects with a `tag 0` tail and a five-field head.
        let mut here: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if !is_third_shape(object.off) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let head = resolve(word_at(bytes, object.off + 8));
            if head.and_then(|h| at.get(&h)).map(|h| (h.tag, h.other)) == Some((0, 5)) {
                here.insert(object.off);
            }
        }

        // Edges: node -> its head record's slot 4, when that is itself a node.
        let mut successor: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        for &node in &here {
            let head = resolve(word_at(bytes, node + 8)).expect("nodes have head records");
            if let Some(target) = resolve(word_at(bytes, head + 8 + 8 * 4))
                && is_third_shape(target)
            {
                if here.contains(&target) {
                    successor.insert(node, target);
                } else {
                    targets_outside += 1;
                }
            }
        }

        let mut incoming: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        for target in successor.values() {
            *incoming.entry(*target).or_default() += 1;
        }
        for &node in &here {
            *in_degrees
                .entry(incoming.get(&node).copied().unwrap_or(0))
                .or_default() += 1;
            if !successor.contains_key(&node) && !incoming.contains_key(&node) {
                isolated += 1;
            }
            // Walk forward from every node; a root is one with no incoming.
            if incoming.get(&node).is_none() {
                let mut walked: BTreeSet<usize> = BTreeSet::new();
                let mut cursor = node;
                let mut length = 0usize;
                while let Some(&next) = successor.get(&cursor) {
                    if !walked.insert(cursor) {
                        cycles += 1;
                        break;
                    }
                    cursor = next;
                    length += 1;
                }
                longest = longest.max(length);
            }
        }

        nodes += here.len();
        edges += successor.len();
    }

    if !prelude_loaded {
        assert_eq!(nodes, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(nodes, 71, "the tag-0-tailed third-shape objects");
    assert_eq!(edges, 8, "the links `8ca067f9` found");
    assert!(
        edges > 0,
        "with no edges every claim below is vacuously true about a graph with \
         no structure to describe"
    );
    assert_eq!(
        targets_outside, 0,
        "every link target is itself one of the 71"
    );

    // The shape, which is the correction.
    assert_eq!(
        in_degrees.into_iter().collect::<Vec<_>>(),
        vec![(0, 63), (1, 8)],
        "no node is pointed at twice: the links do not converge"
    );
    assert_eq!(cycles, 0, "and they do not close");
    assert_eq!(
        longest, 1,
        "the longest path from any root is ONE EDGE. Eight edges among 71 nodes \
         is equally consistent with a chain of nine or a tree; it is neither. \
         `8ca067f9` said \"a chain or a tree\" without traversing, and this is \
         the traversal"
    );
    assert_eq!(
        isolated, 55,
        "so the structure is 8 disjoint pairs and 55 isolated nodes: 16 of the \
         71 are not independent, and the other 55 are"
    );
}

/// The 157 array elements are (Name, Name, Expr) triples.
///
/// BOTH OPTIONS ARE STILL IMPOSSIBLE and this is the fifth wave to offer one of
/// them. The head records are `tag 0` ARITY 5, so there is no slot 5 - pinned
/// at `2475a62f`, and `8ca067f9` read slot 4, the last one. The 11 tag-4
/// objects have no head records at all, because `9d365d6a` pins that not one of
/// them has a pointer head. Repeating the reasons rather than quietly
/// substituting work is the only way the log stays honest about what was asked.
///
/// So this opens the one thing I could still name as unread: `3b510e62`
/// counted 157 elements across the 69 slot-2 arrays and never looked inside
/// them.
///
/// Every element is the same three-field shape, and the three fields go to the
/// PRODUCTION decoders rather than to a shape comparison: slots 0 and 1 to
/// `decode_name`, slot 2 to `decode_expr`, 471 decodes in all. That is the
/// instrument that identified the `Expr.const` declNames at `aec3efd1` and the
/// binder names at `c7836115`, and it is the difference between the bytes
/// agreeing with themselves and the decoder agreeing with the bytes.
///
/// Slot 1 admits BOTH name link constructors, 97 and 60, and slot 2 admits six
/// expression shapes. A field that varies is holding real values; the uniform
/// slot 0 is the one that would look the same if it held a repeated constant,
/// which is why the varying ones are worth counting separately.
///
/// The 157 references reach 111 distinct objects. That is the third
/// reference-versus-object gap in this structure, after `2475a62f`'s 71-and-69
/// and `c7836115`'s 69-and-52, and by now it should be assumed rather than
/// discovered: a compacted region shares every structurally identical subterm,
/// so a count of references is never a count of objects until it has been
/// deduplicated.
///
/// No size is asserted, and no type, extension or schema is named.
#[test]
fn the_slot_two_array_elements_are_name_name_expr_triples() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut arrays = 0usize;
    let mut elements = 0usize;
    let mut boxed_elements = 0usize;
    let mut distinct: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut element_shapes: BTreeSet<(u8, u8)> = BTreeSet::new();
    let mut names_decoded = 0usize;
    let mut exprs_decoded = 0usize;
    let mut second_names: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut third_shapes: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let head = resolve(word_at(bytes, object.off + 8));
            if head.and_then(|h| at.get(&h)).map(|h| (h.tag, h.other)) == Some((0, 5))
                && let Some(head) = head
            {
                records.insert(head);
            }
        }

        for record in records {
            arrays += 1;
            let array = resolve(word_at(bytes, record + 8 + 8 * 2)).expect("slot 2 is an array");
            let length = word_at(bytes, array + 8);
            for i in 0..length {
                elements += 1;
                let word = word_at(bytes, array + 24 + 8 * i as usize);
                let Some(off) = resolve(word) else {
                    boxed_elements += 1;
                    continue;
                };
                let element = at.get(&off).expect("resolved above");
                element_shapes.insert((element.tag, element.other));
                distinct.insert((index, off));

                // Field 0 and field 1 to `decode_name`; field 2 to `decode_expr`.
                for slot in 0..2usize {
                    let field = word_at(bytes, off + 8 + 8 * slot);
                    DeclDecoder::new(&view, WalkBudget::default())
                        .decode_name(field)
                        .unwrap_or_else(|e| {
                            panic!("{module}: element field {slot} must decode as a Name: {e}")
                        });
                    names_decoded += 1;
                    if slot == 1
                        && let Some(link) = resolve(field)
                    {
                        let link = at.get(&link).expect("resolved above");
                        *second_names
                            .entry(format!("tag {} arity {}", link.tag, link.other))
                            .or_default() += 1;
                    }
                }
                let third = word_at(bytes, off + 8 + 8 * 2);
                DeclDecoder::new(&view, WalkBudget::default())
                    .decode_expr(third)
                    .unwrap_or_else(|e| {
                        panic!("{module}: element field 2 must decode as an Expr: {e}")
                    });
                exprs_decoded += 1;
                if let Some(expression) = resolve(third) {
                    let expression = at.get(&expression).expect("resolved above");
                    *third_shapes
                        .entry(format!("tag {} arity {}", expression.tag, expression.other))
                        .or_default() += 1;
                }
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(arrays, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(arrays, 69, "one slot-2 array per distinct head record");
    assert_eq!(
        elements, 157,
        "the elements `3b510e62` counted and never opened"
    );
    assert_eq!(boxed_elements, 0, "every element is a pointer");
    assert_eq!(
        distinct.len(),
        111,
        "reaching 111 distinct objects - the third reference-versus-object gap \
         in this structure, after 71-and-69 and 69-and-52"
    );
    assert_eq!(
        element_shapes.into_iter().collect::<Vec<_>>(),
        vec![(0, 3)],
        "and every one is the same three-field shape"
    );

    // The production decoders, not shape comparisons.
    assert_eq!(
        names_decoded, 314,
        "two names per element, every one accepted by `decode_name`"
    );
    assert_eq!(
        exprs_decoded, 157,
        "and one expression per element, accepted by `decode_expr`"
    );
    assert_eq!(
        second_names.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 2".to_owned(), 97),
            ("tag 2 arity 2".to_owned(), 60)
        ],
        "the second name admits BOTH link constructors, so it holds real names \
         rather than a repeated constant"
    );
    assert_eq!(
        third_shapes.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 1".to_owned(), 61),
            ("tag 10 arity 2".to_owned(), 2),
            ("tag 3 arity 1".to_owned(), 30),
            ("tag 4 arity 2".to_owned(), 23),
            ("tag 5 arity 2".to_owned(), 16),
            ("tag 7 arity 3".to_owned(), 25),
        ],
        "and the expression admits six shapes"
    );
}

/// The triples' first field is one numbered name family.
///
/// The tag-4 option is offered a sixth time and is still impossible -
/// `9d365d6a` pins that not one of the 11 has a pointer head, so there are no
/// tag-4 head records. The first option is real, and this takes it.
///
/// `a4de2083` found field 0 UNIFORM where fields 1 and 2 vary, and said so as a
/// caution: a uniform field is what a repeated constant looks like. It is not a
/// constant. Across 157 references it reaches 31 distinct objects, every one a
/// `Name.num` link whose prefix is a SINGLE-COMPONENT name and whose numeral is
/// a boxed scalar - never a heap mpz - with 31 distinct values from 1 to 42.
///
/// So the field holds a numbered family: one base name, numbered instances. It
/// is uniform in SHAPE and various in VALUE, which is a different thing from
/// the repeated constant `a4de2083` was right to worry about, and only reading
/// the numerals separates the two.
///
/// THE SINGLE-COMPONENT FACT IS STRUCTURAL - the prefix link's own prefix slot
/// is the boxed anonymous name - and so is the boxedness of every numeral.
/// Neither depends on decoding a string. The SPELLING does: `_uniq` comes from
/// reading the string payload with the walker in this file, which I corrected
/// once already this session after it returned truncated text. It is pinned
/// because it is the identifying fact, and flagged because it is the fragile
/// one: a red there names the real spelling and is a finding, not a fault.
///
/// All 157 are additionally handed to the production `decode_name`, which is
/// what makes "these are names" a claim about the decoder rather than about my
/// arithmetic.
///
/// No size is asserted. No extension or schema is named, and nothing is claimed
/// about what the family MEANS - only that it is one.
#[test]
fn the_triple_first_field_is_a_numbered_name_family() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut references = 0usize;
    let mut distinct: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut link_shapes: BTreeSet<(u8, u8)> = BTreeSet::new();
    let mut single_component = 0usize;
    let mut boxed_numerals = 0usize;
    let mut numerals: BTreeSet<u64> = BTreeSet::new();
    let mut decoded = 0usize;
    let mut spellings: BTreeSet<String> = BTreeSet::new();

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && at.get(&head).map(|h| (h.tag, h.other)) == Some((0, 5))
            {
                records.insert(head);
            }
        }

        for record in records {
            let array = resolve(word_at(bytes, record + 8 + 8 * 2)).expect("slot 2 is an array");
            for i in 0..word_at(bytes, array + 8) {
                let element =
                    resolve(word_at(bytes, array + 24 + 8 * i as usize)).expect("an element");
                let field = word_at(bytes, element + 8);
                let off = resolve(field).expect("field 0 is a pointer");
                references += 1;
                distinct.insert((index, off));

                let link = at.get(&off).expect("resolved above");
                link_shapes.insert((link.tag, link.other));

                // Structural: the prefix's own prefix slot is the anonymous name.
                let prefix = resolve(word_at(bytes, off + 8)).expect("a prefix link");
                if word_at(bytes, prefix + 8) & 1 == 1 && word_at(bytes, prefix + 8) >> 1 == 0 {
                    single_component += 1;
                }
                // Structural: the numeral is boxed, never a heap object.
                let numeral = word_at(bytes, off + 16);
                if numeral & 1 == 1 {
                    boxed_numerals += 1;
                    numerals.insert(numeral >> 1);
                }
                // The production decoder, and the spelling it produces.
                let name = DeclDecoder::new(&view, WalkBudget::default())
                    .decode_name(field)
                    .unwrap_or_else(|e| panic!("{module}: field 0 must decode as a Name: {e}"));
                decoded += 1;
                let shown = name.to_display_string();
                spellings.insert(
                    shown
                        .rsplit_once('.')
                        .map_or(shown.clone(), |(base, _)| base.to_owned()),
                );
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(references, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(references, 157, "one field 0 per triple");
    assert_eq!(
        distinct.len(),
        31,
        "reaching 31 distinct names - uniform in SHAPE but various in VALUE, \
         which is not the repeated constant a uniform field could have been"
    );
    assert_eq!(
        link_shapes.into_iter().collect::<Vec<_>>(),
        vec![(2, 2)],
        "every one the numbered link constructor"
    );

    // Structural, independent of any string decoding.
    assert_eq!(
        single_component, 157,
        "every base name is a single component: the prefix link's own prefix \
         slot is the boxed anonymous name"
    );
    assert_eq!(
        boxed_numerals, 157,
        "and every numeral is a boxed scalar, never a heap mpz"
    );
    assert_eq!(
        (
            numerals.len(),
            numerals.first().copied(),
            numerals.last().copied()
        ),
        (31, Some(1), Some(42)),
        "31 distinct numerals from 1 to 42 - a numbered family, not a constant"
    );

    // The production decoder, then the fragile part.
    assert_eq!(decoded, 157, "every one accepted by `decode_name`");
    assert_eq!(
        spellings.into_iter().collect::<Vec<_>>(),
        vec!["_uniq".to_owned()],
        "one base name across all 157. The SPELLING is the least robust thing \
         in this cell - it comes from reading the string payload - so a failure \
         here names the real base name and is a finding rather than a fault"
    );
}

/// The 111 DISTINCT triples, decoded - and they weigh differently from the 157
/// references.
///
/// `a4de2083` already decoded these fields and pinned field 1's constructor
/// split and field 2's expression shapes. It did so over the 157 REFERENCES.
/// This does it over the 111 distinct objects, and the two disagree:
///
///   field 1   97 / 60 by reference, 61 / 50 by object
///   field 2   61, 2, 30, 23, 16, 25 by reference
///             26, 2, 26, 21, 13, 23 by object
///
/// A reference-weighted histogram counts a shared value once per pointer to it,
/// so it describes how often a value is USED; an object-weighted one describes
/// how many values there ARE. Neither is wrong and they answer different
/// questions, which is precisely why both belong in the file rather than one
/// silently standing for the other. The gap is not small: field 2's most common
/// shape by reference is not its most common shape by object.
///
/// This is the fourth reference-versus-object distinction in this structure -
/// after 71-and-69, 69-and-52, and 157-and-111 - and the first where the
/// deduplication changes a RANKING rather than only a total. The sharing is
/// heavy: 111 slots reach 51 distinct names in field 1 and 49 distinct
/// expressions in field 2.
///
/// Field 0 is uniform and stays uniform: 31 distinct names across the 111,
/// the same 31 `3373af3b` found across the 157. A field whose distinct count
/// does not move under deduplication is one whose sharing is already total.
///
/// All 333 fields go through the production decoders - two names and one
/// expression per record - because a shape histogram alone would be my
/// arithmetic agreeing with itself.
///
/// No size is asserted. No schema, type or extension is named.
#[test]
fn the_distinct_triples_weigh_differently_from_their_references() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut triples = 0usize;
    let mut names_decoded = 0usize;
    let mut exprs_decoded = 0usize;
    let mut first_names: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut second_names: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut expressions: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut second_split: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut expression_shapes: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && at.get(&head).map(|h| (h.tag, h.other)) == Some((0, 5))
            {
                records.insert(head);
            }
        }

        // Deduplicate the elements BEFORE reading them. That single `BTreeSet`
        // is the whole difference from `a4de2083`.
        let mut distinct: BTreeSet<usize> = BTreeSet::new();
        for record in records {
            let array = resolve(word_at(bytes, record + 8 + 8 * 2)).expect("slot 2 is an array");
            for i in 0..word_at(bytes, array + 8) {
                if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) {
                    distinct.insert(element);
                }
            }
        }

        for triple in distinct {
            triples += 1;
            for slot in 0..2usize {
                let field = word_at(bytes, triple + 8 + 8 * slot);
                DeclDecoder::new(&view, WalkBudget::default())
                    .decode_name(field)
                    .unwrap_or_else(|e| panic!("{module}: field {slot} must be a Name: {e}"));
                names_decoded += 1;
                let off = resolve(field).expect("a name link");
                if slot == 0 {
                    first_names.insert((index, off));
                } else {
                    second_names.insert((index, off));
                    let link = at.get(&off).expect("resolved above");
                    *second_split
                        .entry(format!("tag {} arity {}", link.tag, link.other))
                        .or_default() += 1;
                }
            }
            let third = word_at(bytes, triple + 8 + 8 * 2);
            DeclDecoder::new(&view, WalkBudget::default())
                .decode_expr(third)
                .unwrap_or_else(|e| panic!("{module}: field 2 must be an Expr: {e}"));
            exprs_decoded += 1;
            let off = resolve(third).expect("an expression");
            expressions.insert((index, off));
            let expression = at.get(&off).expect("resolved above");
            *expression_shapes
                .entry(format!("tag {} arity {}", expression.tag, expression.other))
                .or_default() += 1;
        }
    }

    if !prelude_loaded {
        assert_eq!(triples, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(triples, 111, "the distinct triples `a4de2083` counted");
    assert_eq!(
        names_decoded, 222,
        "two names per record, through `decode_name`"
    );
    assert_eq!(
        exprs_decoded, 111,
        "one expression per record, through `decode_expr`"
    );

    // Field 0: uniform, and unchanged by deduplication.
    assert_eq!(
        first_names.len(),
        31,
        "field 0 is uniform and stays uniform - the same 31 names `3373af3b` \
         found across the 157 references. A distinct count that does not move \
         under deduplication is one whose sharing was already total"
    );

    // Fields 1 and 2: the object-weighted answers, which differ from
    // `a4de2083`'s reference-weighted ones.
    assert_eq!(
        second_split.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 2".to_owned(), 61),
            ("tag 2 arity 2".to_owned(), 50)
        ],
        "field 1 by OBJECT, against 97 and 60 by reference"
    );
    assert_eq!(second_names.len(), 51, "reaching 51 distinct names");
    assert_eq!(
        expression_shapes.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 1".to_owned(), 26),
            ("tag 10 arity 2".to_owned(), 2),
            ("tag 3 arity 1".to_owned(), 26),
            ("tag 4 arity 2".to_owned(), 21),
            ("tag 5 arity 2".to_owned(), 13),
            ("tag 7 arity 3".to_owned(), 23),
        ],
        "field 2 by OBJECT, against 61, 2, 30, 23, 16 and 25 by reference - the \
         most common shape is not the same one under the two weightings"
    );
    assert_eq!(expressions.len(), 49, "reaching 49 distinct expressions");
}

/// The two other slot-4 shapes, opened - and they interlock.
///
/// `8ca067f9` pinned slot 4 as three shapes with counts and opened only one of
/// them, the eight that are themselves third-shape. These are the other two:
/// `(0, 2)` fifty-seven times and `(5, 1)` four times.
///
/// The `(5, 1)` objects are a single field wrapping a numbered name link, and
/// all four go to the production `decode_name` rather than being matched by
/// shape.
///
/// THE `(0, 2)` OBJECTS INTERLOCK WITH THEM. Their first field is uniformly a
/// four-field record; their second admits three shapes - and two of those three
/// are `(0, 2)` and `(5, 1)`, the same two shapes slot 4 itself admits. So an
/// object of one kind can hold an object of the other, and 44 of the 56 hold
/// another of their own kind.
///
/// That is a spine: not the pairing `3575962c` measured among the third-shape
/// objects themselves, but a second and separate chaining one level down.
/// `3575962c` is why this cell does NOT say how long the spine is or what shape
/// it forms - eight edges there were consistent with a chain, a tree or eight
/// pairs, and only a traversal could tell them apart. Counting what each field
/// admits is not traversing, and the wave that traverses this one can say what
/// it builds.
///
/// Deduplicated as well as counted by reference, because that distinction has
/// now changed a total three times and a ranking once: 57 references reach 56
/// objects, and the four `(5, 1)` are four.
///
/// No size is asserted. No schema, type or extension is named.
#[test]
fn the_slot_four_other_shapes_interlock() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut pair_references = 0usize;
    let mut wrapper_references = 0usize;
    let mut pairs: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut wrappers: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut first_fields: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut second_fields: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut wrapped: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut names_decoded = 0usize;

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape_of = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && at.get(&head).map(|h| (h.tag, h.other)) == Some((0, 5))
            {
                records.insert(head);
            }
        }

        for record in records {
            let Some(off) = resolve(word_at(bytes, record + 8 + 8 * 4)) else {
                continue;
            };
            match at.get(&off).map(|o| (o.tag, o.other)) {
                Some((0, 2)) => {
                    pair_references += 1;
                    pairs.insert((index, off));
                }
                Some((5, 1)) => {
                    wrapper_references += 1;
                    wrappers.insert((index, off));
                }
                _ => {}
            }
        }

        // Deduplicated before reading, the `c0a4f175` discipline.
        for (_, off) in pairs.iter().filter(|(i, _)| *i == index) {
            let first = resolve(word_at(bytes, off + 8)).expect("field 0 is a pointer");
            *first_fields.entry(shape_of(first)).or_default() += 1;
            let second = resolve(word_at(bytes, off + 16)).expect("field 1 is a pointer");
            *second_fields.entry(shape_of(second)).or_default() += 1;
        }
        for (_, off) in wrappers.iter().filter(|(i, _)| *i == index) {
            let field = word_at(bytes, off + 8);
            let inner = resolve(field).expect("the wrapped field is a pointer");
            *wrapped.entry(shape_of(inner)).or_default() += 1;
            DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(field)
                .unwrap_or_else(|e| panic!("{module}: a wrapped name must decode: {e}"));
            names_decoded += 1;
        }
    }

    if !prelude_loaded {
        assert_eq!(
            pair_references + wrapper_references,
            0,
            "not in the C3 fixtures"
        );
        return;
    }

    assert_eq!(
        (pair_references, pairs.len()),
        (57, 56),
        "the two-field shape: 57 references reaching 56 objects"
    );
    assert_eq!(
        (wrapper_references, wrappers.len()),
        (4, 4),
        "and the one-field shape, shared by nothing"
    );

    // The one-field shape wraps a name, established by the decoder.
    assert_eq!(
        wrapped.into_iter().collect::<Vec<_>>(),
        vec![("tag 2 arity 2".to_owned(), 4)],
        "each wraps a numbered name link"
    );
    assert_eq!(names_decoded, 4, "and `decode_name` accepts every one");

    // The two-field shape, and the interlock.
    assert_eq!(
        first_fields.into_iter().collect::<Vec<_>>(),
        vec![("tag 0 arity 4".to_owned(), 56)],
        "field 0 is uniformly a four-field record"
    );
    assert_eq!(
        second_fields.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 0 arity 2".to_owned(), 44),
            ("tag 4 arity 1".to_owned(), 6),
            ("tag 5 arity 1".to_owned(), 6),
        ],
        "field 1 admits three shapes, and TWO of them are the two shapes slot 4 \
         itself admits - so an object of one kind can hold one of the other, and \
         44 of the 56 hold another of their own kind. That is a spine; how long \
         it is and what it forms needs a traversal, which `3575962c` is the \
         reason not to guess"
    );
}

/// The spine, TRAVERSED - and it is none of the three things I would have
/// guessed.
///
/// `241893a7` found that 44 of 56 two-field objects hold another of their own
/// kind and deliberately refused to say what that builds, because `3575962c`
/// had just caught me inferring "a chain or a tree" from an edge count when the
/// truth was eight disjoint pairs. This is the traversal that settles it.
///
/// IT IS NOT ANY OF THEM. Not disjoint pairs, not a chain, and not a tree:
///
///   seeds reached from slot 4    56
///   nodes after closing on field 1   102
///   edges    62
///   in-degree   56 nodes at 0, 43 at 1, 2 at 2, and ONE at 15
///   roots    56, longest walk 6 edges, no cycles
///
/// A tree has in-degree at most one everywhere. A node with fifteen incoming
/// edges is a confluence: fifteen distinct walks arrive at the same object and
/// share everything after it. So the structure is a DAG that CONVERGES, which
/// is what a compacted region does to lists that share a suffix.
///
/// THE CONVERGENCE IS PROVED TWICE, by design. Once by the in-degree histogram,
/// and once by arithmetic that does not depend on it: walking from every root
/// visits 119 nodes counted with multiplicity, over a node set of 102. Walks
/// that overlap are the same thing as edges that converge, and two independent
/// routes to it means a mistake in either one is caught.
///
/// THE NODE SET NEARLY DOUBLES UNDER CLOSURE - 56 seeds become 102 nodes. The
/// spine extends well past what slot 4 reaches, so 46 of these objects were
/// invisible to every previous cell. Counting the objects a field ADMITS never
/// finds them; only following the edges does, which is the same lesson as
/// `3575962c` arriving from the other side: there the inference overstated the
/// structure, here it would have understated the population.
///
/// No size is asserted. No schema, type or extension is named.
#[test]
fn the_pair_spine_is_a_converging_dag() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut seeds = 0usize;
    let mut nodes = 0usize;
    let mut edges = 0usize;
    let mut roots = 0usize;
    let mut cycles = 0usize;
    let mut longest = 0usize;
    let mut visits = 0usize;
    let mut in_degrees: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();
    let mut walk_lengths: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let is_pair = |off: usize| at.get(&off).map(|o| (o.tag, o.other)) == Some((0, 2));

        // Seeds: the two-field objects slot 4 points at.
        let mut here: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(record) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&record).map(|h| (h.tag, h.other)) != Some((0, 5)) {
                continue;
            }
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && is_pair(target)
            {
                here.insert(target);
            }
        }
        seeds += here.len();

        // Close on field 1. The node set is NOT the seed set.
        let mut all = here.clone();
        let mut frontier: Vec<usize> = here.into_iter().collect();
        let mut successor: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && is_pair(target)
            {
                successor.insert(node, target);
                if all.insert(target) {
                    frontier.push(target);
                }
            }
        }
        nodes += all.len();
        edges += successor.len();

        let mut incoming: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        for target in successor.values() {
            *incoming.entry(*target).or_default() += 1;
        }
        for &node in &all {
            *in_degrees
                .entry(incoming.get(&node).copied().unwrap_or(0))
                .or_default() += 1;
        }

        for &node in &all {
            if incoming.contains_key(&node) {
                continue;
            }
            roots += 1;
            let mut walked: BTreeSet<usize> = BTreeSet::new();
            let mut cursor = node;
            let mut length = 0usize;
            visits += 1;
            while let Some(&next) = successor.get(&cursor) {
                if !walked.insert(cursor) {
                    cycles += 1;
                    break;
                }
                cursor = next;
                length += 1;
                visits += 1;
            }
            *walk_lengths.entry(length).or_default() += 1;
            longest = longest.max(length);
        }
    }

    if !prelude_loaded {
        assert_eq!(nodes, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert!(edges > 0, "with no edges every claim below is vacuous");
    assert_eq!(
        (seeds, nodes),
        (56, 102),
        "the node set nearly doubles under closure: 46 of these objects are not \
         reached from slot 4 at all, and no cell that counted what a field \
         ADMITS could have found them"
    );
    assert_eq!(edges, 62, "the field-1 links");

    // Not a tree, not chains: something has fifteen parents.
    assert_eq!(
        in_degrees.into_iter().collect::<Vec<_>>(),
        vec![(0, 56), (1, 43), (2, 2), (15, 1)],
        "a tree has in-degree at most one everywhere. A node with fifteen \
         incoming edges is a confluence"
    );
    assert_eq!(cycles, 0, "and nothing closes, so it is a DAG");
    assert_eq!(
        (roots, longest),
        (56, 6),
        "56 roots, and the longest walk is six edges"
    );
    assert_eq!(
        walk_lengths.into_iter().collect::<Vec<_>>(),
        vec![(0, 12), (1, 33), (2, 6), (3, 4), (6, 1)],
        "walk lengths from each root"
    );

    // The convergence, proved a second way that does not use in-degree.
    assert_eq!(
        (visits, nodes),
        (119, 102),
        "walking from every root visits 119 nodes counted with multiplicity \
         over a node set of 102, so the walks OVERLAP - which is the same fact \
         as the in-degree histogram, reached without it"
    );
}

/// The 46 interior spine nodes: same shape, disjoint contents.
///
/// `b327b20c` found them by closing the spine on field 1 - 56 seeds becoming
/// 102 nodes - and characterised none of them. They had been invisible to every
/// earlier cell because every earlier cell reached objects by asking what a
/// field ADMITS, and these are reached only by following edges.
///
/// They are `(0, 2)` by construction, so their shape is not news. What is news
/// is that they are not simply more of the same:
///
///   FIELD 0 IS DISJOINT. The 56 seeds carry 54 distinct four-field records
///   between them; the 46 interior nodes carry 46, one each; and the two sets
///   share NOT ONE object. Whatever these records hold, the interior of the
///   spine holds different ones from its entry points, and no amount of sharing
///   connects them.
///
///   FIELD 1 DIFFERS CATEGORICALLY. The seeds admit three shapes; the interior
///   admits two. The `(4, 1)` shape occurs six times among the seeds and ZERO
///   times among the 46. That is a categorical absence rather than a
///   difference of proportion, which is why it is asserted as a count of zero
///   and not as a distribution.
///
/// The interior also terminates differently - 28 of its 46 end in the
/// one-field shape against 6 of 56 - but that is a difference of proportion
/// over small numbers, so it is pinned as the two histograms and NOT described
/// as a tendency. Two counts side by side let a reader draw that conclusion;
/// a sentence asserting it would be me drawing it for them from 46 samples.
///
/// No size is asserted. No schema, type or extension is named.
#[test]
fn the_forty_six_interior_spine_nodes_are_disjoint() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut seed_count = 0usize;
    let mut interior_count = 0usize;
    let mut seed_records: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut interior_records: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut shared_records = 0usize;
    let mut seed_shapes: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut interior_shapes: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut seed_next: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut interior_next: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let is_pair = |off: usize| at.get(&off).map(|o| (o.tag, o.other)) == Some((0, 2));
        let shape_of = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(record) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&record).map(|h| (h.tag, h.other)) != Some((0, 5)) {
                continue;
            }
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && is_pair(target)
            {
                seeds.insert(target);
            }
        }

        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && is_pair(target)
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        for node in &all {
            let seed = seeds.contains(node);
            let record = resolve(word_at(bytes, node + 8)).expect("field 0 is a pointer");
            let next = resolve(word_at(bytes, node + 16));
            let next_shape = next.map_or("boxed or unresolvable".to_owned(), &shape_of);
            if seed {
                seed_count += 1;
                seed_records.insert((index, record));
                *seed_shapes.entry(shape_of(record)).or_default() += 1;
                *seed_next.entry(next_shape).or_default() += 1;
            } else {
                interior_count += 1;
                interior_records.insert((index, record));
                *interior_shapes.entry(shape_of(record)).or_default() += 1;
                *interior_next.entry(next_shape).or_default() += 1;
            }
        }
        shared_records += seed_records
            .iter()
            .filter(|entry| interior_records.contains(entry))
            .count();
    }

    if !prelude_loaded {
        assert_eq!(
            interior_count, 0,
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    assert_eq!(
        (seed_count, interior_count),
        (56, 46),
        "the seeds and the nodes only the traversal found"
    );

    // Same shape - not the news.
    assert_eq!(
        seed_shapes.into_iter().collect::<Vec<_>>(),
        vec![("tag 0 arity 4".to_owned(), 56)],
        "every seed's field 0 is a four-field record"
    );
    assert_eq!(
        interior_shapes.into_iter().collect::<Vec<_>>(),
        vec![("tag 0 arity 4".to_owned(), 46)],
        "and so is every interior node's"
    );

    // Disjoint contents - the news.
    assert_eq!(
        (seed_records.len(), interior_records.len(), shared_records),
        (54, 46, 0),
        "the seeds carry 54 distinct records, the interior 46, and the two sets \
         share NOT ONE. The interior of the spine holds different records from \
         its entry points"
    );

    // Categorical absence, asserted as a zero rather than as a proportion.
    assert_eq!(
        seed_next.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 0 arity 2".to_owned(), 44),
            ("tag 4 arity 1".to_owned(), 6),
            ("tag 5 arity 1".to_owned(), 6),
        ],
        "the seeds' field 1 admits three shapes"
    );
    assert_eq!(
        interior_next.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 0 arity 2".to_owned(), 18),
            ("tag 5 arity 1".to_owned(), 28),
        ],
        "the interior admits two: the `tag 4 arity 1` shape occurs six times \
         among the seeds and ZERO times here, which is a categorical absence \
         rather than a difference of proportion"
    );
}

/// The four-field records - both populations, kept apart.
///
/// The order says "the four-field record at field 0 of the `(0, 2)` objects",
/// and `d8906952` is why that phrase now needs a qualifier: there are TWO
/// disjoint sets of them, 54 reached from the seeds and 46 from the interior,
/// sharing not one object. A cell that merged them would report histograms over
/// a population nobody named. So both are measured and neither is folded into
/// the other.
///
/// THEY SHARE A LAYOUT. Slot 0 is a numbered name link in all 100. Slot 1 is a
/// name link in all 100. Slot 2 is an expression in all 100. Slots 0, 1 and 2
/// therefore go to the production `decode_name` and `decode_expr` - 200 names
/// and 100 expressions - rather than being matched by shape.
///
/// SLOT 3 IS NOT DECODED, and saying why is the point. It carries three shapes,
/// two of arity three and one of arity two, and none of them is a name link or
/// an expression constructor. I have no decoder that accepts it and no basis
/// for naming its type, so it is pinned as shapes and counts and left there.
/// Running `decode_expr` on it to see what happens would be a guess with a
/// pass/fail dressed as evidence.
///
/// THE TWO POPULATIONS DIFFER IN THEIR DISTRIBUTIONS, and this cell reports the
/// difference without characterising it. Slot 1 admits both name constructors
/// among the seeds - 52 and 2 - and only one among the interior's 46. Slots 2
/// and 3 differ in proportion. Two of those are small numbers, so they are two
/// histograms side by side and no sentence about a tendency, the discipline
/// `d8906952` settled after `3575962c`.
///
/// No size is asserted. No schema, type or extension is named.
#[test]
fn the_four_field_records_share_a_layout() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut counts = [0usize; 2];
    let mut names_decoded = 0usize;
    let mut exprs_decoded = 0usize;
    let mut first = [(); 2].map(|()| std::collections::BTreeMap::<String, usize>::new());
    let mut second = [(); 2].map(|()| std::collections::BTreeMap::<String, usize>::new());
    let mut third = [(); 2].map(|()| std::collections::BTreeMap::<String, usize>::new());
    let mut fourth = [(); 2].map(|()| std::collections::BTreeMap::<String, usize>::new());

    for (module, bytes) in &modules {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let is_pair = |off: usize| at.get(&off).map(|o| (o.tag, o.other)) == Some((0, 2));
        let shape_of = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(record) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&record).map(|h| (h.tag, h.other)) != Some((0, 5)) {
                continue;
            }
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && is_pair(target)
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && is_pair(target)
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        // Two disjoint record sets, deduplicated within each.
        let mut records: [BTreeSet<usize>; 2] = [BTreeSet::new(), BTreeSet::new()];
        for node in &all {
            let which = usize::from(!seeds.contains(node));
            if let Some(record) = resolve(word_at(bytes, node + 8)) {
                records[which].insert(record);
            }
        }

        for (which, set) in records.iter().enumerate() {
            for &record in set {
                counts[which] += 1;
                for slot in 0..2usize {
                    let field = word_at(bytes, record + 8 + 8 * slot);
                    DeclDecoder::new(&view, WalkBudget::default())
                        .decode_name(field)
                        .unwrap_or_else(|e| panic!("{module}: slot {slot} must be a Name: {e}"));
                    names_decoded += 1;
                    let off = resolve(field).expect("a name link");
                    let target = if slot == 0 { &mut first } else { &mut second };
                    *target[which].entry(shape_of(off)).or_default() += 1;
                }
                let expression = word_at(bytes, record + 8 + 8 * 2);
                DeclDecoder::new(&view, WalkBudget::default())
                    .decode_expr(expression)
                    .unwrap_or_else(|e| panic!("{module}: slot 2 must be an Expr: {e}"));
                exprs_decoded += 1;
                *third[which]
                    .entry(shape_of(resolve(expression).expect("an expression")))
                    .or_default() += 1;
                // Slot 3: shapes only. No decoder accepts it and none is tried.
                *fourth[which]
                    .entry(shape_of(
                        resolve(word_at(bytes, record + 8 + 8 * 3)).expect("slot 3 is a pointer"),
                    ))
                    .or_default() += 1;
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(counts, [0, 0], "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(
        counts,
        [54, 46],
        "the two disjoint record populations `d8906952` established"
    );
    assert_eq!(
        names_decoded, 200,
        "two names per record, through `decode_name`"
    );
    assert_eq!(
        exprs_decoded, 100,
        "one expression per record, through `decode_expr`"
    );

    // Shared layout.
    assert_eq!(
        first[0]
            .iter()
            .chain(first[1].iter())
            .map(|(k, v)| (k.clone(), *v))
            .collect::<Vec<_>>(),
        vec![
            ("tag 2 arity 2".to_owned(), 54),
            ("tag 2 arity 2".to_owned(), 46)
        ],
        "slot 0 is the numbered name link in all 100"
    );

    // Distributions, reported side by side and not characterised.
    assert_eq!(
        second[0].clone().into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 2".to_owned(), 2),
            ("tag 2 arity 2".to_owned(), 52)
        ],
        "the seeds' slot 1 admits both name constructors"
    );
    assert_eq!(
        second[1].clone().into_iter().collect::<Vec<_>>(),
        vec![("tag 2 arity 2".to_owned(), 46)],
        "the interior's admits one"
    );
    assert_eq!(
        third[0].clone().into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 1".to_owned(), 4),
            ("tag 4 arity 2".to_owned(), 9),
            ("tag 5 arity 2".to_owned(), 12),
            ("tag 7 arity 3".to_owned(), 29),
        ],
        "the seeds' expressions"
    );
    assert_eq!(
        third[1].clone().into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 1".to_owned(), 4),
            ("tag 4 arity 2".to_owned(), 10),
            ("tag 5 arity 2".to_owned(), 27),
            ("tag 7 arity 3".to_owned(), 5),
        ],
        "and the interior's, over the same four shapes"
    );
    assert_eq!(
        fourth[0].clone().into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 2 arity 3".to_owned(), 34),
            ("tag 3 arity 3".to_owned(), 9),
            ("tag 4 arity 2".to_owned(), 11),
        ],
        "slot 3 is none of the types this file can decode: three shapes, pinned \
         as shapes and left there rather than guessed at"
    );
    assert_eq!(
        fourth[1].clone().into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 2 arity 3".to_owned(), 11),
            ("tag 3 arity 3".to_owned(), 9),
            ("tag 4 arity 2".to_owned(), 26),
        ],
        "the same three shapes on the interior side"
    );
}

/// Slot 3's three shapes, structurally - and one field that is sometimes a
/// pointer and sometimes not.
///
/// `2d251138` already pins what WAVE 186 asks for: the three shapes and their
/// seed and interior counts, 34/9/11 against 11/9/26. This is WAVE 187's
/// stronger question - tags, arities, pointer-or-scalar, and counts, for both
/// populations kept apart - and it does not decode anything, because no
/// production decoder in this crate accepts these and inventing one would be
/// the guess `2d251138` declined to make.
///
/// ONE FIELD IS MIXED, AND NOTHING ELSE IN THIS FILE HAS BEEN. Every field
/// characterised across fourteen waves has been uniformly a pointer or
/// uniformly a scalar - the 71's 142 pointers, the 17's 34 scalars, the head
/// records' 345 pointers, the 11's boxed heads. Slot 1 of the `(3, 3)` shape is
/// neither: among the seeds it is boxed four times and a name link twice, and
/// among the interior boxed five times and a name link four times.
///
/// That matters for how this file reads its own evidence. A uniform
/// pointer/scalar split has been treated here as evidence the walk is on real
/// object boundaries - twice, at `84951450` and `a7a7a9e0`. A mixed field is
/// not counter-evidence, because a constructor with both nullary and
/// non-nullary cases produces exactly this; but it does mean uniformity is a
/// property of the FIELDS measured so far and not a law, and a future cell must
/// not read a mixture as a walker fault.
///
/// The rest is layout. The `(2, 3)` shape holds a name link, a boxed value, and
/// a numbered name link. The `(3, 3)` shape holds a name link, the mixed field,
/// and an array. The `(4, 2)` shape holds a numbered name link and an array,
/// with no scalars at all.
///
/// No size is asserted, nothing is decoded, and no schema, type or extension is
/// named.
#[test]
fn the_slot_three_shapes_have_a_mixed_field() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    // Keyed "population/shape" and "population/shape/slot" so the two
    // populations can never be folded together by accident.
    let mut totals: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();
    let mut pointer_scalar: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();
    let mut slots: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let is_pair = |off: usize| at.get(&off).map(|o| (o.tag, o.other)) == Some((0, 2));

        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(record) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&record).map(|h| (h.tag, h.other)) != Some((0, 5)) {
                continue;
            }
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && is_pair(target)
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && is_pair(target)
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        for population in ["seed", "interior"] {
            let mut records: BTreeSet<usize> = BTreeSet::new();
            for node in &all {
                let seed = seeds.contains(node);
                if (population == "seed") == seed
                    && let Some(record) = resolve(word_at(bytes, node + 8))
                {
                    records.insert(record);
                }
            }
            // Slot 3 targets, counted by reference and deduplicated.
            let mut references: Vec<usize> = Vec::new();
            for record in &records {
                references.push(
                    resolve(word_at(bytes, record + 8 + 8 * 3)).expect("slot 3 is a pointer"),
                );
            }
            let mut by_shape: std::collections::BTreeMap<(u8, u8), Vec<usize>> =
                std::collections::BTreeMap::new();
            for &target in &references {
                let object = at.get(&target).expect("a walked object");
                by_shape
                    .entry((object.tag, object.other))
                    .or_default()
                    .push(target);
            }
            for ((tag, arity), group) in by_shape {
                let key = format!("{population}/tag {tag} arity {arity}");
                let unique: BTreeSet<usize> = group.iter().copied().collect();
                let entry = totals.entry(key.clone()).or_default();
                entry.0 += group.len();
                entry.1 += unique.len();
                for object in unique {
                    for slot in 0..usize::from(arity) {
                        let word = word_at(bytes, object + 8 + 8 * slot);
                        let counts = pointer_scalar.entry(key.clone()).or_default();
                        let described = match resolve(word) {
                            Some(child) => {
                                counts.0 += 1;
                                let child = at.get(&child).expect("resolved above");
                                format!("tag {} arity {}", child.tag, child.other)
                            }
                            None => {
                                counts.1 += 1;
                                format!("boxed {}", word >> 1)
                            }
                        };
                        *slots
                            .entry(format!("{key}/slot {slot} {described}"))
                            .or_default() += 1;
                    }
                }
            }
        }
    }

    if !prelude_loaded {
        assert!(
            totals.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    // References and distinct objects, per population per shape.
    assert_eq!(
        totals.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/tag 2 arity 3".to_owned(), (11, 10)),
            ("interior/tag 3 arity 3".to_owned(), (9, 9)),
            ("interior/tag 4 arity 2".to_owned(), (26, 24)),
            ("seed/tag 2 arity 3".to_owned(), (34, 33)),
            ("seed/tag 3 arity 3".to_owned(), (9, 6)),
            ("seed/tag 4 arity 2".to_owned(), (11, 11)),
        ],
        "the three shapes by reference and by object, the two populations apart"
    );

    // Pointer-or-scalar, over the distinct objects.
    assert_eq!(
        pointer_scalar.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/tag 2 arity 3".to_owned(), (20, 10)),
            ("interior/tag 3 arity 3".to_owned(), (22, 5)),
            ("interior/tag 4 arity 2".to_owned(), (48, 0)),
            ("seed/tag 2 arity 3".to_owned(), (66, 33)),
            ("seed/tag 3 arity 3".to_owned(), (14, 4)),
            ("seed/tag 4 arity 2".to_owned(), (22, 0)),
        ],
        "pointers and scalars per shape. The `tag 4` shape has no scalars at \
         all; the other two do"
    );

    // The layout, and the mixed field.
    assert_eq!(
        slots.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/tag 2 arity 3/slot 0 tag 1 arity 2".to_owned(), 10),
            ("interior/tag 2 arity 3/slot 1 boxed 0".to_owned(), 5),
            ("interior/tag 2 arity 3/slot 1 boxed 1".to_owned(), 2),
            ("interior/tag 2 arity 3/slot 1 boxed 2".to_owned(), 1),
            ("interior/tag 2 arity 3/slot 1 boxed 3".to_owned(), 1),
            ("interior/tag 2 arity 3/slot 1 boxed 4".to_owned(), 1),
            ("interior/tag 2 arity 3/slot 2 tag 2 arity 2".to_owned(), 10),
            ("interior/tag 3 arity 3/slot 0 tag 1 arity 2".to_owned(), 9),
            ("interior/tag 3 arity 3/slot 1 boxed 0".to_owned(), 5),
            ("interior/tag 3 arity 3/slot 1 tag 1 arity 2".to_owned(), 4),
            (
                "interior/tag 3 arity 3/slot 2 tag 246 arity 0".to_owned(),
                9
            ),
            ("interior/tag 4 arity 2/slot 0 tag 2 arity 2".to_owned(), 24),
            (
                "interior/tag 4 arity 2/slot 1 tag 246 arity 0".to_owned(),
                24
            ),
            ("seed/tag 2 arity 3/slot 0 tag 1 arity 2".to_owned(), 33),
            ("seed/tag 2 arity 3/slot 1 boxed 0".to_owned(), 29),
            ("seed/tag 2 arity 3/slot 1 boxed 1".to_owned(), 2),
            ("seed/tag 2 arity 3/slot 1 boxed 2".to_owned(), 2),
            ("seed/tag 2 arity 3/slot 2 tag 2 arity 2".to_owned(), 33),
            ("seed/tag 3 arity 3/slot 0 tag 1 arity 2".to_owned(), 6),
            ("seed/tag 3 arity 3/slot 1 boxed 0".to_owned(), 4),
            ("seed/tag 3 arity 3/slot 1 tag 1 arity 2".to_owned(), 2),
            ("seed/tag 3 arity 3/slot 2 tag 246 arity 0".to_owned(), 6),
            ("seed/tag 4 arity 2/slot 0 tag 2 arity 2".to_owned(), 11),
            ("seed/tag 4 arity 2/slot 1 tag 246 arity 0".to_owned(), 11),
        ],
        "every slot of every shape. Slot 1 of the `tag 3` shape is BOTH boxed \
         and a pointer in both populations - the first field in this file that \
         is not uniformly one or the other, so uniformity is a property of the \
         fields measured so far and not a law"
    );
}

/// The arrays inside slot 3 - including an EMPTY one, and a second non-uniform
/// field.
///
/// `6a4dba87` found arrays at slot 2 of the `tag 3` shape and slot 1 of the
/// `tag 4` shape and measured neither. There are four groups, not two: the
/// order names nine and twenty-four, which are the interior's, and the seeds
/// contribute six and eleven.
///
/// AN EMPTY ARRAY EXISTS, one in each `tag 3` group, and it is the reason this
/// cell pins array counts and element counts SEPARATELY rather than reporting a
/// single population. A length-zero array contributes nothing to an element
/// histogram, so "the elements of these arrays" has a smaller denominator than
/// "these arrays" - and a cell that only counted elements would describe a set
/// that silently excludes one of its members. That is the sampler defect this
/// file has already hit once, at `c48c0813`, arriving now as an empty container
/// rather than an unclassifiable object.
///
/// ONE ELEMENT IS BOXED where all the others are pointers - the interior's
/// `tag 3` arrays hold 30 pointers and one boxed zero. That is the SECOND
/// non-uniform field found here, after slot 1 of the `tag 3` shape at
/// `6a4dba87`, and it confirms what that cell said: uniformity is a property of
/// the fields measured so far, not a law of the data.
///
/// The elements are two one-field shapes across all four groups. Nothing is
/// decoded: no production decoder in this crate accepts them, and the order
/// forbids inventing one.
///
/// Both populations are kept apart throughout, and each group is counted by
/// reference and by object, since sharing differs between them - the seeds'
/// eleven `tag 4` arrays are ten objects, the interior's twenty-four are
/// twenty-four.
///
/// No size is asserted. No schema, type or extension is named.
#[test]
fn the_slot_three_arrays_include_an_empty_one() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut arrays: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();
    let mut lengths: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut elements: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();
    let mut element_shapes: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let is_pair = |off: usize| at.get(&off).map(|o| (o.tag, o.other)) == Some((0, 2));

        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(record) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&record).map(|h| (h.tag, h.other)) != Some((0, 5)) {
                continue;
            }
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && is_pair(target)
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && is_pair(target)
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        for population in ["seed", "interior"] {
            let mut carriers: BTreeSet<usize> = BTreeSet::new();
            for node in &all {
                if (population == "seed") == seeds.contains(node)
                    && let Some(record) = resolve(word_at(bytes, node + 8))
                    && let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 3))
                {
                    carriers.insert(target);
                }
            }
            for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                let key = format!("{population}/tag {tag} slot {slot}");
                let mut references = 0usize;
                let mut distinct: BTreeSet<usize> = BTreeSet::new();
                for &carrier in &carriers {
                    if at.get(&carrier).map(|o| (o.tag, o.other)) != Some((tag, arity)) {
                        continue;
                    }
                    references += 1;
                    if let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot)) {
                        distinct.insert(array);
                    }
                }
                let entry = arrays.entry(key.clone()).or_default();
                entry.0 += references;
                entry.1 += distinct.len();

                for array in distinct {
                    let length = word_at(bytes, array + 8);
                    *lengths.entry(format!("{key}/length {length}")).or_default() += 1;
                    for i in 0..length {
                        let word = word_at(bytes, array + 24 + 8 * i as usize);
                        let counts = elements.entry(key.clone()).or_default();
                        let described = match resolve(word) {
                            Some(child) => {
                                counts.0 += 1;
                                let child = at.get(&child).expect("resolved above");
                                format!("tag {} arity {}", child.tag, child.other)
                            }
                            None => {
                                counts.1 += 1;
                                format!("boxed {}", word >> 1)
                            }
                        };
                        *element_shapes
                            .entry(format!("{key}/{described}"))
                            .or_default() += 1;
                    }
                }
            }
        }
    }

    if !prelude_loaded {
        assert!(
            arrays.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    assert_eq!(
        arrays.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/tag 3 slot 2".to_owned(), (9, 9)),
            ("interior/tag 4 slot 1".to_owned(), (24, 24)),
            ("seed/tag 3 slot 2".to_owned(), (6, 4)),
            ("seed/tag 4 slot 1".to_owned(), (11, 10)),
        ],
        "four groups, not two: the order names the interior's nine and \
         twenty-four, and the seeds contribute six and eleven. By reference and \
         by object, since sharing differs between them"
    );

    // Lengths, including the empty ones.
    assert_eq!(
        lengths.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/tag 3 slot 2/length 0".to_owned(), 1),
            ("interior/tag 3 slot 2/length 2".to_owned(), 2),
            ("interior/tag 3 slot 2/length 3".to_owned(), 1),
            ("interior/tag 3 slot 2/length 4".to_owned(), 2),
            ("interior/tag 3 slot 2/length 5".to_owned(), 2),
            ("interior/tag 3 slot 2/length 6".to_owned(), 1),
            ("interior/tag 4 slot 1/length 1".to_owned(), 5),
            ("interior/tag 4 slot 1/length 2".to_owned(), 14),
            ("interior/tag 4 slot 1/length 3".to_owned(), 4),
            ("interior/tag 4 slot 1/length 4".to_owned(), 1),
            ("seed/tag 3 slot 2/length 0".to_owned(), 1),
            ("seed/tag 3 slot 2/length 2".to_owned(), 3),
            ("seed/tag 4 slot 1/length 1".to_owned(), 4),
            ("seed/tag 4 slot 1/length 2".to_owned(), 6),
        ],
        "an EMPTY array exists in each `tag 3` group, so `these arrays` and \
         `the elements of these arrays` have different denominators"
    );

    // Elements: pointers and scalars, separately from the array counts.
    assert_eq!(
        elements.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/tag 3 slot 2".to_owned(), (30, 1)),
            ("interior/tag 4 slot 1".to_owned(), (49, 0)),
            ("seed/tag 3 slot 2".to_owned(), (6, 0)),
            ("seed/tag 4 slot 1".to_owned(), (16, 0)),
        ],
        "ONE element is boxed where all the others are pointers - the second \
         non-uniform field found here, after slot 1 of the `tag 3` shape"
    );
    assert_eq!(
        element_shapes.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/tag 3 slot 2/boxed 0".to_owned(), 1),
            ("interior/tag 3 slot 2/tag 1 arity 1".to_owned(), 20),
            ("interior/tag 3 slot 2/tag 2 arity 1".to_owned(), 10),
            ("interior/tag 4 slot 1/tag 1 arity 1".to_owned(), 35),
            ("interior/tag 4 slot 1/tag 2 arity 1".to_owned(), 14),
            ("seed/tag 3 slot 2/tag 1 arity 1".to_owned(), 6),
            ("seed/tag 4 slot 1/tag 1 arity 1".to_owned(), 15),
            ("seed/tag 4 slot 1/tag 2 arity 1".to_owned(), 1),
        ],
        "the elements are two one-field shapes across all four groups; nothing \
         is decoded, because no decoder here accepts them"
    );
}

/// The one-field elements: one shape wraps a name, the other wraps the first.
///
/// `4277a152` counted 102 elements across the four array groups and left them
/// unopened. One of the 102 is boxed, so 101 are objects, and this reads those.
///
/// A COUNTING TRAP SITS IN FRONT OF THIS MEASUREMENT AND I WALKED INTO IT
/// BEFORE CATCHING IT. Iterating the arrays by CARRIER gives 104 elements,
/// because a shared array is visited once per carrier that points at it.
/// `4277a152` counted over DISTINCT arrays. The two numbers describe different
/// things and only one of them reconciles with what is already pinned, so this
/// cell deduplicates arrays first and asserts the reconciliation - 22 from the
/// seeds and 79 from the interior against the 6, 16, 30 and 49 pointer elements
/// `4277a152` pins.
///
/// That is the fifth reference-versus-object confusion in this structure, and
/// the first to appear inside the measuring code rather than in the data. It is
/// caught here only because a total disagreed with a landed pin; without that
/// cross-check it would have produced a clean, wrong histogram.
///
/// THE `tag 1` SHAPE WRAPS A NAME, uniformly - a numbered name link in all 35
/// distinct objects across both populations - and every one goes to the
/// production `decode_name` rather than being matched by shape.
///
/// THE `tag 2` SHAPE WRAPS THE `tag 1` SHAPE, in 11 of its 16 distinct objects,
/// and something else in the other 5. So the two element shapes interlock, the
/// same way the two slot-4 shapes did at `241893a7`. This cell says the edges
/// exist and how many; it does not say what they build, because `3575962c`
/// established that counting edges cannot answer that.
///
/// The seeds' entire `tag 2` population is ONE object, which is why its inner
/// histogram is a single entry and no proportion is drawn from it.
///
/// No size is asserted. No schema, type or extension is named.
#[test]
fn the_one_field_elements_wrap_names() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut totals: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();
    let mut by_shape: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();
    let mut inner: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut names_decoded = 0usize;

    for (module, bytes) in &modules {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let is_pair = |off: usize| at.get(&off).map(|o| (o.tag, o.other)) == Some((0, 2));
        let shape_of = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(record) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&record).map(|h| (h.tag, h.other)) != Some((0, 5)) {
                continue;
            }
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && is_pair(target)
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && is_pair(target)
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        for population in ["seed", "interior"] {
            let mut carriers: BTreeSet<usize> = BTreeSet::new();
            for node in &all {
                if (population == "seed") == seeds.contains(node)
                    && let Some(record) = resolve(word_at(bytes, node + 8))
                    && let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 3))
                {
                    carriers.insert(target);
                }
            }
            // Deduplicate the ARRAYS before reading elements, or a shared array
            // is counted once per carrier and the total stops reconciling.
            let mut arrays: BTreeSet<usize> = BTreeSet::new();
            for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                for &carrier in &carriers {
                    if at.get(&carrier).map(|o| (o.tag, o.other)) == Some((tag, arity))
                        && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                    {
                        arrays.insert(array);
                    }
                }
            }

            let mut references = 0usize;
            let mut distinct: BTreeSet<usize> = BTreeSet::new();
            let mut per_shape: std::collections::BTreeMap<String, BTreeSet<usize>> =
                std::collections::BTreeMap::new();
            let mut shape_references: std::collections::BTreeMap<String, usize> =
                std::collections::BTreeMap::new();
            for array in arrays {
                for i in 0..word_at(bytes, array + 8) {
                    if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) {
                        references += 1;
                        distinct.insert(element);
                        let shape = shape_of(element);
                        *shape_references.entry(shape.clone()).or_default() += 1;
                        per_shape.entry(shape).or_default().insert(element);
                    }
                }
            }
            let entry = totals.entry(population.to_owned()).or_default();
            entry.0 += references;
            entry.1 += distinct.len();

            for (shape, group) in per_shape {
                let key = format!("{population}/{shape}");
                let counts = by_shape.entry(key.clone()).or_default();
                counts.0 += shape_references.get(&shape).copied().unwrap_or(0);
                counts.1 += group.len();
                for element in group {
                    let field = word_at(bytes, element + 8);
                    let target = resolve(field).expect("the single field is a pointer");
                    *inner
                        .entry(format!("{key}/{}", shape_of(target)))
                        .or_default() += 1;
                    // Only the `tag 1` shape claims to hold a name; only it is
                    // handed to the decoder.
                    if shape == "tag 1 arity 1" {
                        DeclDecoder::new(&view, WalkBudget::default())
                            .decode_name(field)
                            .unwrap_or_else(|e| panic!("{module}: must be a Name: {e}"));
                        names_decoded += 1;
                    }
                }
            }
        }
    }

    if !prelude_loaded {
        assert!(
            totals.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    // The reconciliation: 22 + 79 is `4277a152`'s 6 + 16 + 30 + 49.
    assert_eq!(
        totals.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior".to_owned(), (79, 36)),
            ("seed".to_owned(), (22, 15)),
        ],
        "element references and distinct objects. 22 + 79 = 101, which is the \
         pointer elements `4277a152` pins as 6, 16, 30 and 49 - iterating \
         arrays by CARRIER instead gives 104, because a shared array is visited \
         once per carrier"
    );

    assert_eq!(
        by_shape.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/tag 1 arity 1".to_owned(), (55, 21)),
            ("interior/tag 2 arity 1".to_owned(), (24, 15)),
            ("seed/tag 1 arity 1".to_owned(), (21, 14)),
            ("seed/tag 2 arity 1".to_owned(), (1, 1)),
        ],
        "the two shapes per population. The seeds' entire `tag 2` population is \
         ONE object"
    );

    assert_eq!(
        inner.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/tag 1 arity 1/tag 2 arity 2".to_owned(), 21),
            ("interior/tag 2 arity 1/tag 1 arity 1".to_owned(), 10),
            ("interior/tag 2 arity 1/tag 4 arity 2".to_owned(), 5),
            ("seed/tag 1 arity 1/tag 2 arity 2".to_owned(), 14),
            ("seed/tag 2 arity 1/tag 1 arity 1".to_owned(), 1),
        ],
        "the `tag 1` shape wraps a numbered name link uniformly; the `tag 2` \
         shape wraps the `tag 1` shape in 11 of its 16 distinct objects, so the \
         two interlock - how deep is a traversal's question, not a count's"
    );
    assert_eq!(
        names_decoded, 35,
        "every `tag 1` element's field accepted by the production `decode_name`"
    );
}

/// The `tag 4` objects the elements wrap - the same tag and arity as the slot-3
/// ones, and NOT the same thing.
///
/// `fffc0e71` found that 5 of the interior's 16 `tag 2` elements wrap something
/// other than a `tag 1`, and that something is `tag 4 arity 2`. So is one of
/// the three shapes at slot 3, pinned at `6a4dba87`. They are not the same
/// type:
///
///   slot 3's `tag 4`     a numbered name link, and an ARRAY
///   these                a name link, and a field that is boxed or a pointer
///
/// A tag and an arity do not identify a type. That is the finding this whole
/// investigation opened with - `daaaabe2`, where `(1, 2)` at 24 bytes turned
/// out to be `List.cons` and several other things - and here it is again, four
/// levels deeper, between two populations this file has been describing
/// separately for three waves without noticing they collide.
///
/// NOTHING IS DECODED HERE, and the collision is exactly why. The `(4, 2)`
/// shape has been identified once in this file, at `aec3efd1`, as `Expr.const`.
/// These match that shape and one of them even carries what a `List Level`
/// would look like. Handing them to `decode_expr` would very likely succeed and
/// would prove nothing about which of two types sharing a shape this is - it
/// would be the shape argument again, wearing a decoder.
///
/// THE SEEDS HAVE NONE. Zero, not a small number: the seeds' entire `tag 2`
/// population is one object and it wraps a `tag 1`. That is asserted as a count
/// of zero, the discipline `d8906952` settled for categorical absences.
///
/// THIS CELL WAS RED AT w155 AND THE CAUSE WAS THE SAME CONFUSION IT REPORTS.
/// The comparison below counts DISTINCT slot-3 carriers, because the walk
/// gathers them into a set; the first version asserted 26, which is the
/// REFERENCE count `6a4dba87` pins next to the distinct count of 24. Both
/// numbers were already in this file, one line apart, and I took the wrong one.
/// The seeds are 11 either way, so half the assertion matched and the failure
/// looked like a data disagreement rather than a units error.
///
/// The type-distinction claim above is untouched by that: it rests on WHAT the
/// two populations' fields are, not on how many of them there are.
///
/// Slot 1 is boxed four times and a pointer once - the THIRD non-uniform field
/// found here, after `6a4dba87` and `4277a152`. Five objects support no
/// proportion, so the two counts are pinned and nothing is said about which
/// case is typical.
#[test]
fn the_wrapped_tag_four_objects_are_not_the_slot_three_ones() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut totals: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();
    let mut fields: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut slot_three_fields: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let is_pair = |off: usize| at.get(&off).map(|o| (o.tag, o.other)) == Some((0, 2));
        let shape_of = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(record) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&record).map(|h| (h.tag, h.other)) != Some((0, 5)) {
                continue;
            }
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && is_pair(target)
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && is_pair(target)
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        for population in ["seed", "interior"] {
            let mut carriers: BTreeSet<usize> = BTreeSet::new();
            for node in &all {
                if (population == "seed") == seeds.contains(node)
                    && let Some(record) = resolve(word_at(bytes, node + 8))
                    && let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 3))
                {
                    carriers.insert(target);
                }
            }
            // Arrays deduplicated first, the `fffc0e71` reconciliation.
            let mut arrays: BTreeSet<usize> = BTreeSet::new();
            for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                for &carrier in &carriers {
                    if at.get(&carrier).map(|o| (o.tag, o.other)) == Some((tag, arity))
                        && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                    {
                        arrays.insert(array);
                    }
                }
                // For the comparison below: what slot 3's own `tag 4` holds.
                if tag == 4 {
                    for &carrier in &carriers {
                        if at.get(&carrier).map(|o| (o.tag, o.other)) != Some((4, 2)) {
                            continue;
                        }
                        for field in 0..2usize {
                            let word = word_at(bytes, carrier + 8 + 8 * field);
                            let described = resolve(word)
                                .map_or_else(|| format!("boxed {}", word >> 1), &shape_of);
                            *slot_three_fields
                                .entry(format!("{population}/slot {field} {described}"))
                                .or_default() += 1;
                        }
                    }
                }
            }

            let mut references = 0usize;
            let mut distinct: BTreeSet<usize> = BTreeSet::new();
            for array in arrays {
                for i in 0..word_at(bytes, array + 8) {
                    let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) else {
                        continue;
                    };
                    if at.get(&element).map(|o| (o.tag, o.other)) != Some((2, 1)) {
                        continue;
                    }
                    if let Some(target) = resolve(word_at(bytes, element + 8))
                        && at.get(&target).map(|o| (o.tag, o.other)) == Some((4, 2))
                    {
                        references += 1;
                        distinct.insert(target);
                    }
                }
            }
            let entry = totals.entry(population.to_owned()).or_default();
            entry.0 += references;
            entry.1 += distinct.len();
            for target in distinct {
                for field in 0..2usize {
                    let word = word_at(bytes, target + 8 + 8 * field);
                    let described =
                        resolve(word).map_or_else(|| format!("boxed {}", word >> 1), &shape_of);
                    *fields
                        .entry(format!("{population}/slot {field} {described}"))
                        .or_default() += 1;
                }
            }
        }
    }

    if !prelude_loaded {
        assert!(
            totals.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    assert_eq!(
        totals.into_iter().collect::<Vec<_>>(),
        vec![("interior".to_owned(), (6, 5)), ("seed".to_owned(), (0, 0)),],
        "the seeds have NONE - zero, not a small number, because their entire \
         `tag 2` population is one object and it wraps a `tag 1`"
    );

    assert_eq!(
        fields.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/slot 0 tag 1 arity 2".to_owned(), 5),
            ("interior/slot 1 boxed 0".to_owned(), 4),
            ("interior/slot 1 tag 1 arity 2".to_owned(), 1),
        ],
        "a name link, and a field that is boxed four times and a pointer once - \
         the THIRD non-uniform field found here. Five objects support no \
         proportion, so both counts are pinned and neither is called typical"
    );

    // The collision: same tag, same arity, different fields.
    assert_eq!(
        slot_three_fields.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/slot 0 tag 2 arity 2".to_owned(), 24),
            ("interior/slot 1 tag 246 arity 0".to_owned(), 24),
            ("seed/slot 0 tag 2 arity 2".to_owned(), 11),
            ("seed/slot 1 tag 246 arity 0".to_owned(), 11),
        ],
        "slot 3's `tag 4` objects hold a NUMBERED name link and an ARRAY. The \
         wrapped ones hold a name link and a boxed-or-pointer field. Same tag, \
         same arity, different type - which is `daaaabe2`'s finding four levels \
         deeper, and why nothing here is handed to a decoder. \
         \
         These counts are over DISTINCT carriers, because the walk above \
         collects them into a set: 24 for the interior, not the 26 REFERENCES \
         `6a4dba87` pins beside them. That cell's own per-slot histogram \
         already says 24; this cell first asserted 26 and was red until w155. \
         The seeds are 11 either way, which is why they matched and hid it"
    );
}

/// The nesting TERMINATES - and "interlock" was the wrong word.
///
/// The other option this wave offers is already pinned: `7e65ed09` asserts the
/// five wrapped objects' second field as `boxed 0` four times and a pointer
/// once, which is boxed-versus-pointer with counts. So this takes the
/// traversal.
///
/// `fffc0e71` said the two element shapes "interlock, the same way the two
/// slot-4 shapes did at `241893a7`". That word implies mutual reference and the
/// traversal does not support it. `tag 2` wraps `tag 1`; `tag 1` points at a
/// numbered name link and NEVER at a `tag 1` or a `tag 2`, in all 46 of them.
/// The nesting is one-way and two deep, and it stops. Same shape of error as
/// `3575962c`: a relation observed in one direction, described as if it went
/// both ways, without the walk that would have said so.
///
/// AND THE POPULATION IS BIGGER THAN `fffc0e71` COUNTED. The `tag 1` objects
/// wrapped by `tag 2` are DISJOINT from the `tag 1` objects that appear as
/// array elements - zero overlap in both populations - so there are 15 and 31
/// of them, not the 14 and 21 that cell pinned. Its 35 was the array elements,
/// which is what it measured and said; the 11 wrapped ones are a separate set
/// that no cell had reached.
///
/// The decode is reported for what it is, per `7e65ed09`. All 46 fields are
/// accepted by the production `decode_name`, which establishes they are
/// well-formed names. It does not establish they are the same TYPE as anything
/// else so decoded, because a passing decode is not an identification where
/// shapes collide - and that cell found `(4, 2)` doing exactly that.
#[test]
fn the_element_nesting_terminates() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut populations: std::collections::BTreeMap<String, (usize, usize, usize)> =
        std::collections::BTreeMap::new();
    let mut points_at: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut names_decoded = 0usize;

    for (module, bytes) in &modules {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let is_pair = |off: usize| at.get(&off).map(|o| (o.tag, o.other)) == Some((0, 2));
        let shape_of = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let tail = resolve(word_at(bytes, object.off + 16));
            if tail.and_then(|t| at.get(&t)).map(|t| (t.tag, t.other)) != Some((0, 2)) {
                continue;
            }
            let Some(record) = resolve(word_at(bytes, object.off + 8)) else {
                continue;
            };
            if at.get(&record).map(|h| (h.tag, h.other)) != Some((0, 5)) {
                continue;
            }
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && is_pair(target)
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && is_pair(target)
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        for population in ["seed", "interior"] {
            let mut carriers: BTreeSet<usize> = BTreeSet::new();
            for node in &all {
                if (population == "seed") == seeds.contains(node)
                    && let Some(record) = resolve(word_at(bytes, node + 8))
                    && let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 3))
                {
                    carriers.insert(target);
                }
            }
            let mut arrays: BTreeSet<usize> = BTreeSet::new();
            for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                for &carrier in &carriers {
                    if at.get(&carrier).map(|o| (o.tag, o.other)) == Some((tag, arity))
                        && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                    {
                        arrays.insert(array);
                    }
                }
            }

            let mut as_elements: BTreeSet<usize> = BTreeSet::new();
            let mut wrappers: BTreeSet<usize> = BTreeSet::new();
            for array in arrays {
                for i in 0..word_at(bytes, array + 8) {
                    let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) else {
                        continue;
                    };
                    match at.get(&element).map(|o| (o.tag, o.other)) {
                        Some((1, 1)) => {
                            as_elements.insert(element);
                        }
                        Some((2, 1)) => {
                            wrappers.insert(element);
                        }
                        _ => {}
                    }
                }
            }
            // The `tag 1` objects reached only through a `tag 2`.
            let mut wrapped: BTreeSet<usize> = BTreeSet::new();
            for wrapper in wrappers {
                if let Some(target) = resolve(word_at(bytes, wrapper + 8))
                    && at.get(&target).map(|o| (o.tag, o.other)) == Some((1, 1))
                {
                    wrapped.insert(target);
                }
            }
            let overlap = as_elements.intersection(&wrapped).count();
            let entry = populations.entry(population.to_owned()).or_default();
            entry.0 += as_elements.len();
            entry.1 += wrapped.len();
            entry.2 += overlap;

            // Where every `tag 1` points, from both sources.
            for object in as_elements.union(&wrapped) {
                let field = word_at(bytes, object + 8);
                let target = resolve(field).expect("the single field is a pointer");
                *points_at.entry(shape_of(target)).or_default() += 1;
                DeclDecoder::new(&view, WalkBudget::default())
                    .decode_name(field)
                    .unwrap_or_else(|e| panic!("{module}: must be a Name: {e}"));
                names_decoded += 1;
            }
        }
    }

    if !prelude_loaded {
        assert!(
            populations.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    assert_eq!(
        populations.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior".to_owned(), (21, 10, 0)),
            ("seed".to_owned(), (14, 1, 0)),
        ],
        "`tag 1` objects as array elements, as wrapped by a `tag 2`, and the \
         overlap. The overlap is ZERO in both, so the wrapped ones are a \
         separate set: 15 and 31 objects, not the 14 and 21 `fffc0e71` pinned \
         for the array elements it measured"
    );

    // The termination.
    assert_eq!(
        points_at.into_iter().collect::<Vec<_>>(),
        vec![("tag 2 arity 2".to_owned(), 46)],
        "every `tag 1` points at a numbered name link and NEVER at a `tag 1` or \
         a `tag 2`. The nesting is one-way and two deep and it stops - so \
         `fffc0e71`'s \"interlock\", which implies mutual reference, was wrong"
    );
    assert_eq!(
        names_decoded, 46,
        "all 46 accepted by the production `decode_name`, which establishes \
         they are well-formed names and NOT that they are the same type as \
         anything else so decoded - per `7e65ed09`, a passing decode is not an \
         identification where shapes collide"
    );
}

/// The reconciliation ledger - every stage with its UNIT, and the arithmetic
/// between them.
///
/// The five wrapped objects' second field is already pinned at `7e65ed09` as
/// `boxed 0` four times and a pointer once, with the seeds at zero; this wave
/// offers it a third time and it needs no second cell. What this file does need
/// is the mechanism I named after `5313a5c9`: that red was a number drifting
/// from a total already pinned twenty lines away, and nothing tied the two
/// together. This is the tie.
///
/// It walks the whole structure once and asserts the identities BETWEEN stages,
/// which no individual cell can: 71 + 11 + 17 = 99, 57 + 8 + 4 = 69,
/// 56 + 46 = 102, 54 + 46 = 100, 101 + 1 = 102. A number that drifts in any one
/// cell now contradicts an identity here rather than passing quietly.
///
/// IT ALREADY FOUND TWO THINGS, and both are units rather than errors.
///
/// The slot-2 arrays are 69 by REFERENCE and 51 by object, carrying 157
/// elements counted per reference and 123 per distinct array - and 111 distinct
/// elements either way. `3b510e62` and `a4de2083` are both right and are
/// counting different things.
///
/// AND THE TWO POPULATIONS ARE NOT DISJOINT BELOW THE RECORDS. `d8906952`
/// proved the four-field records disjoint - 54 and 46, sharing none - and I
/// have written "both populations kept apart" in five commits since as though
/// that separation continued downward. It does not. They share 5 arrays, 12
/// `tag 1` elements, 1 `tag 2` element and 1 wrapped object. So `2d20e69f`'s 46
/// is 46 per-population MEMBERSHIPS over 33 distinct objects, which is what its
/// arithmetic computes and not what its prose implies.
///
/// Disjointness proved at one depth is not disjointness, and nothing in this
/// file said where it stopped.
#[test]
fn the_measured_chain_reconciles() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut ledger: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let mut count = |key: &str, by: usize| *ledger.entry(key.to_owned()).or_default() += by;

        // Stage 1: the third shape, split by what its tail is.
        let (mut tag0, mut tag4, mut boxed) = (Vec::new(), 0usize, 0usize);
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            if second & 1 == 1 {
                if second >> 1 != 0 {
                    boxed += 1;
                }
                continue;
            }
            match resolve(second).and_then(shape) {
                Some((1, 2)) | None => {}
                Some((0, 2)) => tag0.push(object.off),
                Some((4, 2)) => tag4 += 1,
                Some(_) => {}
            }
        }
        count("1 third/tag0-tailed", tag0.len());
        count("1 third/tag4-tailed", tag4);
        count("1 third/boxed-tailed", boxed);

        // Stage 2: head records, by reference and by object.
        let heads: Vec<usize> = tag0
            .iter()
            .filter_map(|&node| resolve(word_at(bytes, node + 8)))
            .filter(|&head| shape(head) == Some((0, 5)))
            .collect();
        let records: BTreeSet<usize> = heads.iter().copied().collect();
        count("2 heads/references", heads.len());
        count("2 heads/objects", records.len());

        // Stage 3: slot-2 arrays, in three units.
        let mut array_references = 0usize;
        let mut arrays: BTreeSet<usize> = BTreeSet::new();
        let mut per_reference = 0usize;
        for &record in &records {
            if let Some(array) = resolve(word_at(bytes, record + 8 + 8 * 2)) {
                array_references += 1;
                arrays.insert(array);
                per_reference += word_at(bytes, array + 8) as usize;
            }
        }
        let mut per_object = 0usize;
        let mut elements: BTreeSet<usize> = BTreeSet::new();
        for &array in &arrays {
            for i in 0..word_at(bytes, array + 8) {
                per_object += 1;
                if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) {
                    elements.insert(element);
                }
            }
        }
        count("3 arrays/references", array_references);
        count("3 arrays/objects", arrays.len());
        count("3 elements/per array reference", per_reference);
        count("3 elements/per array object", per_object);
        count("3 elements/objects", elements.len());

        // Stage 4: slot 4.
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            match resolve(word_at(bytes, record + 8 + 8 * 4)) {
                Some(target) => match shape(target) {
                    Some((0, 2)) => {
                        count("4 slot4/pair", 1);
                        seeds.insert(target);
                    }
                    Some((1, 2)) => count("4 slot4/third shape", 1),
                    Some((5, 1)) => count("4 slot4/wrapper", 1),
                    _ => {}
                },
                None => {}
            }
        }

        // Stage 5: the spine.
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }
        count("5 spine/seeds", seeds.len());
        count("5 spine/nodes", all.len());
        count("5 spine/interior", all.len() - seeds.len());

        // Stage 6/7: four-field records, then their slot-3 arrays and elements,
        // per population AND pooled.
        let mut pooled_arrays: BTreeSet<usize> = BTreeSet::new();
        let mut pooled_first: BTreeSet<usize> = BTreeSet::new();
        let mut pooled_all_tag1: BTreeSet<usize> = BTreeSet::new();
        let mut memberships = 0usize;
        for population in [true, false] {
            let mut four: BTreeSet<usize> = BTreeSet::new();
            for &node in &all {
                if seeds.contains(&node) == population
                    && let Some(record) = resolve(word_at(bytes, node + 8))
                {
                    four.insert(record);
                }
            }
            count(
                if population {
                    "6 records/seed"
                } else {
                    "6 records/interior"
                },
                four.len(),
            );

            let mut group: BTreeSet<usize> = BTreeSet::new();
            for &record in &four {
                let Some(carrier) = resolve(word_at(bytes, record + 8 + 8 * 3)) else {
                    continue;
                };
                for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                    if shape(carrier) == Some((tag, arity))
                        && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                    {
                        group.insert(array);
                    }
                }
            }
            let mut first: BTreeSet<usize> = BTreeSet::new();
            let mut second: BTreeSet<usize> = BTreeSet::new();
            for &array in &group {
                for i in 0..word_at(bytes, array + 8) {
                    let word = word_at(bytes, array + 24 + 8 * i as usize);
                    match resolve(word) {
                        None => count("7 elements/boxed", 1),
                        Some(element) => {
                            count("7 elements/pointer", 1);
                            match shape(element) {
                                Some((1, 1)) => {
                                    first.insert(element);
                                }
                                Some((2, 1)) => {
                                    second.insert(element);
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
            let wrapped: BTreeSet<usize> = second
                .iter()
                .filter_map(|&object| resolve(word_at(bytes, object + 8)))
                .filter(|&target| shape(target) == Some((1, 1)))
                .collect();
            memberships += first.union(&wrapped).count();
            pooled_arrays.extend(&group);
            pooled_first.extend(&first);
            pooled_all_tag1.extend(first.union(&wrapped));
        }
        count("8 tag1/memberships", memberships);
        count("8 tag1/pooled objects", pooled_all_tag1.len());
        count("8 arrays/pooled objects", pooled_arrays.len());
        count("8 tag1 elements/pooled objects", pooled_first.len());
    }

    if !prelude_loaded {
        assert!(
            ledger.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    let get = |key: &str| ledger.get(key).copied().unwrap_or_default();

    // Every stage, with its unit named in the key.
    assert_eq!(
        ledger
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect::<Vec<_>>(),
        vec![
            ("1 third/boxed-tailed".to_owned(), 17),
            ("1 third/tag0-tailed".to_owned(), 71),
            ("1 third/tag4-tailed".to_owned(), 11),
            ("2 heads/objects".to_owned(), 69),
            ("2 heads/references".to_owned(), 71),
            ("3 arrays/objects".to_owned(), 51),
            ("3 arrays/references".to_owned(), 69),
            ("3 elements/objects".to_owned(), 111),
            ("3 elements/per array object".to_owned(), 123),
            ("3 elements/per array reference".to_owned(), 157),
            ("4 slot4/pair".to_owned(), 57),
            ("4 slot4/third shape".to_owned(), 8),
            ("4 slot4/wrapper".to_owned(), 4),
            ("5 spine/interior".to_owned(), 46),
            ("5 spine/nodes".to_owned(), 102),
            ("5 spine/seeds".to_owned(), 56),
            ("6 records/interior".to_owned(), 46),
            ("6 records/seed".to_owned(), 54),
            ("7 elements/boxed".to_owned(), 1),
            ("7 elements/pointer".to_owned(), 101),
            ("8 arrays/pooled objects".to_owned(), 42),
            ("8 tag1 elements/pooled objects".to_owned(), 23),
            ("8 tag1/memberships".to_owned(), 46),
            ("8 tag1/pooled objects".to_owned(), 33),
        ],
        "the whole chain, each number with its unit"
    );

    // The identities between stages - what no single cell can assert.
    assert_eq!(
        get("1 third/tag0-tailed") + get("1 third/tag4-tailed") + get("1 third/boxed-tailed"),
        99,
        "the third shape splits three ways and nowhere else"
    );
    assert_eq!(
        get("4 slot4/pair") + get("4 slot4/third shape") + get("4 slot4/wrapper"),
        get("2 heads/objects"),
        "slot 4 accounts for every head record"
    );
    assert_eq!(
        get("5 spine/seeds") + get("5 spine/interior"),
        get("5 spine/nodes"),
        "the spine is its seeds plus its interior"
    );
    assert_eq!(
        get("6 records/seed") + get("6 records/interior"),
        100,
        "one four-field record per spine node, less two. The two are SEED nodes \
         sharing a record with each other - measured in \
         `the_sharing_excesses_account_for_every_gap` as a seed excess of 2 and \
         an interior excess of 0. This message said \"the two shared head \
         records\" until then, which is a different pair at a different level \
         that happens also to number two"
    );
    assert_eq!(
        get("7 elements/pointer") + get("7 elements/boxed"),
        102,
        "the slot-3 array elements"
    );

    // The two unit facts this ledger found.
    assert_ne!(
        get("3 elements/per array reference"),
        get("3 elements/per array object"),
        "157 and 123 count the same elements through references and through \
         objects, and both yield 111 distinct - `3b510e62` and `a4de2083` are \
         counting different things and both are right"
    );
    assert_eq!(
        (get("8 tag1/memberships"), get("8 tag1/pooled objects")),
        (46, 33),
        "`2d20e69f`'s 46 is per-population MEMBERSHIPS over 33 distinct \
         objects. The two populations are NOT disjoint below the four-field \
         records - `d8906952` proved the RECORDS disjoint, and that is where it \
         stops: they share 5 arrays and 12 `tag 1` elements"
    );
    assert_eq!(
        (
            get("8 arrays/pooled objects"),
            get("8 tag1 elements/pooled objects")
        ),
        (42, 23),
        "pooled against the per-population 14 + 33 arrays and 14 + 21 elements"
    );
}

/// The overlap sets - which did not exist as sets until `243053f8`.
///
/// The ledger found that the two populations share 5 arrays and 12 `tag 1`
/// elements below the four-field records. Nothing has opened those. They are
/// the newest thing in the descent and the only set the ledger counts that no
/// cell has looked inside.
///
/// THE SHARED ELEMENTS ARE NOT SPECIAL, which is `c726dec5`'s answer for the
/// shared head records arriving again four levels down. Every `tag 1` element
/// points at a numbered name link - the 12 shared ones, the 2 seed-only, the 9
/// interior-only, without distinction. Sharing is what compaction does to
/// identical subterms, not a mark on the data.
///
/// THE EMPTY ARRAY IS ONE OBJECT, NOT TWO. `4277a152` pinned a length-zero
/// array in each `tag 3` group and I described it as "one in each". Both
/// populations reach the SAME object: the seeds have one, the interior has one,
/// and the shared set has one. Two memberships, one array - the membership
/// versus object distinction again, in a sentence I wrote before the ledger
/// existed to catch it.
///
/// AND THE SHARING IS NOT EXPLAINED BY THE SHARED ARRAYS. Only 4 of the 12
/// shared elements sit inside a shared array; the other 8 are reached through
/// DIFFERENT arrays in each population that happen to hold the same element.
/// So the overlap is not one shared container dragging its contents along - the
/// elements are shared on their own account, which is a stronger statement and
/// the one the containers would have hidden.
///
/// The length histograms are pinned per group and nothing is said about their
/// tendency; five shared arrays support no adjective.
#[test]
fn the_shared_objects_are_not_special() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut sizes: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut lengths: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut inner: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut empties: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut containment: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        let mut carriers: Vec<usize> = Vec::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) == Some((0, 2)) {
                carriers.push(object.off);
            }
        }
        let records: BTreeSet<usize> = carriers
            .iter()
            .filter_map(|&node| resolve(word_at(bytes, node + 8)))
            .filter(|&head| shape(head) == Some((0, 5)))
            .collect();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        // The two populations' arrays and `tag 1` elements.
        let mut group: [(BTreeSet<usize>, BTreeSet<usize>); 2] = [
            (BTreeSet::new(), BTreeSet::new()),
            (BTreeSet::new(), BTreeSet::new()),
        ];
        for (which, population) in [true, false].into_iter().enumerate() {
            for &node in &all {
                if seeds.contains(&node) != population {
                    continue;
                }
                let Some(record) = resolve(word_at(bytes, node + 8)) else {
                    continue;
                };
                let Some(carrier) = resolve(word_at(bytes, record + 8 + 8 * 3)) else {
                    continue;
                };
                for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                    if shape(carrier) == Some((tag, arity))
                        && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                    {
                        group[which].0.insert(array);
                    }
                }
            }
            let arrays = group[which].0.clone();
            for array in arrays {
                for i in 0..word_at(bytes, array + 8) {
                    if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                        && shape(element) == Some((1, 1))
                    {
                        group[which].1.insert(element);
                    }
                }
            }
        }

        let shared_arrays: BTreeSet<usize> =
            group[0].0.intersection(&group[1].0).copied().collect();
        let shared_elements: BTreeSet<usize> =
            group[0].1.intersection(&group[1].1).copied().collect();

        for (name, set) in [
            ("arrays/shared", shared_arrays.clone()),
            (
                "arrays/seed only",
                group[0].0.difference(&group[1].0).copied().collect(),
            ),
            (
                "arrays/interior only",
                group[1].0.difference(&group[0].0).copied().collect(),
            ),
        ] {
            *sizes.entry(name.to_owned()).or_default() += set.len();
            for array in set {
                let length = word_at(bytes, array + 8);
                *lengths
                    .entry(format!("{name}/length {length}"))
                    .or_default() += 1;
            }
        }
        for (name, set) in [
            ("tag1/shared", shared_elements.clone()),
            (
                "tag1/seed only",
                group[0].1.difference(&group[1].1).copied().collect(),
            ),
            (
                "tag1/interior only",
                group[1].1.difference(&group[0].1).copied().collect(),
            ),
        ] {
            *sizes.entry(name.to_owned()).or_default() += set.len();
            for element in set {
                let target = resolve(word_at(bytes, element + 8)).expect("a pointer");
                *inner
                    .entry(format!(
                        "{name}/tag {} arity {}",
                        at[&target].tag, at[&target].other
                    ))
                    .or_default() += 1;
            }
        }

        // The empty array: one object, or one per population?
        for (name, set) in [
            ("seed", group[0].0.clone()),
            ("interior", group[1].0.clone()),
            ("shared", shared_arrays.clone()),
        ] {
            *empties.entry(name.to_owned()).or_default() +=
                set.iter().filter(|&&a| word_at(bytes, a + 8) == 0).count();
        }

        // Are the shared elements inside the shared arrays?
        let mut inside: BTreeSet<usize> = BTreeSet::new();
        for &array in &shared_arrays {
            for i in 0..word_at(bytes, array + 8) {
                if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                    && shape(element) == Some((1, 1))
                {
                    inside.insert(element);
                }
            }
        }
        *containment
            .entry("inside a shared array".to_owned())
            .or_default() += inside.len();
        *containment
            .entry("of those, shared".to_owned())
            .or_default() += inside.intersection(&shared_elements).count();
        *containment
            .entry("shared but not inside one".to_owned())
            .or_default() += shared_elements.difference(&inside).count();
    }

    if !prelude_loaded {
        assert!(
            sizes.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    assert_eq!(
        sizes.into_iter().collect::<Vec<_>>(),
        vec![
            ("arrays/interior only".to_owned(), 28),
            ("arrays/seed only".to_owned(), 9),
            ("arrays/shared".to_owned(), 5),
            ("tag1/interior only".to_owned(), 9),
            ("tag1/seed only".to_owned(), 2),
            ("tag1/shared".to_owned(), 12),
        ],
        "the overlap sets the ledger found, and their complements"
    );

    // Not special: every `tag 1` element points at the same thing.
    assert_eq!(
        inner.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag1/interior only/tag 2 arity 2".to_owned(), 9),
            ("tag1/seed only/tag 2 arity 2".to_owned(), 2),
            ("tag1/shared/tag 2 arity 2".to_owned(), 12),
        ],
        "shared and unshared alike point at a numbered name link - `c726dec5`'s \
         answer for the head records, four levels down"
    );

    // One empty array, two memberships.
    assert_eq!(
        empties.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior".to_owned(), 1),
            ("seed".to_owned(), 1),
            ("shared".to_owned(), 1),
        ],
        "`4277a152` pinned a length-zero array in each group and I called it \
         \"one in each\". The shared set has one too, so both populations reach \
         the SAME object: two memberships, one array"
    );

    // The sharing is not the containers'.
    assert_eq!(
        containment.into_iter().collect::<Vec<_>>(),
        vec![
            ("inside a shared array".to_owned(), 4),
            ("of those, shared".to_owned(), 4),
            ("shared but not inside one".to_owned(), 8),
        ],
        "only 4 of the 12 shared elements sit in a shared array; the other 8 \
         are reached through DIFFERENT arrays holding the same element, so the \
         overlap is not one container dragging its contents along"
    );

    assert_eq!(
        lengths.into_iter().collect::<Vec<_>>(),
        vec![
            ("arrays/interior only/length 1".to_owned(), 3),
            ("arrays/interior only/length 2".to_owned(), 14),
            ("arrays/interior only/length 3".to_owned(), 5),
            ("arrays/interior only/length 4".to_owned(), 3),
            ("arrays/interior only/length 5".to_owned(), 2),
            ("arrays/interior only/length 6".to_owned(), 1),
            ("arrays/seed only/length 1".to_owned(), 2),
            ("arrays/seed only/length 2".to_owned(), 7),
            ("arrays/shared/length 0".to_owned(), 1),
            ("arrays/shared/length 1".to_owned(), 2),
            ("arrays/shared/length 2".to_owned(), 2),
        ],
        "lengths per group; five shared arrays support no adjective, so none is \
         offered"
    );
}

/// The membership gap, DECOMPOSED - and the pooling question answered the other
/// way this time.
///
/// `243053f8` pins 46 per-population memberships against 33 distinct `tag 1`
/// objects and never says why they differ by 13. Stating both numbers is not
/// accounting for the difference between them, and an unexplained gap is where
/// a miscount hides: any error in either figure would still leave "46 and 33"
/// looking like two facts rather than one contradiction.
///
/// The gap decomposes exactly: 46 - 33 = 13 = 12 shared elements + 1 shared
/// wrapped object. Both routes are asserted, so a drift in either overlap
/// contradicts the arithmetic instead of passing.
///
/// AND THE POOLING QUESTION HAD TO BE ASKED AGAIN, because the last time I
/// assumed the answer I was wrong. `2d20e69f` pins that the element `tag 1`s
/// and the wrapped `tag 1`s do not overlap - PER POPULATION, zero in each. At
/// `243053f8` I learned that per-population disjointness is not pooled
/// disjointness: the seeds and the interior share objects below the four-field
/// records even though their records are disjoint.
///
/// So the same question here has to be measured, not inherited. It is measured,
/// and this time the answer is the OTHER one: pooled overlap is zero as well,
/// so 23 + 10 = 33 exactly.
///
/// THAT ASYMMETRY IS THE POINT. The lesson from `243053f8` is not "disjointness
/// never extends" - here it does. It is that whether it extends is a SEPARATE
/// QUESTION each time, with no default answer, and the only way to hold that
/// discipline is to measure the pooled case even when the per-population one is
/// already pinned.
#[test]
fn the_membership_gap_decomposes() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        let mut elements: [BTreeSet<usize>; 2] = [BTreeSet::new(), BTreeSet::new()];
        let mut wrapped: [BTreeSet<usize>; 2] = [BTreeSet::new(), BTreeSet::new()];
        for (which, population) in [true, false].into_iter().enumerate() {
            let mut arrays: BTreeSet<usize> = BTreeSet::new();
            for &node in &all {
                if seeds.contains(&node) != population {
                    continue;
                }
                let Some(record) = resolve(word_at(bytes, node + 8)) else {
                    continue;
                };
                let Some(carrier) = resolve(word_at(bytes, record + 8 + 8 * 3)) else {
                    continue;
                };
                for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                    if shape(carrier) == Some((tag, arity))
                        && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                    {
                        arrays.insert(array);
                    }
                }
            }
            let mut wrappers: BTreeSet<usize> = BTreeSet::new();
            for array in arrays {
                for i in 0..word_at(bytes, array + 8) {
                    let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) else {
                        continue;
                    };
                    match shape(element) {
                        Some((1, 1)) => {
                            elements[which].insert(element);
                        }
                        Some((2, 1)) => {
                            wrappers.insert(element);
                        }
                        _ => {}
                    }
                }
            }
            for wrapper in wrappers {
                if let Some(target) = resolve(word_at(bytes, wrapper + 8))
                    && shape(target) == Some((1, 1))
                {
                    wrapped[which].insert(target);
                }
            }
        }

        let mut count = |key: &str, by: usize| *counts.entry(key.to_owned()).or_default() += by;
        // Per population, as `2d20e69f` measures it.
        for (which, name) in [(0usize, "seed"), (1, "interior")] {
            count(
                &format!("1 per population/{name} membership"),
                elements[which].union(&wrapped[which]).count(),
            );
            count(
                &format!("1 per population/{name} element-wrapped overlap"),
                elements[which].intersection(&wrapped[which]).count(),
            );
        }
        // Pooled - the question that must be asked again rather than inherited.
        let pooled_elements: BTreeSet<usize> = elements[0].union(&elements[1]).copied().collect();
        let pooled_wrapped: BTreeSet<usize> = wrapped[0].union(&wrapped[1]).copied().collect();
        count("2 pooled/elements", pooled_elements.len());
        count("2 pooled/wrapped", pooled_wrapped.len());
        count(
            "2 pooled/element-wrapped overlap",
            pooled_elements.intersection(&pooled_wrapped).count(),
        );
        count(
            "2 pooled/all tag1",
            pooled_elements.union(&pooled_wrapped).count(),
        );
        // The two components of the gap.
        count(
            "3 shared/elements",
            elements[0].intersection(&elements[1]).count(),
        );
        count(
            "3 shared/wrapped",
            wrapped[0].intersection(&wrapped[1]).count(),
        );
    }

    if !prelude_loaded {
        assert!(
            counts.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    let get = |key: &str| counts.get(key).copied().unwrap_or_default();

    assert_eq!(
        counts
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect::<Vec<_>>(),
        vec![
            (
                "1 per population/interior element-wrapped overlap".to_owned(),
                0
            ),
            ("1 per population/interior membership".to_owned(), 31),
            (
                "1 per population/seed element-wrapped overlap".to_owned(),
                0
            ),
            ("1 per population/seed membership".to_owned(), 15),
            ("2 pooled/all tag1".to_owned(), 33),
            ("2 pooled/element-wrapped overlap".to_owned(), 0),
            ("2 pooled/elements".to_owned(), 23),
            ("2 pooled/wrapped".to_owned(), 10),
            ("3 shared/elements".to_owned(), 12),
            ("3 shared/wrapped".to_owned(), 1),
        ],
        "per population, pooled, and the two overlaps"
    );

    // The pooling question, measured rather than inherited.
    assert_eq!(
        get("2 pooled/element-wrapped overlap"),
        0,
        "`2d20e69f` pins this as zero PER POPULATION. At `243053f8` \
         per-population disjointness turned out not to imply the pooled kind, \
         so it is measured here rather than inherited - and this time it does \
         hold, which is why neither answer can be a default"
    );
    assert_eq!(
        get("2 pooled/elements") + get("2 pooled/wrapped"),
        get("2 pooled/all tag1"),
        "so the pooled sets add exactly: 23 + 10 = 33"
    );

    // The gap, decomposed, by two routes.
    let memberships =
        get("1 per population/seed membership") + get("1 per population/interior membership");
    assert_eq!(memberships, 46, "the memberships `243053f8` pins");
    assert!(
        memberships > get("2 pooled/all tag1"),
        "the gap must be non-zero, or this cell decomposes nothing"
    );
    assert_eq!(
        memberships - get("2 pooled/all tag1"),
        13,
        "46 memberships over 33 objects"
    );
    assert_eq!(
        get("3 shared/elements") + get("3 shared/wrapped"),
        13,
        "and the 13 is exactly the shared elements plus the shared wrapped \
         object - the gap `243053f8` states and does not account for, closed \
         from both ends"
    );
}

/// The remaining pooled identities - and the seeds contribute no `tag 2` of
/// their own.
///
/// `8132075a` closed the `tag 1` accounting: 46 memberships less 33 objects is
/// 13, and the 13 is the shared elements plus the shared wrapped object. Two
/// pooled quantities the ledger names were left with no such identity - the
/// slot-3 arrays and the `tag 2` elements - and the single shared `tag 2`
/// object has never been opened at all. This closes both.
///
///   arrays   14 + 33 = 47 memberships, 42 pooled, gap 5 = the shared 5,
///            and 9 seed-only + 28 interior-only + 5 shared = 42
///   tag 2     1 + 15 = 16 memberships, 15 pooled, gap 1 = the shared 1,
///            and 0 + 14 + 1 = 15
///
/// Each is asserted twice - once as memberships minus pooled, once as the three
/// disjoint parts summing to the pooled total - so a drift in any one part
/// contradicts the other route. `ddfa2317` pins the parts and `243053f8` pins
/// the pooled totals; nothing tied them, which is the same gap `8132075a`
/// closed for `tag 1`.
///
/// THE SEEDS CONTRIBUTE NO `tag 2` OF THEIR OWN. Seed-only is ZERO: the seed
/// population has exactly one `tag 2` element and it is the shared one. That is
/// a categorical absence, asserted as a count rather than described, and it is
/// why the `tag 2` gap of 1 is the whole of the seeds' contribution rather than
/// an incidental overlap.
///
/// AND THE SHARED `tag 2` IS NOT SPECIAL EITHER. It wraps a `tag 1`, which is
/// what 9 of the 14 interior-only ones do; the other 5 wrap the other shape. So
/// it sits in the majority class and nothing marks it out - the third
/// population where I have asked whether a shared object is distinguished and
/// found it is not, after `c726dec5` and `ddfa2317`.
///
/// One object supports no proportion, so its class membership is pinned and no
/// inference is drawn from it beyond "not distinguished".
#[test]
fn the_remaining_pooled_identities() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut inner: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        let mut arrays: [BTreeSet<usize>; 2] = [BTreeSet::new(), BTreeSet::new()];
        let mut wrappers: [BTreeSet<usize>; 2] = [BTreeSet::new(), BTreeSet::new()];
        for (which, population) in [true, false].into_iter().enumerate() {
            for &node in &all {
                if seeds.contains(&node) != population {
                    continue;
                }
                let Some(record) = resolve(word_at(bytes, node + 8)) else {
                    continue;
                };
                let Some(carrier) = resolve(word_at(bytes, record + 8 + 8 * 3)) else {
                    continue;
                };
                for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                    if shape(carrier) == Some((tag, arity))
                        && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                    {
                        arrays[which].insert(array);
                    }
                }
            }
            let group = arrays[which].clone();
            for array in group {
                for i in 0..word_at(bytes, array + 8) {
                    if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                        && shape(element) == Some((2, 1))
                    {
                        wrappers[which].insert(element);
                    }
                }
            }
        }

        let mut count = |key: &str, by: usize| *counts.entry(key.to_owned()).or_default() += by;
        for (name, sets) in [("arrays", &arrays), ("tag2", &wrappers)] {
            count(&format!("{name}/seed"), sets[0].len());
            count(&format!("{name}/interior"), sets[1].len());
            count(&format!("{name}/pooled"), sets[0].union(&sets[1]).count());
            count(
                &format!("{name}/shared"),
                sets[0].intersection(&sets[1]).count(),
            );
            count(
                &format!("{name}/seed only"),
                sets[0].difference(&sets[1]).count(),
            );
            count(
                &format!("{name}/interior only"),
                sets[1].difference(&sets[0]).count(),
            );
        }

        // Open the shared `tag 2` object, and the unshared ones for contrast.
        let shared: BTreeSet<usize> = wrappers[0].intersection(&wrappers[1]).copied().collect();
        for (name, set) in [
            ("shared", shared.clone()),
            (
                "interior only",
                wrappers[1]
                    .difference(&wrappers[0])
                    .copied()
                    .collect::<BTreeSet<_>>(),
            ),
        ] {
            for object in set {
                let described = match resolve(word_at(bytes, object + 8)) {
                    Some(target) => {
                        let target = at.get(&target).expect("resolved above");
                        format!("tag {} arity {}", target.tag, target.other)
                    }
                    None => "boxed".to_owned(),
                };
                *inner.entry(format!("{name}/{described}")).or_default() += 1;
            }
        }
    }

    if !prelude_loaded {
        assert!(
            counts.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    let get = |key: &str| counts.get(key).copied().unwrap_or_default();

    assert_eq!(
        counts
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect::<Vec<_>>(),
        vec![
            ("arrays/interior".to_owned(), 33),
            ("arrays/interior only".to_owned(), 28),
            ("arrays/pooled".to_owned(), 42),
            ("arrays/seed".to_owned(), 14),
            ("arrays/seed only".to_owned(), 9),
            ("arrays/shared".to_owned(), 5),
            ("tag2/interior".to_owned(), 15),
            ("tag2/interior only".to_owned(), 14),
            ("tag2/pooled".to_owned(), 15),
            ("tag2/seed".to_owned(), 1),
            ("tag2/seed only".to_owned(), 0),
            ("tag2/shared".to_owned(), 1),
        ],
        "both quantities, per population and pooled"
    );

    // Each identity twice: memberships minus pooled, and the parts summing.
    for name in ["arrays", "tag2"] {
        let memberships = get(&format!("{name}/seed")) + get(&format!("{name}/interior"));
        let pooled = get(&format!("{name}/pooled"));
        let shared = get(&format!("{name}/shared"));
        assert!(
            memberships > pooled,
            "{name}: the gap must be non-zero, or there is no identity to close"
        );
        assert_eq!(
            memberships - pooled,
            shared,
            "{name}: memberships less pooled objects is exactly the shared set"
        );
        assert_eq!(
            get(&format!("{name}/seed only")) + get(&format!("{name}/interior only")) + shared,
            pooled,
            "{name}: and the three disjoint parts sum to the pooled total - the \
             same fact by a route that does not use the memberships"
        );
    }

    // The categorical absence.
    assert_eq!(
        get("tag2/seed only"),
        0,
        "the seeds contribute NO `tag 2` of their own: they have exactly one \
         and it is the shared one, so their whole contribution is the overlap"
    );

    // Not special, a third time.
    assert_eq!(
        inner.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior only/tag 1 arity 1".to_owned(), 9),
            ("interior only/tag 4 arity 2".to_owned(), 5),
            ("shared/tag 1 arity 1".to_owned(), 1),
        ],
        "the shared `tag 2` wraps a `tag 1`, which is what 9 of the 14 \
         interior-only ones do - it sits in the majority class and nothing \
         marks it out, after `c726dec5` and `ddfa2317` found the same"
    );
}

/// Every gap in the ledger accounted for as a SHARING EXCESS.
///
/// I wrote at `75a1373c` that every pooled quantity the ledger names now has
/// its identity closed. That was true of the pooled-versus-membership ones and
/// false of the reference-versus-object ones, which are the other half of the
/// same table and had three gaps with no explanation: 71 heads to 69 objects,
/// 69 slot-2 arrays to 51, and 123 elements to 111.
///
/// Each is exactly the sharing excess - the sum over objects of one less than
/// their reference count - and each is asserted both as a subtraction and as
/// that sum, so neither route stands alone.
///
///   heads     71 - 69 = 2    refcounts 67 once, 2 twice
///   arrays    69 - 51 = 18   refcounts 44 once, 6 twice, and ONE THIRTEEN TIMES
///   elements 123 - 111 = 12
///
/// ONE ARRAY IS REFERENCED THIRTEEN TIMES. Six others are referenced twice and
/// the remaining 44 once, so a single object accounts for twelve of the
/// eighteen. That is the same shape as the in-degree-15 node `b327b20c` found
/// in the spine: this data has hubs, and a mean would hide them.
///
/// AND THE LEDGER MISATTRIBUTED A CAUSE. Its `100` assertion read "less the two
/// shared head records". The two are SEED NODES sharing a four-field record
/// with each other - seed excess 2, interior excess 0 - which is a different
/// pair at a different level that happens also to number two. The assertion was
/// right and its explanation was wrong, which is worse than no explanation:
/// a reader debugging that line would have gone to the head records. The
/// message is corrected in this commit.
///
/// Two equal numbers arising at different levels is exactly how a wrong cause
/// gets written down and never questioned - it agrees with the arithmetic.
#[test]
fn the_sharing_excesses_account_for_every_gap() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut refcounts: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        // Tally references, then derive objects and excess from the tally.
        let tally = |references: &[usize]| -> (usize, usize, usize, Vec<(usize, usize)>) {
            let mut per: std::collections::BTreeMap<usize, usize> =
                std::collections::BTreeMap::new();
            for &object in references {
                *per.entry(object).or_default() += 1;
            }
            let excess: usize = per.values().map(|count| count - 1).sum();
            let mut histogram: std::collections::BTreeMap<usize, usize> =
                std::collections::BTreeMap::new();
            for count in per.values() {
                *histogram.entry(*count).or_default() += 1;
            }
            (
                references.len(),
                per.len(),
                excess,
                histogram.into_iter().collect(),
            )
        };

        // Heads.
        let mut head_references: Vec<usize> = Vec::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                head_references.push(head);
            }
        }
        let (heads, head_objects, head_excess, head_histogram) = tally(&head_references);
        *counts.entry("heads/references".to_owned()).or_default() += heads;
        *counts.entry("heads/objects".to_owned()).or_default() += head_objects;
        *counts.entry("heads/excess".to_owned()).or_default() += head_excess;
        for (count, many) in head_histogram {
            *refcounts.entry(format!("heads/{count}")).or_default() += many;
        }

        let records: BTreeSet<usize> = head_references.iter().copied().collect();

        // Slot-2 arrays.
        let array_references: Vec<usize> = records
            .iter()
            .filter_map(|&record| resolve(word_at(bytes, record + 8 + 8 * 2)))
            .collect();
        let (arrays, array_objects, array_excess, array_histogram) = tally(&array_references);
        *counts.entry("arrays/references".to_owned()).or_default() += arrays;
        *counts.entry("arrays/objects".to_owned()).or_default() += array_objects;
        *counts.entry("arrays/excess".to_owned()).or_default() += array_excess;
        for (count, many) in array_histogram {
            *refcounts.entry(format!("arrays/{count}")).or_default() += many;
        }

        // Elements, over the DISTINCT arrays.
        let mut element_references: Vec<usize> = Vec::new();
        for &array in &array_references.iter().copied().collect::<BTreeSet<_>>() {
            for i in 0..word_at(bytes, array + 8) {
                if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) {
                    element_references.push(element);
                }
            }
        }
        let (elements, element_objects, element_excess, _) = tally(&element_references);
        *counts.entry("elements/references".to_owned()).or_default() += elements;
        *counts.entry("elements/objects".to_owned()).or_default() += element_objects;
        *counts.entry("elements/excess".to_owned()).or_default() += element_excess;

        // The spine's record excess, per population - the ledger's misattributed 2.
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }
        for (name, population) in [("seed", true), ("interior", false)] {
            let references: Vec<usize> = all
                .iter()
                .filter(|&&node| seeds.contains(&node) == population)
                .filter_map(|&node| resolve(word_at(bytes, node + 8)))
                .collect();
            let (refs, objects_, excess, _) = tally(&references);
            *counts
                .entry(format!("spine {name}/references"))
                .or_default() += refs;
            *counts.entry(format!("spine {name}/objects")).or_default() += objects_;
            *counts.entry(format!("spine {name}/excess")).or_default() += excess;
        }
    }

    if !prelude_loaded {
        assert!(
            counts.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    let get = |key: &str| counts.get(key).copied().unwrap_or_default();

    assert_eq!(
        counts
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect::<Vec<_>>(),
        vec![
            ("arrays/excess".to_owned(), 18),
            ("arrays/objects".to_owned(), 51),
            ("arrays/references".to_owned(), 69),
            ("elements/excess".to_owned(), 12),
            ("elements/objects".to_owned(), 111),
            ("elements/references".to_owned(), 123),
            ("heads/excess".to_owned(), 2),
            ("heads/objects".to_owned(), 69),
            ("heads/references".to_owned(), 71),
            ("spine interior/excess".to_owned(), 0),
            ("spine interior/objects".to_owned(), 46),
            ("spine interior/references".to_owned(), 46),
            ("spine seed/excess".to_owned(), 2),
            ("spine seed/objects".to_owned(), 54),
            ("spine seed/references".to_owned(), 56),
        ],
        "every reference-versus-object pair the ledger names, with its excess"
    );

    // Each gap is exactly the excess, by two routes.
    for name in [
        "heads",
        "arrays",
        "elements",
        "spine seed",
        "spine interior",
    ] {
        let references = get(&format!("{name}/references"));
        let objects_ = get(&format!("{name}/objects"));
        assert_eq!(
            references - objects_,
            get(&format!("{name}/excess")),
            "{name}: references less objects is the sharing excess, the sum over \
             objects of one less than their reference count"
        );
    }
    assert!(
        get("arrays/excess") > 0 && get("heads/excess") > 0,
        "with no excess anywhere these identities are 0 = 0 and describe nothing"
    );

    // The hub.
    assert_eq!(
        refcounts.into_iter().collect::<Vec<_>>(),
        vec![
            ("arrays/1".to_owned(), 44),
            ("arrays/13".to_owned(), 1),
            ("arrays/2".to_owned(), 6),
            ("heads/1".to_owned(), 67),
            ("heads/2".to_owned(), 2),
        ],
        "ONE array is referenced thirteen times and accounts for twelve of the \
         eighteen excess on its own - the same hub shape as `b327b20c`'s \
         in-degree-15 node, which a mean would hide"
    );

    // The ledger's misattributed cause, measured.
    assert_eq!(
        (get("spine seed/excess"), get("spine interior/excess")),
        (2, 0),
        "the ledger's `100` said \"less the two shared head records\". The two \
         are SEED NODES sharing a four-field record with each other; the head \
         records' own excess is also 2, at a different level. The assertion was \
         right and its explanation was wrong, which is worse than none"
    );
}

/// The thirteen-times array, as an object rather than as arithmetic.
///
/// `bd0266d2` found it only as a refcount histogram entry: one array carrying
/// twelve of the eighteen excess. A histogram entry is not an object - it
/// cannot be opened, and nothing said which array it was. This pins it by
/// address, re-derives its refcount from the bytes at that address, and reads
/// what it holds.
///
/// IT IS NOT SPECIAL. Its length is 2, which is the MODAL length across the 51
/// arrays - 18 of them are that length, 17 without it. Its two elements are the
/// same `(Name, Name, Expr)` triples every other array holds. Nothing about the
/// object distinguishes it from the arrays referenced once; only the count of
/// pointers into it does. That is the fourth population here where I have asked
/// whether a heavily shared object is marked out and found it is not, after
/// `c726dec5`, `ddfa2317` and `75a1373c`.
///
/// ITS THIRTEEN REFERRERS ARE ALL SLOT-4 PAIRS - thirteen of thirteen, with
/// zero of the other two shapes - against a population that is 57 pairs, 8
/// third-shape and 4 wrappers. THAT IS PINNED AND NOT CHARACTERISED. Pairs are
/// 83 per cent of the records, so thirteen draws landing entirely inside them
/// is an unremarkable outcome; calling it a pattern would be reading thirteen
/// samples as a finding. Both counts are asserted side by side so a reader can
/// see the base rate next to the observation.
///
/// The address carries a guard, the `d7518917` pattern: the cell goes to the
/// pinned offset and re-establishes that the object there is an array of that
/// length with exactly that many pointers into it. A pinned constant nothing
/// re-derives rots quietly.
#[test]
fn the_thirteen_times_array() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut hubs: Vec<(usize, usize, u64)> = Vec::new();
    let mut elements: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut lengths: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut referrers: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut population: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let described = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }

        // Which array each record points at, and how many point at each.
        let mut by_array: std::collections::BTreeMap<usize, Vec<usize>> =
            std::collections::BTreeMap::new();
        for &record in &records {
            if let Some(array) = resolve(word_at(bytes, record + 8 + 8 * 2)) {
                by_array.entry(array).or_default().push(record);
            }
        }
        for (&array, holders) in &by_array {
            let length = word_at(bytes, array + 8);
            *lengths.entry(format!("all/length {length}")).or_default() += 1;
            if holders.len() == 1 {
                *lengths
                    .entry(format!("referenced once/length {length}"))
                    .or_default() += 1;
            }
            if holders.len() > 2 {
                hubs.push((array, holders.len(), length));
            }
        }

        // The population's slot-4 shapes, for the base rate.
        for &record in &records {
            let target = resolve(word_at(bytes, record + 8 + 8 * 4));
            *population
                .entry(target.map_or("boxed".to_owned(), &described))
                .or_default() += 1;
        }

        // The hub, opened, with a guard at its address.
        for &(array, count, length) in &hubs {
            assert_eq!(
                at.get(&array).map(|o| o.tag),
                Some(abi::TAG_ARRAY),
                "the pinned hub must still be an array"
            );
            assert_eq!(
                by_array.get(&array).map(Vec::len),
                Some(count),
                "and must still carry exactly that many references"
            );
            for i in 0..length {
                let element =
                    resolve(word_at(bytes, array + 24 + 8 * i as usize)).expect("a hub element");
                *elements.entry(described(element)).or_default() += 1;
            }
            for &record in by_array.get(&array).expect("the holders") {
                let target = resolve(word_at(bytes, record + 8 + 8 * 4));
                *referrers
                    .entry(target.map_or("boxed".to_owned(), &described))
                    .or_default() += 1;
            }
        }
    }

    if !prelude_loaded {
        assert!(hubs.is_empty(), "the third shape is not in the C3 fixtures");
        return;
    }

    // Exactly one array is referenced more than twice, and this is it.
    assert_eq!(
        hubs,
        vec![(0x2aee08, 13, 2)],
        "the hub by address, reference count and length - `bd0266d2` found it \
         only as a histogram entry, which cannot be opened"
    );

    // Not special: modal length, ordinary contents.
    assert_eq!(
        lengths.into_iter().collect::<Vec<_>>(),
        vec![
            ("all/length 1".to_owned(), 16),
            ("all/length 2".to_owned(), 18),
            ("all/length 3".to_owned(), 5),
            ("all/length 4".to_owned(), 4),
            ("all/length 5".to_owned(), 8),
            ("referenced once/length 1".to_owned(), 14),
            ("referenced once/length 2".to_owned(), 13),
            ("referenced once/length 3".to_owned(), 5),
            ("referenced once/length 4".to_owned(), 4),
            ("referenced once/length 5".to_owned(), 8),
        ],
        "the hub's length of 2 is the MODAL length across the 51 arrays, so \
         nothing about its shape marks it out"
    );
    assert_eq!(
        elements.into_iter().collect::<Vec<_>>(),
        vec![("tag 0 arity 3".to_owned(), 2)],
        "and it holds the same triples every other array holds"
    );

    // Pinned, not characterised.
    assert_eq!(
        referrers.into_iter().collect::<Vec<_>>(),
        vec![("tag 0 arity 2".to_owned(), 13)],
        "all thirteen referrers are slot-4 pairs"
    );
    assert_eq!(
        population.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 0 arity 2".to_owned(), 57),
            ("tag 1 arity 2".to_owned(), 8),
            ("tag 5 arity 1".to_owned(), 4),
        ],
        "against a population that is 57 pairs of 69. Thirteen draws landing \
         entirely inside a class holding 83 per cent of the records is an \
         unremarkable outcome, so the base rate is pinned beside the \
         observation and no pattern is claimed from thirteen samples"
    );
}

/// The categorical zeros, with the denominators they were never given.
///
/// `1cc74dd0` declined to call thirteen-of-thirteen a pattern because pairs are
/// 83 per cent of the population, and I recorded there that I had been
/// asserting categorical zeros for several waves WITHOUT ever doing that
/// arithmetic. This is that audit. It is not a new set; it is the strength of
/// claims already landed, which nothing in the file states.
///
/// A zero is only informative against a base rate that makes zero surprising.
/// Three of this file's zeros, each with its denominator and the rate it should
/// be read against:
///
///   0 of 11   tag-4 third shapes with a pointer head   (`9d365d6a`)
///             against 71 of 71 for the tag-0 group - a rate of ONE
///   0 of  1   seed `tag 2` elements wrapping a `tag 4` (`7e65ed09`)
///             against 5 of 15 for the interior - a rate of about a third
///   0 of 99   third-shape objects reachable from `constants` (`1dd7c288`)
///             against 2259 of 2465 cons-shaped cells - a rate of about 0.92
///
/// TWO OF THE THREE ARE STRONG AND ONE IS EMPTY. Against a rate of one, zero of
/// eleven is impossible by chance; against 0.92, zero of ninety-nine is beyond
/// arithmetic. But `7e65ed09`'s zero is ZERO OF ONE, drawn from a class that
/// occurs a third of the time, so its chance of arising with no cause at all is
/// about two in three. It says nothing, and I presented it as a categorical
/// absence with the same emphasis as the other two.
///
/// The cell asserts that denominator of 1 explicitly, so the file records which
/// of its own claims is content-free rather than leaving a reader to discover
/// it. That is the honest form: the claim stays, its strength is stated, and
/// nobody has to re-derive whether it meant anything.
///
/// What this does NOT do is retract anything. `7e65ed09`'s zero is a true fact
/// about the corpus - the seeds' single `tag 2` element does not wrap a
/// `tag 4`. It is the INFERENCE from it that the denominator forbids.
#[test]
fn the_categorical_zeros_have_denominators() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let mut count = |key: &str, by: usize| *counts.entry(key.to_owned()).or_default() += by;

        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root");
        let declarations = reachable_from(bytes, base, word_at(bytes, root + 24));

        let mut tag0: Vec<usize> = Vec::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            let tail = resolve(second);
            let cons_shaped =
                (second & 1 == 1 && second >> 1 == 0) || tail.and_then(shape) == Some((1, 2));

            if cons_shaped {
                // Zero C's comparison group: ordinary cons cells.
                count("C compare/total", 1);
                if declarations.contains(&object.off) {
                    count("C compare/in constants", 1);
                }
                continue;
            }

            // Zero C: the third shape.
            count("C zero/total", 1);
            if declarations.contains(&object.off) {
                count("C zero/in constants", 1);
            }

            // Zeros A: pointer heads, by which group the tail puts it in.
            let pointer_head = word_at(bytes, object.off + 8) & 1 == 0;
            match tail.and_then(shape) {
                Some((4, 2)) => {
                    count("A zero/total", 1);
                    if pointer_head {
                        count("A zero/pointer heads", 1);
                    }
                }
                Some((0, 2)) => {
                    count("A compare/total", 1);
                    if pointer_head {
                        count("A compare/pointer heads", 1);
                    }
                    tag0.push(object.off);
                }
                _ => {}
            }
        }

        // Zero B: the seeds' `tag 2` elements, against the interior's rate.
        let records: BTreeSet<usize> = tag0
            .iter()
            .filter_map(|&node| resolve(word_at(bytes, node + 8)))
            .filter(|&head| shape(head) == Some((0, 5)))
            .collect();
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }
        for (name, population) in [("B zero", true), ("B compare", false)] {
            let mut arrays: BTreeSet<usize> = BTreeSet::new();
            for &node in &all {
                if seeds.contains(&node) != population {
                    continue;
                }
                let Some(record) = resolve(word_at(bytes, node + 8)) else {
                    continue;
                };
                let Some(carrier) = resolve(word_at(bytes, record + 8 + 8 * 3)) else {
                    continue;
                };
                for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                    if shape(carrier) == Some((tag, arity))
                        && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                    {
                        arrays.insert(array);
                    }
                }
            }
            let mut wrappers: BTreeSet<usize> = BTreeSet::new();
            for array in arrays {
                for i in 0..word_at(bytes, array + 8) {
                    if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                        && shape(element) == Some((2, 1))
                    {
                        wrappers.insert(element);
                    }
                }
            }
            count(&format!("{name}/total"), wrappers.len());
            for wrapper in wrappers {
                if resolve(word_at(bytes, wrapper + 8)).and_then(shape) == Some((4, 2)) {
                    count(&format!("{name}/wrapping tag4"), 1);
                }
            }
        }
    }

    if !prelude_loaded {
        assert!(
            counts.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    let get = |key: &str| counts.get(key).copied().unwrap_or_default();

    // Each zero with its denominator and the rate it should be read against.
    assert_eq!(
        (get("A zero/pointer heads"), get("A zero/total")),
        (0, 11),
        "`9d365d6a`'s zero"
    );
    assert_eq!(
        (get("A compare/pointer heads"), get("A compare/total")),
        (71, 71),
        "against a comparison rate of ONE, so zero of eleven cannot arise by \
         chance - the zero is as strong as a zero gets"
    );

    assert_eq!(
        (get("B zero/wrapping tag4"), get("B zero/total")),
        (0, 1),
        "`7e65ed09`'s zero is ZERO OF ONE"
    );
    assert_eq!(
        (get("B compare/wrapping tag4"), get("B compare/total")),
        (5, 15),
        "against a rate of about a third, so its chance of arising with no \
         cause is about two in three. It is a true fact about the corpus and it \
         supports NO inference - and I presented it with the same emphasis as \
         the other two"
    );
    assert_eq!(
        get("B zero/total"),
        1,
        "asserted on its own so the file records which of its claims is \
         content-free, rather than leaving a reader to work it out"
    );

    assert_eq!(
        (get("C zero/in constants"), get("C zero/total")),
        (0, 99),
        "`1dd7c288`'s zero"
    );
    assert_eq!(
        (get("C compare/in constants"), get("C compare/total")),
        (2259, 2465),
        "against a rate of about 0.92 over 2465 cells, so zero of ninety-nine \
         is beyond arithmetic - and this one already carried a guard"
    );

    // Anti-vacuity: a rate comparison needs a comparison group.
    assert!(
        get("A compare/total") > 0 && get("B compare/total") > 0 && get("C compare/total") > 0,
        "each zero needs a non-empty comparison group, or its denominator says \
         nothing either"
    );
}

/// The "not special" findings, and whether their tests could have said
/// otherwise.
///
/// `1006bd18` gave the categorical zeros the denominators they lacked. The same
/// vacuity applies to a negative result: this file says four times that a
/// shared or heavily-referenced object is NOT SPECIAL, and each time it says so
/// by comparing that object's properties against the population's. If the
/// property is UNIFORM across the whole population, the comparison cannot come
/// out any other way, and "not special" is guaranteed before it is measured.
///
/// So: how many distinct values does each property take?
///
///   `c726dec5`  head-record slots 0-3   ONE value each across all 69
///               head-record slot 4      three values, 57 / 8 / 4
///   `ddfa2317`  the `tag 1` inner       ONE value across the population
///   `75a1373c`  the `tag 2` inner       two values
///   `1cc74dd0`  the array length        five values
///
/// ONE OF THE FOUR WAS VACUOUS. `ddfa2317` concluded that the 12 shared `tag 1`
/// elements are not distinguished because they point at a numbered name link -
/// and so does every other `tag 1` element in the corpus. That comparison had
/// no discriminating power at all; it could not have produced any other answer.
///
/// AND `c726dec5` WAS FOUR-FIFTHS VACUOUS. Its first four slot comparisons are
/// uniform across all 69 records, so only the fifth - slot 4, which takes three
/// values - could have distinguished the two shared records from the rest. The
/// finding stands on that one comparison, not on five.
///
/// The other two are sound: two values and five values respectively, so a
/// shared object COULD have sat outside the common case and did not.
///
/// This retracts nothing. Every one of those observations is true. What was
/// missing is that a negative result is only as strong as the test's ability to
/// have come out positive, and I asserted four of them without once asking
/// whether the test could.
///
/// THE MULTIPLICITIES BELOW WERE WRONG UNTIL w165, AND THE FINDING WAS NOT.
/// This cell's walk deduplicates elements into a `BTreeSet`, so its counts are
/// DISTINCT OBJECTS pooled across both populations. The first version pinned
/// occurrence counts instead - 70 where the walk computes 23, and 19 + 6 where
/// it computes 10 + 5 - taken from the measurement script rather than from the
/// walk. The corrected numbers reconcile with `243053f8`'s pooled totals, which
/// the wrong ones did not.
///
/// The conclusion is untouched, because it rests on how many DISTINCT VALUES
/// each property takes and not on how often each occurs: one value for
/// `ddfa2317`'s inner either way, two for `75a1373c`'s either way. A
/// discriminating-power audit is insensitive to multiplicity by construction,
/// which is why a wrong count could sit inside a right finding.
#[test]
fn the_not_special_findings_needed_discriminating_power() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    // Each property, as the multiset of values it takes over its population.
    let mut values: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let described = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut tag0: Vec<usize> = Vec::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) == Some((0, 2)) {
                tag0.push(object.off);
            }
        }
        let records: BTreeSet<usize> = tag0
            .iter()
            .filter_map(|&node| resolve(word_at(bytes, node + 8)))
            .filter(|&head| shape(head) == Some((0, 5)))
            .collect();

        // `c726dec5`'s property: each of the head record's five slots.
        for &record in &records {
            for slot in 0..5usize {
                let word = word_at(bytes, record + 8 + 8 * slot);
                let described = resolve(word).map_or("boxed".to_owned(), &described);
                *values
                    .entry(format!("c726dec5 slot {slot}/{described}"))
                    .or_default() += 1;
            }
            // `1cc74dd0`'s property: the slot-2 array's length.
            if let Some(array) = resolve(word_at(bytes, record + 8 + 8 * 2)) {
                let length = word_at(bytes, array + 8);
                *values
                    .entry(format!("1cc74dd0 length/{length}"))
                    .or_default() += 1;
            }
        }

        // `ddfa2317` and `75a1373c`: the element inners.
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }
        let mut arrays: BTreeSet<usize> = BTreeSet::new();
        for &node in &all {
            let Some(record) = resolve(word_at(bytes, node + 8)) else {
                continue;
            };
            let Some(carrier) = resolve(word_at(bytes, record + 8 + 8 * 3)) else {
                continue;
            };
            for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                if shape(carrier) == Some((tag, arity))
                    && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                {
                    arrays.insert(array);
                }
            }
        }
        let mut first: BTreeSet<usize> = BTreeSet::new();
        let mut second: BTreeSet<usize> = BTreeSet::new();
        for array in arrays {
            for i in 0..word_at(bytes, array + 8) {
                let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) else {
                    continue;
                };
                match shape(element) {
                    Some((1, 1)) => {
                        first.insert(element);
                    }
                    Some((2, 1)) => {
                        second.insert(element);
                    }
                    _ => {}
                }
            }
        }
        for (name, set) in [("ddfa2317 inner", first), ("75a1373c inner", second)] {
            for element in set {
                let word = word_at(bytes, element + 8);
                let described = resolve(word).map_or("boxed".to_owned(), &described);
                *values.entry(format!("{name}/{described}")).or_default() += 1;
            }
        }
    }

    if !prelude_loaded {
        assert!(
            values.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    // How many distinct values each property takes: the discriminating power.
    let distinct =
        |prefix: &str| -> usize { values.keys().filter(|key| key.starts_with(prefix)).count() };

    assert_eq!(
        values
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect::<Vec<_>>(),
        vec![
            ("1cc74dd0 length/1".to_owned(), 18),
            ("1cc74dd0 length/2".to_owned(), 34),
            ("1cc74dd0 length/3".to_owned(), 5),
            ("1cc74dd0 length/4".to_owned(), 4),
            ("1cc74dd0 length/5".to_owned(), 8),
            ("75a1373c inner/tag 1 arity 1".to_owned(), 10),
            ("75a1373c inner/tag 4 arity 2".to_owned(), 5),
            ("c726dec5 slot 0/tag 2 arity 2".to_owned(), 69),
            ("c726dec5 slot 1/tag 2 arity 2".to_owned(), 69),
            ("c726dec5 slot 2/tag 246 arity 0".to_owned(), 69),
            ("c726dec5 slot 3/tag 7 arity 3".to_owned(), 69),
            ("c726dec5 slot 4/tag 0 arity 2".to_owned(), 57),
            ("c726dec5 slot 4/tag 1 arity 2".to_owned(), 8),
            ("c726dec5 slot 4/tag 5 arity 1".to_owned(), 4),
            ("ddfa2317 inner/tag 2 arity 2".to_owned(), 23),
        ],
        "every property, as the values it takes over its whole population. \
         \
         THE BASIS IS DISTINCT OBJECTS, POOLED across both populations - the \
         walk above collects elements into a `BTreeSet` before reading them, so \
         each object contributes once however many arrays hold it. The 23 is \
         `243053f8`'s pooled `tag 1` element count and the 10 + 5 is its pooled \
         `tag 2` count of 15, so this row reconciles with two landed totals. \
         \
         It first pinned 70 and 19 + 6, which are OCCURRENCE counts from the \
         measurement script rather than anything this walk computes, and w165 \
         caught it"
    );

    // The vacuous ones: a property with a single value cannot distinguish.
    assert_eq!(
        distinct("ddfa2317 inner/"),
        1,
        "`ddfa2317` concluded the 12 shared `tag 1` elements are not \
         distinguished because they point at a numbered name link - and so does \
         EVERY `tag 1` element. That comparison had no discriminating power and \
         could not have produced another answer"
    );
    assert_eq!(
        (
            distinct("c726dec5 slot 0/"),
            distinct("c726dec5 slot 1/"),
            distinct("c726dec5 slot 2/"),
            distinct("c726dec5 slot 3/"),
        ),
        (1, 1, 1, 1),
        "`c726dec5`'s first four slot comparisons are uniform across all 69 \
         records, so four-fifths of that finding could not have come out \
         otherwise"
    );
    assert_eq!(
        distinct("c726dec5 slot 4/"),
        3,
        "only its fifth comparison could distinguish, so the finding stands on \
         one comparison and not five"
    );

    // The sound ones.
    assert_eq!(
        (distinct("75a1373c inner/"), distinct("1cc74dd0 length/")),
        (2, 5),
        "these two properties vary, so a shared object COULD have sat outside \
         the common case and did not"
    );

    // Anti-vacuity for this cell itself.
    assert!(
        distinct("1cc74dd0 length/") > 1,
        "at least one property must vary, or this cell is the same vacuity it \
         is auditing"
    );
}

/// The audit I deferred at `7e65ed09`: none of the identified shapes is unique.
///
/// That cell found `(4, 2)` doing duty for two different things and I wrote:
/// "the identifications at `aec3efd1`, `c7836115`, `a4de2083` and `fffc0e71`
/// were made where I had no evidence of a collision - which is not the same as
/// evidence of no collision. Auditing them is bigger than one cell." It is not.
/// The audit is one scan, and the answer is worse than the deferral implied.
///
/// Across the corpus, each shape this file identifies:
///
///   (4, 2)    2537 objects   3 field signatures   sizes 24 and 32
///   (7, 3)   12912 objects  68 field signatures   sizes 40 and 48
///   (0, 3)    5553 objects  37 field signatures   sizes 32 and 40
///   (1, 1)    1912 objects   8 field signatures   sizes 16 and 24
///   (2, 1)      78 objects   8 field signatures   size 16
///   (2, 2)    1955 objects  15 field signatures   sizes 24 and 32
///
/// SIGNATURE COUNT IS THE WEAK MEASURE AND I AM NOT LEANING ON IT. A single
/// type's fields legitimately hold different subtypes - a `forallE`'s binder
/// type can be any expression - so 68 signatures at `(7, 3)` is what ONE type
/// looks like, not evidence of sixty-eight. Reading it as a collision count
/// would be exactly the over-reading these audits exist to stop.
///
/// SIZE COUNT IS THE STRONG ONE. Two distinct stored sizes at the same tag and
/// arity mean two different scalar-area widths, which is two different LAYOUTS
/// and cannot be one type. Five of the six shapes have that.
///
/// So shape never identified anything, anywhere in this chain. Where the
/// identification was right - and `aec3efd1`'s `Expr.const` reading matched a
/// corpus measurement, `c7836115`'s `forallE` matched `49b72dcf`'s 9,547
/// objects - it was right because the SIZE and the field types agreed, not
/// because the tag and arity did. The cells that pinned a size were doing more
/// work than the ones that pinned only tag and arity, and I did not know that
/// when I wrote them.
///
/// This asserts sizes as a measured property of the corpus. It proposes no size
/// rule for `list_ptrs` and takes no position on one.
#[test]
fn the_identified_shapes_are_not_unique() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    const IDENTIFIED: [(u8, u8); 6] = [(4, 2), (7, 3), (0, 3), (1, 1), (2, 1), (2, 2)];

    let mut totals: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut signatures: std::collections::BTreeMap<String, BTreeSet<String>> =
        std::collections::BTreeMap::new();
    let mut sizes: std::collections::BTreeMap<String, std::collections::BTreeMap<u16, usize>> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        for object in &objects {
            if !IDENTIFIED.contains(&(object.tag, object.other)) {
                continue;
            }
            let key = format!("tag {} arity {}", object.tag, object.other);
            *totals.entry(key.clone()).or_default() += 1;
            *sizes
                .entry(key.clone())
                .or_default()
                .entry(object.cs_sz)
                .or_default() += 1;

            let signature: Vec<String> = (0..usize::from(object.other))
                .map(|slot| {
                    let word = word_at(bytes, object.off + 8 + 8 * slot);
                    match resolve(word) {
                        Some(child) => {
                            let child = at.get(&child).expect("resolved above");
                            format!("{}/{}", child.tag, child.other)
                        }
                        None => "scalar".to_owned(),
                    }
                })
                .collect();
            signatures
                .entry(key)
                .or_default()
                .insert(signature.join("|"));
        }
    }

    if !prelude_loaded {
        assert!(
            totals.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    assert_eq!(
        totals
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect::<Vec<_>>(),
        vec![
            ("tag 0 arity 3".to_owned(), 5553),
            ("tag 1 arity 1".to_owned(), 1912),
            ("tag 2 arity 1".to_owned(), 78),
            ("tag 2 arity 2".to_owned(), 1955),
            ("tag 4 arity 2".to_owned(), 2537),
            ("tag 7 arity 3".to_owned(), 12912),
        ],
        "how many objects in the corpus carry each shape this file identifies - \
         against the tens this chain examined"
    );

    // The weak measure, pinned but not leaned on.
    assert_eq!(
        signatures
            .iter()
            .map(|(k, v)| (k.clone(), v.len()))
            .collect::<Vec<_>>(),
        vec![
            ("tag 0 arity 3".to_owned(), 37),
            ("tag 1 arity 1".to_owned(), 8),
            ("tag 2 arity 1".to_owned(), 8),
            ("tag 2 arity 2".to_owned(), 15),
            ("tag 4 arity 2".to_owned(), 3),
            ("tag 7 arity 3".to_owned(), 68),
        ],
        "field signatures per shape. This is the WEAK measure: one type's fields \
         legitimately hold different subtypes, so 68 at `(7, 3)` is what one \
         type looks like and not evidence of sixty-eight"
    );

    // The strong one: two sizes at one tag and arity is two layouts.
    let by_size: Vec<(String, Vec<u16>)> = sizes
        .iter()
        .map(|(k, v)| (k.clone(), v.keys().copied().collect()))
        .collect();
    assert_eq!(
        by_size,
        vec![
            ("tag 0 arity 3".to_owned(), vec![32, 40]),
            ("tag 1 arity 1".to_owned(), vec![16, 24]),
            ("tag 2 arity 1".to_owned(), vec![16]),
            ("tag 2 arity 2".to_owned(), vec![24, 32]),
            ("tag 4 arity 2".to_owned(), vec![24, 32]),
            ("tag 7 arity 3".to_owned(), vec![40, 48]),
        ],
        "stored sizes per shape. Two distinct sizes at one tag and arity is two \
         different scalar-area widths - two LAYOUTS, which cannot be one type"
    );
    assert_eq!(
        by_size.iter().filter(|(_, s)| s.len() > 1).count(),
        5,
        "five of the six shapes this file identifies carry two layouts, so the \
         tag and arity never identified anything. Where an identification was \
         right it was the SIZE and the field types carrying it"
    );

    // Anti-vacuity: a uniqueness audit over one object per shape proves nothing.
    assert!(
        totals.values().all(|&count| count > 50),
        "each shape needs a population before its uniqueness can be tested"
    );
}

/// The triples' SECOND name field, read at last - and it is nothing like the
/// first.
///
/// `c0a4f175` pinned field 1 by constructor - 61 and 50 over the 111 distinct
/// triples - and never read a name. I named this set as unopened in that
/// commit's own bead comment and then spent four waves on audits instead. This
/// opens it.
///
/// UNITS FIRST, since `88fb5754` was a whole wave lost to leaving them
/// implicit. The 51 and the 20 count DISTINCT OBJECTS; the 61, 50 and 111 count
/// USES, one per distinct triple. Both bases appear here on purpose, and both
/// are named in every assertion that carries them.
///
/// FIELD 1 IS NOT FIELD 0, in every dimension available:
///
///                     field 0 (`3373af3b`)      field 1 (here)
///   distinct objects  31                        51
///   distinct roots    ONE, `_uniq`              20
///   link kinds        one - numbered only       both, 61 and 50
///   components        all two                   61 one, 50 two
///
/// THE COMPONENT COUNT TRACKS THE LINK KIND EXACTLY - 61 single-component and
/// 61 string links, 50 two-component and 50 numbered links. That is not
/// automatic: a string link may carry a multi-component prefix and a numbered
/// link may sit on the anonymous name, so both correlations could have failed
/// and neither does.
///
/// This comparison has discriminating power, which is the check `f2da5b0e`
/// added and which I now run before claiming a difference: field 1's root count
/// is 20, so "one root like field 0" was reachable and is not what the corpus
/// says.
///
/// THE SPELLINGS ARE THE FRAGILE PART, flagged as at `aec3efd1` and `3373af3b`.
/// The 20 roots come from reading string payloads with the walker in this file,
/// which I have had to correct once. The counts of DISTINCT roots and the
/// correlations above do not depend on any byte of that decoding being right.
#[test]
fn the_triple_second_field_names() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut objects_seen: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut uses = 0usize;
    let mut kinds: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut components: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();
    let mut roots: BTreeSet<String> = BTreeSet::new();
    let mut correlated = 0usize;

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        // Arrays deduplicated, then triples deduplicated - the `c0a4f175` basis.
        let mut arrays: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(array) = resolve(word_at(bytes, record + 8 + 8 * 2)) {
                arrays.insert(array);
            }
        }
        let mut triples: BTreeSet<usize> = BTreeSet::new();
        for array in arrays {
            for i in 0..word_at(bytes, array + 8) {
                if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                    && shape(element) == Some((0, 3))
                {
                    triples.insert(element);
                }
            }
        }

        for triple in triples {
            let word = word_at(bytes, triple + 8 + 8);
            let link = resolve(word).expect("field 1 is a pointer");
            uses += 1;
            objects_seen.insert((index, link));

            let object = at.get(&link).expect("resolved above");
            let kind = format!("tag {} arity {}", object.tag, object.other);
            *kinds.entry(kind.clone()).or_default() += 1;

            // Components, from the production decoder's rendering.
            let name = DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(word)
                .unwrap_or_else(|e| panic!("{module}: field 1 must be a Name: {e}"))
                .to_display_string();
            let parts = name.split('.').count();
            *components.entry(parts).or_default() += 1;
            roots.insert(name.split('.').next().unwrap_or_default().to_owned());

            // The correlation: one component with a string link, two with a
            // numbered link. Neither is automatic.
            if (parts == 1) == (object.tag == 1) {
                correlated += 1;
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(uses, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    // DISTINCT OBJECTS.
    assert_eq!(
        objects_seen.len(),
        51,
        "distinct field-1 name OBJECTS - the 51 `c0a4f175` pins"
    );
    assert_eq!(
        roots.len(),
        20,
        "and 20 distinct root components among them, against field 0's ONE"
    );

    // USES, one per distinct triple.
    assert_eq!(uses, 111, "USES, one per distinct triple");
    assert_eq!(
        kinds.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 2".to_owned(), 61),
            ("tag 2 arity 2".to_owned(), 50),
        ],
        "by link kind, per use - the 61 and 50 `c0a4f175` pins, so this cell \
         reconciles with a landed total on the same basis"
    );
    assert_eq!(
        components.into_iter().collect::<Vec<_>>(),
        vec![(1, 61), (2, 50)],
        "and by component count, per use"
    );
    assert_eq!(
        correlated, uses,
        "the component count tracks the link kind EXACTLY - a string link may \
         carry a multi-component prefix and a numbered link may sit on the \
         anonymous name, so both correlations could have failed and neither \
         does"
    );

    // Discriminating power, checked before the difference is claimed.
    assert!(
        roots.len() > 1,
        "field 1 having many roots is only a difference from field 0 if more \
         than one root was reachable here"
    );
}

/// The triples' third field: the ranking INVERTS between the two bases.
///
/// `c0a4f175` pinned these expressions per USE - 26, 2, 26, 21, 13, 23 over the
/// 111 distinct triples - and never on the object basis. That is the same units
/// gap that reddened `f2da5b0e`, sitting unexamined in a landed cell, so both
/// bases are measured here and both are named.
///
///   shape        uses  objects
///   tag 3 / 1      26        3
///   tag 1 / 1      26        4
///   tag 4 / 2      21        8
///   tag 5 / 2      13       11
///   tag 7 / 3      23       21
///   tag 10 / 2      2        2
///
/// PER USE THE TWO ARITY-ONE SHAPES TIE AT THE TOP; PER OBJECT THEY ARE THE
/// SMALLEST GROUPS. Twenty-six uses of `tag 3` come from three objects, while
/// twenty-three uses of `tag 7` come from twenty-one. Sharing is concentrated
/// in the simple expressions and almost absent from the complex ones.
///
/// That is not a small-sample artefact - 26 uses against 3 objects and 23
/// against 21 are both substantial - and it is what a compacted region does:
/// identical subterms are shared, and a leaf is far more likely to be identical
/// to another leaf than a three-field node is to another three-field node. It
/// is also exactly the fact a per-use histogram hides, which is why reading
/// `c0a4f175`'s row as a description of the value set would have inverted the
/// ranking.
///
/// SIZES ARE ASSERTED HERE, and `2baabd20` is why. I spent thirteen waves
/// avoiding sizes because `daaaabe2` refuted one as a RULE for `list_ptrs`, and
/// that audit showed size is the strong characteriser and tag-with-arity the
/// weak one. Three sizes appear across these six shapes. No rule is proposed
/// and none is implied.
///
/// Depth and node counts are pinned as distributions over the 49 objects,
/// summing to 49 by construction so a miscount cannot hide in either.
#[test]
fn the_triple_third_field_expressions() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    // Which slots of an Expr constructor are themselves expressions.
    fn expression_children(tag: u8) -> &'static [usize] {
        match tag {
            5 => &[0, 1],
            6 | 7 => &[1, 2],
            8 => &[1, 2, 3],
            10 => &[1],
            11 => &[2],
            _ => &[],
        }
    }

    let mut per_use: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut per_object: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut sizes: std::collections::BTreeMap<u16, usize> = std::collections::BTreeMap::new();
    let mut depths: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    let mut nodes: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    let mut objects_total = 0usize;
    let mut decoded = 0usize;

    for (module, bytes) in &modules {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let described = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut arrays: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(array) = resolve(word_at(bytes, record + 8 + 8 * 2)) {
                arrays.insert(array);
            }
        }
        let mut triples: BTreeSet<usize> = BTreeSet::new();
        for array in arrays {
            for i in 0..word_at(bytes, array + 8) {
                if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                    && shape(element) == Some((0, 3))
                {
                    triples.insert(element);
                }
            }
        }

        // Per USE, then deduplicate for the object basis.
        let mut distinct: BTreeSet<usize> = BTreeSet::new();
        for triple in triples {
            let word = word_at(bytes, triple + 8 + 8 * 2);
            let expression = resolve(word).expect("field 2 is a pointer");
            *per_use.entry(described(expression)).or_default() += 1;
            distinct.insert(expression);
        }

        for expression in distinct {
            objects_total += 1;
            *per_object.entry(described(expression)).or_default() += 1;
            *sizes
                .entry(at.get(&expression).expect("resolved").cs_sz)
                .or_default() += 1;
            DeclDecoder::new(&view, WalkBudget::default())
                .decode_expr(word_at_pointer(bytes, base, expression))
                .unwrap_or_else(|e| panic!("{module}: field 2 must be an Expr: {e}"));
            decoded += 1;

            // Depth and node count over expression children only.
            let mut seen: BTreeSet<usize> = BTreeSet::new();
            let mut deepest = 0usize;
            let mut stack = vec![(expression, 1usize)];
            while let Some((node, depth)) = stack.pop() {
                if !seen.insert(node) {
                    continue;
                }
                deepest = deepest.max(depth);
                let tag = at.get(&node).expect("a walked object").tag;
                for &slot in expression_children(tag) {
                    if let Some(child) = resolve(word_at(bytes, node + 8 + 8 * slot)) {
                        stack.push((child, depth + 1));
                    }
                }
            }
            *depths.entry(deepest).or_default() += 1;
            *nodes.entry(seen.len()).or_default() += 1;
        }
    }

    if !prelude_loaded {
        assert_eq!(
            objects_total, 0,
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    // Both bases, named.
    assert_eq!(
        per_use.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 1".to_owned(), 26),
            ("tag 10 arity 2".to_owned(), 2),
            ("tag 3 arity 1".to_owned(), 26),
            ("tag 4 arity 2".to_owned(), 21),
            ("tag 5 arity 2".to_owned(), 13),
            ("tag 7 arity 3".to_owned(), 23),
        ],
        "per USE, one per distinct triple - `c0a4f175`'s row, reconciled"
    );
    assert_eq!(
        per_object
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect::<Vec<_>>(),
        vec![
            ("tag 1 arity 1".to_owned(), 4),
            ("tag 10 arity 2".to_owned(), 2),
            ("tag 3 arity 1".to_owned(), 3),
            ("tag 4 arity 2".to_owned(), 8),
            ("tag 5 arity 2".to_owned(), 11),
            ("tag 7 arity 3".to_owned(), 21),
        ],
        "per OBJECT - never pinned before, and the ranking INVERTS. Twenty-six \
         uses of `tag 3` come from three objects; twenty-three uses of `tag 7` \
         from twenty-one. Sharing is concentrated in the simple expressions"
    );
    assert_eq!(objects_total, 49, "the 49 distinct expressions");
    assert_eq!(decoded, 49, "each accepted by the production `decode_expr`");

    // Sizes, asserted because `2baabd20` showed they carry the weight.
    assert_eq!(
        sizes.into_iter().collect::<Vec<_>>(),
        vec![(24, 7), (32, 21), (48, 21)],
        "three sizes across the six shapes. No rule is proposed and none is \
         implied"
    );

    // Distributions that must sum to the population.
    assert_eq!(
        depths.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>(),
        vec![(1, 15), (2, 14), (3, 7), (4, 9), (5, 1), (6, 3)],
        "expression depth over the 49"
    );
    assert_eq!(
        depths.values().sum::<usize>(),
        objects_total,
        "the depth distribution must cover every object"
    );
    assert_eq!(
        nodes.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>(),
        vec![
            (1, 15),
            (2, 3),
            (3, 11),
            (4, 1),
            (5, 1),
            (6, 7),
            (8, 8),
            (10, 2),
            (11, 1)
        ],
        "and node count, counting each shared subterm once"
    );
    assert_eq!(nodes.values().sum::<usize>(), objects_total, "likewise");
}

/// The pointer word that reaches `offset`, for handing an object back to a
/// decoder that takes pointers rather than offsets.
fn word_at_pointer(_bytes: &[u8], base: u64, offset: usize) -> u64 {
    base + u64::try_from(offset).expect("in-range")
}

/// Which of this file's other histograms invert - and one of them does.
///
/// `d40f5aba` found the triples' third field ranked one way per use and the
/// opposite way per object. That raises an obvious question about every other
/// per-use histogram here, and the question had never been asked. Three are
/// checked on both bases:
///
///   field 0   uses 111, objects 31       one value; cannot invert
///   field 1   uses 61 / 50               objects 16 / 35     INVERTS
///   slot 4    uses 57 / 8 / 4            objects 56 / 8 / 4  does not
///
/// FIELD 1 INVERTS, AND I PINNED ONLY ITS USE BASIS AT `2a2d8234`. Per use the
/// string links dominate, 61 to 50; per object the numbered links do, 35 to 16.
/// The majority kind flips. That cell described the field from the use basis
/// alone - including the contrast with field 0's single kind - two waves after
/// `88fb5754` cost a wave to exactly this.
///
/// The 16 and 35 sum to the 51 distinct objects `2a2d8234` pins, so the object
/// basis reconciles with a landed total while the use basis it was compared
/// against does not describe the same thing.
///
/// FIELD 0 CANNOT INVERT AND THAT IS NOT A RESULT. It takes one value, so its
/// two bases are trivially in the same order - the single-valued case
/// `f2da5b0e` taught me to recognise, arriving in a ranking rather than a
/// comparison. It is reported so the audit's coverage is visible, not as
/// evidence of anything.
///
/// SLOT 4 GENUINELY DOES NOT INVERT: three values, substantial counts, and the
/// order holds. That matters for this cell's own honesty - an audit where every
/// multi-valued histogram inverted would not distinguish "I checked" from "the
/// check always says yes". One inverts, one does not, so the test discriminates.
#[test]
fn the_other_histograms_checked_for_inversion() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut uses: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut objects_by_kind: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut seen: BTreeSet<(usize, &'static str, usize)> = BTreeSet::new();

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let described = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }

        let mut record = |histogram: &'static str, offset: usize| {
            let kind = described(offset);
            *uses.entry(format!("{histogram}/use/{kind}")).or_default() += 1;
            if seen.insert((index, histogram, offset)) {
                *objects_by_kind
                    .entry(format!("{histogram}/object/{kind}"))
                    .or_default() += 1;
            }
        };

        // Slot 4: one use per head record, targets possibly shared.
        for &head in &records {
            if let Some(target) = resolve(word_at(bytes, head + 8 + 8 * 4)) {
                record("slot4", target);
            }
        }

        // Fields 0 and 1: one use per distinct triple.
        let mut arrays: BTreeSet<usize> = BTreeSet::new();
        for &head in &records {
            if let Some(array) = resolve(word_at(bytes, head + 8 + 8 * 2)) {
                arrays.insert(array);
            }
        }
        let mut triples: BTreeSet<usize> = BTreeSet::new();
        for array in arrays {
            for i in 0..word_at(bytes, array + 8) {
                if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                    && shape(element) == Some((0, 3))
                {
                    triples.insert(element);
                }
            }
        }
        for triple in triples {
            for (histogram, slot) in [("field0", 0usize), ("field1", 1)] {
                if let Some(target) = resolve(word_at(bytes, triple + 8 + 8 * slot)) {
                    record(histogram, target);
                }
            }
        }
    }

    if !prelude_loaded {
        assert!(uses.is_empty(), "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(
        uses.into_iter().collect::<Vec<_>>(),
        vec![
            ("field0/use/tag 2 arity 2".to_owned(), 111),
            ("field1/use/tag 1 arity 2".to_owned(), 61),
            ("field1/use/tag 2 arity 2".to_owned(), 50),
            ("slot4/use/tag 0 arity 2".to_owned(), 57),
            ("slot4/use/tag 1 arity 2".to_owned(), 8),
            ("slot4/use/tag 5 arity 1".to_owned(), 4),
        ],
        "each histogram per USE - the basis this file pinned for all three"
    );
    assert_eq!(
        objects_by_kind.into_iter().collect::<Vec<_>>(),
        vec![
            ("field0/object/tag 2 arity 2".to_owned(), 31),
            ("field1/object/tag 1 arity 2".to_owned(), 16),
            ("field1/object/tag 2 arity 2".to_owned(), 35),
            ("slot4/object/tag 0 arity 2".to_owned(), 56),
            ("slot4/object/tag 1 arity 2".to_owned(), 8),
            ("slot4/object/tag 5 arity 1".to_owned(), 4),
        ],
        "and per OBJECT. FIELD 1 INVERTS: 61 to 50 by use, 16 to 35 by object, \
         so the majority link kind flips. `2a2d8234` pinned only the use basis \
         and described the field from it"
    );

    // The reconciliation the use basis cannot offer.
    assert_eq!(
        16 + 35,
        51,
        "field 1's object counts sum to the 51 distinct name objects \
         `2a2d8234` pins"
    );

    // Coverage, and the guard that makes the audit discriminating.
    assert_eq!(
        (61 > 50, 16 < 35),
        (true, true),
        "field 1's order reverses between the bases"
    );
    assert_eq!(
        (57 > 8 && 8 > 4, 56 > 8 && 8 > 4),
        (true, true),
        "slot 4's does NOT - three values, substantial counts, same order. An \
         audit where every multi-valued histogram inverted could not \
         distinguish having checked from a check that always says yes"
    );
}

/// The slot-3 slots on both bases - and the mixed field inverts.
///
/// `6a4dba87` pinned these per-slot histograms over DISTINCT carriers and never
/// per use, which is the single-basis gap `0c7fd8af` found in field 1 - here in
/// the opposite direction, since that cell pinned uses and this one pinned
/// objects. Four of the slots take more than one value, so four can be checked:
///
///   seed / tag 3 / slot 1     use  boxed 0 x5, tag 1 x5   (tied)
///                             obj  boxed 0 x4, tag 1 x2
///   seed / tag 2 / slot 1     use  30, 2, 2   obj 29, 2, 2
///   interior / tag 2 / slot 1 use  5, 3, 1, 1, 1
///                             obj  5, 2, 1, 1, 1
///   interior / tag 3 / slot 1 use  5, 4        obj 5, 4
///
/// NO SLOT INVERTS ON THIS BASIS, AND THE FIRST VERSION OF THIS CELL SAID ONE
/// DID. It claimed the mixed field flipped its majority - a pointer five times
/// against boxed four per use, boxed four against a pointer twice per object.
/// The 5 and 4 is the per-RECORD count. This walk counts per NODE, and there
/// the field TIES at five and five, so there is no majority to flip. w173
/// caught the carrier totals; the slot rows were wrong for the same reason and
/// the headline rested on them.
///
/// What survives is weaker and is what the corpus supports: per object boxed
/// leads four to two, per node the two are tied, so the bases DISAGREE ABOUT
/// WHETHER THERE IS A LEADER. That is worth recording and is not an inversion.
///
/// Every row reconciles with `6a4dba87`'s own reference-and-object totals - 9
/// and 6 for the seed `tag 3`, 34 and 33 for the seed `tag 2`, 11 and 10 for
/// the interior `tag 2`, 9 and 9 for the interior `tag 3` - so the two bases
/// are tied to a landed pin rather than standing alone.
///
/// THREE OF THE FOUR DO NOT INVERT, which is what makes the check worth
/// running. An audit where everything inverted would not distinguish having
/// looked from a test that always fires, the guard `0c7fd8af` added and this
/// cell inherits.
///
/// The interior `tag 3` slot is identical on both bases because nothing there
/// is shared - nine references to nine objects - so it is the control that
/// shows the two bases can coincide.
#[test]
fn the_slot_three_slots_on_both_bases() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut per_use: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut per_object: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut carriers: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        for (name, population) in [("seed", true), ("interior", false)] {
            let mut references: Vec<usize> = Vec::new();
            for &node in &all {
                if seeds.contains(&node) != population {
                    continue;
                }
                if let Some(record) = resolve(word_at(bytes, node + 8))
                    && let Some(carrier) = resolve(word_at(bytes, record + 8 + 8 * 3))
                {
                    references.push(carrier);
                }
            }
            let distinct: BTreeSet<usize> = references.iter().copied().collect();

            let tally = |carrier: usize, into: &mut std::collections::BTreeMap<String, usize>| {
                let object = at.get(&carrier).expect("a walked object");
                for slot in 0..usize::from(object.other) {
                    let word = word_at(bytes, carrier + 8 + 8 * slot);
                    let value = match resolve(word) {
                        Some(child) => {
                            let child = at.get(&child).expect("resolved above");
                            format!("tag {} arity {}", child.tag, child.other)
                        }
                        None => format!("boxed {}", word >> 1),
                    };
                    *into
                        .entry(format!(
                            "{name}/tag {} arity {}/slot {slot}/{value}",
                            object.tag, object.other
                        ))
                        .or_default() += 1;
                }
                let key = format!("{name}/tag {} arity {}", object.tag, object.other);
                key
            };

            for &carrier in &references {
                let key = tally(carrier, &mut per_use);
                carriers.entry(key).or_default().0 += 1;
            }
            for &carrier in &distinct {
                let key = tally(carrier, &mut per_object);
                carriers.entry(key).or_default().1 += 1;
            }
        }
    }

    if !prelude_loaded {
        assert!(
            per_use.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    // The two bases tied to `6a4dba87`'s own reference-and-object totals.
    assert_eq!(
        carriers.into_iter().collect::<Vec<_>>(),
        vec![
            ("interior/tag 2 arity 3".to_owned(), (11, 10)),
            ("interior/tag 3 arity 3".to_owned(), (9, 9)),
            ("interior/tag 4 arity 2".to_owned(), (26, 24)),
            ("seed/tag 2 arity 3".to_owned(), (34, 33)),
            ("seed/tag 3 arity 3".to_owned(), (10, 6)),
            ("seed/tag 4 arity 2".to_owned(), (12, 11)),
        ],
        "references PER SPINE NODE, and objects. The object column is \
         `6a4dba87`'s exactly; the reference column is NOT, because that cell \
         counts one carrier per four-field RECORD and this walk counts one per \
         NODE. Two seed nodes share a record, so the seed references are 56 and \
         not 54, and they reconcile with the ledger's 102 spine nodes rather \
         than with a record count"
    );

    // The mixed field, on both bases.
    let use_of = |key: &str| per_use.get(key).copied().unwrap_or_default();
    let object_of = |key: &str| per_object.get(key).copied().unwrap_or_default();

    assert_eq!(
        (
            use_of("seed/tag 3 arity 3/slot 1/tag 1 arity 2"),
            use_of("seed/tag 3 arity 3/slot 1/boxed 0"),
        ),
        (5, 5),
        "per NODE the mixed field TIES - a pointer five times and boxed five \
         times. This cell first pinned 5 and 4, which is the per-RECORD count, \
         and claimed the majority flipped between the bases. On the basis this \
         walk uses there is no majority to flip"
    );
    assert_eq!(
        (
            object_of("seed/tag 3 arity 3/slot 1/boxed 0"),
            object_of("seed/tag 3 arity 3/slot 1/tag 1 arity 2"),
        ),
        (4, 2),
        "per OBJECT it is boxed four times against a pointer twice. Boxed \
         leads here and ties there, so the two bases DISAGREE about whether \
         there is a leader - which is weaker than an inversion and is what the \
         corpus supports"
    );

    // The three that do not invert, which is what makes the check meaningful.
    assert_eq!(
        (
            use_of("seed/tag 2 arity 3/slot 1/boxed 0"),
            object_of("seed/tag 2 arity 3/slot 1/boxed 0"),
        ),
        (30, 29),
        "the seed `tag 2` slot leads on both bases"
    );
    assert_eq!(
        (
            use_of("interior/tag 2 arity 3/slot 1/boxed 0"),
            object_of("interior/tag 2 arity 3/slot 1/boxed 0"),
        ),
        (5, 5),
        "and the interior `tag 2` slot likewise"
    );
    assert_eq!(
        (
            use_of("interior/tag 3 arity 3/slot 1/boxed 0"),
            object_of("interior/tag 3 arity 3/slot 1/boxed 0"),
        ),
        (5, 5),
        "the interior `tag 3` slot is identical on both bases because nothing \
         there is shared - nine references to nine objects - so it is the \
         control showing the two bases CAN coincide"
    );
}

/// The two shared seed records, and the one base-rate check that SURVIVES.
///
/// `bd0266d2` pins the seed spine's record excess as 2 and never says which
/// records - the "a histogram entry is not an object" gap `1cc74dd0` closed for
/// the array hub. An excess of 2 is also ambiguous: one record shared three
/// ways, or two shared twice. It is two shared twice; the refcounts are 52 ones
/// and 2 twos.
///
/// ALL FOUR HOLDERS HAVE A `tag 4 arity 1` TAIL, and that is six of the
/// fifty-six seed nodes. Four draws landing entirely inside a class holding
/// just over a tenth of the population is roughly one chance in seven thousand
/// six hundred if nothing connects them.
///
/// THAT IS THE FIRST TIME THIS ARITHMETIC HAS SUPPORTED A CLAIM RATHER THAN
/// DISSOLVING ONE. `1cc74dd0` computed the same check and found thirteen of
/// thirteen inside an eighty-three per cent class - about one in eleven, and
/// nothing. `1006bd18` found one of three categorical zeros drawn from a
/// population of one. Here the base rate makes the observation surprising
/// instead of expected, which is what the check exists to distinguish.
///
/// It is a base-rate sanity check and not a significance test: it assumes the
/// four draws are independent, which is exactly what a shared record might make
/// false. The honest reading is that the four holders are not a random four,
/// not that a mechanism has been identified.
///
/// The records' own slots are pinned beside the unshared profile so the
/// comparison has somewhere to stand. Both shared records carry a `tag 5` at
/// slot 2, where the unshared population is mostly `tag 7` - ten of
/// fifty-two - but TWO samples support no such claim and none is made.
///
/// Addresses carry a guard at the address, the `d7518917` pattern.
#[test]
fn the_shared_seed_records() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut refcounts: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    let mut shared: Vec<usize> = Vec::new();
    let mut shared_slots: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut unshared_slots: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut holder_tails: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut all_tails: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut seed_nodes = 0usize;

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let described = |word: u64| -> String {
            match resolve(word) {
                Some(child) => {
                    let child = at.get(&child).expect("resolved above");
                    format!("tag {} arity {}", child.tag, child.other)
                }
                None => format!("boxed {}", word >> 1),
            }
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        seed_nodes += seeds.len();

        // Which four-field record each seed node carries, and how many carry each.
        let mut holders: std::collections::BTreeMap<usize, Vec<usize>> =
            std::collections::BTreeMap::new();
        for &node in &seeds {
            if let Some(record) = resolve(word_at(bytes, node + 8)) {
                holders.entry(record).or_default().push(node);
            }
            *all_tails
                .entry(described(word_at(bytes, node + 16)))
                .or_default() += 1;
        }

        for (&record, nodes) in &holders {
            *refcounts.entry(nodes.len()).or_default() += 1;
            let into = if nodes.len() > 1 {
                shared.push(record);
                // The guard, at the address about to be pinned.
                assert_eq!(
                    shape(record),
                    Some((0, 4)),
                    "a pinned shared record must still be the four-field shape"
                );
                assert_eq!(
                    holders.get(&record).map(Vec::len),
                    Some(nodes.len()),
                    "and must still carry exactly that many holders"
                );
                for &node in nodes {
                    *holder_tails
                        .entry(described(word_at(bytes, node + 16)))
                        .or_default() += 1;
                }
                &mut shared_slots
            } else {
                &mut unshared_slots
            };
            for slot in 0..4usize {
                *into
                    .entry(format!(
                        "slot {slot}/{}",
                        described(word_at(bytes, record + 8 + 8 * slot))
                    ))
                    .or_default() += 1;
            }
        }
    }

    if !prelude_loaded {
        assert!(
            shared.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    // Two shared twice, not one shared three ways.
    assert_eq!(
        refcounts.into_iter().collect::<Vec<_>>(),
        vec![(1, 52), (2, 2)],
        "the excess of 2 `bd0266d2` pins is TWO records shared TWICE, not one \
         shared three ways - an excess alone cannot say which"
    );
    shared.sort_unstable();
    assert_eq!(
        shared,
        vec![0x2afdd0, 0x2b4998],
        "the shared records, locatable rather than only counted"
    );

    // The finding, with its base rate beside it.
    assert_eq!(
        holder_tails.into_iter().collect::<Vec<_>>(),
        vec![("tag 4 arity 1".to_owned(), 4)],
        "all four holders have the same tail shape"
    );
    assert_eq!(
        all_tails.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 0 arity 2".to_owned(), 44),
            ("tag 4 arity 1".to_owned(), 6),
            ("tag 5 arity 1".to_owned(), 6),
        ],
        "against six of the fifty-six seed nodes. Four draws landing entirely \
         inside a class holding just over a tenth is roughly one in seven \
         thousand six hundred - so unlike `1cc74dd0`'s thirteen-of-thirteen at \
         one in eleven, the base rate makes this surprising rather than \
         expected. It is a sanity check assuming independence, not a \
         significance test"
    );
    assert_eq!(seed_nodes, 56, "the population the base rate is over");

    // The slot profiles, with no claim drawn from two samples.
    assert_eq!(
        shared_slots.into_iter().collect::<Vec<_>>(),
        vec![
            ("slot 0/tag 2 arity 2".to_owned(), 2),
            ("slot 1/tag 2 arity 2".to_owned(), 2),
            ("slot 2/tag 5 arity 2".to_owned(), 2),
            ("slot 3/tag 3 arity 3".to_owned(), 1),
            ("slot 3/tag 4 arity 2".to_owned(), 1),
        ],
        "the two shared records' own slots"
    );
    assert_eq!(
        unshared_slots.into_iter().collect::<Vec<_>>(),
        vec![
            ("slot 0/tag 2 arity 2".to_owned(), 52),
            ("slot 1/tag 1 arity 2".to_owned(), 2),
            ("slot 1/tag 2 arity 2".to_owned(), 50),
            ("slot 2/tag 1 arity 1".to_owned(), 4),
            ("slot 2/tag 4 arity 2".to_owned(), 9),
            ("slot 2/tag 5 arity 2".to_owned(), 10),
            ("slot 2/tag 7 arity 3".to_owned(), 29),
            ("slot 3/tag 2 arity 3".to_owned(), 34),
            ("slot 3/tag 3 arity 3".to_owned(), 8),
            ("slot 3/tag 4 arity 2".to_owned(), 10),
        ],
        "and the unshared profile beside them. Both shared records carry a \
         `tag 5` at slot 2 where the unshared population is mostly `tag 7`, but \
         TWO samples support no such claim and none is made"
    );
}

/// The six `tag 4 arity 1` tails - uniform, and not self-references.
///
/// `241893a7` opened the `(0, 2)` and `(5, 1)` spine tails and pinned `(4, 1)`
/// as a count only. `a23b6daa` then found all four shared-record holders have
/// exactly this tail, four of the six, so these are the objects that finding
/// points at and nobody has looked inside them.
///
/// THEY ARE UNIFORM. Six references to six objects, no sharing, one size, and
/// every one wraps a single four-field record. The four implicated by
/// `a23b6daa` and the two that are not have IDENTICAL profiles.
///
/// SO THAT COMPARISON HAS NO DISCRIMINATING POWER, and this cell says so rather
/// than reporting "they are the same" as a result. The property is uniform
/// across all six, so it could not have separated them however they were
/// arranged - the vacuity `f2da5b0e` found in one of four earlier "not special"
/// findings, checked here before the claim instead of three waves after it.
/// Nothing about these objects explains why four of six hold shared records.
///
/// THE INNER RECORD IS NEVER THE NODE'S OWN RECORD - zero of six. That zero is
/// worth its denominator, per `1006bd18`: it is not surprising in itself, since
/// an arbitrary pick from about a hundred records would miss almost always.
/// What it does is refute a specific reading. The obvious guess for a one-field
/// wrapper sitting on a node is that it points back at that node's own record,
/// which would give six of six; it gives none, so these wrap something else and
/// the six inner records are six further distinct objects.
///
/// The nodes' own records reproduce `a23b6daa`'s two shared records and their
/// exact holders - `0x2afdd0` from two nodes and `0x2b4998` from two others -
/// which is a free cross-check that this cell and that one are walking the same
/// structure.
#[test]
fn the_six_tag_four_tails() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut references = 0usize;
    let mut distinct: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut inner_shapes: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut inner_distinct: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut implicated: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut unimplicated: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut inner_is_own_record = 0usize;
    let mut shared_records: BTreeSet<usize> = BTreeSet::new();
    let mut holders_of_shared = 0usize;

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let described = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }

        // Which seed nodes share a four-field record - `a23b6daa`'s finding.
        let mut holders: std::collections::BTreeMap<usize, Vec<usize>> =
            std::collections::BTreeMap::new();
        for &node in &seeds {
            if let Some(record) = resolve(word_at(bytes, node + 8)) {
                holders.entry(record).or_default().push(node);
            }
        }
        let sharing: BTreeSet<usize> = holders
            .iter()
            .filter(|(_, nodes)| nodes.len() > 1)
            .flat_map(|(record, nodes)| {
                shared_records.insert(*record);
                nodes.iter().copied()
            })
            .collect();
        holders_of_shared += sharing.len();

        for &node in &seeds {
            let Some(tail) = resolve(word_at(bytes, node + 16)) else {
                continue;
            };
            if shape(tail) != Some((4, 1)) {
                continue;
            }
            references += 1;
            distinct.insert((index, tail));

            let inner = resolve(word_at(bytes, tail + 8)).expect("the wrapped field");
            *inner_shapes.entry(described(inner)).or_default() += 1;
            inner_distinct.insert((index, inner));

            let into = if sharing.contains(&node) {
                &mut implicated
            } else {
                &mut unimplicated
            };
            *into.entry(described(inner)).or_default() += 1;

            if resolve(word_at(bytes, node + 8)) == Some(inner) {
                inner_is_own_record += 1;
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(references, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    // Uniform, and unshared.
    assert_eq!(
        (references, distinct.len()),
        (6, 6),
        "six references to six objects - these wrappers are not shared"
    );
    assert_eq!(
        inner_shapes.into_iter().collect::<Vec<_>>(),
        vec![("tag 0 arity 4".to_owned(), 6)],
        "and every one wraps a four-field record"
    );
    assert_eq!(
        inner_distinct.len(),
        6,
        "six distinct inner records, one per wrapper"
    );

    // The comparison that cannot discriminate, said as such.
    assert_eq!(
        (
            implicated.into_iter().collect::<Vec<_>>(),
            unimplicated.into_iter().collect::<Vec<_>>(),
        ),
        (
            vec![("tag 0 arity 4".to_owned(), 4)],
            vec![("tag 0 arity 4".to_owned(), 2)],
        ),
        "the four `a23b6daa` implicates and the two it does not have IDENTICAL \
         profiles. The property is uniform across all six, so it could not have \
         separated them however they were arranged - this is a vacuous \
         comparison and is reported as one, not as a finding that they match"
    );

    // The zero, with what it is evidence against.
    assert_eq!(
        inner_is_own_record, 0,
        "the wrapped record is NEVER the node's own record. Not surprising in \
         itself - an arbitrary pick from about a hundred records would miss \
         almost always - but it refutes the obvious reading of a one-field \
         wrapper on a node as pointing back at that node's record, which would \
         give six of six"
    );

    // Free cross-check against `a23b6daa`.
    assert_eq!(
        (shared_records.len(), holders_of_shared),
        (2, 4),
        "two shared records between four holders, reproducing `a23b6daa` from \
         this cell's own walk"
    );
}

/// The six inner records are a THIRD population - and size does not separate
/// them either.
///
/// I closed `19eef9ff` by calling these "distinct from every record population
/// already characterised". What that cell MEASURED was only that each differs
/// from its own node's record, which is a much weaker fact. The claim was
/// written ahead of its evidence; this is the measurement, and it happens to
/// hold - none of the six is among the 54 seed records or the 46 interior ones.
/// Being right does not make the order of those two steps right.
///
/// THEY ARE NOT THE SAME KIND OF RECORD AT ALL, which is more than disjointness:
///
///              the six                 the known 100
///   slot 0     tag 1 arity 2, all      tag 2 arity 2, ALL
///   slot 2     tag 2 arity 2, all      -
///   slot 3     an ARRAY, all           tag 2/3, tag 3/3, tag 4/2 - never an array
///
/// Both contrasts are categorical and both survive a base rate. The known
/// hundred are `tag 2` at slot 0 at a rate of ONE, so zero of six is impossible
/// by chance; they hold an array at slot 3 at a rate of ZERO, so six of six is
/// equally so. This is not the population-of-one case `1006bd18` found.
///
/// AND THE SIZES ARE IDENTICAL - forty bytes on both sides. `2baabd20`
/// concluded that two sizes at one tag and arity mean two layouts and that size
/// is the strong characteriser where tag and arity are weak. That stands, and
/// this qualifies it: HERE THE TAG, THE ARITY AND THE SIZE ALL AGREE and the
/// types still differ. Size is stronger than tag-with-arity and it is not
/// sufficient either. Only reading the fields separated these.
///
/// So the file now knows three disjoint four-field-record populations sharing
/// one header triple, where `2baabd20` had shown five shapes carrying two
/// layouts apiece. Nothing here proposes a rule.
#[test]
fn the_six_inner_records_are_a_third_population() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut inner_total = 0usize;
    let mut in_seed = 0usize;
    let mut in_interior = 0usize;
    let mut in_neither = 0usize;
    let mut known_total = 0usize;
    let mut inner_slots: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut known_slots: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut inner_sizes: BTreeSet<u16> = BTreeSet::new();
    let mut known_sizes: BTreeSet<u16> = BTreeSet::new();

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let described = |word: u64| -> String {
            match resolve(word) {
                Some(child) => {
                    let child = at.get(&child).expect("resolved above");
                    format!("tag {} arity {}", child.tag, child.other)
                }
                None => format!("boxed {}", word >> 1),
            }
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }

        // The two known record populations.
        let mut seed_records: BTreeSet<usize> = BTreeSet::new();
        let mut interior_records: BTreeSet<usize> = BTreeSet::new();
        for &node in &all {
            if let Some(record) = resolve(word_at(bytes, node + 8)) {
                if seeds.contains(&node) {
                    seed_records.insert(record);
                } else {
                    interior_records.insert(record);
                }
            }
        }
        for &record in seed_records.iter().chain(interior_records.iter()) {
            known_total += 1;
            known_sizes.insert(at.get(&record).expect("resolved").cs_sz);
            for slot in 0..4usize {
                *known_slots
                    .entry(format!(
                        "slot {slot}/{}",
                        described(word_at(bytes, record + 8 + 8 * slot))
                    ))
                    .or_default() += 1;
            }
        }

        // The six the `tag 4` wrappers point at.
        let mut inner: BTreeSet<usize> = BTreeSet::new();
        for &node in &seeds {
            if let Some(tail) = resolve(word_at(bytes, node + 16))
                && shape(tail) == Some((4, 1))
                && let Some(record) = resolve(word_at(bytes, tail + 8))
            {
                inner.insert(record);
            }
        }
        for &record in &inner {
            inner_total += 1;
            inner_sizes.insert(at.get(&record).expect("resolved").cs_sz);
            if seed_records.contains(&record) {
                in_seed += 1;
            } else if interior_records.contains(&record) {
                in_interior += 1;
            } else {
                in_neither += 1;
            }
            for slot in 0..4usize {
                *inner_slots
                    .entry(format!(
                        "slot {slot}/{}",
                        described(word_at(bytes, record + 8 + 8 * slot))
                    ))
                    .or_default() += 1;
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(inner_total, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    // A third population, measured rather than asserted.
    assert_eq!(
        (inner_total, in_seed, in_interior, in_neither),
        (6, 0, 0, 6),
        "none of the six is among the 54 seed records or the 46 interior ones - \
         the claim `19eef9ff` closed with, now actually measured"
    );
    assert_eq!(
        known_total, 100,
        "the two known populations it is disjoint from"
    );

    // Not the same kind of record: two categorical contrasts.
    assert_eq!(
        inner_slots.into_iter().collect::<Vec<_>>(),
        vec![
            ("slot 0/tag 1 arity 2".to_owned(), 6),
            ("slot 1/tag 1 arity 1".to_owned(), 2),
            ("slot 1/tag 4 arity 2".to_owned(), 3),
            ("slot 1/tag 5 arity 2".to_owned(), 1),
            ("slot 2/tag 2 arity 2".to_owned(), 6),
            ("slot 3/tag 246 arity 0".to_owned(), 6),
        ],
        "the six: a string-link name, a varying field, a numbered name, and an \
         ARRAY"
    );
    assert_eq!(
        known_slots
            .iter()
            .filter(|(key, _)| key.starts_with("slot 0/") || key.starts_with("slot 3/"))
            .map(|(key, value)| (key.clone(), *value))
            .collect::<Vec<_>>(),
        vec![
            ("slot 0/tag 2 arity 2".to_owned(), 100),
            ("slot 3/tag 2 arity 3".to_owned(), 45),
            ("slot 3/tag 3 arity 3".to_owned(), 18),
            ("slot 3/tag 4 arity 2".to_owned(), 37),
        ],
        "against the known hundred, which are `tag 2` at slot 0 at a rate of \
         ONE and hold an array at slot 3 at a rate of ZERO. So zero of six and \
         six of six are both impossible by chance - not the population-of-one \
         case `1006bd18` found"
    );

    // The qualification to `2baabd20`.
    assert_eq!(
        (
            inner_sizes.iter().copied().collect::<Vec<_>>(),
            known_sizes.iter().copied().collect::<Vec<_>>(),
        ),
        (vec![40], vec![40]),
        "the sizes are IDENTICAL. `2baabd20` showed size is the strong \
         characteriser where tag and arity are weak; here tag, arity and size \
         all agree and the types still differ, so size is not sufficient \
         either. Only reading the fields separated these"
    );
}

/// The six inner records' arrays - a parallel structure, and a disjointness
/// that proves less than it looks.
///
/// `8a1b98cb` left these unread and said so as UNMEASURED, which is the
/// correction that cell made to its own predecessor. Measured now:
///
///   6 references to 5 distinct arrays, one shared by two records
///   none of the 5 is among the 51 slot-2 arrays or the 42 slot-3 arrays
///   every one has length 2
///   10 elements, all the three-field triple shape, 10 distinct, none boxed
///   none of the 10 is among the 111 known triples
///
/// SO THE `tag 4` WRAPPERS LEAD INTO A PARALLEL COPY OF THE SAME STRUCTURE:
/// four-field record, then an array, then triples - the same shapes at every
/// level, and disjoint objects at every level.
///
/// THE DISJOINTNESS IS THE WEAK HALF AND I AM SAYING SO RATHER THAN LEADING
/// WITH IT. `2baabd20` measured 5,553 objects of the triple shape across this
/// corpus. The 111 already characterised are about two per cent of them, so ten
/// draws landing outside that set is the EXPECTED outcome under no hypothesis
/// at all - roughly four chances in five. The same argument applies to the
/// arrays. Reporting "disjoint at every level" as the finding would be the
/// mistake `1cc74dd0` caught in thirteen-of-thirteen, three levels deeper.
///
/// WHAT CARRIES WEIGHT IS THE PARALLELISM, which no base rate explains away:
/// the same three shapes in the same nesting, every array the same length, and
/// sharing present at the array level exactly as it is in the characterised
/// structure. That is a description of arrangement, not of membership, and
/// arrangement is what disjointness cannot speak to.
///
/// This is the fourth distinct use of the base-rate check in this file, and the
/// second where it limits a result of mine rather than dissolving or supporting
/// one.
#[test]
fn the_six_inner_record_arrays() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut references = 0usize;
    let mut arrays: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut refcounts: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    let mut in_slot2 = 0usize;
    let mut in_slot3 = 0usize;
    let mut lengths: std::collections::BTreeMap<u64, usize> = std::collections::BTreeMap::new();
    let mut element_shapes: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut elements: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut in_known_triples = 0usize;
    let mut known_triples = 0usize;
    let mut triple_shape_total = 0usize;

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        // The corpus-wide triple-shape population, for the base rate.
        triple_shape_total += objects
            .iter()
            .filter(|object| (object.tag, object.other) == (0, 3))
            .count();

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }

        // The characterised populations this is compared against.
        let mut slot2_arrays: BTreeSet<usize> = BTreeSet::new();
        let mut triples: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(array) = resolve(word_at(bytes, record + 8 + 8 * 2)) {
                slot2_arrays.insert(array);
                for i in 0..word_at(bytes, array + 8) {
                    if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                        && shape(element) == Some((0, 3))
                    {
                        triples.insert(element);
                    }
                }
            }
        }
        known_triples += triples.len();

        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }
        let mut slot3_arrays: BTreeSet<usize> = BTreeSet::new();
        for &node in &all {
            if let Some(record) = resolve(word_at(bytes, node + 8))
                && let Some(carrier) = resolve(word_at(bytes, record + 8 + 8 * 3))
            {
                for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                    if shape(carrier) == Some((tag, arity))
                        && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                    {
                        slot3_arrays.insert(array);
                    }
                }
            }
        }

        // The six inner records, and their slot-3 arrays.
        let mut inner: BTreeSet<usize> = BTreeSet::new();
        for &node in &seeds {
            if let Some(tail) = resolve(word_at(bytes, node + 16))
                && shape(tail) == Some((4, 1))
                && let Some(record) = resolve(word_at(bytes, tail + 8))
            {
                inner.insert(record);
            }
        }
        let mut counts: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        for &record in &inner {
            if let Some(array) = resolve(word_at(bytes, record + 8 + 8 * 3)) {
                references += 1;
                arrays.insert((index, array));
                *counts.entry(array).or_default() += 1;
            }
        }
        for (&array, &count) in &counts {
            *refcounts.entry(count).or_default() += 1;
            if slot2_arrays.contains(&array) {
                in_slot2 += 1;
            }
            if slot3_arrays.contains(&array) {
                in_slot3 += 1;
            }
            let length = word_at(bytes, array + 8);
            *lengths.entry(length).or_default() += 1;
            for i in 0..length {
                let element =
                    resolve(word_at(bytes, array + 24 + 8 * i as usize)).expect("an element");
                let object = at.get(&element).expect("resolved above");
                *element_shapes
                    .entry(format!("tag {} arity {}", object.tag, object.other))
                    .or_default() += 1;
                elements.insert((index, element));
                if triples.contains(&element) {
                    in_known_triples += 1;
                }
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(references, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(
        (references, arrays.len()),
        (6, 5),
        "six references to five arrays"
    );
    assert_eq!(
        refcounts.into_iter().collect::<Vec<_>>(),
        vec![(1, 4), (2, 1)],
        "one of them shared by two records - sharing is present here exactly as \
         it is in the characterised structure"
    );
    assert_eq!(
        lengths.into_iter().collect::<Vec<_>>(),
        vec![(2, 5)],
        "every array has length 2"
    );
    assert_eq!(
        element_shapes.into_iter().collect::<Vec<_>>(),
        vec![("tag 0 arity 3".to_owned(), 10)],
        "and holds the three-field triple shape"
    );
    assert_eq!(elements.len(), 10, "ten distinct elements, none shared");

    // The weak half, with the base rate that weakens it.
    assert_eq!(
        (in_slot2, in_slot3, in_known_triples),
        (0, 0, 0),
        "none of the arrays is among the 51 slot-2 or 42 slot-3 arrays, and \
         none of the ten elements is among the known triples"
    );
    assert_eq!(known_triples, 111, "the triple population compared against");
    assert_eq!(
        triple_shape_total, 5553,
        "against 5,553 objects of that shape in the corpus, so the 111 are \
         about two per cent and ten draws landing outside them is the EXPECTED \
         outcome under no hypothesis - roughly four chances in five. The \
         disjointness is not the finding; the parallel arrangement is, and no \
         base rate speaks to arrangement"
    );
}

/// The ten are not the same kind of object as the 111 - and here size DOES
/// separate them.
///
/// `7e1ab465` called this "a parallel copy of the same structure" and noted the
/// shapes match at every level. The shapes do. The contents at this level do
/// not, and the phrase overstates what was measured - the skeleton is parallel,
/// the things hanging on it are a different kind:
///
///              the 111                    the ten
///   size       40                         32
///   field 0    tag 2 arity 2, ALL         tag 1 arity 2, all
///   field 1    a name, ALL                an ARRAY, all
///   field 2    six expression shapes      tag 0 arity 2 once, tag 5 arity 1 nine
///
/// EVERY COMPARISON GROUP SITS AT A RATE OF ONE, so all four contrasts are
/// decisive rather than suggestive. The 111 are `tag 2` at field 0, a name at
/// field 1 and forty bytes without exception; the ten are none of those without
/// exception. This is not the population-of-one case `1006bd18` found nor the
/// uniform-property case `f2da5b0e` found - the properties vary across the
/// union and agree perfectly within each side.
///
/// AND SIZE SEPARATES THEM, which is the complement to `8a1b98cb`. There, three
/// record populations shared tag, arity AND size, and only the fields told them
/// apart - so size was shown insufficient. Here the sizes differ, 32 against
/// 40, and size alone would have sufficed. Neither result generalises: size is
/// evidence when it differs and silence when it does not, which is all
/// `2baabd20` ever licensed.
///
/// The field-0 names are `Decidable` eight times and `EStateM` twice, against
/// `_uniq` for all 111. Those SPELLINGS are the fragile part, read with this
/// file's own string walker, flagged as at `aec3efd1` and `3373af3b`. The
/// structural contrast - a string link where the 111 have a numbered one -
/// needs no byte of that decoding.
#[test]
fn the_ten_triples_are_not_the_same_kind() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut sizes: std::collections::BTreeMap<String, BTreeSet<u16>> =
        std::collections::BTreeMap::new();
    let mut roots: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut overlap = 0usize;

    for (module, bytes) in &modules {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let described = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }

        // The 111.
        let mut known: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(array) = resolve(word_at(bytes, record + 8 + 8 * 2)) {
                for i in 0..word_at(bytes, array + 8) {
                    if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                        && shape(element) == Some((0, 3))
                    {
                        known.insert(element);
                    }
                }
            }
        }

        // The ten, through the `tag 4` wrappers.
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut ten: BTreeSet<usize> = BTreeSet::new();
        for &node in &seeds {
            if let Some(tail) = resolve(word_at(bytes, node + 16))
                && shape(tail) == Some((4, 1))
                && let Some(inner) = resolve(word_at(bytes, tail + 8))
                && let Some(array) = resolve(word_at(bytes, inner + 8 + 8 * 3))
            {
                for i in 0..word_at(bytes, array + 8) {
                    if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                        && shape(element) == Some((0, 3))
                    {
                        ten.insert(element);
                    }
                }
            }
        }
        overlap += known.intersection(&ten).count();

        for (label, group) in [("111", &known), ("ten", &ten)] {
            for &triple in group {
                *counts.entry(format!("{label}/population")).or_default() += 1;
                sizes
                    .entry(label.to_owned())
                    .or_default()
                    .insert(at.get(&triple).expect("resolved").cs_sz);
                for slot in 0..3usize {
                    let field = resolve(word_at(bytes, triple + 8 + 8 * slot))
                        .expect("a triple field is a pointer");
                    *counts
                        .entry(format!("{label}/field {slot}/{}", described(field)))
                        .or_default() += 1;
                }
                // Field 0's root component, via the production decoder.
                let name = DeclDecoder::new(&view, WalkBudget::default())
                    .decode_name(word_at(bytes, triple + 8))
                    .unwrap_or_else(|e| panic!("{module}: field 0 must be a Name: {e}"))
                    .to_display_string();
                *roots
                    .entry(format!(
                        "{label}/{}",
                        name.split('.').next().unwrap_or_default()
                    ))
                    .or_default() += 1;
            }
        }
    }

    if !prelude_loaded {
        assert!(
            counts.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    let get = |key: &str| counts.get(key).copied().unwrap_or_default();

    assert_eq!(
        (get("111/population"), get("ten/population"), overlap),
        (111, 10, 0),
        "the two populations and their overlap"
    );

    // Four categorical contrasts, each against a comparison group at rate one.
    assert_eq!(
        (
            get("111/field 0/tag 2 arity 2"),
            get("ten/field 0/tag 1 arity 2"),
        ),
        (111, 10),
        "field 0: the 111 are a numbered link WITHOUT EXCEPTION, the ten a \
         string link without exception"
    );
    assert_eq!(
        (
            get("111/field 1/tag 1 arity 2") + get("111/field 1/tag 2 arity 2"),
            get("ten/field 1/tag 246 arity 0"),
        ),
        (111, 10),
        "field 1: a name in all 111, an ARRAY in all ten"
    );
    assert_eq!(
        (
            get("ten/field 2/tag 5 arity 1"),
            get("ten/field 2/tag 0 arity 2"),
        ),
        (9, 1),
        "field 2: two shapes here, against the six the 111 admit"
    );

    // Size, which separates here and did not at `8a1b98cb`.
    assert_eq!(
        (
            sizes
                .get("111")
                .map(|s| s.iter().copied().collect::<Vec<_>>()),
            sizes
                .get("ten")
                .map(|s| s.iter().copied().collect::<Vec<_>>()),
        ),
        (Some(vec![40]), Some(vec![32])),
        "the sizes DIFFER, 40 against 32 - so size alone would have separated \
         these, where at `8a1b98cb` three record populations shared tag, arity \
         and size and only the fields told them apart. Size is evidence when it \
         differs and silence when it does not"
    );

    // The fragile part, flagged.
    assert_eq!(
        roots.into_iter().collect::<Vec<_>>(),
        vec![
            ("111/_uniq".to_owned(), 111),
            ("ten/Decidable".to_owned(), 8),
            ("ten/EStateM".to_owned(), 2),
        ],
        "field 0's root component. The SPELLINGS come from this file's own \
         string walker and are the fragile part; the structural contrast above \
         needs no byte of that decoding"
    );
}

/// The ten's field-1 arrays - and below them, objects of the 111's kind again.
///
/// `cae89f06` left these unread and said so as unmeasured. Measured:
///
///   10 references to 6 distinct arrays; four of the six are used twice
///   none of the 6 is among the 51 slot-2, 42 slot-3 or 5 inner-record arrays
///   lengths 1 four times and 2 twice - NOT uniform
///   8 elements, all the three-field shape, 8 distinct, none boxed
///   none of the 8 is among the ten or the 111
///
/// THE LENGTHS ARE NOT UNIFORM, which weakens "parallel" one step further.
/// `7e1ab465` found every array at the level above to be length 2 and called
/// the arrangement parallel; `cae89f06` had to qualify that once already when
/// the contents turned out to be a different kind. Here even the container
/// shape stops matching.
///
/// AND YET THE OBJECTS BELOW ARE THE 111'S KIND AGAIN:
///
///                 the 111    the ten    these 8
///   size          40         32         40
///   field 0       tag 2/2    tag 1/2    tag 2/2
///   field 1       a name     an ARRAY   a name
///
/// So the descent alternates: objects of the 111's kind, then a wrapper into
/// objects of a different kind, then objects of the 111's kind again - disjoint
/// from the 111 at every step.
///
/// THE COMPARISON HAS DEMONSTRATED DISCRIMINATING POWER, which is the check
/// `f2da5b0e` added and the reason this claim is worth making. Agreeing with a
/// rate-one group proves nothing if disagreement was impossible - but the ten
/// disagree on all three of these properties, so they are a worked
/// counterexample showing the properties CAN differ. Matching them is therefore
/// a fact and not a tautology.
///
/// The eight are still disjoint from the 111, and by `7e1ab465`'s arithmetic
/// that disjointness carries little on its own: the 111 are about two per cent
/// of the corpus's objects of this shape. It is the profile match that carries,
/// not the membership miss.
#[test]
fn the_ten_field_one_arrays() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut references = 0usize;
    let mut arrays: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut refcounts: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    let mut overlaps: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut lengths: std::collections::BTreeMap<u64, usize> = std::collections::BTreeMap::new();
    let mut below: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut below_profile: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut below_sizes: BTreeSet<u16> = BTreeSet::new();

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));
        let described = |off: usize| -> String {
            let object = at.get(&off).expect("a walked object");
            format!("tag {} arity {}", object.tag, object.other)
        };

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }

        // The three known array populations and the 111.
        let mut slot2: BTreeSet<usize> = BTreeSet::new();
        let mut known111: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(array) = resolve(word_at(bytes, record + 8 + 8 * 2)) {
                slot2.insert(array);
                for i in 0..word_at(bytes, array + 8) {
                    if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                        && shape(element) == Some((0, 3))
                    {
                        known111.insert(element);
                    }
                }
            }
        }
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut all = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && all.insert(target)
            {
                frontier.push(target);
            }
        }
        let mut slot3: BTreeSet<usize> = BTreeSet::new();
        for &node in &all {
            if let Some(record) = resolve(word_at(bytes, node + 8))
                && let Some(carrier) = resolve(word_at(bytes, record + 8 + 8 * 3))
            {
                for (tag, arity, slot) in [(3u8, 3u8, 2usize), (4, 2, 1)] {
                    if shape(carrier) == Some((tag, arity))
                        && let Some(array) = resolve(word_at(bytes, carrier + 8 + 8 * slot))
                    {
                        slot3.insert(array);
                    }
                }
            }
        }

        // The ten, and the arrays they hold at field 1.
        let mut inner_arrays: BTreeSet<usize> = BTreeSet::new();
        let mut ten: BTreeSet<usize> = BTreeSet::new();
        for &node in &seeds {
            if let Some(tail) = resolve(word_at(bytes, node + 16))
                && shape(tail) == Some((4, 1))
                && let Some(inner) = resolve(word_at(bytes, tail + 8))
                && let Some(array) = resolve(word_at(bytes, inner + 8 + 8 * 3))
            {
                inner_arrays.insert(array);
                for i in 0..word_at(bytes, array + 8) {
                    if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                        && shape(element) == Some((0, 3))
                    {
                        ten.insert(element);
                    }
                }
            }
        }

        let mut counts: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        for &triple in &ten {
            if let Some(array) = resolve(word_at(bytes, triple + 8 + 8)) {
                references += 1;
                arrays.insert((index, array));
                *counts.entry(array).or_default() += 1;
            }
        }
        for (&array, &count) in &counts {
            *refcounts.entry(count).or_default() += 1;
            if slot2.contains(&array) {
                *overlaps.entry("slot 2".to_owned()).or_default() += 1;
            }
            if slot3.contains(&array) {
                *overlaps.entry("slot 3".to_owned()).or_default() += 1;
            }
            if inner_arrays.contains(&array) {
                *overlaps.entry("inner record".to_owned()).or_default() += 1;
            }
            let length = word_at(bytes, array + 8);
            *lengths.entry(length).or_default() += 1;
            for i in 0..length {
                let element =
                    resolve(word_at(bytes, array + 24 + 8 * i as usize)).expect("an element");
                below.insert((index, element));
                if ten.contains(&element) {
                    *overlaps.entry("the ten".to_owned()).or_default() += 1;
                }
                if known111.contains(&element) {
                    *overlaps.entry("the 111".to_owned()).or_default() += 1;
                }
                below_sizes.insert(at.get(&element).expect("resolved").cs_sz);
                for slot in 0..3usize {
                    let field = resolve(word_at(bytes, element + 8 + 8 * slot))
                        .expect("a field is a pointer");
                    *below_profile
                        .entry(format!("field {slot}/{}", described(field)))
                        .or_default() += 1;
                }
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(references, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(
        (references, arrays.len()),
        (10, 6),
        "ten references to six arrays"
    );
    assert_eq!(
        refcounts.into_iter().collect::<Vec<_>>(),
        vec![(1, 2), (2, 4)],
        "four of the six are used twice - heavier sharing than any array level \
         above"
    );
    assert!(
        overlaps.is_empty(),
        "none of the six arrays is among the three known array populations, and \
         none of the eight elements is among the ten or the 111: {overlaps:?}"
    );
    assert_eq!(
        lengths.into_iter().collect::<Vec<_>>(),
        vec![(1, 4), (2, 2)],
        "lengths are NOT uniform. `7e1ab465` found every array one level up to \
         be length 2 and called the arrangement parallel; here even the \
         container shape stops matching"
    );

    // Below them: the 111's kind again.
    assert_eq!(below.len(), 8, "eight distinct objects below");
    assert_eq!(
        below_sizes.iter().copied().collect::<Vec<_>>(),
        vec![40],
        "forty bytes - the 111's size, not the ten's 32"
    );
    assert_eq!(
        below_profile.into_iter().collect::<Vec<_>>(),
        vec![
            ("field 0/tag 2 arity 2".to_owned(), 8),
            ("field 1/tag 2 arity 2".to_owned(), 8),
            ("field 2/tag 1 arity 1".to_owned(), 4),
            ("field 2/tag 4 arity 2".to_owned(), 4),
        ],
        "a numbered link at field 0 and a name at field 1 - the 111's profile, \
         where the ten had a string link and an ARRAY. The descent alternates: \
         the 111's kind, a wrapper into a different kind, then the 111's kind \
         again. And the ten are a worked counterexample proving these three \
         properties CAN differ, so matching them is a fact and not a tautology"
    );
}

/// The eight terminate the descent - the alternation does not repeat.
///
/// `dbf145f6` left two questions as unmeasured: whether the eight lead anywhere
/// further, and whether the alternation repeats below them. Both are answered
/// by one closure. Everything reachable from all eight is 39 objects:
///
///   tag 2 arity 2   19      tag 0 arity 3    8   (the eight themselves)
///   tag 249         4       tag 1 arity 2    4
///   tag 1 arity 1   3       tag 4 arity 2    1
///
/// NO ARRAY IS REACHABLE, and neither is any of the four structural shapes this
/// descent has been made of: no head record, no wrapper, no four-field record,
/// no pair. The only objects of the triple shape reachable from the eight are
/// the eight. What lies below them is names, the strings inside those names,
/// and two small expression nodes.
///
/// So the container chain ENDS here. The alternation `dbf145f6` found - the
/// 111's kind, a wrapper, the 111's kind again - does not continue, because
/// nothing below offers a container to continue through.
///
/// THE THIRTY-NINE IS THE GUARD, and it is doing real work. A walk that had
/// failed would return the eight roots and nothing else, and "no arrays
/// reachable" would be exactly what a broken traversal reports. Thirty-nine
/// objects across six shapes, including strings four levels of pointer down,
/// is a walk that demonstrably walked. Without that count the absence would be
/// unreadable.
///
/// The absences are reported for what they are worth. Each shape occurs in the
/// hundreds elsewhere in the corpus, so their absence from a 39-object closure
/// is not surprising on its own - a set that small will miss most things. What
/// carries is that the closure is CLOSED: 39 objects and no branching
/// container, which is a property of the whole set rather than of any one
/// shape's absence.
#[test]
fn the_eight_terminate_the_descent() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut roots = 0usize;
    let mut reachable = 0usize;
    let mut shapes: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut structural: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut triples_reachable = 0usize;
    let mut triples_are_the_roots = 0usize;

    for (module, bytes) in &modules {
        let _ = module;
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        // Down to the eight: wrapper, inner record, its array, the ten, their
        // field-1 arrays, and the elements there.
        let mut eight: BTreeSet<usize> = BTreeSet::new();
        for &node in &seeds {
            let Some(tail) = resolve(word_at(bytes, node + 16)) else {
                continue;
            };
            if shape(tail) != Some((4, 1)) {
                continue;
            }
            let Some(inner) = resolve(word_at(bytes, tail + 8)) else {
                continue;
            };
            let Some(array) = resolve(word_at(bytes, inner + 8 + 8 * 3)) else {
                continue;
            };
            for i in 0..word_at(bytes, array + 8) {
                let Some(ten) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) else {
                    continue;
                };
                if shape(ten) != Some((0, 3)) {
                    continue;
                }
                let Some(below) = resolve(word_at(bytes, ten + 8 + 8)) else {
                    continue;
                };
                for k in 0..word_at(bytes, below + 8) {
                    if let Some(element) = resolve(word_at(bytes, below + 24 + 8 * k as usize))
                        && shape(element) == Some((0, 3))
                    {
                        eight.insert(element);
                    }
                }
            }
        }
        roots += eight.len();

        // The closure under every pointer field, arrays included.
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut stack: Vec<usize> = eight.iter().copied().collect();
        while let Some(offset) = stack.pop() {
            if !seen.insert(offset) {
                continue;
            }
            let object = at.get(&offset).expect("a walked object");
            if object.tag <= abi::TAG_MAX_CTOR_TAG {
                for slot in 0..usize::from(object.other) {
                    if let Some(child) = resolve(word_at(bytes, offset + 8 + 8 * slot)) {
                        stack.push(child);
                    }
                }
            } else if object.tag == abi::TAG_ARRAY {
                for i in 0..word_at(bytes, offset + 8) {
                    if let Some(child) = resolve(word_at(bytes, offset + 24 + 8 * i as usize)) {
                        stack.push(child);
                    }
                }
            }
        }
        reachable += seen.len();

        for &offset in &seen {
            let object = at.get(&offset).expect("a walked object");
            *shapes
                .entry(format!("tag {} arity {}", object.tag, object.other))
                .or_default() += 1;
            for (probe, label) in [
                ((0u8, 5u8), "head record"),
                ((4, 1), "wrapper"),
                ((0, 4), "four-field record"),
                ((0, 2), "pair"),
            ] {
                if (object.tag, object.other) == probe {
                    *structural.entry(label.to_owned()).or_default() += 1;
                }
            }
            if object.tag == abi::TAG_ARRAY {
                *structural.entry("array".to_owned()).or_default() += 1;
            }
            if (object.tag, object.other) == (0, 3) {
                triples_reachable += 1;
                if eight.contains(&offset) {
                    triples_are_the_roots += 1;
                }
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(roots, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(roots, 8, "the eight `dbf145f6` found");

    // The guard first: a failed walk returns the roots and nothing else.
    assert_eq!(
        reachable, 39,
        "thirty-nine objects reachable from the eight. This is the guard: a \
         walk that had failed would return the eight roots alone, and \"no \
         arrays reachable\" is exactly what a broken traversal reports"
    );
    assert!(
        reachable > roots * 2,
        "the closure must reach well beyond its own roots, or the absences \
         below are unreadable"
    );

    assert_eq!(
        shapes.into_iter().collect::<Vec<_>>(),
        vec![
            ("tag 0 arity 3".to_owned(), 8),
            ("tag 1 arity 1".to_owned(), 3),
            ("tag 1 arity 2".to_owned(), 4),
            ("tag 2 arity 2".to_owned(), 19),
            ("tag 249 arity 0".to_owned(), 4),
            ("tag 4 arity 2".to_owned(), 1),
        ],
        "names, the strings inside them, and two small expression nodes"
    );

    // The termination.
    assert!(
        structural.is_empty(),
        "no array and none of the four structural shapes this descent is made \
         of is reachable: {structural:?}. The container chain ENDS here, so the \
         alternation `dbf145f6` found does not continue - nothing below offers \
         a container to continue through"
    );
    assert_eq!(
        (triples_reachable, triples_are_the_roots),
        (8, 8),
        "and the only objects of the triple shape reachable from the eight are \
         the eight themselves"
    );
}

/// The one `tag 4 arity 2` node in the closure - and a units slip in
/// `aec3efd1`'s prose.
///
/// `b314a1a5` found exactly one node of this shape among the 39 objects
/// reachable from the eight. Its identity:
///
///   one object at size 32, reached from FOUR of the eight
///   slot 0   a name link, which the production `decode_name` accepts
///   slot 1   boxed nil - the empty list
///
/// That is `aec3efd1`'s `Expr.const` profile exactly: two pointers plus a
/// trailing word, a name, and an empty level list.
///
/// THE CHECK THIS WAVE ASKED FOR IS A TAUTOLOGY AND I AM SAYING SO. "Confirm it
/// is not among the 111, the ten, or the eight" cannot fail: all three of those
/// populations are the three-field shape and this is a two-field one, so the
/// shape excludes it before anything is measured. Asserting it would be the
/// circularity refused at `84951450`, where the order asked me to pin that a
/// `tag 0` tail is "not cons" and the selection had already guaranteed it.
///
/// THE NON-TAUTOLOGICAL MEMBERSHIP QUESTION is whether this is one of the
/// `Expr.const` nodes `aec3efd1` characterised, and it is not.
///
/// AND THOSE NUMBER TWO OBJECTS, NOT ELEVEN. `aec3efd1` describes "11 objects,
/// scalar width 8, size 32"; the eleven third-shape parents with a `tag 4` tail
/// reach only TWO distinct tail objects, named `obj` five times and `tobj` six.
/// That cell's ASSERTIONS are per-use and remain true - it counted one entry
/// per parent - but its prose called them objects. The same units slip that
/// reddened `f2da5b0e` and `c998a3f8`, here in a description rather than a pin,
/// which is why nothing caught it.
///
/// `2baabd20` measured this shape carrying two sizes, so the shape alone
/// identifies nothing; the size and the field types do the work, exactly as
/// that cell concluded.
///
/// TWO POPULATIONS APPEAR IN THIS CELL AND THEY ARE NOT THE SAME ONE. The node
/// and the eight live only in `Init/Prelude.olean`; the size histogram spans
/// all four modules, because the loop that tallies it runs over every module.
/// The first version pinned the Prelude-only figures - 220 and 2,235 - against
/// a walk that counts all four, and w186 caught it. Both numbers are correct
/// for what they count, which is exactly why the basis is now named in the
/// assertion rather than left to be inferred.
///
/// The corrected pair sums to the corpus-wide total `2baabd20` already holds,
/// and that sum is asserted. The wrong pair summed to 2,455 and reconciled with
/// nothing, so the tie is the thing that was missing rather than the care.
#[test]
fn the_one_tag_four_node_in_the_closure() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut found: Vec<(u16, usize)> = Vec::new();
    let mut slot0: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut slot1_boxed_nil = 0usize;
    let mut decoded = 0usize;
    let mut among_the_eleven = 0usize;
    let mut eleven_uses = 0usize;
    let mut eleven_objects: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut corpus_by_size: std::collections::BTreeMap<u16, usize> =
        std::collections::BTreeMap::new();

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        // `aec3efd1`'s tails, by use and by object.
        for object in &objects {
            if (object.tag, object.other) == (4, 2) {
                *corpus_by_size.entry(object.cs_sz).or_default() += 1;
            }
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if let Some(tail) = resolve(word_at(bytes, object.off + 16))
                && shape(tail) == Some((4, 2))
            {
                eleven_uses += 1;
                eleven_objects.insert((index, tail));
            }
        }
        let eleven: BTreeSet<usize> = eleven_objects
            .iter()
            .filter(|(i, _)| *i == index)
            .map(|(_, off)| *off)
            .collect();

        // Down to the eight, then the closure.
        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut eight: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            let Some(node) = resolve(word_at(bytes, record + 8 + 8 * 4)) else {
                continue;
            };
            if shape(node) != Some((0, 2)) {
                continue;
            }
            let Some(tail) = resolve(word_at(bytes, node + 16)) else {
                continue;
            };
            if shape(tail) != Some((4, 1)) {
                continue;
            }
            let Some(inner) = resolve(word_at(bytes, tail + 8)) else {
                continue;
            };
            let Some(array) = resolve(word_at(bytes, inner + 8 + 8 * 3)) else {
                continue;
            };
            for i in 0..word_at(bytes, array + 8) {
                let Some(ten) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) else {
                    continue;
                };
                let Some(below) = resolve(word_at(bytes, ten + 8 + 8)) else {
                    continue;
                };
                for k in 0..word_at(bytes, below + 8) {
                    if let Some(element) = resolve(word_at(bytes, below + 24 + 8 * k as usize))
                        && shape(element) == Some((0, 3))
                    {
                        eight.insert(element);
                    }
                }
            }
        }

        // Closure from each root separately, so "reached from how many" is
        // per-root and not a single merged walk.
        let closure_of = |root: usize| -> BTreeSet<usize> {
            let mut seen: BTreeSet<usize> = BTreeSet::new();
            let mut stack = vec![root];
            while let Some(offset) = stack.pop() {
                if !seen.insert(offset) {
                    continue;
                }
                let object = at.get(&offset).expect("a walked object");
                if object.tag <= abi::TAG_MAX_CTOR_TAG {
                    for slot in 0..usize::from(object.other) {
                        if let Some(child) = resolve(word_at(bytes, offset + 8 + 8 * slot)) {
                            stack.push(child);
                        }
                    }
                } else if object.tag == abi::TAG_ARRAY {
                    for i in 0..word_at(bytes, offset + 8) {
                        if let Some(child) = resolve(word_at(bytes, offset + 24 + 8 * i as usize)) {
                            stack.push(child);
                        }
                    }
                }
            }
            seen
        };
        let closures: Vec<BTreeSet<usize>> = eight.iter().map(|&root| closure_of(root)).collect();
        let mut union: BTreeSet<usize> = BTreeSet::new();
        for closure in &closures {
            union.extend(closure);
        }

        for &offset in &union {
            if shape(offset) != Some((4, 2)) {
                continue;
            }
            let object = at.get(&offset).expect("resolved above");
            let reached = closures.iter().filter(|c| c.contains(&offset)).count();
            found.push((object.cs_sz, reached));
            if eleven.contains(&offset) {
                among_the_eleven += 1;
            }
            let name_word = word_at(bytes, offset + 8);
            let link = resolve(name_word).expect("slot 0 is a pointer");
            *slot0
                .entry(format!("tag {} arity {}", at[&link].tag, at[&link].other))
                .or_default() += 1;
            DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(name_word)
                .unwrap_or_else(|e| panic!("{module}: slot 0 must be a Name: {e}"));
            decoded += 1;
            let levels = word_at(bytes, offset + 16);
            if levels & 1 == 1 && levels >> 1 == 0 {
                slot1_boxed_nil += 1;
            }
        }
    }

    if !prelude_loaded {
        assert!(
            found.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    // The node's identity, as an object.
    assert_eq!(
        found,
        vec![(32, 4)],
        "exactly one node of this shape in the closure: size 32, reached from \
         FOUR of the eight"
    );
    assert_eq!(
        slot0.into_iter().collect::<Vec<_>>(),
        vec![("tag 1 arity 2".to_owned(), 1)],
        "slot 0 is a string name link"
    );
    assert_eq!(decoded, 1, "which the production `decode_name` accepts");
    assert_eq!(
        slot1_boxed_nil, 1,
        "and slot 1 is boxed nil - `aec3efd1`'s `Expr.const` profile exactly"
    );

    // The membership question that is not settled by the shape.
    assert_eq!(
        among_the_eleven, 0,
        "it is not one of the `Expr.const` nodes `aec3efd1` characterised. \
         Checking it against the 111, the ten or the eight would settle \
         nothing: those are all the three-field shape and this is a two-field \
         one, so the shape excludes it before anything is measured"
    );
    assert_eq!(
        (eleven_uses, eleven_objects.len()),
        (11, 2),
        "and `aec3efd1`'s tails are TWO objects reached eleven times. That \
         cell's assertions are per-use and remain true; its prose called them \
         \"11 objects\", which is the units slip that reddened `f2da5b0e` and \
         `c998a3f8`, here in a description rather than a pin"
    );

    // The shape identifies nothing on its own.
    let corpus: Vec<(u16, usize)> = corpus_by_size.into_iter().collect();
    assert_eq!(
        corpus,
        vec![(24, 231), (32, 2306)],
        "this shape carries two sizes ACROSS ALL FOUR MODULES, which is the \
         population this loop walks. The first version pinned 220 and 2,235 - \
         `Init/Prelude.olean` alone - because that is where I measured it, and \
         w186 caught the difference. The other three fixtures contribute 11 and \
         71"
    );
    assert_eq!(
        corpus.iter().map(|(_, count)| count).sum::<usize>(),
        2537,
        "and the two sizes sum to the corpus-wide total `2baabd20` pins for \
         this shape. The wrong values summed to 2,455 and reconciled with \
         nothing - this assertion is the tie that would have caught them"
    );
}

/// One level below the `tag 4` node: its name link, and how widely it is
/// shared.
///
/// THE NODE'S OWN FIELDS ARE ALREADY PINNED. It has arity 2, and `4584151d`
/// walks both - slot 0 a name link the production `decode_name` accepts, slot 1
/// boxed nil. Walking "that node's fields" again would re-pin two assertions
/// that already exist, so this goes one level deeper, into the name link's own
/// fields, which nothing has read.
///
/// AND THE NON-MEMBERSHIP CHECK IS STILL A TAUTOLOGY. The 111, the ten and the
/// eight are all the three-field shape; this node is a two-field one and its
/// name link is a different shape again. Nothing measured can make that check
/// fail. It is asked here for the second consecutive wave and the answer is the
/// one `84951450` established: a comparison the selection already guarantees is
/// not evidence.
///
/// What the link actually holds:
///
///   prefix   boxed zero - the anonymous name, so this is a SINGLE component
///   string   an eight-character payload
///   exactly ONE name link in the corpus points at that string object
///   the link itself is referenced FIVE times across the corpus
///
/// THE SINGLE-COMPONENT FACT COULD HAVE COME OUT OTHERWISE, which is what makes
/// it worth asserting: a name link may carry a pointer prefix, and this file has
/// measured plenty that do - `2a2d8234` found 50 of 111 two-component names in
/// one field alone. The check has discriminating power, per `f2da5b0e`.
///
/// THE FIVE REFERENCES ARE THE INTERESTING NUMBER. The node itself is reached
/// from four of the eight, and the link it names is used five times corpus-wide
/// - so this name is not private to the structure this bead has been walking.
/// That is the first object in the whole descent measured to be shared with
/// something OUTSIDE it.
///
/// The eight-character text is the fragile part, flagged as at `aec3efd1` and
/// `3373af3b`; every structural fact above is independent of it.
#[test]
fn the_tag_four_node_name() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut links = 0usize;
    let mut anonymous_prefix = 0usize;
    let mut string_payloads: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();
    let mut links_sharing_the_string = 0usize;
    let mut link_references = 0usize;
    let mut decoded: BTreeSet<String> = BTreeSet::new();
    let mut components: BTreeSet<usize> = BTreeSet::new();

    for (module, bytes) in &modules {
        let view = OleanView::parse(bytes).unwrap_or_else(|e| panic!("{module}: parse: {e}"));
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        // Down to the eight, then the closure, then the one `tag 4` node.
        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut eight: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            let Some(node) = resolve(word_at(bytes, record + 8 + 8 * 4)) else {
                continue;
            };
            let Some(tail) = resolve(word_at(bytes, node + 16)) else {
                continue;
            };
            if shape(tail) != Some((4, 1)) {
                continue;
            }
            let Some(inner) = resolve(word_at(bytes, tail + 8)) else {
                continue;
            };
            let Some(array) = resolve(word_at(bytes, inner + 8 + 8 * 3)) else {
                continue;
            };
            for i in 0..word_at(bytes, array + 8) {
                let Some(ten) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) else {
                    continue;
                };
                let Some(below) = resolve(word_at(bytes, ten + 8 + 8)) else {
                    continue;
                };
                for k in 0..word_at(bytes, below + 8) {
                    if let Some(element) = resolve(word_at(bytes, below + 24 + 8 * k as usize))
                        && shape(element) == Some((0, 3))
                    {
                        eight.insert(element);
                    }
                }
            }
        }
        let mut closure: BTreeSet<usize> = BTreeSet::new();
        let mut stack: Vec<usize> = eight.iter().copied().collect();
        while let Some(offset) = stack.pop() {
            if !closure.insert(offset) {
                continue;
            }
            let object = at.get(&offset).expect("a walked object");
            if object.tag <= abi::TAG_MAX_CTOR_TAG {
                for slot in 0..usize::from(object.other) {
                    if let Some(child) = resolve(word_at(bytes, offset + 8 + 8 * slot)) {
                        stack.push(child);
                    }
                }
            } else if object.tag == abi::TAG_ARRAY {
                for i in 0..word_at(bytes, offset + 8) {
                    if let Some(child) = resolve(word_at(bytes, offset + 24 + 8 * i as usize)) {
                        stack.push(child);
                    }
                }
            }
        }

        for &offset in &closure {
            if shape(offset) != Some((4, 2)) {
                continue;
            }
            let link = resolve(word_at(bytes, offset + 8)).expect("slot 0 is a pointer");
            links += 1;

            // Structural: the prefix, and the string it names.
            let prefix = word_at(bytes, link + 8);
            if prefix & 1 == 1 && prefix >> 1 == 0 {
                anonymous_prefix += 1;
            }
            let string = resolve(word_at(bytes, link + 16)).expect("the component");
            assert_eq!(
                at.get(&string).map(|o| o.tag),
                Some(abi::TAG_STRING),
                "{module}: a string link's component is a string"
            );
            *string_payloads
                .entry(usize::try_from(word_at(bytes, string + 8)).expect("in range"))
                .or_default() += 1;

            // How widely the string and the link are shared.
            links_sharing_the_string += objects
                .iter()
                .filter(|other| (other.tag, other.other) == (1, 2))
                .filter(|other| resolve(word_at(bytes, other.off + 16)) == Some(string))
                .count();
            for other in &objects {
                if other.tag <= abi::TAG_MAX_CTOR_TAG {
                    for slot in 0..usize::from(other.other) {
                        if resolve(word_at(bytes, other.off + 8 + 8 * slot)) == Some(link) {
                            link_references += 1;
                        }
                    }
                } else if other.tag == abi::TAG_ARRAY {
                    for i in 0..word_at(bytes, other.off + 8) {
                        if resolve(word_at(bytes, other.off + 24 + 8 * i as usize)) == Some(link) {
                            link_references += 1;
                        }
                    }
                }
            }

            let name = DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(word_at(bytes, offset + 8))
                .unwrap_or_else(|e| panic!("{module}: the name must decode: {e}"))
                .to_display_string();
            components.insert(name.split('.').count());
            decoded.insert(name);
        }
    }

    if !prelude_loaded {
        assert_eq!(links, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    assert_eq!(links, 1, "one node, one name link");

    // Structural, independent of any string decoding.
    assert_eq!(
        anonymous_prefix, 1,
        "the prefix is the boxed anonymous name, so this is a SINGLE component. \
         A name link may carry a pointer prefix and this file has measured 50 \
         that do, so the check could have come out otherwise"
    );
    assert_eq!(
        components.into_iter().collect::<Vec<_>>(),
        vec![1],
        "which the production decoder's rendering agrees with"
    );
    assert_eq!(
        string_payloads.into_iter().collect::<Vec<_>>(),
        vec![(9, 1)],
        "the component's stored byte count, terminator included"
    );
    assert_eq!(
        links_sharing_the_string, 1,
        "exactly one name link in the corpus names that string object"
    );
    assert_eq!(
        link_references, 5,
        "and the link itself is referenced FIVE times corpus-wide, against a \
         node reached from four of the eight. So this name is not private to \
         the structure this bead has been walking - the first object in the \
         whole descent measured to be shared with something OUTSIDE it"
    );

    // The fragile part, last and flagged.
    assert_eq!(
        decoded.into_iter().collect::<Vec<_>>(),
        vec!["lcErased".to_owned()],
        "the eight-character text, read through the production decoder. This is \
         the fragile assertion; every structural fact above is independent of it"
    );
}

/// Where else that name link is used - the first step OUTWARD from the
/// structure.
///
/// `c2f98113` measured the link as referenced five times corpus-wide against a
/// node reached from four of the eight, and named the other references as
/// unmeasured. They are five DISTINCT holder objects - no object names it twice
/// - and exactly one of them is the node in the closure.
///
/// THE OTHER FOUR ARE OUTSIDE EVERY POPULATION THIS BEAD HAS CHARACTERISED:
/// not the ten, not the 111, not the eight, not a spine node, not a seed. Their
/// shapes:
///
///   an array, twice - once at slot 43 of a large one
///   a three-field record at 32 bytes, once
///   a two-field object at 24 bytes, once
///
/// TWO OF THEM WEAR SHAPES THIS FILE HAS ALREADY NAMED AND ARE NOT MEMBERS OF
/// THEM. The three-field record at 32 bytes is the TEN's exact profile -
/// `cae89f06` pinned that combination as what distinguishes the ten from the
/// 111 - and this object is not one of the ten. The two-field object is the
/// spine-node shape and is not a spine node.
///
/// So the shape-is-not-identity finding, which `daaaabe2` opened and
/// `2baabd20` generalised, holds at the boundary too: leaving the structure
/// does not leave the shapes behind.
///
/// NOT ONE OF THE FIVE IS IN A CHARACTERISED POPULATION, and the first version
/// of this cell said one was. It counted the closure as though it were one of
/// them; the node is in the closure and is a two-field object, which none of
/// the four populations contains. w189 caught it, and the corrected figure
/// makes the outward step cleaner: every holder is outside all four, and what
/// distinguishes the node is closure membership alone.
///
/// THAT COSTS THE REACHABILITY ARGUMENT ITS ORIGINAL FORM. I had written that
/// membership was reachable because one holder had it. None does. What carries
/// it instead is below: two holders wear the exact shapes of characterised
/// populations without being members, so membership was shape-reachable and the
/// misses are a measured outcome rather than something the selection forced.
///
/// POPULATION SCOPE, named because `b28cb524` was a wave lost to leaving it
/// implicit: the link and all five holders live in `Init/Prelude.olean`. The
/// other three fixtures contribute nothing here, and the cell asserts that
/// rather than letting an all-module walk be read as a Prelude figure.
#[test]
fn the_other_references_to_that_name() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut references = 0usize;
    let mut holders: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut in_closure = 0usize;
    let mut in_characterised = 0usize;
    let mut shapes: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut modules_with_the_link: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut ten_profile_outside = 0usize;
    let mut spine_shape_outside = 0usize;

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        // Every population this bead has characterised.
        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut known111: BTreeSet<usize> = BTreeSet::new();
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            if let Some(array) = resolve(word_at(bytes, record + 8 + 8 * 2)) {
                for i in 0..word_at(bytes, array + 8) {
                    if let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize))
                        && shape(element) == Some((0, 3))
                    {
                        known111.insert(element);
                    }
                }
            }
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }
        let mut spine = seeds.clone();
        let mut frontier: Vec<usize> = seeds.iter().copied().collect();
        while let Some(node) = frontier.pop() {
            if let Some(target) = resolve(word_at(bytes, node + 16))
                && shape(target) == Some((0, 2))
                && spine.insert(target)
            {
                frontier.push(target);
            }
        }
        let mut ten: BTreeSet<usize> = BTreeSet::new();
        let mut eight: BTreeSet<usize> = BTreeSet::new();
        for &node in &seeds {
            let Some(tail) = resolve(word_at(bytes, node + 16)) else {
                continue;
            };
            if shape(tail) != Some((4, 1)) {
                continue;
            }
            let Some(inner) = resolve(word_at(bytes, tail + 8)) else {
                continue;
            };
            let Some(array) = resolve(word_at(bytes, inner + 8 + 8 * 3)) else {
                continue;
            };
            for i in 0..word_at(bytes, array + 8) {
                let Some(element) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) else {
                    continue;
                };
                if shape(element) != Some((0, 3)) {
                    continue;
                }
                ten.insert(element);
                if let Some(below) = resolve(word_at(bytes, element + 8 + 8)) {
                    for k in 0..word_at(bytes, below + 8) {
                        if let Some(deeper) = resolve(word_at(bytes, below + 24 + 8 * k as usize))
                            && shape(deeper) == Some((0, 3))
                        {
                            eight.insert(deeper);
                        }
                    }
                }
            }
        }
        if eight.is_empty() {
            continue;
        }

        // The closure, and the one node in it.
        let mut closure: BTreeSet<usize> = BTreeSet::new();
        let mut stack: Vec<usize> = eight.iter().copied().collect();
        while let Some(offset) = stack.pop() {
            if !closure.insert(offset) {
                continue;
            }
            let object = at.get(&offset).expect("a walked object");
            if object.tag <= abi::TAG_MAX_CTOR_TAG {
                for slot in 0..usize::from(object.other) {
                    if let Some(child) = resolve(word_at(bytes, offset + 8 + 8 * slot)) {
                        stack.push(child);
                    }
                }
            } else if object.tag == abi::TAG_ARRAY {
                for i in 0..word_at(bytes, offset + 8) {
                    if let Some(child) = resolve(word_at(bytes, offset + 24 + 8 * i as usize)) {
                        stack.push(child);
                    }
                }
            }
        }
        let node = closure
            .iter()
            .copied()
            .find(|&offset| shape(offset) == Some((4, 2)))
            .expect("the one `tag 4` node");
        let link = resolve(word_at(bytes, node + 8)).expect("its name link");

        // Every slot naming that link.
        for holder in &objects {
            let naming = if holder.tag <= abi::TAG_MAX_CTOR_TAG {
                (0..usize::from(holder.other))
                    .filter(|&slot| {
                        resolve(word_at(bytes, holder.off + 8 + 8 * slot)) == Some(link)
                    })
                    .count()
            } else if holder.tag == abi::TAG_ARRAY {
                (0..word_at(bytes, holder.off + 8))
                    .filter(|&i| {
                        resolve(word_at(bytes, holder.off + 24 + 8 * i as usize)) == Some(link)
                    })
                    .count()
            } else {
                0
            };
            if naming == 0 {
                continue;
            }
            references += naming;
            holders.insert((index, holder.off));
            *modules_with_the_link.entry(module.clone()).or_default() += naming;
            *shapes
                .entry(if holder.tag == abi::TAG_ARRAY {
                    "array".to_owned()
                } else {
                    format!(
                        "tag {} arity {} size {}",
                        holder.tag, holder.other, holder.cs_sz
                    )
                })
                .or_default() += 1;

            if closure.contains(&holder.off) {
                in_closure += 1;
            }
            let characterised = ten.contains(&holder.off)
                || known111.contains(&holder.off)
                || eight.contains(&holder.off)
                || spine.contains(&holder.off);
            if characterised {
                in_characterised += 1;
            } else {
                if (holder.tag, holder.other, holder.cs_sz) == (0, 3, 32) {
                    ten_profile_outside += 1;
                }
                if (holder.tag, holder.other) == (0, 2) {
                    spine_shape_outside += 1;
                }
            }
        }
    }

    if !prelude_loaded {
        assert_eq!(references, 0, "the third shape is not in the C3 fixtures");
        return;
    }

    // Objects, not occurrences.
    assert_eq!(
        (references, holders.len()),
        (5, 5),
        "five references from five DISTINCT holders - no object names the link \
         twice, so here the two bases coincide"
    );
    assert_eq!(
        modules_with_the_link.len(),
        1,
        "and every one of them is in a single module. The link is \
         Prelude-only; the other three fixtures contribute nothing, which is \
         asserted rather than left for an all-module walk to be misread as a \
         Prelude figure"
    );

    assert_eq!(
        in_closure, 1,
        "exactly one holder is the node in the closure"
    );
    assert_eq!(
        in_characterised, 0,
        "and NOT ONE holder is in any of the four populations this bead has \
         characterised - not the ten, the 111, the eight or the spine. The \
         first version pinned 1, conflating the CLOSURE with those four: the \
         node is in the closure, but it is a two-field object and none of the \
         four contains one. w189 caught it. \
         \
         So all five are outside, and closure membership is what separates the \
         node from the other four - not membership in a characterised \
         population, which none of them has"
    );

    assert_eq!(
        shapes.into_iter().collect::<Vec<_>>(),
        vec![
            ("array".to_owned(), 2),
            ("tag 0 arity 2 size 24".to_owned(), 1),
            ("tag 0 arity 3 size 32".to_owned(), 1),
            ("tag 4 arity 2 size 32".to_owned(), 1),
        ],
        "the holders by shape"
    );

    // Shape is not identity, at the boundary too.
    assert_eq!(
        (ten_profile_outside, spine_shape_outside),
        (1, 1),
        "one holder outside every population carries the TEN's exact profile - \
         three fields at 32 bytes, the combination `cae89f06` pinned as what \
         separates the ten from the 111 - and another carries the spine-node \
         shape. Neither is a member. Leaving the structure does not leave the \
         shapes behind"
    );
}

/// The objects no context resolves - and the ranking inverts.
///
/// `259eadde` reported 159 "minority objects" and called them small numbers. It
/// gave no denominator, which is the failure this file keeps catching in itself,
/// and the figure answers a narrower question than its name suggests. Two
/// things are wrong with it and one thing is missing.
///
/// WHAT 159 ACTUALLY COUNTS is the error rate of a rule that guesses each mixed
/// context's MAJORITY size. That is a real quantity and it is not the number of
/// objects a context cannot resolve: an object on the majority side of a mixed
/// context, with no other arrival, is just as indeterminate. Counted per
/// object, the indeterminate total is 1,174 - SEVEN TIMES the 159.
///
/// AND A WHOLE CATEGORY WAS NEVER COUNTED. 10,262 objects of these six shapes
/// have NO constructor arrival at all - they are reached only through array
/// elements, where there is no parent shape or slot to key on. A rule keyed on
/// constructor context has nothing to work with for 41% of the population, and
/// no cell before this one could see them, because every cell tallied CONTEXTS
/// and an object with no context contributes to no tally.
///
/// The decomposition, pooled over the six shapes' 24,867 objects:
///
///   resolvable through some pure context   13,431
///   every arrival through a mixed context   1,174
///   no constructor arrival at all          10,262
///
/// so 46% are indeterminate, not the impression "159" left.
///
/// THE RANKING INVERTS, WHICH IS THE FINDING. By mixed-context count
/// (`03c853b1`) and by minority arrivals (`259eadde`), `(1, 2)` is the worst of
/// the six. By the fraction of its own objects that no context resolves it is
/// the BEST, at 1.4%; `(0, 2)` is the worst at 89.3% because 5,238 of its 6,506
/// objects are array-only. Three consecutive cells of mine ranked `(1, 2)`
/// worst on measures that do not survive the change of unit.
///
/// WHAT THIS DOES NOT DO. It does not unblock `list_ptrs`. 110 `(1, 2)` objects
/// remain indeterminate and a decoder has to be right on every one of them, and
/// all of this measures STORED SIZE, which is a proxy for the cons-or-name
/// question rather than that question. What does not survive is my framing that
/// `(1, 2)` is uniquely bad - it is uniquely bad in contexts and unremarkable
/// in objects.
///
/// POPULATION SCOPE: all four modules pooled, constructor objects only, the six
/// shapes no refinement in `03c853b1` separated; array arrivals are excluded
/// from the context notion and counted as their own category rather than
/// silently dropped.
#[test]
fn the_objects_no_context_resolves() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }
    if !prelude_loaded {
        return;
    }

    type Context = (u8, u8, u16, usize);
    let mut sizes: std::collections::BTreeMap<(u8, u8), BTreeSet<u16>> =
        std::collections::BTreeMap::new();
    let mut context_sizes: std::collections::BTreeMap<((u8, u8), Context), BTreeSet<u16>> =
        std::collections::BTreeMap::new();
    let mut shape_of: std::collections::BTreeMap<(usize, usize), (u8, u8)> =
        std::collections::BTreeMap::new();
    let mut ctor_arrivals: std::collections::BTreeMap<(usize, usize), BTreeSet<Context>> =
        std::collections::BTreeMap::new();

    for (index, (_, bytes)) in modules.iter().enumerate() {
        let bytes = bytes.as_slice();
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        for object in &objects {
            if object.tag <= abi::TAG_MAX_CTOR_TAG {
                sizes
                    .entry((object.tag, object.other))
                    .or_default()
                    .insert(object.cs_sz);
                shape_of.insert((index, object.off), (object.tag, object.other));
            }
        }
        // Only CONSTRUCTOR arrivals give a context; array arrivals do not.
        for parent in &objects {
            if parent.tag > abi::TAG_MAX_CTOR_TAG {
                continue;
            }
            for slot in 0..usize::from(parent.other) {
                let word = word_at(bytes, parent.off + 8 + 8 * slot);
                let Some(child) = resolve(word).and_then(|off| at.get(&off)) else {
                    continue;
                };
                if child.tag > abi::TAG_MAX_CTOR_TAG {
                    continue;
                }
                let key = (parent.tag, parent.other, parent.cs_sz, slot);
                context_sizes
                    .entry(((child.tag, child.other), key))
                    .or_default()
                    .insert(child.cs_sz);
                ctor_arrivals
                    .entry((index, child.off))
                    .or_default()
                    .insert(key);
            }
        }
    }

    // The six shapes no refinement separated.
    let survivors: Vec<(u8, u8)> = sizes
        .iter()
        .filter(|(shape, seen)| {
            seen.len() > 1
                && context_sizes
                    .iter()
                    .any(|((s, _), sizes)| s == *shape && sizes.len() > 1)
        })
        .map(|(shape, _)| *shape)
        .collect();
    assert_eq!(
        survivors,
        vec![(0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (2, 2)],
        "the same six shapes, recomputed rather than quoted"
    );

    // Per shape, the three fates of an object.
    let mut table: Vec<(u8, u8, usize, usize, usize, usize)> = Vec::new();
    for shape in &survivors {
        let mut total = 0usize;
        let mut resolvable = 0usize;
        let mut all_mixed = 0usize;
        let mut no_context = 0usize;
        for (key, object_shape) in &shape_of {
            if object_shape != shape {
                continue;
            }
            total += 1;
            match ctor_arrivals.get(key) {
                None => no_context += 1,
                Some(contexts) => {
                    if contexts.iter().any(|context| {
                        context_sizes
                            .get(&(*shape, *context))
                            .is_some_and(|seen| seen.len() == 1)
                    }) {
                        resolvable += 1;
                    } else {
                        all_mixed += 1;
                    }
                }
            }
        }
        assert_eq!(
            resolvable + all_mixed + no_context,
            total,
            "every object of {shape:?} must fall in exactly one of the three"
        );
        table.push((shape.0, shape.1, total, resolvable, all_mixed, no_context));
    }
    assert_eq!(
        table,
        vec![
            (0, 1, 1350, 584, 277, 489),
            (0, 2, 6506, 696, 572, 5238),
            (0, 3, 5553, 2472, 148, 2933),
            (1, 1, 1912, 317, 6, 1589),
            (1, 2, 7591, 7481, 97, 13),
            (2, 2, 1955, 1881, 74, 0),
        ],
        "per shape: objects, those resolvable through some PURE context, those \
         whose every constructor arrival is through a MIXED one, and those with \
         NO constructor arrival at all. The third column is the category no \
         earlier cell could see, because they all tallied contexts and an \
         object with no context contributes to no tally"
    );

    let pooled = |pick: fn(&(u8, u8, usize, usize, usize, usize)) -> usize| -> usize {
        table.iter().map(pick).sum()
    };
    assert_eq!(
        (
            pooled(|row| row.2),
            pooled(|row| row.3),
            pooled(|row| row.4),
            pooled(|row| row.5)
        ),
        (24867, 13431, 1174, 10262),
        "pooled: 46% of these objects are indeterminate under any context rule. \
         `259eadde`'s 159 is the error count of a rule guessing each context's \
         MAJORITY - a real quantity, but not this one, and seven times smaller"
    );

    // The inversion.
    let mut by_indeterminacy: Vec<((u8, u8), usize)> = table
        .iter()
        .map(|row| ((row.0, row.1), (row.4 + row.5) * 1000 / row.2))
        .collect();
    by_indeterminacy.sort_by_key(|(_, permille)| *permille);
    assert_eq!(
        by_indeterminacy,
        vec![
            ((1, 2), 14),
            ((2, 2), 37),
            ((0, 3), 554),
            ((0, 1), 567),
            ((1, 1), 834),
            ((0, 2), 893),
        ],
        "indeterminate objects per thousand, best first. `(1, 2)` - worst by \
         mixed-context count in `03c853b1` and by minority arrivals in \
         `259eadde` - is the BEST of the six here, and `(0, 2)` the worst \
         because 5,238 of its 6,506 objects are array-only. Three of my cells \
         ranked `(1, 2)` worst on measures that do not survive the change of \
         unit. \
         `(0, 2)` was pinned at 892 in the first version and w233 caught it: I \
         took 89.3% from a float and wrote it out as a per-mille, where the \
         integer division here gives 893. Every other figure in this cell came \
         from the walk; this was the one column I derived in my head"
    );

    // The finding is an ORDERING, and it is pinned as one as well as by value,
    // so it does not rest solely on six hand-checkable literals.
    assert!(
        by_indeterminacy
            .windows(2)
            .all(|pair| pair[0].1 <= pair[1].1),
        "the vector above must stay sorted, or `best first` is not what it says"
    );
    assert_eq!(
        (
            by_indeterminacy.first().expect("six shapes").0,
            by_indeterminacy.last().expect("six shapes").0
        ),
        ((1, 2), (0, 2)),
        "and the INVERSION is the finding: the shape three earlier cells called \
         the worst is the least indeterminate of the six, and the worst is \
         `(0, 2)`, which none of them singled out. That holds whatever the \
         exact per-mille figures are"
    );
}

/// The ten surviving mixed contexts, enumerated - and what they cost in OBJECTS.
///
/// `03c853b1` ended by saying the six irreducible shapes' mixed contexts "are
/// now enumerable". It did not enumerate them, and a claim that something could
/// be measured is not a measurement. There are TEN, and this is the list.
///
/// COUNTING CONTEXTS AND COUNTING OBJECTS RANK THEM DIFFERENTLY, which is the
/// finding. By context count four shapes tie at one apiece and look alike. By
/// the number of objects a context rule would get wrong - the MINORITY side of
/// each split, which is what a decoder would actually misclassify - they are:
///
///   (0, 1)   19        (0, 2)    1        (0, 3)    6
///   (1, 1)    5        (1, 2)   95        (2, 2)   33
///
/// `(0, 2)`'s entire irreducible ambiguity is ONE OBJECT out of 572 arriving
/// through that context. `(2, 2)`'s is 33. The context count called those two
/// equal.
///
/// `(1, 2)` IS STILL THE WORST ON BOTH MEASURES, and the honest correction is
/// to its MARGIN rather than to its rank: five contexts against one is a factor
/// of five, but 95 minority objects against 33 is a factor of 2.9.
/// `03c853b1` reported the first and I have pointed its doc here.
///
/// Its rank does not survive a third measure.
/// `the_objects_no_context_resolves` counts, per OBJECT, how many are left
/// indeterminate by any context at all, and on that measure `(1, 2)` is the
/// BEST of the six at 1.4% while `(0, 2)` is the worst at 89%. The 159 below is
/// also not the count of unresolvable objects - it is the error count of a rule
/// that guesses each context's majority, and the unresolvable count is 1,174.
///
/// EDGES WOULD HAVE MISLED WORSE STILL. `(1, 2)`'s context under a
/// `(0, 3, 32)` parent carries 1,586 arrival EDGES but only 40 distinct
/// objects, and `(1, 1)`'s single context carries 490 edges over 17 objects.
/// An edge-based severity would rank the first about forty times worse than it
/// is. Both counts are pinned side by side so the divergence is in the
/// assertion rather than in this comment.
///
/// POPULATION SCOPE: all four modules pooled, constructor objects only, array
/// arrivals excluded - the same notion `03c853b1` was left with, recomputed
/// here rather than quoted.
#[test]
fn the_ten_surviving_mixed_contexts() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }
    if !prelude_loaded {
        return;
    }

    // Context keyed on the parent's shape, SIZE and slot; array arrivals are
    // not a context a decoder could key on and are excluded.
    type Context = (u8, u8, u16, usize);
    let mut sizes: std::collections::BTreeMap<(u8, u8), BTreeSet<u16>> =
        std::collections::BTreeMap::new();
    let mut edges: std::collections::BTreeMap<((u8, u8), Context, u16), usize> =
        std::collections::BTreeMap::new();
    let mut objects_seen: std::collections::BTreeMap<
        ((u8, u8), Context, u16),
        BTreeSet<(usize, usize)>,
    > = std::collections::BTreeMap::new();

    for (index, (_, bytes)) in modules.iter().enumerate() {
        let bytes = bytes.as_slice();
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        for object in &objects {
            if object.tag <= abi::TAG_MAX_CTOR_TAG {
                sizes
                    .entry((object.tag, object.other))
                    .or_default()
                    .insert(object.cs_sz);
            }
        }
        for parent in &objects {
            if parent.tag > abi::TAG_MAX_CTOR_TAG {
                continue;
            }
            for slot in 0..usize::from(parent.other) {
                let word = word_at(bytes, parent.off + 8 + 8 * slot);
                let Some(child) = resolve(word).and_then(|off| at.get(&off)) else {
                    continue;
                };
                if child.tag > abi::TAG_MAX_CTOR_TAG {
                    continue;
                }
                let key = (
                    (child.tag, child.other),
                    (parent.tag, parent.other, parent.cs_sz, slot),
                    child.cs_sz,
                );
                *edges.entry(key).or_default() += 1;
                objects_seen
                    .entry(key)
                    .or_default()
                    .insert((index, child.off));
            }
        }
    }

    // Which (shape, context) pairs still see more than one size.
    let mut mixed: std::collections::BTreeMap<((u8, u8), Context), BTreeSet<u16>> =
        std::collections::BTreeMap::new();
    for ((shape, context, size), _) in &edges {
        if sizes[shape].len() > 1 {
            mixed.entry((*shape, *context)).or_default().insert(*size);
        }
    }
    mixed.retain(|_, seen| seen.len() > 1);

    // The list, with both counts side by side.
    let table: Vec<(u8, u8, u8, u8, u16, usize, Vec<(u16, usize, usize)>)> = mixed
        .iter()
        .map(|((shape, context), seen)| {
            (
                shape.0,
                shape.1,
                context.0,
                context.1,
                context.2,
                context.3,
                seen.iter()
                    .map(|size| {
                        let key = (*shape, *context, *size);
                        (*size, edges[&key], objects_seen[&key].len())
                    })
                    .collect(),
            )
        })
        .collect();
    assert_eq!(
        table,
        vec![
            (0, 1, 0, 1, 16, 0, vec![(16, 19, 19), (24, 266, 266)]),
            (0, 2, 0, 2, 24, 1, vec![(24, 608, 571), (32, 1, 1)]),
            (0, 3, 0, 2, 24, 1, vec![(32, 116, 6), (40, 142, 142)]),
            (1, 1, 0, 3, 40, 2, vec![(16, 373, 5), (24, 117, 12)]),
            (1, 2, 0, 1, 16, 0, vec![(24, 56, 56), (32, 5, 5)]),
            (1, 2, 0, 2, 24, 1, vec![(24, 205, 84), (32, 44, 44)]),
            (1, 2, 0, 3, 32, 1, vec![(24, 1568, 22), (32, 18, 18)]),
            (1, 2, 0, 4, 48, 1, vec![(24, 210, 14), (32, 142, 142)]),
            (1, 2, 1, 1, 16, 0, vec![(24, 14, 14), (32, 165, 165)]),
            (2, 2, 1, 2, 24, 0, vec![(24, 64, 64), (32, 43, 33)]),
        ],
        "every surviving mixed context: child shape, then the parent's tag, \
         arity, SIZE and slot, then per child size the arrival EDGES and the \
         distinct OBJECTS. The two diverge badly - `(1, 2)` under a \
         `(0, 3, 32)` parent has 1,586 edges over 40 objects, and `(1, 1)`'s \
         single context 490 edges over 17 - so an edge-based severity would \
         rank the first about forty times worse than it is"
    );
    assert_eq!(
        table.len(),
        10,
        "ten contexts, which `03c853b1` did not list"
    );

    // What a context rule would actually get wrong, per shape.
    let mut minority: std::collections::BTreeMap<(u8, u8), usize> =
        std::collections::BTreeMap::new();
    for ((shape, context), seen) in &mixed {
        let counts: Vec<usize> = seen
            .iter()
            .map(|size| objects_seen[&(*shape, *context, *size)].len())
            .collect();
        let total: usize = counts.iter().sum();
        *minority.entry(*shape).or_default() +=
            total - counts.iter().copied().max().expect("non-empty");
    }
    assert_eq!(
        minority.into_iter().collect::<Vec<_>>(),
        vec![
            ((0, 1), 19),
            ((0, 2), 1),
            ((0, 3), 6),
            ((1, 1), 5),
            ((1, 2), 95),
            ((2, 2), 33),
        ],
        "the MINORITY side of each split, summed per shape - the objects a \
         context rule would misclassify. By context count `(0, 2)` and `(2, 2)` \
         both have exactly one mixed context and look alike; in objects one is \
         a SINGLE object out of 572 and the other is 33. `(1, 2)` is still the \
         worst on both measures, but its margin over the next worst falls from \
         a factor of five in contexts to 2.9 in objects"
    );
}

/// Strengthening the context buys two shapes - and `(1, 2)` is an outlier.
///
/// `49e423e7` asked whether the arrival context determines a child's stored
/// size, with context taken as `(parent tag, parent arity, slot)`. Six of
/// fourteen shapes separated. That leaves the obvious question it did not ask:
/// is that the right notion of context, or would a stronger one do better?
///
/// TWO STRENGTHENINGS, BOTH INDEPENDENT, WORTH ONE SHAPE EACH.
///
///   ignore ARRAY arrivals            6 -> 7, flipping `(0, 4)`
///   include the PARENT'S OWN SIZE    6 -> 7, flipping `(7, 3)`
///   both together                    6 -> 8
///
/// They flip DIFFERENT shapes and compose, which is measured rather than
/// assumed - two refinements each worth "+1" could easily have been the same
/// +1, and the composed count is asserted to show they are not.
///
/// Including the parent's size is the natural strengthening: it asks whether
/// the parent's LAYOUT, not merely its shape, fixes the child's. It raises the
/// context count for `(1, 2)` from 40 to 52 and leaves its mixed count at SIX,
/// unchanged. More contexts, no more separation.
///
/// SIX SHAPES SURVIVE BOTH REFINEMENTS: `(0,1)` `(0,2)` `(0,3)` `(1,1)`
/// `(1,2)` `(2,2)`. Among them the mixed counts are 1, 1, 1, 1, 5, 1 - five
/// shapes with a single stubborn context each, and `(1, 2)` with five.
///
/// Counting CONTEXTS is not the same as counting objects, and
/// `the_ten_surviving_mixed_contexts` enumerates them and measures the
/// difference. "A factor of five" below is a factor in this metric; in objects
/// it is 2.9, and one of the four single-context shapes turns out to be a
/// single OBJECT.
///
/// THAT IS THE SHARPEST FORM THE BLOCK HAS TAKEN. `daaaabe2` showed a size rule
/// cannot identify a cons cell; `49e423e7` showed `(1, 2)` is the worst of the
/// unseparable shapes. This shows it stays the worst after the context notion
/// has been strengthened twice in independent directions, and by a factor of
/// five over every other survivor. `list_ptrs` is not blocked by a discriminator
/// I have not thought of yet; it is blocked by the one shape that resists every
/// discriminator this file has tried.
///
/// POPULATION SCOPE: all four modules pooled, constructor objects only - the
/// same 14 multi-size shapes and 46,334 objects as `49e423e7`, recomputed here
/// rather than quoted.
#[test]
fn strengthening_the_context_buys_two_shapes() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }
    if !prelude_loaded {
        return;
    }

    // Context A keys on the parent's shape; context B adds its stored size.
    // The array key stands for "arrived through an array element".
    const ARRAY_A: (u8, u8, usize) = (abi::TAG_ARRAY, 0, usize::MAX);
    const ARRAY_B: (u8, u8, u16, usize) = (abi::TAG_ARRAY, 0, 0, usize::MAX);

    let mut sizes: std::collections::BTreeMap<(u8, u8), BTreeSet<u16>> =
        std::collections::BTreeMap::new();
    let mut population: std::collections::BTreeMap<(u8, u8), usize> =
        std::collections::BTreeMap::new();
    let mut ctx_a: std::collections::BTreeMap<
        (u8, u8),
        std::collections::BTreeMap<(u8, u8, usize), BTreeSet<u16>>,
    > = std::collections::BTreeMap::new();
    let mut ctx_b: std::collections::BTreeMap<
        (u8, u8),
        std::collections::BTreeMap<(u8, u8, u16, usize), BTreeSet<u16>>,
    > = std::collections::BTreeMap::new();

    for (_, bytes) in &modules {
        let bytes = bytes.as_slice();
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        for object in &objects {
            if object.tag <= abi::TAG_MAX_CTOR_TAG {
                sizes
                    .entry((object.tag, object.other))
                    .or_default()
                    .insert(object.cs_sz);
                *population.entry((object.tag, object.other)).or_default() += 1;
            }
        }
        for parent in &objects {
            let arrivals: Vec<((u8, u8, usize), (u8, u8, u16, usize), u64)> =
                if parent.tag <= abi::TAG_MAX_CTOR_TAG {
                    (0..usize::from(parent.other))
                        .map(|slot| {
                            (
                                (parent.tag, parent.other, slot),
                                (parent.tag, parent.other, parent.cs_sz, slot),
                                word_at(bytes, parent.off + 8 + 8 * slot),
                            )
                        })
                        .collect()
                } else if parent.tag == abi::TAG_ARRAY {
                    (0..word_at(bytes, parent.off + 8))
                        .map(|i| {
                            (
                                ARRAY_A,
                                ARRAY_B,
                                word_at(bytes, parent.off + 24 + 8 * i as usize),
                            )
                        })
                        .collect()
                } else {
                    Vec::new()
                };
            for (key_a, key_b, word) in arrivals {
                let Some(child) = resolve(word).and_then(|off| at.get(&off)) else {
                    continue;
                };
                if child.tag > abi::TAG_MAX_CTOR_TAG {
                    continue;
                }
                let shape = (child.tag, child.other);
                ctx_a
                    .entry(shape)
                    .or_default()
                    .entry(key_a)
                    .or_default()
                    .insert(child.cs_sz);
                ctx_b
                    .entry(shape)
                    .or_default()
                    .entry(key_b)
                    .or_default()
                    .insert(child.cs_sz);
            }
        }
    }

    let multi: Vec<(u8, u8)> = sizes
        .iter()
        .filter(|(_, seen)| seen.len() > 1)
        .map(|(shape, _)| *shape)
        .collect();
    assert_eq!(
        (
            multi.len(),
            multi.iter().map(|s| population[s]).sum::<usize>()
        ),
        (14, 46334),
        "the same multi-size population as `49e423e7`, recomputed rather than \
         quoted"
    );

    // Contexts and mixed counts under both notions, per shape.
    let table: Vec<(u8, u8, usize, usize, usize, usize)> = multi
        .iter()
        .map(|shape| {
            let a = &ctx_a[shape];
            let b = &ctx_b[shape];
            (
                shape.0,
                shape.1,
                a.len(),
                a.values().filter(|seen| seen.len() > 1).count(),
                b.len(),
                b.values().filter(|seen| seen.len() > 1).count(),
            )
        })
        .collect();
    assert_eq!(
        table,
        vec![
            (0, 1, 19, 2, 19, 2),
            (0, 2, 8, 2, 8, 2),
            (0, 3, 12, 2, 12, 2),
            (0, 4, 8, 1, 8, 1),
            (0, 5, 8, 0, 8, 0),
            (0, 6, 2, 0, 2, 0),
            (0, 7, 2, 0, 2, 0),
            (1, 1, 24, 2, 26, 1),
            (1, 2, 40, 6, 52, 6),
            (2, 2, 19, 1, 21, 1),
            (3, 1, 9, 0, 10, 0),
            (4, 1, 11, 0, 11, 0),
            (4, 2, 20, 0, 23, 0),
            (7, 3, 13, 1, 16, 0),
        ],
        "tag, arity, then contexts and MIXED contexts under A (parent shape and \
         slot) and under B (parent shape, SIZE and slot). `(1, 2)` gains twelve \
         contexts under B and keeps all six of its mixed ones - more contexts, \
         no more separation"
    );

    // What each refinement is worth, and that they are not the same one.
    let count = |pick: &dyn Fn(&(u8, u8)) -> bool| multi.iter().filter(|s| pick(s)).count();
    let sep_a = |shape: &(u8, u8)| ctx_a[shape].values().all(|seen| seen.len() == 1);
    let sep_a_no_array = |shape: &(u8, u8)| {
        ctx_a[shape]
            .iter()
            .filter(|(key, _)| **key != ARRAY_A)
            .all(|(_, seen)| seen.len() == 1)
    };
    let sep_b = |shape: &(u8, u8)| ctx_b[shape].values().all(|seen| seen.len() == 1);
    let sep_both = |shape: &(u8, u8)| {
        ctx_b[shape]
            .iter()
            .filter(|(key, _)| **key != ARRAY_B)
            .all(|(_, seen)| seen.len() == 1)
    };
    assert_eq!(
        (
            count(&sep_a),
            count(&sep_a_no_array),
            count(&sep_b),
            count(&sep_both)
        ),
        (6, 7, 7, 8),
        "separable shapes under the base notion, under each refinement alone, \
         and under both. Each refinement is worth exactly ONE shape and \
         together they are worth TWO"
    );
    assert_eq!(
        (
            multi
                .iter()
                .filter(|s| sep_a_no_array(s) && !sep_a(s))
                .copied()
                .collect::<Vec<_>>(),
            multi
                .iter()
                .filter(|s| sep_b(s) && !sep_a(s))
                .copied()
                .collect::<Vec<_>>()
        ),
        (vec![(0, 4)], vec![(7, 3)]),
        "and they flip DIFFERENT shapes, which is why they compose. Two \
         refinements each worth `+1` could have been the same +1; measured, \
         they are not"
    );

    // What survives both, and how badly.
    let survivors: Vec<(u8, u8, usize)> = multi
        .iter()
        .filter(|shape| !sep_both(shape))
        .map(|shape| {
            (
                shape.0,
                shape.1,
                ctx_b[shape]
                    .iter()
                    .filter(|(key, seen)| **key != ARRAY_B && seen.len() > 1)
                    .count(),
            )
        })
        .collect();
    assert_eq!(
        survivors,
        vec![
            (0, 1, 1),
            (0, 2, 1),
            (0, 3, 1),
            (1, 1, 1),
            (1, 2, 5),
            (2, 2, 1),
        ],
        "the six shapes no refinement here separates, with their surviving \
         mixed-context counts. Five have ONE stubborn context; `(1, 2)` has \
         FIVE. It stays the worst after the context notion has been \
         strengthened twice in independent directions, by a factor of five over \
         every other survivor"
    );
}

/// Which multi-size shapes the arrival context separates - the whole census.
///
/// `5efac560` measured one shape and concluded that discrimination is
/// "shape-specific". That was two data points wearing the language of a general
/// claim, so this asks the same question of EVERY shape that has more than one
/// stored size.
///
/// Of 36 constructor shapes pooled across the four modules, FOURTEEN store more
/// than one size - 46,334 objects between them. Asking whether the arrival
/// context determines the stored size:
///
///   SEPARABLE (no mixed context)   6:  (0,5) (0,6) (0,7) (3,1) (4,1) (4,2)
///   NOT separable                  8:  (0,1) (0,2) (0,3) (0,4)
///                                      (1,1) (1,2) (2,2) (7,3)
///
/// SO THE CLAIM SURVIVES AND MY FRAMING OF IT DID NOT. Separation is indeed
/// shape-specific, but `5efac560` presented `(4, 1)` as the positive case and
/// left the impression that separation is rare. Six of fourteen separate. The
/// finding worth keeping is the other half: EIGHT DO NOT, and `(1, 2)` - the
/// shape that blocks `list_ptrs` - is the worst of them, with SIX mixed
/// contexts out of 40. Its nearest rivals have two.
///
/// THE ARRAY CONTEXT IS AN OFFENDER FIVE TIMES AND THE SOLE OFFENDER ONCE, and
/// measuring that mattered because the tempting story is wrong. An array
/// arrival cannot fix a size - arrays are homogeneous in type, not in layout -
/// so "arrays spoil it" looks like it would explain the eight. It does not:
/// ignoring array arrivals entirely moves the separable count from 6 to SEVEN,
/// not to fourteen. One shape flips. The other seven fail on constructor
/// contexts alone.
///
/// The per-shape table is pinned in full rather than as summary counts, so a
/// shape moving between the two groups cannot leave the totals looking right -
/// the decomposition rule from `a-count-grep-cannot-find-a-decomposition`.
///
/// POPULATION SCOPE: all four modules pooled, constructor objects only; array
/// and string objects have no arity to vary and are excluded by construction,
/// which is why the shape count is 36 rather than the walk's full inventory.
#[test]
fn the_context_separability_census() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }
    if !prelude_loaded {
        return;
    }

    const ARRAY_CONTEXT: (u8, u8, usize) = (abi::TAG_ARRAY, 0, usize::MAX);

    let mut sizes: std::collections::BTreeMap<(u8, u8), std::collections::BTreeMap<u16, usize>> =
        std::collections::BTreeMap::new();
    let mut contexts: std::collections::BTreeMap<
        (u8, u8),
        std::collections::BTreeMap<(u8, u8, usize), BTreeSet<u16>>,
    > = std::collections::BTreeMap::new();

    for (_, bytes) in &modules {
        let bytes = bytes.as_slice();
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        for object in &objects {
            if object.tag <= abi::TAG_MAX_CTOR_TAG {
                *sizes
                    .entry((object.tag, object.other))
                    .or_default()
                    .entry(object.cs_sz)
                    .or_default() += 1;
            }
        }
        for parent in &objects {
            let slots: Vec<((u8, u8, usize), u64)> = if parent.tag <= abi::TAG_MAX_CTOR_TAG {
                (0..usize::from(parent.other))
                    .map(|slot| {
                        (
                            (parent.tag, parent.other, slot),
                            word_at(bytes, parent.off + 8 + 8 * slot),
                        )
                    })
                    .collect()
            } else if parent.tag == abi::TAG_ARRAY {
                (0..word_at(bytes, parent.off + 8))
                    .map(|i| {
                        (
                            ARRAY_CONTEXT,
                            word_at(bytes, parent.off + 24 + 8 * i as usize),
                        )
                    })
                    .collect()
            } else {
                Vec::new()
            };
            for (key, word) in slots {
                let Some(child) = resolve(word).and_then(|off| at.get(&off)) else {
                    continue;
                };
                if child.tag > abi::TAG_MAX_CTOR_TAG {
                    continue;
                }
                contexts
                    .entry((child.tag, child.other))
                    .or_default()
                    .entry(key)
                    .or_default()
                    .insert(child.cs_sz);
            }
        }
    }

    let multi: Vec<(u8, u8)> = sizes
        .iter()
        .filter(|(_, by_size)| by_size.len() > 1)
        .map(|(shape, _)| *shape)
        .collect();
    let objects_in_multi: usize = multi
        .iter()
        .map(|shape| sizes[shape].values().sum::<usize>())
        .sum();
    assert_eq!(
        (sizes.len(), multi.len(), objects_in_multi),
        (36, 14, 46334),
        "constructor shapes, those storing more than one size, and the objects \
         they hold between them"
    );

    // The whole table, so a shape cannot move group unnoticed.
    let table: Vec<(u8, u8, usize, Vec<(u16, usize)>, usize, usize)> = multi
        .iter()
        .map(|shape| {
            let by_size = &sizes[shape];
            let ctx = &contexts[shape];
            (
                shape.0,
                shape.1,
                by_size.values().sum::<usize>(),
                by_size.iter().map(|(k, v)| (*k, *v)).collect(),
                ctx.len(),
                ctx.values().filter(|seen| seen.len() > 1).count(),
            )
        })
        .collect();
    assert_eq!(
        table,
        vec![
            (0, 1, 1350, vec![(16, 958), (24, 392)], 19, 2),
            (0, 2, 6506, vec![(24, 6350), (32, 156)], 8, 2),
            (0, 3, 5553, vec![(32, 2730), (40, 2823)], 12, 2),
            (0, 4, 4747, vec![(40, 1218), (48, 3529)], 8, 1),
            (0, 5, 784, vec![(48, 461), (56, 323)], 8, 0),
            (0, 6, 161, vec![(56, 34), (64, 127)], 2, 0),
            (0, 7, 152, vec![(64, 23), (72, 129)], 2, 0),
            (1, 1, 1912, vec![(16, 1863), (24, 49)], 24, 2),
            (1, 2, 7591, vec![(24, 2564), (32, 5027)], 40, 6),
            (2, 2, 1955, vec![(24, 65), (32, 1890)], 19, 1),
            (3, 1, 52, vec![(16, 5), (24, 47)], 9, 0),
            (4, 1, 122, vec![(16, 106), (24, 16)], 11, 0),
            (4, 2, 2537, vec![(24, 231), (32, 2306)], 20, 0),
            (7, 3, 12912, vec![(40, 38), (48, 12874)], 13, 1),
        ],
        "tag, arity, objects, sizes, arrival contexts, and contexts reaching \
         BOTH sizes - pinned per shape rather than as group totals, so a shape \
         changing group cannot leave the counts looking right"
    );

    let separable = table.iter().filter(|row| row.5 == 0).count();
    assert_eq!(
        (separable, table.len() - separable),
        (6, 8),
        "SIX of the fourteen are separated by their arrival context and EIGHT \
         are not. `5efac560` measured one of the six and framed it as the \
         positive case; separation is not rare. The finding is the other half - \
         eight are not separable, and `(1, 2)`, the shape that blocks \
         `list_ptrs`, is the worst with six mixed contexts against its nearest \
         rivals' two"
    );

    // The tempting story about arrays, measured instead of assumed.
    let array_offender = multi
        .iter()
        .filter(|shape| {
            contexts[*shape]
                .get(&ARRAY_CONTEXT)
                .is_some_and(|seen| seen.len() > 1)
        })
        .count();
    let array_sole = multi
        .iter()
        .filter(|shape| {
            let mixed: Vec<&(u8, u8, usize)> = contexts[*shape]
                .iter()
                .filter(|(_, seen)| seen.len() > 1)
                .map(|(key, _)| key)
                .collect();
            mixed == vec![&ARRAY_CONTEXT]
        })
        .count();
    let separable_without_arrays = multi
        .iter()
        .filter(|shape| {
            contexts[*shape]
                .iter()
                .filter(|(key, _)| **key != ARRAY_CONTEXT)
                .all(|(_, seen)| seen.len() == 1)
        })
        .count();
    assert_eq!(
        (array_offender, array_sole, separable_without_arrays),
        (5, 1, 7),
        "an array arrival cannot fix a size - arrays are homogeneous in type, \
         not in layout - so `arrays spoil it` looks like it should explain the \
         eight. It does not: the array context is an offender for five shapes \
         but the SOLE offender for one, and ignoring array arrivals moves the \
         separable count from 6 to SEVEN rather than to fourteen. Seven shapes \
         fail on constructor contexts alone"
    );
}

/// The `(4, 1)` layouts ARE separated by context - the positive case.
///
/// `ed5d41d5` pinned `(4, 1)` at 122 objects across two stored sizes and used
/// that to refuse a claim: two sizes are two layouts, so the shape cannot name
/// one type. It left the obvious question unasked - if shape does not separate
/// them, does anything?
///
/// It does, and this is the first place in this bead where I MEASURED a
/// discriminator working. TWO do, independently.
///
/// It is not, however, an unusual shape:
/// `the_context_separability_census` asks this of all fourteen multi-size
/// shapes and finds SIX separable. This cell's framing invites the reading that
/// separation is rare and `(4, 1)` special; it is neither. What is unusual is
/// the other direction - eight shapes are NOT separable, and `(1, 2)` is the
/// worst of them.
///
///   by the CHILD: size 16 always holds `(0, 4, 40)` or `(0, 1, 24)` in slot 0;
///   size 24 always holds `(1, 2, 32)`. The two sets are disjoint.
///
///   by the PARENT: of the 11 arrival contexts that reach a `(4, 1)` object,
///   ZERO reach both sizes. Every context determines the size it arrives at.
///
/// THE CONTRAST IS MEASURED HERE ON THE SAME FOOTING, not quoted. Asking the
/// identical question of `(2, 2)` - does the arrival context determine the
/// stored size - over the identical pooled population gives 19 contexts and ONE
/// mixed. So discrimination is not impossible in this format; it is
/// SHAPE-SPECIFIC, and the earlier cells' failures were facts about `(1, 2)`
/// and `(2, 2)` rather than about the file.
///
/// AND THE ONE OFFENDER IS THE FAMILIAR ONE: the single mixed context is
/// `(1, 2)` slot 0, the cons-or-name shape that blocks `list_ptrs` and that
/// `a5e8cb68` already found mixing its children's classes. The same parent
/// spoils both questions.
///
/// A CAVEAT THAT THE PER-MODULE COUNTS MAKE VISIBLE rather than leaving in
/// prose: ALL 106 size-16 objects are in Prelude. The three C3 fixtures
/// contribute only size-24 objects - three and two, with `Init.olean`
/// contributing none - so one half of this separation rests on a single module,
/// and the per-module tally is asserted so that is not hidden by the pooled
/// figure.
///
/// POPULATION SCOPE: all four modules pooled for the context and child tallies,
/// with the object counts asserted per module.
#[test]
fn the_four_one_layouts_are_separated_by_context() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }
    if !prelude_loaded {
        return;
    }

    // Same question of both shapes: does the arrival context fix the size?
    let mut per_module: Vec<(String, Vec<(u16, usize)>)> = Vec::new();
    let mut children: std::collections::BTreeMap<
        u16,
        std::collections::BTreeMap<(u8, u8, u16), usize>,
    > = std::collections::BTreeMap::new();
    let mut contexts_four: std::collections::BTreeMap<(u8, u8, usize), BTreeSet<u16>> =
        std::collections::BTreeMap::new();
    let mut contexts_two: std::collections::BTreeMap<(u8, u8, usize), BTreeSet<u16>> =
        std::collections::BTreeMap::new();
    let mut two_two_total = 0usize;

    for (module, bytes) in &modules {
        let bytes = bytes.as_slice();
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        let mut tally: std::collections::BTreeMap<u16, usize> = std::collections::BTreeMap::new();
        let mut four: std::collections::BTreeMap<usize, u16> = std::collections::BTreeMap::new();
        let mut two: std::collections::BTreeMap<usize, u16> = std::collections::BTreeMap::new();
        for object in &objects {
            match (object.tag, object.other) {
                (4, 1) => {
                    *tally.entry(object.cs_sz).or_default() += 1;
                    four.insert(object.off, object.cs_sz);
                    // What it points at.
                    if let Some(child) = resolve(word_at(bytes, object.off + 8))
                        && let Some(shape) = at.get(&child)
                    {
                        *children
                            .entry(object.cs_sz)
                            .or_default()
                            .entry((shape.tag, shape.other, shape.cs_sz))
                            .or_default() += 1;
                    }
                }
                (2, 2) => {
                    two.insert(object.off, object.cs_sz);
                    two_two_total += 1;
                }
                _ => {}
            }
        }
        per_module.push((module.clone(), tally.into_iter().collect()));

        // Arrival contexts for both shapes, in one pass.
        for parent in &objects {
            let slots: Vec<(usize, u64)> = if parent.tag <= abi::TAG_MAX_CTOR_TAG {
                (0..usize::from(parent.other))
                    .map(|slot| (slot, word_at(bytes, parent.off + 8 + 8 * slot)))
                    .collect()
            } else if parent.tag == abi::TAG_ARRAY {
                (0..word_at(bytes, parent.off + 8))
                    .map(|i| (usize::MAX, word_at(bytes, parent.off + 24 + 8 * i as usize)))
                    .collect()
            } else {
                Vec::new()
            };
            for (slot, word) in slots {
                let Some(child) = resolve(word) else {
                    continue;
                };
                let key = (parent.tag, parent.other, slot);
                if let Some(&size) = four.get(&child) {
                    contexts_four.entry(key).or_default().insert(size);
                }
                if let Some(&size) = two.get(&child) {
                    contexts_two.entry(key).or_default().insert(size);
                }
            }
        }
    }

    // Per module, so the pooled figure cannot hide where each half lives.
    assert_eq!(
        per_module
            .iter()
            .map(|(m, t)| (m.as_str(), t.clone()))
            .collect::<Vec<_>>(),
        vec![
            ("Init.olean", vec![]),
            ("Init.BinderNameHint.olean", vec![(24, 3)]),
            ("Init.SizeOfLemmas.olean", vec![(24, 2)]),
            ("Init/Prelude.olean", vec![(16, 106), (24, 11)]),
        ],
        "`(4, 1)` objects by stored size, per module. ALL 106 of the size-16 \
         objects are in Prelude and the fixtures contribute only size-24, so \
         one half of the separation below rests on a single module - asserted \
         rather than hidden inside the pooled 122"
    );

    // The child separates them.
    assert_eq!(
        children
            .iter()
            .map(|(size, shapes)| (
                *size,
                shapes.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>()
            ))
            .collect::<Vec<_>>(),
        vec![
            (16, vec![((0, 1, 24), 4), ((0, 4, 40), 102)]),
            (24, vec![((1, 2, 32), 16)]),
        ],
        "what each `(4, 1)` object holds in slot 0, by its own stored size. The \
         two sets of child shapes are DISJOINT, so the child alone tells the \
         layouts apart"
    );

    // And so does the parent - unlike `(2, 2)`, asked the same way.
    let mixed_four: Vec<((u8, u8, usize), Vec<u16>)> = contexts_four
        .iter()
        .filter(|(_, sizes)| sizes.len() > 1)
        .map(|(key, sizes)| (*key, sizes.iter().copied().collect()))
        .collect();
    let mixed_two: Vec<((u8, u8, usize), Vec<u16>)> = contexts_two
        .iter()
        .filter(|(_, sizes)| sizes.len() > 1)
        .map(|(key, sizes)| (*key, sizes.iter().copied().collect()))
        .collect();
    assert_eq!(
        (contexts_four.len(), mixed_four.len()),
        (11, 0),
        "of the arrival contexts reaching a `(4, 1)` object, NONE reaches both \
         sizes: the parent determines the layout"
    );
    assert_eq!(
        (two_two_total, contexts_two.len(), mixed_two.len()),
        (1955, 19, 1),
        "the identical question of `(2, 2)`, over the identical pooled \
         population, measured here rather than quoted: one context DOES reach \
         both sizes. So discrimination is not impossible in this format, it is \
         SHAPE-SPECIFIC - the earlier failures were facts about `(1, 2)` and \
         `(2, 2)`, not about the walk"
    );
    assert_eq!(
        mixed_two,
        vec![((1, 2, 0), vec![24, 32])],
        "and the single offender is the familiar one: `(1, 2)` slot 0, the \
         cons-or-name shape that blocks `list_ptrs` and that `a5e8cb68` already \
         found mixing its children's classes. The same parent spoils both \
         questions"
    );
}

/// The rest of the `mpz` family has no witness - with denominators this time.
///
/// `ddb61b49` closed by listing three items of this family as still uncovered:
/// "Nat with negative mpz", "Name.num mpz", and "Int: neither scalar nor mpz".
/// That is a list of claims about the corpus, and `be041416` is the record of
/// what happens when I carry such a list forward instead of testing it. So this
/// tests it, and reports a denominator for every zero rather than a bare zero.
///
/// THE ONLY THING THAT REFERENCES AN `mpz` IN THIS CORPUS is the single-field
/// `(0, 1, 16)` literal wrapper, at slot 0, twice. Across all four modules, no
/// object of any other shape points at one. That single fact settles two of the
/// three items, and it is a stronger statement than either of them.
///
///   Nat with negative mpz   0 of 2 - both size words are +2
///   Name.num mpz            0 of 1,955 `(2, 2)` objects hold an `mpz`
///
/// THE THIRD IS NOT SHAPE-DECIDABLE AND IS RECORDED AS UNDECIDED, NOT AS ZERO.
/// `decode_int` is reached only from a `DataValue` variant, and a `DataValue`
/// cannot be picked out by shape: `(4, 1)` has 122 objects across these modules
/// at TWO stored sizes, 16 and 24, and two stored sizes at one tag and arity
/// mean two layouts and so at least two types. A zero here would be a claim
/// about a population I cannot enumerate. What IS measured is the bound above:
/// nothing but the literal wrapper points at an `mpz`, so if such a `DataValue`
/// exists it does not hold one.
///
/// AND THE SIZE WORD HAS TWO HALVES THAT I HAVE BEEN READING DIFFERENTLY.
/// `region::mpz_limbs` takes the signed size from the HIGH 32 bits;
/// `ddb61b49`'s wire walk takes its limb count from the LOW 32. On both objects
/// the halves are 2 and 2, so that cell is correct - but it was correct by a
/// coincidence it did not check, and its "independent" walk would have read a
/// different limb count had the halves differed. Both halves are pinned here
/// and that cell's comment now says which field it reads.
///
/// This is the same shape as `7a0a90fa`'s predicate mismatch: I used one field
/// and described a check computed from another. It is worth noting that the
/// version that bites is always the one where the two happen to agree, because
/// nothing goes red.
///
/// POPULATION SCOPE: all four modules pooled for the counts, with the `mpz`
/// objects themselves per module; the three C3 fixtures hold none, so every
/// non-zero figure here comes from `Init/Prelude.olean`.
#[test]
fn the_remaining_mpz_family_items_have_no_witness() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }
    if !prelude_loaded {
        return;
    }

    let mut holder_shapes: std::collections::BTreeMap<(u8, u8, u16, usize), usize> =
        std::collections::BTreeMap::new();
    let mut size_halves: Vec<(u32, i32)> = Vec::new();
    let mut mpz_total = 0usize;
    let mut negative = 0usize;
    let mut two_two = 0usize;
    let mut two_two_with_mpz = 0usize;
    let mut four_one = 0usize;
    let mut four_one_sizes: BTreeSet<u16> = BTreeSet::new();

    for (_, bytes) in &modules {
        let bytes = bytes.as_slice();
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let mpz: BTreeSet<usize> = objects
            .iter()
            .filter(|o| o.tag == abi::TAG_MPZ)
            .map(|o| o.off)
            .collect();
        mpz_total += mpz.len();

        for &off in &mpz {
            let word = word_at(bytes, off + 8);
            // `region::mpz_limbs` reads the HIGH half as a signed size; the
            // limb count this file's other cell uses is the LOW half.
            let low = (word & 0xFFFF_FFFF) as u32;
            let high = ((word >> 32) as u32) as i32;
            size_halves.push((low, high));
            if high < 0 {
                negative += 1;
            }
        }

        for object in &objects {
            if (object.tag, object.other) == (2, 2) {
                two_two += 1;
                if resolve(word_at(bytes, object.off + 16))
                    .is_some_and(|target| mpz.contains(&target))
                {
                    two_two_with_mpz += 1;
                }
            }
            if (object.tag, object.other) == (4, 1) {
                four_one += 1;
                four_one_sizes.insert(object.cs_sz);
            }
            // Every reference to an `mpz`, by holder shape and slot.
            if object.tag <= abi::TAG_MAX_CTOR_TAG {
                for slot in 0..usize::from(object.other) {
                    if resolve(word_at(bytes, object.off + 8 + 8 * slot))
                        .is_some_and(|target| mpz.contains(&target))
                    {
                        *holder_shapes
                            .entry((object.tag, object.other, object.cs_sz, slot))
                            .or_default() += 1;
                    }
                }
            } else if object.tag == abi::TAG_ARRAY {
                for i in 0..word_at(bytes, object.off + 8) {
                    if resolve(word_at(bytes, object.off + 24 + 8 * i as usize))
                        .is_some_and(|target| mpz.contains(&target))
                    {
                        *holder_shapes
                            .entry((object.tag, 0, object.cs_sz, usize::MAX))
                            .or_default() += 1;
                    }
                }
            }
        }
    }

    // One holder shape, and it settles two of the three items.
    assert_eq!(
        holder_shapes.into_iter().collect::<Vec<_>>(),
        vec![((0, 1, 16, 0), 2)],
        "the ONLY objects referencing an `mpz` anywhere in the four modules are \
         two single-field `(0, 1, 16)` literal wrappers, at slot 0. No object \
         of any other shape points at one - which is a stronger statement than \
         either of the two items it settles"
    );
    assert_eq!(
        (mpz_total, negative),
        (2, 0),
        "`Nat with negative mpz` has no witness: neither of the two `mpz` \
         objects carries a negative size. Reported against its denominator, not \
         as a bare zero"
    );
    assert_eq!(
        (two_two, two_two_with_mpz),
        (1955, 0),
        "`Name.num mpz` has no witness either: of 1,955 `(2, 2)` objects pooled \
         across the four modules, NONE holds an `mpz` at slot 1"
    );

    // The third item is not decidable from shape, and is not reported as zero.
    assert_eq!(
        (four_one, four_one_sizes.into_iter().collect::<Vec<_>>()),
        (122, vec![16, 24]),
        "`Int: neither scalar nor mpz` is reached only from a `DataValue`, and \
         `DataValue` cannot be picked out by shape: `(4, 1)` has 122 objects at \
         TWO stored sizes, and two sizes at one tag and arity are two layouts \
         and so at least two types. This cell therefore records that item as \
         UNDECIDED rather than as a zero - a zero would be a claim about a \
         population it cannot enumerate"
    );

    // The two halves of the size word, which I have been reading differently.
    assert_eq!(
        size_halves,
        vec![(2, 2), (2, 2)],
        "the LOW half of each size word and its HIGH half read as a signed \
         size. `region::mpz_limbs` uses the high one and `ddb61b49`'s wire walk \
         uses the low one; they agree on both objects, so that cell is right - \
         but it was right by a coincidence it never checked, and its walk would \
         have read a different limb count had the halves differed"
    );
}

/// The `mpz` literal decodes through the production path - the block `be041416`
/// retired, taken.
///
/// `be041416` found two `TAG_MPZ` objects in Prelude and recorded that the
/// obstacle I had named for the `mpz` rules - "an object no fixture builds" -
/// was gone. This takes the pin.
///
/// THE VALUE IS 2^64, which is the whole reason the object exists. It is the
/// smallest natural number that does not fit a `u64`, so it is the smallest one
/// the boxed-scalar representation cannot carry. Both `mpz` objects in the
/// module hold that same value, stored as two little-endian limbs `[0, 1]`.
///
/// BOTH ARMS OF `decode_nat` ARE EXERCISED HERE, which is what makes this a
/// test of the branch rather than of one object. Prelude has 53 `Expr.lit`
/// objects: 35 natural-number literals and 18 strings. Of the 35, THIRTY-THREE
/// take the scalar arm and TWO take the `mpz` arm, and 33 + 2 is asserted
/// against the 35 so neither arm can be silently empty. The largest scalar
/// literal is 2^32 - comfortably inside a `u64` - against the `mpz`'s 2^64, so
/// the two arms are separated by the representation boundary and not by an
/// accident of which literals this module happens to contain.
///
/// PRODUCTION DECODER, NOT A RE-IMPLEMENTATION. Each literal is decoded with
/// `DeclDecoder::decode_expr`, and the `mpz` result is checked three ways: it
/// equals `Expr::lit(Literal::Nat(..))` built from the limbs; its `to_u64` is
/// NONE, which is the property that forced the `mpz` in the first place; and
/// its limbs equal the ones this cell reads off the wire independently. The
/// third is the one that would catch a decoder agreeing with a wrong
/// expectation.
///
/// The wire read takes the limb count from the LOW half of the size word;
/// `region::mpz_limbs` takes its signed size from the HIGH half. Those are
/// different fields, which is what makes the check independent - and it is only
/// a check at all because they agree on these two objects.
/// `the_remaining_mpz_family_items_have_no_witness` measures that agreement,
/// which this cell assumed.
///
/// THE SCALAR CONTROL IS DECODED THE SAME WAY and its `to_u64` is SOME, so the
/// two arms are distinguished by a property of the decoded value rather than by
/// where the cell looked.
///
/// POPULATION SCOPE: `Init/Prelude.olean` for the literals; the `mpz` object
/// counts cover all four modules, and the three C3 fixtures are asserted to
/// have NONE - which is why this pin needs the corpus and could not have been
/// written against the fixtures alone.
#[test]
fn the_mpz_literal_decodes_through_the_production_path() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut mpz_per_module: Vec<(String, usize)> = Vec::new();
    for (module, bytes) in &modules {
        let (objects, _) = objects_of(bytes);
        mpz_per_module.push((
            module.clone(),
            objects.iter().filter(|o| o.tag == abi::TAG_MPZ).count(),
        ));
    }
    assert_eq!(
        mpz_per_module
            .iter()
            .map(|(m, n)| (m.as_str(), *n))
            .collect::<Vec<_>>(),
        [
            ("Init.olean", 0),
            ("Init.BinderNameHint.olean", 0),
            ("Init.SizeOfLemmas.olean", 0),
            ("Init/Prelude.olean", 2),
        ]
        .into_iter()
        .filter(|(m, _)| prelude_loaded || *m != "Init/Prelude.olean")
        .collect::<Vec<_>>(),
        "`mpz` objects per module: the three C3 fixtures have NONE, which is why \
         this pin needs the corpus"
    );

    if !prelude_loaded {
        return;
    }
    let bytes = modules
        .last()
        .map(|(_, bytes)| bytes.as_slice())
        .expect("Prelude loaded");

    let (objects, base) = objects_of(bytes);
    let at: std::collections::BTreeMap<usize, Obj> = objects.iter().map(|o| (o.off, *o)).collect();
    let resolve = |word: u64| -> Option<usize> {
        (word & 1 == 0)
            .then(|| usize::try_from(word.wrapping_sub(base)).ok())
            .flatten()
            .filter(|off| at.contains_key(off))
    };
    let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

    // Classify every `Expr.lit` by the arm its payload takes.
    let mut strings = 0usize;
    let mut scalar_arm: Vec<(u64, usize)> = Vec::new();
    let mut mpz_arm: Vec<usize> = Vec::new();
    let mut literals = 0usize;
    for object in &objects {
        if (object.tag, object.other) != (9, 1) {
            continue;
        }
        literals += 1;
        let Some(payload) = resolve(word_at(bytes, object.off + 8)) else {
            continue;
        };
        match shape(payload) {
            Some((1, 1)) => strings += 1,
            Some((0, 1)) => {
                let word = word_at(bytes, payload + 8);
                if word & 1 == 1 {
                    scalar_arm.push((word >> 1, object.off));
                } else if resolve(word).and_then(|t| at.get(&t)).map(|o| o.tag)
                    == Some(abi::TAG_MPZ)
                {
                    mpz_arm.push(object.off);
                }
            }
            _ => {}
        }
    }
    assert_eq!(
        (literals, strings, scalar_arm.len(), mpz_arm.len()),
        (53, 18, 33, 2),
        "`Expr.lit` objects, string literals, and natural-number literals by \
         arm. Both arms of `decode_nat` are populated in this one module"
    );
    assert_eq!(
        strings + scalar_arm.len() + mpz_arm.len(),
        literals,
        "and the three account for every `Expr.lit`, so neither arm's count is \
         a filtered sample"
    );

    // The limbs, read off the wire independently of the decoder.
    let mut wire_limbs: BTreeSet<Vec<u64>> = BTreeSet::new();
    for &expr in &mpz_arm {
        let payload = resolve(word_at(bytes, expr + 8)).expect("literal payload");
        let mpz = resolve(word_at(bytes, payload + 8)).expect("mpz object");
        // The LOW half of the size word. `region::mpz_limbs` reads the HIGH
        // half as a signed size; the two agree here, measured in
        // `the_remaining_mpz_family_items_have_no_witness`.
        let size = usize::try_from(word_at(bytes, mpz + 8) & 0xFFFF_FFFF).expect("limb count");
        let limbs_at = usize::try_from(word_at(bytes, mpz + 16).wrapping_sub(base)).expect("limbs");
        wire_limbs.insert(
            (0..size)
                .map(|i| word_at(bytes, limbs_at + 8 * i))
                .collect::<Vec<u64>>(),
        );
    }
    assert_eq!(
        wire_limbs.iter().cloned().collect::<Vec<_>>(),
        vec![vec![0_u64, 1]],
        "both `mpz` objects store the same two little-endian limbs - the value \
         2^64, the smallest natural the scalar arm cannot carry"
    );

    // Through the production decoder.
    let view = OleanView::parse(bytes).expect("Prelude header");
    let expected = Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1])));
    for &expr in &mpz_arm {
        let decoded = DeclDecoder::new(&view, WalkBudget::default())
            .decode_expr(base + u64::try_from(expr).expect("in range"))
            .expect("the mpz literal decodes");
        assert_eq!(
            decoded, expected,
            "`decode_expr` takes the `mpz` arm and yields the 2^64 literal"
        );
        let ExprNode::Lit {
            literal: Literal::Nat(nat),
        } = decoded.node()
        else {
            panic!("an `Expr.lit` holding a natural number");
        };
        assert_eq!(
            nat.to_u64(),
            None,
            "and the decoded value does NOT fit a `u64` - the property that \
             forces the `mpz` representation, checked on the decoder's own \
             output rather than on the expectation built beside it"
        );
        assert_eq!(
            nat.limbs_le(),
            &[0_u64, 1],
            "with the limbs this cell read off the wire by a separate walk - \
             one that takes its count from the LOW half of the size word where \
             the decoder takes a signed size from the HIGH half, so a decoder \
             agreeing with a wrong expectation would still fail here"
        );
    }

    // The scalar arm, decoded the same way.
    let (largest, largest_at) = *scalar_arm
        .iter()
        .max_by_key(|(value, _)| *value)
        .expect("a scalar literal");
    let decoded = DeclDecoder::new(&view, WalkBudget::default())
        .decode_expr(base + u64::try_from(largest_at).expect("in range"))
        .expect("the scalar literal decodes");
    let ExprNode::Lit {
        literal: Literal::Nat(nat),
    } = decoded.node()
    else {
        panic!("an `Expr.lit` holding a natural number");
    };
    assert_eq!(
        (largest, nat.to_u64()),
        (4_294_967_296, Some(4_294_967_296)),
        "the largest scalar-arm literal is 2^32 and DOES fit a `u64`. The two \
         arms are told apart by a property of the decoded value, not by where \
         this cell looked - and 2^32 against 2^64 puts them on opposite sides \
         of the representation boundary rather than at an arbitrary split"
    );
}

/// The walk is closed - and the fixtures have no `mpz`, but the corpus does.
///
/// `7a0a90fa` said the two scalar predicates could have been separated by "an
/// unresolvable non-boxed word". That was offered as the reason its agreement
/// was worth measuring, and I did not check that such a word exists. It does
/// not: across all four modules, EVERY non-boxed slot word resolves to a walked
/// object. Zero dangling, over 215,995 resolving pointers in Prelude alone. So
/// the predicates agree on every slot rather than merely per shape, and the
/// reason I gave for the agreement was not a reason. That aside is corrected.
///
/// A ZERO NEEDS A CONTROL, and this one especially: the walk DEFINES
/// resolvability by adding whatever it can follow, so "everything resolves"
/// risks being the walk agreeing with itself. It is not quite that - a word is
/// unresolvable when it is misaligned, below the header, or past end-of-file,
/// and those are real conditions a malformed pointer would meet. But the
/// stronger control is what the pointers LAND ON: every one of Prelude's 88,880
/// walked objects carries a ZERO reference count in its header. A pointer into
/// arbitrary bytes would have to find a zero rc and one of a dozen-odd tags to
/// pass unnoticed. That is evidence the closure is real, not a proof of it, and
/// it is stated at that strength.
///
/// THE TAG INVENTORY, and the thing it turned up. Pinning the non-constructor
/// tags present per module gives `[246, 249]` for all three C3 fixtures and
/// `[246, 249, 250]` for Prelude. `abi::TAG_MPZ` IS 250, and Prelude holds TWO
/// of them - each reachable from `constants`, each held by exactly one
/// single-field object.
///
/// THAT RETIRES A BLOCK I HAVE DECLARED REPEATEDLY. Across many comments on
/// this bead I recorded the `mpz` rules as needing "an object no fixture
/// builds". The fixture half is still true and is asserted here - all three C3
/// fixtures have none. What was never true is the conclusion I drew from it:
/// the corpus these cells ALREADY READ contains two, in the declaration graph,
/// so a corpus-based `mpz` pin needs no hand-built object. A block is a claim
/// and it expires; this one expired without my noticing because I kept
/// restating it instead of re-testing it.
///
/// This cell does not write that pin - it is a different decoder path and
/// belongs in its own increment. It records that the obstacle named for it is
/// gone.
///
/// POPULATION SCOPE: all four modules, each asserted by name; the object and
/// pointer counts are per module, not pooled into a total that could hide a
/// zero.
#[test]
fn the_walk_is_closed_and_the_fixtures_have_no_mpz() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut closure: Vec<(String, usize, usize, usize)> = Vec::new();
    let mut headers: Vec<(String, usize, usize)> = Vec::new();
    let mut foreign_tags: Vec<(String, Vec<u8>)> = Vec::new();
    let mut mpz_facts: Vec<(String, usize, usize, usize)> = Vec::new();

    for (module, bytes) in &modules {
        let bytes = bytes.as_slice();
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        let mut boxed = 0usize;
        let mut resolving = 0usize;
        let mut dangling = 0usize;
        let mut nonzero_rc = 0usize;
        let mut tags: BTreeSet<u8> = BTreeSet::new();

        for object in &objects {
            // Low 32 bits of the header word are the reference count, which a
            // compacted region stores as zero.
            if word_at(bytes, object.off) & 0xFFFF_FFFF != 0 {
                nonzero_rc += 1;
            }
            if object.tag > abi::TAG_MAX_CTOR_TAG {
                tags.insert(object.tag);
            }

            let words: Vec<u64> = if object.tag <= abi::TAG_MAX_CTOR_TAG {
                (0..usize::from(object.other))
                    .map(|slot| word_at(bytes, object.off + 8 + 8 * slot))
                    .collect()
            } else if object.tag == abi::TAG_ARRAY {
                (0..word_at(bytes, object.off + 8))
                    .map(|i| word_at(bytes, object.off + 24 + 8 * i as usize))
                    .collect()
            } else {
                Vec::new()
            };
            for word in words {
                if word & 1 == 1 {
                    boxed += 1;
                } else if resolve(word).is_some() {
                    resolving += 1;
                } else {
                    dangling += 1;
                }
            }
        }
        closure.push((module.clone(), boxed, resolving, dangling));
        headers.push((module.clone(), objects.len(), nonzero_rc));
        foreign_tags.push((module.clone(), tags.into_iter().collect()));

        // The `mpz` objects, per node.
        let mpz: Vec<usize> = objects
            .iter()
            .filter(|o| o.tag == abi::TAG_MPZ)
            .map(|o| o.off)
            .collect();
        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root");
        let constants = reachable_from(bytes, base, word_at(bytes, root + 24));
        let in_constants = mpz.iter().filter(|off| constants.contains(off)).count();
        let single_holder = mpz
            .iter()
            .filter(|&&target| {
                objects
                    .iter()
                    .filter(|holder| {
                        holder.tag <= abi::TAG_MAX_CTOR_TAG
                            && (0..usize::from(holder.other)).any(|slot| {
                                resolve(word_at(bytes, holder.off + 8 + 8 * slot)) == Some(target)
                            })
                    })
                    .count()
                    == 1
            })
            .count();
        mpz_facts.push((module.clone(), mpz.len(), in_constants, single_holder));
    }

    let keep = |all: Vec<(&str, usize, usize, usize)>| -> Vec<(String, usize, usize, usize)> {
        all.into_iter()
            .filter(|(m, _, _, _)| prelude_loaded || *m != "Init/Prelude.olean")
            .map(|(m, a, b, c)| (m.to_owned(), a, b, c))
            .collect()
    };

    // Nothing dangles.
    assert_eq!(
        closure,
        keep(vec![
            ("Init.olean", 8, 205, 0),
            ("Init.BinderNameHint.olean", 87, 431, 0),
            ("Init.SizeOfLemmas.olean", 314, 1332, 0),
            ("Init/Prelude.olean", 17058, 215995, 0),
        ]),
        "boxed slots, resolving pointers, and NON-BOXED UNRESOLVABLE words - \
         zero of the last in every module. `7a0a90fa` offered such a word as \
         the reason its two predicates might disagree; there are none, so the \
         predicates agree on every slot and that reason was not a reason"
    );

    // The control on the zero.
    assert_eq!(
        headers
            .iter()
            .map(|(m, n, bad)| (m.as_str(), *n, *bad))
            .collect::<Vec<_>>(),
        [
            ("Init.olean", 158, 0),
            ("Init.BinderNameHint.olean", 267, 0),
            ("Init.SizeOfLemmas.olean", 795, 0),
            ("Init/Prelude.olean", 88880, 0),
        ]
        .into_iter()
        .filter(|(m, _, _)| prelude_loaded || *m != "Init/Prelude.olean")
        .collect::<Vec<_>>(),
        "walked objects, and those whose header carries a NON-ZERO reference \
         count: none. The walk defines resolvability, so `everything resolves` \
         needs a control; a pointer into arbitrary bytes would have to land on \
         a zero rc to pass unnoticed. Evidence that the closure is real, not a \
         proof of it"
    );

    // The inventory, and what it turned up.
    assert_eq!(
        foreign_tags
            .iter()
            .map(|(m, t)| (m.as_str(), t.clone()))
            .collect::<Vec<_>>(),
        [
            ("Init.olean", vec![abi::TAG_ARRAY, abi::TAG_STRING]),
            (
                "Init.BinderNameHint.olean",
                vec![abi::TAG_ARRAY, abi::TAG_STRING]
            ),
            (
                "Init.SizeOfLemmas.olean",
                vec![abi::TAG_ARRAY, abi::TAG_STRING]
            ),
            (
                "Init/Prelude.olean",
                vec![abi::TAG_ARRAY, abi::TAG_STRING, abi::TAG_MPZ]
            ),
        ]
        .into_iter()
        .filter(|(m, _)| prelude_loaded || *m != "Init/Prelude.olean")
        .collect::<Vec<_>>(),
        "the non-constructor tags present in each module. Only Prelude has \
         `TAG_MPZ`"
    );
    assert_eq!(
        mpz_facts,
        keep(vec![
            ("Init.olean", 0, 0, 0),
            ("Init.BinderNameHint.olean", 0, 0, 0),
            ("Init.SizeOfLemmas.olean", 0, 0, 0),
            ("Init/Prelude.olean", 2, 2, 2),
        ]),
        "`mpz` objects, those reachable from `constants`, and those held by \
         exactly one object. THE FIXTURES HAVE NONE - which is the half of my \
         standing block that was true - but the corpus these cells already read \
         holds TWO, both in the declaration graph. The conclusion I drew from \
         the fixture half, that an `mpz` pin needs an object nothing builds, \
         does not follow and has not for as long as this file has read Prelude"
    );
}

/// The coarsening merges ten shapes - measuring `ebfa87eb`'s own aside.
///
/// `ebfa87eb` closed with "split implies more than one field signature and not
/// the reverse". The first half is a derivation. THE SECOND HALF IS AN
/// EXISTENCE CLAIM and I did not measure it: if no shape had many signatures
/// and one pattern, the distinction would be true and do no work - the
/// true-but-empty failure that same cell had just named in someone else's
/// sentence, which is mine.
///
/// It is not empty. Over the four modules:
///
///   constructor shapes                              36
///   more than one FIELD SIGNATURE                   25
///   more than one boxed-or-pointer PATTERN          15
///   many signatures but exactly ONE pattern         10
///
/// and 15 + 10 = 25, asserted as a decomposition rather than three separate
/// counts. The ten are what the coarsening merges, and they are not marginal:
/// `tag 5 arity 2` has 33 signatures across 26,394 objects and every one of
/// them has both slots as pointers; `tag 6 arity 3` has 60 across 10,852. Those
/// are shapes whose signature varies only in WHICH pointee sits in a slot,
/// which is exactly the variation a pattern is meant to ignore.
///
/// THE DERIVATION HOLDS EMPIRICALLY TOO: zero shapes have more than one pattern
/// and only one signature. That direction is forced - different patterns are
/// different signatures - so measuring it is a control on the walk rather than
/// a discovery, and it is asserted for that reason.
///
/// AND `ebfa87eb`'S 15 IS NOT A PREDICATE ARTEFACT. That cell called a slot
/// scalar when its low bit was set; the signature audit calls a slot scalar
/// when it does not resolve to a walked object. They select the SAME 15 shapes
/// here. Measured rather than assumed, because I used one predicate and quoted
/// a number computed with the other.
///
/// This paragraph used to add "an unresolvable non-boxed word would separate
/// them", offered as the reason the agreement was worth measuring.
/// `the_walk_is_closed_and_the_fixtures_have_no_mpz` measures that case at
/// ZERO instances in all four modules, so the two predicates do not merely
/// agree per shape - they agree on every slot, and nothing could have
/// separated them. The agreement is still worth pinning; the reason I gave for
/// it was not a reason.
///
/// POPULATION SCOPE: all four modules pooled, which is the signature audit's
/// population, so the 25 is comparable with its per-shape counts. The
/// shape-level tallies are identical if Prelude is taken alone - 36, 25, 15,
/// 10 - even though the object counts are not, and that is asserted too rather
/// than left as an impression.
#[test]
fn the_coarsening_merges_ten_shapes() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }
    if !prelude_loaded {
        return;
    }

    // Two runs over the same walk: every module, then Prelude alone.
    let mut tallies: Vec<(usize, usize, usize, usize)> = Vec::new();
    let mut merged: Vec<(u8, u8, usize, usize)> = Vec::new();
    let mut predicates_agree = Vec::new();

    for pooled in [true, false] {
        let chosen: Vec<&(String, Vec<u8>)> = modules
            .iter()
            .filter(|(name, _)| pooled || name == "Init/Prelude.olean")
            .collect();

        let mut signatures: std::collections::BTreeMap<(u8, u8), BTreeSet<String>> =
            std::collections::BTreeMap::new();
        let mut by_resolve: std::collections::BTreeMap<(u8, u8), BTreeSet<String>> =
            std::collections::BTreeMap::new();
        let mut by_boxed: std::collections::BTreeMap<(u8, u8), BTreeSet<String>> =
            std::collections::BTreeMap::new();
        let mut population: std::collections::BTreeMap<(u8, u8), usize> =
            std::collections::BTreeMap::new();

        for (_, bytes) in chosen {
            let bytes = bytes.as_slice();
            let (objects, base) = objects_of(bytes);
            let at: std::collections::BTreeMap<usize, Obj> =
                objects.iter().map(|o| (o.off, *o)).collect();
            let resolve = |word: u64| -> Option<usize> {
                (word & 1 == 0)
                    .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                    .flatten()
                    .filter(|off| at.contains_key(off))
            };
            for object in &objects {
                if object.tag > abi::TAG_MAX_CTOR_TAG {
                    continue;
                }
                let shape = (object.tag, object.other);
                *population.entry(shape).or_default() += 1;
                let mut signature = Vec::new();
                let mut resolved = Vec::new();
                let mut boxed = Vec::new();
                for slot in 0..usize::from(object.other) {
                    let word = word_at(bytes, object.off + 8 + 8 * slot);
                    match resolve(word) {
                        // The signature audit's own rule: a slot is scalar when
                        // it does not resolve to a walked object.
                        Some(child) => {
                            let child = at.get(&child).expect("resolved above");
                            signature.push(format!("{}/{}", child.tag, child.other));
                            resolved.push("ptr");
                        }
                        None => {
                            signature.push("scalar".to_owned());
                            resolved.push("scalar");
                        }
                    }
                    // `ebfa87eb`'s rule: a slot is scalar when its low bit is set.
                    boxed.push(if word & 1 == 1 { "boxed" } else { "ptr" });
                }
                signatures
                    .entry(shape)
                    .or_default()
                    .insert(signature.join("|"));
                by_resolve
                    .entry(shape)
                    .or_default()
                    .insert(resolved.join("|"));
                by_boxed.entry(shape).or_default().insert(boxed.join("|"));
            }
        }

        let many_signatures: BTreeSet<(u8, u8)> = signatures
            .iter()
            .filter(|(_, set)| set.len() > 1)
            .map(|(shape, _)| *shape)
            .collect();
        let many_patterns: BTreeSet<(u8, u8)> = by_resolve
            .iter()
            .filter(|(_, set)| set.len() > 1)
            .map(|(shape, _)| *shape)
            .collect();
        let split_by_boxed: BTreeSet<(u8, u8)> = by_boxed
            .iter()
            .filter(|(_, set)| set.len() > 1)
            .map(|(shape, _)| *shape)
            .collect();

        // Shapes the coarsening actually merges.
        let coarsened: Vec<(u8, u8, usize, usize)> = signatures
            .iter()
            .filter(|(shape, set)| set.len() > 1 && !many_patterns.contains(shape))
            .map(|(shape, set)| {
                (
                    shape.0,
                    shape.1,
                    set.len(),
                    *population.get(shape).expect("counted"),
                )
            })
            .collect();

        tallies.push((
            signatures.len(),
            many_signatures.len(),
            many_patterns.len(),
            coarsened.len(),
        ));
        predicates_agree.push(many_patterns == split_by_boxed);
        // The forced direction: no shape splits by pattern without splitting by
        // signature.
        assert!(
            many_patterns.is_subset(&many_signatures),
            "a differing pattern is a differing signature by construction; a \
             counterexample would mean the walk disagrees with itself"
        );
        if pooled {
            merged = coarsened;
        }
    }

    // The decomposition, not three loose counts.
    assert_eq!(
        tallies[0],
        (36, 25, 15, 10),
        "pooled over the four modules: constructor shapes, those with more than \
         one FIELD SIGNATURE, those with more than one boxed-or-pointer \
         PATTERN, and those with many signatures but exactly ONE pattern"
    );
    assert_eq!(
        tallies[0].2 + tallies[0].3,
        tallies[0].1,
        "15 + 10 = 25, so every multi-signature shape is either split by pattern \
         or merged by it and none is unaccounted for"
    );

    // What the coarsening merges, per shape rather than as a total.
    assert_eq!(
        merged,
        vec![
            (2, 1, 8, 78),
            (3, 2, 6, 30),
            (4, 1, 3, 122),
            (5, 1, 2, 163),
            (5, 2, 33, 26394),
            (6, 3, 60, 10852),
            (8, 4, 3, 8),
            (9, 1, 2, 61),
            (10, 2, 4, 83),
            (11, 3, 2, 150),
        ],
        "the ten shapes with many signatures and one pattern, as (tag, arity, \
         signatures, objects). `ebfa87eb`'s `and not the reverse` is therefore \
         SUBSTANTIVE and not the true-but-empty kind it had just caught \
         elsewhere: `tag 5 arity 2` alone merges 33 signatures over 26,394 \
         objects whose slots are always both pointers"
    );

    // The predicate `ebfa87eb` used and the one the audit uses agree.
    assert_eq!(
        predicates_agree,
        vec![true, true],
        "`ebfa87eb` called a slot scalar by its low bit and the signature audit \
         calls it scalar when it does not resolve. Those are different tests \
         and they select the SAME shapes here, pooled and in Prelude alone - \
         measured, because that cell quoted a count computed with the other rule"
    );

    // Shape-level tallies do not move when the fixtures drop out.
    assert_eq!(
        tallies[1],
        (36, 25, 15, 10),
        "Prelude alone gives the same four shape-level counts as the pooled \
         walk, though its object populations are smaller - so the tallies above \
         are not carried by the fixtures"
    );
}

/// Necessary, not sufficient - measuring two sentences `a5e8cb68` left behind.
///
/// That cell asserted two things in prose and measured neither. Both are wrong,
/// and they are wrong in opposite directions, which is why one cell measures
/// both. The sentences are corrected in the same commit.
///
/// FIRST: "a parent whose own identity is undecided cannot decide its child's".
/// Call a constructor shape SPLIT when its objects do not all share one
/// boxed-or-pointer slot pattern - that is, when the shape alone does not fix
/// which slots hold scalars. Prelude has 36 constructor shapes and 15 are
/// split. Crossing that against the 18 arrival contexts of `a5e8cb68`:
///
///   unsplit parent, pure context     4
///   split   parent, pure context    12
///   split   parent, mixed context    2
///   unsplit parent, mixed context    0
///
/// The zero is real and one-directional: NO mixed context has an unsplit
/// parent, so a split parent is NECESSARY. It is nowhere near sufficient -
/// twelve of the fourteen split-parent contexts are perfectly pure. An
/// undecided parent usually does decide its child. The sentence claimed the
/// implication that does not hold.
///
/// This is the shape `fln-shrinking-allowance-guard-direction` warns about: the
/// true statement is one-way, and stating it as an equivalence turns a
/// twelve-context majority into counterexamples.
///
/// SECOND: "even a rule keyed on context would have to agree with itself across
/// arrivals". That reads as a hazard and names none. ZERO of the 414
/// multi-arrival objects reach a pure context that disagrees with another pure
/// context, AND NONE CAN: a pure context's class is the class of every child it
/// has, so two pure contexts naming one object must name it the same. The
/// constraint is satisfied by construction. What the 414 actually decompose
/// into is 333 that arrive only through pure contexts and 81 that touch at
/// least one mixed one - which is a fact, where the warning was not.
///
/// SPLIT IS COARSER THAN THE SIGNATURE AUDIT, and the two do not conflict. That
/// audit counts distinct FIELD signatures per shape; this counts distinct
/// boxed-or-pointer patterns, which merges signatures that differ only in which
/// pointee type sits in a slot. So split implies more than one field signature
/// and not the reverse, and 15 split shapes is a floor under that audit's
/// counts rather than a competing number.
///
/// Its `(2, 2)` population is 1,955 against this cell's 1,938 for the same
/// reason and not a disagreement: that audit pools four modules and this one is
/// Prelude alone, 1938 + 1 + 10 + 6.
///
/// POPULATION SCOPE: `Init/Prelude.olean`, asserted rather than left implicit.
#[test]
fn the_inheritance_claim_is_necessary_not_sufficient() {
    let Some(lib) = reference_lib() else {
        return;
    };
    let Ok(bytes) = std::fs::read(lib.join("Init/Prelude.olean")) else {
        return;
    };
    let bytes = bytes.as_slice();

    let (objects, base) = objects_of(bytes);
    let at: std::collections::BTreeMap<usize, Obj> = objects.iter().map(|o| (o.off, *o)).collect();
    let resolve = |word: u64| -> Option<usize> {
        (word & 1 == 0)
            .then(|| usize::try_from(word.wrapping_sub(base)).ok())
            .flatten()
            .filter(|off| at.contains_key(off))
    };

    // A shape is SPLIT when its objects disagree about which slots are scalars.
    let mut patterns: std::collections::BTreeMap<(u8, u8), BTreeSet<Vec<bool>>> =
        std::collections::BTreeMap::new();
    for object in &objects {
        if object.tag > abi::TAG_MAX_CTOR_TAG {
            continue;
        }
        let pattern: Vec<bool> = (0..usize::from(object.other))
            .map(|slot| word_at(bytes, object.off + 8 + 8 * slot) & 1 == 1)
            .collect();
        patterns
            .entry((object.tag, object.other))
            .or_default()
            .insert(pattern);
    }
    let split: BTreeSet<(u8, u8)> = patterns
        .iter()
        .filter(|(_, seen)| seen.len() > 1)
        .map(|(shape, _)| *shape)
        .collect();

    // `a5e8cb68`'s contexts, rebuilt rather than quoted.
    let two_two: BTreeSet<usize> = objects
        .iter()
        .filter(|o| (o.tag, o.other) == (2, 2))
        .map(|o| o.off)
        .collect();
    let class = |off: usize| -> &'static str {
        let word = word_at(bytes, off + 16);
        if word & 1 == 1 {
            "boxed"
        } else if resolve(word).is_some() {
            "pointer"
        } else {
            "unresolved"
        }
    };
    let mut contexts: std::collections::BTreeMap<(u8, u8, usize), BTreeSet<&'static str>> =
        std::collections::BTreeMap::new();
    let mut arrivals: std::collections::BTreeMap<usize, BTreeSet<(u8, u8, usize)>> =
        std::collections::BTreeMap::new();
    for parent in &objects {
        let slots: Vec<(usize, u64)> = if parent.tag <= abi::TAG_MAX_CTOR_TAG {
            (0..usize::from(parent.other))
                .map(|slot| (slot, word_at(bytes, parent.off + 8 + 8 * slot)))
                .collect()
        } else if parent.tag == abi::TAG_ARRAY {
            (0..word_at(bytes, parent.off + 8))
                .map(|i| (usize::MAX, word_at(bytes, parent.off + 24 + 8 * i as usize)))
                .collect()
        } else {
            Vec::new()
        };
        for (slot, word) in slots {
            let Some(child) = resolve(word).filter(|c| two_two.contains(c)) else {
                continue;
            };
            let key = (parent.tag, parent.other, slot);
            contexts.entry(key).or_default().insert(class(child));
            arrivals.entry(child).or_default().insert(key);
        }
    }

    // The cross-tab. The zero is the whole point.
    let mut cross = [[0usize; 2]; 2];
    for (key, classes) in &contexts {
        let parent_split = usize::from(split.contains(&(key.0, key.1)));
        let mixed = usize::from(classes.len() > 1);
        cross[parent_split][mixed] += 1;
    }
    assert_eq!(
        (patterns.len(), split.len()),
        (36, 15),
        "constructor shapes in Prelude, and those whose objects disagree about \
         which slots hold scalars"
    );
    assert_eq!(
        (cross[0][0], cross[0][1], cross[1][0], cross[1][1]),
        (4, 0, 12, 2),
        "arrival contexts by (parent shape is split, context is mixed). NO \
         mixed context has an unsplit parent, so a split parent is NECESSARY. \
         Twelve of the fourteen split-parent contexts are perfectly pure, so it \
         is nowhere near sufficient - `a5e8cb68` claimed the implication that \
         does not hold, and stating a one-way rule as an equivalence turns a \
         twelve-context majority into counterexamples"
    );
    assert_eq!(
        cross.iter().flatten().sum::<usize>(),
        18,
        "and the four cells account for every context, so the zero is a \
         measured absence rather than a group that was never looked at"
    );

    // The second sentence: a hazard that names none.
    let pure: std::collections::BTreeMap<(u8, u8, usize), &'static str> = contexts
        .iter()
        .filter(|(_, classes)| classes.len() == 1)
        .map(|(key, classes)| (*key, *classes.iter().next().expect("one")))
        .collect();
    let multi: Vec<&BTreeSet<(u8, u8, usize)>> =
        arrivals.values().filter(|set| set.len() > 1).collect();
    let disagreeing = multi
        .iter()
        .filter(|set| {
            set.iter()
                .filter_map(|key| pure.get(key))
                .collect::<BTreeSet<_>>()
                .len()
                > 1
        })
        .count();
    let pure_only = multi
        .iter()
        .filter(|set| set.iter().all(|key| pure.contains_key(key)))
        .count();
    assert_eq!(
        (multi.len(), disagreeing, pure_only, multi.len() - pure_only),
        (414, 0, 333, 81),
        "of the 414 multi-arrival objects, ZERO reach two pure contexts that \
         disagree - and none can, since a pure context's class is the class of \
         every child it has, so two of them naming one object must name it the \
         same. `a5e8cb68` wrote that as a hazard; it is satisfied by \
         construction. The decomposition is the fact: 333 arrive only through \
         pure contexts and 81 touch at least one mixed one"
    );
}

/// The arrival context does not discriminate either - and one refinement of two.
///
/// `e0dd56f8` ended by saying that where tag, arity and size fail to identify a
/// constructor, "the field a walk arrived through" succeeds. I wrote that as a
/// summary and did not measure it. IT IS FALSE, and this cell is the
/// measurement that says so; the sentence is corrected in the same commit.
///
/// Every `(2, 2)` object in Prelude is reached from at least one parent - 1,938
/// objects across 8,654 arrival edges, none orphaned, so the denominator is the
/// whole population. Grouping those edges by `(parent tag, parent arity, slot)`
/// gives EIGHTEEN distinct contexts. SIXTEEN are pure. TWO are not:
///
///   parent `(1, 2)` slot 0   ->  583 boxed  and  106 pointer
///   parent `(1, 1)` slot 0   ->   75 boxed  and   10 pointer
///
/// THE AMBIGUITY IS INHERITED, which is the part worth having. Both mixed
/// parents wear shapes this file has already shown to be ambiguous - `(1, 2)`
/// is the cons-or-name shape that blocks `list_ptrs`, and `(1, 1)` appears in
/// `e0dd56f8`'s four-shape family.
///
/// This paragraph used to end "a parent whose own identity is undecided cannot
/// decide its child's". Measured in
/// `the_inheritance_claim_is_necessary_not_sufficient`, that is FALSE: an
/// undecided parent is NECESSARY for a mixed context and nowhere near
/// sufficient - twelve contexts have an undecided parent and decide their child
/// perfectly. The one-directional form is the true one.
///
/// ONE MORE BIT RESOLVES ONE OF THEM AND NOT THE OTHER. Refining the `(1, 2)`
/// parent by its OWN second field splits the 689 edges into three contexts, all
/// PURE: a string tail gives 583 boxed, a nil tail 88 pointers, a cons tail 18.
/// Refining the `(1, 1)` parent by its size does NOT: size 16 is pure with 56
/// boxed, but size 24 carries 19 boxed AND 10 pointers.
///
/// So the answer is partial and is pinned per context rather than as a slogan.
/// I tried EXACTLY ONE refinement on the `(1, 1)` side - its size - and it
/// fails; this cell says that and does not say no refinement exists, which
/// would be a claim about every rule I did not try.
///
/// CONTEXTS ARE NOT UNIQUE PER OBJECT EITHER: 414 of the 1,938 are reached from
/// more than one distinct context.
///
/// That sentence used to continue "so even a rule keyed on context would have
/// to agree with itself across arrivals", as though it named a hazard. It does
/// not. Measured: ZERO of the 414 arrive through two pure contexts that
/// disagree, and none can - a pure context's class is the class of every child
/// it has, so two of them naming one object must name it the same. The
/// requirement is satisfied by construction and the warning was empty.
///
/// Both refinements are pinned with their edge counts reconciled against the
/// mixed totals they refine - 583 + 88 + 18 against 689, and 56 + 19 + 10
/// against 85 - so a refinement cannot silently drop edges.
///
/// POPULATION SCOPE: `Init/Prelude.olean`, asserted rather than left implicit.
#[test]
fn the_arrival_context_does_not_discriminate_either() {
    let Some(lib) = reference_lib() else {
        return;
    };
    let Ok(bytes) = std::fs::read(lib.join("Init/Prelude.olean")) else {
        return;
    };
    let bytes = bytes.as_slice();

    let (objects, base) = objects_of(bytes);
    let at: std::collections::BTreeMap<usize, Obj> = objects.iter().map(|o| (o.off, *o)).collect();
    let resolve = |word: u64| -> Option<usize> {
        (word & 1 == 0)
            .then(|| usize::try_from(word.wrapping_sub(base)).ok())
            .flatten()
            .filter(|off| at.contains_key(off))
    };
    let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

    // What slot 1 of a `(2, 2)` object holds - the thing a rule would decide.
    let class = |off: usize| -> &'static str {
        let word = word_at(bytes, off + 16);
        if word & 1 == 1 {
            "boxed"
        } else if resolve(word).is_some() {
            "pointer"
        } else {
            "unresolved"
        }
    };
    let two_two: BTreeSet<usize> = objects
        .iter()
        .filter(|o| (o.tag, o.other) == (2, 2))
        .map(|o| o.off)
        .collect();

    // Every arrival edge, grouped by (parent tag, parent arity, slot).
    let mut contexts: std::collections::BTreeMap<
        (u8, u8, usize),
        std::collections::BTreeMap<&'static str, usize>,
    > = std::collections::BTreeMap::new();
    let mut edges = 0usize;
    let mut arrivals: std::collections::BTreeMap<usize, BTreeSet<(u8, u8, usize)>> =
        std::collections::BTreeMap::new();
    // The two refinements.
    let mut by_tail: std::collections::BTreeMap<
        &'static str,
        std::collections::BTreeMap<&'static str, usize>,
    > = std::collections::BTreeMap::new();
    let mut by_size: std::collections::BTreeMap<
        u16,
        std::collections::BTreeMap<&'static str, usize>,
    > = std::collections::BTreeMap::new();

    for parent in &objects {
        let slots: Vec<(usize, u64)> = if parent.tag <= abi::TAG_MAX_CTOR_TAG {
            (0..usize::from(parent.other))
                .map(|slot| (slot, word_at(bytes, parent.off + 8 + 8 * slot)))
                .collect()
        } else if parent.tag == abi::TAG_ARRAY {
            (0..word_at(bytes, parent.off + 8))
                .map(|i| (usize::MAX, word_at(bytes, parent.off + 24 + 8 * i as usize)))
                .collect()
        } else {
            Vec::new()
        };
        for (slot, word) in slots {
            let Some(child) = resolve(word) else {
                continue;
            };
            if !two_two.contains(&child) {
                continue;
            }
            edges += 1;
            let key = (parent.tag, parent.other, slot);
            *contexts
                .entry(key)
                .or_default()
                .entry(class(child))
                .or_default() += 1;
            arrivals.entry(child).or_default().insert(key);

            if (parent.tag, parent.other) == (1, 2) && slot == 0 {
                let second = word_at(bytes, parent.off + 16);
                let tail = resolve(second);
                let kind = if second & 1 == 1 {
                    if second >> 1 == 0 {
                        "nil-tail"
                    } else {
                        "scalar-tail"
                    }
                } else {
                    match tail.and_then(shape) {
                        Some((1, 2)) => "cons-tail",
                        _ if tail.and_then(|t| at.get(&t)).map(|o| o.tag)
                            == Some(abi::TAG_STRING) =>
                        {
                            "string-tail"
                        }
                        _ => "other-tail",
                    }
                };
                *by_tail
                    .entry(kind)
                    .or_default()
                    .entry(class(child))
                    .or_default() += 1;
            }
            if (parent.tag, parent.other) == (1, 1) && slot == 0 {
                *by_size
                    .entry(parent.cs_sz)
                    .or_default()
                    .entry(class(child))
                    .or_default() += 1;
            }
        }
    }

    // The denominator is the whole population.
    assert_eq!(
        (two_two.len(), edges, arrivals.len()),
        (1938, 8654, 1938),
        "every `(2, 2)` object is reached from at least one parent, so no object \
         is missing from the context tally"
    );

    // Sixteen pure, two mixed.
    let mixed: Vec<((u8, u8, usize), Vec<(&'static str, usize)>)> = contexts
        .iter()
        .filter(|(_, classes)| classes.len() > 1)
        .map(|(key, classes)| (*key, classes.iter().map(|(k, v)| (*k, *v)).collect()))
        .collect();
    assert_eq!(
        (contexts.len(), contexts.len() - mixed.len(), mixed.len()),
        (18, 16, 2),
        "arrival contexts, pure ones, and MIXED ones. Two contexts yield both \
         kinds, so `(parent shape, slot)` does not decide what slot 1 holds - \
         which is what `e0dd56f8`'s closing sentence claimed it did"
    );
    assert_eq!(
        mixed,
        vec![
            ((1, 1, 0), vec![("boxed", 75), ("pointer", 10)]),
            ((1, 2, 0), vec![("boxed", 583), ("pointer", 106)]),
        ],
        "and BOTH mixed parents wear shapes this file has already shown to be \
         ambiguous - `(1, 2)` is the cons-or-name shape that blocks \
         `list_ptrs`. An undecided parent is NECESSARY for a mixed context and \
         not sufficient; the first version of this message said an undecided \
         parent `cannot decide its child's`, which \
         `the_inheritance_claim_is_necessary_not_sufficient` measures false"
    );

    // One refinement works.
    assert_eq!(
        by_tail
            .iter()
            .map(|(k, v)| (*k, v.iter().map(|(c, n)| (*c, *n)).collect::<Vec<_>>()))
            .collect::<Vec<_>>(),
        vec![
            ("cons-tail", vec![("pointer", 18)]),
            ("nil-tail", vec![("pointer", 88)]),
            ("string-tail", vec![("boxed", 583)]),
        ],
        "refining the `(1, 2)` parent by its OWN second field makes all three \
         sub-contexts PURE"
    );
    assert_eq!(
        by_tail.values().flat_map(|v| v.values()).sum::<usize>(),
        689,
        "and accounts for every one of the 583 + 106 edges it refines, so the \
         refinement cannot have silently dropped any"
    );

    // The other does not.
    assert_eq!(
        by_size
            .iter()
            .map(|(k, v)| (*k, v.iter().map(|(c, n)| (*c, *n)).collect::<Vec<_>>()))
            .collect::<Vec<_>>(),
        vec![
            (16, vec![("boxed", 56)]),
            (24, vec![("boxed", 19), ("pointer", 10)]),
        ],
        "refining the `(1, 1)` parent by its SIZE does not: size 24 still \
         carries both. EXACTLY ONE refinement was tried here, and it fails - \
         that is not a claim that no refinement exists, which would be a \
         statement about every rule I did not try"
    );
    assert_eq!(
        by_size.values().flat_map(|v| v.values()).sum::<usize>(),
        85,
        "accounting for every one of the 75 + 10 edges it refines"
    );

    // Contexts are not unique per object either.
    assert_eq!(
        arrivals.values().filter(|set| set.len() > 1).count(),
        414,
        "414 of the 1,938 are reached from more than one distinct context. The \
         first version added `so even a context-keyed rule would have to agree \
         with itself across arrivals`, which reads as a hazard and is not one - \
         see `the_inheritance_claim_is_necessary_not_sufficient`, where zero of \
         the 414 disagree and none can"
    );
}

/// The size rule fails for the numeric-name shape too - and in a worse place.
///
/// `daaaabe2` measured that size 24 does not identify a cons cell: 99 objects
/// wear `(1, 2, 24)` without being one, which is what BLOCKS a size rule in
/// `list_ptrs`. The saving grace there was location - `1dd7c288` measured 0 of
/// those 99 reachable from `constants`, so the declaration graph never meets
/// them.
///
/// This asks the same question of the OTHER two-field shape, `(2, 2)`, which is
/// the numeric name component's form. The answer is worse in exactly the way
/// that matters.
///
/// SIZE DOES NOT SEPARATE IT EITHER. Of Prelude's 1,938 `(2, 2)` objects, 1,826
/// carry a boxed scalar in slot 1 and 112 carry a POINTER. Splitting by size
/// does not sort them: `(2, 2, 24)` is 64 pointer-holders, but `(2, 2, 32)` is
/// 1,826 boxed AND 48 pointer-holders. A decoder that accepted `(2, 2, 32)` and
/// read slot 1 as a number would read 48 pointers as numbers.
///
/// I MEASURED THIS WRONG FIRST, and the shape of the mistake is worth keeping.
/// Comparing the string-holders against the boxed ones gave a clean split - all
/// 64 at size 24, all 1,826 at size 32 - and it looked like a discriminator. It
/// is not: 48 of the 112 pointer-holders are NOT string-holders, and they sit
/// at size 32 with the boxed ones. Two subsets agreed and the complement
/// disagreed, and only counting the complement showed it.
///
/// AND THEY ARE INSIDE THE DECLARATION GRAPH. All 48 are reachable from
/// `constants`; 7 from `entries` as well. That is the opposite of the 99, which
/// `constants` never reaches. So the `(1, 2)` collision is blocked-but-remote
/// and this one is blocked-and-local: the objects a size test would misread are
/// exactly the ones a declaration walk visits.
///
/// NOT A PRELUDE ARTEFACT: `Init.SizeOfLemmas.olean` contains one such object,
/// also reachable from `constants`, in a fixture of 26 arrays and 795 objects.
///
/// A FOUR-SHAPE FAMILY - one hop, not a closure. Both fields of all 48 resolve
/// into the same four-shape set - `(1, 1, 24)`, `(2, 2, 32)`, `(3, 2, 32)`,
/// `(4, 1, 24)` - and the set is identical for slot 0 and slot 1. That is ONE
/// HOP from the 48 and nothing more; whether the family is closed under further
/// hops is not measured here and the word `closed` is deliberately not used.
/// This cell pins the set
/// structurally and does NOT name the type: `c4cbf83c` was reddened for reading
/// a shape as an identity, and a fourth shape sharing `(2, 2, 32)` would break
/// any name I put on it.
///
/// WHAT THIS DOES NOT DO: it does not unblock `list_ptrs` and does not propose
/// a rule. It generalises the block - tag, arity and size together do not
/// identify a constructor across TYPES.
///
/// The first version of this paragraph ended "and only the field a walk arrived
/// through does". That was written as a summary and never measured, and
/// `the_arrival_context_does_not_discriminate_either` measures it FALSE: the
/// parent's shape and slot leave two of eighteen contexts mixed. What actually
/// disambiguates is not established by either cell.
///
/// POPULATION SCOPE: the cross-tab covers all four modules with the fixtures
/// participating; the reachability facts are named per module.
#[test]
fn the_size_rule_fails_for_the_numeric_name_shape_too() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut cross: Vec<(String, Vec<((u16, &'static str), usize)>)> = Vec::new();
    let mut in_constants: Vec<(String, usize, usize)> = Vec::new();
    let mut non_cons_in_constants: Vec<(String, usize, usize)> = Vec::new();
    let mut families: Vec<(String, Vec<(u8, u8, u16)>)> = Vec::new();

    for (module, bytes) in &modules {
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let profile = |off: usize| at.get(&off).map(|o| (o.tag, o.other, o.cs_sz));

        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root");
        let constants = reachable_from(bytes, base, word_at(bytes, root + 24));

        let mut tally: std::collections::BTreeMap<(u16, &'static str), usize> =
            std::collections::BTreeMap::new();
        let mut pointer_at_32: Vec<usize> = Vec::new();
        for object in &objects {
            if (object.tag, object.other) != (2, 2) {
                continue;
            }
            let word = word_at(bytes, object.off + 16);
            let kind = if word & 1 == 1 {
                "boxed"
            } else if resolve(word).is_some() {
                "pointer"
            } else {
                "unresolved"
            };
            *tally.entry((object.cs_sz, kind)).or_default() += 1;
            if object.cs_sz == 32 && kind == "pointer" {
                pointer_at_32.push(object.off);
            }
        }
        cross.push((module.clone(), tally.into_iter().collect()));

        // Where the counterexamples live.
        let reached = pointer_at_32
            .iter()
            .filter(|off| constants.contains(off))
            .count();
        in_constants.push((module.clone(), pointer_at_32.len(), reached));

        // The same question for the shape that blocks `list_ptrs`.
        let mut non_cons = 0usize;
        let mut non_cons_reached = 0usize;
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            let cons_shaped = (second & 1 == 1 && second >> 1 == 0)
                || resolve(second)
                    .and_then(|t| at.get(&t))
                    .map(|o| (o.tag, o.other))
                    == Some((1, 2));
            if cons_shaped {
                continue;
            }
            non_cons += 1;
            if constants.contains(&object.off) {
                non_cons_reached += 1;
            }
        }
        non_cons_in_constants.push((module.clone(), non_cons, non_cons_reached));

        // What the counterexamples' own fields resolve to.
        if !pointer_at_32.is_empty() {
            let mut both: BTreeSet<(u8, u8, u16)> = BTreeSet::new();
            for &off in &pointer_at_32 {
                for slot in 0..2 {
                    if let Some(child) = resolve(word_at(bytes, off + 8 + 8 * slot))
                        && let Some(shape) = profile(child)
                    {
                        both.insert(shape);
                    }
                }
            }
            families.push((module.clone(), both.into_iter().collect()));
        }
    }

    let keep = |all: Vec<(&str, usize, usize)>| -> Vec<(String, usize, usize)> {
        all.into_iter()
            .filter(|(m, _, _)| prelude_loaded || *m != "Init/Prelude.olean")
            .map(|(m, a, b)| (m.to_owned(), a, b))
            .collect()
    };

    // Size does not sort slot 1.
    assert_eq!(
        cross
            .iter()
            .map(|(m, t)| (m.as_str(), t.clone()))
            .collect::<Vec<_>>(),
        [
            ("Init.olean", vec![((32, "boxed"), 1)]),
            (
                "Init.BinderNameHint.olean",
                vec![((24, "pointer"), 1), ((32, "boxed"), 9)]
            ),
            (
                "Init.SizeOfLemmas.olean",
                vec![((32, "boxed"), 5), ((32, "pointer"), 1)]
            ),
            (
                "Init/Prelude.olean",
                vec![
                    ((24, "pointer"), 64),
                    ((32, "boxed"), 1826),
                    ((32, "pointer"), 48)
                ]
            ),
        ]
        .into_iter()
        .filter(|(m, _)| prelude_loaded || *m != "Init/Prelude.olean")
        .collect::<Vec<_>>(),
        "`(2, 2)` objects by size and by what slot 1 holds. Size 32 carries \
         BOTH 1,826 boxed scalars and 48 pointers, so a size test cannot decide \
         whether slot 1 is a number. Comparing only the string-holders against \
         the boxed ones gives a clean 24-versus-32 split and is wrong - the \
         complement is what shows it"
    );

    // And they are where a declaration walk goes.
    assert_eq!(
        in_constants,
        keep(vec![
            ("Init.olean", 0, 0),
            ("Init.BinderNameHint.olean", 0, 0),
            ("Init.SizeOfLemmas.olean", 1, 1),
            ("Init/Prelude.olean", 48, 48),
        ]),
        "every pointer-holder at size 32 is reachable from `constants` - 48 of \
         48 in Prelude and 1 of 1 in a C3 fixture, so this is not a Prelude \
         artefact"
    );
    assert_eq!(
        non_cons_in_constants,
        keep(vec![
            ("Init.olean", 0, 0),
            ("Init.BinderNameHint.olean", 0, 0),
            ("Init.SizeOfLemmas.olean", 0, 0),
            ("Init/Prelude.olean", 99, 0),
        ]),
        "against the shape that blocks `list_ptrs`, re-measured here rather \
         than quoted: 99 non-cons objects at `(1, 2, 24)` and `constants` \
         reaches NONE of them. So the cons collision is blocked-but-remote and \
         this one is blocked-and-LOCAL - the objects a size test would misread \
         are exactly the ones a declaration walk visits"
    );

    if !prelude_loaded {
        return;
    }

    // Structurally, without naming a type.
    assert_eq!(
        families
            .iter()
            .map(|(m, f)| (m.as_str(), f.clone()))
            .collect::<Vec<_>>(),
        vec![
            ("Init.SizeOfLemmas.olean", vec![(1, 1, 24), (4, 1, 24)]),
            (
                "Init/Prelude.olean",
                vec![(1, 1, 24), (2, 2, 32), (3, 2, 32), (4, 1, 24)]
            ),
        ],
        "both fields of every counterexample resolve into a small shape set: \
         four in Prelude, and in the fixture a SUBSET of those four, because \
         one object cannot exhibit all of them. Pinned per module rather than \
         merged - the first version of this assertion collapsed both into one \
         set and would have claimed the fixture shows four shapes when it shows \
         two. Left unnamed as well: `c4cbf83c` was reddened for reading a shape \
         as an identity, and one of these four is `(2, 2, 32)` itself, the very \
         shape this cell has just shown to be ambiguous"
    );
    assert!(
        families.iter().all(|(_, f)| f.iter().all(|shape| families
            .last()
            .expect("Prelude last")
            .1
            .contains(shape))),
        "and the fixture's set is contained in Prelude's, so the two are one \
         family seen at two sizes rather than two different families"
    );
}

/// The interned empty array: one object per module, thousands of references.
///
/// `4d5fba7a` found ONE empty array object behind 2,178 slots of the
/// `exportedAxiomsExt` payload and called it sharing. That was a fact about one
/// extension. This asks the module-wide question, and the answer is stronger:
/// EVERY module here contains EXACTLY ONE zero-length array object, and every
/// reference to an empty array in the whole file resolves to it. So the payload
/// slots are not sharing an array with each other, they are naming the module's
/// single empty array - which the payload has no special claim on.
///
/// That makes the earlier finding a corollary rather than a separate fact, and
/// this cell does not re-assert it: with exactly one such object, any set of
/// empty-array references trivially points at the same one.
///
/// OBJECTS AGAINST OCCURRENCES, WITH A REAL COUNTEREXAMPLE. In Prelude 2,999
/// slots name it, from 2,932 DISTINCT objects - the two differ because 62
/// objects name it more than once. `Init.olean` is the sharp case: THREE slots,
/// ONE holder. That holder is the `ModuleData` root itself, which stores the
/// empty array as its `constNames`, its `constants` AND its
/// `extraConstNames` - a module that declares nothing spends three of its five
/// roots on one object. A walk counting occurrences would report three holders
/// there and be wrong by a factor of three.
///
/// The multiplicity histogram is pinned per module and reconciled against both
/// totals, so it cannot drift from either.
///
/// DISCRIMINATING POWER: Prelude holds 2,434 array objects and 2,999 references
/// to an empty one. Without interning there could be up to 2,999 zero-length
/// arrays; there is one. The count is not a consequence of arrays being scarce.
///
/// NOT UNIFORM, AND PINNED PER MODULE BECAUSE OF IT. The set of `ModuleData`
/// roots that reaches the empty array is DIFFERENT IN ALL FOUR MODULES -
/// `{constNames, constants, extraConstNames}`, `{entries}`,
/// `{extraConstNames, entries}`, `{imports, entries}`. Every blanket sentence I
/// could write about where it lives is false in at least one module. The number
/// of distinct holder SHAPES varies too: 1, 2, 2 and 8.
///
/// POPULATION SCOPE: all four modules, fixtures participating, each pinned by
/// name rather than pooled into a total that could hide a zero.
#[test]
fn the_interned_empty_array() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut counts: Vec<(String, usize, usize)> = Vec::new();
    let mut references: Vec<(String, usize, usize)> = Vec::new();
    let mut histograms: Vec<(String, Vec<(usize, usize)>)> = Vec::new();
    let mut shapes_seen: Vec<(String, usize)> = Vec::new();
    let mut root_sets: Vec<(String, Vec<&'static str>)> = Vec::new();
    let mut dimensions: BTreeSet<(u64, u64)> = BTreeSet::new();
    let mut empty_root_slots: Vec<u64> = Vec::new();

    for (module, bytes) in &modules {
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };

        // Every array object, and the zero-length ones among them.
        let arrays: Vec<usize> = objects
            .iter()
            .filter(|o| o.tag == abi::TAG_ARRAY)
            .map(|o| o.off)
            .collect();
        let empties: Vec<usize> = arrays
            .iter()
            .copied()
            .filter(|&off| word_at(bytes, off + 8) == 0)
            .collect();
        counts.push((module.clone(), arrays.len(), empties.len()));
        if empties.len() != 1 {
            references.push((module.clone(), 0, 0));
            histograms.push((module.clone(), Vec::new()));
            shapes_seen.push((module.clone(), 0));
            root_sets.push((module.clone(), Vec::new()));
            continue;
        }
        let empty = empties[0];
        dimensions.insert((word_at(bytes, empty + 8), word_at(bytes, empty + 16)));

        // Slots against holders, per OBJECT.
        let mut histogram: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        let mut shapes: BTreeSet<(u8, u8)> = BTreeSet::new();
        let mut slots = 0usize;
        let mut holders = 0usize;
        for object in &objects {
            let mut names_it = 0usize;
            if object.tag <= abi::TAG_MAX_CTOR_TAG {
                for slot in 0..usize::from(object.other) {
                    if resolve(word_at(bytes, object.off + 8 + 8 * slot)) == Some(empty) {
                        names_it += 1;
                    }
                }
            } else if object.tag == abi::TAG_ARRAY {
                for i in 0..word_at(bytes, object.off + 8) {
                    if resolve(word_at(bytes, object.off + 24 + 8 * i as usize)) == Some(empty) {
                        names_it += 1;
                    }
                }
            }
            if names_it == 0 {
                continue;
            }
            slots += names_it;
            holders += 1;
            *histogram.entry(names_it).or_default() += 1;
            shapes.insert((object.tag, object.other));
        }
        references.push((module.clone(), slots, holders));
        shapes_seen.push((module.clone(), shapes.len()));

        // The histogram must reconcile with BOTH totals, or it has drifted.
        assert_eq!(
            histogram.values().sum::<usize>(),
            holders,
            "{module}: the multiplicity histogram must account for every holder"
        );
        assert_eq!(
            histogram.iter().map(|(k, v)| k * v).sum::<usize>(),
            slots,
            "{module}: and for every slot"
        );
        histograms.push((module.clone(), histogram.into_iter().collect()));

        // Which roots reach it.
        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root");
        let mut reached = Vec::new();
        for (index, name) in [
            "imports",
            "constNames",
            "constants",
            "extraConstNames",
            "entries",
        ]
        .into_iter()
        .enumerate()
        {
            if reachable_from(bytes, base, word_at(bytes, root + 8 + 8 * index)).contains(&empty) {
                reached.push(name);
            }
        }
        root_sets.push((module.clone(), reached));

        // The declaration-free module spends three root slots on it.
        if module == "Init.olean" {
            for index in 0..5u64 {
                if resolve(word_at(bytes, root + 8 + 8 * index as usize)) == Some(empty) {
                    empty_root_slots.push(index);
                }
            }
        }
    }

    let expect = |all: Vec<(&str, usize, usize)>| -> Vec<(String, usize, usize)> {
        all.into_iter()
            .filter(|(m, _, _)| prelude_loaded || *m != "Init/Prelude.olean")
            .map(|(m, a, b)| (m.to_owned(), a, b))
            .collect()
    };

    // Exactly one, in every module.
    assert_eq!(
        counts,
        expect(vec![
            ("Init.olean", 5, 1),
            ("Init.BinderNameHint.olean", 24, 1),
            ("Init.SizeOfLemmas.olean", 26, 1),
            ("Init/Prelude.olean", 2434, 1),
        ]),
        "array objects, and zero-length array objects among them: EXACTLY ONE \
         per module. Prelude holds 2,434 arrays and 2,999 references to an \
         empty one, so a single zero-length object is not a consequence of \
         arrays being scarce"
    );

    // Slots against holders.
    assert_eq!(
        references,
        expect(vec![
            ("Init.olean", 3, 1),
            ("Init.BinderNameHint.olean", 3, 3),
            ("Init.SizeOfLemmas.olean", 17, 17),
            ("Init/Prelude.olean", 2999, 2932),
        ]),
        "slots naming it, against DISTINCT holder objects. `Init.olean` is the \
         counterexample that makes the distinction real: three slots, ONE \
         holder. Counting occurrences there would be wrong by a factor of three"
    );

    // The decomposition, per module.
    assert_eq!(
        histograms
            .iter()
            .map(|(m, h)| (m.as_str(), h.clone()))
            .collect::<Vec<_>>(),
        [
            ("Init.olean", vec![(3, 1)]),
            ("Init.BinderNameHint.olean", vec![(1, 3)]),
            ("Init.SizeOfLemmas.olean", vec![(1, 17)]),
            (
                "Init/Prelude.olean",
                vec![(1, 2870), (2, 58), (3, 3), (4, 1)]
            ),
        ]
        .into_iter()
        .filter(|(m, _)| prelude_loaded || *m != "Init/Prelude.olean")
        .collect::<Vec<_>>(),
        "how many slots each holder spends on it. Reconciled against both \
         totals above inside the loop, so it cannot drift from either"
    );

    // A module that declares nothing spends three roots on one object.
    assert_eq!(
        empty_root_slots,
        vec![1, 2, 3],
        "`Init.olean` declares nothing, and its `constNames`, `constants` and \
         `extraConstNames` are all the SAME empty array - which is why its one \
         holder is the `ModuleData` root and why its slot count is three"
    );

    // Nothing uniform to say about where it lives.
    assert_eq!(
        root_sets
            .iter()
            .map(|(m, r)| (m.as_str(), r.clone()))
            .collect::<Vec<_>>(),
        [
            (
                "Init.olean",
                vec!["constNames", "constants", "extraConstNames"]
            ),
            ("Init.BinderNameHint.olean", vec!["entries"]),
            (
                "Init.SizeOfLemmas.olean",
                vec!["extraConstNames", "entries"]
            ),
            ("Init/Prelude.olean", vec!["imports", "entries"]),
        ]
        .into_iter()
        .filter(|(m, _)| prelude_loaded || *m != "Init/Prelude.olean")
        .collect::<Vec<_>>(),
        "the roots that reach it are DIFFERENT IN ALL FOUR MODULES, so every \
         blanket sentence about where the empty array lives is false in at \
         least one of them"
    );
    assert_eq!(
        shapes_seen
            .iter()
            .map(|(m, n)| (m.as_str(), *n))
            .collect::<Vec<_>>(),
        [
            ("Init.olean", 1),
            ("Init.BinderNameHint.olean", 2),
            ("Init.SizeOfLemmas.olean", 2),
            ("Init/Prelude.olean", 8),
        ]
        .into_iter()
        .filter(|(m, _)| prelude_loaded || *m != "Init/Prelude.olean")
        .collect::<Vec<_>>(),
        "and the distinct holder SHAPES vary as well - eight in Prelude, so the \
         sharing spans many different structures rather than one extension"
    );

    // Length and capacity, the two fields that carry meaning here.
    assert_eq!(
        dimensions.into_iter().collect::<Vec<_>>(),
        vec![(0, 0)],
        "every module's empty array has length 0 AND capacity 0 - one shape, \
         not four coincidences"
    );
}

/// Where the sixteen dependents point - and the arrays they do NOT own.
///
/// `bed63990` split the 26 singleton slots into ten whose element is the
/// entry's own name and sixteen whose is not, and left the sixteen unread.
/// This reads them, and doing so exposes a defect in that cell's own prose.
///
/// THE ARRAYS ARE SHARED, so slots and objects are different populations.
/// `bed63990` pins the histogram `{0: 2178, 1: 26}` and its comment called that
/// a count "over array objects". It is a count over SLOTS. Per distinct object
/// the same walk gives ONE empty array, referenced from 2,178 slots, and TEN
/// singletons across 26. The assertion was correct and its description was not;
/// w198 passed it because the number matches the code. The comment is corrected
/// in this commit.
///
/// THE TEN SINGLETONS ARE ONE PER AXIOM: the set of names they contain is
/// exactly the ten self-referential names, by object identity. Their slot
/// multiplicities are `[1, 1, 1, 1, 1, 1, 1, 1, 6, 12]`, summing to the 26.
///
/// AND THAT IS THE MECHANISM BEHIND THE SIXTEEN. A dependent entry does not get
/// an array of its own - it points at the SAME array object the axiom's own
/// entry points at. So each multiplicity is one own-slot plus its dependents,
/// 10 own + 16 dependents = 26, and the two shared arrays carry 11 and 5. The
/// sixteen of `bed63990` are precisely the surplus slots on those two.
///
/// WHERE THEY POINT: all sixteen name a member of the ten, by pointer identity
/// - but only TWO DISTINCT OBJECTS between them, `lcProof` eleven times and
/// `Classical.choice` five. Sixteen occurrences, two objects. Counting
/// occurrences would report sixteen targets and miss that eight of the ten are
/// never named by anything but themselves.
///
/// So the ten split two targeted and eight untargeted, pinned as indices.
///
/// DISCRIMINATING POWER: the ten are 10 of 2,204 declarations, so sixteen
/// arbitrary names landing inside them is not something an indifferent
/// structure produces. And no dependent names ITSELF, which is what makes
/// `bed63990`'s classification a real split rather than a restatement.
///
/// THE TWO TARGETS, structurally rather than by rendering: prefix-first, one is
/// a single component of 8 stored bytes and the other is two components of 10
/// and 7. Read off the wire, so nothing here depends on the decoder's
/// rendering.
///
/// POPULATION SCOPE: `Init/Prelude.olean`, asserted rather than left implicit.
#[test]
fn where_the_sixteen_dependents_point() {
    let Some(lib) = reference_lib() else {
        return;
    };
    let Ok(bytes) = std::fs::read(lib.join("Init/Prelude.olean")) else {
        return;
    };
    let bytes = bytes.as_slice();

    let (objects, base) = objects_of(bytes);
    let at: std::collections::BTreeMap<usize, Obj> = objects.iter().map(|o| (o.off, *o)).collect();
    let resolve = |word: u64| -> Option<usize> {
        (word & 1 == 0)
            .then(|| usize::try_from(word.wrapping_sub(base)).ok())
            .flatten()
            .filter(|off| at.contains_key(off))
    };
    let tag = |off: usize| at.get(&off).map(|o| o.tag);

    let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root");
    let names_array = resolve(word_at(bytes, root + 16)).expect("constNames array");
    let entries_array = resolve(word_at(bytes, root + 40)).expect("entries array");
    let names_len = word_at(bytes, names_array + 8);

    // The one payload aligned with `constNames`, found rather than assumed.
    let mut payload = None;
    for e in 0..word_at(bytes, entries_array + 8) {
        let Some(entry) = resolve(word_at(bytes, entries_array + 24 + 8 * e as usize)) else {
            continue;
        };
        let Some(candidate) = resolve(word_at(bytes, entry + 16)) else {
            continue;
        };
        if tag(candidate) != Some(abi::TAG_ARRAY) || word_at(bytes, candidate + 8) != names_len {
            continue;
        }
        let aligned = (0..names_len).all(|i| {
            let slot = 24 + 8 * i as usize;
            resolve(word_at(bytes, candidate + slot))
                .and_then(|element| resolve(word_at(bytes, element + 8)))
                == resolve(word_at(bytes, names_array + slot))
        });
        if aligned && names_len > 0 {
            payload = Some(candidate);
        }
    }
    let payload = payload.expect("the aligned payload");

    // Slots grouped by the array OBJECT they hold.
    let mut by_object: std::collections::BTreeMap<usize, Vec<u64>> =
        std::collections::BTreeMap::new();
    for i in 0..names_len {
        let Some(element) = resolve(word_at(bytes, payload + 24 + 8 * i as usize)) else {
            continue;
        };
        let Some(list) = resolve(word_at(bytes, element + 16)) else {
            continue;
        };
        if tag(list) == Some(abi::TAG_ARRAY) {
            by_object.entry(list).or_default().push(i);
        }
    }

    let mut empty_objects = 0usize;
    let mut empty_slots = 0usize;
    let mut singleton_objects = 0usize;
    let mut singleton_slots = 0usize;
    let mut multiplicities: Vec<usize> = Vec::new();
    let mut own = 0usize;
    let mut dependents = 0usize;
    let mut contents: BTreeSet<usize> = BTreeSet::new();
    let mut targets: Vec<usize> = Vec::new();
    let mut self_named: BTreeSet<usize> = BTreeSet::new();

    for (&list, slots) in &by_object {
        if word_at(bytes, list + 8) == 0 {
            empty_objects += 1;
            empty_slots += slots.len();
            continue;
        }
        singleton_objects += 1;
        singleton_slots += slots.len();
        multiplicities.push(slots.len());
        let held = resolve(word_at(bytes, list + 24)).expect("the singleton's element");
        contents.insert(held);
        for &i in slots {
            let named = resolve(word_at(bytes, names_array + 24 + 8 * i as usize));
            if named == Some(held) {
                own += 1;
                self_named.insert(i as usize);
            } else {
                dependents += 1;
                targets.push(held);
            }
        }
    }
    multiplicities.sort_unstable();

    // Objects against slots - the correction this cell exists to make.
    assert_eq!(
        (
            empty_objects,
            empty_slots,
            singleton_objects,
            singleton_slots
        ),
        (1, 2178, 10, 26),
        "ONE empty array object is referenced from 2,178 slots and TEN singleton \
         objects from 26. `bed63990` pins the per-slot pair and its comment \
         called it a count over objects; the objects are 1 and 10, and that \
         comment is corrected in this commit"
    );

    // One singleton per axiom, by object identity.
    assert_eq!(
        (contents.len(), singleton_objects),
        (10, 10),
        "the singletons hold ten DISTINCT names between them - one array per \
         axiom, no two axioms sharing an array"
    );

    // The mechanism, as an arithmetic identity rather than a description.
    assert_eq!(
        multiplicities,
        vec![1, 1, 1, 1, 1, 1, 1, 1, 6, 12],
        "slot multiplicity per array OBJECT: eight arrays used once, one used \
         six times, one twelve"
    );
    assert_eq!(
        (own, dependents, own + dependents),
        (10, 16, 26),
        "and each multiplicity is one OWN slot plus its dependents, so 10 + 16 \
         is the 26. The sixteen of `bed63990` are exactly the surplus slots on \
         the two shared arrays - a dependent never gets an array of its own, it \
         points at the one the axiom's own entry points at"
    );

    // Where the sixteen point: occurrences against objects.
    let distinct: BTreeSet<usize> = targets.iter().copied().collect();
    assert_eq!(
        (targets.len(), distinct.len()),
        (16, 2),
        "SIXTEEN OCCURRENCES, TWO OBJECTS. Counting occurrences would report \
         sixteen targets and hide that the sixteen name only two things"
    );
    let mut multiplicity: Vec<usize> = distinct
        .iter()
        .map(|t| targets.iter().filter(|&&x| x == *t).count())
        .collect();
    multiplicity.sort_unstable();
    assert_eq!(
        multiplicity,
        vec![5, 11],
        "eleven of the sixteen name one of them and five the other"
    );
    assert!(
        distinct.iter().all(|t| contents.contains(t)),
        "every target is one of the ten, by pointer identity - and the ten are \
         10 of {names_len} declarations, so sixteen names landing inside them \
         is not what an indifferent structure gives"
    );
    assert_eq!(
        self_named.len(),
        10,
        "the own-slots are ten distinct indices, so no entry is counted twice"
    );

    // Two targeted, eight not - as indices, not as a count.
    let targeted: Vec<u64> = (0..names_len)
        .filter(|&i| {
            resolve(word_at(bytes, names_array + 24 + 8 * i as usize))
                .is_some_and(|named| distinct.contains(&named))
        })
        .collect();
    assert_eq!(
        targeted,
        vec![504, 885],
        "the ten split TWO targeted and eight named by nothing but themselves, \
         pinned as indices so that a member moving across the split cannot \
         leave a total looking right"
    );

    // Which two, structurally rather than by rendering.
    let mut shapes: Vec<Vec<u64>> = distinct
        .iter()
        .map(|&target| {
            let mut component = Some(target);
            let mut stored = Vec::new();
            while let Some(off) = component {
                stored.push(
                    resolve(word_at(bytes, off + 16))
                        .map(|string| word_at(bytes, string + 8))
                        .unwrap_or(0),
                );
                component = resolve(word_at(bytes, off + 8));
            }
            stored.reverse();
            stored
        })
        .collect();
    shapes.sort();
    assert_eq!(
        shapes,
        vec![vec![8_u64], vec![10_u64, 7]],
        "prefix-first stored byte counts: one target is a single component of 8 \
         bytes, the other two components of 10 and 7. Read off the wire, so \
         this does not depend on how the decoder renders a name"
    );
}

/// The compiler structure inside `entries` that shares the declaration names.
///
/// `c384f87e` showed `constNames[i]` and the `ConstantVal` under `constants[i]`
/// are the same name object. The two remaining unread holders are the
/// `entries`-rooted ones that are not the node: a two-field pair and a
/// one-element array. This walks them.
///
/// THE PAIR IS ELEMENT 43 OF AN EXTENSION PAYLOAD, and 43 is the same index
/// again. The path is `entries[19]`, whose payload array is element-for-element
/// aligned with `constNames` - 2,204 of 2,204, pointer identity, none
/// unresolved. So THREE roots share one name object at that index: the name
/// array, the declaration record, and this extension's entry. The pair's second
/// field is the one-element array, and its single element is that object again.
///
/// LENGTH DOES NOT IMPLY ALIGNMENT, and that is what keeps this honest.
/// Selecting extension payloads by "as many elements as `constNames`" finds six
/// across these modules and only four are aligned:
/// `Init.BinderNameHint.olean` has THREE length-matches and ONE aligned. The
/// tidy version of this finding - an extension sized like the module is indexed
/// like the module - is false, and the two counterexamples are pinned rather
/// than filtered out. The count varies too, two in `Init.SizeOfLemmas.olean`
/// against one in Prelude, so there is no such thing as `the` aligned
/// extension.
///
/// WHICH EXTENSION, pinned structurally rather than by rendering. Its name is
/// SEVEN components, one NUMERIC - the `_private` mangling shape - ending in an
/// 18-byte string, `exportedAxiomsExt` and its terminator. All read off the
/// wire, so none of it depends on how the production decoder renders a numeric
/// component. `c2f98113` put its one rendering-dependent assertion last and
/// flagged it; this cell needs none.
///
/// PER-NODE, NOT PER-RECORD: the payload's second fields are 2,178 EMPTY arrays
/// and 26 singletons, counted over array objects. The 26 split ten whose single
/// element is the entry's own name and sixteen whose is not, and the ten are
/// pinned AS INDICES rather than as a count, because
/// `a-count-grep-cannot-find-a-decomposition`.
///
/// A ONE-WAY IMPLICATION ACROSS TWO ROOTS, WITH THE CONVERSE MEASURED FALSE.
/// All ten self-referential entries are declarations whose `ConstantInfo`
/// carries constructor tag 0, against a base rate of 256 in 2,204 - so the
/// agreement is not what an arbitrary ten indices would give. The converse does
/// NOT hold: 239 of those 256 have an EMPTY array here, and seven of the
/// sixteen non-self-referential entries are tag 0 as well. Pinned in one
/// direction with a floor, per `fln-shrinking-allowance-guard-direction`;
/// equality would be a wall that a correct decoder fails against.
///
/// ANTI-VACUITY: an empty payload satisfies "every index agrees" while checking
/// nothing, so alignment requires a non-empty array, and the pooled aligned
/// population is asserted above 100.
///
/// POPULATION SCOPE: the per-module counts cover all four modules with the
/// fixtures participating; the index-43, histogram and tag facts are
/// `Init/Prelude.olean` alone, asserted rather than left implicit.
#[test]
fn the_extension_that_shares_the_declaration_names() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut length_matches: Vec<(String, usize)> = Vec::new();
    let mut aligned_at: Vec<(String, Vec<u64>)> = Vec::new();
    let mut pooled_aligned = 0usize;
    let mut lengths_histogram: std::collections::BTreeMap<u64, usize> =
        std::collections::BTreeMap::new();
    let mut self_indices: Vec<u64> = Vec::new();
    let mut other_indices: Vec<u64> = Vec::new();
    let mut self_tags: std::collections::BTreeMap<u8, usize> = std::collections::BTreeMap::new();
    let mut other_tag_zero = 0usize;
    let mut tag_zero_total = 0usize;
    let mut tag_zero_empty = 0usize;
    let mut name_components = 0usize;
    let mut numeric_components = 0usize;
    let mut last_component_bytes = 0u64;

    for (module, bytes) in &modules {
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let arity = |off: usize| at.get(&off).map(|o| o.other).unwrap_or(0);
        let tag = |off: usize| at.get(&off).map(|o| o.tag);

        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root");
        let names_array = resolve(word_at(bytes, root + 16)).expect("constNames array");
        let consts_array = resolve(word_at(bytes, root + 24)).expect("constants array");
        let entries_array = resolve(word_at(bytes, root + 40)).expect("entries array");
        let names_len = word_at(bytes, names_array + 8);

        let mut matches = 0usize;
        let mut aligned: Vec<u64> = Vec::new();
        for e in 0..word_at(bytes, entries_array + 8) {
            let Some(entry) = resolve(word_at(bytes, entries_array + 24 + 8 * e as usize)) else {
                continue;
            };
            if arity(entry) < 2 {
                continue;
            }
            let Some(payload) = resolve(word_at(bytes, entry + 16)) else {
                continue;
            };
            if tag(payload) != Some(abi::TAG_ARRAY) || word_at(bytes, payload + 8) != names_len {
                continue;
            }
            matches += 1;

            let mut agree = 0u64;
            let mut counted = 0u64;
            for i in 0..names_len {
                let slot = 24 + 8 * i as usize;
                // Counted, never skipped - a skipped index would shrink the
                // denominator and make this walk a sampler.
                counted += 1;
                let named = resolve(word_at(bytes, names_array + slot));
                let Some(element) =
                    resolve(word_at(bytes, payload + slot)).filter(|&o| arity(o) >= 1)
                else {
                    continue;
                };
                if named.is_some() && resolve(word_at(bytes, element + 8)) == named {
                    agree += 1;
                }
            }
            // A zero-length payload would satisfy `agree == counted` while
            // checking nothing at all.
            if counted == 0 || agree != counted {
                continue;
            }
            aligned.push(e);
            pooled_aligned += usize::try_from(counted).expect("in range");

            if module != "Init/Prelude.olean" {
                continue;
            }

            // The extension's own name, read off the wire.
            let mut component = resolve(word_at(bytes, entry + 8)).expect("extension name");
            last_component_bytes = resolve(word_at(bytes, component + 16))
                .map(|string| word_at(bytes, string + 8))
                .expect("its last component is a string");
            loop {
                name_components += 1;
                if tag(component) == Some(2) {
                    numeric_components += 1;
                }
                match resolve(word_at(bytes, component + 8)) {
                    Some(next) => component = next,
                    None => break,
                }
            }

            // The second fields, per array OBJECT, and who they name.
            for i in 0..names_len {
                let slot = 24 + 8 * i as usize;
                let Some(element) = resolve(word_at(bytes, payload + slot)) else {
                    continue;
                };
                let Some(list) = resolve(word_at(bytes, element + 16)) else {
                    continue;
                };
                if tag(list) != Some(abi::TAG_ARRAY) {
                    continue;
                }
                let len = word_at(bytes, list + 8);
                *lengths_histogram.entry(len).or_default() += 1;

                // The declaration record's variant at the same index.
                let variant = resolve(word_at(bytes, consts_array + slot)).and_then(tag);
                if variant == Some(0) {
                    tag_zero_total += 1;
                    if len == 0 {
                        tag_zero_empty += 1;
                    }
                }
                if len == 0 {
                    continue;
                }
                let named = resolve(word_at(bytes, element + 8));
                if named.is_some() && resolve(word_at(bytes, list + 24)) == named {
                    self_indices.push(i);
                    *self_tags.entry(variant.unwrap_or(u8::MAX)).or_default() += 1;
                } else {
                    other_indices.push(i);
                    if variant == Some(0) {
                        other_tag_zero += 1;
                    }
                }
            }
        }
        length_matches.push((module.clone(), matches));
        aligned_at.push((module.clone(), aligned));
    }

    // Selected by length.
    assert_eq!(
        length_matches
            .iter()
            .map(|(m, n)| (m.as_str(), *n))
            .collect::<Vec<_>>(),
        if prelude_loaded {
            vec![
                ("Init.olean", 0),
                ("Init.BinderNameHint.olean", 3),
                ("Init.SizeOfLemmas.olean", 2),
                ("Init/Prelude.olean", 1),
            ]
        } else {
            vec![
                ("Init.olean", 0),
                ("Init.BinderNameHint.olean", 3),
                ("Init.SizeOfLemmas.olean", 2),
            ]
        },
        "extension payloads with exactly as many elements as `constNames`"
    );

    // And how many of those are actually aligned. THIS IS THE POINT.
    assert_eq!(
        aligned_at
            .iter()
            .map(|(m, a)| (m.as_str(), a.clone()))
            .collect::<Vec<_>>(),
        if prelude_loaded {
            vec![
                ("Init.olean", vec![]),
                ("Init.BinderNameHint.olean", vec![1_u64]),
                ("Init.SizeOfLemmas.olean", vec![1_u64, 2]),
                ("Init/Prelude.olean", vec![19_u64]),
            ]
        } else {
            vec![
                ("Init.olean", vec![]),
                ("Init.BinderNameHint.olean", vec![1_u64]),
                ("Init.SizeOfLemmas.olean", vec![1_u64, 2]),
            ]
        },
        "LENGTH DOES NOT IMPLY ALIGNMENT: six payloads are sized like their \
         module and only four are indexed like it. `Init.BinderNameHint.olean` \
         has three length-matches and one aligned, so the two misses stay in \
         the pin rather than being filtered out of it. The count varies as \
         well - two in `Init.SizeOfLemmas.olean`, one in Prelude - so there is \
         no such thing as `the` aligned extension"
    );
    assert!(
        pooled_aligned >= 100,
        "anti-vacuity: the aligned indices must stay a real population, got \
         {pooled_aligned}"
    );

    if !prelude_loaded {
        assert!(
            self_indices.is_empty(),
            "the extension is not in the C3 fixtures"
        );
        return;
    }

    // Which extension, structurally rather than by rendering.
    assert_eq!(
        (name_components, numeric_components, last_component_bytes),
        (7, 1, 18),
        "the extension's name is seven components with one NUMERIC among them - \
         the `_private` mangling shape - ending in an 18-byte string, \
         `exportedAxiomsExt` and its terminator. Read off the wire, so it does \
         not depend on how a numeric component is rendered"
    );

    // Per SLOT. See `where_the_sixteen_dependents_point` for the object count.
    assert_eq!(
        lengths_histogram.into_iter().collect::<Vec<_>>(),
        vec![(0, 2178), (1, 26)],
        "the payload has 2,178 slots holding an empty array and 26 holding a \
         singleton - counted PER SLOT, one tally per index. The first version \
         of this comment said `counted over array objects`, which is false: \
         the arrays are SHARED, and per distinct object the same walk gives 1 \
         empty and 10 singletons. The assertion was right and its description \
         was not, which is why w198 passed it"
    );

    // The decomposition, bound per member and not as a total.
    assert_eq!(
        self_indices,
        vec![43, 504, 633, 885, 969, 1127, 1152, 1359, 1531, 1537],
        "the ten entries whose single element is the entry's own name, pinned \
         as INDICES so that moving one member across the split cannot leave a \
         total looking right. Element 43 is among them - the same 43 at which \
         that name sits in `constNames` and in `constants`, so three roots \
         share one name object and the third holds it twice"
    );
    assert_eq!(
        (self_indices.len(), other_indices.len()),
        (10, 16),
        "ten of the 26 singletons, sixteen not"
    );

    // One direction, with the converse measured false.
    assert_eq!(
        self_tags.into_iter().collect::<Vec<_>>(),
        vec![(0, 10)],
        "every one of the ten is a declaration whose `ConstantInfo` carries \
         constructor tag 0, which is 256 of 2,204 overall - so ten out of ten \
         is not what an arbitrary ten indices would give"
    );
    assert_eq!(
        (tag_zero_total, tag_zero_empty, other_tag_zero),
        (256, 239, 7),
        "and the CONVERSE DOES NOT HOLD: 239 of those 256 have an empty array \
         here, and seven of the sixteen non-self-referential entries are tag 0 \
         too. So this is an implication in one direction only. Pinning it as an \
         equivalence would be a wall a correct decoder fails against, per \
         `fln-shrinking-allowance-guard-direction`"
    );
}

/// What the `constants`-rooted holder IS: this module's declaration 43.
///
/// `83016935` split the link from the node - the link reaches three roots, the
/// node reaches `entries` alone - and left the holders themselves unread. The
/// `constants`-rooted one is the interesting half, because it is the object
/// that carries the name out of `entries`, and its identity was never measured.
///
/// It is a `ConstantVal`, and NOT because of its shape. `c4cbf83c` was reddened
/// for reading `(0, 3, 32)` as identifying `ConstantVal`, and this cell does not
/// repeat that: the object is reached by INDEXING, from `constants[43]` through
/// the `ConstantInfo` wrapper and its payload, and its name field is then the
/// same object as the link.
///
/// THE FACT THAT MAKES IT MORE THAN ONE OBJECT'S BIOGRAPHY. `constNames[i]` and
/// the `ConstantVal` under `constants[i]` are the SAME NAME OBJECT, at every
/// index of every module here - 2,222 of 2,222 pooled, none unresolved. The two
/// arrays do not merely agree on spelling, they share storage. So a decoder that
/// let the two arrays drift apart, or indexed one by the other's position, is
/// producing declarations under the wrong names, and this is the identity that
/// would catch it.
///
/// THAT IS THE RESOLUTION OF `83016935`. The name escapes `entries` because
/// `lcErased` IS A DECLARATION OF THIS MODULE - element 43 of the name array
/// and element 43 of the declaration array - while the compiler structure in
/// `entries` references the very same name object. Nothing crosses the boundary
/// except a shared pointer, which is why `1dd7c288`'s object-level exclusion
/// survives it untouched.
///
/// DISCRIMINATING POWER, because index-wise identity would be worthless if the
/// candidates were few: every module's name objects are pairwise DISTINCT -
/// 2,204 distinct objects across 2,204 indices in Prelude - so there is exactly
/// one right answer per index and 2,203 wrong ones.
///
/// THE DENOMINATOR IS THE WHOLE ARRAY, asserted rather than assumed. The walk
/// counts an unresolved index instead of skipping it, and the unresolved count
/// is pinned at zero, so the 2,222 cannot be a filtered sample of a larger
/// population - the trap `bs5o` fell into.
///
/// ONE THING THAT IS NOT UNIFORM, and it is pinned per module rather than
/// blanket. In the three modules that declare anything the two arrays are
/// DIFFERENT objects, so the shared-name-object finding is not the trivial
/// consequence of one array being the other. In `Init.olean`, which declares
/// nothing, they are THE SAME OBJECT - one empty array, shared. A blanket
/// "the arrays are distinct" would have been false, and this file has now been
/// reddened four times for stating a convenient reading as a measured one.
///
/// POPULATION SCOPE: the invariant is pooled over all four modules and their
/// lengths are pinned individually; the index-43 facts are `Init/Prelude.olean`
/// alone, asserted rather than left implicit.
#[test]
fn the_constants_rooted_holder_is_this_modules_declaration() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut lengths: Vec<(String, u64, u64)> = Vec::new();
    let mut same_object: Vec<(String, bool)> = Vec::new();
    let mut shared = 0usize;
    let mut pooled = 0usize;
    let mut unresolved = 0usize;
    let mut distinct: Vec<(String, usize, usize)> = Vec::new();
    let mut link_indices: Vec<u64> = Vec::new();
    let mut holder_is_declaration = 0usize;

    for (module, bytes) in &modules {
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root");
        let names_array = resolve(word_at(bytes, root + 16)).expect("constNames array");
        let consts_array = resolve(word_at(bytes, root + 24)).expect("constants array");
        let names_len = word_at(bytes, names_array + 8);
        let consts_len = word_at(bytes, consts_array + 8);
        lengths.push((module.clone(), names_len, consts_len));
        same_object.push((module.clone(), names_array == consts_array));

        // The shared-storage invariant, index by index.
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut counted = 0usize;
        for i in 0..names_len {
            let slot = 24 + 8 * i as usize;
            let named = resolve(word_at(bytes, names_array + slot));
            let info = resolve(word_at(bytes, consts_array + slot));
            // A `ConstantInfo` wraps one payload; every payload's slot 0 is its
            // `ConstantVal`, whichever variant it is.
            let value = info
                .filter(|&off| at.get(&off).is_some_and(|o| o.other >= 1))
                .and_then(|off| resolve(word_at(bytes, off + 8)))
                .and_then(|payload| resolve(word_at(bytes, payload + 8)));
            let Some((named, value)) = named.zip(value) else {
                // Counted, never skipped: a skipped index would shrink the
                // denominator and turn this walk into a sampler.
                unresolved += 1;
                continue;
            };
            counted += 1;
            seen.insert(named);
            if resolve(word_at(bytes, value + 8)) == Some(named) {
                shared += 1;
            }
        }
        pooled += counted;
        distinct.push((module.clone(), seen.len(), counted));

        if module != "Init/Prelude.olean" {
            continue;
        }

        // Prelude only: rebuild the closure, take its one `tag 4` node, and
        // follow that node's name link back into the two arrays.
        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            if resolve(word_at(bytes, object.off + 16)).and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        let mut eight: BTreeSet<usize> = BTreeSet::new();
        for &record in &records {
            let Some(seed) = resolve(word_at(bytes, record + 8 + 8 * 4)) else {
                continue;
            };
            if shape(seed) != Some((0, 2)) {
                continue;
            }
            let Some(tail) = resolve(word_at(bytes, seed + 16)) else {
                continue;
            };
            if shape(tail) != Some((4, 1)) {
                continue;
            }
            let Some(inner) = resolve(word_at(bytes, tail + 8)) else {
                continue;
            };
            let Some(array) = resolve(word_at(bytes, inner + 8 + 8 * 3)) else {
                continue;
            };
            for i in 0..word_at(bytes, array + 8) {
                let Some(ten) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) else {
                    continue;
                };
                let Some(below) = resolve(word_at(bytes, ten + 8 + 8)) else {
                    continue;
                };
                for k in 0..word_at(bytes, below + 8) {
                    if let Some(element) = resolve(word_at(bytes, below + 24 + 8 * k as usize))
                        && shape(element) == Some((0, 3))
                    {
                        eight.insert(element);
                    }
                }
            }
        }
        let mut closure: BTreeSet<usize> = BTreeSet::new();
        for &element in &eight {
            closure.extend(reachable_from(bytes, base, base + element as u64));
        }
        let node = closure
            .iter()
            .copied()
            .find(|&off| shape(off) == Some((4, 2)))
            .expect("the one `tag 4` node");
        let link = resolve(word_at(bytes, node + 8)).expect("its name link");

        for i in 0..names_len {
            if resolve(word_at(bytes, names_array + 24 + 8 * i as usize)) == Some(link) {
                link_indices.push(i);
            }
        }
        for &i in &link_indices {
            let slot = 24 + 8 * i as usize;
            let value = resolve(word_at(bytes, consts_array + slot))
                .and_then(|off| resolve(word_at(bytes, off + 8)))
                .and_then(|payload| resolve(word_at(bytes, payload + 8)))
                .expect("the declaration record at that index");
            // The holder `83016935` found under `constants` is exactly this.
            if resolve(word_at(bytes, value + 8)) == Some(link) {
                holder_is_declaration += 1;
            }
        }
    }

    // The arrays are the same length in every module, empty one included.
    assert_eq!(
        lengths
            .iter()
            .map(|(m, n, c)| (m.as_str(), *n, *c))
            .collect::<Vec<_>>(),
        if prelude_loaded {
            vec![
                ("Init.olean", 0, 0),
                ("Init.BinderNameHint.olean", 2, 2),
                ("Init.SizeOfLemmas.olean", 16, 16),
                ("Init/Prelude.olean", 2204, 2204),
            ]
        } else {
            vec![
                ("Init.olean", 0, 0),
                ("Init.BinderNameHint.olean", 2, 2),
                ("Init.SizeOfLemmas.olean", 16, 16),
            ]
        },
        "`constNames` and `constants` have equal length in each module"
    );

    // Not blanket: distinct arrays wherever anything is declared, one shared
    // empty array where nothing is.
    assert_eq!(
        same_object
            .iter()
            .map(|(m, same)| (m.as_str(), *same))
            .collect::<Vec<_>>(),
        if prelude_loaded {
            vec![
                ("Init.olean", true),
                ("Init.BinderNameHint.olean", false),
                ("Init.SizeOfLemmas.olean", false),
                ("Init/Prelude.olean", false),
            ]
        } else {
            vec![
                ("Init.olean", true),
                ("Init.BinderNameHint.olean", false),
                ("Init.SizeOfLemmas.olean", false),
            ]
        },
        "the two roots are DIFFERENT array objects wherever the module declares \
         anything, so the shared-name-object finding below is not the trivial \
         consequence of one array being the other. `Init.olean` declares \
         nothing and its two roots are the SAME empty array - pinned per module \
         because a blanket claim either way is false"
    );

    // The denominator is the whole array.
    assert_eq!(
        unresolved, 0,
        "every index resolved to a name and a declaration record, so the pooled \
         count below is the whole population and not a filtered sample of it"
    );

    // The invariant: same index, same NAME OBJECT.
    let expected = if prelude_loaded { 2222 } else { 18 };
    assert_eq!(
        (shared, pooled),
        (expected, expected),
        "`constNames[i]` and the `ConstantVal` under `constants[i]` are the SAME \
         OBJECT at every index of every module - the arrays share storage rather \
         than merely agreeing on spelling. A decoder that let them drift, or \
         indexed one by the other's position, would produce declarations under \
         the wrong names and would fail here"
    );

    // Discriminating power: one right answer per index, and many wrong ones.
    assert_eq!(
        distinct
            .iter()
            .map(|(m, d, c)| (m.as_str(), *d, *c))
            .collect::<Vec<_>>(),
        if prelude_loaded {
            vec![
                ("Init.olean", 0, 0),
                ("Init.BinderNameHint.olean", 2, 2),
                ("Init.SizeOfLemmas.olean", 16, 16),
                ("Init/Prelude.olean", 2204, 2204),
            ]
        } else {
            vec![
                ("Init.olean", 0, 0),
                ("Init.BinderNameHint.olean", 2, 2),
                ("Init.SizeOfLemmas.olean", 16, 16),
            ]
        },
        "the name objects are pairwise DISTINCT in every module - as many \
         distinct objects as indices - so index-wise identity has exactly one \
         right answer out of 2,204 in Prelude and is not something a wrong \
         decoder could hit by accident"
    );
    assert!(
        pooled >= 100,
        "anti-vacuity: the pooled population must stay large enough for the \
         base rate above to mean anything, got {pooled}"
    );

    if !prelude_loaded {
        assert!(
            link_indices.is_empty(),
            "the closure is not in the C3 fixtures"
        );
        return;
    }

    // The link is a declaration of this module, at one index.
    assert_eq!(
        link_indices,
        vec![43],
        "the node's name link is element 43 of `constNames`, and at exactly one \
         index - counted as OBJECT positions, not as occurrences of a spelling"
    );
    assert_eq!(
        holder_is_declaration, 1,
        "and the `ConstantVal` reached by INDEXING `constants` at that same 43 \
         is the very object `83016935` found under the `constants` root: its \
         name field is the link itself. Reached by index rather than by shape, \
         because `c4cbf83c` was reddened for reading `(0, 3, 32)` as \
         identifying `ConstantVal` and this cell must not repeat it"
    );
}

/// What the four outside holders belong to - and a name that crosses the root
/// boundary.
///
/// `653365bd` found holders of that name link outside every population this
/// bead has characterised and named their identity as unmeasured. It said four;
/// w189 showed it is all five, since the fifth is in the closure and not in any
/// of the four populations. The
/// instrument for "what does an object belong to" in this file is the one
/// `1dd7c288` used: which of `ModuleData`'s roots reaches it.
///
/// The five holders sit under THREE DIFFERENT ROOTS:
///
///   constNames   one - an array
///   constants    one - a three-field record at 32 bytes
///   entries      three - an array, a two-field object, and the node itself
///
/// AND THE LINK ITSELF IS REACHABLE FROM ALL THREE, while the NODE that holds
/// it is reachable from `entries` ALONE. That pair is the whole finding: the
/// name crosses the root boundary, the object carrying it does not.
///
/// The first version of this cell pinned the link at two roots, `constants` and
/// `entries`. w190 caught it. The walk is right and the pin was wrong, and it
/// was wrong in a way that needed no measurement to expose: a holder sits under
/// `constNames` twenty lines above, and being a holder MEANS naming the link,
/// so `constNames` reaches the link in one more hop. The two assertions
/// contradicted each other in the same cell. What I wrote down was the two
/// roots `1dd7c288`'s argument is ABOUT, not the set the walk computes - and
/// the word `BOTH` sealed it, since a two-element word reads as complete no
/// matter what the code found.
///
/// So the `node_roots` pin below is not decoration. The conflation that
/// produced the bad number was between the LINK and the NODE, and those two now
/// have separate, differing assertions instead of one sentence covering both.
///
/// THAT IS A DEPARTURE FROM `1dd7c288`, AND THE SCOPE OF ITS FINDING IS WHAT
/// MOVES. That cell pinned the third shape as reachable from `entries` and
/// NEVER from `constants` - zero of 99, against 2,259 of 2,465 for ordinary
/// cons cells, which is as strong as a zero gets. Nothing about that changes.
/// What this shows is that the exclusion is a fact about those OBJECTS and not
/// about the NAMES they reference: the structure stays inside `entries` while
/// one of its names is also in the declaration graph and in the module's
/// constant-name array.
///
/// So `1dd7c288`'s boundary is a boundary on reachability of objects, not a
/// partition of the module. I read it as the latter for twenty waves without
/// ever testing the difference, and nothing in the file distinguished them
/// until a name was followed outward.
///
/// The check could have come out otherwise, which is what makes it evidence:
/// entries-only was the observed pattern for every object in this descent, so
/// finding a holder under `constants` is a measured departure and not a
/// consequence of how holders were selected.
///
/// POPULATION SCOPE: the link and all five holders are in `Init/Prelude.olean`,
/// asserted rather than left implicit, per `b28cb524`.
#[test]
fn the_four_outside_holders() {
    let mut modules: Vec<(String, Vec<u8>)> = [
        "Init.olean",
        "Init.BinderNameHint.olean",
        "Init.SizeOfLemmas.olean",
    ]
    .into_iter()
    .map(|module| (module.to_owned(), fixture(module)))
    .collect();
    let mut prelude_loaded = false;
    if let Some(lib) = reference_lib() {
        let prelude = lib.join("Init/Prelude.olean");
        if let Ok(bytes) = std::fs::read(&prelude) {
            modules.push(("Init/Prelude.olean".to_owned(), bytes));
            prelude_loaded = true;
        }
    }

    let mut holders: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut by_root: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut link_roots: BTreeSet<&'static str> = BTreeSet::new();
    let mut node_roots: BTreeSet<&'static str> = BTreeSet::new();
    let mut third_shape_in_constants = 0usize;
    let mut third_shape_total = 0usize;
    let mut modules_seen: BTreeSet<String> = BTreeSet::new();

    for (index, (module, bytes)) in modules.iter().enumerate() {
        let (objects, base) = objects_of(bytes);
        let at: std::collections::BTreeMap<usize, Obj> =
            objects.iter().map(|o| (o.off, *o)).collect();
        let resolve = |word: u64| -> Option<usize> {
            (word & 1 == 0)
                .then(|| usize::try_from(word.wrapping_sub(base)).ok())
                .flatten()
                .filter(|off| at.contains_key(off))
        };
        let shape = |off: usize| at.get(&off).map(|o| (o.tag, o.other));

        let root = usize::try_from(word_at(bytes, 88).wrapping_sub(base)).expect("root");
        let roots: [(&'static str, BTreeSet<usize>); 5] = [
            (
                "imports",
                reachable_from(bytes, base, word_at(bytes, root + 8)),
            ),
            (
                "constNames",
                reachable_from(bytes, base, word_at(bytes, root + 16)),
            ),
            (
                "constants",
                reachable_from(bytes, base, word_at(bytes, root + 24)),
            ),
            (
                "extraConstNames",
                reachable_from(bytes, base, word_at(bytes, root + 32)),
            ),
            (
                "entries",
                reachable_from(bytes, base, word_at(bytes, root + 40)),
            ),
        ];

        // `1dd7c288`'s population, re-measured here rather than quoted.
        let mut seeds: BTreeSet<usize> = BTreeSet::new();
        let mut records: BTreeSet<usize> = BTreeSet::new();
        for object in &objects {
            if (object.tag, object.other, object.cs_sz) != (1, 2, 24) {
                continue;
            }
            let second = word_at(bytes, object.off + 16);
            let tail = resolve(second);
            let cons_shaped =
                (second & 1 == 1 && second >> 1 == 0) || tail.and_then(shape) == Some((1, 2));
            if !cons_shaped {
                third_shape_total += 1;
                if roots[2].1.contains(&object.off) {
                    third_shape_in_constants += 1;
                }
            }
            if tail.and_then(shape) != Some((0, 2)) {
                continue;
            }
            if let Some(head) = resolve(word_at(bytes, object.off + 8))
                && shape(head) == Some((0, 5))
            {
                records.insert(head);
            }
        }
        for &record in &records {
            if let Some(target) = resolve(word_at(bytes, record + 8 + 8 * 4))
                && shape(target) == Some((0, 2))
            {
                seeds.insert(target);
            }
        }

        // Down to the node, and its name link.
        let mut eight: BTreeSet<usize> = BTreeSet::new();
        for &node in &seeds {
            let Some(tail) = resolve(word_at(bytes, node + 16)) else {
                continue;
            };
            if shape(tail) != Some((4, 1)) {
                continue;
            }
            let Some(inner) = resolve(word_at(bytes, tail + 8)) else {
                continue;
            };
            let Some(array) = resolve(word_at(bytes, inner + 8 + 8 * 3)) else {
                continue;
            };
            for i in 0..word_at(bytes, array + 8) {
                let Some(ten) = resolve(word_at(bytes, array + 24 + 8 * i as usize)) else {
                    continue;
                };
                let Some(below) = resolve(word_at(bytes, ten + 8 + 8)) else {
                    continue;
                };
                for k in 0..word_at(bytes, below + 8) {
                    if let Some(element) = resolve(word_at(bytes, below + 24 + 8 * k as usize))
                        && shape(element) == Some((0, 3))
                    {
                        eight.insert(element);
                    }
                }
            }
        }
        if eight.is_empty() {
            continue;
        }
        modules_seen.insert(module.clone());

        let mut closure: BTreeSet<usize> = BTreeSet::new();
        let mut stack: Vec<usize> = eight.iter().copied().collect();
        while let Some(offset) = stack.pop() {
            if !closure.insert(offset) {
                continue;
            }
            let object = at.get(&offset).expect("a walked object");
            if object.tag <= abi::TAG_MAX_CTOR_TAG {
                for slot in 0..usize::from(object.other) {
                    if let Some(child) = resolve(word_at(bytes, offset + 8 + 8 * slot)) {
                        stack.push(child);
                    }
                }
            } else if object.tag == abi::TAG_ARRAY {
                for i in 0..word_at(bytes, offset + 8) {
                    if let Some(child) = resolve(word_at(bytes, offset + 24 + 8 * i as usize)) {
                        stack.push(child);
                    }
                }
            }
        }
        let node = closure
            .iter()
            .copied()
            .find(|&offset| shape(offset) == Some((4, 2)))
            .expect("the one `tag 4` node");
        let link = resolve(word_at(bytes, node + 8)).expect("its name link");
        for (name, set) in &roots {
            if set.contains(&link) {
                link_roots.insert(name);
            }
            if set.contains(&node) {
                node_roots.insert(name);
            }
        }

        // Every holder, and which root reaches it.
        for holder in &objects {
            let names_it = if holder.tag <= abi::TAG_MAX_CTOR_TAG {
                (0..usize::from(holder.other))
                    .any(|slot| resolve(word_at(bytes, holder.off + 8 + 8 * slot)) == Some(link))
            } else if holder.tag == abi::TAG_ARRAY {
                (0..word_at(bytes, holder.off + 8)).any(|i| {
                    resolve(word_at(bytes, holder.off + 24 + 8 * i as usize)) == Some(link)
                })
            } else {
                false
            };
            if !names_it {
                continue;
            }
            holders.insert((index, holder.off));
            for (name, set) in &roots {
                if set.contains(&holder.off) {
                    *by_root.entry((*name).to_owned()).or_default() += 1;
                }
            }
        }
    }

    if !prelude_loaded {
        assert!(
            holders.is_empty(),
            "the third shape is not in the C3 fixtures"
        );
        return;
    }

    // Objects, and the population they were drawn from.
    assert_eq!(holders.len(), 5, "five holder OBJECTS");
    assert_eq!(
        modules_seen.len(),
        1,
        "all in a single module - the scope is `Init/Prelude.olean`, asserted \
         rather than left implicit"
    );

    // What they belong to.
    assert_eq!(
        by_root.into_iter().collect::<Vec<_>>(),
        vec![
            ("constNames".to_owned(), 1),
            ("constants".to_owned(), 1),
            ("entries".to_owned(), 3),
        ],
        "the holders sit under THREE different `ModuleData` roots, and each \
         under exactly one - five holders, five root memberships"
    );
    assert_eq!(
        link_roots.into_iter().collect::<Vec<_>>(),
        vec!["constNames", "constants", "entries"],
        "and the link itself is reachable from ALL THREE - which follows from \
         the `by_root` pin above without any walk at all, since one holder is \
         under `constNames` and a holder is by definition an object that names \
         the link. The first version pinned two here and contradicted its own \
         neighbour; w190 caught it"
    );
    assert_eq!(
        node_roots.into_iter().collect::<Vec<_>>(),
        vec!["entries"],
        "while the NODE that holds the link is reachable from `entries` ALONE. \
         This is the assertion the bad pin was standing in front of: the name \
         escapes `entries` and the object does not, and one sentence covering \
         both is what let a two-element set look right"
    );

    // What that does and does not do to `1dd7c288`.
    assert_eq!(
        (third_shape_in_constants, third_shape_total),
        (0, 99),
        "`1dd7c288`'s exclusion is re-measured here and stands: not one of the \
         99 third-shape objects is reachable from `constants`. What moves is \
         its SCOPE - the exclusion is a fact about those objects, not a \
         partition of the module, because one of their names is in the \
         declaration graph and in the constant-name array. Entries-only was the \
         observed pattern for every object in this descent, so a holder under \
         `constants` is a measured departure and not an artefact of selection"
    );
}
