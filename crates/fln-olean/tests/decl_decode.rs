//! Declaration-decoder suite (bead franken_lean-z6c seed): real pinned-Reference
//! declarations decoded from the C3 fixture corpus, with the identity-layer
//! cross-checks (Name.hash / Level.Data / Expr.Data) that make a layout misread
//! or a hash-law divergence a typed error rather than silent corruption.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::path::PathBuf;

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

        // Every `ConstantVal` on the wire, by the name in its slot 0, with the
        // length of the `levelParams` chain in its slot 1.
        let mut on_the_wire: std::collections::BTreeMap<String, usize> =
            std::collections::BTreeMap::new();
        for object in &objects {
            // (0, 3, 32): three pointer fields and no scalar area, the shape
            // measured over 215,111 objects and enforced by `decode_constant_val`.
            if (object.tag, object.other, object.cs_sz) != (0, 3, 32) {
                continue;
            }
            let Ok(name) = DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(word_at(bytes, object.off + 8))
            else {
                continue;
            };

            let mut cursor = word_at(bytes, object.off + 16);
            let mut cells = 0usize;
            while cursor & 1 == 0 {
                let Some(cell) = deref(cursor) else {
                    break;
                };
                let Some(cell) = at.get(&cell) else {
                    break;
                };
                assert_eq!(
                    (cell.tag, cell.other),
                    (1, 2),
                    "{module}: a `levelParams` chain must be cons cells"
                );
                widths.insert(i64::from(cell.cs_sz) - (8 + 8 * i64::from(cell.other)));
                sizes.insert(cell.cs_sz);
                cells += 1;
                cursor = word_at(bytes, cell.off + 16);
            }
            on_the_wire.insert(name.to_display_string(), cells);
        }

        // The binding, per declaration.
        for info in &infos {
            let name = info.name().to_display_string();
            let decoded = info.constant_val().level_params.len();
            let chained = on_the_wire.get(&name).copied().unwrap_or_else(|| {
                panic!("{module}: {name} decoded, but no ConstantVal on the wire carries its name")
            });
            assert_eq!(
                chained, decoded,
                "{module}: {name}: the decoder returned {decoded} universe \
                 parameters from a chain of {chained} cells. Unequal means the \
                 cells measured by the cells above are not the cells \
                 `list_ptrs` walks, and the recorded width describes the wrong \
                 population"
            );
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
