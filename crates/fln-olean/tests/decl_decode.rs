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
