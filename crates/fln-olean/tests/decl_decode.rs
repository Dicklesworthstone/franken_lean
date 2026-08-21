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
