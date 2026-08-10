//! Declaration-decoder suite (bead franken_lean-z6c seed): real pinned-Reference
//! declarations decoded from the C3 fixture corpus, with the identity-layer
//! cross-checks (Name.hash / Level.Data / Expr.Data) that make a layout misread
//! or a hash-law divergence a typed error rather than silent corruption.

#![forbid(unsafe_code)]

use std::path::PathBuf;

use fln_env::constants::ConstantInfo;
use fln_olean::decl::{DeclDecoder, DeclError};
use fln_olean::region::{OleanView, WalkBudget};

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
fn module_system_private_part_restores_bodies_and_private_auxiliaries() {
    let Some(home) = std::env::var_os("HOME") else {
        return;
    };
    let module = PathBuf::from(home)
        .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
        .join("Init/Data/List/ToArrayImpl.olean");
    if !module.is_file() {
        return;
    }

    let public = std::fs::read(&module).expect("read public module part");
    let server =
        std::fs::read(module.with_extension("olean.server")).expect("read server module part");
    let private =
        std::fs::read(module.with_extension("olean.private")).expect("read private module part");

    let public_view = OleanView::parse(&public).expect("parse public module part");
    let public_infos = DeclDecoder::new(&public_view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode public module part");
    assert_eq!(public_infos.len(), 5, "pin's public declaration census");

    let private_view = OleanView::parse_with_dependencies(&private, &[&public, &server])
        .expect("parse private module part with its compacted dependencies");
    let private_infos = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode private module part through dependency address space");
    assert!(
        private_infos.len() > public_infos.len(),
        "private level must restore declarations absent from the exported part"
    );
    assert!(
        private_infos.iter().any(|info| {
            info.name().to_display_string()
                == "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1"
        }),
        "equation compiler auxiliary omitted by public-only decode"
    );
    assert!(
        matches!(
            private_infos
                .iter()
                .find(|info| info.name().to_display_string() == "List.toArrayAux"),
            Some(ConstantInfo::Defn(_))
        ),
        "private level must retain the definition body rather than a weakened axiom"
    );
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
