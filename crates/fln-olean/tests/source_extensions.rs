//! The actual pinned Prelude journals, plus hostile captured-entry mutations.
#![forbid(unsafe_code)]
use fln_core::expr::{Literal, NatLit};
use fln_core::name::Name;
use fln_olean::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
use fln_olean::source_extensions::{
    DecodeError, DecodeLimits, DiscrTreeKey, InlineKind, ReducibilityStatus, SimpKind,
    SourceExtensions, decode,
};
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use fln_rt::region::{compact, materialize};
use std::sync::OnceLock;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn blocks() -> &'static Vec<OpaqueExtensionBlock> {
    static BLOCKS: OnceLock<Vec<OpaqueExtensionBlock>> = OnceLock::new();
    BLOCKS.get_or_init(|| {
        let public = include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean");
        let server =
            include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.server");
        let private =
            include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.private");
        OleanView::parse_with_dependencies(private, &[public, server])
            .unwrap()
            .extension_payloads(WalkBudget::default(), 32 << 20)
            .unwrap()
    })
}
fn entry(extension: &str) -> Obj {
    materialize(
        &blocks()
            .iter()
            .find(|b| b.name == n(extension))
            .unwrap()
            .entries[0],
        0,
    )
    .unwrap()
}
fn one(extension: &str, object: &Obj) -> Vec<OpaqueExtensionBlock> {
    vec![OpaqueExtensionBlock {
        name: n(extension),
        entries: vec![compact(object, 0).unwrap()],
    }]
}
fn read(blocks: &[OpaqueExtensionBlock]) -> Result<SourceExtensions, DecodeError> {
    decode(blocks, DecodeLimits::default())
}

#[test]
fn real_prelude_decodes_class_outputs_instance_order_and_defaults() {
    let decoded = read(blocks()).unwrap();
    assert_eq!(
        (
            decoded.classes.len(),
            decoded.instances.len(),
            decoded.defaults.len()
        ),
        (75, 151, 18)
    );
    let addition = decoded
        .classes
        .iter()
        .find(|row| row.name == n("HAdd"))
        .unwrap();
    assert_eq!(addition.out_params, [2]);
    assert_eq!(addition.out_level_params, [2]);
    let beq = decoded
        .instances
        .iter()
        .find(|row| row.declaration == n("instBEqOfDecidableEq"))
        .unwrap();
    assert_eq!(beq.priority, 500);
    assert_eq!(beq.synth_order, [1]);
    assert!(beq.scope.is_none());
    let conjunction = decoded
        .instances
        .iter()
        .find(|row| row.declaration == n("instDecidableAnd"))
        .unwrap();
    assert_eq!(conjunction.synth_order, [2, 3]);
    assert!(decoded.defaults.iter().any(|row| row.class == n("OfNat")));
    // `export Decidable (isTrue isFalse decide)` (vendored src/Init/Prelude.lean)
    // is decoded, not reported as an uninterpreted extension.
    assert!(!decoded.uninterpreted.contains(&n("Lean.aliasExtension")));
    for name in ["isTrue", "isFalse", "decide"] {
        assert!(
            decoded.aliases.iter().any(|row| row.alias == n(name)
                && row.declaration == Name::from_components(["Decidable", name])),
            "the Prelude exports {name} as Decidable.{name}"
        );
    }
    // `protectedExt` (vendored src/Lean/Modifiers.lean) is decoded too. The pinned
    // `lean` reports `(protectedExt.getModuleEntries env idx).size` = 611 for
    // Init.Prelude, and `isProtected` true for the first five names below and
    // false for the last four.
    assert!(!decoded.uninterpreted.contains(&n("Lean.protectedExt")));
    assert_eq!(decoded.protected.len(), 611);
    for name in [
        "Nat.add",
        "Nat.lt_irrefl",
        "Nat.le_refl",
        "Nat.zero.elim",
        "Lean.SourceInfo.none",
    ] {
        assert!(decoded.protected.contains(&n(name)), "{name} is protected");
    }
    for name in ["Nat.pred", "Nat.succ", "Nat.ble", "Nat.le.refl"] {
        assert!(
            !decoded.protected.contains(&n(name)),
            "{name} is not protected"
        );
    }
    // The pin writes each module's tags sorted by `Name.quickLt`
    // (`mkTagDeclarationExtension`'s `toArrayFn`) and binary-searches them in
    // `isTagged`. Its 611 entries are strictly ascending under fln_core's
    // `quick_lt`, so FrankenLean's writer can produce an array the pin can search.
    assert!(
        decoded
            .protected
            .windows(2)
            .all(|pair| pair[0].quick_lt(&pair[1])),
        "the pin's protected entries are in Name.quickLt order"
    );
    assert!(
        decoded
            .instances
            .iter()
            .all(|row| !row.value.has_expr_mvar() && !row.value.has_level_mvar())
    );
}

/// The pinned Reference reports 317 auxRecExt entries for Init.Prelude. Unlike
/// the general isAuxRecursor query, the journal itself does not include Eq.ndrec:
/// that declaration is one of the pin's three explicit legacy exceptions.
#[test]
fn real_auxiliary_tags_roundtrip_in_the_pins_binary_search_order() {
    use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};
    use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget};
    let decoded = read(blocks()).unwrap();
    assert!(!decoded.uninterpreted.contains(&n("Lean.auxRecExt")));
    assert_eq!(decoded.aux_recursors.len(), 317);
    for name in ["Nat.recOn", "Nat.casesOn", "Nat.brecOn", "Nat.below"] {
        assert!(decoded.aux_recursors.contains(&n(name)), "{name}");
    }
    for name in ["Nat.add", "Eq.ndrec"] {
        assert!(!decoded.aux_recursors.contains(&n(name)), "{name}");
    }
    assert!(
        decoded
            .aux_recursors
            .windows(2)
            .all(|pair| pair[0].quick_lt(&pair[1]))
    );
    let mut supplied = decoded.aux_recursors.clone();
    supplied.reverse();
    for version in fln_olean::format::OLEAN_ACCEPTED_VERSIONS {
        let encoded = encode_module_with_source_metadata(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[],
                extra_const_names: &[],
            },
            &SourceMetadata {
                aux_recursors: supplied.clone(),
                ..SourceMetadata::default()
            },
            OleanWriteHeader {
                version: *version,
                flags: 1,
                lean_version: fln_olean::format::PIN_TAG.strip_prefix('v').unwrap(),
                githash: fln_olean::format::PIN_COMMIT,
                base_addr: 2 * fln_olean::format::REGION_ALIGN as u64,
            },
            WriteBudget::default(),
        )
        .unwrap();
        let view = OleanView::parse(&encoded.bytes).unwrap();
        let actual = view
            .extension_payloads(WalkBudget::default(), 4 << 20)
            .unwrap();
        let actual = read(&actual).unwrap();
        assert_eq!(actual.aux_recursors, decoded.aux_recursors);
        assert!(actual.uninterpreted.is_empty());
    }
}

/// The Prelude's `reducibilityCore` entries (bead fln-gkhu), against what the
/// pinned `lean` reports through `getReducibilityStatus` for the same names:
/// instOfNatNat, Nat.add, instAddNat, instLTNat and Nat.decLt are
/// implicitReducible; inferInstance is reducible; id, OfNat.ofNat, Nat.lt and
/// Nat.le are semireducible, the default, which the pin records by absence.
#[test]
fn real_prelude_decodes_the_reducibility_status_the_pin_reports() {
    let decoded = read(blocks()).unwrap();
    assert!(!decoded.uninterpreted.contains(&n("reducibilityCore")));
    assert_eq!(decoded.reducibility.len(), 1061);
    let status = |name: &str| {
        let rows: Vec<_> = decoded
            .reducibility
            .iter()
            .filter(|row| row.declaration == n(name))
            .map(|row| row.status)
            .collect();
        assert!(rows.len() <= 1, "{name} is recorded once");
        rows.first()
            .copied()
            .unwrap_or(ReducibilityStatus::Semireducible)
    };
    for name in [
        "instOfNatNat",
        "Nat.add",
        "instAddNat",
        "instLTNat",
        "Nat.decLt",
    ] {
        assert_eq!(
            status(name),
            ReducibilityStatus::ImplicitReducible,
            "{name}"
        );
    }
    assert_eq!(status("inferInstance"), ReducibilityStatus::Reducible);
    for name in ["id", "OfNat.ofNat", "Nat.lt", "Nat.le"] {
        assert_eq!(status(name), ReducibilityStatus::Semireducible, "{name}");
    }
}

/// The Prelude's `Lean.Compiler.inlineAttrs` entries. Its written `@[macro_inline]` declarations
/// are the twelve the vendored `src/Init/Prelude.lean` tags (`rg -n -A2 macro_inline`), the two
/// anonymous instances under the names the pin gives them (`instDecidableAnd`,
/// `instDecidableOr`). The pin also tags the generated `T.ctorIdx` of each one-constructor type
/// (vendored `src/Lean/Meta/Constructions/CtorIdx.lean:92-93`): 91 in the Prelude. Other kinds
/// are decoded, never promoted: `Nat.add` is not tagged at all.
#[test]
fn real_prelude_decodes_the_inline_attribute_kinds() {
    let decoded = read(blocks()).unwrap();
    assert!(
        !decoded
            .uninterpreted
            .contains(&n("Lean.Compiler.inlineAttrs"))
    );
    let (constructor_indices, mut macro_inline): (Vec<_>, Vec<_>) = decoded
        .inline
        .iter()
        .filter(|row| row.kind == InlineKind::MacroInline)
        .map(|row| row.declaration.clone())
        .partition(|name| name.to_display_string().ends_with(".ctorIdx"));
    assert_eq!(constructor_indices.len(), 91);
    macro_inline.sort();
    let mut expected: Vec<_> = [
        "False.elim",
        "absurd",
        "cast",
        "dite",
        "ite",
        "instDecidableAnd",
        "instDecidableOr",
        "cond",
        "Bool.dcond",
        "Bool.or",
        "Bool.and",
        "Option.getD",
    ]
    .map(n)
    .to_vec();
    expected.sort();
    assert_eq!(macro_inline, expected);
    assert!(
        decoded
            .inline
            .iter()
            .any(|row| row.kind != InlineKind::MacroInline),
        "the other inlining kinds are decoded too"
    );
    assert!(
        !decoded
            .inline
            .iter()
            .any(|row| row.declaration == n("Nat.add"))
    );
    // Each declaration has one kind: a repeated row is malformed.
    let row = blocks()
        .iter()
        .find(|block| block.name == n("Lean.Compiler.inlineAttrs"))
        .unwrap()
        .entries[0]
        .clone();
    let repeated = vec![OpaqueExtensionBlock {
        name: n("Lean.Compiler.inlineAttrs"),
        entries: vec![row.clone(), row],
    }];
    assert!(read(&repeated).is_err());
}

#[test]
fn companion_journals_are_cumulative_not_three_disjoint_fragments() {
    let public = include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean");
    let server =
        include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.server");
    let expected = read(blocks()).unwrap();
    for (bytes, dependencies) in [
        (public.as_slice(), vec![]),
        (server.as_slice(), vec![public.as_slice()]),
    ] {
        let blocks = OleanView::parse_with_dependencies(bytes, &dependencies)
            .unwrap()
            .extension_payloads(WalkBudget::default(), 32 << 20)
            .unwrap();
        let actual = read(&blocks).unwrap();
        assert_eq!(actual.classes, expected.classes);
        assert_eq!(actual.instances, expected.instances);
        assert_eq!(actual.defaults, expected.defaults);
    }
}

#[test]
fn scope_is_retained_and_not_silently_promoted_to_global() {
    let wrapped = entry("Lean.Meta.instanceExtension");
    let original = wrapped.ctor_child(0);
    let fields = (0..5).map(|i| original.ctor_child(i)).collect();
    let scoped = Obj::mk_ctor(0, fields, &[2]);
    let scoped = Obj::mk_ctor(1, vec![inject_name(&n("Example")), scoped], &[]);
    let decoded = read(&one("Lean.Meta.instanceExtension", &scoped)).unwrap();
    assert_eq!(decoded.instances[0].scope, Some(n("Example")));
    let inconsistent = Obj::mk_ctor(1, vec![inject_name(&n("Example")), original], &[]);
    assert!(read(&one("Lean.Meta.instanceExtension", &inconsistent)).is_err());
}

#[test]
fn forged_names_shapes_and_duplicate_synthesis_indices_refuse() {
    let class = entry("Lean.classExtension");
    let wrong = Obj::mk_ctor(
        0,
        vec![
            Obj::mk_string("not a Name"),
            class.ctor_child(1),
            class.ctor_child(2),
        ],
        &[],
    );
    assert!(read(&one("Lean.classExtension", &wrong)).is_err());
    let repeated = Obj::mk_ctor(
        0,
        vec![
            class.ctor_child(0),
            Obj::mk_array(vec![Obj::mk_nat(0), Obj::mk_nat(0)]),
            class.ctor_child(2),
        ],
        &[],
    );
    assert!(read(&one("Lean.classExtension", &repeated)).is_err());
    assert!(read(&one("Lean.classExtension", &Obj::mk_nat(0))).is_err());
    let original = entry("Lean.Meta.instanceExtension").ctor_child(0);
    for (index, replacement) in [
        (3, Obj::mk_ctor(1, vec![inject_name(&n("forged"))], &[])),
        (4, Obj::mk_array(vec![Obj::mk_nat(1), Obj::mk_nat(1)])),
        (2, Obj::mk_mpz(&[1], true)),
    ] {
        let fields = (0..5)
            .map(|i| {
                if i == index {
                    replacement.clone_ref()
                } else {
                    original.ctor_child(i)
                }
            })
            .collect();
        let malformed = Obj::mk_ctor(0, vec![Obj::mk_ctor(0, fields, &[0])], &[]);
        assert!(read(&one("Lean.Meta.instanceExtension", &malformed)).is_err());
    }
}

/// A `protectedExt` entry is one `Name`. A name tagged twice (the pin tags a
/// declaration only in its own module) and a payload that is not a `Name` are
/// refused, and neither exposes the valid prefix decoded before it.
#[test]
fn protected_entries_are_names_and_a_repeat_refuses() {
    let tagged = entry("Lean.protectedExt");
    let single = one("Lean.protectedExt", &tagged);
    let decoded = read(&single).unwrap();
    assert_eq!(decoded.protected.len(), 1);
    // Source activation merges every module's entries into one block, so this is
    // also a name tagged by two modules.
    let mut repeated = single.clone();
    repeated[0].entries.push(single[0].entries[0].clone());
    assert!(matches!(read(&repeated), Err(DecodeError::Shape { .. })));
    for forged in [
        Obj::mk_string("Nat.add"),
        Obj::mk_nat(7),
        Obj::mk_ctor(0, vec![tagged.clone_ref(), tagged.clone_ref()], &[]),
    ] {
        let mut prefixed = single.clone();
        prefixed[0].entries.push(compact(&forged, 0).unwrap());
        assert!(read(&prefixed).is_err(), "a non-Name payload is refused");
    }
}

#[test]
fn auxiliary_entries_reject_duplicate_anonymous_and_non_name_payloads() {
    let tagged = entry("Lean.auxRecExt");
    let single = one("Lean.auxRecExt", &tagged);
    assert_eq!(read(&single).unwrap().aux_recursors.len(), 1);
    let mut repeated = single.clone();
    repeated[0].entries.push(single[0].entries[0].clone());
    assert!(matches!(read(&repeated), Err(DecodeError::Shape { .. })));
    for forged in [
        inject_name(&Name::anonymous()),
        Obj::mk_string("Nat.casesOn"),
        Obj::mk_nat(7),
    ] {
        let mut prefixed = single.clone();
        prefixed[0].entries.push(compact(&forged, 0).unwrap());
        assert!(read(&prefixed).is_err());
    }
    assert!(matches!(
        decode(
            &single,
            DecodeLimits {
                max_entries: 0,
                ..DecodeLimits::default()
            }
        ),
        Err(DecodeError::Limit { .. })
    ));
}

#[test]
fn selected_payloads_are_cumulatively_bounded_and_no_prefix_escapes() {
    let only = one("Lean.classExtension", &entry("Lean.classExtension"));
    for limits in [
        DecodeLimits {
            max_bytes: 0,
            ..Default::default()
        },
        DecodeLimits {
            max_objects: 0,
            ..Default::default()
        },
        DecodeLimits {
            max_entries: 0,
            ..Default::default()
        },
    ] {
        assert!(matches!(
            decode(&only, limits),
            Err(DecodeError::Limit { .. })
        ));
    }
    let mut repeated = only.clone();
    let first = repeated[0].entries[0].clone();
    repeated[0].entries.push(first);
    assert!(
        decode(
            &repeated,
            DecodeLimits {
                max_bytes: only[0].entries[0].len(),
                ..Default::default()
            }
        )
        .unwrap_err()
        .is_resource()
    );
    repeated[0].entries.push(vec![]);
    assert!(
        read(&repeated).is_err(),
        "a valid prefix is not a successful result"
    );
}

#[test]
fn extension_names_are_structural_and_duplicate_blocks_refuse() {
    let only = one("Lean.classExtension", &entry("Lean.classExtension"));
    let duplicate = vec![only[0].clone(), only[0].clone()];
    assert!(read(&duplicate).is_err());
    let mut lookalike = only;
    lookalike[0].name = Name::from_components(["Lean.classExtension"]);
    let decoded = read(&lookalike).unwrap();
    assert!(decoded.classes.is_empty());
    assert_eq!(
        decoded.uninterpreted,
        [Name::from_components(["Lean.classExtension"])]
    );
}

/// The pin's stored `DiscrTree` paths (`InstanceEntry.keys`), read back from the
/// pinned Prelude. Expected values are the pin's own: `Meta.instanceExtension`
/// state under `import Lean`, printed with `repr` per instance, and the key
/// kinds counted over every instance whose module is `Init.Prelude`.
#[test]
fn real_prelude_instance_keys_are_the_pins_paths() {
    let decoded = read(blocks()).unwrap();
    let keys = |name: &str| {
        decoded
            .instances
            .iter()
            .find(|row| row.declaration == n(name))
            .unwrap()
            .keys
            .clone()
    };
    let c = |name: &str, arity: u32| DiscrTreeKey::Const(n(name), arity);
    use DiscrTreeKey::{Arrow, Other, Star};
    assert_eq!(
        keys("instDecidableAnd"),
        [c("Decidable", 1), c("And", 2), Star, Star]
    );
    assert_eq!(keys("instOfNatNat"), [c("OfNat", 2), c("Nat", 0), Star]);
    assert_eq!(keys("instBEqOfDecidableEq"), [c("BEq", 1), Star]);
    assert_eq!(
        keys("Nat.decLt"),
        [
            c("Decidable", 1),
            c("LT.lt", 4),
            c("Nat", 0),
            Star,
            Star,
            Star
        ]
    );
    assert_eq!(
        keys("instDecidableEqNat"),
        [c("Decidable", 1), c("Eq", 3), c("Nat", 0), Star, Star]
    );
    assert_eq!(keys("instLTNat"), [c("LT", 1), c("Nat", 0)]);
    assert_eq!(keys("instHAdd"), [c("HAdd", 3), Star, Star, Star]);
    assert_eq!(
        keys("instDecidableNot"),
        [c("Decidable", 1), c("Not", 1), Star]
    );
    assert_eq!(keys("Pi.instNonempty"), [c("Nonempty", 1), Arrow, Star]);
    assert_eq!(keys("instInhabitedSort"), [c("Inhabited", 1), Other]);
    let mut kinds = [0usize; 7];
    for row in &decoded.instances {
        assert!(
            matches!(row.keys[0], DiscrTreeKey::Const(..)),
            "{:?}",
            row.declaration
        );
        for key in &row.keys {
            kinds[match key {
                Star => 0,
                Other => 1,
                DiscrTreeKey::Lit(_) => 2,
                DiscrTreeKey::FVar(..) => 3,
                DiscrTreeKey::Const(..) => 4,
                Arrow => 5,
                DiscrTreeKey::Proj(..) => 6,
            }] += 1;
        }
    }
    assert_eq!(kinds, [239, 1, 0, 0, 289, 5, 0]);
    let simp_keys: usize = decoded
        .simps
        .iter()
        .map(|entry| match &entry.kind {
            SimpKind::Theorem(theorem) => theorem.keys.len(),
            _ => 0,
        })
        .sum();
    let total: usize = kinds.iter().sum::<usize>() + simp_keys;
    let limits = |max_keys| DecodeLimits {
        max_keys,
        ..Default::default()
    };
    assert!(decode(blocks(), limits(total)).is_ok());
    assert!(matches!(
        decode(blocks(), limits(total - 1)),
        Err(DecodeError::Limit { .. })
    ));
}

/// An instance entry whose stored path is `keys`, around a real Prelude entry.
fn with_keys(keys: Vec<Obj>) -> Vec<OpaqueExtensionBlock> {
    let original = entry("Lean.Meta.instanceExtension").ctor_child(0);
    let mut fields: Vec<Obj> = (0..5).map(|i| original.ctor_child(i)).collect();
    fields[0] = Obj::mk_array(keys);
    let wrapped = Obj::mk_ctor(0, vec![Obj::mk_ctor(0, fields, &[0])], &[]);
    one("Lean.Meta.instanceExtension", &wrapped)
}

#[test]
fn every_key_kind_decodes_and_forged_keys_refuse() {
    let name = |text: &str| inject_name(&n(text));
    let literal =
        |tag: u8, payload: Obj| Obj::mk_ctor(2, vec![Obj::mk_ctor(tag, vec![payload], &[])], &[]);
    let kinds = vec![
        Obj::mk_ctor(4, vec![name("Decidable"), Obj::mk_nat(1)], &[]),
        literal(0, Obj::mk_nat(5)),
        literal(0, Obj::mk_mpz(&[0, 1], false)),
        literal(1, Obj::mk_string("é")),
        Obj::mk_ctor(
            6,
            vec![name("Subtype"), Obj::mk_nat(0), Obj::mk_nat(0)],
            &[],
        ),
        Obj::mk_ctor(3, vec![name("h"), Obj::mk_nat(2)], &[]),
        Obj::mk_nat(0),
        Obj::mk_nat(1),
        Obj::mk_nat(5),
    ];
    let decoded = read(&with_keys(kinds)).unwrap();
    assert_eq!(
        decoded.instances[0].keys,
        [
            DiscrTreeKey::Const(n("Decidable"), 1),
            DiscrTreeKey::Lit(Literal::Nat(NatLit::from_u64(5))),
            DiscrTreeKey::Lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1]))),
            DiscrTreeKey::Lit(Literal::Str("é".into())),
            DiscrTreeKey::Proj(n("Subtype"), 0, 0),
            DiscrTreeKey::FVar(n("h"), 2),
            DiscrTreeKey::Star,
            DiscrTreeKey::Other,
            DiscrTreeKey::Arrow,
        ]
    );
    // FrankenLean's own artifacts store no path; that instance is left unindexed.
    assert!(
        read(&with_keys(vec![])).unwrap().instances[0]
            .keys
            .is_empty()
    );
    let head = || Obj::mk_ctor(4, vec![name("Decidable"), Obj::mk_nat(1)], &[]);
    for (why, forged) in [
        ("`lit` as a scalar", vec![head(), Obj::mk_nat(2)]),
        ("an unknown scalar key", vec![head(), Obj::mk_nat(7)]),
        (
            "an unknown key constructor",
            vec![head(), Obj::mk_ctor(7, vec![name("x")], &[])],
        ),
        (
            "`const` without its arity",
            vec![Obj::mk_ctor(4, vec![name("Decidable")], &[])],
        ),
        (
            "`const` naming a string",
            vec![Obj::mk_ctor(
                4,
                vec![Obj::mk_string("x"), Obj::mk_nat(1)],
                &[],
            )],
        ),
        (
            "an arity that is not a Nat",
            vec![Obj::mk_ctor(
                4,
                vec![name("Decidable"), Obj::mk_string("1")],
                &[],
            )],
        ),
        (
            "an unknown literal",
            vec![head(), literal(2, Obj::mk_nat(5))],
        ),
        (
            "a negative literal",
            vec![head(), literal(0, Obj::mk_mpz(&[1], true))],
        ),
        (
            "`proj` without its argument count",
            vec![
                head(),
                Obj::mk_ctor(6, vec![name("S"), Obj::mk_nat(0)], &[]),
            ],
        ),
    ] {
        assert!(read(&with_keys(forged)).is_err(), "{why} must refuse");
    }
}

/// `@[pp_using_anonymous_constructor]` (vendored `src/Init/Prelude.lean`) tags `And`, `Subtype`
/// and `Fin` in the pinned Prelude, and nothing there is `@[pp_nodot]` or an
/// `@[app_unexpander]`.
#[test]
fn real_prelude_decodes_the_delaborator_tags() {
    let decoded = read(blocks()).unwrap();
    let mut tagged: Vec<String> = decoded
        .pp_anonymous_constructor
        .iter()
        .map(Name::to_display_string)
        .collect();
    tagged.sort();
    assert_eq!(tagged, ["And", "Fin", "Subtype"]);
    assert!(decoded.pp_nodot.is_empty());
    assert!(decoded.app_unexpanders.is_empty());
}

/// The pinned `Init.NotationExtra` registers its unexpanders globally, `(a, b)` for
/// `Prod.mk` among them (vendored `src/Init/NotationExtra.lean`).
#[test]
fn real_notation_extra_decodes_its_app_unexpanders() {
    let lib = match std::env::var("FLN_REFERENCE_LIB") {
        Ok(dir) => std::path::PathBuf::from(dir),
        Err(_) => match std::env::var("HOME") {
            Ok(home) => std::path::PathBuf::from(home)
                .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean"),
            Err(_) => return,
        },
    };
    let path = lib.join("Init/NotationExtra.olean");
    let Ok(public) = std::fs::read(&path) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return;
    };
    let server = std::fs::read(path.with_extension("olean.server")).unwrap();
    let private = std::fs::read(path.with_extension("olean.private")).unwrap();
    let blocks = OleanView::parse_with_dependencies(&private, &[&public, &server])
        .unwrap()
        .extension_payloads(WalkBudget::default(), 32 << 20)
        .unwrap();
    let decoded = read(&blocks).unwrap();
    let keys: std::collections::BTreeSet<String> = decoded
        .app_unexpanders
        .iter()
        .map(|entry| entry.key.to_display_string())
        .collect();
    for key in ["Prod.mk", "List.cons", "Unit.unit"] {
        assert!(keys.contains(key), "{key}: {keys:?}");
    }
    assert!(
        decoded
            .app_unexpanders
            .iter()
            .all(|entry| entry.scope.is_none())
    );
    let prod = decoded
        .app_unexpanders
        .iter()
        .find(|entry| entry.key == n("Prod.mk"))
        .unwrap();
    assert_eq!(prod.declaration, n("unexpandProdMk"));
}
