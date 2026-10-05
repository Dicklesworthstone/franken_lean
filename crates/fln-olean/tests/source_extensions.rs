//! The actual pinned Prelude journals, plus hostile captured-entry mutations.
#![forbid(unsafe_code)]
use fln_core::expr::{Literal, NatLit};
use fln_core::name::Name;
use fln_olean::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
use fln_olean::source_extensions::{
    DecodeError, DecodeLimits, InstanceKey, ReducibilityStatus, SourceExtensions, decode,
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
    let c = |name: &str, arity: u32| InstanceKey::Const(n(name), arity);
    use InstanceKey::{Arrow, Other, Star};
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
            matches!(row.keys[0], InstanceKey::Const(..)),
            "{:?}",
            row.declaration
        );
        for key in &row.keys {
            kinds[match key {
                Star => 0,
                Other => 1,
                InstanceKey::Lit(_) => 2,
                InstanceKey::FVar(..) => 3,
                InstanceKey::Const(..) => 4,
                Arrow => 5,
                InstanceKey::Proj(..) => 6,
            }] += 1;
        }
    }
    assert_eq!(kinds, [239, 1, 0, 0, 289, 5, 0]);
    let total: usize = kinds.iter().sum();
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
            InstanceKey::Const(n("Decidable"), 1),
            InstanceKey::Lit(Literal::Nat(NatLit::from_u64(5))),
            InstanceKey::Lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1]))),
            InstanceKey::Lit(Literal::Str("é".into())),
            InstanceKey::Proj(n("Subtype"), 0, 0),
            InstanceKey::FVar(n("h"), 2),
            InstanceKey::Star,
            InstanceKey::Other,
            InstanceKey::Arrow,
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
