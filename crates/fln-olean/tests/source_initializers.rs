//! Initialized globals must not be confused with their stored placeholder body.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_olean::initializers::{
    BUILTIN_INIT_EXTENSION, InitEntry, InitJournals, REGULAR_INIT_EXTENSION, decode,
};
use fln_olean::region::OpaqueExtensionBlock;
use fln_olean::source_extensions::{DecodeError, DecodeLimits};
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use fln_rt::region::{audit, compact};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn pair(declaration: &Name, initializer: &Name) -> Obj {
    Obj::mk_ctor(
        0,
        vec![inject_name(declaration), inject_name(initializer)],
        &[],
    )
}
fn block(extension: &str, entries: &[Obj]) -> OpaqueExtensionBlock {
    OpaqueExtensionBlock {
        name: name(extension),
        entries: entries
            .iter()
            .map(|entry| compact(entry, 0).unwrap())
            .collect(),
    }
}

#[test]
fn preserves_both_journals_and_distinguishes_standalone_actions() {
    let regular = block(
        REGULAR_INIT_EXTENSION,
        &[
            pair(&name("z"), &name("initZ")),
            pair(&name("standalone"), &Name::anonymous()),
            pair(&name("a"), &name("initA")),
        ],
    );
    let builtin = block(
        BUILTIN_INIT_EXTENSION,
        &[pair(&name("z"), &name("builtinZ"))],
    );
    assert_eq!(
        decode(&[regular, builtin], DecodeLimits::default()).unwrap(),
        InitJournals {
            regular: vec![
                InitEntry {
                    declaration: name("z"),
                    initializer: Some(name("initZ")),
                },
                InitEntry {
                    declaration: name("standalone"),
                    initializer: None,
                },
                InitEntry {
                    declaration: name("a"),
                    initializer: Some(name("initA")),
                },
            ],
            builtin: vec![InitEntry {
                declaration: name("z"),
                initializer: Some(name("builtinZ")),
            }],
        }
    );
}

#[test]
fn malformed_pairs_and_names_never_expose_a_valid_prefix() {
    let valid = pair(&name("value"), &name("initializeValue"));
    let invalid = [
        Obj::mk_nat(0),
        Obj::mk_ctor(
            1,
            vec![inject_name(&name("value")), inject_name(&name("init"))],
            &[],
        ),
        Obj::mk_ctor(0, vec![inject_name(&name("value"))], &[]),
        pair(&Name::anonymous(), &name("init")),
        Obj::mk_ctor(
            0,
            vec![inject_name(&name("value")), Obj::mk_string("not a Name")],
            &[],
        ),
    ];
    for object in invalid {
        let entries = block(REGULAR_INIT_EXTENSION, &[valid.clone_ref(), object]);
        assert!(decode(&[entries], DecodeLimits::default()).is_err());
    }
    let mut corrupt = block(REGULAR_INIT_EXTENSION, &[valid]);
    corrupt.entries.push(vec![]);
    assert!(decode(&[corrupt], DecodeLimits::default()).is_err());
}

#[test]
fn limits_are_shared_between_regular_and_builtin_journals() {
    let regular = block(REGULAR_INIT_EXTENSION, &[pair(&name("a"), &name("ia"))]);
    let builtin = block(BUILTIN_INIT_EXTENSION, &[pair(&name("b"), &name("ib"))]);
    let bytes = regular.entries[0].len();
    let objects = audit(&regular.entries[0], 0).unwrap().objects;
    let blocks = [regular, builtin];
    for limits in [
        DecodeLimits {
            max_bytes: bytes,
            ..Default::default()
        },
        DecodeLimits {
            max_objects: objects,
            ..Default::default()
        },
        DecodeLimits {
            max_entries: 1,
            ..Default::default()
        },
    ] {
        // Each ceiling admits the first journal; none admits the complete batch.
        assert!(decode(&blocks[..1], limits).is_ok());
        assert!(matches!(
            decode(&blocks, limits),
            Err(DecodeError::Limit { .. })
        ));
    }
}

#[test]
fn zero_budgets_allow_empty_journals_but_not_an_entry() {
    let limits = DecodeLimits {
        max_bytes: 0,
        max_objects: 0,
        max_entries: 0,
        ..Default::default()
    };
    let empty = [
        block(REGULAR_INIT_EXTENSION, &[]),
        block(BUILTIN_INIT_EXTENSION, &[]),
    ];
    assert_eq!(decode(&empty, limits).unwrap(), InitJournals::default());
    for extension in [REGULAR_INIT_EXTENSION, BUILTIN_INIT_EXTENSION] {
        let single = block(extension, &[pair(&name("a"), &Name::anonymous())]);
        assert!(decode(&[single], limits).unwrap_err().is_resource());
    }
}

#[test]
fn names_are_structural_and_duplicate_blocks_are_rejected() {
    let original = block(REGULAR_INIT_EXTENSION, &[pair(&name("a"), &name("ia"))]);
    assert!(matches!(
        decode(
            &[original.clone(), original.clone()],
            DecodeLimits::default()
        ),
        Err(DecodeError::Shape { .. })
    ));
    let mut lookalike = original;
    lookalike.name = Name::from_components([REGULAR_INIT_EXTENSION]);
    // An unrelated extension need not even contain the selected schema.
    lookalike.entries.push(vec![]);
    assert_eq!(
        decode(&[lookalike], DecodeLimits::default()).unwrap(),
        InitJournals::default()
    );
}

#[test]
fn source_metadata_accounts_for_initializer_rows_in_its_shared_budget() {
    let init = block(
        REGULAR_INIT_EXTENSION,
        &[pair(&name("value"), &name("initializeValue"))],
    );
    let alias = block(
        fln_olean::source_extensions::ALIAS_EXTENSION,
        &[pair(&name("alias"), &name("value"))],
    );
    let decoded = fln_olean::source_extensions::decode(
        &[alias.clone(), init.clone()],
        DecodeLimits::default(),
    )
    .unwrap();
    assert_eq!(
        decoded.initializers,
        decode(std::slice::from_ref(&init), DecodeLimits::default()).unwrap()
    );
    assert_eq!(decoded.aliases.len(), 1);
    assert!(decoded.uninterpreted.is_empty());
    for limits in [
        DecodeLimits {
            max_entries: 1,
            ..Default::default()
        },
        DecodeLimits {
            max_bytes: alias.entries[0].len().max(init.entries[0].len()),
            ..Default::default()
        },
        DecodeLimits {
            max_objects: audit(&alias.entries[0], 0)
                .unwrap()
                .objects
                .max(audit(&init.entries[0], 0).unwrap().objects),
            ..Default::default()
        },
    ] {
        assert!(fln_olean::source_extensions::decode(std::slice::from_ref(&alias), limits).is_ok());
        assert!(fln_olean::source_extensions::decode(std::slice::from_ref(&init), limits).is_ok());
        assert!(
            fln_olean::source_extensions::decode(&[alias.clone(), init.clone()], limits)
                .unwrap_err()
                .is_resource()
        );
    }
    let malformed = block(BUILTIN_INIT_EXTENSION, &[Obj::mk_nat(0)]);
    assert!(
        fln_olean::source_extensions::decode(&[alias, malformed], DecodeLimits::default()).is_err()
    );
}
