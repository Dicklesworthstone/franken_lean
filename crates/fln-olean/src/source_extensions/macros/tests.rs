use super::*;
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use fln_rt::region::compact;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn registration(key: &Name, declaration: &Name, scope: Option<&Name>) -> Obj {
    let entry = Obj::mk_ctor(0, vec![inject_name(key), inject_name(declaration)], &[]);
    match scope {
        None => Obj::mk_ctor(super::super::format::SCOPE_GLOBAL, vec![entry], &[]),
        Some(scope) => Obj::mk_ctor(
            super::super::format::SCOPE_SCOPED,
            vec![inject_name(scope), entry],
            &[],
        ),
    }
}

fn block(objects: &[Obj]) -> OpaqueExtensionBlock {
    OpaqueExtensionBlock {
        name: name(MACRO_EXTENSION),
        entries: objects
            .iter()
            .map(|object| compact(object, 0).unwrap())
            .collect(),
    }
}

#[test]
fn exact_scoped_keyed_layout_keeps_order_and_structural_names() {
    let key = Name::str(Name::anonymous(), "a.b");
    let first = Name::num(name("_private.User"), 7);
    let second = name("User.second");
    let scope = name("Activated");
    let input = block(&[
        registration(&key, &first, None),
        registration(&key, &second, Some(&scope)),
        registration(&key, &first, None),
    ]);
    let rows = decode(&[input], DecodeLimits::default()).unwrap();
    assert_eq!(
        rows,
        [
            MacroEntry {
                key: key.clone(),
                declaration: first.clone(),
                scope: None
            },
            MacroEntry {
                key: key.clone(),
                declaration: second,
                scope: Some(scope)
            },
            MacroEntry {
                key,
                declaration: first,
                scope: None
            },
        ]
    );
    assert_ne!(rows[0].key, name("a.b"));
}

#[test]
fn cumulative_bytes_objects_and_entries_have_exact_boundaries() {
    let input = block(&[registration(&name("kind"), &name("User.rule"), None)]);
    let bytes = input.entries[0].len();
    let objects = audit(&input.entries[0], 0).unwrap().objects;
    for (limits, resource) in [
        (
            DecodeLimits {
                max_bytes: bytes,
                ..DecodeLimits::default()
            },
            "macro payload bytes",
        ),
        (
            DecodeLimits {
                max_objects: objects,
                ..DecodeLimits::default()
            },
            "macro objects",
        ),
        (
            DecodeLimits {
                max_entries: 1,
                ..DecodeLimits::default()
            },
            "macro entries",
        ),
    ] {
        let mut decoder = Decoder::new(limits);
        assert_eq!(
            decoder.decode(std::slice::from_ref(&input)).unwrap().len(),
            1
        );
        assert!(matches!(decoder.decode(std::slice::from_ref(&input)),
            Err(DecodeError::Limit { resource: actual }) if actual == resource));
        assert!(decoder.decode(&[]).unwrap_err().is_resource());
    }
    let exact = DecodeLimits {
        max_bytes: bytes,
        max_objects: objects,
        max_entries: 1,
        ..DecodeLimits::default()
    };
    assert_eq!(
        decode(std::slice::from_ref(&input), exact).unwrap().len(),
        1
    );
    assert!(
        decode(
            &[input],
            DecodeLimits {
                max_bytes: bytes - 1,
                ..exact
            }
        )
        .unwrap_err()
        .is_resource()
    );
}

#[test]
fn malformed_suffix_and_duplicate_blocks_never_publish_a_prefix() {
    let valid = registration(&name("kind"), &name("User.rule"), None);
    let malformed = block(&[valid.clone_ref(), Obj::mk_nat(0)]);
    let mut decoder = Decoder::new(DecodeLimits::default());
    assert!(matches!(
        decoder.decode(&[malformed]),
        Err(DecodeError::Shape { .. })
    ));
    assert!(matches!(
        decoder.decode(&[block(&[valid.clone_ref()])]),
        Err(DecodeError::Shape {
            detail: "macro decoder reused after refusal"
        })
    ));
    let one = block(&[valid]);
    assert!(matches!(
        decode(&[one.clone(), one], DecodeLimits::default()),
        Err(DecodeError::Shape {
            detail: "duplicate macro metadata extension block"
        })
    ));
}

#[test]
fn malformed_key_declaration_scope_and_wrapper_refuse() {
    let key = name("kind");
    let declaration = name("User.rule");
    for value in [
        registration(&Name::anonymous(), &declaration, None),
        registration(&key, &Name::anonymous(), None),
        Obj::mk_ctor(9, vec![inject_name(&key)], &[]),
        Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[]),
    ] {
        assert!(matches!(
            decode(&[block(&[value])], DecodeLimits::default()),
            Err(DecodeError::Shape { .. })
        ));
    }
}

#[test]
fn unknown_extension_has_no_macro_or_execution_authority() {
    let input = OpaqueExtensionBlock {
        name: name("User.macroAttribute"),
        entries: vec![vec![0xff]],
    };
    let limits = DecodeLimits {
        max_bytes: 0,
        max_entries: 0,
        max_objects: 0,
        ..DecodeLimits::default()
    };
    assert!(decode(&[input], limits).unwrap().is_empty());
}
