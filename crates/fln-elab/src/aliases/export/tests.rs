//! Journal projection fixtures exercise data validation, not declaration admission.
use super::*;
use fln_core::{expr::Expr, level::Level};
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn declarations() -> Environment {
    ["Original.x", "Other.x"]
        .into_iter()
        .fold(Environment::new(), |env, text| {
            env.add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n(text),
                    level_params: vec![],
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }))
            .unwrap()
        })
}
fn row(alias: &Name, target: &Name) -> Vec<u8> {
    let mut bytes = MAGIC.to_vec();
    write_name(alias, &mut bytes).unwrap();
    write_name(target, &mut bytes).unwrap();
    bytes
}
fn raw(env: &Environment, bytes: Vec<u8>) -> Environment {
    let env = if env.extension(&extension_name()).is_none() {
        env.register_extension(descriptor()).unwrap()
    } else {
        env.clone()
    };
    env.push_extension_entry(&extension_name(), bytes).unwrap()
}

#[test]
fn exports_preserve_the_chronological_suffix_and_allow_imported_targets() {
    let base = register(&declarations(), &n("inherited"), &n("Original.x")).unwrap();
    let mut result = base.clone();
    let expected = vec![
        (n("Z.x"), n("Original.x")),
        (n("A.x"), n("Other.x")),
        (n("Z.x"), n("Other.x")),
    ];
    for (alias, target) in &expected {
        result = register(&result, alias, target).unwrap();
    }
    assert_eq!(
        registrations(&base, &result, usize::MAX).unwrap().entries,
        expected
    );
    assert!(
        registrations(&result, &result, usize::MAX)
            .unwrap()
            .entries
            .is_empty()
    );
    let repeated = register(&result, &n("Z.x"), &n("Original.x")).unwrap();
    assert_eq!(
        registrations(&base, &repeated, usize::MAX).unwrap().entries,
        expected
    );
    assert_eq!(
        base.len(),
        result.len(),
        "aliases never manufacture declarations"
    );
}

#[test]
fn removed_reordered_or_replaced_inherited_metadata_is_refused() {
    let empty = declarations();
    let base = register(&empty, &n("a"), &n("Original.x")).unwrap();
    let replaced = register(&empty, &n("a"), &n("Other.x")).unwrap();
    assert_eq!(
        registrations(&base, &empty, usize::MAX),
        Err(AliasError::Malformed)
    );
    assert_eq!(
        registrations(&base, &replaced, usize::MAX),
        Err(AliasError::Malformed)
    );
    let same_bytes = raw(&empty, row(&n("a"), &n("Original.x")));
    assert!(
        registrations(&base, &same_bytes, usize::MAX)
            .unwrap()
            .entries
            .is_empty()
    );
    let longer = register(&base, &n("b"), &n("Other.x")).unwrap();
    assert_eq!(
        registrations(&longer, &base, usize::MAX),
        Err(AliasError::Malformed)
    );
}

#[test]
fn malformed_rows_foreign_descriptors_and_unknown_names_are_not_exported() {
    let empty = declarations();
    let mut trailing = row(&n("a"), &n("Original.x"));
    trailing.push(0);
    for bytes in [vec![], MAGIC.to_vec(), trailing, [MAGIC, &[0, 0]].concat()] {
        let invalid = raw(&empty, bytes);
        assert_eq!(
            registrations(&empty, &invalid, usize::MAX),
            Err(AliasError::Malformed)
        );
        assert_eq!(
            registrations(&invalid, &invalid, usize::MAX),
            Err(AliasError::Malformed)
        );
    }
    let unknown = raw(&empty, row(&n("a"), &n("Missing.x")));
    assert_eq!(
        registrations(&empty, &unknown, usize::MAX),
        Err(AliasError::UnknownDeclaration(n("Missing.x")))
    );
    let mut foreign = descriptor();
    foreign.provenance = PayloadProvenance::Opaque;
    assert!(!supports(&foreign));
    assert!(supports(&descriptor()));
    let invalid = empty.register_extension(foreign).unwrap();
    assert_eq!(
        registrations(&empty, &invalid, usize::MAX),
        Err(AliasError::Malformed)
    );
}

#[test]
fn every_export_work_cutoff_is_a_nonanswer_and_a_fresh_retry_is_exact() {
    let base = declarations();
    let result = register(&base, &n("Facade.x"), &n("Original.x")).unwrap();
    let expected = registrations(&base, &result, usize::MAX).unwrap();
    assert!(expected.work > 1 && expected.bytes_examined > 0);
    for stop in 0..expected.work {
        assert_eq!(registrations(&base, &result, stop), Err(AliasError::Limit));
    }
    assert_eq!(
        registrations(&base, &result, expected.work).unwrap(),
        expected
    );
    let oversized = raw(&base, vec![0; MAX_ENTRY_BYTES + 1]);
    assert_eq!(
        registrations(&base, &oversized, usize::MAX),
        Err(AliasError::Limit)
    );
}
