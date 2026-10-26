//! The public capsule doors recheck real declaration graphs, including hostile
//! containers whose object and frame digests have all been recomputed.
#![forbid(unsafe_code)]

use std::collections::BTreeMap;

use fln::capsule::{
    CapsuleError, CapsuleLimits, CapsuleVerification, PINNED_EPOCH, SCHEMA_OLEAN_CAPSULE,
    SealedOleanCapsule, seal_olean_capsule, verify_olean_capsule,
};
use fln::{
    BinderInfo, Budget, ConstantInfo, ConstantVal, ConstructorVal, ContentRoot, DataValue, Engine,
    EpochId, Expr, InductiveVal, KVMap, Level, Name, OleanModuleImport, OleanModuleInput,
    OleanModuleWriteInput, OleanWriteBudget, OleanWriteHeader, Outcome, RecursorRule, RecursorVal,
    TheoremVal,
};
use fln_hash::canon::{CanonReader, CanonWriter, Canonical, DecodeBudget};
use fln_hash::cartridge::{
    CartridgeArchiveV1, CartridgeBuilderV1, CartridgeObjectIdV1, CartridgeObjectKindV1,
    ObjectPortabilityV1, ObjectRequirementV1,
};

fn n(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn limits() -> CapsuleLimits {
    CapsuleLimits::new(4 * 1024 * 1024, Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn complete<T: std::fmt::Debug>(result: Result<Outcome<T>, CapsuleError>) -> T {
    result.unwrap().into_complete().unwrap()
}

fn theorem(name: &str, forged: bool) -> ConstantInfo {
    let proposition = Expr::sort(Level::zero());
    ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: Expr::forall_e(
                n("P"),
                proposition.clone(),
                Expr::forall_e(n("h"), b(0), b(1), BinderInfo::Default),
                BinderInfo::Default,
            ),
        },
        value: Expr::lam(
            n("P"),
            proposition,
            Expr::lam(n("h"), b(0), b(u32::from(forged)), BinderInfo::Default),
            BinderInfo::Default,
        ),
        all: vec![n(name)],
    })
}

fn encoded(constants: &[ConstantInfo], imports: &[&str], module: bool, region: u64) -> Vec<u8> {
    let imports: Vec<_> = imports
        .iter()
        .map(|name| OleanModuleImport {
            module: n(name),
            import_all: false,
            is_exported: true,
            is_meta: false,
        })
        .collect();
    fln::encode_olean_module(
        OleanModuleWriteInput {
            is_module: module,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: region * fln::OLEAN_REGION_ALIGN as u64,
        },
        OleanWriteBudget::default(),
    )
    .unwrap()
    .bytes
}

fn input<'a>(name: &'a Name, artifact: &'a [u8]) -> OleanModuleInput<'a> {
    OleanModuleInput {
        name,
        artifact,
        server_artifact: None,
        private_artifact: None,
    }
}

fn single(options: &KVMap) -> SealedOleanCapsule {
    let bytes = encoded(&[theorem("Main.keep", false)], &[], false, 2);
    complete(seal_olean_capsule(
        &[input(&n("Main"), &bytes)],
        options,
        PINNED_EPOCH,
        limits(),
    ))
}

fn archive(bytes: &[u8]) -> CartridgeArchiveV1 {
    CartridgeArchiveV1::from_canonical_bytes(bytes)
        .into_complete()
        .unwrap()
        .unwrap()
}

fn object_bytes(archive: &CartridgeArchiveV1, id: CartridgeObjectIdV1) -> Vec<u8> {
    archive
        .assemble_object(id, limits().max_expanded_bytes as u64)
        .into_complete()
        .unwrap()
        .unwrap()
        .unwrap()
}

fn prefix() -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_OLEAN_CAPSULE);
    writer.into_bytes()
}

/// Mutate content, then rebuild every content-addressed layer. Module pointers in
/// the receipt follow changed objects, while its expected checking roots do not.
fn reseal(
    original: &CartridgeArchiveV1,
    root: ContentRoot,
    mut change: impl FnMut(CartridgeObjectKindV1, Vec<u8>) -> Vec<u8>,
) -> Vec<u8> {
    let mut builder = CartridgeBuilderV1::new(original.manifest.epoch, root);
    let mut ids = BTreeMap::<CartridgeObjectIdV1, CartridgeObjectIdV1>::new();
    for receipts in [false, true] {
        for object in &original.manifest.objects {
            if (object.kind == CartridgeObjectKindV1::Receipt) != receipts {
                continue;
            }
            let mut bytes = object_bytes(original, object.id);
            if receipts {
                for (old, new) in &ids {
                    if old == new {
                        continue;
                    }
                    let positions: Vec<_> = bytes
                        .windows(32)
                        .enumerate()
                        .filter_map(|(at, bytes)| (bytes == old.digest().0).then_some(at))
                        .collect();
                    assert!(!positions.is_empty());
                    for at in positions {
                        bytes[at..at + 32].copy_from_slice(&new.digest().0);
                    }
                }
            }
            let id = builder.add_object(
                object.kind,
                object.requirement,
                object.portability.clone(),
                change(object.kind, bytes),
            );
            ids.insert(object.id, id);
        }
    }
    for id in &original.manifest.root_receipts {
        builder.add_root_receipt(ids[id]);
    }
    for attachment in &original.manifest.attachments {
        builder.attach(
            ids[&attachment.receipt],
            attachment.role,
            ids[&attachment.object],
        );
    }
    builder.build().unwrap().to_canonical_bytes().unwrap()
}

/// A complete nonrecursive Type inductive, with its generated dependent recursor.
/// The envelope is supplied as untrusted rows; both checkers reconstruct it.
fn unit_inductive() -> Vec<ConstantInfo> {
    let family = n("Base.Unit");
    let constructor = n("Base.Unit.unit");
    let ty = || Expr::const_(family.clone(), vec![]);
    let unit = || Expr::const_(constructor.clone(), vec![]);
    let motive = Expr::forall_e(
        n("t"),
        ty(),
        Expr::sort(Level::param(n("u"))),
        BinderInfo::Default,
    );
    let recursor_type = Expr::forall_e(
        n("motive"),
        motive.clone(),
        Expr::forall_e(
            n("unit"),
            Expr::app(b(0), unit()),
            Expr::forall_e(n("t"), ty(), Expr::app(b(2), b(0)), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let rule = Expr::lam(
        n("motive"),
        motive,
        Expr::lam(
            n("unit"),
            Expr::app(b(0), unit()),
            b(0),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    vec![
        ConstantInfo::Rec(RecursorVal {
            base: ConstantVal {
                name: n("Base.Unit.rec"),
                level_params: vec![n("u")],
                type_: recursor_type,
            },
            all: vec![family.clone()],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: constructor.clone(),
                nfields: 0,
                rhs: rule,
            }],
            k: false,
            is_unsafe: false,
        }),
        ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: constructor.clone(),
                level_params: vec![],
                type_: ty(),
            },
            induct: family.clone(),
            cidx: 0,
            num_params: 0,
            num_fields: 0,
            is_unsafe: false,
        }),
        ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: family.clone(),
                level_params: vec![],
                type_: Expr::sort(Level::one()),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![family],
            ctors: vec![constructor],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
    ]
}

#[test]
fn complete_graph_recomputes_inductive_and_dependent_theorem_admission() {
    let mut declarations = unit_inductive();
    declarations.push(theorem("Base.keep", false));
    let base = encoded(&declarations, &[], false, 2);
    let ConstantInfo::Thm(mut child) = theorem("Main.keep", false) else {
        unreachable!()
    };
    child.value = Expr::const_(n("Base.keep"), vec![]);
    let main = encoded(&[ConstantInfo::Thm(child)], &["Base"], false, 2);
    let names = [n("Base"), n("Main")];
    let modules = [input(&names[1], &main), input(&names[0], &base)];
    let sealed = complete(seal_olean_capsule(
        &modules,
        &KVMap::new(),
        PINNED_EPOCH,
        limits(),
    ));
    assert_eq!(sealed.report.modules, 2);
    assert_eq!(sealed.report.declarations, 5);
    let verified = complete(verify_olean_capsule(&sealed.bytes, limits()));
    assert_eq!(
        verified,
        CapsuleVerification::Semantic(sealed.report.clone())
    );
    let ordinary = Engine::builder()
        .build_empty()
        .check_olean_modules(&modules, &KVMap::new(), limits().check)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        sealed.report.result_logical_root,
        ordinary.result_logical_root
    );
    assert_eq!(ordinary.engine.environment().len(), 5);
    let reversed = complete(seal_olean_capsule(
        &[modules[1], modules[0]],
        &KVMap::new(),
        PINNED_EPOCH,
        limits(),
    ));
    assert_eq!(sealed.bytes, reversed.bytes);
}

#[test]
fn ordered_options_and_duplicates_survive_the_profile_without_normalization() {
    let entries = vec![
        (n("capsule.option"), DataValue::OfNat(1)),
        (n("capsule.option"), DataValue::OfNat(2)),
        (n("capsule.other"), DataValue::OfBool(true)),
    ];
    let options = KVMap::from_entries(entries.clone());
    let sealed = single(&options);
    let container = archive(&sealed.bytes);
    let receipt = object_bytes(&container, container.manifest.root_receipts[0]);
    let mut reader = CanonReader::with_budget(&receipt, DecodeBudget::unlimited());
    reader.expect_schema(SCHEMA_OLEAN_CAPSULE).unwrap();
    reader.u64().unwrap();
    reader.u64().unwrap();
    reader.u8().unwrap();
    reader.u8().unwrap();
    reader.str().unwrap();
    reader.str().unwrap();
    assert_eq!(
        KVMap::read_body(&mut reader).unwrap().entries(),
        entries.as_slice()
    );
    assert_eq!(
        complete(verify_olean_capsule(&sealed.bytes, limits())),
        CapsuleVerification::Semantic(sealed.report.clone())
    );
    let reversed = single(&KVMap::from_entries(entries.into_iter().rev().collect()));
    assert_ne!(
        sealed.report.base_logical_root,
        reversed.report.base_logical_root
    );
    assert_ne!(
        sealed.report.result_logical_root,
        reversed.report.result_logical_root
    );
    assert_ne!(sealed.bytes, reversed.bytes);
}

#[test]
fn fully_resealed_false_proof_reaches_the_checker_and_is_rejected() {
    let sealed = single(&KVMap::new());
    let original = archive(&sealed.bytes);
    let forged = encoded(&[theorem("Main.keep", true)], &[], false, 2);
    let bytes = reseal(
        &original,
        original.manifest.environment_root,
        |kind, bytes| {
            if kind == CartridgeObjectKindV1::Declaration {
                forged.clone()
            } else {
                bytes
            }
        },
    );
    let error = verify_olean_capsule(&bytes, limits()).unwrap_err();
    assert_eq!(error.disposition(), ("kernel-rejection", true, 1));
    assert!(matches!(error, CapsuleError::Check(_)));
    let error = seal_olean_capsule(
        &[input(&n("Main"), &forged)],
        &KVMap::new(),
        PINNED_EPOCH,
        limits(),
    )
    .unwrap_err();
    assert_eq!(error.disposition(), ("kernel-rejection", true, 1));
}

#[test]
fn recomputed_roots_must_match_both_the_receipt_and_the_manifest() {
    let sealed = single(&KVMap::new());
    let original = archive(&sealed.bytes);
    let wrong_manifest = reseal(&original, ContentRoot::new([0x75; 32]), |_, bytes| bytes);
    assert!(matches!(
        verify_olean_capsule(&wrong_manifest, limits()),
        Err(CapsuleError::RootMismatch { .. })
    ));
    let wrong_receipt = reseal(
        &original,
        original.manifest.environment_root,
        |kind, mut bytes| {
            if kind == CartridgeObjectKindV1::Receipt {
                let root = sealed.report.result_logical_root.0.0;
                let positions: Vec<_> = bytes
                    .windows(32)
                    .enumerate()
                    .filter_map(|(i, bytes)| (bytes == root).then_some(i))
                    .collect();
                assert!(!positions.is_empty());
                for at in positions {
                    bytes[at..at + 32].fill(0x76);
                }
            }
            bytes
        },
    );
    assert!(matches!(
        verify_olean_capsule(&wrong_receipt, limits()),
        Err(CapsuleError::RootMismatch { .. })
    ));
}

#[test]
fn missing_imports_and_module_system_companions_cannot_be_sealed() {
    let imports = encoded(&[], &["Missing"], false, 2);
    let error = seal_olean_capsule(
        &[input(&n("Main"), &imports)],
        &KVMap::new(),
        PINNED_EPOCH,
        limits(),
    )
    .unwrap_err();
    assert_eq!(error.disposition(), ("unresolved-imports", false, 1));
    let public = encoded(&[], &[], true, 2);
    let server = encoded(&[], &[], true, 4);
    let private = encoded(&[theorem("Main.hidden", false)], &[], true, 6);
    let name = n("Main");
    for companions in [
        (None, None),
        (Some(server.as_slice()), None),
        (None, Some(private.as_slice())),
    ] {
        let module = OleanModuleInput {
            name: &name,
            artifact: &public,
            server_artifact: companions.0,
            private_artifact: companions.1,
        };
        assert!(
            matches!(seal_olean_capsule(&[module], &KVMap::new(), PINNED_EPOCH, limits()), Err(CapsuleError::Check(error)) if matches!(*error, fln::OleanCheckError::MissingCompanionParts { .. }))
        );
    }
    let module = OleanModuleInput {
        name: &name,
        artifact: &public,
        server_artifact: Some(&server),
        private_artifact: Some(&private),
    };
    let sealed = complete(seal_olean_capsule(
        &[module],
        &KVMap::new(),
        PINNED_EPOCH,
        limits(),
    ));
    assert_eq!(sealed.report.declarations, 1);
    assert_eq!(
        complete(verify_olean_capsule(&sealed.bytes, limits())),
        CapsuleVerification::Semantic(sealed.report)
    );
}

#[test]
fn unknown_profile_version_and_wrong_object_kind_never_downgrade_to_legacy() {
    let sealed = single(&KVMap::new());
    let original = archive(&sealed.bytes);
    let unknown = reseal(
        &original,
        original.manifest.environment_root,
        |kind, mut bytes| {
            if kind == CartridgeObjectKindV1::Receipt {
                let end = prefix().len();
                bytes[end - 2..end].copy_from_slice(&999u16.to_le_bytes());
            }
            bytes
        },
    );
    assert_eq!(
        verify_olean_capsule(&unknown, limits()),
        Err(CapsuleError::UnsupportedProfileVersion { seen: 999 })
    );
    let mut builder = CartridgeBuilderV1::new(PINNED_EPOCH, original.manifest.environment_root);
    builder.add_object(
        CartridgeObjectKindV1::Declaration,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        object_bytes(&original, original.manifest.root_receipts[0]),
    );
    let legacy = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"old receipt".as_slice(),
    );
    builder.add_root_receipt(legacy);
    let disguised = builder.build().unwrap().to_canonical_bytes().unwrap();
    assert!(matches!(
        verify_olean_capsule(&disguised, limits()),
        Err(CapsuleError::MalformedProfile(_))
    ));
}

#[test]
fn unsupported_epoch_mode_and_pin_are_explicit_refusals() {
    let sealed = single(&KVMap::new());
    let original = archive(&sealed.bytes);
    for which in 0..3 {
        let bytes = reseal(
            &original,
            original.manifest.environment_root,
            |kind, mut bytes| {
                if kind == CartridgeObjectKindV1::Receipt {
                    let header = prefix().len();
                    match which {
                        0 => bytes[header..header + 8].copy_from_slice(&99u64.to_le_bytes()),
                        1 => bytes[header + 16] = fln::Mode::Faithful.tag(),
                        _ => {
                            let at = bytes
                                .windows(fln::OLEAN_PIN_COMMIT.len())
                                .position(|bytes| bytes == fln::OLEAN_PIN_COMMIT.as_bytes())
                                .unwrap();
                            bytes[at] = b'X';
                        }
                    }
                }
                bytes
            },
        );
        let error = verify_olean_capsule(&bytes, limits()).unwrap_err();
        assert!(!error.disposition().1);
        assert!(matches!(
            error,
            CapsuleError::UnsupportedEpoch { .. } | CapsuleError::MalformedProfile(_)
        ));
    }
    let raw = encoded(&[], &[], false, 2);
    assert!(matches!(
        seal_olean_capsule(
            &[input(&n("Main"), &raw)],
            &KVMap::new(),
            EpochId::new(99),
            limits()
        ),
        Err(CapsuleError::UnsupportedEpoch { .. })
    ));
}

#[test]
fn exact_transport_profile_and_expansion_limits_are_inclusive() {
    let sealed = single(&KVMap::new());
    let original = archive(&sealed.bytes);
    let profile = original
        .manifest
        .object(original.manifest.root_receipts[0])
        .unwrap()
        .len as usize;
    let expanded = original
        .manifest
        .objects
        .iter()
        .map(|object| object.len as usize)
        .sum();
    let mut exact = limits();
    exact.max_archive_bytes = sealed.bytes.len();
    exact.max_profile_bytes = profile;
    exact.max_expanded_bytes = expanded;
    assert!(matches!(
        complete(verify_olean_capsule(&sealed.bytes, exact)),
        CapsuleVerification::Semantic(_)
    ));
    for which in 0..4 {
        let mut short = exact;
        match which {
            0 => short.max_archive_bytes -= 1,
            1 => short.max_profile_bytes -= 1,
            2 => short.max_expanded_bytes -= 1,
            _ => short.max_decode_nodes = 0,
        }
        assert!(matches!(
            verify_olean_capsule(&sealed.bytes, short).unwrap(),
            Outcome::Inconclusive(_)
        ));
    }
    let bytes = encoded(&[theorem("Main.keep", false)], &[], false, 2);
    let name = n("Main");
    let modules = [input(&name, &bytes)];
    assert_eq!(
        complete(seal_olean_capsule(
            &modules,
            &KVMap::new(),
            PINNED_EPOCH,
            exact
        ))
        .bytes,
        sealed.bytes
    );
    for which in 0..3 {
        let mut short = exact;
        match which {
            0 => short.max_archive_bytes = 1,
            1 => short.max_profile_bytes = 1,
            _ => short.max_expanded_bytes = 1,
        }
        assert!(matches!(
            seal_olean_capsule(&modules, &KVMap::new(), PINNED_EPOCH, short).unwrap(),
            Outcome::Inconclusive(_)
        ));
    }
}

#[test]
fn shared_chunks_cannot_hide_excessive_aggregate_object_expansion() {
    let sealed = single(&KVMap::new());
    let original = archive(&sealed.bytes);
    let mut builder = CartridgeBuilderV1::new(PINNED_EPOCH, original.manifest.environment_root)
        .with_chunk_size(1024)
        .unwrap();
    for object in &original.manifest.objects {
        let id = builder.add_object(
            object.kind,
            object.requirement,
            object.portability.clone(),
            object_bytes(&original, object.id),
        );
        assert_eq!(id, object.id);
    }
    builder.add_root_receipt(original.manifest.root_receipts[0]);
    for suffix in 0..100u8 {
        let mut bytes = vec![0; 16 * 1024];
        bytes.push(suffix);
        builder.add_object(
            CartridgeObjectKindV1::Fixture,
            ObjectRequirementV1::Optional,
            ObjectPortabilityV1::Portable,
            bytes,
        );
    }
    let expanded = builder.build().unwrap();
    let bytes = expanded.to_canonical_bytes().unwrap();
    let total: usize = expanded
        .manifest
        .objects
        .iter()
        .map(|object| object.len as usize)
        .sum();
    assert!(bytes.len() < total / 2);
    let mut allowed = limits();
    allowed.max_expanded_bytes = total;
    assert!(matches!(
        complete(verify_olean_capsule(&bytes, allowed)),
        CapsuleVerification::Semantic(_)
    ));
    allowed.max_expanded_bytes -= 1;
    assert!(matches!(
        verify_olean_capsule(&bytes, allowed).unwrap(),
        Outcome::Inconclusive(_)
    ));
}

#[test]
fn exhausted_checking_fuel_never_becomes_an_integrity_success_or_theorem_rejection() {
    let sealed = single(&KVMap::new());
    let mut stopped = limits();
    stopped.check.admission.kernel.steps = 0;
    match verify_olean_capsule(&sealed.bytes, stopped) {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => {
            let (_, authority, code) = error.disposition();
            assert!(!authority);
            assert_eq!(code, 3);
        }
        result => panic!("exhausted checker returned a domain answer: {result:?}"),
    }
}

#[test]
fn resealed_profiles_cannot_remove_a_dependency_or_hide_private_companions() {
    fn row_name(name: &Name) -> Vec<u8> {
        let mut writer = CanonWriter::new();
        name.write_body(&mut writer);
        writer.into_bytes()
    }
    fn unique_at(bytes: &[u8], needle: &[u8]) -> usize {
        let matches: Vec<_> = bytes
            .windows(needle.len())
            .enumerate()
            .filter_map(|(at, bytes)| (bytes == needle).then_some(at))
            .collect();
        assert_eq!(matches.len(), 1);
        matches[0]
    }
    fn shrink(original: &CartridgeArchiveV1, artifact: &[u8], receipt: Vec<u8>) -> Vec<u8> {
        let mut builder = CartridgeBuilderV1::new(PINNED_EPOCH, original.manifest.environment_root);
        let id = builder.add_object(
            CartridgeObjectKindV1::Declaration,
            ObjectRequirementV1::Required,
            ObjectPortabilityV1::EpochBound,
            artifact,
        );
        assert!(original.manifest.object(id).is_some());
        let id = builder.add_object(
            CartridgeObjectKindV1::Receipt,
            ObjectRequirementV1::Required,
            ObjectPortabilityV1::EpochBound,
            receipt,
        );
        builder.add_root_receipt(id);
        builder.build().unwrap().to_canonical_bytes().unwrap()
    }

    let base = encoded(&[theorem("Base.keep", false)], &[], false, 2);
    let ConstantInfo::Thm(mut child) = theorem("Main.keep", false) else {
        unreachable!()
    };
    child.value = Expr::const_(n("Base.keep"), vec![]);
    let main = encoded(&[ConstantInfo::Thm(child)], &["Base"], false, 2);
    let sealed = complete(seal_olean_capsule(
        &[input(&n("Base"), &base), input(&n("Main"), &main)],
        &KVMap::new(),
        PINNED_EPOCH,
        limits(),
    ));
    let original = archive(&sealed.bytes);
    let mut receipt = object_bytes(&original, original.manifest.root_receipts[0]);
    let name = row_name(&n("Base"));
    let at = unique_at(&receipt, &name);
    assert_eq!(&receipt[at - 8..at], 2u64.to_le_bytes());
    receipt[at - 8..at].copy_from_slice(&1u64.to_le_bytes());
    // A companion-free row consists of name, public id, false, two roots and count.
    assert_eq!(receipt[at + name.len() + 32], 0);
    drop(receipt.drain(at..at + name.len() + 32 + 1 + 64 + 8));
    let missing_dependency = shrink(&original, &main, receipt);
    let error = verify_olean_capsule(&missing_dependency, limits()).unwrap_err();
    assert_eq!(error.disposition(), ("unresolved-imports", false, 1));

    let public = encoded(&[], &[], true, 2);
    let server = encoded(&[], &[], true, 4);
    let private = encoded(&[theorem("Main.private", false)], &[], true, 6);
    let name = n("Main");
    let module = OleanModuleInput {
        name: &name,
        artifact: &public,
        server_artifact: Some(&server),
        private_artifact: Some(&private),
    };
    let sealed = complete(seal_olean_capsule(
        &[module],
        &KVMap::new(),
        PINNED_EPOCH,
        limits(),
    ));
    let original = archive(&sealed.bytes);
    let mut receipt = object_bytes(&original, original.manifest.root_receipts[0]);
    let name = row_name(&name);
    let flag = unique_at(&receipt, &name) + name.len() + 32;
    assert_eq!(receipt[flag], 1);
    receipt[flag] = 0;
    drop(receipt.drain(flag + 1..flag + 65));
    let missing_companions = shrink(&original, &public, receipt);
    assert!(
        matches!(verify_olean_capsule(&missing_companions, limits()),
        Err(CapsuleError::Check(error)) if matches!(*error, fln::OleanCheckError::MissingCompanionParts { .. }))
    );
}
