//! Real sealed `.flnpack` capsule verification tests for `fln-wasm`.
//!
//! Every fixture is a genuine pinned-format `.olean` module sealed into a real
//! `fln.capsule.olean-replay/1` archive (`CartridgeArchiveV1`) — no mocks.
#![forbid(unsafe_code)]

use fln::capsule::{CapsuleLimits, PINNED_EPOCH, SCHEMA_OLEAN_CAPSULE, seal_olean_capsule};
use fln::{
    AxiomVal, BinderInfo, Budget, ConstantInfo, ConstantVal, ConstructorVal, ContentRoot,
    DataValue, DefinitionSafety, DefinitionVal, Expr, InductiveVal, KVMap, Level, Mode, Name,
    OLEAN_ACCEPTED_VERSIONS, OLEAN_PIN_COMMIT, OLEAN_PIN_TAG, OLEAN_REGION_ALIGN,
    OleanModuleImport, OleanModuleInput, OleanModuleWriteInput, OleanWriteBudget, OleanWriteHeader,
    Outcome, QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints,
    ReproducibilityProfile, TheoremVal, encode_olean_module,
};
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::cartridge::{
    CartridgeBuilderV1, CartridgeObjectKindV1, ObjectPortabilityV1, ObjectRequirementV1,
};
use fln_hash::domain::Digest;
use fln_wasm::{
    CapsuleError, Verdict, VerificationBudget, verify_flnpack_capsule, verify_olean_parts,
};

fn zero_root() -> ContentRoot {
    ContentRoot::new([0u8; 32])
}

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn identity_theorem(name: &str, binder: &str, style: BinderInfo) -> ConstantInfo {
    let type_ = Expr::forall_e(
        n(binder),
        Expr::sort(Level::zero()),
        Expr::forall_e(n("proof"), b(0), b(1), BinderInfo::Default),
        style,
    );
    let value = Expr::lam(
        n(binder),
        Expr::sort(Level::zero()),
        Expr::lam(n("proof"), b(0), b(0), BinderInfo::Default),
        style,
    );
    ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        value,
        all: vec![n(name)],
    })
}

fn alternate_proof(mut info: ConstantInfo) -> ConstantInfo {
    let ConstantInfo::Thm(theorem) = &mut info else {
        panic!("theorem fixture");
    };
    theorem.value = Expr::app(
        Expr::lam(
            n("saved"),
            theorem.base.type_.clone(),
            b(0),
            BinderInfo::Default,
        ),
        theorem.value.clone(),
    );
    info
}

fn erased_theorem(info: &ConstantInfo, is_unsafe: bool) -> ConstantInfo {
    let ConstantInfo::Thm(theorem) = info else {
        panic!("theorem fixture");
    };
    ConstantInfo::Axiom(AxiomVal {
        base: theorem.base.clone(),
        is_unsafe,
    })
}

fn proof_definition(name: &str, type_: Expr, value: Expr) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

fn generic_theorem(name: &str, forged: bool) -> ConstantInfo {
    let binders = [
        (
            n("A"),
            Expr::sort(Level::param(n("u"))),
            BinderInfo::Implicit,
        ),
        (
            n("P"),
            Expr::forall_e(n("x"), b(0), Expr::sort(Level::zero()), BinderInfo::Default),
            BinderInfo::Default,
        ),
        (n("a"), b(1), BinderInfo::Default),
        (n("h"), Expr::app(b(1), b(0)), BinderInfo::Default),
    ];
    let mut type_ = Expr::app(b(2), b(1));
    let mut value = b(u32::from(forged));
    for (binder_name, domain, style) in binders.into_iter().rev() {
        type_ = Expr::forall_e(binder_name.clone(), domain.clone(), type_, style);
        value = Expr::lam(binder_name, domain, value, style);
    }
    ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![n("u")],
            type_,
        },
        value,
        all: vec![n(name)],
    })
}

fn simple_axiom(name: &str) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        },
        is_unsafe: false,
    })
}

/// Concrete ill-typed definition (`def bad : Prop := Prop`, i.e. inferred `Type` vs expected `Prop`)
/// whose head mismatch is decided directly by `fln-checker` as `Rejected`.
fn ill_typed_def(name: &str) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        },
        value: Expr::sort(Level::zero()),
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

fn proposition_alias(name: &str, target: &str) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        },
        value: Expr::const_(n(target), vec![]),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

fn recursive_definition(
    name: &str,
    target: &str,
    safety: DefinitionSafety,
    members: &[&str],
) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: Expr::const_(n("Base.P"), vec![]),
        },
        value: Expr::const_(n(target), vec![]),
        hints: ReducibilityHints::Regular(1),
        safety,
        all: members.iter().map(|name| n(name)).collect(),
    })
}

fn app(function: Expr, arguments: &[Expr]) -> Expr {
    arguments.iter().cloned().fold(function, Expr::app)
}

fn pi(binders: &[(&str, BinderInfo, Expr)], body: Expr) -> Expr {
    binders
        .iter()
        .rev()
        .fold(body, |body, (name, style, type_)| {
            Expr::forall_e(n(name), type_.clone(), body, *style)
        })
}

fn lam(binders: &[(&str, BinderInfo, Expr)], body: Expr) -> Expr {
    binders
        .iter()
        .rev()
        .fold(body, |body, (name, style, type_)| {
            Expr::lam(n(name), type_.clone(), body, *style)
        })
}

/// Complete single-constructor data family, including its dependent recursor.
fn unit_inductive(name: &str) -> Vec<ConstantInfo> {
    use BinderInfo::{Default, Implicit};
    let family = n(name);
    let constructor = n(&format!("{name}.unit"));
    let ty = || Expr::const_(family.clone(), vec![]);
    let unit = || Expr::const_(constructor.clone(), vec![]);
    let motive = pi(&[("t", Default, ty())], Expr::sort(Level::param(n("u"))));
    let minor = Expr::app(b(0), unit());
    vec![
        ConstantInfo::Rec(RecursorVal {
            base: ConstantVal {
                name: n(&format!("{name}.rec")),
                level_params: vec![n("u")],
                type_: pi(
                    &[
                        ("motive", Implicit, motive.clone()),
                        ("unit", Default, minor.clone()),
                        ("t", Default, ty()),
                    ],
                    Expr::app(b(2), b(0)),
                ),
            },
            all: vec![family.clone()],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: constructor.clone(),
                nfields: 0,
                rhs: lam(
                    &[("motive", Default, motive), ("unit", Default, minor)],
                    b(0),
                ),
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

/// Pinned Eq family and exact primitive quotient declarations, all as untrusted
/// rows. The native sealer and the independent checker reconstruct both units.
fn equality_and_quotient() -> Vec<ConstantInfo> {
    use BinderInfo::{Default, Implicit};
    let u = Level::param(n("u"));
    let u1 = Level::param(n("u_1"));
    let v = Level::param(n("v"));
    let prop = || Expr::sort(Level::zero());
    let eq = |alpha: Expr, left: Expr, right: Expr| {
        app(
            Expr::const_(n("Eq"), vec![u1.clone()]),
            &[alpha, left, right],
        )
    };
    let motive = pi(
        &[("b", Default, b(1)), ("h", Default, eq(b(2), b(1), b(0)))],
        Expr::sort(u.clone()),
    );
    let minor = app(
        b(0),
        &[
            b(1),
            app(Expr::const_(n("Eq.refl"), vec![u1.clone()]), &[b(2), b(1)]),
        ],
    );
    let mut rows = vec![
        ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: n("Eq"),
                level_params: vec![n("u_1")],
                type_: pi(
                    &[
                        ("α", Implicit, Expr::sort(u1.clone())),
                        ("a", Default, b(0)),
                        ("b", Default, b(1)),
                    ],
                    prop(),
                ),
            },
            num_params: 2,
            num_indices: 1,
            all: vec![n("Eq")],
            ctors: vec![n("Eq.refl")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
        ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: n("Eq.refl"),
                level_params: vec![n("u_1")],
                type_: pi(
                    &[
                        ("α", Implicit, Expr::sort(u1.clone())),
                        ("a", Default, b(0)),
                    ],
                    eq(b(1), b(0), b(0)),
                ),
            },
            induct: n("Eq"),
            cidx: 0,
            num_params: 2,
            num_fields: 0,
            is_unsafe: false,
        }),
        ConstantInfo::Rec(RecursorVal {
            base: ConstantVal {
                name: n("Eq.rec"),
                level_params: vec![n("u"), n("u_1")],
                type_: pi(
                    &[
                        ("α", Implicit, Expr::sort(u1.clone())),
                        ("a", Implicit, b(0)),
                        ("motive", Implicit, motive.clone()),
                        ("minor", Default, minor.clone()),
                        ("b", Implicit, b(3)),
                        ("t", Default, eq(b(4), b(3), b(0))),
                    ],
                    app(b(3), &[b(1), b(0)]),
                ),
            },
            all: vec![n("Eq")],
            num_params: 2,
            num_indices: 1,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: n("Eq.refl"),
                nfields: 0,
                rhs: lam(
                    &[
                        ("α", Implicit, Expr::sort(u1)),
                        ("a", Default, b(0)),
                        ("motive", Default, motive),
                        ("minor", Default, minor),
                    ],
                    b(0),
                ),
            }],
            k: true,
            is_unsafe: false,
        }),
    ];
    let relation = || pi(&[("a", Default, b(0)), ("b", Default, b(1))], prop());
    let quot = |alpha: Expr, relation: Expr| {
        app(Expr::const_(n("Quot"), vec![u.clone()]), &[alpha, relation])
    };
    let respects = pi(
        &[
            ("a", Default, b(3)),
            ("b", Default, b(4)),
            ("h", Default, app(b(4), &[b(1), b(0)])),
        ],
        app(
            Expr::const_(n("Eq"), vec![v.clone()]),
            &[b(4), Expr::app(b(3), b(2)), Expr::app(b(3), b(1))],
        ),
    );
    let induction_minor = pi(
        &[("a", Default, b(2))],
        Expr::app(
            b(1),
            app(
                Expr::const_(n("Quot.mk"), vec![u.clone()]),
                &[b(3), b(2), b(0)],
            ),
        ),
    );
    for (name, levels, kind, type_) in [
        (
            "Quot",
            vec![n("u")],
            QuotKind::Type,
            pi(
                &[
                    ("α", Implicit, Expr::sort(u.clone())),
                    ("r", Default, relation()),
                ],
                Expr::sort(u.clone()),
            ),
        ),
        (
            "Quot.mk",
            vec![n("u")],
            QuotKind::Ctor,
            pi(
                &[
                    ("α", Implicit, Expr::sort(u.clone())),
                    ("r", Default, relation()),
                    ("a", Default, b(1)),
                ],
                quot(b(2), b(1)),
            ),
        ),
        (
            "Quot.lift",
            vec![n("u"), n("v")],
            QuotKind::Lift,
            pi(
                &[
                    ("α", Implicit, Expr::sort(u.clone())),
                    ("r", Implicit, relation()),
                    ("β", Implicit, Expr::sort(v)),
                    ("f", Default, pi(&[("a", Default, b(2))], b(1))),
                    ("respects", Default, respects),
                    ("q", Default, quot(b(4), b(3))),
                ],
                b(3),
            ),
        ),
        (
            "Quot.ind",
            vec![n("u")],
            QuotKind::Ind,
            pi(
                &[
                    ("α", Implicit, Expr::sort(u.clone())),
                    ("r", Implicit, relation()),
                    (
                        "β",
                        Implicit,
                        pi(&[("q", Default, quot(b(1), b(0)))], prop()),
                    ),
                    ("mk", Default, induction_minor),
                    ("q", Default, quot(b(3), b(2))),
                ],
                Expr::app(b(2), b(0)),
            ),
        ),
    ] {
        rows.push(ConstantInfo::Quot(QuotVal {
            base: ConstantVal {
                name: n(name),
                level_params: levels,
                type_,
            },
            kind,
        }));
    }
    rows
}

fn encode_module(constants: &[ConstantInfo], imports: &[&str], region: u64) -> Vec<u8> {
    encode_module_kind(constants, imports, region, false)
}

fn encode_module_kind(
    constants: &[ConstantInfo],
    imports: &[&str],
    region: u64,
    is_module: bool,
) -> Vec<u8> {
    let imports: Vec<_> = imports
        .iter()
        .map(|name| OleanModuleImport {
            module: n(name),
            import_all: false,
            is_exported: true,
            is_meta: false,
        })
        .collect();
    encode_olean_module(
        OleanModuleWriteInput {
            is_module,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: OLEAN_PIN_TAG.trim_start_matches('v'),
            githash: OLEAN_PIN_COMMIT,
            base_addr: region * OLEAN_REGION_ALIGN as u64,
        },
        OleanWriteBudget::default(),
    )
    .expect("encode olean")
    .bytes
}

fn seal_two_module_capsule() -> Vec<u8> {
    let base_bytes = encode_module(
        &[simple_axiom("Base.P"), generic_theorem("Base.ok", false)],
        &[],
        2,
    );
    let top_bytes = encode_module(&[generic_theorem("Top.ok", false)], &["Base"], 2);
    let base_name = n("Base");
    let top_name = n("Top");
    let inputs = [
        OleanModuleInput {
            name: &base_name,
            artifact: &base_bytes,
            server_artifact: None,
            private_artifact: None,
        },
        OleanModuleInput {
            name: &top_name,
            artifact: &top_bytes,
            server_artifact: None,
            private_artifact: None,
        },
    ];
    let limits = CapsuleLimits::new(16 * 1024 * 1024, Budget::for_stack_bytes(2 * 1024 * 1024));
    match seal_olean_capsule(&inputs, &KVMap::new(), PINNED_EPOCH, limits).expect("seal capsule") {
        Outcome::Complete(sealed) => sealed.bytes,
        other => panic!("expected Complete sealed capsule, got {other:?}"),
    }
}

fn seal_modules(modules: &[(&str, &[u8])]) -> Vec<u8> {
    let names: Vec<_> = modules.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = modules
        .iter()
        .zip(&names)
        .map(|((_, artifact), name)| OleanModuleInput {
            name,
            artifact,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    let limits = CapsuleLimits::new(16 * 1024 * 1024, Budget::for_stack_bytes(2 * 1024 * 1024));
    match seal_olean_capsule(&inputs, &KVMap::new(), PINNED_EPOCH, limits).expect("seal modules") {
        Outcome::Complete(sealed) => sealed.bytes,
        other => panic!("expected sealed modules, got {other:?}"),
    }
}

/// Valid transport around deliberately untrusted module claims. Such a profile
/// cannot be made by `seal_olean_capsule`, which checks its closure first.
fn untrusted_module_capsule(
    modules: &[(&str, &[u8], u64)],
    requirement: ObjectRequirementV1,
) -> Vec<u8> {
    let mut builder = CartridgeBuilderV1::new(PINNED_EPOCH, zero_root());
    let mut modules = modules.to_vec();
    modules.sort_by_key(|(name, _, _)| n(name));
    let objects: Vec<_> = modules
        .iter()
        .map(|(_, bytes, _)| {
            builder.add_object(
                CartridgeObjectKindV1::Declaration,
                requirement,
                ObjectPortabilityV1::EpochBound,
                bytes.to_vec(),
            )
        })
        .collect();
    let mut profile = CanonWriter::new();
    profile.schema(SCHEMA_OLEAN_CAPSULE);
    profile.u64(PINNED_EPOCH.get() as u64);
    profile.u64((PINNED_EPOCH.get() >> 64) as u64);
    profile.u8(Mode::Sound.tag());
    profile.u8(ReproducibilityProfile::Standard.tag());
    profile.str(OLEAN_PIN_TAG);
    profile.str(OLEAN_PIN_COMMIT);
    KVMap::new().write_body(&mut profile);
    profile.digest(&Digest([0; 32]));
    profile.digest(&Digest([0; 32]));
    profile.u64(modules.len() as u64);
    for ((name, _, declarations), object) in modules.iter().zip(objects) {
        n(name).write_body(&mut profile);
        profile.digest(&object.digest());
        profile.bool(false);
        profile.digest(&Digest([0; 32]));
        profile.digest(&Digest([0; 32]));
        profile.u64(*declarations);
    }
    let receipt = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        profile.into_bytes(),
    );
    builder.add_root_receipt(receipt);
    builder
        .build()
        .expect("valid transport")
        .to_canonical_bytes()
        .expect("encode transport")
}

#[test]
fn valid_sealed_multi_module_capsule_is_accepted() {
    let bytes = seal_two_module_capsule();
    let verdict = verify_flnpack_capsule(&bytes, VerificationBudget::default());
    assert_eq!(verdict, Verdict::Accepted { declarations: 3 });
}

#[test]
fn capsule_dependency_order_is_independent_of_module_name_order() {
    let base = encode_module(&[simple_axiom("ZBase.P")], &[], 2);
    let middle = encode_module(&[proposition_alias("Middle.P", "ZBase.P")], &["ZBase"], 2);
    let top = encode_module(&[proposition_alias("ATop.P", "Middle.P")], &["Middle"], 2);
    let bytes = seal_modules(&[("ATop", &top), ("Middle", &middle), ("ZBase", &base)]);
    assert_eq!(
        verify_flnpack_capsule(&bytes, VerificationBudget::default()),
        Verdict::Accepted { declarations: 3 }
    );
}

#[test]
fn declaration_storage_permutations_replay_the_same_valid_dependencies() {
    let rows = [
        proposition_alias("Alias.first", "ZBase.P"),
        proposition_alias("Alias.second", "Alias.first"),
        simple_axiom("ZBase.P"),
    ];
    for permutation in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let constants: Vec<_> = permutation
            .iter()
            .map(|&index| rows[index].clone())
            .collect();
        let artifact = encode_module(&constants, &[], 2);
        let capsule = seal_modules(&[("Unordered", &artifact)]);
        assert_eq!(
            verify_flnpack_capsule(&capsule, VerificationBudget::default()),
            Verdict::Accepted { declarations: 3 },
            "native-sealed storage permutation {permutation:?}"
        );
        assert_eq!(
            verify_olean_parts(&[&artifact], VerificationBudget::default()),
            Verdict::Accepted { declarations: 3 }
        );
    }
}

#[test]
fn imported_identical_declarations_reuse_checked_authority_including_family_subsets() {
    let proposition = simple_axiom("Base.P");
    let base = encode_module(std::slice::from_ref(&proposition), &[], 2);
    let top = encode_module(
        &[proposition, proposition_alias("Top.P", "Base.P")],
        &["Base"],
        4,
    );
    let capsule = seal_modules(&[("Base", &base), ("Top", &top)]);
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Accepted { declarations: 3 }
    );

    let family = unit_inductive("Base.Unit");
    let base = encode_module(&family, &[], 2);
    // This row has no local inductive or recursor companion. Its entire family
    // was already checked in the imported module, exactly as in native replay.
    let top = encode_module(&[family[1].clone()], &["Base"], 4);
    let capsule = seal_modules(&[("Base", &base), ("Top", &top)]);
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Accepted { declarations: 4 }
    );
}

#[test]
fn native_sealed_theorem_repeats_recheck_distinct_proofs_and_binder_styles() {
    let original = identity_theorem("Shared.id", "P", BinderInfo::Default);
    for repeated in [
        alternate_proof(original.clone()),
        identity_theorem("Shared.id", "Q", BinderInfo::Implicit),
    ] {
        for imported in [false, true] {
            let base = encode_module(std::slice::from_ref(&original), &[], 2);
            let imports = if imported { vec!["Base"] } else { vec![] };
            let top = encode_module(std::slice::from_ref(&repeated), &imports, 4);
            let capsule = seal_modules(&[("Base", &base), ("Top", &top)]);
            assert_eq!(
                verify_flnpack_capsule(&capsule, VerificationBudget::default()),
                Verdict::Accepted { declarations: 2 },
                "imported={imported}"
            );
        }
    }

    // Universe parameters and shared universe nodes use the independent
    // structural comparison too, rather than a primary Expr equality answer.
    let original = generic_theorem("Shared.generic", false);
    let base = encode_module(std::slice::from_ref(&original), &[], 2);
    let top = encode_module(&[alternate_proof(original)], &["Base"], 4);
    let capsule = seal_modules(&[("Base", &base), ("Top", &top)]);
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Accepted { declarations: 2 }
    );
}

#[test]
fn native_sealed_erased_axiom_repeats_preserve_theorem_checks() {
    let theorem = identity_theorem("Shared.id", "P", BinderInfo::Default);
    let erased = erased_theorem(&theorem, false);
    for (first, repeated) in [(&theorem, &erased), (&erased, &theorem)] {
        let base = encode_module(std::slice::from_ref(first), &[], 2);
        let top = encode_module(std::slice::from_ref(repeated), &["Base"], 4);
        let capsule = seal_modules(&[("Base", &base), ("Top", &top)]);
        assert_eq!(
            verify_flnpack_capsule(&capsule, VerificationBudget::default()),
            Verdict::Accepted { declarations: 2 }
        );
    }
}

#[test]
fn repeated_theorem_helpers_use_old_imports_and_scratch_names_never_escape() {
    let original = identity_theorem("Shared.id", "P", BinderInfo::Default);
    let ConstantInfo::Thm(mut repeated) = original.clone() else {
        panic!("theorem fixture");
    };
    let helper = proof_definition(
        "Top.helper",
        repeated.base.type_.clone(),
        Expr::const_(n("Shared.id"), vec![]),
    );
    repeated.value = Expr::const_(n("Top.helper"), vec![]);
    let collision = simple_axiom("Shared.id._fln_subsumed_repeat");
    let base = encode_module(&[original], &[], 2);
    let top = encode_module(
        &[ConstantInfo::Thm(repeated.clone()), collision, helper],
        &["Base"],
        4,
    );
    let capsule = seal_modules(&[("Base", &base), ("Top", &top)]);
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Accepted { declarations: 4 },
        "the new proof depends on a local helper which uses the old import"
    );

    let scratch = Name::num(Name::str(n("Shared.id"), "_fln_subsumed_repeat"), 1);
    let leak = encode_module(
        &[proof_definition(
            "Leak.use",
            repeated.base.type_,
            Expr::const_(scratch, vec![]),
        )],
        &["Top"],
        6,
    );
    let capsule = untrusted_module_capsule(
        &[("Base", &base, 1), ("Top", &top, 3), ("Leak", &leak, 1)],
        ObjectRequirementV1::Required,
    );
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Rejected {
            first_rejection: n("Leak.use"),
            rejection_count: 1
        },
        "the collision-free checking identity must not enter an import snapshot"
    );
}

#[test]
fn forged_theorem_repeats_are_rejected_in_each_actual_import_closure() {
    let original = identity_theorem("Shared.id", "P", BinderInfo::Default);
    let ConstantInfo::Thm(mut forged) = original.clone() else {
        panic!("theorem fixture");
    };
    // This closed, well-formed term applies Prop as a function. Inference
    // refuses it with FunctionExpected, independently of the repeat signature.
    forged.value = Expr::app(Expr::sort(Level::zero()), Expr::sort(Level::zero()));
    let base = encode_module(std::slice::from_ref(&original), &[], 2);
    for imported in [false, true] {
        let imports = if imported { vec!["Base"] } else { vec![] };
        let top = encode_module(&[ConstantInfo::Thm(forged.clone())], &imports, 4);
        let capsule = untrusted_module_capsule(
            &[("Base", &base, 1), ("Top", &top, 1)],
            ObjectRequirementV1::Required,
        );
        assert_eq!(
            verify_flnpack_capsule(&capsule, VerificationBudget::default()),
            Verdict::Rejected {
                first_rejection: n("Shared.id"),
                rejection_count: 1
            },
            "imported={imported}; report the original name, never its scratch name"
        );

        // A loose bound variable is a different checker contract: malformed
        // inference input currently yields an internal fault, never rejection.
        let mut malformed = forged.clone();
        malformed.value = b(0);
        let top = encode_module(&[ConstantInfo::Thm(malformed)], &imports, 4);
        let capsule = untrusted_module_capsule(
            &[("Base", &base, 1), ("Top", &top, 1)],
            ObjectRequirementV1::Required,
        );
        assert!(matches!(
            verify_flnpack_capsule(&capsule, VerificationBudget::default()),
            Verdict::Inconclusive { verified_so_far: 1, reason }
                if reason.contains("LooseBoundVariables")
        ));
    }

    let ConstantInfo::Thm(mut borrowed) = original.clone() else {
        panic!("theorem fixture");
    };
    let hidden = proof_definition(
        "Base.hidden",
        borrowed.base.type_.clone(),
        borrowed.value.clone(),
    );
    borrowed.value = Expr::const_(n("Base.hidden"), vec![]);
    let base = encode_module(&[original, hidden], &[], 2);
    let top = encode_module(&[ConstantInfo::Thm(borrowed)], &[], 4);
    let capsule = untrusted_module_capsule(
        &[("Base", &base, 2), ("Top", &top, 1)],
        ObjectRequirementV1::Required,
    );
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Rejected {
            first_rejection: n("Shared.id"),
            rejection_count: 1
        },
        "compatible global signatures do not import a sibling's proof dependencies"
    );
}

#[test]
fn nonidentical_repeat_headers_preserve_metadata_safety_and_definition_conflicts() {
    let original = identity_theorem("Shared.id", "P", BinderInfo::Default);
    let ConstantInfo::Thm(theorem) = &original else {
        panic!("theorem fixture");
    };
    let mut cases = Vec::new();
    let mut changed = theorem.clone();
    changed.base.type_ = Expr::sort(Level::zero());
    cases.push((original.clone(), ConstantInfo::Thm(changed), "statement"));
    let mut changed = theorem.clone();
    changed.base.level_params.push(n("u"));
    cases.push((
        original.clone(),
        ConstantInfo::Thm(changed),
        "level parameters",
    ));
    let mut changed = theorem.clone();
    changed.all = vec![n("Other.theorem")];
    cases.push((
        original.clone(),
        ConstantInfo::Thm(changed),
        "mutual metadata",
    ));
    cases.push((
        original.clone(),
        erased_theorem(&original, true),
        "unsafe axiom",
    ));

    let mut left = theorem.clone();
    left.base.type_ = Expr::let_e(
        n("unused"),
        Expr::sort(Level::zero()),
        theorem.base.type_.clone(),
        theorem.base.type_.clone(),
        false,
    );
    let mut right = theorem.clone();
    right.base.type_ = Expr::let_e(
        n("unused"),
        Expr::sort(Level::zero()),
        theorem.base.type_.clone(),
        theorem.base.type_.clone(),
        true,
    );
    cases.push((
        ConstantInfo::Thm(left),
        ConstantInfo::Thm(right),
        "let non-dependence",
    ));

    let mut left = theorem.clone();
    let mut right = theorem.clone();
    let mut first_metadata = KVMap::new();
    first_metadata.insert(n("repeat.flag"), DataValue::OfBool(false));
    let mut second_metadata = KVMap::new();
    second_metadata.insert(n("repeat.flag"), DataValue::OfBool(true));
    left.base.type_ = Expr::mdata(first_metadata, theorem.base.type_.clone());
    right.base.type_ = Expr::mdata(second_metadata, theorem.base.type_.clone());
    cases.push((
        ConstantInfo::Thm(left),
        ConstantInfo::Thm(right),
        "statement metadata",
    ));

    let ConstantInfo::Thm(alternate) = alternate_proof(original.clone()) else {
        panic!("theorem fixture");
    };
    cases.push((
        proof_definition(
            "Shared.id",
            theorem.base.type_.clone(),
            theorem.value.clone(),
        ),
        proof_definition("Shared.id", alternate.base.type_, alternate.value),
        "different definition bodies",
    ));
    for (first, repeated, label) in cases {
        let base = encode_module(&[first], &[], 2);
        let top = encode_module(&[repeated], &["Base"], 4);
        let capsule = untrusted_module_capsule(
            &[("Base", &base, 1), ("Top", &top, 1)],
            ObjectRequirementV1::Required,
        );
        assert!(
            matches!(
                verify_flnpack_capsule(&capsule, VerificationBudget::default()),
                Verdict::Malformed(CapsuleError::ModuleGraph(_))
            ),
            "must preserve {label}"
        );
    }
}

#[test]
fn repeated_theorem_comparison_and_fresh_name_generation_are_bounded() {
    let original = identity_theorem("Shared.id", "P", BinderInfo::Default);
    let mut rows = vec![original.clone()];
    let stem = Name::str(n("Shared.id"), "_fln_subsumed_repeat");
    for suffix in 0..12 {
        let name = if suffix == 0 {
            stem.clone()
        } else {
            Name::num(stem.clone(), suffix)
        };
        let mut collision = simple_axiom("unused");
        let ConstantInfo::Axiom(value) = &mut collision else {
            panic!("axiom fixture");
        };
        value.base.name = name;
        rows.push(collision);
    }
    let base = encode_module(&rows, &[], 2);
    let top = encode_module(&[alternate_proof(original)], &["Base"], 4);
    let capsule = seal_modules(&[("Base", &base), ("Top", &top)]);
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Accepted { declarations: 14 }
    );
    for max_steps in [0, 1] {
        assert!(matches!(
            verify_flnpack_capsule(
                &capsule,
                VerificationBudget {
                    max_steps,
                    ..VerificationBudget::default()
                }
            ),
            Verdict::Inconclusive { .. }
        ));
    }
    assert!(matches!(
        verify_flnpack_capsule(&capsule, VerificationBudget { max_steps: 256, ..VerificationBudget::default() }),
        Verdict::Inconclusive { verified_so_far: 13, reason }
            if reason == "import repeat comparison budget exhausted"
    ));
}

#[test]
fn safe_definitions_with_multiple_all_names_are_admitted_separately() {
    let mut left = proposition_alias("Alias.left", "Base.P");
    let mut right = proposition_alias("Alias.right", "Alias.left");
    for entry in [&mut left, &mut right] {
        let ConstantInfo::Defn(definition) = entry else {
            panic!("definition fixture");
        };
        definition.all = vec![n("Alias.left"), n("Alias.right")];
    }
    let artifact = encode_module(&[right, simple_axiom("Base.P"), left], &[], 2);
    let capsule = seal_modules(&[("Safe", &artifact)]);
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Accepted { declarations: 3 }
    );
}

#[test]
fn interleaved_independent_inductive_families_keep_separate_admission_units() {
    let left = unit_inductive("Left.Unit");
    let right = unit_inductive("Right.Unit");
    let mut rows = vec![
        left[0].clone(),
        right[1].clone(),
        left[2].clone(),
        simple_axiom("Separate.P"),
        right[0].clone(),
        left[1].clone(),
        right[2].clone(),
    ];
    for _ in 0..2 {
        let artifact = encode_module(&rows, &[], 2);
        let capsule = seal_modules(&[("Families", &artifact)]);
        assert_eq!(
            verify_flnpack_capsule(&capsule, VerificationBudget::default()),
            Verdict::Accepted { declarations: 7 }
        );
        rows.reverse();
    }

    let incomplete = encode_module(&[left[0].clone(), left[2].clone()], &[], 2);
    assert!(matches!(
        verify_olean_parts(&[&incomplete], VerificationBudget::default()),
        Verdict::Rejected { .. }
    ));
    let mut forged = left;
    let ConstantInfo::Ctor(constructor) = &mut forged[1] else {
        panic!("constructor fixture");
    };
    constructor.induct = n("Right.Unit");
    let artifact = encode_module(&forged, &[], 2);
    assert!(matches!(
        verify_olean_parts(&[&artifact], VerificationBudget::default()),
        Verdict::Rejected { .. }
    ));
}

#[test]
fn nonadjacent_mutual_members_and_partial_singletons_use_block_admission() {
    for safety in [DefinitionSafety::Unsafe, DefinitionSafety::Partial] {
        let members = ["Mutual.left", "Mutual.right"];
        let rows = [
            recursive_definition("Mutual.right", "Mutual.left", safety, &members),
            simple_axiom("Separate.P"),
            recursive_definition(
                "Singleton.loop",
                "Singleton.loop",
                DefinitionSafety::Partial,
                &["Singleton.loop"],
            ),
            simple_axiom("Base.P"),
            recursive_definition("Mutual.left", "Mutual.right", safety, &members),
        ];
        let artifact = encode_module(&rows, &[], 2);
        let capsule = seal_modules(&[("Mutual", &artifact)]);
        assert_eq!(
            verify_flnpack_capsule(&capsule, VerificationBudget::default()),
            Verdict::Accepted { declarations: 5 },
            "{safety:?} mutual block with separate recursive partial singleton"
        );

        let missing = encode_module(&rows[..4], &[], 2);
        assert!(matches!(
            verify_olean_parts(&[&missing], VerificationBudget::default()),
            Verdict::Rejected { .. }
        ));
    }
}

#[test]
fn compiled_recursor_metadata_groups_only_definitions_with_the_same_all_and_safety() {
    let rows = [
        recursive_definition(
            "Compiled.right",
            "Compiled.left",
            DefinitionSafety::Partial,
            &["Original.Tree"],
        ),
        recursive_definition(
            "Compiled.singleton",
            "Compiled.singleton",
            DefinitionSafety::Partial,
            &["Original.List"],
        ),
        simple_axiom("Base.P"),
        recursive_definition(
            "Compiled.left",
            "Compiled.right",
            DefinitionSafety::Partial,
            &["Original.Tree"],
        ),
    ];
    let artifact = encode_module(&rows, &[], 2);
    let capsule = seal_modules(&[("Compiled", &artifact)]);
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Accepted { declarations: 4 }
    );

    for change_safety in [false, true] {
        let mut crossed = rows.clone();
        let ConstantInfo::Defn(left) = &mut crossed[3] else {
            panic!("definition fixture");
        };
        if change_safety {
            left.safety = DefinitionSafety::Unsafe;
        } else {
            left.all = vec![n("Other.Tree")];
        }
        let artifact = encode_module(&crossed, &[], 2);
        assert!(matches!(
            verify_olean_parts(&[&artifact], VerificationBudget::default()),
            Verdict::Rejected { .. }
        ));
    }
}

#[test]
fn interleaved_quotient_rows_replay_after_the_complete_equality_family() {
    let rows = equality_and_quotient();
    let mut interleaved: Vec<_> = [5, 2, 3, 1, 6, 0, 4]
        .iter()
        .map(|&index| rows[index].clone())
        .collect();
    interleaved.insert(2, simple_axiom("Separate.P"));
    let artifact = encode_module(&interleaved, &[], 2);
    let capsule = seal_modules(&[("Quotients", &artifact)]);
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Accepted { declarations: 8 }
    );

    let missing = encode_module(&rows[..6], &[], 2);
    assert!(matches!(
        verify_olean_parts(&[&missing], VerificationBudget::default()),
        Verdict::Rejected { .. }
    ));
    let mut forged = rows;
    let ConstantInfo::Quot(lift) = &mut forged[5] else {
        panic!("quotient fixture");
    };
    lift.base.type_ = Expr::sort(Level::zero());
    let artifact = encode_module(&forged, &[], 2);
    let capsule = untrusted_module_capsule(
        &[("ForgedQuotient", &artifact, 7)],
        ObjectRequirementV1::Required,
    );
    assert!(matches!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Rejected { .. }
    ));
}

#[test]
fn declaration_planning_refuses_missing_dependencies_cycles_and_exhaustion() {
    for rows in [
        vec![proposition_alias("Alias.missing", "Absent.P")],
        vec![
            proposition_alias("Alias.left", "Alias.right"),
            proposition_alias("Alias.right", "Alias.left"),
        ],
    ] {
        let artifact = encode_module(&rows, &[], 2);
        let capsule = untrusted_module_capsule(
            &[("Unplannable", &artifact, rows.len() as u64)],
            ObjectRequirementV1::Required,
        );
        assert!(matches!(
            verify_flnpack_capsule(&capsule, VerificationBudget::default()),
            Verdict::Rejected { .. }
        ));
    }

    let artifact = encode_module(
        &[
            proposition_alias("Alias.P", "Base.P"),
            simple_axiom("Base.P"),
        ],
        &[],
        2,
    );
    assert!(matches!(
        verify_olean_parts(
            &[&artifact],
            VerificationBudget {
                max_steps: 3,
                ..VerificationBudget::default()
            }
        ),
        Verdict::Inconclusive { verified_so_far: 0, reason }
            if reason == "declaration planning budget exhausted"
    ));
}

#[test]
fn capsule_import_graph_requires_every_import_and_refuses_cycles() {
    let missing = encode_module(&[simple_axiom("Top.P")], &["Missing"], 2);
    let bytes = untrusted_module_capsule(&[("Top", &missing, 1)], ObjectRequirementV1::Required);
    assert!(matches!(
        verify_flnpack_capsule(&bytes, VerificationBudget::default()),
        Verdict::Malformed(CapsuleError::ModuleGraph(detail))
            if detail.contains("Top imports missing module Missing")
    ));

    let a = encode_module(&[simple_axiom("A.P")], &["Z"], 2);
    let z = encode_module(&[simple_axiom("Z.P")], &["A"], 2);
    let bytes =
        untrusted_module_capsule(&[("A", &a, 1), ("Z", &z, 1)], ObjectRequirementV1::Required);
    assert!(matches!(
        verify_flnpack_capsule(&bytes, VerificationBudget::default()),
        Verdict::Malformed(CapsuleError::ModuleGraph(detail)) if detail == "import cycle"
    ));
}

#[test]
fn a_capsule_module_cannot_borrow_unimported_sibling_declarations() {
    let base = encode_module(&[simple_axiom("Base.P")], &[], 2);
    let top = encode_module(&[proposition_alias("Top.P", "Base.P")], &[], 2);
    let bytes = untrusted_module_capsule(
        &[("Base", &base, 1), ("Top", &top, 1)],
        ObjectRequirementV1::Required,
    );
    assert_eq!(
        verify_flnpack_capsule(&bytes, VerificationBudget::default()),
        Verdict::Rejected {
            first_rejection: n("Top.P"),
            rejection_count: 1
        }
    );

    let imported_top = encode_module(&[proposition_alias("Top.P", "Base.P")], &["Base"], 2);
    let control = seal_modules(&[("Base", &base), ("Top", &imported_top)]);
    assert_eq!(
        verify_flnpack_capsule(&control, VerificationBudget::default()),
        Verdict::Accepted { declarations: 2 }
    );
}

#[test]
fn standalone_parts_require_a_closed_module_and_semantic_objects_are_required() {
    let standalone = encode_module(&[simple_axiom("Solo.P")], &["Absent"], 2);
    assert!(matches!(
        verify_olean_parts(&[&standalone], VerificationBudget::default()),
        Verdict::Malformed(CapsuleError::ModuleGraph(detail))
            if detail.contains("standalone artifact requires import Absent")
    ));
    let closed = encode_module(&[simple_axiom("Solo.P")], &[], 2);
    let bytes = untrusted_module_capsule(&[("Solo", &closed, 1)], ObjectRequirementV1::Optional);
    assert!(matches!(
        verify_flnpack_capsule(&bytes, VerificationBudget::default()),
        Verdict::Malformed(_)
    ));
}

#[test]
fn standalone_olean_parts_accept_valid_and_reject_forged() {
    let valid_bytes = encode_module(&[generic_theorem("Solo.ok", false)], &[], 2);
    assert_eq!(
        verify_olean_parts(&[&valid_bytes], VerificationBudget::default()),
        Verdict::Accepted { declarations: 1 }
    );

    let forged_bytes = encode_module(&[ill_typed_def("Solo.forged")], &[], 2);
    assert_eq!(
        verify_olean_parts(&[&forged_bytes], VerificationBudget::default()),
        Verdict::Rejected {
            first_rejection: n("Solo.forged"),
            rejection_count: 1,
        }
    );

    // When the checker defers a Bound-vs-Apply conversion mismatch, FL-INV-07
    // requires Inconclusive — never Accepted.
    let deferred_bytes = encode_module(&[generic_theorem("Solo.deferred", true)], &[], 2);
    assert!(matches!(
        verify_olean_parts(&[&deferred_bytes], VerificationBudget::default()),
        Verdict::Inconclusive { .. }
    ));
}

#[test]
fn forged_proof_resealed_into_valid_archive_is_rejected() {
    let forged_bytes = encode_module(&[ill_typed_def("Evil.forged")], &[], 2);
    let mut builder = CartridgeBuilderV1::new(PINNED_EPOCH, zero_root());
    let decl_id = builder.add_object(
        CartridgeObjectKindV1::Declaration,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        forged_bytes,
    );

    // Craft a syntactically valid semantic profile pointing at the forged module.
    let mut profile = CanonWriter::new();
    profile.schema(SCHEMA_OLEAN_CAPSULE);
    profile.u64(PINNED_EPOCH.get() as u64);
    profile.u64((PINNED_EPOCH.get() >> 64) as u64);
    profile.u8(Mode::Sound.tag());
    profile.u8(ReproducibilityProfile::Standard.tag());
    profile.str(OLEAN_PIN_TAG);
    profile.str(OLEAN_PIN_COMMIT);
    KVMap::new().write_body(&mut profile);
    profile.digest(&Digest([0u8; 32]));
    profile.digest(&Digest([0u8; 32]));
    profile.u64(1);
    n("Evil").write_body(&mut profile);
    profile.digest(&decl_id.digest());
    profile.bool(false);
    profile.digest(&Digest([0u8; 32]));
    profile.digest(&Digest([0u8; 32]));
    profile.u64(1);
    let profile_bytes = profile.into_bytes();

    let receipt_id = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        profile_bytes,
    );
    builder.add_root_receipt(receipt_id);
    let archive_bytes = builder
        .build()
        .expect("build")
        .to_canonical_bytes()
        .expect("encode");

    assert_eq!(
        verify_flnpack_capsule(&archive_bytes, VerificationBudget::default()),
        Verdict::Rejected {
            first_rejection: n("Evil.forged"),
            rejection_count: 1,
        }
    );
}

#[test]
fn corrupted_archive_and_legacy_capsule_return_malformed() {
    let mut bytes = seal_two_module_capsule();
    let mid = bytes.len() / 2;
    bytes[mid] ^= 0xFF;
    assert!(matches!(
        verify_flnpack_capsule(&bytes, VerificationBudget::default()),
        Verdict::Malformed(_)
    ));

    // Legacy archive with no semantic receipt must be refused, not accepted.
    let mut legacy = CartridgeBuilderV1::new(PINNED_EPOCH, zero_root());
    let obj = legacy.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"legacy-opaque-receipt".to_vec(),
    );
    legacy.add_root_receipt(obj);
    let legacy_bytes = legacy
        .build()
        .expect("build")
        .to_canonical_bytes()
        .expect("encode");
    assert_eq!(
        verify_flnpack_capsule(&legacy_bytes, VerificationBudget::default()),
        Verdict::Malformed(CapsuleError::Truncated)
    );
}

#[test]
fn unsupported_profile_version_returns_unsupported_version() {
    let mut builder = CartridgeBuilderV1::new(PINNED_EPOCH, zero_root());
    let mut profile = CanonWriter::new();
    profile.str(SCHEMA_OLEAN_CAPSULE.name);
    profile.u16(99);
    let receipt_id = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        profile.into_bytes(),
    );
    builder.add_root_receipt(receipt_id);
    let archive_bytes = builder
        .build()
        .expect("build")
        .to_canonical_bytes()
        .expect("encode");

    assert_eq!(
        verify_flnpack_capsule(&archive_bytes, VerificationBudget::default()),
        Verdict::Malformed(CapsuleError::UnsupportedVersion(99))
    );
}

#[test]
fn tight_budgets_yield_inconclusive_never_accepted_or_rejected() {
    let bytes = seal_two_module_capsule();

    let byte_limited = VerificationBudget {
        max_payload_bytes: 1,
        ..VerificationBudget::default()
    };
    assert!(matches!(
        verify_flnpack_capsule(&bytes, byte_limited),
        Verdict::Inconclusive {
            verified_so_far: 0,
            ..
        }
    ));
    let standalone = encode_module(&[simple_axiom("Solo.P")], &[], 2);
    assert!(matches!(
        verify_olean_parts(&[&standalone], byte_limited),
        Verdict::Inconclusive {
            verified_so_far: 0,
            ..
        }
    ));

    let decl_limited = verify_flnpack_capsule(
        &bytes,
        VerificationBudget {
            max_declarations: 1,
            ..VerificationBudget::default()
        },
    );
    assert!(
        matches!(decl_limited, Verdict::Inconclusive { .. }),
        "expected Inconclusive on declaration limit, got {decl_limited:?}"
    );

    let step_limited = verify_flnpack_capsule(
        &bytes,
        VerificationBudget {
            max_steps: 1,
            ..VerificationBudget::default()
        },
    );
    assert!(
        matches!(step_limited, Verdict::Inconclusive { .. }),
        "expected Inconclusive on step limit, got {step_limited:?}"
    );
}

#[test]
fn artifact_identity_is_checked_even_inside_a_resealed_capsule() {
    let original = encode_module(&[simple_axiom("Solo.P")], &[], 2);
    assert_eq!(
        verify_olean_parts(&[&original], VerificationBudget::default()),
        Verdict::Accepted { declarations: 1 }
    );
    // Generated OLEAN_CONTRACT.md §1: GMP flag, version string and its
    // padding, then the pinned compiler hash. Each is independently bound.
    for offset in [6, 7, 39, 40] {
        let mut changed = original.clone();
        changed[offset] ^= 1;
        assert_eq!(
            verify_olean_parts(&[&changed], VerificationBudget::default()),
            Verdict::Malformed(CapsuleError::AxiomMismatch),
            "header byte {offset}"
        );
        let resealed =
            untrusted_module_capsule(&[("Solo", &changed, 1)], ObjectRequirementV1::Required);
        assert_eq!(
            verify_flnpack_capsule(&resealed, VerificationBudget::default()),
            Verdict::Malformed(CapsuleError::AxiomMismatch),
            "a new archive digest must not authorize header byte {offset}"
        );
    }
}

#[test]
fn module_parts_require_checked_private_bodies_and_public_imports() {
    let theorem = generic_theorem("Module.keep", false);
    let public = encode_module_kind(std::slice::from_ref(&theorem), &[], 2, true);
    let server = encode_module_kind(std::slice::from_ref(&theorem), &[], 4, true);
    let private = encode_module_kind(std::slice::from_ref(&theorem), &[], 6, true);
    let budget = VerificationBudget::default();
    assert_eq!(
        verify_olean_parts(&[&public, &server, &private], budget),
        Verdict::Accepted { declarations: 1 }
    );
    for parts in [vec![public.as_slice()], vec![&public, &server]] {
        assert!(matches!(
            verify_olean_parts(&parts, budget),
            Verdict::Malformed(_)
        ));
    }
    let empty_private = encode_module_kind(&[], &[], 6, true);
    assert!(matches!(
        verify_olean_parts(&[&public, &server, &empty_private], budget),
        Verdict::Malformed(_)
    ));

    let ConstantInfo::Thm(value) = theorem else {
        panic!("the fixture is a theorem");
    };
    let erased = ConstantInfo::Axiom(AxiomVal {
        base: value.base,
        is_unsafe: false,
    });
    let weakened = encode_module_kind(std::slice::from_ref(&erased), &[], 6, true);
    assert!(matches!(
        verify_olean_parts(&[&public, &server, &weakened], budget),
        Verdict::Malformed(_)
    ));
    // The opposite direction is the pin's ordinary body-erasure scheme.
    let exported_axiom = encode_module_kind(std::slice::from_ref(&erased), &[], 2, true);
    assert_eq!(
        verify_olean_parts(&[&exported_axiom, &server, &private], budget),
        Verdict::Accepted { declarations: 1 }
    );

    let imported_public = encode_module_kind(&[erased], &["Absent"], 2, true);
    assert!(matches!(
        verify_olean_parts(&[&imported_public, &server, &private], budget),
        Verdict::Malformed(CapsuleError::ModuleGraph(_))
    ));
    let mut wrong_pin_private = private.clone();
    wrong_pin_private[40] ^= 1;
    assert_eq!(
        verify_olean_parts(&[&public, &server, &wrong_pin_private], budget),
        Verdict::Malformed(CapsuleError::AxiomMismatch)
    );
}

#[test]
fn disjoint_modules_cannot_publish_conflicting_declarations() {
    let proposition = simple_axiom("Shared");
    let mut type_ = proposition.clone();
    let ConstantInfo::Axiom(value) = &mut type_ else {
        panic!("the fixture is an axiom");
    };
    value.base.type_ = Expr::sort(Level::succ(Level::zero()).unwrap());
    let a = encode_module(std::slice::from_ref(&proposition), &[], 2);
    let b = encode_module(&[type_], &[], 4);
    let capsule =
        untrusted_module_capsule(&[("A", &a, 1), ("B", &b, 1)], ObjectRequirementV1::Required);
    assert!(matches!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Malformed(CapsuleError::ModuleGraph(_))
    ));
    let b = encode_module(&[proposition], &[], 4);
    let capsule =
        untrusted_module_capsule(&[("A", &a, 1), ("B", &b, 1)], ObjectRequirementV1::Required);
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Accepted { declarations: 2 }
    );
}

#[test]
fn checked_import_snapshots_merge_both_sides_of_a_diamond() {
    let base = encode_module(&[simple_axiom("Base.P")], &[], 2);
    let left = encode_module(&[proposition_alias("Left.P", "Base.P")], &["ZBase"], 4);
    let right = encode_module(
        &[
            proposition_alias("Right.P", "Base.P"),
            proposition_alias("Right.Q", "Right.P"),
        ],
        &["ZBase"],
        6,
    );
    let top = encode_module(
        &[
            proposition_alias("Top.left", "Left.P"),
            proposition_alias("Top.right", "Right.Q"),
        ],
        &["YLeft", "XRight"],
        8,
    );
    let capsule = seal_modules(&[
        ("ATop", &top),
        ("XRight", &right),
        ("YLeft", &left),
        ("ZBase", &base),
    ]);
    assert_eq!(
        verify_flnpack_capsule(&capsule, VerificationBudget::default()),
        Verdict::Accepted { declarations: 6 }
    );
}
