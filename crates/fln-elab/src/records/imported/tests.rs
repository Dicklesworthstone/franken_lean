use super::*;
use crate::lctx::LocalDecl;
use crate::records::{RecordSpec, record_declarations};
use fln_core::expr::{FVarId, Literal, NatLit};
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::Budget;

fn n(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn c(value: &str) -> Expr {
    Expr::const_(n(value), vec![])
}

fn publish(env: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) =
        admit(env, declaration, Budget::for_stack_bytes(2 * 1024 * 1024))
    else {
        panic!("record interface did not pass K1");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("record interface admission did not agree");
    };
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::BlockCommitted(publication)) => publication.environment,
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(publication))) => {
            publication.environment
        }
        other => panic!("record interface publication failed: {other:?}"),
    }
}

fn local(label: &str, type_: Expr, style: BinderInfo) -> LocalDecl {
    LocalDecl {
        id: FVarId(n(label)),
        user_name: n(label),
        type_,
        value: None,
        binder_info: style,
        index: 0,
    }
}

fn record(
    env: &Environment,
    name: &str,
    parameters: Vec<LocalDecl>,
    fields: Vec<LocalDecl>,
) -> Environment {
    let spec = RecordSpec {
        name: n(name),
        level_params: vec![],
        parameters,
        fields,
        result_level: Level::one(),
        is_class: false,
    };
    let mut out = env.clone();
    for declaration in record_declarations(&spec, RecordBudget::default()).unwrap() {
        out = publish(&out, declaration);
    }
    out
}

fn base() -> Environment {
    let env = publish(
        &Environment::new(),
        crate::seed::nat_inductive_seed_declaration(),
    );
    let env = record(
        &env,
        "Parent",
        vec![],
        vec![local("value", c("Nat"), BinderInfo::Default)],
    );
    let env = record(
        &env,
        "Child",
        vec![],
        vec![
            local("toParent", c("Parent"), BinderInfo::InstImplicit),
            local("extra", c("Nat"), BinderInfo::Default),
        ],
    );
    let parameter = local("A", Expr::sort(Level::one()), BinderInfo::Default);
    record(
        &env,
        "Box",
        vec![parameter.clone()],
        vec![local(
            "value",
            Expr::fvar(parameter.id),
            BinderInfo::Default,
        )],
    )
}

fn field(record: &str, label: &str, subobject: Option<&str>, style: BinderInfo) -> StructureField {
    StructureField {
        name: n(label),
        projection: n(&format!("{record}.{label}")),
        subobject: subobject.map(n),
        binder_info: style,
    }
}

fn rows() -> Vec<StructureEntry> {
    vec![
        StructureEntry {
            name: n("Parent"),
            fields: vec![field("Parent", "value", None, BinderInfo::Default)],
            parents: vec![],
        },
        StructureEntry {
            name: n("Child"),
            fields: vec![
                field(
                    "Child",
                    "toParent",
                    Some("Parent"),
                    BinderInfo::InstImplicit,
                ),
                field("Child", "extra", None, BinderInfo::Default),
            ],
            parents: vec![StructureParent {
                name: n("Parent"),
                subobject: true,
                projection: n("Child.toParent"),
            }],
        },
        StructureEntry {
            name: n("Box"),
            fields: vec![field("Box", "value", None, BinderInfo::Default)],
            parents: vec![],
        },
    ]
}

#[test]
fn admitted_interfaces_roundtrip_and_retained_module_deltas_match_fresh_registration() {
    let env = base();
    let before = env.logical_root(&KVMap::new());
    let rows = rows();
    let registered = register(&env, &rows).unwrap();
    let read = ImportedStructures::read(&registered).unwrap();
    for row in &rows {
        assert_eq!(read.get(&row.name), Some(row));
    }
    assert_eq!(
        register(&registered, &rows).unwrap(),
        registered,
        "equal metadata is idempotent"
    );
    let parents = RecordParents::read(&registered).unwrap();
    assert_eq!(
        parents.parents(&n("Child")),
        &[RecordParent {
            record: n("Child"),
            field: 0,
            parent: n("Parent"),
        }]
    );
    assert!(
        parents
            .fields(&registered, &n("Child"), RecordBudget::default())
            .unwrap()
            .iter()
            .any(|field| field.name == n("value") && field.path.len() == 2)
    );

    let mut activation = crate::instances::imported::ImportActivation::new(env.clone());
    let mut per_call = env.clone();
    for row in &rows {
        let previous = activation.environment().clone();
        activation = activation
            .register_structures(std::slice::from_ref(row))
            .unwrap();
        per_call = register(&per_call, std::slice::from_ref(row)).unwrap();
        assert_eq!(
            activation.environment(),
            &per_call,
            "each module retains its own exact delta"
        );
        assert_eq!(
            ImportedStructures::read(&previous).unwrap().get(&row.name),
            None
        );
    }
    assert_eq!(activation.finish().unwrap(), registered);
    assert_eq!(env.logical_root(&KVMap::new()), before);
    assert!(
        ImportedStructures::read(&env)
            .unwrap()
            .get(&n("Child"))
            .is_none()
    );
}

#[test]
fn wrong_field_projection_parent_and_binder_metadata_refuse_atomically() {
    let env = base();
    let before = env.logical_root(&KVMap::new());
    let correct = rows();
    let child = correct[1].clone();
    let mut cases = Vec::new();
    let mut bad = child.clone();
    bad.fields.swap(0, 1);
    cases.push(bad);
    let mut bad = child.clone();
    bad.fields[0].projection = n("Child.extra");
    cases.push(bad);
    let mut bad = child.clone();
    bad.fields[0].binder_info = BinderInfo::Default;
    cases.push(bad);
    let mut bad = child.clone();
    bad.fields[0].subobject = Some(n("Box"));
    cases.push(bad);
    let mut bad = child.clone();
    bad.parents[0].subobject = false;
    cases.push(bad);
    let mut bad = child.clone();
    bad.parents[0].projection = n("Child.extra");
    cases.push(bad);
    let mut bad = child.clone();
    bad.parents.push(bad.parents[0].clone());
    cases.push(bad);
    let mut bad = child.clone();
    bad.fields[1].name = n("value.with.prefix");
    cases.push(bad);
    for bad in cases {
        assert!(register(&env, &[correct[0].clone(), bad]).is_err());
        assert_eq!(env.logical_root(&KVMap::new()), before);
        assert!(
            ImportedStructures::read(&env)
                .unwrap()
                .get(&n("Parent"))
                .is_none()
        );
    }
    assert!(register(&env, &[child.clone(), child]).is_err());
    assert!(
        register(&env, &correct).is_ok(),
        "the same predecessor supports a valid retry"
    );
}

#[test]
fn malformed_journals_counts_and_foreign_descriptors_remain_refusals() {
    let env = base();
    let before = env.logical_root(&KVMap::new());
    let mut huge = MAGIC.to_vec();
    write_name(&n("Child"), &mut huge).unwrap();
    huge.extend(u32::MAX.to_le_bytes());
    for payload in [vec![], b"FLNRIMP\x02".to_vec(), huge] {
        let bad = env
            .register_extension(descriptor())
            .unwrap()
            .push_extension_entry(&extension_name(), payload)
            .unwrap();
        assert!(ImportedStructures::read(&bad).is_err());
    }
    let mut foreign = descriptor();
    foreign.provenance = PayloadProvenance::Opaque;
    assert!(ImportedStructures::read(&env.register_extension(foreign).unwrap()).is_err());
    let mut duplicate = env.register_extension(descriptor()).unwrap();
    let payload = encode(&rows()[0]).unwrap();
    for _ in 0..2 {
        duplicate = duplicate
            .push_extension_entry(&extension_name(), payload.clone())
            .unwrap();
    }
    assert_eq!(
        ImportedStructures::read(&duplicate),
        Err(RecordError::DuplicateField)
    );
    let mut remaining = 0;
    assert_eq!(
        validate(&env, &rows()[0], &mut remaining),
        Err(RecordError::ResourceLimit)
    );
    assert_eq!(env.logical_root(&KVMap::new()), before);
}

#[test]
fn exact_interface_comparisons_meter_shared_nodes_and_detect_changed_checked_shapes() {
    let env = base();
    let info = env.find(&n("Child.extra")).unwrap();
    assert_eq!(
        same_interface(info, info, &mut 0),
        Err(RecordError::ResourceLimit)
    );
    assert!(same_interface(info, info, &mut 10_000).unwrap());
    let mut changed = info.clone();
    let ConstantInfo::Defn(definition) = &mut changed else {
        panic!("projection")
    };
    definition.value = Expr::lam(
        n("self"),
        c("Child"),
        Expr::lit(Literal::Nat(NatLit::from_u64(0))),
        BinderInfo::Default,
    );
    assert!(!same_interface(info, &changed, &mut 10_000).unwrap());

    fn shared(depth: usize) -> Expr {
        let mut value = c("Nat");
        for _ in 0..depth {
            value = Expr::app(value.clone(), value);
        }
        value
    }
    let (left, right) = (shared(128), shared(128));
    let mut remaining = 600;
    assert!(equality::expression(&left, &right, &mut remaining).unwrap());
    assert!(
        remaining > 200,
        "sharing must be charged by compared pairs, not its exponential tree"
    );
    assert_eq!(
        equality::expression(&left, &right, &mut 10),
        Err(RecordError::ResourceLimit)
    );
    let differently_named = Expr::lam(
        n("x"),
        c("Nat"),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    let original = Expr::lam(
        n("y"),
        c("Nat"),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    assert!(!equality::expression(&original, &differently_named, &mut 100).unwrap());
}

#[test]
fn added_parent_edges_cannot_complete_a_cycle_through_an_earlier_row() {
    let mut entries = BTreeMap::new();
    let row = |child: &str, parent: &str| StructureEntry {
        name: n(child),
        fields: vec![],
        parents: vec![StructureParent {
            name: n(parent),
            subobject: false,
            projection: n("unused"),
        }],
    };
    entries.insert(n("A"), row("A", "B"));
    assert!(acyclic(&entries, entries.keys(), &mut 100).is_ok());
    entries.insert(n("B"), row("B", "A"));
    assert_eq!(
        acyclic(&entries, [&n("B")], &mut 100),
        Err(RecordError::InvalidTelescope)
    );
}

#[derive(Clone, Copy)]
enum ProofProjection {
    Correct,
    OtherField,
    Opaque,
}

fn proof_record(variant: ProofProjection) -> Environment {
    let parameter = local("P", Expr::sort(Level::zero()), BinderInfo::Default);
    let spec = RecordSpec {
        name: n("ProofFields"),
        level_params: vec![],
        parameters: vec![parameter.clone()],
        fields: vec![
            local(
                "first",
                Expr::fvar(parameter.id.clone()),
                BinderInfo::Default,
            ),
            local("second", Expr::fvar(parameter.id), BinderInfo::Default),
        ],
        result_level: Level::zero(),
        is_class: false,
    };
    let declarations = record_declarations(&spec, RecordBudget::default()).unwrap();
    let second = declarations
        .iter()
        .find_map(|declaration| match declaration {
            Declaration::Thm(theorem) if theorem.base.name == n("ProofFields.second") => {
                Some(theorem.value.clone())
            }
            _ => None,
        })
        .expect("proof fields have theorem projections");
    let mut env = Environment::new();
    for declaration in declarations {
        let declaration = match declaration {
            Declaration::Thm(mut theorem) if theorem.base.name == n("ProofFields.first") => {
                match variant {
                    ProofProjection::Correct => Declaration::Thm(theorem),
                    ProofProjection::OtherField => {
                        // Both fields prove the same proposition. This different
                        // body still passes K1, but is not the declared projection.
                        theorem.value = second.clone();
                        Declaration::Thm(theorem)
                    }
                    ProofProjection::Opaque => Declaration::Opaque(fln_env::constants::OpaqueVal {
                        base: theorem.base,
                        value: theorem.value,
                        is_unsafe: false,
                        all: theorem.all,
                    }),
                }
            }
            declaration => declaration,
        };
        env = publish(&env, declaration);
    }
    env
}

#[test]
fn admitted_theorem_projections_keep_exact_body_and_declaration_kind() {
    let env = proof_record(ProofProjection::Correct);
    let before = env.logical_root(&KVMap::new());
    let row = StructureEntry {
        name: n("ProofFields"),
        fields: vec![
            field("ProofFields", "first", None, BinderInfo::Default),
            field("ProofFields", "second", None, BinderInfo::Default),
        ],
        parents: vec![],
    };
    let registered = register(&env, std::slice::from_ref(&row)).unwrap();
    assert_eq!(
        ImportedStructures::read(&registered)
            .unwrap()
            .get(&row.name),
        Some(&row),
    );
    let proof = env.find(&n("ProofFields.first")).unwrap();
    assert!(matches!(proof, ConstantInfo::Thm(_)));
    assert!(same_interface(proof, &proof.clone(), &mut 10_000).unwrap());
    assert_eq!(
        same_interface(proof, &proof.clone(), &mut 0),
        Err(RecordError::ResourceLimit),
    );

    for variant in [ProofProjection::OtherField, ProofProjection::Opaque] {
        let changed = proof_record(variant);
        let changed_root = changed.logical_root(&KVMap::new());
        let changed_proof = changed.find(&n("ProofFields.first")).unwrap();
        assert!(
            !same_interface(proof, changed_proof, &mut 10_000).unwrap(),
            "a checked proof with a different body or kind is a different interface",
        );
        assert!(
            register(&changed, std::slice::from_ref(&row)).is_err(),
            "proof irrelevance cannot authorize a wrong field or opaque projection",
        );
        assert_eq!(changed.logical_root(&KVMap::new()), changed_root);
        assert!(
            ImportedStructures::read(&changed)
                .unwrap()
                .get(&row.name)
                .is_none(),
        );
    }
    let ConstantInfo::Thm(theorem) = proof else {
        unreachable!()
    };
    let as_definition = ConstantInfo::Defn(fln_env::constants::DefinitionVal {
        base: theorem.base.clone(),
        value: theorem.value.clone(),
        hints: fln_env::constants::ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: theorem.all.clone(),
    });
    assert!(!same_interface(proof, &as_definition, &mut 10_000).unwrap());
    assert_eq!(env.logical_root(&KVMap::new()), before);
}
