//! Hand-built mutual recursors through the production K1 + independent council.
#![forbid(unsafe_code)]
#[path = "../../fln-checker/tests/support/mutual.rs"]
mod fixtures;
use fixtures::{Fixture, Mutation, fixture, name};
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap};
use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::level::Level;
use fln_core::outcome::Outcome;
use fln_env::constants::{
    ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal, InductiveVal, RecursorRule,
    RecursorVal, ReducibilityHints,
};
use fln_env::environment::Environment;
use fln_kernel::{Declaration, InductiveBlock, verdict::Verdict};

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(budget())
}
fn base() -> Engine {
    Engine::from_environment(Environment::new())
}

// In these fixtures all motives occur in an explicit constructor minor and all
// parameters/indices occur in later explicit domains. Match their declared Lean
// calling convention, without deriving any type or iota term from either seat.
fn calling_convention(
    expr: &Expr,
    parameters: usize,
    motives: usize,
    minors: usize,
    indices: usize,
) -> Expr {
    let mut binders = Vec::new();
    let mut tail = expr;
    while let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        ..
    } = tail.node()
    {
        let i = binders.len();
        let implicit = i < parameters + motives
            || (i >= parameters + motives + minors && i < parameters + motives + minors + indices);
        binders.push((
            binder_name.clone(),
            binder_type.clone(),
            if implicit {
                BinderInfo::Implicit
            } else {
                BinderInfo::Default
            },
        ));
        tail = body;
    }
    binders
        .into_iter()
        .rev()
        .fold(tail.clone(), |body, (n, ty, style)| {
            Expr::forall_e(n, ty, body, style)
        })
}
fn candidate(f: &Fixture) -> Declaration {
    Declaration::Inductive(InductiveBlock {
        types: f
            .types
            .iter()
            .map(|t| InductiveVal {
                base: ConstantVal {
                    name: t.name.clone(),
                    level_params: f.levels.clone(),
                    type_: t.ty.clone(),
                },
                num_params: f.parameters as u32,
                num_indices: t.indices as u32,
                all: f.names.clone(),
                ctors: t.ctors.clone(),
                num_nested: 0,
                is_rec: f.recursive,
                is_unsafe: false,
                is_reflexive: f.reflexive,
            })
            .collect(),
        ctors: f
            .ctors
            .iter()
            .map(|c| ConstructorVal {
                base: ConstantVal {
                    name: c.name.clone(),
                    level_params: f.levels.clone(),
                    type_: c.ty.clone(),
                },
                induct: f.names[c.family].clone(),
                cidx: c.index as u32,
                num_params: f.parameters as u32,
                num_fields: c.fields as u32,
                is_unsafe: false,
            })
            .collect(),
        recursors: f
            .recs
            .iter()
            .map(|r| RecursorVal {
                base: ConstantVal {
                    name: r.name.clone(),
                    level_params: f.rec_levels.clone(),
                    type_: calling_convention(
                        &r.ty,
                        f.parameters,
                        f.names.len(),
                        f.ctors.len(),
                        r.indices,
                    ),
                },
                all: f.names.clone(),
                num_params: f.parameters as u32,
                num_indices: r.indices as u32,
                num_motives: f.names.len() as u32,
                num_minors: f.ctors.len() as u32,
                rules: r
                    .rules
                    .iter()
                    .map(|r| RecursorRule {
                        ctor: r.ctor.clone(),
                        nfields: r.fields as u32,
                        rhs: r.rhs.clone(),
                    })
                    .collect(),
                k: false,
                is_unsafe: false,
            })
            .collect(),
    })
}
fn accept(f: &Fixture) -> Engine {
    let declaration = candidate(f);
    let kernel = fln_kernel::check(&Environment::new(), &declaration, budget());
    assert!(
        matches!(kernel, Outcome::Complete(Verdict::Accepted { .. })),
        "K1: {kernel:?}"
    );
    let admitted = base()
        .admit_declaration(declaration, &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("council: {e:?}"))
        .into_complete()
        .expect("complete council");
    for name in &f.names {
        assert!(admitted.engine.environment().contains(name));
    }
    for rec in &f.recs {
        assert!(admitted.engine.environment().contains(&rec.name));
    }
    admitted.engine
}
#[test]
fn two_seats_admit_mutual_data_and_dependent_indexed_families() {
    for f in [
        fixture(false, false, false, 2, Mutation::None),
        fixture(false, false, false, 3, Mutation::None),
        fixture(true, false, false, 2, Mutation::None),
        fixture(true, true, false, 2, Mutation::None),
    ] {
        accept(&f);
    }
}
#[test]
fn two_seats_admit_positive_function_children_across_mutual_families() {
    accept(&fixture(true, false, true, 3, Mutation::None));
    accept(&fixture(true, true, true, 2, Mutation::None));
}
#[test]
fn forged_rules_cannot_publish_a_partial_mutual_environment() {
    let engine = base();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for mutation in [
        Mutation::WrongCallFamily,
        Mutation::SwapMotives,
        Mutation::SwapMinors,
        Mutation::MissingInductionHypothesis,
        Mutation::WrongChildIndex,
        Mutation::FalseRecursive,
        Mutation::FalseReflexive,
    ] {
        let f = fixture(true, true, true, 2, mutation);
        assert!(
            engine
                .admit_declaration(candidate(&f), &options, limits())
                .is_err(),
            "{mutation:?}"
        );
        assert_eq!(engine.logical_root(&options), root);
        assert!(!engine.environment().contains(&name("Mutual0")));
    }
    accept(&fixture(true, true, true, 2, Mutation::None));
}
#[test]
fn admitted_cross_family_iota_rules_compute_during_ordinary_declaration_checking() {
    let engine = accept(&fixture(false, false, false, 2, Mutation::None));
    let c = |s| Expr::const_(name(s), vec![]);
    let lam = |ty, body| Expr::lam(name("x"), ty, body, BinderInfo::Default);
    let app = |f: Expr, args: Vec<Expr>| args.into_iter().fold(f, Expr::app);
    let type_ = Expr::sort(Level::one());
    let major = Expr::app(
        c("Mutual0.node"),
        Expr::app(c("Mutual1.node"), c("Mutual0.leaf")),
    );
    let computation = app(
        Expr::const_(
            name("Mutual0.rec"),
            vec![Level::succ(Level::one()).unwrap()],
        ),
        vec![
            lam(c("Mutual0"), type_.clone()),
            lam(c("Mutual1"), type_.clone()),
            c("Mutual0"),
            lam(c("Mutual1"), lam(type_.clone(), Expr::bvar(0).unwrap())),
            lam(c("Mutual0"), lam(type_, Expr::bvar(0).unwrap())),
            major,
        ],
    );
    let declaration = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name("mutualWitness"),
            level_params: vec![],
            type_: computation,
        },
        value: c("Mutual0.leaf"),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("mutualWitness")],
    });
    let result = engine
        .admit_declaration(declaration, &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("mutual computation: {e:?}"))
        .into_complete()
        .unwrap();
    assert!(result.engine.environment().contains(&name("mutualWitness")));
    assert!(!engine.environment().contains(&name("mutualWitness")));
}

#[test]
fn both_seats_reconstruct_interleaved_self_and_cross_family_children() {
    for (generic, indexed, higher, families) in [
        (false, false, false, 3),
        (true, false, false, 3),
        (true, true, false, 2),
        (true, false, true, 3),
        (true, true, true, 2),
    ] {
        accept(&fixture(
            generic,
            indexed,
            higher,
            families,
            Mutation::MultipleChildren,
        ));
    }
}

fn constants(f: &Fixture) -> Vec<fln::ConstantInfo> {
    let Declaration::Inductive(block) = candidate(f) else {
        unreachable!()
    };
    block
        .types
        .into_iter()
        .map(fln::ConstantInfo::Induct)
        .chain(block.ctors.into_iter().map(fln::ConstantInfo::Ctor))
        .chain(block.recursors.into_iter().map(fln::ConstantInfo::Rec))
        .collect()
}

fn artifact(constants: &[fln::ConstantInfo]) -> Vec<u8> {
    fln::encode_olean_module(
        fln::OleanModuleWriteInput {
            is_module: false,
            imports: &[],
            constants,
            extra_const_names: &[],
        },
        fln::OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: (fln::OLEAN_REGION_ALIGN as u64) * 2,
        },
        fln::OleanWriteBudget::default(),
    )
    .expect("native producer serializes the complete candidate")
    .bytes
}

#[test]
fn native_olean_decode_planning_and_council_reconstruct_the_complete_mutual_unit() {
    // These are native-produced artifacts, not claimed Reference fixtures.
    // Recursor rows lead the stream; metadata, not row order, determines the
    // authority unit and shared motive order presented to each admission seat.
    for f in [
        fixture(false, false, false, 3, Mutation::None),
        fixture(true, true, true, 2, Mutation::MultipleChildren),
    ] {
        let mut rows = constants(&f);
        rows.reverse();
        let bytes = artifact(&rows);
        let predecessor = base();
        let checked = predecessor
            .check_olean_artifact(
                &bytes,
                &KVMap::new(),
                fln::OleanCheckLimits::new(bytes.len(), budget()),
            )
            .unwrap_or_else(|e| panic!("mutual artifact: {e:?}"))
            .into_complete()
            .expect("both seats return complete mutual admission");
        assert_eq!(checked.decoded.constants, rows);
        assert_eq!(checked.declarations.len(), rows.len());
        assert_eq!(checked.engine.environment().len(), rows.len());
        assert!(
            checked
                .declarations
                .iter()
                .all(|d| d.checker.schema == fln_checker::admit::ADMISSION_SCHEMA)
        );
        assert!(predecessor.environment().is_empty());
    }
}

#[test]
fn a_later_bad_artifact_declaration_cannot_publish_the_checked_mutual_prefix() {
    let mut rows = constants(&fixture(false, false, false, 2, Mutation::None));
    rows.push(fln::ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name("bad"),
            level_params: vec![],
            type_: Expr::const_(name("Mutual0"), vec![]),
        },
        value: Expr::sort(Level::zero()),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("bad")],
    }));
    rows.reverse();
    let bytes = artifact(&rows);
    let predecessor = base();
    let options = KVMap::new();
    let root = predecessor.logical_root(&options);
    let result = predecessor.check_olean_artifact(
        &bytes,
        &options,
        fln::OleanCheckLimits::new(bytes.len(), budget()),
    );
    assert!(
        matches!(
            result,
            Err(fln::OleanCheckError::Admission(
                fln::EngineAdmissionError::BatchDeclaration { index: 1, .. }
            ))
        ),
        "{result:?}"
    );
    assert!(predecessor.environment().is_empty());
    assert_eq!(predecessor.logical_root(&options), root);
}

#[test]
fn an_independent_checker_nonanswer_still_vetoes_a_kernel_accepted_mutual_block() {
    let f = fixture(true, true, true, 2, Mutation::MultipleChildren);
    let predecessor = base();
    let options = KVMap::new();
    let root = predecessor.logical_root(&options);
    assert!(matches!(
        fln_kernel::check(predecessor.environment(), &candidate(&f), budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    for staging_stop in [false, true] {
        let mut limits = limits();
        if staging_stop {
            limits.checker.environment.max_arena_nodes = 24;
        } else {
            limits.checker.admission.conversion.quick.max_comparisons = 0;
        }
        let result = predecessor.admit_declaration(candidate(&f), &options, limits);
        match result {
            Err(fln::EngineAdmissionError::CouncilHalted { .. }) => {}
            Err(error) => panic!("wrong nonanswer at staging={staging_stop}: {error:?}"),
            Ok(_) => panic!("checker budget was not exhausted at staging={staging_stop}"),
        }
        assert!(predecessor.environment().is_empty());
        assert_eq!(predecessor.logical_root(&options), root);
    }
    accept(&f);
}
