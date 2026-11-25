//! Unit, mutant-killing, cancellation, and hostile-batch tests for the
//! provisional `.olean` frontier (`--continue --provisional`, bead
//! `fln-provisional-frontier-vf32`, FL-INV-01 / FL-INV-02 / FL-INV-06 / FL-INV-07).

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroUsize;
use std::sync::atomic::{AtomicBool, Ordering};

use fln::{
    Budget, Engine, Environment, KVMap, Name, OleanCheckError, OleanCheckLimits, OleanFrontierJobs,
    OleanModuleImport, OleanModuleInput, OleanModuleVerdict, OleanModuleWriteInput,
    OleanWriteBudget, OleanWriteHeader, ProvisionalEnvironment, ProvisionalModuleVerdict,
    classify_blocked_eligibility, compute_root_dominators, encode_olean_module,
};
use fln_admission::reuse::{
    CheckerIdentity, ImportClosureKey, ImportReuseRecord, ImportReuseRefusal,
    check_environment_recordable,
};
use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal,
    InductiveVal, RecursorRule, RecursorVal, ReducibilityHints,
};
use fln_env::modules::CancellationProbe;

const STACK: usize = 64 * 1024 * 1024;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn axiom(name: &str, ty: Expr) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: Vec::new(),
            type_: ty,
        },
        is_unsafe: false,
    })
}

fn safe_def(name: &str, ty: Expr, value: Expr) -> ConstantInfo {
    let decl_name = n(name);
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: decl_name.clone(),
            level_params: Vec::new(),
            type_: ty,
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![decl_name],
    })
}

/// Build a valid, well-typed term that requires `depth` K1 beta-reductions /
/// binder traversals to typecheck, so a tight `Budget::max_steps` deterministically
/// produces an `Inconclusive` stop on this declaration while cheap declarations pass.
fn beta_chain(prop_name: &str, witness_name: &str, depth: usize) -> Expr {
    let prop = Expr::const_(n(prop_name), Vec::new());
    let mut expr = Expr::const_(n(witness_name), Vec::new());
    for _ in 0..depth {
        let id = Expr::lam(
            Name::str(Name::anonymous(), "x"),
            prop.clone(),
            Expr::bvar(0).expect("bvar 0"),
            BinderInfo::Default,
        );
        expr = Expr::app(id, expr);
    }
    expr
}

fn encode_module(imports: &[&str], constants: &[ConstantInfo]) -> Vec<u8> {
    let imports: Vec<OleanModuleImport> = imports
        .iter()
        .map(|module| OleanModuleImport {
            module: n(module),
            import_all: false,
            is_exported: false,
            is_meta: false,
        })
        .collect();
    encode_olean_module(
        OleanModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: fln::OLEAN_REGION_ALIGN as u64,
        },
        OleanWriteBudget::default(),
    )
    .expect("valid pinned-format olean fixture")
    .bytes
}

fn limits_with_steps(max_steps: u64) -> OleanCheckLimits {
    let mut budget = Budget::for_stack_bytes(STACK);
    budget.steps = max_steps;
    OleanCheckLimits::new(16 * 1024 * 1024, budget)
}

fn jobs(threads: usize) -> OleanFrontierJobs {
    OleanFrontierJobs {
        threads: NonZeroUsize::new(threads).expect("non-zero threads"),
        worker_stack_bytes: STACK,
    }
}

struct FlagProbe<'a>(&'a AtomicBool);
impl CancellationProbe for FlagProbe<'_> {
    fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::SeqCst)
    }
}

fn chain_fixture() -> Vec<(Name, Vec<u8>)> {
    let p_ty = Expr::const_(n("A.P"), Vec::new());
    let mod_a = encode_module(
        &[],
        &[
            axiom("A.P", Expr::sort(Level::zero())),
            axiom("A.p", p_ty.clone()),
        ],
    );
    let mod_b = encode_module(
        &["A"],
        &[
            safe_def("B.ok1", p_ty.clone(), Expr::const_(n("A.p"), Vec::new())),
            safe_def("B.heavy", p_ty.clone(), beta_chain("A.P", "A.p", 80)),
            safe_def("B.ok2", p_ty.clone(), Expr::const_(n("B.ok1"), Vec::new())),
        ],
    );
    let mod_c = encode_module(
        &["B"],
        &[safe_def(
            "C.useB",
            p_ty.clone(),
            Expr::const_(n("B.heavy"), Vec::new()),
        )],
    );
    let mod_d = encode_module(
        &["C"],
        &[safe_def(
            "D.useC",
            p_ty,
            Expr::const_(n("C.useB"), Vec::new()),
        )],
    );
    vec![
        (n("A"), mod_a),
        (n("B"), mod_b),
        (n("C"), mod_c),
        (n("D"), mod_d),
    ]
}

fn to_inputs(mods: &[(Name, Vec<u8>)]) -> Vec<OleanModuleInput<'_>> {
    mods.iter()
        .map(|(name, bytes)| OleanModuleInput {
            name,
            artifact: bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect()
}

type RowSignature = (String, u8, &'static str, Vec<String>, usize, Vec<String>);

fn row_signature<E>(frontier: &fln::ProvisionalFrontier<E>) -> Vec<RowSignature> {
    frontier
        .rows
        .iter()
        .map(|row| {
            let (tag, assumed_names) = match &row.verdict {
                ProvisionalModuleVerdict::Accepted { .. } => ("accepted", Vec::new()),
                ProvisionalModuleVerdict::AcceptedUnderAssumptions { .. } => {
                    ("accepted-under-assumptions", Vec::new())
                }
                ProvisionalModuleVerdict::Failed(_) => ("failed", Vec::new()),
                ProvisionalModuleVerdict::Inconclusive {
                    assumed_declaration_names,
                    ..
                } => (
                    "inconclusive",
                    assumed_declaration_names
                        .iter()
                        .map(Name::to_display_string)
                        .collect(),
                ),
                ProvisionalModuleVerdict::InternalFault(_) => ("internal-fault", Vec::new()),
                ProvisionalModuleVerdict::Blocked { .. } => ("blocked", Vec::new()),
            };
            (
                row.name.to_display_string(),
                row.phase,
                tag,
                row.assumes.iter().map(Name::to_display_string).collect(),
                row.assumed_declarations,
                assumed_names,
            )
        })
        .collect()
}

#[test]
fn provisional_chain_explores_past_inconclusive_root_and_preserves_conservation() {
    let fixture = chain_fixture();
    let inputs = to_inputs(&fixture);
    let engine = Engine::from_environment(Environment::new());
    let limits = limits_with_steps(120);

    // Without provisional: A accepted, B inconclusive, C and D blocked.
    let plain = engine
        .check_olean_frontier(&inputs, &KVMap::new(), limits)
        .expect("frontier runs");
    assert_eq!(plain.rows.len(), 4);
    assert!(matches!(
        plain.rows[0].verdict,
        OleanModuleVerdict::Accepted { declarations: 2 }
    ));
    assert!(matches!(
        plain.rows[1].verdict,
        OleanModuleVerdict::Inconclusive(_)
    ));
    assert!(matches!(
        plain.rows[2].verdict,
        OleanModuleVerdict::Blocked { .. }
    ));
    assert!(matches!(
        plain.rows[3].verdict,
        OleanModuleVerdict::Blocked { .. }
    ));

    // With provisional: B re-run decl-by-decl (2/3 accepted, 1 assumed [B.heavy]);
    // C and D accepted-under-assumptions with assumes=["B"], assumedDeclarations=1.
    let prov = engine
        .check_olean_frontier_provisional(&inputs, &KVMap::new(), limits)
        .expect("provisional frontier runs");
    let counts = prov.counts();
    counts.assert_conservation();
    assert_eq!(counts.modules, 4);
    assert_eq!(counts.accepted, 1);
    assert_eq!(counts.accepted_under_assumptions, 2);
    assert_eq!(counts.inconclusive, 1);
    assert_eq!(counts.failed, 0);
    assert_eq!(counts.internal_fault, 0);
    assert_eq!(counts.blocked, 0);
    assert!(prov.has_phase2_rows);
    assert!(
        !prov.is_authoritative(),
        "phase-2 rows must force authority=false"
    );
    assert_eq!(prov.exit_code(), 3, "non-zero exit when phase-2 rows exist");
    assert_eq!(prov.eligible_blocked, vec![n("C"), n("D")]);
    assert!(prov.ineligible_blocked.is_empty());

    // Phase-1 engine must hold ONLY A's declarations, zero B/C/D or assumed decls.
    let p1_engine = prov.phase1_engine.as_ref().expect("phase1 engine clean");
    assert!(!p1_engine.environment().has_assumptions());
    assert!(p1_engine.environment().contains(&n("A.P")));
    assert!(!p1_engine.environment().contains(&n("B.heavy")));
    assert!(!p1_engine.environment().contains(&n("C.useB")));

    // Check root B's declaration-by-declaration summary and dominator unlock value.
    assert_eq!(prov.roots.len(), 1);
    let root_b = &prov.roots[0];
    assert_eq!(root_b.module, n("B"));
    assert_eq!(root_b.unlock_value, 2);
    assert_eq!(root_b.first_blocker_count, 2);
    assert_eq!(root_b.accepted_declarations, 2);
    assert_eq!(root_b.total_declarations, 3);
    assert_eq!(root_b.assumed_declarations, 1);
    assert_eq!(root_b.assumed_declaration_names, vec![n("B.heavy")]);

    let sig = row_signature(&prov);
    assert_eq!(
        sig,
        vec![
            ("A".to_owned(), 1, "accepted", vec![], 0, vec![]),
            (
                "B".to_owned(),
                2,
                "inconclusive",
                vec![],
                1,
                vec!["B.heavy".to_owned()]
            ),
            (
                "C".to_owned(),
                2,
                "accepted-under-assumptions",
                vec!["B".to_owned()],
                1,
                vec![]
            ),
            (
                "D".to_owned(),
                2,
                "accepted-under-assumptions",
                vec!["B".to_owned()],
                1,
                vec![]
            ),
        ]
    );
}

#[test]
fn mutant_counting_phase2_acceptances_in_accepted_is_killed() {
    let fixture = chain_fixture();
    let inputs = to_inputs(&fixture);
    let engine = Engine::from_environment(Environment::new());
    let prov = engine
        .check_olean_frontier_provisional(&inputs, &KVMap::new(), limits_with_steps(120))
        .expect("provisional frontier");
    let counts = prov.counts();
    // Mutant: folding accepted_under_assumptions (2) into accepted (1) would give 3.
    assert_eq!(
        counts.accepted, 1,
        "phase-2 acceptances must NEVER be counted in accepted"
    );
    assert_eq!(counts.accepted_under_assumptions, 2);
    assert_ne!(
        prov.exit_code(),
        0,
        "accepted-under-assumptions must NEVER yield exit 0"
    );
}

#[test]
fn mutant_assuming_past_a_failed_import_is_killed() {
    let p_ty = Expr::const_(n("A.P"), Vec::new());
    let mod_a = encode_module(
        &[],
        &[
            axiom("A.P", Expr::sort(Level::zero())),
            axiom("A.p", p_ty.clone()),
        ],
    );
    // B declares an ill-typed definition (`Sort 1` where `A.P` expected) -> K1 Failed.
    let mod_b = encode_module(
        &["A"],
        &[safe_def("B.bad", p_ty.clone(), Expr::sort(Level::one()))],
    );
    let mod_c = encode_module(
        &["B"],
        &[safe_def(
            "C.useB",
            p_ty,
            Expr::const_(n("B.bad"), Vec::new()),
        )],
    );
    let fixture = vec![(n("A"), mod_a), (n("B"), mod_b), (n("C"), mod_c)];
    let inputs = to_inputs(&fixture);
    let engine = Engine::from_environment(Environment::new());
    let limits = limits_with_steps(10_000);

    let prov = engine
        .check_olean_frontier_provisional(&inputs, &KVMap::new(), limits)
        .expect("provisional frontier");
    let counts = prov.counts();
    assert_eq!(counts.accepted, 1);
    assert_eq!(counts.failed, 1);
    assert_eq!(counts.blocked, 1);
    assert_eq!(counts.accepted_under_assumptions, 0);
    assert!(prov.eligible_blocked.is_empty());
    assert_eq!(prov.ineligible_blocked, vec![n("C")]);
    assert!(matches!(
        prov.rows[2].verdict,
        ProvisionalModuleVerdict::Blocked { ref by, .. } if *by == n("B")
    ));
}

#[test]
fn mutant_dropping_authority_false_downgrade_is_killed() {
    let fixture = chain_fixture();
    let inputs = to_inputs(&fixture);
    let engine = Engine::from_environment(Environment::new());
    let prov = engine
        .check_olean_frontier_provisional(&inputs, &KVMap::new(), limits_with_steps(120))
        .expect("provisional frontier");
    assert!(
        prov.policy_summary.attestable,
        "policy itself is release/attestable"
    );
    assert!(prov.has_phase2_rows);
    // Mutant: returning policy_summary.attestable directly would yield true.
    assert!(
        !prov.is_authoritative(),
        "any phase-2 row MUST downgrade authority to false even under Release policy"
    );
}

#[test]
fn mutant_deriving_assumes_from_completion_order_is_killed_and_schedule_independent() {
    let p_ty = Expr::const_(n("A.P"), Vec::new());
    let mod_a = encode_module(
        &[],
        &[
            axiom("A.P", Expr::sort(Level::zero())),
            axiom("A.p", p_ty.clone()),
        ],
    );
    // Two independent inconclusive roots (ZRoot and BRoot) with different step costs
    // so multi-threaded workers complete them in varying order, plus a diamond merger M
    // and a failed branch F + ineligible BehindFail.
    let mod_z = encode_module(
        &["A"],
        &[safe_def(
            "ZRoot.heavy",
            p_ty.clone(),
            beta_chain("A.P", "A.p", 90),
        )],
    );
    let mod_b = encode_module(
        &["A"],
        &[safe_def(
            "BRoot.heavy",
            p_ty.clone(),
            beta_chain("A.P", "A.p", 70),
        )],
    );
    let mod_f = encode_module(
        &["A"],
        &[safe_def(
            "FailRoot.bad",
            p_ty.clone(),
            Expr::sort(Level::one()),
        )],
    );
    let mod_only_z = encode_module(
        &["ZRoot"],
        &[safe_def(
            "OnlyZ.use",
            p_ty.clone(),
            Expr::const_(n("ZRoot.heavy"), Vec::new()),
        )],
    );
    let mod_only_b = encode_module(
        &["BRoot"],
        &[safe_def(
            "OnlyB.use",
            p_ty.clone(),
            Expr::const_(n("BRoot.heavy"), Vec::new()),
        )],
    );
    let mod_diamond = encode_module(
        &["OnlyZ", "OnlyB"],
        &[safe_def(
            "Diamond.use",
            p_ty.clone(),
            Expr::const_(n("OnlyZ.use"), Vec::new()),
        )],
    );
    let mod_behind_fail = encode_module(
        &["OnlyB", "FailRoot"],
        &[safe_def(
            "BehindFail.use",
            p_ty,
            Expr::const_(n("FailRoot.bad"), Vec::new()),
        )],
    );
    let fixture = vec![
        (n("A"), mod_a),
        (n("ZRoot"), mod_z),
        (n("BRoot"), mod_b),
        (n("FailRoot"), mod_f),
        (n("OnlyZ"), mod_only_z),
        (n("OnlyB"), mod_only_b),
        (n("Diamond"), mod_diamond),
        (n("BehindFail"), mod_behind_fail),
    ];
    let inputs = to_inputs(&fixture);
    let engine = Engine::from_environment(Environment::new());
    let limits = limits_with_steps(120);

    let r1 = engine
        .check_olean_frontier_provisional_scheduled(
            &inputs,
            &KVMap::new(),
            limits,
            jobs(1),
            None,
            &mut |_| {},
        )
        .expect("jobs=1");
    let r8 = engine
        .check_olean_frontier_provisional_scheduled(
            &inputs,
            &KVMap::new(),
            limits,
            jobs(8),
            None,
            &mut |_| {},
        )
        .expect("jobs=8");
    let r32 = engine
        .check_olean_frontier_provisional_scheduled(
            &inputs,
            &KVMap::new(),
            limits,
            jobs(32),
            None,
            &mut |_| {},
        )
        .expect("jobs=32");

    let sig1 = row_signature(&r1);
    assert_eq!(
        sig1,
        row_signature(&r8),
        "rows must be identical at --jobs 1 and 8"
    );
    assert_eq!(
        sig1,
        row_signature(&r32),
        "rows must be identical at --jobs 1 and 32"
    );
    assert_eq!(r1.roots, r8.roots);
    assert_eq!(r1.roots, r32.roots);

    // Diamond imports OnlyZ (ZRoot) then OnlyB (BRoot), yet assumes MUST be sorted ["BRoot", "ZRoot"].
    let diamond = r1
        .rows
        .iter()
        .find(|row| row.name == n("Diamond"))
        .expect("diamond row");
    assert!(matches!(
        diamond.verdict,
        ProvisionalModuleVerdict::AcceptedUnderAssumptions { declarations: 1 }
    ));
    assert_eq!(diamond.assumes, vec![n("BRoot"), n("ZRoot")]);
    assert_eq!(diamond.assumed_declarations, 2);

    // BehindFail imports BRoot + FailRoot -> ineligible, stays Blocked!
    let behind_fail = r1
        .rows
        .iter()
        .find(|row| row.name == n("BehindFail"))
        .expect("behind fail row");
    assert!(matches!(
        behind_fail.verdict,
        ProvisionalModuleVerdict::Blocked { .. }
    ));
    assert_eq!(r1.eligible_blocked.len(), 3);
    assert_eq!(r1.ineligible_blocked, vec![n("BehindFail")]);

    // Dominator unlockValue check: BRoot dominates ONLY OnlyB (1), NOT Diamond and NOT BehindFail;
    // ZRoot dominates ONLY OnlyZ (1), NOT Diamond.
    let by_root: BTreeMap<Name, &fln::ProvisionalRootSummary> =
        r1.roots.iter().map(|r| (r.module.clone(), r)).collect();
    assert_eq!(by_root[&n("BRoot")].unlock_value, 1);
    assert_eq!(by_root[&n("ZRoot")].unlock_value, 1);
    // Meanwhile firstBlockerCount over-credits whichever root appeared first on Diamond/BehindFail.
    let total_first_blocker: usize = r1.roots.iter().map(|r| r.first_blocker_count).sum();
    assert!(
        total_first_blocker >= 3,
        "first_blocker_count over-credits shared blocked descendants while dominator unlock_value does not"
    );
}

#[test]
fn reuse_record_writer_refuses_assumption_bearing_environment() {
    let base = Environment::new();
    let p_decl = axiom("Assumed.P", Expr::sort(Level::zero()));
    let prov = ProvisionalEnvironment::from_admitted(base)
        .assume_constants(&[p_decl])
        .expect("assume constant");
    assert!(prov.has_assumptions());
    assert_eq!(prov.assumed_count(), 1);
    assert!(prov.is_assumed(&n("Assumed.P")));

    // Direct writer refusal on the poisoned environment.
    let refusal = check_environment_recordable(prov.as_check_environment());
    assert!(matches!(refusal, Err(ImportReuseRefusal::Unrecordable(_))));

    // Also prove ImportReuseRecord::draft refuses a CheckedOleanSet carrying a poisoned Engine.
    let poisoned_engine = Engine::from_environment(prov.as_check_environment().clone());
    assert!(poisoned_engine.environment().has_assumptions());
    let fake_set = fln::CheckedOleanSet {
        engine: poisoned_engine,
        base_logical_root: Environment::new().logical_root(&KVMap::new()),
        result_logical_root: Environment::new().logical_root(&KVMap::new()),
        modules: Vec::new(),
    };
    let key = ImportClosureKey::compute(
        &[],
        &[],
        &KVMap::new(),
        CheckerIdentity::admission_authority(),
    );
    let draft = ImportReuseRecord::draft(
        key,
        CheckerIdentity::admission_authority(),
        &KVMap::new(),
        &fake_set,
    );
    assert!(
        matches!(draft, Err(ImportReuseRefusal::Unrecordable(_))),
        "reuse-record writer must refuse assumption-bearing CheckedOleanSet, got {draft:?}"
    );
}

#[test]
fn inductive_block_is_assumed_whole_never_in_part() {
    // Build a minimal inductive `MyUnit` (type + ctor + rec) whose recursor/unit
    // is forced to hit a tiny step limit (max_steps = 1) so the ENTIRE inductive
    // block (Induct + Ctor + Rec) is assumed atomically as one unit.
    let ind_name = n("MyUnit");
    let ctor_name = n("MyUnit.mk");
    let rec_name = n("MyUnit.rec");
    let ind_const = Expr::const_(ind_name.clone(), Vec::new());
    let u = Name::str(Name::anonymous(), "u");
    let ind = ConstantInfo::Induct(InductiveVal {
        base: ConstantVal {
            name: ind_name.clone(),
            level_params: Vec::new(),
            type_: Expr::sort(Level::one()),
        },
        num_params: 0,
        num_indices: 0,
        all: vec![ind_name.clone()],
        ctors: vec![ctor_name.clone()],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    });
    let ctor = ConstantInfo::Ctor(ConstructorVal {
        base: ConstantVal {
            name: ctor_name.clone(),
            level_params: Vec::new(),
            type_: ind_const.clone(),
        },
        induct: ind_name.clone(),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    });
    let rec = ConstantInfo::Rec(RecursorVal {
        base: ConstantVal {
            name: rec_name.clone(),
            level_params: vec![u.clone()],
            type_: Expr::forall_e(
                Name::str(Name::anonymous(), "motive"),
                Expr::forall_e(
                    Name::anonymous(),
                    ind_const.clone(),
                    Expr::sort(Level::param(u)),
                    BinderInfo::Default,
                ),
                Expr::forall_e(
                    Name::str(Name::anonymous(), "mk"),
                    Expr::app(
                        Expr::bvar(0).unwrap(),
                        Expr::const_(ctor_name.clone(), Vec::new()),
                    ),
                    Expr::forall_e(
                        Name::str(Name::anonymous(), "t"),
                        ind_const.clone(),
                        Expr::app(Expr::bvar(2).unwrap(), Expr::bvar(0).unwrap()),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
        },
        all: vec![ind_name.clone()],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            ctor: ctor_name.clone(),
            nfields: 0,
            rhs: Expr::lam(
                Name::str(Name::anonymous(), "motive"),
                Expr::forall_e(
                    Name::anonymous(),
                    ind_const.clone(),
                    Expr::sort(Level::param(Name::str(Name::anonymous(), "u"))),
                    BinderInfo::Default,
                ),
                Expr::lam(
                    Name::str(Name::anonymous(), "mk"),
                    Expr::app(
                        Expr::bvar(0).unwrap(),
                        Expr::const_(ctor_name.clone(), Vec::new()),
                    ),
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
        }],
        k: false,
        is_unsafe: false,
    });
    let mod_ind = encode_module(&[], &[ind, ctor, rec]);
    let mod_use = encode_module(
        &["IndMod"],
        &[safe_def(
            "UseMod.val",
            ind_const,
            Expr::const_(ctor_name.clone(), Vec::new()),
        )],
    );
    let fixture = vec![(n("IndMod"), mod_ind), (n("UseMod"), mod_use)];
    let inputs = to_inputs(&fixture);
    let engine = Engine::from_environment(Environment::new());
    // Step limit = 1 forces IndMod's inductive block to hit Inconclusive;
    // all 3 constants (MyUnit, MyUnit.mk, MyUnit.rec) MUST be assumed together!
    let prov = engine
        .check_olean_frontier_provisional(&inputs, &KVMap::new(), limits_with_steps(1))
        .expect("provisional frontier");
    assert_eq!(prov.roots.len(), 1);
    assert_eq!(
        prov.roots[0].assumed_declaration_names,
        vec![ind_name, ctor_name, rec_name],
        "inductive block must be assumed whole (type + ctor + rec together)"
    );
}

#[test]
fn cancellation_and_hostile_batch_preserve_conservation_and_recovery() {
    let fixture = chain_fixture();
    let inputs = to_inputs(&fixture);
    let engine = Engine::from_environment(Environment::new());
    let limits = limits_with_steps(120);

    // Cancelled Phase 2: must yield Inconclusive::cancelled on unstarted Phase-2 rows,
    // preserve conservation, keep authority=false, and succeed cleanly when retried.
    let cancelled = AtomicBool::new(true);
    let probe = FlagProbe(&cancelled);
    let stopped = engine
        .check_olean_frontier_provisional_scheduled(
            &inputs,
            &KVMap::new(),
            limits,
            jobs(1),
            Some(&probe),
            &mut |_| {},
        )
        .expect("cancelled provisional run completes with typed non-answers");
    let stopped_counts = stopped.counts();
    stopped_counts.assert_conservation();
    assert_eq!(stopped_counts.accepted, 1);
    assert_eq!(stopped_counts.inconclusive, 3);
    assert!(!stopped.is_authoritative());
    assert_eq!(stopped.exit_code(), 3);

    // Recovery: clear cancellation flag and re-run -> full Phase-2 results.
    cancelled.store(false, Ordering::SeqCst);
    let recovered = engine
        .check_olean_frontier_provisional_scheduled(
            &inputs,
            &KVMap::new(),
            limits,
            jobs(1),
            Some(&probe),
            &mut |_| {},
        )
        .expect("recovered provisional run");
    assert_eq!(recovered.counts().accepted_under_assumptions, 2);

    // Hostile-batch control: mix corrupt bytes, missing import, cycle, and valid chain.
    let mut hostile = chain_fixture();
    hostile.push((n("Corrupt"), b"not-an-olean-artifact".to_vec()));
    hostile.push((n("MissingDep"), encode_module(&["NoSuchModule"], &[])));
    hostile.push((n("CycA"), encode_module(&["CycB"], &[])));
    hostile.push((n("CycB"), encode_module(&["CycA"], &[])));
    hostile.push((n("BehindCorrupt"), encode_module(&["Corrupt"], &[])));
    let hostile_inputs = to_inputs(&hostile);
    let hostile_run = engine
        .check_olean_frontier_provisional(&hostile_inputs, &KVMap::new(), limits)
        .expect("hostile batch stays typed");
    let hcounts = hostile_run.counts();
    hcounts.assert_conservation();
    assert_eq!(hcounts.accepted, 1);
    assert_eq!(hcounts.accepted_under_assumptions, 2);
    assert_eq!(hcounts.inconclusive, 1);
    assert_eq!(
        hcounts.failed, 4,
        "Corrupt, MissingDep, CycA, CycB must fail"
    );
    assert_eq!(hcounts.blocked, 1, "BehindCorrupt must stay blocked");
    assert!(!hostile_run.is_authoritative());
    assert_eq!(hostile_run.exit_code(), 1);
}

#[test]
fn pure_dominator_and_eligibility_helpers_match_diamond_graph_law() {
    // 0: A (accepted), 1: R1 (inconclusive), 2: R2 (inconclusive), 3: F (failed)
    // 4: C1 -> R1, 5: C2 -> R2, 6: M -> {C1, C2}, 7: X -> {C1, F}
    let order = vec![0, 1, 2, 3, 4, 5, 6, 7];
    let deps = vec![
        BTreeSet::new(),
        BTreeSet::from([0]),
        BTreeSet::from([0]),
        BTreeSet::from([0]),
        BTreeSet::from([1]),
        BTreeSet::from([2]),
        BTreeSet::from([4, 5]),
        BTreeSet::from([4, 3]),
    ];
    let v_acc = OleanModuleVerdict::Accepted { declarations: 1 };
    let v_inc = OleanModuleVerdict::Inconclusive(fln::Inconclusive::authority_incomplete("step"));
    let v_fail = OleanModuleVerdict::Failed(OleanCheckError::MissingConstants {
        declaration: n("F.x"),
        names: vec![n("Missing")],
    });
    let v_blk_r1 = OleanModuleVerdict::Blocked { by: n("R1") };
    let v_blk_r2 = OleanModuleVerdict::Blocked { by: n("R2") };
    let v_blk_c1 = OleanModuleVerdict::Blocked { by: n("C1") };
    let verdicts = vec![
        &v_acc, &v_inc, &v_inc, &v_fail, &v_blk_r1, &v_blk_r2, &v_blk_c1, &v_blk_c1,
    ];
    let (eligible, ineligible, _) = classify_blocked_eligibility(&order, &deps, &verdicts);
    assert_eq!(eligible, vec![4, 5, 6]);
    assert_eq!(ineligible, vec![7]);

    let is_accepted = vec![true, false, false, false, false, false, false, false];
    let is_blocked = vec![false, false, false, false, true, true, true, true];
    let first_blocker = vec![None, None, None, None, Some(1), Some(2), Some(4), Some(4)];
    let (unlock, first_cnt) =
        compute_root_dominators(&order, &deps, &is_accepted, &is_blocked, &first_blocker);
    assert_eq!(unlock[&1], 1, "R1 dominates only C1 (not M or X)");
    assert_eq!(unlock[&2], 1, "R2 dominates only C2 (not M)");
    assert_eq!(
        unlock[&3], 0,
        "F does not solely dominate X (R1 also blocks X)"
    );
    assert_eq!(
        first_cnt[&1], 3,
        "first_blocker over-credits R1 for C1, M, and X"
    );
    assert_eq!(first_cnt[&2], 1);
}

/// Regression test for the Phase-2 `HostAllocationFailure` worker-unwind
/// deadlock found on live Mathlib S27: when Phase-2 workers unwind on
/// `HostAllocationFailure` at `--jobs 4`, `phase2_guarded` catches the unwind,
/// schedules an isolated single-threaded retry, never drops a worker or stalls
/// `in_flight`, and exercises persistent `ProvisionalEnvironment` base reuse
/// across a multi-hop Phase-2 chain (`Root -> Mid -> Leaf`).
#[test]
fn phase2_host_allocation_failure_retries_isolated_and_never_deadlocks_workers() {
    use std::sync::atomic::AtomicUsize;

    let prop = Expr::sort(Level::zero());
    let base_bytes = encode_module(
        &[],
        &[
            axiom("Base.P", prop.clone()),
            axiom("Base.p", Expr::const_(n("Base.P"), Vec::new())),
        ],
    );
    let root_bytes = encode_module(
        &["Base"],
        &[
            safe_def(
                "Root.cheap",
                Expr::const_(n("Base.P"), Vec::new()),
                Expr::const_(n("Base.p"), Vec::new()),
            ),
            safe_def(
                "Root.heavy",
                Expr::const_(n("Base.P"), Vec::new()),
                beta_chain("Base.P", "Base.p", 250),
            ),
        ],
    );
    // Transient OOM target (`Mid`) plus its dependent (`Leaf`) to verify
    // `phase2_base_of` persistent-environment reuse and consumer retirement.
    let mid_bytes = encode_module(
        &["Base", "Root"],
        &[safe_def(
            "Mid.useHeavy",
            Expr::const_(n("Base.P"), Vec::new()),
            Expr::const_(n("Root.heavy"), Vec::new()),
        )],
    );
    let leaf_bytes = encode_module(
        &["Base", "Root", "Mid"],
        &[safe_def(
            "Leaf.useMid",
            Expr::const_(n("Base.P"), Vec::new()),
            Expr::const_(n("Mid.useHeavy"), Vec::new()),
        )],
    );
    // Persistent OOM target (`Doomed`) plus its dependent (`BehindDoomed`) to
    // verify repeated OOM settles cleanly as `Inconclusive` + `Blocked`.
    let doomed_bytes = encode_module(
        &["Base", "Root"],
        &[safe_def(
            "Doomed.useHeavy",
            Expr::const_(n("Base.P"), Vec::new()),
            Expr::const_(n("Root.heavy"), Vec::new()),
        )],
    );
    let behind_doomed_bytes = encode_module(
        &["Base", "Doomed"],
        &[safe_def(
            "BehindDoomed.useDoomed",
            Expr::const_(n("Base.P"), Vec::new()),
            Expr::const_(n("Doomed.useHeavy"), Vec::new()),
        )],
    );

    let mods = vec![
        (n("Base"), base_bytes),
        (n("Root"), root_bytes),
        (n("Mid"), mid_bytes),
        (n("Leaf"), leaf_bytes),
        (n("Doomed"), doomed_bytes),
        (n("BehindDoomed"), behind_doomed_bytes),
    ];
    let inputs = to_inputs(&mods);

    let limits = limits_with_steps(300);
    let options = KVMap::new();
    let jobs = jobs(4);

    // Decode call counts per module:
    // - Call 1 happens during Phase 1 initial decode.
    // - Call 2 is Phase 2's first attempt.
    // - Call 3 is Phase 2's isolated retry.
    let mid_calls = AtomicUsize::new(0);
    let doomed_calls = AtomicUsize::new(0);
    let admitted = fln_admission::Admitted {
        environment: Environment::new(),
        checker_environment: None,
        imported_modules: Default::default(),
        imported_environment: None,
        imported_module_dependencies: Default::default(),
        executable_opaques: Default::default(),
        runtime_initializers: Default::default(),
        options: KVMap::new(),
    };
    let hooks = fln_admission::FrontierRunHooks {
        check: &|job| admitted.frontier_check_module(job, &options, limits),
        decode: &|idx| {
            if idx == 2 {
                let call = mid_calls.fetch_add(1, Ordering::SeqCst) + 1;
                if call == 2 {
                    std::panic::panic_any(fln_admission::HostAllocationFailure {
                        requested: 65_536,
                    });
                }
            }
            if idx == 4 {
                let call = doomed_calls.fetch_add(1, Ordering::SeqCst) + 1;
                if call >= 2 {
                    std::panic::panic_any(fln_admission::HostAllocationFailure {
                        requested: 131_072,
                    });
                }
            }
            fln_admission::decode_olean_module_input(&inputs[idx], limits)
        },
        memory: &fln_admission::HostProcessMemorySource,
    };

    let frontier = admitted
        .check_olean_frontier_provisional_using(&inputs, limits, jobs, None, &mut |_| {}, hooks)
        .expect("provisional frontier must recover from Phase-2 HostAllocationFailure");

    let by_name: BTreeMap<String, _> = frontier
        .rows
        .iter()
        .map(|row| (row.name.to_display_string(), row))
        .collect();

    assert_eq!(
        mid_calls.load(Ordering::SeqCst),
        3,
        "Mid decoded once in P1, failed once in P2, succeeded on isolated P2 retry"
    );
    assert_eq!(
        doomed_calls.load(Ordering::SeqCst),
        3,
        "Doomed decoded once in P1, failed once in P2, and failed once on isolated P2 retry"
    );

    let mid = by_name["Mid"];
    assert!(
        matches!(
            mid.verdict,
            ProvisionalModuleVerdict::AcceptedUnderAssumptions { declarations: 1 }
        ),
        "Mid must recover on isolated retry: {:?}",
        mid.verdict
    );
    assert!(
        mid.memory_retry.is_some(),
        "Mid must record its Phase-2 memory_retry"
    );
    assert_eq!(mid.assumes, vec![n("Root")]);
    assert_eq!(mid.assumed_declarations, 1);

    let leaf = by_name["Leaf"];
    assert!(
        matches!(
            leaf.verdict,
            ProvisionalModuleVerdict::AcceptedUnderAssumptions { declarations: 1 }
        ),
        "Leaf must accept via Mid's reused base ProvisionalEnvironment: {:?}",
        leaf.verdict
    );
    assert_eq!(leaf.assumes, vec![n("Root")]);
    assert_eq!(leaf.assumed_declarations, 1);

    let doomed = by_name["Doomed"];
    assert!(
        matches!(
            doomed.verdict,
            ProvisionalModuleVerdict::Inconclusive { .. }
        ),
        "Doomed must settle as typed Inconclusive after isolated retry fails: {:?}",
        doomed.verdict
    );
    assert!(
        doomed.memory_retry.is_some(),
        "Doomed must record its Phase-2 memory_retry"
    );

    let behind = by_name["BehindDoomed"];
    assert!(
        matches!(
            &behind.verdict,
            ProvisionalModuleVerdict::Blocked { by, .. } if by == &n("Doomed")
        ),
        "BehindDoomed must settle cleanly as Blocked by Doomed: {:?}",
        behind.verdict
    );
}

#[test]
fn phase2_memory_admission_accounts_for_retained_rss_and_inflight_estimates() {
    struct RetainedMemory {
        phase2: AtomicBool,
        limit: Option<u64>,
    }

    impl fln_admission::FrontierMemorySource for RetainedMemory {
        fn sample(&self) -> fln_admission::FrontierMemorySample {
            fln_admission::FrontierMemorySample {
                // Model the import environments retained after Phase 1. Their
                // bytes are absent from the new workers' closure reservations.
                rss_bytes: if self.phase2.load(Ordering::SeqCst) {
                    80
                } else {
                    0
                },
                limit_bytes: self.limit,
            }
        }

        fn estimate_bytes(&self, _: usize, _: u64) -> u64 {
            15
        }
    }

    let mut fixture = chain_fixture();
    // C and E become ready together once B has been explored. D consumes C's
    // provisional environment, exercising reservation release across batches.
    fixture.push((
        n("E"),
        encode_module(
            &["B"],
            &[safe_def(
                "E.useB",
                Expr::const_(n("A.P"), Vec::new()),
                Expr::const_(n("B.heavy"), Vec::new()),
            )],
        ),
    ));
    let inputs = to_inputs(&fixture);
    let limits = limits_with_steps(120);
    let options = KVMap::new();
    let admitted = fln_admission::Admitted {
        environment: Environment::new(),
        checker_environment: None,
        imported_modules: Default::default(),
        imported_environment: None,
        imported_module_dependencies: Default::default(),
        executable_opaques: Default::default(),
        runtime_initializers: Default::default(),
        options: KVMap::new(),
    };
    let run = |threads, limit| {
        let memory = RetainedMemory {
            phase2: AtomicBool::new(false),
            limit,
        };
        let mut progress = BTreeMap::new();
        let frontier = admitted
            .check_olean_frontier_provisional_using_with_progress(
                &inputs,
                limits,
                jobs(threads),
                None,
                &mut |event| {
                    if matches!(
                        event,
                        fln::OleanFrontierEvent::Decided {
                            position, total, ..
                        } if position == total
                    ) {
                        memory.phase2.store(true, Ordering::SeqCst);
                    }
                },
                Some(&mut |_, _, row| {
                    assert!(
                        progress
                            .insert(row.name.clone(), row.memory.admission_deferrals)
                            .is_none(),
                        "each Phase-2 row is reported once"
                    );
                }),
                fln_admission::FrontierRunHooks {
                    check: &|job| admitted.frontier_check_module(job, &options, limits),
                    decode: &|index| {
                        fln_admission::decode_olean_module_input(&inputs[index], limits)
                    },
                    memory: &memory,
                },
            )
            .expect("memory estimates must defer work without inventing a verdict");
        let counts = frontier.counts();
        assert_eq!(counts.modules, 5);
        assert_eq!(counts.accepted, 1);
        assert_eq!(counts.inconclusive, 1);
        assert_eq!(counts.accepted_under_assumptions, 3);
        assert_eq!(counts.failed + counts.blocked + counts.internal_fault, 0);
        assert!(!frontier.is_authoritative());
        assert!(
            frontier
                .phase1_rows
                .iter()
                .all(|row| row.memory.admission_deferrals == 0),
            "the scheduling pressure begins in Phase 2"
        );
        for row in frontier.rows.iter().filter(|row| row.phase == 2) {
            assert_eq!(row.memory.estimated_bytes, 15);
            assert_eq!(
                progress.get(&row.name),
                Some(&row.memory.admission_deferrals),
                "streamed and final memory attribution must agree"
            );
        }
        frontier
    };

    let serial = run(1, Some(100));
    let bounded = run(4, Some(100));
    assert_eq!(row_signature(&serial), row_signature(&bounded));
    assert!(
        bounded
            .rows
            .iter()
            .any(|row| row.memory.admission_deferrals > 0),
        "80 retained + 15 reserved + 15 next exceeds 100, although live RSS alone does not"
    );

    // An idle worker must still try when its estimate alone exceeds the cap:
    // only the actual decoder/checkers can produce a resource non-answer.
    let below_retained = run(4, Some(10));
    assert_eq!(row_signature(&serial), row_signature(&below_retained));

    // Without a ceiling, --jobs keeps its ordinary parallel scheduling; there
    // is no arbitrary Phase-2 cap masquerading as memory admission control.
    let unbounded = run(4, None);
    assert_eq!(row_signature(&serial), row_signature(&unbounded));
    assert!(
        unbounded
            .rows
            .iter()
            .all(|row| row.memory.admission_deferrals == 0)
    );
}

#[test]
fn phase2_cancellation_settles_a_pending_memory_retry_without_running_it() {
    use std::sync::atomic::AtomicUsize;

    let fixture = chain_fixture();
    let inputs = to_inputs(&fixture);
    let limits = limits_with_steps(120);
    let options = KVMap::new();
    let cancelled = AtomicBool::new(false);
    let probe = FlagProbe(&cancelled);
    let c_calls = AtomicUsize::new(0);
    let d_calls = AtomicUsize::new(0);
    let admitted = fln_admission::Admitted {
        environment: Environment::new(),
        checker_environment: None,
        imported_modules: Default::default(),
        imported_environment: None,
        imported_module_dependencies: Default::default(),
        executable_opaques: Default::default(),
        runtime_initializers: Default::default(),
        options: KVMap::new(),
    };

    let stopped = admitted
        .check_olean_frontier_provisional_using(
            &inputs,
            limits,
            jobs(4),
            Some(&probe),
            &mut |_| {},
            fln_admission::FrontierRunHooks {
                check: &|job| admitted.frontier_check_module(job, &options, limits),
                decode: &|index| {
                    if index == 2 && c_calls.fetch_add(1, Ordering::SeqCst) == 1 {
                        // Phase 1 already decoded C. Cancel during its first
                        // Phase-2 attempt, before the scheduler can enqueue the
                        // memory retry. No timing or sibling ordering is involved.
                        cancelled.store(true, Ordering::SeqCst);
                        std::panic::panic_any(fln_admission::HostAllocationFailure {
                            requested: 65_536,
                        });
                    }
                    if index == 3 {
                        d_calls.fetch_add(1, Ordering::SeqCst);
                    }
                    fln_admission::decode_olean_module_input(&inputs[index], limits)
                },
                memory: &fln_admission::HostProcessMemorySource,
            },
        )
        .expect("cancellation must settle the queued retry without stalling");

    assert_eq!(
        c_calls.load(Ordering::SeqCst),
        2,
        "C's isolated retry must not start after cancellation was observed"
    );
    assert_eq!(
        d_calls.load(Ordering::SeqCst),
        1,
        "D must not run in Phase 2 after its import was cancelled"
    );
    let counts = stopped.counts();
    assert_eq!(counts.modules, 4);
    assert_eq!(counts.accepted, 1);
    assert_eq!(counts.inconclusive, 3);
    assert_eq!(counts.accepted_under_assumptions, 0);
    assert_eq!(counts.failed + counts.blocked + counts.internal_fault, 0);
    assert!(!stopped.is_authoritative());
    assert_eq!(stopped.exit_code(), 3);
    for module in ["C", "D"] {
        let row = stopped
            .rows
            .iter()
            .find(|row| row.name == n(module))
            .expect("every module has a row");
        assert!(
            matches!(
                &row.verdict,
                ProvisionalModuleVerdict::Inconclusive { reason, .. }
                    if matches!(
                        &reason.cause,
                        fln_core::outcome::InconclusiveCause::Cancelled { .. }
                    )
            ),
            "{module} must remain a typed cancellation: {:?}",
            row.verdict
        );
        assert!(
            row.memory_retry.is_none(),
            "cancelling a queued retry must not claim a second attempt ran"
        );
    }

    cancelled.store(false, Ordering::SeqCst);
    let recovered = admitted
        .check_olean_frontier_provisional_scheduled(
            &inputs,
            &options,
            limits,
            jobs(4),
            Some(&probe),
            &mut |_| {},
        )
        .expect("a fresh run after cancellation can explore the same closure");
    assert_eq!(recovered.counts().accepted_under_assumptions, 2);
    assert_eq!(recovered.counts().inconclusive, 1);
    assert!(!recovered.is_authoritative());
}

#[test]
fn phase2_unread_artifact_blocks_descendants_without_inventing_assumptions() {
    use std::sync::atomic::AtomicUsize;

    // Refuse the independent reading both at the inconclusive root B and at
    // its provisional descendant C. A missing whole-module reading provides
    // no complete import environment, unlike a checked atomic unit that was
    // explicitly assumed after exhausting its budget.
    for unread_index in [1, 2] {
        let mut serial_signature = None;
        for threads in [1, 4] {
            let fixture = chain_fixture();
            let inputs = to_inputs(&fixture);
            let limits = limits_with_steps(120);
            let options = KVMap::new();
            let calls: Vec<_> = (0..inputs.len()).map(|_| AtomicUsize::new(0)).collect();
            let admitted = fln_admission::Admitted {
                environment: Environment::new(),
                checker_environment: None,
                imported_modules: Default::default(),
                imported_environment: None,
                imported_module_dependencies: Default::default(),
                executable_opaques: Default::default(),
                runtime_initializers: Default::default(),
                options: KVMap::new(),
            };
            let frontier = admitted
                .check_olean_frontier_provisional_using(
                    &inputs,
                    limits,
                    jobs(threads),
                    None,
                    &mut |_| {},
                    fln_admission::FrontierRunHooks {
                        check: &|job| admitted.frontier_check_module(job, &options, limits),
                        decode: &|index| {
                            let attempt = calls[index].fetch_add(1, Ordering::SeqCst);
                            let mut decoded =
                                fln_admission::decode_olean_module_input(&inputs[index], limits)?;
                            if index == unread_index && attempt == 1 {
                                assert!(matches!(
                                    &decoded.independent,
                                    fln_admission::IndependentReading::Read(_)
                                ));
                                decoded.independent = fln_admission::IndependentReading::Unread(
                                    "independent reader resource stop".to_owned(),
                                );
                            }
                            Ok(decoded)
                        },
                        memory: &fln_admission::HostProcessMemorySource,
                    },
                )
                .expect("an unavailable reading must settle the frontier");

            let unread = frontier
                .rows
                .iter()
                .find(|row| row.name == fixture[unread_index].0)
                .expect("unread module has a final row");
            assert_eq!(calls[unread_index].load(Ordering::SeqCst), 2);
            assert!(
                matches!(
                    &unread.verdict,
                    ProvisionalModuleVerdict::Inconclusive {
                        accepted_declarations: 0,
                        assumed_declaration_names,
                        ..
                    } if assumed_declaration_names.is_empty()
                ),
                "an unread module must remain a nonanswer without assumed declarations: {:?}",
                unread.verdict
            );
            assert!(unread.unit_reports.is_empty());
            assert!(unread.memory_retry.is_none());
            assert_eq!(unread.assumed_declarations, usize::from(unread_index == 2));

            for index in unread_index + 1..fixture.len() {
                assert_eq!(
                    calls[index].load(Ordering::SeqCst),
                    1,
                    "a dependent must not decode again after its Phase-2 import became unavailable"
                );
                let dependent = frontier
                    .rows
                    .iter()
                    .find(|row| row.name == fixture[index].0)
                    .expect("blocked descendant has a final row");
                assert!(
                    matches!(
                        &dependent.verdict,
                        ProvisionalModuleVerdict::Blocked { by, .. }
                            if by == &fixture[index - 1].0
                    ),
                    "a missing import environment must block its dependent: {:?}",
                    dependent.verdict
                );
                assert!(dependent.unit_reports.is_empty());
            }

            let counts = frontier.counts();
            counts.assert_conservation();
            assert_eq!(counts.accepted, 1);
            assert_eq!(counts.inconclusive, unread_index);
            assert_eq!(counts.blocked, fixture.len() - unread_index - 1);
            assert_eq!(counts.accepted_under_assumptions, 0);
            assert_eq!(counts.failed + counts.internal_fault, 0);
            assert!(!frontier.is_authoritative());
            let signature = row_signature(&frontier);
            if let Some(serial) = &serial_signature {
                assert_eq!(
                    &signature, serial,
                    "resource stops must be schedule independent"
                );
            } else {
                serial_signature = Some(signature);
            }
        }
    }
}

#[test]
fn repeated_declarations_preserve_independent_projection_nonanswers() {
    use fln_admission::{
        CheckerDecodeBudget, PerDeclarationModuleOutcome, check_decoded_olean_per_declaration,
    };
    use fln_core::outcome::Outcome;
    use fln_env::constants::TheoremVal;

    let options = KVMap::new();
    let limits = limits_with_steps(10_000);
    let proposition = Expr::const_(n("Repeat.P"), Vec::new());
    let repeated = axiom("Repeat.t", proposition.clone());
    let theorem = ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name: n("Repeat.t"),
            level_params: Vec::new(),
            type_: proposition.clone(),
        },
        value: Expr::const_(n("Repeat.w"), Vec::new()),
        all: vec![n("Repeat.t")],
    });
    let artifact = encode_module(&[], std::slice::from_ref(&repeated));
    let module_name = n("Repeat");
    let input = OleanModuleInput {
        name: &module_name,
        artifact: &artifact,
        server_artifact: None,
        private_artifact: None,
    };

    // Exact duplicate axioms take already_present; a theorem of the same
    // proposition subsumes the imported axiom and takes the repeat branch.
    // Both paths still owe an independent reading of this artifact.
    for (label, prior) in [("exact duplicate", repeated), ("subsumed axiom", theorem)] {
        let base_artifact = encode_module(
            &[],
            &[
                axiom("Repeat.P", Expr::sort(Level::zero())),
                axiom("Repeat.w", proposition.clone()),
                prior,
            ],
        );
        let Outcome::Complete(checked_base) = Engine::from_environment(Environment::new())
            .check_olean_artifact(&base_artifact, &options, limits)
            .expect("base artifact must decode")
        else {
            panic!("{label}: the ordinary council must admit the base");
        };
        let base = ProvisionalEnvironment::from_admitted(checked_base.engine.environment().clone());
        let base_root = base.as_check_environment().logical_root(&options);
        let decoded = fln_admission::decode_olean_module_input(&input, limits)
            .expect("repeat artifact must decode independently");

        let complete = check_decoded_olean_per_declaration(&base, &decoded, limits, true)
            .expect("valid repeat must be checked");
        assert!(
            matches!(&complete.verdict, PerDeclarationModuleOutcome::AllAccepted),
            "{label}: {:?}",
            complete.verdict
        );
        assert_eq!(complete.accepted_declarations, 1);
        assert!(complete.final_env.is_some());
        assert!(complete.assumed_declaration_names.is_empty());

        let mut exhausted = limits;
        exhausted.admission.checker.decode = CheckerDecodeBudget::new(0, 0);
        let stopped = check_decoded_olean_per_declaration(&base, &decoded, exhausted, true)
            .expect("projection exhaustion is a typed nonanswer");
        assert!(
            matches!(
                &stopped.verdict,
                PerDeclarationModuleOutcome::PartialAssumed(_)
            ),
            "{label}: a failed reading projection must not count as acceptance: {:?}",
            stopped.verdict
        );
        assert_eq!(stopped.accepted_declarations, 0);
        assert_eq!(stopped.total_declarations, 1);
        assert!(stopped.entries.is_empty());
        assert!(stopped.final_env.is_none());
        assert!(stopped.assumed_declaration_names.is_empty());
        assert!(stopped.unit_reports.is_empty());
        assert!(matches!(
            checked_base
                .engine
                .check_olean_artifact(&artifact, &options, exhausted)
                .expect("the authoritative path must preserve the same budget stop"),
            Outcome::Inconclusive(_)
        ));

        // A disagreeing independent reader remains a concrete failure, never
        // a provisional assumption. This is an adversarial reading mutation.
        let mut mismatched = fln_admission::decode_olean_module_input(&input, limits)
            .expect("unchanged repeat bytes still decode");
        mismatched.independent = fln_admission::IndependentReading::Read(Vec::new());
        let failed = check_decoded_olean_per_declaration(&base, &mismatched, limits, true)
            .expect("the disagreement must have a terminal module outcome");
        assert!(
            matches!(
                &failed.verdict,
                PerDeclarationModuleOutcome::Failed(
                    OleanCheckError::IndependentReadingDiffers { name, .. }
                ) if name == &n("Repeat.t")
            ),
            "{label}: {:?}",
            failed.verdict
        );
        assert!(failed.final_env.is_none());
        assert!(failed.assumed_declaration_names.is_empty());

        let recovered = check_decoded_olean_per_declaration(&base, &decoded, limits, true)
            .expect("a fresh check with the original budget recovers");
        assert!(matches!(
            &recovered.verdict,
            PerDeclarationModuleOutcome::AllAccepted
        ));
        assert_eq!(recovered.accepted_declarations, 1);
        assert!(recovered.final_env.is_some());
        assert_eq!(
            base.as_check_environment().logical_root(&options),
            base_root
        );
        assert!(!base.has_assumptions());
    }
}

#[test]
fn repeated_theorem_assumptions_survive_both_sides_of_a_diamond() {
    use fln_env::constants::TheoremVal;

    let proposition = Expr::const_(n("A.P"), Vec::new());
    let theorem = |value| {
        ConstantInfo::Thm(TheoremVal {
            base: ConstantVal {
                name: n("A.t"),
                level_params: Vec::new(),
                type_: proposition.clone(),
            },
            value,
            all: vec![n("A.t")],
        })
    };
    let base = encode_module(
        &[],
        &[
            axiom("A.P", Expr::sort(Level::zero())),
            axiom("A.p", proposition.clone()),
            theorem(Expr::const_(n("A.p"), Vec::new())),
        ],
    );
    let repeated = theorem(beta_chain("A.P", "A.p", 80));
    let repeat = encode_module(&["A"], std::slice::from_ref(&repeated));
    let heavy = encode_module(
        &["A"],
        &[safe_def(
            "Other.heavy",
            proposition.clone(),
            beta_chain("A.P", "A.p", 80),
        )],
    );
    let join = encode_module(
        &["Left", "Right"],
        &[safe_def(
            "Join.use",
            proposition,
            Expr::const_(n("A.t"), Vec::new()),
        )],
    );
    let repeat_again = encode_module(&["Join"], &[repeated]);

    // Tied import sizes select the first branch as the persistent base. The
    // other branch must carry every newly assumed name in its delta.
    for (repeated, other) in [("Left", "Right"), ("Right", "Left")] {
        let modules = vec![
            (n("A"), base.clone()),
            (n(repeated), repeat.clone()),
            (n(other), heavy.clone()),
            (n("Join"), join.clone()),
            (n("Again"), repeat_again.clone()),
        ];
        for workers in [1, 2] {
            let frontier = Engine::from_environment(Environment::new())
                .check_olean_frontier_provisional_scheduled(
                    &to_inputs(&modules),
                    &KVMap::new(),
                    limits_with_steps(120),
                    jobs(workers),
                    None,
                    &mut |_| {},
                )
                .unwrap();
            let row = frontier.rows.iter().find(|r| r.name == n("Join")).unwrap();
            assert!(matches!(
                row.verdict,
                ProvisionalModuleVerdict::AcceptedUnderAssumptions { .. }
            ));
            assert_eq!(row.assumes, vec![n("Left"), n("Right")]);
            assert_eq!(row.assumed_declarations, 2, "repeat in {repeated}");
            let again = frontier.rows.iter().find(|r| r.name == n("Again")).unwrap();
            assert!(matches!(
                again.verdict,
                ProvisionalModuleVerdict::Inconclusive { .. }
            ));
            assert_eq!(again.assumed_declarations, 2, "repeat of an assumed name");
            assert!(!frontier.is_authoritative());
        }
    }
}
